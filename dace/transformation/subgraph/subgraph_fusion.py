# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" This module contains classes that implement subgraph fusion
"""
import dace

from dace import dtypes, registry, symbolic, subsets, data
from dace.sdfg import nodes, utils, replace, SDFG, scope_contains_scope
from dace.sdfg.graph import SubgraphView
from dace.sdfg.scope import ScopeTree
from dace.memlet import Memlet
from dace.transformation import transformation
from dace.properties import make_properties, Property
from dace.symbolic import symstr, overapproximate
from dace.sdfg.propagation import propagate_memlets_sdfg, propagate_memlet, propagate_memlets_scope, _propagate_node
from dace.transformation.subgraph import helpers
from dace.transformation.dataflow import RedundantArray
from dace.sdfg.utils import consolidate_edges_scope
from dace.transformation.helpers import find_contiguous_subsets

from copy import deepcopy as dcpy
from typing import List, Union
import warnings

import dace.libraries.standard as stdlib

from collections import defaultdict
from itertools import chain


@registry.autoregister_params(singlestate=True)
@make_properties
class SubgraphFusion(transformation.SubgraphTransformation):
    """ Implements the SubgraphFusion transformation.
        Fuses together the maps contained in the subgraph and pushes inner nodes
        into a global outer map, creating transients and new connections
        where necessary.

        SubgraphFusion requires all lowest scope level maps in the subgraph
        to have the same indices and parameter range in every dimension.
        This can be achieved using the MultiExpansion transformation first.
        Reductions can also be expanded using ReduceExpansion as a
        preprocessing step.

    """

    debug = Property(desc="Show debug info", dtype=bool, default=False)

    transient_allocation = Property(
        desc="Storage Location to push transients to that are "
        "fully contained within the subgraph.",
        dtype=dtypes.StorageType,
        default=dtypes.StorageType.Default)

    schedule_innermaps = Property(desc="Schedule of inner maps. If none, "
                                  "keeps schedule.",
                                  dtype=dtypes.ScheduleType,
                                  default=dtypes.ScheduleType.Default,
                                  allow_none=True)
    consolidate = Property(
        desc="Consolidate edges that enter and exit the fused map.",
        dtype=bool,
        default=False)

    propagate = Property(
        desc="Propagate memlets of edges that enter and exit the fused map."
        "Disable if this causes problems. (If memlet propagation does"
        "not work correctly)",
        dtype=bool,
        default=True)

    @staticmethod
    def can_be_applied(sdfg: SDFG, subgraph: SubgraphView) -> bool:
        '''
        Fusible if
        1. Maps have the same access sets and ranges in order
        2. Any nodes in between two maps are AccessNodes only, without WCR
           There is at most one AccessNode only on a path between two maps,
           no other nodes are allowed
        3. The exiting memlets' subsets to an intermediate edge must cover
           the respective incoming memlets' subset into the next map.
           Also, as a limitation, the union of all exiting memlets'
           subsets must be contiguous.
        '''
        # get graph
        graph = subgraph.graph
        for node in subgraph.nodes():
            if node not in graph.nodes():
                return False

        # next, get all the maps
        map_entries = helpers.get_outermost_scope_maps(sdfg, graph, subgraph)
        map_exits = [graph.exit_node(map_entry) for map_entry in map_entries]
        maps = [map_entry.map for map_entry in map_entries]

        # 1. basic checks:
        # 1.1 we need to have at least two maps
        if len(maps) <= 1:
            return False
        '''
        # 1.2 Special Case: If we can establish a valid permutation, we can
        #     skip check 1.3
        permutation = self.find_permutation
        '''
        # 1.3 check whether all maps are the same
        base_map = maps[0]
        for map in maps:
            if map.get_param_num() != base_map.get_param_num():
                return False
            if not all(
                [p1 == p2 for (p1, p2) in zip(map.params, base_map.params)]):
                return False
            if not map.range == base_map.range:
                return False
        # 1.3 check whether all map entries have the same schedule
        schedule = map_entries[0].schedule
        if not all([entry.schedule == schedule for entry in map_entries]):
            return False

        # 2. check intermediate feasiblility
        # see map_fusion.py for similar checks
        # with the restrictions below being more relaxed

        # 2.1 do some preparation work first:
        # calculate all out_nodes and intermediate_nodes
        # definition see in apply()
        node_config = SubgraphFusion.get_adjacent_nodes(sdfg, graph,
                                                        map_entries)
        _, intermediate_nodes, out_nodes = node_config

        # 2.2 topological feasibility:
        if not SubgraphFusion.check_topo_feasibility(
                sdfg, graph, map_entries, intermediate_nodes, out_nodes):
            return False

        # 2.3 memlet feasibility
        # For each intermediate node, look at whether inner adjacent
        # memlets of the exiting map cover inner adjacent memlets
        # of the next entering map.
        # We also check for any WCRs on the fly.

        for node in intermediate_nodes:
            upper_subsets = set()
            lower_subsets = set()
            # First, determine which dimensions of the memlet ranges
            # change with the map, we do not need to care about the other dimensions.
            try:
                dims_to_discard = SubgraphFusion.get_invariant_dimensions(
                    sdfg, graph, map_entries, map_exits, node)
            except NotImplementedError:
                return False
            # find upper_subsets
            for in_edge in graph.in_edges(node):
                in_in_edge = graph.memlet_path(in_edge)[-2]
                # first check for WCRs
                if in_edge.data.wcr:
                    # check whether the WCR is actually produced at
                    # this edge or further up in the memlet path. If not,
                    # we can still fuse!
                    subset_params = set(
                        [str(s) for s in in_in_edge.data.subset.free_symbols])
                    if any([
                            p not in subset_params
                            for p in in_edge.src.map.params
                    ]):
                        return False
                if in_edge.src in map_exits:
                    subset_to_add = dcpy(in_in_edge.data.subset\
                                         if in_in_edge.data.data == node.data\
                                         else in_in_edge.data.other_subset)
                    subset_to_add.pop(dims_to_discard)
                    upper_subsets.add(subset_to_add)
                else:
                    raise NotImplementedError("Nodes between two maps to be"
                                              "fused with *incoming* edges"
                                              "from outside the maps are not"
                                              "allowed yet.")

            # find lower_subsets
            for out_edge in graph.out_edges(node):
                if out_edge.dst in map_entries:
                    # cannot use memlet tree here as there could be
                    # not just one map succedding. Do it manually
                    for oedge in graph.out_edges(out_edge.dst):
                        if oedge.src_conn[3:] == out_edge.dst_conn[2:]:
                            subset_to_add = dcpy(oedge.data.subset \
                                                 if oedge.data.data == node.data \
                                                 else oedge.data.other_subset)
                            subset_to_add.pop(dims_to_discard)
                            lower_subsets.add(subset_to_add)

            # We assume that upper_subsets are contiguous
            # Check for this.
            try:
                contiguous_upper = find_contiguous_subsets(upper_subsets)
                if len(contiguous_upper) > 1:
                    return False
            except TypeError:
                warnings.warn(
                    'Could not determine whether subset is continuous.'
                    'Exiting Check with False.')
                return False

            # now take union of upper subsets
            upper_iter = iter(upper_subsets)
            union_upper = next(upper_iter)
            for subs in upper_iter:
                union_upper = subsets.union(union_upper, subs)
                if not union_upper:
                    # something went wrong using union -- we'd rather abort
                    return False

            # finally check coverage
            # every lower subset must be completely covered by union_upper
            for lower_subset in lower_subsets:
                if not union_upper.covers(lower_subset):
                    return False

        return True

    @staticmethod
    def find_permutation(map_entries: List[nodes.MapEntry]) \
                 -> Union[List[int], None]:
        """ Find permutation between map ranges.
            :param map_entries: List of map entries
            :return: None if no such permutation exists, otherwise a dict
                     that maps each map to a list of
                     indices L such that L[x]'th parameter of
                     each map have the same range.
            """
        result_dict = {}
        first_map = map_entries[0]
        for other_map in map_entries:
            if len(first_map.map.range) != len(other_map.map.range):
                return None

        for other_map in map_entries:
            # Match map ranges with reduce ranges
            result = []
            for i, tmap_rng in enumerate(first_map.map.range):
                found = False
                for j, rng in enumerate(other_map.map.range):
                    if tmap_rng == rng and j not in result:
                        result.append(j)
                        found = True
                        break
                if not found:
                    break
            # Ensure all map ranges matched
            if len(result) != len(first_map.map.range):
                return None
            result_dict[other_map] = result

        return result_dict

    @staticmethod
    def get_adjacent_nodes(sdfg, graph, map_entries):
        ''' For given map entries, finds a set of in, out and intermediate nodes '''
        ### NOTE:
        #- in_nodes, out_nodes, intermediate_nodes refer to the configuration of the final fused map
        #- in_nodes and out_nodes are trivially disjoint
        #- Intermediate_nodes and out_nodes are not necessarily disjoint
        #- Intermediate_nodes and in_nodes are disjoint by design.
        #  There could be a node that has both incoming edges from a map exit
        #  and from outside, but it is just treated as intermediate_node and handled
        #  automatically.

        # Nodes that flow into one or several maps but no data is flowed to them from any map
        in_nodes = set()

        # Nodes into which data is flowed but that no data flows into any map from them
        out_nodes = set()

        # Nodes that act as intermediate node - data flows from a map into them and then there
        # is an outgoing path into another map
        intermediate_nodes = set()

        map_exits = [graph.exit_node(map_entry) for map_entry in map_entries]
        for map_entry, map_exit in zip(map_entries, map_exits):
            for edge in graph.in_edges(map_entry):
                in_nodes.add(edge.src)
            for edge in graph.out_edges(map_exit):
                current_node = edge.dst
                if len(graph.out_edges(current_node)) == 0:
                    out_nodes.add(current_node)
                else:
                    for dst_edge in graph.out_edges(current_node):
                        if dst_edge.dst in map_entries:
                            # add to intermediate_nodes
                            intermediate_nodes.add(current_node)

                        else:
                            # add to out_nodes
                            out_nodes.add(current_node)

        # any intermediate_nodes currently in in_nodes shouldnt be there
        in_nodes -= intermediate_nodes

        for node in intermediate_nodes:
            for e in graph.in_edges(node):
                if e.src not in map_exits:
                    warnings.warn("Nodes between two maps to be"
                                  "fused with *incoming* edges"
                                  "from outside the maps are not"
                                  "allowed yet.")
                    raise NotImplementedError()

        return (in_nodes, intermediate_nodes, out_nodes)

    @staticmethod
    def check_topo_feasibility(sdfg, graph, map_entries, intermediate_nodes,
                               out_nodes):
        ''' Checks whether given map entries have topological structure 
            so that they could be fused 
        '''
        # For each intermediate and out node: must never reach any map
        # entry if it is not connected to map entry immediately

        # for memoization purposes
        visited = set()

        def visit_descendants(graph, node, visited, map_entries):
            # check whether the node has already been processed once
            if node in visited:
                return True
            # check whether the node is in our map entries.
            if node in map_entries:
                return False
            # for every out edge, continue exploring whether
            # we and up at another map entry that is in our set
            for oedge in graph.out_edges(node):
                if not visit_descendants(graph, oedge.dst, visited,
                                         map_entries):
                    return False

            # this node does not lead to any other map entries, add to visited
            visited.add(node)
            return True

        for node in intermediate_nodes | out_nodes:
            # these nodes must not lead to a map entry
            nodes_to_check = set()
            for oedge in graph.out_edges(node):
                if oedge.dst not in map_entries:
                    nodes_to_check.add(oedge.dst)

            for forbidden_node in nodes_to_check:
                if not visit_descendants(graph, forbidden_node, visited,
                                         map_entries):
                    return False

        return True

    @staticmethod
    def get_invariant_dimensions(sdfg, graph, map_entries, map_exits, node):
        '''
        on a non-fused graph, return a set of
        indices that correspond to array dimensions that
        do not change when we are entering maps
        for an intermediate access node
        '''
        variate_dimensions = set()
        subset_length = -1

        for in_edge in graph.in_edges(node):
            if in_edge.src in map_exits:
                other_edge = graph.memlet_path(in_edge)[-2]
                other_subset = other_edge.data.subset \
                               if other_edge.data.data == node.data \
                               else other_edge.data.other_subset

                for (idx, (ssbs1, ssbs2)) \
                    in enumerate(zip(in_edge.data.subset, other_subset)):
                    if ssbs1 != ssbs2:
                        variate_dimensions.add(idx)
            else:
                warnings.warn("Nodes between two maps to be"
                              "fused with *incoming* edges"
                              "from outside the maps are not"
                              "allowed yet.")

            if subset_length < 0:
                subset_length = other_subset.dims()
            else:
                assert other_subset.dims() == subset_length

        for out_edge in graph.out_edges(node):
            if out_edge.dst in map_entries:
                for other_edge in graph.out_edges(out_edge.dst):
                    if other_edge.src_conn[3:] == out_edge.dst_conn[2:]:
                        other_subset = other_edge.data.subset \
                                       if other_edge.data.data == node.data \
                                       else other_edge.data.other_subset
                        for (idx, (ssbs1, ssbs2)) in enumerate(
                                zip(out_edge.data.subset, other_subset)):
                            if ssbs1 != ssbs2:
                                variate_dimensions.add(idx)
                        assert other_subset.dims() == subset_length

        invariant_dimensions = set([i for i in range(subset_length)
                                    ]) - variate_dimensions
        return invariant_dimensions

    def copy_edge(self,
                  graph,
                  edge,
                  new_src=None,
                  new_src_conn=None,
                  new_dst=None,
                  new_dst_conn=None,
                  new_data=None,
                  remove_old=False):
        '''
        Copies an edge going from source to dst.
        If no destination is specified, the edge is copied with the same
        destination and port as the original edge, else the edge is copied
        with the new destination and the new port.
        If no source is specified, the edge is copied with the same
        source and port as the original edge, else the edge is copied
        with the new source and the new port
        If remove_old is specified, the old edge is removed immediately
        If new_data is specified, inserts new_data as a memlet, else
        else makes a deepcopy of the current edges memlet
        '''
        data = new_data if new_data else dcpy(edge.data)
        src = edge.src if new_src is None else new_src
        src_conn = edge.src_conn if new_src is None else new_src_conn
        dst = edge.dst if new_dst is None else new_dst
        dst_conn = edge.dst_conn if new_dst is None else new_dst_conn

        ret = graph.add_edge(src, src_conn, dst, dst_conn, data)

        if remove_old:
            graph.remove_edge(edge)
        '''
        if new_src:
            ret = graph.add_edge(new_src, new_src_conn, edge.dst, edge.dst_conn,
                                 data)
            graph.remove_edge(edge)
        if new_dst:
            ret = graph.add_edge(edge.src, edge.src_conn, new_dst, new_dst_conn,
                                 data)
            graph.remove_edge(edge)
        '''
        return ret

    def adjust_arrays_nsdfg(self, sdfg, nsdfg, name, nname):
        '''
        DFS to replace strides and volumes of data that has adjacent
        nested SDFGs to its access nodes. Needed in a post-processing
        step during fusion.
        '''
        nsdfg.data(nname).strides = dcpy(sdfg.data(name).strides)
        nsdfg.data(nname).total_size = dcpy(sdfg.data(name).total_size)
        # traverse the whole graph and search for arrays
        for ngraph in nsdfg.nodes():
            for nnode in ngraph.nodes():
                if isinstance(nnode, nodes.AccessNode) and nnode.label == nname:
                    # trace and recurse if necessary
                    for e in chain(ngraph.out_edges(nnode),
                                   ngraph.in_edges(nnode)):
                        for te in ngraph.memlet_tree(e):
                            if isinstance(te.dst, nodes.NestedSDFG):
                                self.adjust_arrays_nsdfg(
                                    nsdfg, te.dst.sdfg, nname, te.dst_conn)
                            if isinstance(te.src, nodes.NestedSDFG):
                                self.adjust_arrays_nsdfg(
                                    nsdfg, te.src.sdfg, nname, te.src_conn)

    def prepare_intermediate_nodes(self,
                                   sdfg,
                                   graph,
                                   in_nodes,
                                   out_nodes,
                                   intermediate_nodes,
                                   map_entries,
                                   map_exits,
                                   do_not_override=[]):
        ''' For every interemediate node, determines whether
        it is fully contained in the subgraph and whether it has
        any out connections and thus transients need to be created
        '''
        def redirect(redirect_node, original_node):
            # redirect all outgoing traffic which
            # does not enter fusion scope again
            # from original_node to redirect_node
            # and then create a path from original_node to redirect_node.

            edges = list(graph.out_edges(original_node))
            for edge in edges:
                if edge.dst not in map_entries:
                    self.copy_edge(graph,
                                   edge,
                                   new_src=redirect_node,
                                   remove_old=True)

            graph.add_edge(original_node, None, redirect_node, None, Memlet())

        # first search whether intermediate_nodes appear outside of subgraph
        # and store it in dict
        data_counter = defaultdict(int)
        data_counter_subgraph = defaultdict(int)

        data_intermediate = set([node.data for node in intermediate_nodes])

        # do a full global search and count each data from each intermediate node
        scope_dict = graph.scope_dict()
        for state in sdfg.nodes():
            for node in state.nodes():
                if isinstance(
                        node,
                        nodes.AccessNode) and node.data in data_intermediate:
                    # add them to the counter set in all cases
                    data_counter[node.data] += 1
                    # see whether we are inside the subgraph scope
                    # if so, add to data_counter_subgraph
                    # DO NOT add if it is in out_nodes
                    if state == graph and \
                       (node in intermediate_nodes or scope_dict[node] in map_entries):
                        data_counter_subgraph[node.data] += 1

        # next up: If intermediate_counter and global counter match and if the array
        # is declared transient, it is fully contained by the subgraph

        subgraph_contains_data = {data: data_counter[data] == data_counter_subgraph[data] \
                                        and sdfg.data(data).transient \
                                        and data not in do_not_override \
                                  for data in data_intermediate}

        transients_created = {}
        for node in intermediate_nodes & out_nodes:
            # create new transient at exit replacing the array
            # and redirect all traffic
            data_ref = sdfg.data(node.data)
            out_trans_data_name = node.data + '_OUT'
            data_trans = sdfg.add_transient(name=out_trans_data_name,
                                            shape=dcpy(data_ref.shape),
                                            dtype=dcpy(data_ref.dtype),
                                            storage=dcpy(data_ref.storage),
                                            offset=dcpy(data_ref.offset))
            node_trans = graph.add_access(out_trans_data_name)
            if node.setzero:
                node_trans.setzero = True
            redirect(node_trans, node)
            transients_created[node] = node_trans

        # finally, create dict for every array that for which
        # subgraph_contains_data is true that lists invariant axes.
        invariant_dimensions = {}
        for node in intermediate_nodes:
            data = node.data
            inv_dims = SubgraphFusion.get_invariant_dimensions(
                sdfg, graph, map_entries, map_exits, node)
            if node in invariant_dimensions:
                # do a check -- we want the same result for each
                # node containing the same data
                if not inv_dims == invariant_dimensions[node]:
                    warnings.warn(
                        f"WARNING: Data dimensions that are not propagated through differ"
                        "across multiple instances of access nodes for data {node.data}"
                        "Please check whether all memlets to AccessNodes containing"
                        "this data are sound.")
                    invariant_dimensions[data] |= inv_dims

            else:
                invariant_dimensions[data] = inv_dims

        return (subgraph_contains_data, transients_created,
                invariant_dimensions)

    def apply(self, sdfg, do_not_override=None, **kwargs):
        subgraph = self.subgraph_view(sdfg)
        graph = subgraph.graph

        map_entries = helpers.get_outermost_scope_maps(sdfg, graph, subgraph)
        self.fuse(sdfg, graph, map_entries, do_not_override, **kwargs)

    def fuse(self, sdfg, graph, map_entries, do_not_override=None, **kwargs):
        """ takes the map_entries specified and tries to fuse maps.

            all maps have to be extended into outer and inner map
            (use MapExpansion as a pre-pass)

            Arrays that don't exist outside the subgraph get pushed
            into the map and their data dimension gets cropped.
            Otherwise the original array is taken.

            For every output respective connections are crated automatically.

            :param sdfg: SDFG
            :param graph: State
            :param map_entries: Map Entries (class MapEntry) of the outer maps
                                which we want to fuse
            :param do_not_override: List of data names whose corresponding nodes
                                    are fully contained within the subgraph
                                    but should not be augmented/transformed
                                    nevertheless.
        """

        # if there are no maps, return immediately
        if len(map_entries) == 0:
            return

        do_not_override = do_not_override or []

        # get maps and map exits
        maps = [map_entry.map for map_entry in map_entries]
        map_exits = [graph.exit_node(map_entry) for map_entry in map_entries]

        # See function documentation for an explanation of these variables
        node_config = SubgraphFusion.get_adjacent_nodes(sdfg, graph,
                                                        map_entries)
        (in_nodes, intermediate_nodes, out_nodes) = node_config

        if self.debug:
            print("SubgraphFusion::In_nodes", in_nodes)
            print("SubgraphFusion::Out_nodes", out_nodes)
            print("SubgraphFusion::Intermediate_nodes", intermediate_nodes)

        # all maps are assumed to have the same params and range in order
        global_map = nodes.Map(label="outer_fused",
                               params=maps[0].params,
                               ndrange=maps[0].range)
        global_map_entry = nodes.MapEntry(global_map)
        global_map_exit = nodes.MapExit(global_map)

        schedule = map_entries[0].schedule
        global_map_entry.schedule = schedule
        graph.add_node(global_map_entry)
        graph.add_node(global_map_exit)

        # next up, for any intermediate node, find whether it only appears
        # in the subgraph or also somewhere else / as an input
        # create new transients for nodes that are in out_nodes and
        # intermediate_nodes simultaneously
        # also check which dimensions of each transient data element correspond
        # to map axes and write this information into a dict.
        node_info = self.prepare_intermediate_nodes(sdfg, graph, in_nodes, out_nodes, \
                                                    intermediate_nodes,\
                                                    map_entries, map_exits, \
                                                    do_not_override)

        (subgraph_contains_data, transients_created,
         invariant_dimensions) = node_info
        if self.debug:
            print(
                "SubgraphFusion:: {Intermediate_node: subgraph_contains_data} dict"
            )
            print(subgraph_contains_data)

        inconnectors_dict = {}
        # Dict for saving incoming nodes and their assigned connectors
        # Format: {access_node: (edge, in_conn, out_conn)}

        for map_entry, map_exit in zip(map_entries, map_exits):
            # handle inputs
            # TODO: dynamic map range -- this is fairly unrealistic in such a setting
            for edge in graph.in_edges(map_entry):
                src = edge.src
                mmt = graph.memlet_tree(edge)
                out_edges = [child.edge for child in mmt.root().children]

                if src in in_nodes:
                    in_conn = None
                    out_conn = None
                    if src in inconnectors_dict:
                        # no need to augment subset of outer edge.
                        # will do this at the end in one pass.

                        in_conn = inconnectors_dict[src][1]
                        out_conn = inconnectors_dict[src][2]

                    else:
                        next_conn = global_map_entry.next_connector()
                        in_conn = 'IN_' + next_conn
                        out_conn = 'OUT_' + next_conn
                        global_map_entry.add_in_connector(in_conn)
                        global_map_entry.add_out_connector(out_conn)

                        inconnectors_dict[src] = (edge, in_conn, out_conn)

                        # reroute in edge via global_map_entry
                        self.copy_edge(graph, edge, new_dst = global_map_entry, \
                                                        new_dst_conn = in_conn)

                    # map out edges to new map
                    for out_edge in out_edges:
                        self.copy_edge(graph, out_edge, new_src = global_map_entry, \
                                                            new_src_conn = out_conn)

                else:
                    # connect directly
                    for out_edge in out_edges:
                        mm = dcpy(out_edge.data)
                        self.copy_edge(graph,
                                       out_edge,
                                       new_src=src,
                                       new_src_conn=None,
                                       new_data=mm)

            for edge in graph.out_edges(map_entry):
                # special case: for nodes that have no data connections
                if not edge.src_conn:
                    self.copy_edge(graph, edge, new_src=global_map_entry)

            ######################################

            for edge in graph.in_edges(map_exit):
                if not edge.dst_conn:
                    # no destination connector, path ends here.
                    self.copy_edge(graph, edge, new_dst=global_map_exit)
                    continue
                # find corresponding out_edges for current edge, cannot use mmt anymore
                out_edges = [
                    oedge for oedge in graph.out_edges(map_exit)
                    if oedge.src_conn[3:] == edge.dst_conn[2:]
                ]

                # Tuple to store in/out connector port that might be created
                port_created = None

                for out_edge in out_edges:
                    dst = out_edge.dst

                    if dst in intermediate_nodes & out_nodes:

                        # create connection through global map from
                        # dst to dst_transient that was created
                        dst_transient = transients_created[dst]
                        next_conn = global_map_exit.next_connector()
                        in_conn = 'IN_' + next_conn
                        out_conn = 'OUT_' + next_conn
                        global_map_exit.add_in_connector(in_conn)
                        global_map_exit.add_out_connector(out_conn)

                        # for each transient created, create a union
                        # of outgoing memlets' subsets. this is
                        # a cheap fix to override assignments in invariant
                        # dimensions
                        union = None
                        for oe in graph.out_edges(transients_created[dst]):
                            union = subsets.union(union, oe.data.subset)
                        inner_memlet = dcpy(edge.data)
                        for i, s in enumerate(edge.data.subset):
                            if i in invariant_dimensions[dst.label]:
                                inner_memlet.subset[i] = union[i]

                        inner_memlet.other_subset = dcpy(inner_memlet.subset)

                        e_inner = graph.add_edge(dst, None, global_map_exit,
                                                 in_conn, inner_memlet)
                        mm_outer = propagate_memlet(graph, inner_memlet, global_map_entry, \
                                                    union_inner_edges = False)

                        e_outer = graph.add_edge(global_map_exit, out_conn,
                                                 dst_transient, None, mm_outer)

                        # remove edge from dst to dst_transient that was created
                        # in intermediate preparation.
                        for e in graph.out_edges(dst):
                            if e.dst == dst_transient:
                                graph.remove_edge(e)
                                break

                    # handle separately: intermediate_nodes and pure out nodes
                    # case 1: intermediate_nodes: can just redirect edge
                    if dst in intermediate_nodes:
                        self.copy_edge(graph,
                                       out_edge,
                                       new_src=edge.src,
                                       new_src_conn=edge.src_conn,
                                       new_data=dcpy(edge.data))

                    # case 2: pure out node: connect to outer array node
                    if dst in (out_nodes - intermediate_nodes):
                        if edge.dst != global_map_exit:
                            next_conn = global_map_exit.next_connector()
                            in_conn = 'IN_' + next_conn
                            out_conn = 'OUT_' + next_conn
                            global_map_exit.add_in_connector(in_conn)
                            global_map_exit.add_out_connector(out_conn)
                            self.copy_edge(graph,
                                           edge,
                                           new_dst=global_map_exit,
                                           new_dst_conn=in_conn)
                            port_created = (in_conn, out_conn)

                        else:
                            conn_nr = edge.dst_conn[3:]
                            in_conn = port_created.st
                            out_conn = port_created.nd

                        # map
                        graph.add_edge(global_map_exit, out_conn, dst, None,
                                       dcpy(out_edge.data))

            # maps are now ready to be discarded
            # all connected edges will be finally removed as well
            graph.remove_node(map_entry)
            graph.remove_node(map_exit)

        # create a mapping from data arrays to offsets
        # for later memlet adjustments later
        min_offsets = dict()

        # do one pass to augment all transient arrays
        data_intermediate = set([node.data for node in intermediate_nodes])
        for data_name in data_intermediate:
            if subgraph_contains_data[data_name]:
                all_nodes = [
                    n for n in intermediate_nodes if n.data == data_name
                ]
                in_edges = list(chain(*(graph.in_edges(n) for n in all_nodes)))

                in_edges_iter = iter(in_edges)
                in_edge = next(in_edges_iter)
                target_subset = dcpy(in_edge.data.subset)
                target_subset.pop(invariant_dimensions[data_name])
                ######
                while True:
                    try:  # executed if there are multiple in_edges
                        in_edge = next(in_edges_iter)
                        target_subset_curr = dcpy(in_edge.data.subset)
                        target_subset_curr.pop(invariant_dimensions[data_name])
                        target_subset = subsets.union(target_subset, \
                                                      target_subset_curr)
                    except StopIteration:
                        break

                min_offsets_cropped = target_subset.min_element_approx()
                # calculate the new transient array size.
                target_subset.offset(min_offsets_cropped, True)

                # re-add invariant dimensions with offset 0 and save to min_offsets
                min_offset = []
                index = 0
                for i in range(len(sdfg.data(data_name).shape)):
                    if i in invariant_dimensions[data_name]:
                        min_offset.append(0)
                    else:
                        min_offset.append(min_offsets_cropped[index])
                        index += 1

                min_offsets[data_name] = min_offset

                # determine the shape of the new array.
                new_data_shape = []
                index = 0
                for i, sz in enumerate(sdfg.data(data_name).shape):
                    if i in invariant_dimensions[data_name]:
                        new_data_shape.append(sz)
                    else:
                        new_data_shape.append(target_subset.size()[index])
                        index += 1

                new_data_strides = [
                    data._prod(new_data_shape[i + 1:])
                    for i in range(len(new_data_shape))
                ]

                new_data_totalsize = data._prod(new_data_shape)
                new_data_offset = [0] * len(new_data_shape)
                # augment.
                transient_to_transform = sdfg.data(data_name)
                transient_to_transform.shape = new_data_shape
                transient_to_transform.strides = new_data_strides
                transient_to_transform.total_size = new_data_totalsize
                transient_to_transform.offset = new_data_offset
                transient_to_transform.lifetime = dtypes.AllocationLifetime.Scope
                transient_to_transform.storage = self.transient_allocation

            else:
                # don't modify data container - array is needed outside
                # of subgraph.

                # hack: set lifetime to State if allocation has only been
                # scope so far to avoid allocation issues
                if sdfg.data(
                        data_name).lifetime == dtypes.AllocationLifetime.Scope:
                    sdfg.data(
                        data_name).lifetime = dtypes.AllocationLifetime.State

        # do one pass to adjust and the memlets of in-between transients
        for node in intermediate_nodes:
            # all incoming edges to node
            in_edges = graph.in_edges(node)
            # outgoing edges going to another fused part
            out_edges = graph.out_edges(node)

            # memlets of created transient:
            # correct data names
            if node in transients_created:
                transient_in_edges = graph.in_edges(transients_created[node])
                transient_out_edges = graph.out_edges(transients_created[node])
                for edge in chain(transient_in_edges, transient_out_edges):
                    for e in graph.memlet_tree(edge):
                        if e.data.data == node.data:
                            e.data.data += '_OUT'

            # memlets of all in between transients:
            # offset memlets if array has been augmented
            if subgraph_contains_data[node.data]:
                # get min_offset
                min_offset = min_offsets[node.data]
                # re-add invariant dimensions with offset 0
                for iedge in in_edges:
                    for edge in graph.memlet_tree(iedge):
                        if edge.data.data == node.data:
                            edge.data.subset.offset(min_offset, True)
                        elif edge.data.other_subset:
                            edge.data.other_subset.offset(min_offset, True)
                    # nested SDFG: adjust arrays connected
                    if isinstance(iedge.src, nodes.NestedSDFG):
                        nsdfg = iedge.src.sdfg
                        nested_data_name = edge.src_conn
                        self.adjust_arrays_nsdfg(sdfg, nsdfg, node.data,
                                                 nested_data_name)

                for cedge in out_edges:
                    for edge in graph.memlet_tree(cedge):
                        if edge.data.data == node.data:
                            edge.data.subset.offset(min_offset, True)
                        elif edge.data.other_subset:
                            edge.data.other_subset.offset(min_offset, True)
                        # nested SDFG: adjust arrays connected
                        if isinstance(edge.dst, nodes.NestedSDFG):
                            nsdfg = edge.dst.sdfg
                            nested_data_name = edge.dst_conn
                            self.adjust_arrays_nsdfg(sdfg, nsdfg, node.data,
                                                     nested_data_name)

                # if in_edges has several entries:
                # put other_subset into out_edges for correctness
                if len(in_edges) > 1:
                    for oedge in out_edges:
                        if oedge.dst == global_map_exit and \
                                            oedge.data.other_subset is None:
                            oedge.data.other_subset = dcpy(oedge.data.subset)
                            oedge.data.other_subset.offset(min_offset, True)

        # consolidate edges if desired
        if self.consolidate:
            consolidate_edges_scope(graph, global_map_entry)
            consolidate_edges_scope(graph, global_map_exit)

        # propagate edges adjacent to global map entry and exit
        # if desired
        if self.propagate:
            _propagate_node(graph, global_map_entry)
            _propagate_node(graph, global_map_exit)

        # create a hook for outside access to global_map
        self._global_map_entry = global_map_entry
        if self.schedule_innermaps is not None:
            for node in graph.scope_children()[global_map_entry]:
                if isinstance(node, nodes.MapEntry):
                    node.map.schedule = self.schedule_innermaps
