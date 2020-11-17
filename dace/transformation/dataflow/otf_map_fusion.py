# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" Contains classes that implement the OnTheFlyMapFusion transformation. """

import copy
from dace import registry, symbol, dtypes
from dace.subsets import Range
from dace.sdfg import nodes
from dace.sdfg import utils as sdutil
from dace.transformation import transformation
from dace.properties import make_properties
from dace.codegen.targets.unroller import *

dace.ScheduleType.register('Unrolled')
dace.SCOPEDEFAULT_SCHEDULE[dace.ScheduleType.Unrolled] = dace.ScheduleType.Sequential
dace.SCOPEDEFAULT_STORAGE[dace.ScheduleType.Unrolled] = dace.StorageType.CPU_Heap

@registry.autoregister_params(singlestate=True)
class OnTheFlyMapFusion(transformation.Transformation):

    _first_exit = nodes.MapExit(nodes.Map('', [], []))
    _array = nodes.AccessNode('')
    _second_entry = nodes.MapEntry(nodes.Map('', [], []))

    # Returns a list of graphs that represent the pattern
    @staticmethod
    def expressions():
        return [
            sdutil.node_path_graph(
                OnTheFlyMapFusion._first_exit,
                OnTheFlyMapFusion._array,
                OnTheFlyMapFusion._second_entry,
            )
        ]

    @staticmethod
    def can_be_applied(graph, candidate, expr_index, sdfg, strict=False):
        first_exit = graph.nodes()[candidate[OnTheFlyMapFusion._first_exit]]
        first_entry = graph.entry_node(first_exit)
        second_entry = graph.nodes()[candidate[OnTheFlyMapFusion._second_entry]]

        # Check that all memlets to first_exit have volume 1.
        for edge in graph.in_edges(first_exit):
            if edge.data.volume != 1:
                return False

        # Check that all memlets to first_exit have the same subset.
        subsets = set(edge.data.subset for edge in graph.in_edges(first_exit))
        if len(subsets) != 1:
            return False

        intermediate_nodes = graph.all_nodes_between(first_exit, second_entry)
        if intermediate_nodes is None:
            return False

        for node in intermediate_nodes:
            # Check that intermediate nodes are AccessNodes.
            if not isinstance(node, nodes.AccessNode):
                return False

            # Check that intermediate nodes are transient.
            if not sdfg.arrays[node.data].transient:
                return False
            
            # Check that intermediate nodes have exactly 1 input and 1 output.
            if graph.in_degree(node) != 1:
                return False
            if graph.out_degree(node) != 1:
                return False

            # Check that the date consumed is provided.
            provided = graph.in_edges(node)[0].data.subset
            consumed = graph.out_edges(node)[0].data.subset
            if not provided.covers(consumed):
                return False

            # Check that intermediate nodes occure only once in this state.
            num_occurrences = len([
                    n for n in graph.nodes()
                    if isinstance(n, nodes.AccessNode) and n.data == node
                ])
            if num_occurrences > 1:
                return False

        # Check that the memlets from second_entry all have the same range.
        ranges = set()
        for node in intermediate_nodes:
            edge = graph.out_edges(node)[0]
            path = graph.memlet_path(edge)
            ranges.add(path[path.index(edge) + 1].data.subset)
        if len(ranges) != 1:
            return False


            # # Get the subset of the first map memlet
            # for edge in graph.out_edges(first_exit):
            #     if node.data == edge.data.data:
            #         locally_provided_subset = edge.data.subset

            # begins = {symbol(sym):r[0] for sym, r in zip(first_entry.params, first_entry.range.ranges)}
            # ends = {symbol(sym):r[1] for sym, r in zip(first_entry.params, first_entry.range.ranges)}
            # begin_of_provided_ranges = copy.deepcopy(locally_provided_subset)
            # begin_of_provided_ranges.replace(begins)
            # end_of_provided_ranges = copy.deepcopy(locally_provided_subset)
            # end_of_provided_ranges.replace(ends)
            # globally_provided_subset = Range((begin,end,1) for begin,end in zip(begin_of_provided_ranges.ranges, end_of_provided_ranges.ranges))

            # # Get the subset of the second map memlet
            # for edge in graph.out_edges(second_entry):
            #     if node.data == edge.data.data:
            #         locally_consumed_subset = edge.data.subset

            # begins = {symbol(sym):r[0] for sym, r in zip(second_entry.params, second_entry.range.ranges)}
            # ends = {symbol(sym):r[1] for sym, r in zip(second_entry.params, second_entry.range.ranges)}
            # begin_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
            # begin_of_consumed_ranges.replace(begins)
            # end_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
            # end_of_consumed_ranges.replace(ends)
            # globally_consumed_subset = Range((begin,end,1) for begin,end in zip(begin_of_consumed_ranges.ranges, end_of_consumed_ranges.ranges))

            # # Check that intermediate nodes provide the consumed data through the memlet.
            # if not globally_provided_subset.covers(globally_consumed_subset):
            #     return False

        return True

    @staticmethod
    def match_to_str(graph, candidate):
        first_exit = graph.nodes()[candidate[OnTheFlyMapFusion._first_exit]]
        second_entry = graph.nodes()[candidate[OnTheFlyMapFusion._second_entry]]

        return " -> ".join(entry.map.label + ": " + str(entry.map.params)
                           for entry in [first_exit, second_entry])

    def apply(self, sdfg):
        graph = sdfg.nodes()[self.state_id]
        first_exit = graph.nodes()[self.subgraph[self._first_exit]]
        first_entry = graph.entry_node(first_exit)
        second_entry = graph.nodes()[self.subgraph[self._second_entry]]
        second_exit = graph.exit_node(second_entry)
        
        intermediate_nodes = graph.all_nodes_between(first_exit, second_entry)

        ranges = set()
        for node in intermediate_nodes:
            edge = graph.out_edges(node)[0]
            path = graph.memlet_path(edge)
            ranges.add(path[path.index(edge) + 1].data.subset)
        assert len(ranges) == 1
        otf_range = ranges.pop()

        subsets = set(edge.data.subset for edge in graph.in_edges(first_exit))
        assert len(subsets) == 1
        subset = subsets.pop()

        # Remove second_entry from the intermediate_nodes memlet path.
        for node in intermediate_nodes:
            sdfg.arrays[node.data].shape = tuple(upper - lower + 1 for lower, upper, _ in otf_range.ranges)
            outer_edge = graph.out_edges(node)[0]
            path = graph.memlet_path(outer_edge)
            inner_edge = path[path.index(outer_edge) + 1]

            graph.remove_edge(outer_edge)
            graph.remove_edge(inner_edge)
            second_entry.remove_in_connector(outer_edge.dst_conn)
            second_entry.remove_out_connector(inner_edge.src_conn)
            # Add a direct edge
            graph.add_edge(outer_edge.src, outer_edge.src_conn, inner_edge.dst, inner_edge.dst_conn, inner_edge.data)


        # Put second_entry into memlet path of first_entry's in_edges.
        for edge in graph.in_edges(first_entry):
            graph.remove_edge(edge)
            graph.add_memlet_path(edge.src,
                                second_entry,
                                edge.dst,
                                src_conn=edge.src_conn,
                                memlet=edge.data,
                                dst_conn=edge.dst_conn)

        old_params = [str(r[0]) for r in subset.ranges]
        new_params = ['a','b','c','d']
        first_entry.params = new_params
        first_entry.schedule = dtypes.ScheduleType.Unrolled

        scope = graph.scope_subgraph(first_entry)
        for o, n in zip(old_params, new_params):
            scope.replace(o, n)

        first_entry.range = otf_range

        # # Delete the edges from intermediate_nodes to the second_entry and the in_connectors.
        # edges = [edge for node in intermediate_nodes for edge in graph.out_edges(node)]
        # for edge in edges:
        #     edge.dst.remove_in_connector(edge.dst_conn)
        #     graph.remove_edge(edge)

        # # Redirect the out_edges of second_entry.
        # for edge in graph.out_edges(second_entry):


        # # Intercept the in_edges of first_enty by second_entry.
        # for edge in graph.in_edges(first_entry):
        #     edge.dst = second_entry



        # Change the range of the first_entry.
        # TODO

        # for node in intermediate_nodes:
        #     # Get the subset of the second map memlet
        #     for edge in graph.out_edges(second_entry):
        #         if node.data == edge.data.data:
        #             locally_consumed_subset = edge.data.subset

        #     begins = {symbol(sym):r[0] for sym, r in zip(second_entry.params, second_entry.range.ranges)}
        #     ends = {symbol(sym):r[1] for sym, r in zip(second_entry.params, second_entry.range.ranges)}
        #     begin_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
        #     begin_of_consumed_ranges.replace(begins)
        #     end_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
        #     end_of_consumed_ranges.replace(ends)
        #     globally_consumed_subset = Range((begin,end,1) for begin,end in zip(begin_of_consumed_ranges.ranges, end_of_consumed_ranges.ranges))

        # for node in intermediate_nodes:
        #     for edge in graph.out_edges(second_entry):
        #         break

        # novum_entry, novum_exit = graph.add_map(str(first_entry), str(biggest_range))



