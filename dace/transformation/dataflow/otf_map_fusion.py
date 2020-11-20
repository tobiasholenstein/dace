# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" Contains classes that implement the OnTheFlyMapFusion transformation. """

import copy
from functools import reduce
from operator import mul
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

def prod(iterable):
    return reduce(mul, iterable, 1)

@registry.autoregister_params(singlestate=True)
class OnTheFlyMapFusion(transformation.Transformation):

    _map1_exit = nodes.MapExit(nodes.Map('', [], []))
    _array = nodes.AccessNode('')
    _map2_entry = nodes.MapEntry(nodes.Map('', [], []))

    # Returns a list of graphs that represent the pattern
    @staticmethod
    def expressions():
        return [
            sdutil.node_path_graph(
                OnTheFlyMapFusion._map1_exit,
                OnTheFlyMapFusion._array,
                OnTheFlyMapFusion._map2_entry,
            )
        ]

    @staticmethod
    def can_be_applied(graph, candidate, expr_index, sdfg, strict=False):
        map1_exit = graph.nodes()[candidate[OnTheFlyMapFusion._map1_exit]]
        map2_entry = graph.nodes()[candidate[OnTheFlyMapFusion._map2_entry]]

        # Check that all memlets to map1_exit have volume 1.
        for edge in graph.in_edges(map1_exit):
            if edge.data.volume != 1:
                return False

        # Check that all memlets to map1_exit have the same subset.
        subsets = set(edge.data.subset for edge in graph.in_edges(map1_exit))
        if len(subsets) != 1:
            return False

        caches = graph.all_nodes_between(map1_exit, map2_entry)
        if caches is None:
            return False

        for cache in caches:
            # Check that caches are AccessNodes.
            if not isinstance(cache, nodes.AccessNode):
                return False

            # Check that caches are transient.
            if not sdfg.arrays[cache.data].transient:
                return False
            
            # Check that caches have exactly 1 input and 1 output.
            if graph.in_degree(cache) != 1:
                return False
            if graph.out_degree(cache) != 1:
                return False

            # Check that the date consumed is provided.
            provided = graph.in_edges(cache)[0].data.subset
            consumed = graph.out_edges(cache)[0].data.subset
            if not provided.covers(consumed):
                return False

            # Check that caches occure only once in this state.
            num_occurrences = len([
                    n for n in graph.nodes()
                    if isinstance(n, nodes.AccessNode) and n.data == cache
                ])
            if num_occurrences > 1:
                return False

        # Check that the memlets from map2_entry all have the same range.
        ranges = set()
        for cache in caches:
            edge = graph.out_edges(cache)[0]
            path = graph.memlet_path(edge)
            ranges.add(path[path.index(edge) + 1].data.subset)
        if len(ranges) != 1:
            return False

        return True

    @staticmethod
    def match_to_str(graph, candidate):
        map1_exit = graph.nodes()[candidate[OnTheFlyMapFusion._map1_exit]]
        map2_entry = graph.nodes()[candidate[OnTheFlyMapFusion._map2_entry]]

        return " -> ".join(entry.map.label + ": " + str(entry.map.params)
                           for entry in [map1_exit, map2_entry])

    def apply(self, sdfg):
        graph = sdfg.nodes()[self.state_id]
        map1_exit = graph.nodes()[self.subgraph[self._map1_exit]]
        map1_entry = graph.entry_node(map1_exit)
        map2_entry = graph.nodes()[self.subgraph[self._map2_entry]]
        
        caches = graph.all_nodes_between(map1_exit, map2_entry)

        locally_consumed_cache = set()
        globally_consumed_cache = set()
        for cache in caches:
            out_edge = graph.out_edges(cache)[0]
            path = graph.memlet_path(out_edge)
            locally_consumed_cache.add(path[path.index(out_edge) + 1].data.subset)
            globally_consumed_cache.add(out_edge.data.subset)
        assert len(locally_consumed_cache) == 1
        assert len(globally_consumed_cache) == 1
        locally_consumed_cache = locally_consumed_cache.pop() # the range that is consumed in the second map
        globally_consumed_cache = globally_consumed_cache.pop() # the range that is consumed in the second map

        # TODO: Remove?
        locally_provided_cache = set(edge.data.subset for edge in graph.in_edges(map1_exit))
        assert len(locally_provided_cache) == 1
        locally_provided_cache = locally_provided_cache.pop()

        # Remove map2_entry from the caches memlet path.
        for cache in caches:
            outer_edge = graph.out_edges(cache)[0]
            path = graph.memlet_path(outer_edge)
            inner_edge = path[path.index(outer_edge) + 1]

            graph.remove_edge(outer_edge)
            graph.remove_edge(inner_edge)
            map2_entry.remove_in_connector(outer_edge.dst_conn)
            map2_entry.remove_out_connector(inner_edge.src_conn)

            # Add a direct edge
            graph.add_edge(outer_edge.src, outer_edge.src_conn, inner_edge.dst, inner_edge.dst_conn, inner_edge.data)

        # Put map2_entry into memlet path of map1_entry's in_edges.
        for edge in graph.in_edges(map1_entry):
            graph.remove_edge(edge)
            graph.add_memlet_path(edge.src,
                                map2_entry,
                                edge.dst,
                                src_conn=edge.src_conn,
                                memlet=edge.data,
                                dst_conn=edge.dst_conn)

        # Replace parameters in scope of map1.
        old_params = [str(p) for p in map1_entry.params]
        new_params = ['a', 'b', 'c', 'd']
        map1_entry.params = new_params
        map1_entry.schedule = dtypes.ScheduleType.Unrolled

        scope = graph.scope_subgraph(map1_entry)
        for o, n in zip(old_params, new_params):
            scope.replace(o, n)

        map1_entry.range = locally_consumed_cache.ranges

        # adjust cache properties
        for cache in caches:
            arr = sdfg.arrays[cache.data]
            arr.shape = tuple(upper - lower + 1 for lower, upper, _ in locally_consumed_cache.ranges)
            arr.strides = tuple(prod(arr.shape[:i]) for i in range(len(arr.shape)))
            arr.total_size = prod(arr.shape)

        # dace.propagate_memlets_sdfg(sdfg)

        # # Delete the edges from caches to the map2_entry and the in_connectors.
        # edges = [edge for node in caches for edge in graph.out_edges(node)]
        # for edge in edges:
        #     edge.dst.remove_in_connector(edge.dst_conn)
        #     graph.remove_edge(edge)

        # # Redirect the out_edges of map2_entry.
        # for edge in graph.out_edges(map2_entry):


        # # Intercept the in_edges of first_enty by map2_entry.
        # for edge in graph.in_edges(map1_entry):
        #     edge.dst = map2_entry



        # Change the range of the map1_entry.
        # TODO

        # for node in caches:
        #     # Get the subset of the second map memlet
        #     for edge in graph.out_edges(map2_entry):
        #         if node.data == edge.data.data:
        #             locally_consumed_subset = edge.data.subset

        #     begins = {symbol(sym):r[0] for sym, r in zip(map2_entry.params, map2_entry.range.ranges)}
        #     ends = {symbol(sym):r[1] for sym, r in zip(map2_entry.params, map2_entry.range.ranges)}
        #     begin_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
        #     begin_of_consumed_ranges.replace(begins)
        #     end_of_consumed_ranges = copy.deepcopy(locally_consumed_subset)
        #     end_of_consumed_ranges.replace(ends)
        #     globally_consumed_subset = Range((begin,end,1) for begin,end in zip(begin_of_consumed_ranges.ranges, end_of_consumed_ranges.ranges))

        # for node in caches:
        #     for edge in graph.out_edges(map2_entry):
        #         break

        # novum_entry, novum_exit = graph.add_map(str(map1_entry), str(biggest_range))



