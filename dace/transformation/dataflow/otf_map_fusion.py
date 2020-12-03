# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" Contains classes that implement the OnTheFlyMapFusion transformation. """

from dace import registry, symbol, dtypes, propagate_memlets_sdfg
from dace.subsets import union_of_list
from dace.sdfg import nodes
from dace.sdfg import utils as sdutil
from dace.transformation import transformation
from dace.properties import make_properties
from functools import reduce
from operator import mul

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

        # Check that locally provided buffer has volume 1.
        for edge in graph.in_edges(map1_exit):
            if edge.data.volume != 1:
                return False

        # Check that all locally provided buffers have the same subset.
        subsets = set(edge.data.subset for edge in graph.in_edges(map1_exit))
        if len(subsets) != 1:
            return False

        # Check existance of buffers
        buffers = graph.all_nodes_between(map1_exit, map2_entry)
        if buffers is None:
            return False

        for buffer in buffers:
            # Check that buffers are AccessNodes.
            if not isinstance(buffer, nodes.AccessNode):
                return False

            # Check that buffers are transient.
            if not sdfg.arrays[buffer.data].transient:
                return False
            
            # Check that buffers have exactly 1 input- and 1 output edge.
            if graph.in_degree(buffer) != 1:
                return False
            if graph.out_degree(buffer) != 1:
                return False

            # Check that the data consumed is provided.
            provided = graph.in_edges(buffer)[0].data.subset
            consumed = graph.out_edges(buffer)[0].data.subset
            if not provided.covers(consumed):
                return False

            # Check that buffers occure only once in this state.
            num_occurrences = len([
                    n for n in graph.nodes()
                    if isinstance(n, nodes.AccessNode) and n.data == buffer
                ])
            if num_occurrences > 1:
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
        buffers = graph.all_nodes_between(map1_exit, map2_entry)

        locally_consumed_buffer = []
        for buffer in buffers:
            out_edge = graph.out_edges(buffer)[0]
            path = graph.memlet_path(out_edge)
            locally_consumed_buffer.append(path[path.index(out_edge) + 1].data.subset)
        locally_consumed_buffer = union_of_list(locally_consumed_buffer)

        locally_provided_buffer = set(edge.data.subset for edge in graph.in_edges(map1_exit))
        assert len(locally_provided_buffer) == 1
        locally_provided_buffer = locally_provided_buffer.pop()

        # Remove map2_entry from the buffers memlet path.
        for buffer in buffers:
            outer_edge = graph.out_edges(buffer)[0]
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
        old_params = [str(p[0]) for p in locally_provided_buffer.ranges]
        new_params = ['a', 'b', 'c', 'd'][:len(locally_consumed_buffer.ranges)]
        map1_entry.params = new_params
        map1_entry.schedule = dtypes.ScheduleType.Default

        scope = graph.scope_subgraph(map1_entry)
        for o, n, r in zip(old_params, new_params, locally_consumed_buffer.ranges):
            scope.replace(o, n + '+' + str(r[0]))

        map1_entry.range = [(0, r[1]-r[0],r[2]) for r in locally_consumed_buffer.ranges]

        # adjust locally_provided_buffer memlets
        for edge in graph.in_edges(map1_exit):
            edge.data.subset.ranges = [(r[0]-c[0],r[1]-c[0],r[2]) for r, c in zip(edge.data.subset.ranges, locally_consumed_buffer.ranges)]

        # adjust buffer properties
        for buffer in buffers:
            arr = sdfg.arrays[buffer.data]
            arr.shape = tuple(upper - lower + 1 for lower, upper, _ in locally_consumed_buffer.ranges)
            arr.strides = tuple(prod(arr.shape[:i]) for i in range(len(arr.shape)))
            arr.total_size = prod(arr.shape)

        propagate_memlets_sdfg(sdfg)

        # offset buffer memlets
        for buffer in buffers:
            out_edge = graph.out_edges(buffer)[0]
            out_edge.data.subset.ranges = [(this[0]-total[0], this[1]-total[0], this[2])
                for this, total in zip(out_edge.data.subset.ranges, locally_consumed_buffer)]

