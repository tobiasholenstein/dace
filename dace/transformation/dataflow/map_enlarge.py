# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" Contains classes that implement the map enlarge transformation. """

import dace.data
from dace import registry, SDFG, InterstateEdge
from dace.sdfg import nodes
from dace.sdfg import utils as sdutil
from dace.sdfg.graph import SubgraphView
from dace.transformation import transformation, helpers
from dace.properties import make_properties, Property
from dace.subsets import Range
from dace.symbolic import symbol
from dace.memlet import Memlet

@registry.autoregister_params(singlestate=True)
@make_properties
class MapEnlarge(transformation.Transformation):
    """ Implements the Map Enlarge pattern.

        MapEnlarge takes a map and enlarges its range and internally
        limits it with a branch.
        Example: Map[i=1:I-1] -> Map[i=0:I] If(i in 1:I-1)
    """

    map_entry = transformation.PatternNode(nodes.MapEntry)

    # Properties
    new_range = Property(dtype=Range, default=Range([]),
                         desc="TODO")

    @staticmethod
    def expressions():
        return [sdutil.node_path_graph(MapEnlarge.map_entry)]

    @staticmethod
    def can_be_applied(graph, candidate, expr_index, sdfg, strict=False):
        return True

    @staticmethod
    def match_to_str(graph, candidate):
        map_entry = graph.nodes()[candidate[MapEnlarge.map_entry]]
        return map_entry.map.label + ': ' + str(map_entry.map.params)

    def apply(self, sdfg):
        graph = sdfg.nodes()[self.state_id]
        map_entry = graph.nodes()[self.subgraph[MapEnlarge.map_entry]]
        map_exit = graph.exit_node(map_entry)
        intermediate_nodes = SubgraphView(graph, graph.all_nodes_between(map_entry, map_exit))

        map_param = map_entry.map.params[0]
        map_from, map_to, _ = map_entry.map.range.ranges[0]

        nsdfg = helpers.nest_state_subgraph(sdfg, graph, intermediate_nodes)
        inner_state = nsdfg.sdfg.nodes()[0]

        dummy_state = nsdfg.sdfg.add_state('state', is_start_state=True)
        condition = ' and '.join(f'{frm} <= {param} and {param} <= {to}'
                                    for param, (frm, to, _) in zip(map_entry.map.params, map_entry.map.range.ranges))
        nsdfg.sdfg.add_edge(dummy_state, inner_state, InterstateEdge(condition))

        for sym in nsdfg.sdfg.free_symbols - nsdfg.sdfg.symbols.keys():
            nsdfg.add_symbol(sym, sdfg.symbols.get(sym, int))

        map_entry.map.range = self.new_range
        
        # inner_sdfg = SDFG('nested')
        # nested_sdfg = graph.add_nested_sdfg(
        #     inner_sdfg,
        #     sdfg,
        #     [e.data.data for e in graph.out_edges(map_entry)],
        #     [e.data.data for e in graph.in_edges(map_exit)],
        #     { s:symbol(s) for s in sdfg.symbols.keys() }
        # )

        # for param in map_entry.map.params:
        #     nested_sdfg.symbol_mapping[param] = symbol(param)
        #     inner_sdfg.add_symbol(param, int)

        # dummy_state = inner_sdfg.add_state('dummy', is_start_state=True)
        # inner_state = inner_sdfg.add_state('inner_state')

        # condition = ' and '.join(f'{frm} <= {param} and {param} <= {to}'
        #                             for param, (frm, to, _) in zip(map_entry.map.params, map_entry.map.range.ranges))
        # inner_sdfg.add_edge(dummy_state, inner_state, InterstateEdge(condition))

        # for name, arr in sdfg.arrays.items():
        #     inner_sdfg.add_array(
        #         name,
        #         arr.shape, arr.dtype, arr.storage, 
        #         False, arr.strides,
        #         None,
        #         arr.lifetime, arr.debuginfo, arr.allow_conflicts, arr.total_size
        #     )

        # # Add nodes/edges to nested state.
        # subgraph = SubgraphView(graph, intermediate_nodes)
        # inner_state.add_nodes_from(subgraph.nodes())
        # for edge in subgraph.edges():
        #     inner_state.add_edge(edge.src, edge.src_conn, edge.dst, edge.dst_conn, edge.data)

        # for e in graph.out_edges(map_entry):
        #     # Add edges to nested sdfg.
        #     graph.add_edge(
        #         e.src, e.src_conn,
        #         nested_sdfg, e.data.data,
        #         e.data)

        #     # Add read to nested state and connect it.
        #     read = inner_state.add_read(e.data.data)
        #     inner_state.add_memlet_path(
        #         read,
        #         e.dst,
        #         memlet = e.data,
        #         dst_conn = e.dst_conn
        #     )

        # for e in graph.in_edges(map_exit):
        #     # Add edges from nested sdfg.
        #     graph.add_edge(
        #         nested_sdfg, e.data.data,
        #         e.dst, e.dst_conn,
        #         e.data)

        #     # Add write to nested state and connect it.
        #     write = inner_state.add_read(e.data.data)
        #     inner_state.add_memlet_path(
        #         e.src,
        #         write,
        #         memlet = e.data,
        #         src_conn = e.src_conn
        #     )

        # graph.remove_nodes_from(intermediate_nodes)

