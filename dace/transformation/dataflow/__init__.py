# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
""" This module initializes the dataflow transformations package. """

# Map-related
from .mapreduce import MapReduceFusion, MapWCRFusion
from .map_expansion import MapExpansion
from .map_collapse import MapCollapse
from .map_for_loop import MapToForLoop
from .map_interchange import MapInterchange
from .map_fusion import MapFusion
from .map_fission import MapFission
from .trivial_map_elimination import TrivialMapElimination
from .trivial_map_range_elimination import TrivialMapRangeElimination


# Data movement
from .strip_mining import StripMining
from .tiling import MapTiling
from .vectorization import Vectorization

# Data-related
from .stream_transient import StreamTransient, AccumulateTransient
from .local_storage import InLocalStorage, OutLocalStorage
from .double_buffering import DoubleBuffering
from .streaming_memory import StreamingMemory, StreamingComposition

# Complexity reduction
from .dedup_access import DeduplicateAccess
from .redundant_array import RedundantArray, RedundantSecondArray
from .redundant_array_copying import (RedundantArrayCopying,
                                      RedundantArrayCopying2,
                                      RedundantArrayCopying3)
from .merge_arrays import InMergeArrays, OutMergeArrays, MergeSourceSinkArrays
from .prune_connectors import PruneConnectors, PruneSymbols
from .wcr_conversion import AugAssignToWCR

# Device-related
from .copy_to_device import CopyToDevice
from .gpu_transform import GPUTransformMap
from .gpu_transform_local_storage import GPUTransformLocalStorage
from .mpi import MPITransformMap

# Algorithmic
from .matrix_product_transpose import MatrixProductTranspose
