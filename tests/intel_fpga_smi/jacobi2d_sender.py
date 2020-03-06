# Example generated by StencilFlow project. Note that we just evaluate that it compiles and execute
# not if the result is correct

import dace
import numpy as np
import subprocess as sp
import os



if __name__ == "__main__":

    sdfg = dace.SDFG.from_file("intel_fpga_smi/jacobi2d_32x32x32_before.sdfg")

    # Configure and compile SDFG
    dace.config.Config.set("compiler", "fpga_vendor", value="intel_fpga")
    dace.config.Config.set("optimizer", "interface", value="")
    dace.config.Config.set("compiler", "intel_fpga", "mode", value="emulator")

    sdfg.expand_library_nodes()
    sdfg.specialize(dict(smi_rank=0, smi_num_ranks=2))
    try:
        program = sdfg.compile()
    except dace.codegen.compiler.CompilationError as ex:
        pass

    build_folder = os.path.join(".dacecache", sdfg.name, "build")

    # codegen host
    sp.run(["make", "intelfpga_smi_" + sdfg.name + "_codegen_host", "-j"],
           cwd=build_folder,
           check=True)
    # make host program
    sp.run(["make"],
           cwd=build_folder,
           check=True)
    # emulated bitstream
    sp.run(["make", "intelfpga_smi_compile_" + sdfg.name + "_emulator"],
           cwd=build_folder,
           check=True)

    # reload the program
    program = sdfg.compile()

    #input data
    input = np.zeros((32, 32, 32), dtype=np.float32)
    dace_args = {"a_host": input}
    print("Executing Jacobi3D_sender...")
    program(**dace_args)





