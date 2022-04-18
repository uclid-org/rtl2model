"""
Synthesizes a model for riscv-mini from RTL.
"""

import os
import subprocess
from subprocess import Popen, PIPE
import sys

from easyila.guidance import Guidance, AnnoType
from easyila.synthesis_template import *
from easyila.sketch import *
import easyila.gen_config as gen_config
import easyila.lynth.smt as smt
from easyila.model import *
from easyila.verilog import *

REPO_BASE_DIR = "/home/jhshi/research/hwlifting/"
"""
subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()
"""

BASEDIR = os.path.join(REPO_BASE_DIR, "processors/riscv-mini/")


class RvMiniModel(ModelBuilder):
    def build_binary(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=os.path.join(BASEDIR, "src/main/cc/"),
            target_verilog_dir=BASEDIR,
            root="Tile"
        )
        self.run_proc(["make", "verilatorM"], cwd=BASEDIR)

    def generate_program(self, inputs) -> ConcreteProgram:
        return ProgramSketch(
            inst_word(0) * (31 * 4),     # @000 496 bytes of 0s
            inst_word(0x13) * 4,        # @496 through 508: nop
            Inst(SketchHole("a", 12), SketchValue(0b11000010011, 20)), # @512 addi a2, x0, ???
            Inst(SketchHole("b", 12), SketchValue(0b10110010011, 20)), # @516 addi a1, x0, ???
            inst_word(0xc586b3) * 20,   # @520 (and later) add a3, a1, a2
            # a1 is x11, a2 is x12, a3 is x13
            # remember that instructions don't commit until they reach the last stage, making
            # cycle 14 (IF_PC=532) the minimum -- we can overshoot safely though since there
            # are just more of the same instruction over and over after
            # the trace seems to stall for some reason though? TODO ask adwait about that
            # for now, the pattern seems to be that 4 adds retire successfully, then the next add
            # stalls for an additional 3 cycles
        ).fill({"a": inputs[0] & 0xFFF, "b": inputs[1] & 0xFFF})

    def simulate_and_read_signals(self, sketch):
        hex_arr = sketch.to_hex_str_array()
        with open(os.path.join(BASEDIR, "src/test/resources/rv32ui-p-add2.hex"), 'w') as src_file:
            # Add 4 insts per line, with earliest inst at end
            for i in range(0, len(hex_arr), 4):
                src_file.write("".join(reversed(hex_arr[i:i+4])) + "\n")
        print("Generated hexfile!")
        self.run_proc(["./VTileM", "src/test/resources/rv32ui-p-add2.hex"], cwd=BASEDIR, ok_rcs=[0, 1])
        return read_csv(os.path.join(BASEDIR, "sample2.csv"), self.cycle_count)


def main():
    core = verilog_to_model(
        os.path.join(BASEDIR, "full.v"),
        "Datapath",
        clock_pattern=".*clock",
        important_signals=[
            "io_lft_dpath__pc",
            "io_lft_dpath__fe_pc",
            "io_lft_dpath__ew_pc",
            "io_lft_dpath__fe_inst",
            "io_lft_dpath__regs_11",
            "io_lft_dpath__regs_12",
            "io_lft_dpath__regs_13",
        ],
        coi_conf=COIConf.NO_COI,
    )
    core = core.eliminate_dead_code()
    core.print()
    core.validate()
    # TODO
    # Synthesis loop for filling in UFs:
    # - (user provides oracles, refinement relation)
    # - I/O oracle produces arguments to program under test
    #       (example: ALU add)
    #   Chosen values for synth funs should produce correct results under those I/O pairs
    # - Constraints on synthesis function are indirect (asserts model output
    #   and state equal RTL output/state, synth funs only appear as part of exprs)
    #   That is, foreach UF; replace uf_name by uf_expr in RTL assertions
    #   (with free variables marked anyconst)
    # - Assume that child modules are already verified?
    print(core.to_solver().get_sygus2())

if __name__ == "__main__":
    main()
