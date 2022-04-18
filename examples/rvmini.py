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
    cycle_count = 21
    fe_pc_sig = S("Tile", "lft_tile_fe_pc", 32)
    fe_pc_var = fe_pc_sig.to_variable()
    ew_pc_sig = S("Tile", "lft_tile_ew_pc", 32)
    ew_pc_var = ew_pc_sig.to_variable()
    SIGNALS = [
        S("Tile", "reset", 1),
        S("Tile", "clock", 1),
        S("Tile", "lft_tile_pc", 32),
        fe_pc_sig,
        ew_pc_sig,
        S("Tile", "lft_tile_fe_inst", 32),
        S("Tile", "lft_tile_regFile_io_waddr", 5),
        S("Tile", "lft_tile_regFile_io_wdata", 32),
        S("Tile", "lft_tile_regFile_io_raddr1", 5),
        S("Tile", "lft_tile_regFile_io_raddr2", 5),
        S("Tile", "lft_tile_regFile_io_rdata1", 32),
        S("Tile", "lft_tile_regFile_io_rdata2", 32),
        S("Tile", "lft_tile_alu_io_A", 32),
        S("Tile", "lft_tile_alu_io_B", 32),
        S("Tile", "lft_tile_alu_io_alu_op", 32),
        S("Tile", "lft_tile_alu_io_out", 32),
        S("Tile", "lft_tile_alu_io_sum", 32),
        S("Tile", "lft_tile_regs_10", 32),
        S("Tile", "lft_tile_regs_11", 32),
        S("Tile", "lft_tile_regs_12", 32),
        S("Tile", "lft_tile_regs_13", 32),
    ]
    guidance = Guidance(SIGNALS, cycle_count)
    for sig in ["reset", "lft_tile_pc", "lft_tile_fe_pc", "lft_tile_ew_pc"]:
        guidance.annotate(sig, AnnoType.ASSUME)
    # a1 (shadow var)
    guidance.annotate("lft_tile_regs_11", {ew_pc_var.op_eq(516): AnnoType.PARAM})
    # a2 (shadow var)
    guidance.annotate("lft_tile_regs_12", {ew_pc_var.op_eq(520): AnnoType.PARAM})
    # a3 (output)
    guidance.annotate("lft_tile_regs_13", {ew_pc_var.op_eq(524): AnnoType.OUTPUT})
    guidance.annotate("lft_tile_fe_inst", {
        (fe_pc_var > 520) & (fe_pc_var < 512): AnnoType.ASSUME
    })
    # TODO need to also constrain specific bits of the instruction
    # in order to restrict adding and reg destination
    guidance.annotate("lft_tile_regFile_io_waddr", {
        ew_pc_var.op_eq(512) | ew_pc_var.op_eq(516): AnnoType.ASSUME
    })

    bv32 = smt.BVSort(32)
    x = smt.Variable("__shadow_0", bv32)
    y = smt.Variable("__shadow_1", bv32)
    start = smt.Variable("start", bv32)
    addbv = start + start
    subbv = start - start
    orbv = start | start
    sf = smt.SynthFun(
        "alu_add",
        (x, y),
        bv32,
        smt.Grammar(
            bound_vars=(x, y),
            nonterminals=(start,),
            terms={start: (
                start + start,
                start - start,
                start | start,
            ),},
        )
    )
    solver = sf.new_solver()

    model = RvMiniModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys"), clock_name="clock"),
        solver,
        SIGNALS,
        guidance
    )
    model.build_binary()
    fn = model.main_sygus_loop()

    # v = smt.Variable
    # a = v("io_A", bv32)
    # b = v("io_B", bv32)
    # io_out = v("io_out", bv32)
    # alu = Model(
    #     "ALUArea",
    #     inputs=[a, b, v("io_alu_op", smt.BVSort(4))],
    #     outputs=[io_out, v("io_sum", bv32)],
    #     ufs=[UFPlaceholder("io_sum", bv32, (), False)],
    #     logic={io_out: fn.apply(a, b)},
    # )
    # verilog_to_model(
    #     "../hwlifting/processors/riscv-mini/full.v",
    #     "Core",
    #     clock_pattern=".*clock",
    #     defined_modules=[alu],
    # ).print()

if __name__ == '__main__':
    main()
