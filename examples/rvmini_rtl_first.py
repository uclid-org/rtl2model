"""
Synthesizes a model for riscv-mini from RTL.
"""

import os
import pickle
import subprocess
import sys

from easyila.guidance import Guidance, AnnoType
from easyila.synthesis_template import *
from easyila.sketch import *
import easyila.gen_config as gen_config
import easyila.lynth.smt as smt
from easyila.model import *
from easyila.verilog import *

REPO_BASE_DIR = subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()

BASEDIR = os.path.join(REPO_BASE_DIR, "designs/riscv-mini/")

class RvMiniModel(ModelBuilder):
    def build_binary(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=os.path.join(BASEDIR, "src/main/cc/"),
            target_verilog_dir=BASEDIR,
            root="Tile"
        )
        self.run_proc(["make", "verilatorM"], cwd=BASEDIR)

    def simulate_and_read_signals(self, program):
        hex_arr = program.to_hex_str_array()
        with open(os.path.join(BASEDIR, "src/test/resources/rv32ui-p-add2.hex"), 'w') as src_file:
            # Add 4 insts per line, with earliest inst at end
            for i in range(0, len(hex_arr), 4):
                src_file.write("".join(reversed(hex_arr[i:i+4])) + "\n")
        print("Generated hexfile!")
        self.run_proc(["./VTileM", "src/test/resources/rv32ui-p-add2.hex"], cwd=BASEDIR, ok_rcs=[0, 1])
        return read_csv(os.path.join(BASEDIR, "sample2.csv"), self.cycle_count)


def main():
    v = smt.Variable
    bv32 = smt.BVSort(32)
    bv12 = smt.BVSort(12)
    a, b = v("io_A", bv32), v("io_B", bv32)
    short_a, short_b = v("short_A", bv12), v("short_B", bv12)
    io_out = v("io_out", bv32)

    picklefile = "rvmini.pickle"
    if not os.path.isfile(picklefile):
        alu = Model(
            "ALUArea",
            inputs=[a, b, v("io_alu_op", smt.BVSort(4))],
            state=[short_a, short_b],
            outputs=[io_out, v("io_sum", bv32)],
            ufs=[
                UFPlaceholder("alu_result", bv32, (short_a, short_b), False),
                UFPlaceholder("io_sum", bv32, (), False)
            ],
            logic={
                short_a: a[11:0],
                short_b: b[11:0],
                io_out: v("alu_result", bv32)
            }
        )
        assert alu.validate()
        dpath = verilog_to_model(
            os.path.join(BASEDIR, "full.v"),
            "Datapath",
            clock_pattern=".*clock",
            defined_modules=[alu],
            # important_signals=[
            #     "io_lft_dpath__pc",
            #     "io_lft_dpath__fe_pc",
            #     "io_lft_dpath__ew_pc",
            #     "io_lft_dpath__fe_inst",
            #     "io_lft_dpath__regs_11",
            #     "io_lft_dpath__regs_12",
            #     "io_lft_dpath__regs_13",
            # ],
            # coi_conf=COIConf.NO_COI,
        )
        dpath = dpath.eliminate_dead_code()
        dpath.validate()
        tile = verilog_to_model(
            os.path.join(BASEDIR, "full.v"),
            "Tile",
            clock_pattern=".*clock",
            defined_modules=[dpath],
        )
        print("creating pickle")
        with open(picklefile, "wb") as f:
            pickle.dump(tile, f)
    else:
        print("loading pickled")
        with open(picklefile, "rb") as f:
            tile = pickle.load(f)
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
    # print(core.to_solver().get_sygus2())

    sketch = ProgramSketch(
        inst_word(0) * (31 * 4),     # @000 496 bytes of 0s
        inst_word(0x13) * 4,        # @496 through 508: nop
        Inst(short_a, SketchValue(0b11000010011, 20)), # @512 addi a2, x0, ???
        Inst(short_b, SketchValue(0b10110010011, 20)), # @516 addi a1, x0, ???
        inst_word(0xc586b3) * 20,   # @520 (and later) add a3, a1, a2
        # a1 is x11, a2 is x12, a3 is x13
        # remember that instructions don't commit until they reach the last stage, making
        # cycle 14 (IF_PC=532) the minimum -- we can overshoot safely though since there
        # are just more of the same instruction over and over after
        # the trace seems to stall for some reason though? TODO ask adwait about that
        # for now, the pattern seems to be that 4 adds retire successfully, then the next add
        # stalls for an additional 3 cycles
    )

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
    guidance.annotate("lft_tile_regs_11", {ew_pc_var.op_eq(0x208): AnnoType.ParamIndexed((11, 0), short_a)})
    # a2 (shadow var)
    guidance.annotate("lft_tile_regs_12", {ew_pc_var.op_eq(0x204): AnnoType.ParamIndexed((11, 0), short_b)})
    # a3 (output)
    guidance.annotate("lft_tile_regs_13", {ew_pc_var.op_eq(0x20C): AnnoType.OUTPUT})
    guidance.annotate("lft_tile_fe_inst", {
        (fe_pc_var > 0x204) | (fe_pc_var < 0x200): AnnoType.ASSUME,
        # For everything except the placeholder instructions, assume the whole inst
        # Otherwise, assume everything but the immediate
        smt.BoolConst.T: AnnoType.AssumeIndexed((19, 0))
    })
    guidance.annotate("lft_tile_regFile_io_raddr1", AnnoType.ASSUME)
    guidance.annotate("lft_tile_regFile_io_raddr2", AnnoType.ASSUME)
    guidance.annotate("lft_tile_regFile_io_waddr", AnnoType.ASSUME)
    start = smt.BVVariable("start", 32)
    grammar = smt.Grammar(
        bound_vars=(short_a, short_b),
        nonterminals=(start,),
        terms={start: (
            start + start,
            start - start,
            start | start,
            start[11].ite(smt.BVConst(0xFFFFF000, 32), smt.BVConst(0, 32)),
            short_a.sext(20),
            short_b.sext(20),
        ),},
    )
    model = RvMiniModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys"), clock_name="clock"),
        sketch,
        tile,
        {("ALUArea", "alu_result"): grammar},
        # {("ALUArea", "alu_result"): None},
        guidance,
    )
    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()


class TestRun:
    def test_rvmini_main(self):
        main()