"""
Synthesizes a model for riscv-mini from RTL.
"""

import os
import subprocess
import sys

import rtl2synth.gen_config as gen_config
from rtl2synth.guidance import Guidance, AnnoType
from rtl2synth.synthesis_template import *
from rtl2synth.sketch import *
import rtl2synth.lynth.smt as smt
from rtl2synth.model import *
from rtl2synth.verilog import *

REPO_BASE_DIR = subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()

BASEDIR = os.path.join(REPO_BASE_DIR, "designs/riscv-mini/")

F3_ADD = 0b000
# F3_SLTU = 0b011
F3_XOR = 0b100
F3_OR = 0b110
F3_AND = 0b111
f3_set = {
    F3_ADD,
    F3_XOR,
    F3_OR,
    F3_AND,
}

class RvMiniModel(ModelBuilder):
    def build_sim(self):
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
        self.run_proc(["./VTileM", "src/test/resources/rv32ui-p-add2.hex"], cwd=BASEDIR, ok_rcs=[0, 1])
        return read_csv(os.path.join(BASEDIR, "sample2.csv"), self.cycle_count)


def main():
    v = smt.Variable
    bv32 = smt.BVSort(32)
    bv12 = smt.BVSort(12)
    a, b = v("io_A", bv32), v("io_B", bv32)
    f3 = v("f3", smt.BVSort(3))
    alu_op = v("io_alu_op", smt.BVSort(4))
    short_a, short_b = v("short_A", bv12), v("short_B", bv12)
    io_out = v("io_out", bv32)

    alu = Model(
        "ALUArea",
        inputs=[a, b, v("io_alu_op", smt.BVSort(4))],
        state=[short_a, short_b, f3],
        outputs=[io_out, v("io_sum", bv32)],
        ufs=[
            UFPlaceholder("alu_result", bv32, (short_a, short_b, f3), False),
            UFPlaceholder("io_sum", bv32, (), False)
        ],
        logic={
            short_a: a[11:0],
            short_b: b[11:0],
            # Workaround hack to make decoding work properly
            # Refer to chisel code in ALU design
            f3: alu_op.match_const({
                0: smt.BVConst(F3_ADD, 3),
                2: smt.BVConst(F3_AND, 3),
                3: smt.BVConst(F3_OR, 3),
                4: smt.BVConst(F3_XOR, 3),
                # dummy cases to ensure exhaustion
                1: smt.BVConst(F3_ADD, 3),
                5: smt.BVConst(F3_ADD, 3),
                6: smt.BVConst(F3_ADD, 3),
                7: smt.BVConst(F3_ADD, 3),
            }),
            io_out: v("alu_result", bv32)
        }
    )
    assert alu.validate()
    dpath = verilog_to_model(
        os.path.join(BASEDIR, "full.v"),
        "Datapath",
        clock_pattern=".*clock",
        defined_modules=[alu],
    )
    # dpath = dpath.eliminate_dead_code()
    dpath.print()
    assert dpath.validate()
    tile = verilog_to_model(
        os.path.join(BASEDIR, "full.v"),
        "Tile",
        clock_pattern=".*clock",
        defined_modules=[dpath],
        # pickle_path="rvmini.pickle",
    )

    sketch = ProgramSketch(
        inst_word(0) * (31 * 4),     # @000 496 bytes of 0s
        inst_word(0x13) * 4,        # @496 through 508: nop
        Inst(short_a, SketchValue(0b10110010011, 20)), # @512 addi a1, x0, ???
        Inst(short_b, SketchValue(0b11000010011, 20)), # @516 addi a2, x0, ???
        # Fix R-type opcode; vary f3 field
        Inst(SketchValue(0x18b, 17), f3, SketchValue(0x6b3, 12)), # @520 ?? a3, a1, a2
        inst_word(0x13) * 20,       # 524 (and later): nop
        # inst_word(0xc586b3) * 20,   # @520 (and later) add a3, a1, a2
        # a1 is x11, a2 is x12, a3 is x13
        # remember that instructions don't commit until they reach the last stage, making
        # cycle 14 (IF_PC=532) the minimum -- we can overshoot safely though since there
        # are just more of the same instruction over and over after
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
        S("Tile", "lft_tile_stall", 32),
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
        S("Tile", "lft_tile_regs_11", 32),
        S("Tile", "lft_tile_regs_12", 32),
        S("Tile", "lft_tile_regs_13", 32),
    ]
    guidance = Guidance(SIGNALS, cycle_count)
    for sig in ["reset", "lft_tile_pc", "lft_tile_fe_pc", "lft_tile_ew_pc"]:
        guidance.annotate(sig, AnnoType.ASSUME)
    # a1 (shadow var)
    guidance.annotate("lft_tile_regs_11", {ew_pc_var.op_eq(0x204): AnnoType.ParamIndexed((11, 0), short_a)})
    # a2 (shadow var)
    guidance.annotate("lft_tile_regs_12", {ew_pc_var.op_eq(0x208): AnnoType.ParamIndexed((11, 0), short_b)})
    # a3 (output)
    guidance.annotate("lft_tile_regs_13",
        {ew_pc_var.op_eq(0x20C): AnnoType.Output(v("ALUArea.alu_result", bv32))}
    )
    guidance.annotate("lft_tile_fe_inst", {
        fe_pc_var.op_eq(0x200): AnnoType.AssumeIndexed((19, 0)),
        fe_pc_var.op_eq(0x204): AnnoType.AssumeIndexed((19, 0)),
        fe_pc_var.op_eq(0x208): [
            AnnoType.AssumeIndexed((31, 15), (11, 0)),
            AnnoType.ParamIndexed((14, 12), f3)
        ],
        # For everything except the placeholder instructions, assume the whole inst
        # Otherwise, assume everything but the immediate
        smt.BoolConst.T: AnnoType.ASSUME,
    })
    guidance.annotate("lft_tile_regFile_io_raddr1", AnnoType.ASSUME)
    guidance.annotate("lft_tile_regFile_io_raddr2", AnnoType.ASSUME)
    guidance.annotate("lft_tile_regFile_io_waddr", AnnoType.ASSUME)
    start = smt.bv_variable("start", 32)
    substart = smt.bv_variable("substart", 32)
    bv3 = smt.bv_variable("bv3", 3)
    boolterm = smt.bool_variable("boolterm")
    grammar = smt.Grammar(
        bound_vars=(short_a, short_b, f3),
        nonterminals=(start,),
        terms={
            start: (
                f3.op_eq(bv3).ite(start, start),
                substart,
            ),
            substart: (
                substart + substart,
                substart - substart,
                substart | substart,
                substart & substart,
                substart ^ substart,
                boolterm.ite(smt.BVConst(1, 32), smt.BVConst(0, 32)),
                boolterm.ite(smt.BVConst(0xFFFFF000, 32), smt.BVConst(0, 32)),
                short_a.sext(20),
                short_b.sext(20),
            ),
            boolterm: (
                short_a[11],
                short_b[11],
            ),
            bv3: (
                smt.BVConst(F3_ADD, 3),
                smt.BVConst(F3_OR, 3),
                smt.BVConst(F3_XOR, 3),
                smt.BVConst(F3_AND, 3),
                # smt.BVConst(F3_SLTU, 3),
            )
        },
    )
    model = RvMiniModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys"), clock_name="clock"),
        sketch,
        tile,
        {("ALUArea", "alu_result"): grammar},
        # {("ALUArea", "alu_result"): None},
        guidance,
        {f3: f3_set}
    )
    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()


class TestRun:
    def test_rvmini_main(self):
        main()