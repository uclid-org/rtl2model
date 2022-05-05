
import os
import subprocess

import rtl2synth.gen_config as gen_config
from rtl2synth.guidance import Guidance, AnnoType
from rtl2synth.synthesis_template import *
from rtl2synth.sketch import *
import rtl2synth.lynth.smt as smt
from rtl2synth.verilog import *

# Things needed:
# - verilator file + Makefile + csv emitting stuff (tracing_manager)
# - possibly instrumented variables

REPO_BASE_DIR = subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()
BASEDIR = os.path.join(REPO_BASE_DIR, "designs/R8051/")

class R8051Model(ModelBuilder):
    def build_binary(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=BASEDIR,
            target_verilog_dir=BASEDIR,
            root="top"
        )
        self.run_proc(["make", "default"], cwd=BASEDIR)

    def simulate_and_read_signals(self, program):
        with open(os.path.join(BASEDIR, "myhello"), "wb") as f:
            f.write(program.to_bytearray())
        self.run_proc(["./obj_dir/Vtop"], cwd=BASEDIR)
        return read_csv(os.path.join(BASEDIR, "traces/tr.csv"), self.cycle_count)


def main():
    v = smt.Variable
    bv8 = smt.BVSort(8)
    x, y = v("lft_data1", bv8), v("lft_acc", bv8)
    op = v("lft_cmd0", bv8)

    core = verilog_to_model(
        os.path.join(BASEDIR, "full.v"),
        "r8051",
        clock_pattern="clk",
        # important_signals=[
        #     "rst",
        #     "lft_pc",
        #     "lft_acc",
        #     # "next_acc",
        #     "acc",
        #     "lft_psw_c",
        #     "lft_cmd0",
        #     "lft_cmd1",
        #     "lft_cmd2",
        #     "ram_wr_byte",
        #     "lft_data1",
        # ],
        coi_conf=COIConf.UF_ARGS_COI,
        pickle_path="r8051.pickle"
    )
    core.print()
    core = core.eliminate_dead_code()
    core.print()
    assert core.validate()

    # https://www.keil.com/support/man/docs/is51/is51_opcodes.htm
    sketch = ProgramSketch(
        inst_byte(0x00),    # nop
        inst_byte(0x78),    # MOV R0, imm
        Inst(x),            # (imm)
        inst_byte(0x74),    # MOV A, imm
        Inst(y),            # (imm)
        Inst(op),           # ??? A, R0 (constrained)
        inst_byte(0x00),    # NOP
        inst_byte(0x00),
        inst_byte(0x00),
    )

    cycle_count = 10
    pc_sig = S("tb", "lft_pc", 16)
    pc_var = pc_sig.to_variable()
    SIGNALS = [
        S("tb", "clk", 1),
        S("tb", "rst", 1),
        pc_sig,
        S("tb", "next_acc", 8),
        S("tb", "lft_acc", 8),
        S("tb", "lft_psw_c", 1),
        S("tb", "lft_cmd0", 8),
        S("tb", "lft_cmd1", 8),
        S("tb", "lft_cmd2", 8),
        S("tb", "ram_wr_byte", 8),
        S("tb", "data", 8, bounds=(0, 7)),
    ]
    guidance = Guidance(SIGNALS, cycle_count)
    for sig in ("rst", "lft_pc"):
        guidance.annotate(sig, AnnoType.ASSUME)
    guidance.annotate("lft_cmd0", {
        pc_var.op_eq(3): AnnoType.Param(x),
        pc_var.op_eq(5): AnnoType.Param(y),
        pc_var.op_eq(7): AnnoType.Param(op),
        smt.BoolConst.T: AnnoType.ASSUME,
    })
    guidance.annotate("lft_acc", {
        pc_var.op_eq(8): AnnoType.Output(v("r8051.next_acc", bv8)),
    })

    start = smt.Variable("Start", bv8)
    substart = smt.Variable("BV8", bv8)
    boolterm = smt.bool_variable("B")
    grammar = smt.Grammar(
        (x, y),
        (start, boolterm, substart),
        # Order of these terms matters
        # Python dicts preserve insertion/declaration order
        {
            start: (
                start + start,
                start - start,
                start | start,
                boolterm.ite(substart, substart),
            ),
            boolterm: (
                boolterm & boolterm,
                boolterm | boolterm,
                ~boolterm,
                boolterm.implies(boolterm),
                boolterm ^ boolterm,
                smt.BoolConst.T,
            ),
            substart: (x, y),
        }
    )

    model = R8051Model(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        sketch,
        core,
        {("r8051", "next_acc"): grammar},
        guidance,
        value_sets={op: {
            0x28, # ADD A, R0
            0x48, # ORL A, R0
            0x58, # ANL A, R0
            0xE8, # MOV A, R0
        }}
    )
    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()
