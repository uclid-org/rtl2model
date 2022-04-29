
import os
import pickle
import subprocess

from easyila.guidance import Guidance, AnnoType
from easyila.synthesis_template import *
from easyila.sketch import *
import easyila.gen_config as gen_config
import easyila.lynth.smt as smt
from easyila.verilog import *

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

    picklefile = "r8051.pickle"
    if not os.path.isfile(picklefile):
        core = verilog_to_model(
            os.path.join(BASEDIR, "full.v"),
            "r8051",
            clock_pattern="clk",
            important_signals=[
                "rst",
                "lft_acc",
                "lft_psw_c",
                "lft_cmd0",
                "lft_cmd1",
                "lft_cmd2",
                "ram_wr_byte",
                "lft_data1",
            ],
            coi_conf=COIConf.UF_ARGS_COI,
        )
        core = core.eliminate_dead_code()
        core.print()
        assert core.validate()
        print("creating pickle")
        with open(picklefile, "wb") as f:
            pickle.dump(core, f)
    else:
        print("loading pickled")
        with open(picklefile, "rb") as f:
            core = pickle.load(f)
            core.print()
            assert core.validate()

    # https://www.keil.com/support/man/docs/is51/is51_opcodes.htm
    sketch = ProgramSketch(
        inst_byte(0x00),    # nop
        inst_byte(0x78),    # MOV R0, imm
        Inst(x),            # (imm)
        inst_byte(0x74),    # MOV A, imm
        Inst(y),            # (imm)
        inst_byte(0x28),    # ADD A, R0
        inst_byte(0x00),    # NOP
        inst_byte(0x00),
        inst_byte(0x00),
        inst_byte(0x31),    # ACALL addr11
        inst_byte(0x31),
        inst_byte(0x31),
        inst_byte(0x31),
        inst_byte(0x31),
        inst_byte(0x31),
        inst_byte(0x31)
    )

    cycle_count = 10
    # TODO allow hierarchical specification
    """
    SIGNALS = {
        "tb": {
            "clk": 1,
            "rst": 1,
            etc.
        }
    }
    """
    pc_sig = S("tb", "lft_pc", 16)
    SIGNALS = [
        S("tb", "clk", 1),
        S("tb", "rst", 1),
        pc_sig,
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
        pc_sig.to_variable().op_eq(3): AnnoType.Param(x),
        pc_sig.to_variable().op_eq(5): AnnoType.Param(y),
        smt.BoolConst.T: AnnoType.ASSUME,
    })
    guidance.annotate("lft_acc", {
        pc_sig.to_variable().op_eq(8): AnnoType.OUTPUT,
        smt.BoolConst.T: AnnoType.ASSUME,
    })

    start = smt.Variable("Start", bv8)
    substart = smt.Variable("BV8", bv8)
    boolterm = smt.Variable("B", smt.BoolSort())
    addbv = start + start
    subbv = start - start
    orbv = start | start
    andbool = boolterm & boolterm
    orbool = boolterm | boolterm
    xorbool = boolterm ^ boolterm
    notbool = ~boolterm
    impliesbool = boolterm.implies(boolterm)
    itebv = boolterm.ite(substart, substart)
    grammar = smt.Grammar(
        (x, y),
        (start, boolterm, substart),
        # Order of these terms matters
        # Python dicts preserve insertion/declaration order
        {
            start: (addbv, subbv, orbv, itebv),
            boolterm: (andbool, orbool, notbool, impliesbool, xorbool, smt.BoolConst.T),
            substart: (x, y),
        }
    )

    model = R8051Model(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        sketch,
        core,
        {("r8051", "acc"): grammar},
        guidance,
    )
    # model.build_binary()
    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()

