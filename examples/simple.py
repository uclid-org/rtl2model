
import os
import subprocess

from rtl2model.guidance import Guidance, AnnoType
from rtl2model.synthesis_template import *
from rtl2model.sketch import *
import rtl2model.gen_config as gen_config
import rtl2model.lynth.smt as smt
from rtl2model.verilog import *

REPO_BASE_DIR = subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()
BASEDIR = os.path.join(REPO_BASE_DIR, "designs/simple/")


class SimpleModel(ModelBuilder):
    def build_sim(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=BASEDIR,
            target_verilog_dir=BASEDIR,
            root="top"
        )
        self.run_proc(["make", "default"], cwd=BASEDIR)

    def simulate_and_read_signals(self, program):
        with open(os.path.join(BASEDIR, "inputs.bin"), "wb") as f:
            f.write(program.to_bytearray())
        self.run_proc(["./obj_dir/Vtop", "inputs.bin"], cwd=BASEDIR)
        return read_csv(os.path.join(BASEDIR, "traces/tr.csv"), self.cycle_count)


def main():
    v = smt.Variable
    bv8 = smt.BVSort(8)
    s0 = v("top.s0", bv8)
    i1 = v("i1", bv8)
    i2 = v("i2", bv8)
    out = v("out", bv8)
    top = verilog_to_model(
        os.path.join(BASEDIR, "full.v"),
        "top",
        clock_pattern="clk",
        important_signals=["i1", "i2", "s1", "s2", "out"],
        coi_conf=COIConf.UF_ARGS_COI,
    )
    top.print()
    assert top.validate()
    # Bytes are in order of (i1, i2) for each cycle
    sketch = ProgramSketch(
        inst_byte(0),
        inst_byte(0),
        inst_byte(0),
        inst_byte(0),
        Inst(i1),
        Inst(i2),
        inst_byte(0xF),
        inst_byte(0xA),
        inst_byte(0xF),
        inst_byte(0xF),
        inst_byte(0xF),
        inst_byte(0xF),
    )
    cycle_count = 5
    ctr_sig = S("top", "ctr", 8)
    o_ctr_sig = S("top", "ctr_o", 8)
    signals = [
        S("top", "rst", 1),
        ctr_sig,
        o_ctr_sig,
        S("top", "i1", 8),
        S("top", "i2", 8),
        S("top", "s0", 8),
        S("top", "s1", 8),
        S("top", "s2", 8),
        S("top", "out", 8),
    ]
    guidance = Guidance(signals, cycle_count)
    for sig in ("rst", "ctr"):
        guidance.annotate(sig, AnnoType.ASSUME)
    guidance.annotate("i1", {
        ctr_sig.to_variable().op_eq(1): AnnoType.Param(i1),
        smt.BoolConst.T: AnnoType.ASSUME,
    })
    guidance.annotate("i2", {
        ctr_sig.to_variable().op_eq(1): AnnoType.Param(i2),
        smt.BoolConst.T: AnnoType.ASSUME,
    })
    guidance.annotate("s0", {
        ctr_sig.to_variable().op_eq(1): AnnoType.Output(s0),
    })

    start = v("start", bv8)
    model = SimpleModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        sketch,
        top,
        {("top", "s0"): smt.Grammar(
            bound_vars=(i1, i2),
            nonterminals=(start,),
            # Order of these terms matters
            # Python dicts preserve insertion/declaration order
            terms={start: (
                start + start,
                start - start,
                start | start,
                # start ^ start,
                i1, i2,
            )}
        )},
        guidance,
    )
    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()