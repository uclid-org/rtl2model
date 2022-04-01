
import textwrap

import easyila.lynth.smt as smt
from easyila.verilog import verilog_to_model
from easyila.model import *

class TestCaseSplit:
    """
    Tests automatic case splitting of a model.
    """

    def test_case_split_bool_input(self):
        """
        Splits a model on a boolean input.

        Unused values + instances in each split should be pruned automatically.
        """
        rtl = textwrap.dedent("""\
            module c_true(output [3:0] o);
                assign o = 4'h1;
            endmodule

            module c_false(output [3:0] o);
                assign o = 4'hF;
            endmodule

            module top(input either, output [3:0] big_o);
                wire [3:0] v_t;
                wire [3:0] v_f;
                c_true c_t (.o(v_t));
                c_false c_f (.o(v_f));
                assign big_o = either ? v_t : v_f;
            endmodule
            """)
        v = smt.Variable
        bv4 = smt.BVSort(4)
        o = v("o", bv4)
        big_o = v("big_o", bv4)
        v_t = v("v_t", bv4)
        v_f = v("v_f", bv4)
        either = v("either", smt.BoolSort())
        c_true = Model("c_true", outputs=[o], logic={o: smt.BVConst(1, 4)})
        c_false = Model("c_false", outputs=[o], logic={o: smt.BVConst(0xF, 4)})
        top = Model(
            "top",
            inputs=[either],
            outputs=[big_o],
            state=[v_t, v_f],
            instances={"c_t": Instance(c_true, {}), "c_f": Instance(c_false, {})},
            logic={
                v_t: v("c_t.o", bv4),
                v_f: v("c_f.o", bv4),
                big_o: either.ite(v_t, v_f),
            },
        )
        print("=== ORIGINAL MODEL ===")
        top.print()
        top.validate()
        gen = verilog_to_model(rtl, "top")
        assert gen == top
        cs_top_t = Model(
            "_top__either__TRUE",
            outputs=[big_o],
            state=[v_t],
            instances={"c_t": Instance(c_true, {})},
            logic={
                v_t: v("c_t.o", bv4),
                big_o: v_t,
            }
        )
        cs_top_f = Model(
            "_top__either__FALSE",
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_t.o", bv4),
                big_o: v_f,
            }
        )
        # TODO introduce SMT match term
        # In the case split model, state is elided to the case split terms
        # and all that remains is the identical I/O interface
        cs_top = Model(
            "top",
            inputs=[either],
            outputs=[big_o],
            instances={
                "_top_either__TRUE_inst": Instance(cs_top_t, {}),
                "_top_either__TRUE_inst": Instance(cs_top_f, {})
            },
            logic={
                big_o: either.ite(
                    v("_top_either__TRUE_inst.o", bv4),
                    v("_top_either__FALSE_inst.o", bv4),
                ),
            }
        )
        print("=== CASE SPLIT MODEL ===")
        cs_top.print()
        cs_top.validate()
        assert cs_top.validate()
        alg_split = top.case_split("either")
        assert alg_split == cs_top
