
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

        Because no state variable has a clocked transition update, logic can be split cleanly,
        and this model does not first need to be flattened.
        """
        rtl = textwrap.dedent("""\
            module c_true(output [3:0] o);
                assign o = 4'h1;
            endmodule

            module c_false(output [3:0] o);
                assign o = 4'hF;
            endmodule

            module top(input either, input [3:0] ignore, output [3:0] big_o);
                wire [3:0] v_t;
                wire [3:0] v_f;
                c_true c_t (.o(v_t));
                c_false c_f (.o(v_f));
                // Due to some pyverilog pass, if ignore is outside the expr it
                // will get pushed in
                assign big_o = either ? (ignore & v_t) : (ignore & v_f);
            endmodule
            """)
        v = smt.Variable
        bv4 = smt.BVSort(4)
        o = v("o", bv4)
        big_o = v("big_o", bv4)
        v_t = v("v_t", bv4)
        v_f = v("v_f", bv4)
        either = v("either", smt.BoolSort())
        ignore = v("ignore", bv4)
        c_true = Model("c_true", outputs=[o], logic={o: smt.BVConst(1, 4)})
        c_false = Model("c_false", outputs=[o], logic={o: smt.BVConst(0xF, 4)})
        top = Model(
            "top",
            inputs=[either, ignore],
            outputs=[big_o],
            state=[v_t, v_f],
            instances={"c_t": Instance(c_true, {}), "c_f": Instance(c_false, {})},
            logic={
                v_t: v("c_t.o", bv4),
                v_f: v("c_f.o", bv4),
                big_o: either.ite(ignore & v_t, ignore & v_f),
            },
        )
        print("=== ORIGINAL MODEL ===")
        top.print()
        assert top.validate()
        gen = verilog_to_model(rtl, "top")
        assert gen == top
        cs_top_t = Model(
            "_top__either__TRUE",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_t],
            instances={"c_t": Instance(c_true, {})},
            logic={
                v_t: v("c_t.o", bv4),
                big_o: ignore & v_t,
            }
        )
        cs_top_f = Model(
            "_top__either__FALSE",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_t.o", bv4),
                big_o: ignore & v_f,
            }
        )
        # The case split transformation first flattens all state
        # Then, in the submodel, combinational logic is elided to the case split terms
        # and all that remains is the identical I/O interface
        cs_top = Model(
            "top",
            inputs=[either, ignore],
            outputs=[big_o],
            instances={
                "_top__either__TRUE_inst": Instance(cs_top_t, {ignore: ignore}),
                "_top__either__FALSE_inst": Instance(cs_top_f, {ignore: ignore})
            },
            logic={
                big_o: either.ite(
                    v("_top__either__TRUE_inst.o", bv4),
                    v("_top__either__FALSE_inst.o", bv4),
                ),
            }
        )
        print("=== CASE SPLIT MODEL ===")
        assert cs_top.validate()
        alg_split = top.case_split("either")
        alg_split.print()
        alg_split.validate()
        assert alg_split == cs_top

    def test_case_split_bv_state(self):
        """
        Splits a model on a bitvector state variable.

        In this case, the split variable happens to be an instance output.
        Since said instance no longer has any used outputs, it should be removed
        in all subinstances.
        """
        v = smt.Variable
        bv2 = smt.BVSort(2)
        o = v("o", bv2)
        big_o = v("big_o", bv2)
        v_t = v("v_t", bv2)
        v_f = v("v_f", bv2)
        ignore = v("ignore", bv2)
        c_true = Model("c_true", outputs=[o], logic={o: smt.BVConst(1, 2)})
        c_false = Model("c_false", outputs=[o], logic={o: smt.BVConst(0x3, 2)})
        top = Model(
            "top",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_t, v_f],
            instances={"c_t": Instance(c_true, {}), "c_f": Instance(c_false, {})},
            logic={
                v_t: v("c_t.o", bv2),
                v_f: v("c_f.o", bv2),
                big_o: v_t.op_eq(v_f).ite(ignore & v_t, ignore & v_f),
            },
        )
        print("=== ORIGINAL MODEL ===")
        top.print()
        assert top.validate()
        cs_top_00 = Model(
            "_top__v_t__00",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_f.o", bv2),
                big_o: smt.BVConst(0, 2).op_eq(v_f).ite(ignore & smt.BVConst(0, 2), ignore & v_f),
            }
        )
        cs_top_01 = Model(
            "_top__v_t__01",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_f.o", bv2),
                big_o: smt.BVConst(1, 2).op_eq(v_f).ite(ignore & smt.BVConst(1, 2), ignore & v_f),
            }
        )
        cs_top_10 = Model(
            "_top__v_t__10",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_f.o", bv2),
                big_o: smt.BVConst(2, 2).op_eq(v_f).ite(ignore & smt.BVConst(2, 2), ignore & v_f),
            }
        )
        cs_top_11 = Model(
            "_top__v_t__11",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_f],
            instances={"c_f": Instance(c_false, {})},
            logic={
                v_f: v("c_f.o", bv2),
                big_o: smt.BVConst(3, 2).op_eq(v_f).ite(ignore & smt.BVConst(3, 2), ignore & v_f),
            }
        )
        # In the case split model, state that doesn't determine v_t is elided and pushed
        # into the submodule instances
        cs_top = Model(
            "top",
            inputs=[ignore],
            outputs=[big_o],
            state=[v_t],
            instances={
                "c_t": Instance(c_true, {}),
                "_top__v_t__00_inst": Instance(cs_top_00, {ignore: ignore}),
                "_top__v_t__01_inst": Instance(cs_top_01, {ignore: ignore}),
                "_top__v_t__10_inst": Instance(cs_top_10, {ignore: ignore}),
                "_top__v_t__11_inst": Instance(cs_top_11, {ignore: ignore}),
            },
            logic={
                v_t: v("c_t.o", bv2),
                big_o: v_t.match_const({
                    0: v("_top__v_t__00_inst.big_o", bv2),
                    1: v("_top__v_t__01_inst.big_o", bv2),
                    2: v("_top__v_t__10_inst.big_o", bv2),
                    3: v("_top__v_t__11_inst.big_o", bv2),
                }),
            }
        )
        print("=== CASE SPLIT MODEL ===")
        assert cs_top.validate()
        alg_split = top.case_split("v_t")
        alg_split.print()
        assert alg_split.validate()
        assert alg_split == cs_top

    def test_case_split_bv_clocked_state(self):
        """
        Tests case splitting on a variable that affects a clocked update in the
        model.
        In this case, we cannot simply remove state variables from the top-level design
        because then each submodule would have diverging state; instead, we make the "next"
        value of the variable an output and the current value an input for each submodule.
        """
        v = smt.Variable
        bv2 = smt.BVSort(2)
        in_ = v("in", bv2)
        s_a = v("s_a", bv2)
        s_b = v("s_b", bv2)
        next_s_b = v("__next_s_b", bv2)
        out = v("out", bv2)
        top = Model(
            "top",
            inputs=[in_],
            outputs=[out],
            state=[s_a, s_b],
            logic={out: s_b & s_a},
            default_next={
                s_a: in_.op_eq(smt.BVConst(0b10, 2)).ite(s_a, s_a + 1),
                s_b: s_a.op_eq(in_).ite(s_b, smt.BVConst(0, 2)),
            }
        )
        assert top.validate()
        cases = [
            Model(
                f"_top__s_a__{i:02b}",
                inputs=[in_, s_b],
                outputs=[out, next_s_b],
                logic={
                    out: s_b & smt.BVConst(i, 2),
                    next_s_b: smt.BVConst(i, 2).op_eq(in_).ite(s_b, smt.BVConst(0, 2)),
                },
            )
            for i in range(4)
        ]
        cs_top = Model(
            "top",
            inputs=[in_],
            outputs=[out],
            state=[s_a, s_b],
            instances={
                "_top__s_a__00_inst": Instance(cases[0], {in_: in_, s_b: s_b}),
                "_top__s_a__01_inst": Instance(cases[1], {in_: in_, s_b: s_b}),
                "_top__s_a__10_inst": Instance(cases[2], {in_: in_, s_b: s_b}),
                "_top__s_a__11_inst": Instance(cases[3], {in_: in_, s_b: s_b}),
            },
            logic={
                out: s_a.match_const({
                    0: v("_top__s_a__00_inst.out", bv2),
                    1: v("_top__s_a__01_inst.out", bv2),
                    2: v("_top__s_a__10_inst.out", bv2),
                    3: v("_top__s_a__11_inst.out", bv2),
                }),
            },
            default_next={
                s_a: in_.op_eq(smt.BVConst(0b10, 2)).ite(s_a, s_a + 1),
                s_b: s_a.match_const({
                    0: v("_top__s_a__00_inst.__next_s_b", bv2),
                    1: v("_top__s_a__01_inst.__next_s_b", bv2),
                    2: v("_top__s_a__10_inst.__next_s_b", bv2),
                    3: v("_top__s_a__11_inst.__next_s_b", bv2),
                }),
            }
        )
        assert cs_top.validate()
        alg_split = top.case_split("s_a")
        alg_split.print()
        assert alg_split == cs_top
