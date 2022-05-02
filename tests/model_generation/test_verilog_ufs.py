
import textwrap

import pytest

import easyila.lynth.smt as smt
from easyila.verilog import verilog_to_model, COIConf
from easyila.model import Model, Instance, UFPlaceholder

class TestVerilogUfs:
    """
    Tests verilog parsing with various cone-of-influence behaviors to
    replace hardware signals by uninterpreted functions.
    """

    def test_verilog_single_imp_no_coi(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.
        `coi_conf` is `NO_COI`, meaning non-important signals are 1-arity UFs with a single argument
        for degrees of freedom.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input should_inc, output [2:0] result);
                reg [2:0] a;
                reg [2:0] b;
                wire [2:0] a_p1;
                wire [2:0] b_p1;
                always @(posedge clk) begin
                    if (should_inc) begin
                        a = a_p1;
                        b = b_p1;
                    end
                end
                assign a_p1 = a + 3'h1;
                assign b_p1 = b + 3'h1;
                assign result = ~a | ~b;
            endmodule
            """)
        bv3 = smt.BVSort(3)
        var = smt.Variable
        model_no_a = verilog_to_model(rtl, "top", important_signals=["should_inc", "b", "b_p1", "result"])
        model_no_a.print()
        a = var("a", bv3)
        a_p1 = var("a_p1", bv3)
        b = var("b", bv3)
        b_p1 = var("b_p1", bv3)
        should_inc = var("should_inc", smt.BoolSort())
        result = var("result", bv3)
        assert model_no_a.validate()
        assert model_no_a == \
            Model(
                "top",
                inputs=[should_inc],
                outputs=[result],
                state=[b, b_p1],
                # `a` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as a 1-arity uninterpreted function
                ufs=[UFPlaceholder("a", bv3, (), True)],
                logic={
                    b_p1: b + 1,
                    result: (~a) | (~b)
                },
                transition={b: should_inc.ite(b_p1, b)},
            )
        model_no_b = verilog_to_model(rtl, "top", important_signals=["should_inc", "a", "a_p1", "result"])
        assert model_no_b.validate()
        assert model_no_b == \
            Model(
                "top",
                inputs=[should_inc],
                outputs=[result],
                state=[a, a_p1],
                # `b` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as a 1-arity uninterpreted function
                ufs=[UFPlaceholder("b", bv3, (), True)],
                logic={
                    a_p1: a + 1,
                    result: (~a) | (~b)
                },
                transition={a: should_inc.ite(a_p1, a)},
            )

    def test_verilog_single_imp_uf_coi_logic(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.
        `coi_conf` is `UF_ARGS_COI`, meaning that non-important signals are replaced with uninterpreted
        functions. Unlike `NO_COI`, these UF terms have important arguments in their COI as arguments.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input should_inc, output [2:0] result);
                reg [2:0] a;
                reg [2:0] b;
                wire [2:0] a_p1;
                wire [2:0] b_p1;
                always @(posedge clk) begin
                    if (should_inc) begin
                        a = a_p1;
                        b = b_p1;
                    end
                end
                assign a_p1 = a + 3'h1;
                assign b_p1 = b + 3'h1;
                assign result = ~a | ~b;
            endmodule
            """)
        bv3 = smt.BVSort(3)
        var = smt.Variable
        model_no_a = verilog_to_model(
            rtl,
            "top",
            important_signals=["should_inc", "b", "b_p1", "result"],
            coi_conf=COIConf.UF_ARGS_COI,
        )
        model_no_a.print()
        a = var("a", bv3)
        a_p1 = var("a_p1", bv3)
        b = var("b", bv3)
        b_p1 = var("b_p1", bv3)
        should_inc = var("should_inc", smt.BoolSort())
        result = var("result", bv3)
        assert model_no_a.validate()
        assert model_no_a == \
            Model(
                "top",
                inputs=[should_inc],
                outputs=[result],
                state=[b, b_p1],
                # `a` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as an uninterpreted function
                ufs=[UFPlaceholder("a", bv3, (should_inc,), True)],
                logic={
                    b_p1: b + 1,
                    result: (~a) | (~b)
                },
                transition={b: should_inc.ite(b_p1, b)},
            )
        model_no_b = verilog_to_model(
            rtl,
            "top",
            important_signals=["should_inc", "a", "a_p1", "result"],
            coi_conf=COIConf.UF_ARGS_COI,
        )
        assert model_no_b.validate()
        assert model_no_b == \
            Model(
                "top",
                inputs=[should_inc],
                outputs=[result],
                state=[a, a_p1],
                # `b` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as an uninterpreted function
                ufs=[UFPlaceholder("b", bv3, (should_inc,), True)],
                logic={
                    a_p1: a + 1,
                    result: (~a) | (~b)
                },
                transition={a: should_inc.ite(a_p1, a)},
            )

    def test_verilog_single_imp_uf_coi_temporal_state(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.

        In this example, the dependency between the output and one of the parent unimportant signals
        occurs across multiple cycles. Therefore, passing the important input variable as argument
        is insufficient; we instead must make the transition function for each elided state variable
        an uninterpreted function.

        Furthermore, every state variable but `b` happens to depend on an important variable, or one
        that is modeled as a UF. Accordingly, only `b` needs an extra degree of freedom argument.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input [1:0] in, input [1:0] ignore, output [1:0] out);
                reg [1:0] a;
                reg [1:0] b;
                reg [1:0] c;
                always @(posedge clk) begin
                    a <= in + 1;
                    c <= b;
                end
                assign b = a & ignore;
                assign out = c;
            endmodule
            """)
        actual_model = verilog_to_model(
            rtl,
            "top",
            important_signals=["out", "in"],
            coi_conf=COIConf.UF_ARGS_COI
        )
        actual_model.print()
        assert actual_model.validate()
        bv2 = smt.BVSort(2)
        in_ = smt.Variable("in", bv2)
        out = smt.Variable("out", bv2)
        exp_model = Model(
            "top",
            inputs=[in_],
            outputs=[out],
            ufs=[
                # current value of b depends on current value of a
                UFPlaceholder("b", bv2, (smt.Variable("a", bv2),), True),
            ],
            next_ufs=[
                # next value of c depends on current value of b
                UFPlaceholder("c", bv2, (smt.Variable("b", bv2),), False), # TODO free_arg should be False
                # next value of a depends on current value of a
                UFPlaceholder("a", bv2, (in_,), False), # TODO free_arg should be False
            ],
            logic={out: smt.Variable("c", bv2)}
        )
        assert exp_model.validate()
        assert actual_model == exp_model

    def test_verilog_single_imp_keep_coi(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.
        `coi_conf` is KEEP_COI, meaning any signal in the COI of an important signal is kept.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input should_inc, output [2:0] result);
                reg [2:0] a;
                reg [2:0] b;
                wire [2:0] a_p1;
                wire [2:0] b_p1;
                always @(posedge clk) begin
                    if (should_inc) begin
                        a = a_p1;
                        b = b_p1;
                    end
                end
                assign a_p1 = a + 3'h1;
                assign b_p1 = b + 3'h1;
                assign result = ~a | ~b;
            endmodule
            """)
        model_no_a = verilog_to_model(rtl, "top", important_signals=["b"], coi_conf=COIConf.KEEP_COI)
        model_no_b = verilog_to_model(rtl, "top", important_signals=["a"], coi_conf=COIConf.KEEP_COI)
        model_no_a.print()
        model_no_b.print()
        bv3 = smt.BVSort(3)
        var = smt.Variable
        a = var("a", bv3)
        a_p1 = var("a_p1", bv3)
        b = var("b", bv3)
        b_p1 = var("b_p1", bv3)
        should_inc = var("should_inc", smt.BoolSort())
        assert model_no_a.validate()
        assert model_no_a == Model(
            "top",
            inputs=[should_inc],
            outputs=[],
            # Even though `b_p1` isn't specified as important, it's still in the COI
            state=[b, b_p1],
            logic={b_p1: b + 1},
            transition={b: should_inc.ite(b_p1, b)},
        )
        assert model_no_b.validate()
        assert model_no_b == Model(
            "top",
            inputs=[should_inc],
            outputs=[],
            # Even though `a_p1` isn't specified as important, it's still in the COI
            state=[a, a_p1],
            logic={a_p1: a + 1},
            transition={a: should_inc.ite(a_p1, a)},
        )

    @pytest.mark.skip()
    def test_verilog_output_unimp(self):
        # TODO what do we do when an output is a dependency of an important signal,
        # but the output itself is non-important
        assert False

    def test_verilog_nested_child_no_coi(self):
        """
        Tests behavior for when a child module itself has another child module.

        Note also that there are many shared signal names.
        """
        rtl = textwrap.dedent("""
            module inner2(input clk, input [3:0] value, output [3:0] o);
                reg [3:0] state;
                always @(posedge clk) begin
                    state = value + 4'h1;
                end
                assign o = state ^ 4'b1111;
            endmodule

            module inner1(input clk, input [3:0] value, output [3:0] o);
                reg [3:0] state;
                wire [3:0] inner_s;
                inner2 inst(
                    .value(value),
                    .o(inner_s)
                );
                always @(posedge clk) begin
                    state = inner_s ^ value;
                end
                assign o = state | 4'b110;
            endmodule

            module top(input clk, input [3:0] value, output [3:0] o);
                reg [3:0] state;
                wire [3:0] inner_s;
                inner1 inst(
                    .value(state),
                    .o(inner_s)
                );
                always @(posedge clk) begin
                    state = inner_s & value;
                end
                assign o = inner_s;
            endmodule
            """)
        bvar = smt.BVVariable
        value = bvar("value", 4)
        o = bvar("o", 4)
        state = bvar("state", 4)
        inner_s = bvar("inner_s", 4)
        exp_inner2 = Model(
            "inner2",
            inputs=[value],
            outputs=[o],
            state=[state],
            logic={o: state ^ smt.BVConst(0b1111, 4)},
            transition={state: value + 1},
        )
        exp_inner1 = Model(
            "inner1",
            inputs=[value],
            outputs=[o],
            state=[state, inner_s],
            instances={"inst": Instance(exp_inner2, {value: value})},
            logic={inner_s: bvar("inst.o", 4), o: state | smt.BVConst(0b0110, 4)},
            transition={state: inner_s ^ value},
        )
        exp_top = Model(
            "top",
            inputs=[value],
            outputs=[o],
            state=[state, inner_s],
            instances={"inst": Instance(exp_inner1, {value: state})},
            logic={inner_s: bvar("inst.o", 4), o: inner_s},
            transition={state: inner_s & value}
        )
        assert exp_inner2.validate()
        assert exp_inner1.validate()
        assert exp_top.validate()
        top = verilog_to_model(rtl, "top")
        top.print()
        inner1 = top.instances["inst"].model
        inner1.print()
        inner2 = inner1.instances["inst"].model
        inner2.print()
        assert inner2.validate()
        assert inner1.validate()
        assert top.validate()
        assert inner2 == exp_inner2
        assert inner1 == exp_inner1
        assert top == exp_top

    @pytest.mark.skip()
    def test_verilog_nested_child_coi(self):
        """
        Tests behavior when COI options are enabled and child submodules are traversed.
        """
        ...
        assert False

    @pytest.mark.skip()
    def test_verilog_reused_child(self):
        """
        Tests when a module has multiple instances within a design.
        """
        # Note: in our case studies, rvmini reuses a module just once (the cache)
        ...
        assert False

