
import textwrap
from typing import List, Optional

import pytest

import easyila.lynth.smt as smt
from easyila.verilog import verilog_to_model, COIConf
from easyila.model import Model

class TestVerilogParse:
    """
    Tests generation of Models from Verilog files.

    On the current version of pyverilog, initial register values are not treated properly, hence
    the need for a reset input.

    pyverilog if branches that are missing an else block also will produce a dummy "dest" variable
    when `tocode` is called, though this does not affect the actual dataflow graph.
    """

    def test_verilog_single_noimp(self):
        """
        Tests model generation of a model from a single RTL module.
        No "important" values are specified.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input rst, input should_inc, output [2:0] result);
                reg [2:0] a;
                wire [2:0] a_p1;
                always @(posedge clk) begin
                    if (rst) begin
                        a = 0;
                    end else if (should_inc) begin
                        a = a_p1;
                    end
                end
                assign a_p1 = a + 1;
                assign result = ~a;
            endmodule
            """
        )
        model = verilog_to_model(rtl, "top")
        model.print()
        bv3 = smt.BVSort(3)
        var = smt.Variable
        assert model == \
            Model(
                "top",
                inputs=[var("should_inc", smt.BoolSort)],
                outputs=[var("result", bv3)],
                state=[var("a", bv3), var("a_p1", bv3)],
                logic={
                    var("a_p1", bv3): smt.OpTerm(smt.Kind.BVAdd, var("a", bv3)),
                    var("result", bv3): smt.OpTerm(smt.Kind.BVNot, var("a", bv3)),
                },
                default_next=[{var("a", bv3): var("a_p1", bv3)}],
                init_values={var("a", bv3): smt.BVConst(0, 3)}
            )

    def test_verilog_always_star(self):
        """
        Tests that dependencies from always @* blocks are placed in the correct cycle.
        """
        ...

    def test_verilog_single_imp_no_parents(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.
        `coi_conf` is NO_COI, meaning every important signal needs to be manually specified.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input rst, input should_inc, output [2:0] result);
                reg [2:0] a;
                reg [2:0] b;
                wire [2:0] a_p1;
                wire [2:0] b_p1;
                always @(posedge clk) begin
                    if (rst) begin
                        a = 0;
                        b = 0;
                    end else if (should_inc) begin
                        a = a_p1;
                        b = b_p1;
                    end
                end
                assign a_p1 = a + 1;
                assign b_p1 = b + 1;
                assign result = ~a | ~b;
            endmodule
            """)
        bv3 = smt.BVSort(3)
        var = smt.Variable
        # TODO to allow for composition of child modules, and specifying important_signals for those
        model_no_a = verilog_to_model(rtl, "top", important_signals=["should_inc", "b", "b_p1", "result"])
        model_no_a.print()
        assert model_no_a == \
            Model(
                "top",
                inputs=[var("should_inc", smt.BoolSort)],
                outputs=[var("result", bv3)],
                state=[var("b", bv3), var("b_p1", bv3)],
                # `a` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as an uninterpreted function
                # TODO namespace collision for should_inc parameter?
                ufs=[smt.UFTerm("a", bv3, var("should_inc", smt.BoolSort))],
                logic={
                    var("b_p1", bv3): smt.OpTerm(smt.Kind.BVAdd, var("b", bv3)),
                    var("result", bv3):
                        smt.OpTerm(
                            smt.Kind.BVOr,
                            (smt.OpTerm(
                                smt.Kind.BVNot,
                                # TODO distinguish between ref and decl?
                                var("a", bv3)
                            ),
                            smt.OpTerm(smt.Kind.BVNot, var("b", bv3))),
                        )
                },
                instructions={
                    # TODO
                },
                init_values={var("b", bv3): smt.BVConst(0, 3)}
            )
        model_no_b = verilog_to_model(rtl, "top", important_signals=["should_inc", "a", "a_p1", "result"])
        assert model_no_b == \
            Model(
                "top",
                inputs=[var("should_inc", smt.BoolSort)],
                outputs=[var("result", bv3)],
                state=[var("a", bv3), var("a_p1", bv3)],
                # `b` appears in the expression for `result`, but is not declared important
                # therefore, it is modeled as an uninterpreted function
                # TODO namespace collision for should_inc parameter?
                ufs=[smt.UFTerm("b", bv3, var("should_inc", smt.BoolSort))],
                logic={
                    var("a_p1", bv3): smt.OpTerm(smt.Kind.BVAdd, var("a", bv3)),
                    var("result", bv3):
                        smt.OpTerm(
                            smt.Kind.BVOr,
                            (smt.OpTerm(smt.Kind.BVNot, var("a", bv3)),
                            smt.OpTerm(
                                smt.Kind.BVNot,
                                # TODO distinguish between ref and decl?
                                var("__UF_result_0", bv3)
                            )),
                        )
                },
                instructions={
                    # TODO
                },
                init_values={var("a", bv3): smt.BVConst(0, 3)}
            )

    def test_verilog_single_imp_with_parents(self):
        """
        Tests generation of a model from a single RTL module with specified important signals.
        `coi_conf` is UF_ARGS_COI, meaning some important signals should be inferred.
        """
        rtl = textwrap.dedent("""\
            module top(input clk, input rst, input shouldinc, output [2:0] result);
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
                assign a_p1 = a + 1;
                assign b_p1 = b + 1;
                assign result = ~a | ~b;
            endmodule
            """)
        # TODO to allow for composition of child modules, and specifying important_signals for those
        model_no_a = verilog_to_model(rtl, "top", important_signals=["b"], coi_conf=COIConf.NO_COI)
        assert model_no_a == \
            Model(
            )
        model_no_b = verilog_to_model(rtl, "top", important_signals=["a"], coi_conf=COIConf.NO_COI)
        assert model_no_b == \
            Model(
            )

    def test_verilog_one_child_module(self):
        rtl = textwrap.dedent("""\
            module inner(input clk, input rst, input i_inner, output o_inner);
                reg [2:0] i_state;
                always @(posedge clk) begin
                    if (rst) begin
                        i_state = 0;
                    end else begin
                        i_state = i_inner | i_state;
                    end
                end
                assign o_inner = i_state[0];
            endmodule

            module top(input clk, input rst, input i_top, output reg o_top);
                reg i_top_last;
                wire i_out_next;
                inner sub(
                    .clk(clk),
                    .rst(rst),
                    .i_inner(i_top_last),
                    .o_inner(i_out_next)
                );
                always @(posedge clk) begin
                    i_top_last = i_top;
                    o_top = i_out_next;
                end
            endmodule
            """
        )
        model = verilog_to_model(rtl, "top")
        assert False