"""
Tests for the verification DSL used to write assertions.
"""

import easyila.verification as v
import textwrap

class TestVerifDsl:
    def test_to_verilog_ite(self):
        r = v.RegDecl("counter", 4)
        eq = r.get_ref() == v.BVConst(3, 4)
        stmt = v.IteStatement(
            eq,
            # trivial body
            [v.Assert(r.get_ref() == v.BVConst(3, 4))],
            None
        )
        expected = textwrap.dedent(
            f"""\
            if (counter == 4'd3) begin
                assert (counter == 4'd3);
            end
            """.rstrip()
        )
        assert stmt.to_verilog() == expected

    def test_to_verilog_always_at(self):
        r = v.RegDecl("counter", 4, init_value=0)
        eq = r.get_ref() == v.BVConst(3, 4)
        add_one = v.Assignment(
            r.get_ref(),
            v.BinOpExpr(v.Operators.BVAdd, r.get_ref(), v.BVConst(1, 4))
        )
        stmt = v.StatementSeq([
            r,
            v.AlwaysAt(v.Edge.POS, v.SignalRef("clk"), add_one)
        ])
        expected = textwrap.dedent(
            f"""\
            reg [3:0] counter = 0;
            always @(posedge (clk)) begin
                counter = counter + 4'd1;
            end
            """.rstrip()
        )
        assert stmt.to_verilog() == expected

    def test_to_verilog_ite_nested(self):
        r = v.RegDecl("counter", 4)
        eq = r.get_ref() == v.BVConst(3, 4)
        stmt = v.IteStatement(
            eq,
            # trivial body
            v.IteStatement(
                eq,
                [v.Assert(r.get_ref() == v.BVConst(3, 4))],
                None,
            ),
            None,
        )
        expected = textwrap.dedent(
            f"""\
            if (counter == 4'd3) begin
                if (counter == 4'd3) begin
                    assert (counter == 4'd3);
                end
            end
            """.rstrip()
        )
        print("EXPECTED")
        print(expected)
        print("===")
        print("ACTUAL")
        print(stmt.to_verilog())
        assert stmt.to_verilog() == expected