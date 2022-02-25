from easyila.verification import *

class TestTestCase:
    def test_simple_expr(self):
        # TODO override operators besides EQ for ergonomics
        r1 = RegRef("r1", 3)
        r2 = RegRef("r2", 3)
        e1 = r1 + r2
        e2 = e1 + BVConst(1, 3)
        verilog = e2.to_verilog()
        assert verilog == "(r1 + r2) + 3'd1"

    def test_type_check(self):
        ... # TODO

    def test_simple_statement(self):
        v = SignalRef("fe_pc", 32)
        w = WireDecl("mywire", 32, v)
        c = BVConst(0x200, 32, base=Base.HEX)
        # TODO fix get_ref ergonomics
        assertion = Assert(w.get_ref() == c)
        verilog = StatementSeq([w, assertion]).to_verilog()
        assert verilog == textwrap.dedent(
            """
            wire mywire [31:0] = fe_pc;
            assert (mywire == 32'h200);
            """
        ).strip()

# # Tester
# def main (args):
#     v = VSignal ("fe_pc", 32)
#     w = VWire("mywire", v, 32)
#     # s = VSignal ("a", 4)
#     c = VConst (200, 32, base_=VBases.HEX)
#     e = (w == c)
#     a = VAssert(e)
#     c = VStmtSeq([a])
#     print(get_formal_block())
