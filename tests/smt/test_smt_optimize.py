
import rtl2synth.lynth.smt as smt

class TestSMTOptimize:

    def test_bvconst_index(self):
        expr = smt.BVConst(0xABCD, 16)[11:0]
        assert expr.eval({}) == smt.BVConst(0xBCD, 12)

    def test_constfold(self):
        # Wrapping addition
        expr = smt.BVConst(0x8, 4) + smt.BVConst(0x8, 4)
        assert expr.optimize() == smt.BVConst(0, 4)

    # TODO add cases for &ing, |ing with all 1s/all 0s

    def test_if_branch_elim(self):
        expr = smt.BoolConst.F.ite(smt.BVConst(1, 2), smt.BVConst(3, 2))
        assert expr.optimize() == smt.BVConst(3, 2)

    def test_if_constfold_branch_elim(self):
        # Wrapping addition, evaluates to 0
        cond = (smt.BVConst(0x8, 4) + smt.BVConst(0x8, 4)).op_ne(smt.BVConst(0, 4))
        expr = cond.ite(smt.BVConst(1, 2), smt.BVConst(3, 2))
        assert expr.optimize() == smt.BVConst(3, 2)
        # Condition is a constant, but branches are not
        a = smt.Variable("a", smt.BVSort(2))
        b = smt.Variable("b", smt.BVSort(2))
        expr = cond.ite(a, b)
        assert expr.optimize() == b

    def test_match_branch_elim(self):
        # Condition is 3bv2
        cond = smt.BVConst(2, 2) + smt.BVConst(1, 2)
        vs = [smt.Variable(f"v_{i}", smt.BVSort(2)) for i in range(4)]
        expr = cond.match_const({i: v for i, v in enumerate(vs)})
        assert expr.optimize() == smt.Variable("v_3", smt.BVSort(2))

