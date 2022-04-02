
import easyila.lynth.smt as smt

class TestSMTOptimize:
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

    def test_match_branch_elim(self):
        ...

    def test_match_constfold_branch_elim(self):
        ...
