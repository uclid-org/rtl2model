
import textwrap

import rtl2synth.lynth.smt as smt

class TestSygus:
    """
    Sanity checks for SyGuS functions.
    """

    def test_synth_one_simple(self):
        """
        Tests synthesizing a simple function (addition).
        """
        bv3 = smt.BVSort(3)
        v = smt.Variable
        x = v("x", bv3)
        y = v("y", bv3)
        sf = smt.SynthFun("add", (x, y), bv3)
        s = smt.Solver(
            variables=[x, y],
            synthfuns=[sf],
            constraints=[sf.apply(x, y).op_eq(x + y)],
        )
        result = s.check_synth()
        print(s.get_sygus2())
        assert result.is_unsat
        print(result.solution["add"].body.to_sygus2())
        assert result.solution == {"add": smt.LambdaTerm((x, y), x + y)}

    def test_synth_two_simple_with_grammar(self):
        """
        Tests synthesizing two simple functions with a specified grammar.
        """
        bv3 = smt.BVSort(3)
        v = smt.Variable
        x = v("x", bv3)
        start = v("start", bv3)
        # f0 and f1 are allowed to increment, or mask the lowest bit.
        # Thus, f0(3) == 2 and f1(3) == 5 should lead to
        # f0(x, y) = x & 6 and f1(x, y) = x + 1 + 1
        f0 = smt.SynthFun(
            "f0",
            (x,),
            bv3,
            grammar=smt.Grammar(
                bound_vars=(x,),
                nonterminals=(start,),
                terms={start: (start + 1, start & smt.BVConst(6, 3))}
            )
        )
        f1 = smt.SynthFun(
            "f1",
            (x,),
            bv3,
            grammar=smt.Grammar(
                bound_vars=(x,),
                nonterminals=(start,),
                terms={start: (start + 1, start & smt.BVConst(6, 3))}
            )
        )
        s = smt.Solver(
            variables=[x],
            synthfuns=[f0, f1],
            constraints=[
                f0.apply(smt.BVConst(3, 3)).op_eq(smt.BVConst(2, 3)),
                f1.apply(smt.BVConst(3, 3)).op_eq(smt.BVConst(5, 3))
            ],
        )
        print(s.get_sygus2())
        result = s.check_synth()
        assert result.solution == {
            "f0": smt.LambdaTerm((x,), x & smt.BVConst(6, 3)),
            "f1": smt.LambdaTerm((x,), (x + 1) + 1),
        }

    def test_synth_one_to_sygus2(self):
        bv3 = smt.BVSort(3)
        v = smt.Variable
        x = v("x", bv3)
        y = v("y", bv3)
        sf = smt.SynthFun("add", (x, y), bv3)
        s = smt.Solver(
            variables=[x, y],
            synthfuns=[sf],
            constraints=[sf.apply(x, y).op_ne(x + y)],
        )
        sygus_block = s.get_sygus2()
        expected = textwrap.dedent("""\
            (set-logic AUFBV)
            (declare-var x (_ BitVec 3))
            (declare-var y (_ BitVec 3))
            (synth-fun add ((x (_ BitVec 3)) (y (_ BitVec 3))) (_ BitVec 3))
            (constraint (not (= (add x y) (bvadd x y))))
            (check-synth)
            """
        )
        print(sygus_block)
        assert sygus_block.strip() == expected.strip()
