
import pytest

import easyila.lynth.smt as smt
from easyila.model import Model, Instance

class TestManualModel:
    """
    Tests manual construction and composition of models, and ensure things don't crash.
    """

    def test_error_redclare(self):
        """
        Validation on this model should fail because a variable is declared both input and output.
        """
        bv3 = smt.BVSort(3)
        a = smt.Variable("a", bv3)
        model = Model("top", inputs=[a], outputs=[a], logic={a: smt.BVConst(0, 3)})
        assert not model.validate()

    def test_error_no_logic(self):
        """
        Validation on this model should fail because a state variable is declared with no logic
        or transition relation.
        """
        bv3 = smt.BVSort(3)
        a = smt.Variable("a", bv3)
        model = Model("top", state=[a])
        assert not model.validate()

    def test_simple_model(self):
        bv3 = smt.BVSort(3)
        var = smt.Variable
        a = var("a", bv3)
        a_p1 = var("a_p1", bv3)
        should_inc = smt.BoolVariable("should_inc")
        model = Model(
            "top",
            inputs=[should_inc],
            outputs=[var("result", bv3)],
            state=[a, a_p1],
            logic={
                a_p1: a + 1,
                var("result", bv3): ~a,
            },
            default_next=[{a: should_inc.ite(a_p1, a)}],
        )
        assert model.validate()

    def test_composed_model(self):
        bv3 = smt.BVSort(3)
        a_sub = smt.Variable("a", bv3)
        o_sub = smt.Variable("o", bv3)
        s_sub = smt.Variable("s", bv3)
        submodule = Model(
            "sub",
            inputs=[a_sub],
            state=[s_sub],
            outputs=[o_sub],
            logic={
                s_sub: smt.BVConst(1, 3),
                o_sub: s_sub + 1
            }
        )
        assert submodule.validate()
        a_top = smt.Variable("a", bv3)
        o_top = smt.Variable("o", bv3)
        s_top = smt.Variable("s", bv3)
        top = Model(
            "top",
            inputs=[a_top],
            state=[s_top],
            outputs=[o_top],
            instances={"sub": Instance(submodule, {a_sub: a_top})},
            default_next=[{
                s_top: smt.Variable("sub.s", bv3)
            }],
            logic={
                o_top: s_top + smt.Variable("sub.o", bv3)
            }
        )
        assert top.validate()

    def test_model_variable_dce(self):
        """
        Tests eliminating unused variables from a model.
        Inputs cannot be eliminated because they change the compositional
        behavior of models.
        """
        ...
        assert False
