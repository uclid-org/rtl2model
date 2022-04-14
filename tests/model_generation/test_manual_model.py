
import pytest

import easyila.lynth.smt as smt
from easyila.model import *

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
            default_next={a: should_inc.ite(a_p1, a)},
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
            default_next={
                s_top: smt.Variable("sub.s", bv3)
            },
            logic={
                o_top: s_top + smt.Variable("sub.o", bv3)
            }
        )
        assert top.validate()

    def test_model_flatten_state(self):
        """
        Tests pushing the transition relations of a module into submodules.
        """
        bv3 = smt.BVSort(3)
        a = smt.Variable("a", bv3)
        state = smt.Variable("state", bv3)
        next_state = smt.Variable("__next_state", bv3)
        state_uf_var = smt.Variable("state_uf", bv3)
        logic = smt.Variable("logic", bv3)
        out = smt.Variable("out", bv3)
        top = Model(
            "top",
            inputs=[a],
            outputs=[out],
            state=[state, logic],
            default_next={state: logic & smt.Variable("uf", bv3)},
            logic={logic: a + state_uf_var, out: state + 1},
            ufs=[UFPlaceholder("uf", bv3, (), True)],
            next_ufs=[UFPlaceholder("state_uf", bv3, (), True)],
        )
        assert top.validate()
        assert top.is_stateful
        actual_flattened = top.flatten_state()
        exp_flattened = Model(
            "top",
            inputs=[a],
            outputs=[out],
            state=[state],
            instances={
                "__logic__top_inst": Instance(
                    Model(
                        "__logic__top",
                        inputs=[a, state, state_uf_var],
                        outputs=[out, next_state],
                        logic={
                            logic: a + state_uf_var,
                            next_state: logic & smt.Variable("uf", bv3),
                            out: state + 1,
                        },
                        ufs=[UFPlaceholder("uf", bv3, (), True)]
                    ),
                    {
                        a: a,
                        state: state,
                        state_uf_var: state_uf_var
                    },
                )
            },
            default_next={
                state: smt.Variable("__logic__top_inst.__next__state", bv3),
            },
            logic={
                out: smt.Variable("__logic__top_inst.out", bv3),
            },
            next_ufs=[UFPlaceholder("state_uf", bv3, (), True)],
        )
        assert exp_flattened.validate()
        assert actual_flattened.validate()
        assert actual_flattened == exp_flattened
        assert not actual_flattened.instances["__logic__top_inst"].model.is_stateful

    def test_model_variable_dce(self):
        """
        Tests eliminating unused variables from a model.
        Inputs cannot be eliminated because they change the compositional
        behavior of models.
        """
        v = smt.Variable
        bv2 = smt.BVSort(2)
        a = v("a", bv2)
        b = v("b", bv2)
        s0 = v("s0", bv2)
        s1 = v("s1", bv2)
        s2 = v("s2", bv2)
        s3 = v("s3", bv2)
        s4 = v("s4", bv2)
        o = v("o", bv2)
        top = Model(
            "top",
            inputs=[a, b], # b is unused
            outputs=[o],
            # s0 is used through s2, s1 is unused, s2 is used directly, s3/s4 are used through a used UF
            state=[s0, s1, s2, s3, s4],
            # uf0 is used, uf1 is not used
            ufs=[
                UFPlaceholder("uf0", bv2, (s3,), False),
                UFPlaceholder("uf1", bv2, (s1,), False),
            ],
            # nuf0 is used, nuf1 is not used
            next_ufs=[
                UFPlaceholder("nuf0", bv2, (s4,), False),
                UFPlaceholder("nuf1", bv2, (s1,), False),
            ],
            logic={
                o: s2 + v("uf0", bv2) + v("nuf0", bv2),
                s2: s0 + 2,
                s1: s0 & b & v("uf1", bv2) & v("nuf1", bv2),
            },
            default_next={
                s0: a + 1,
                s3: a + 1,
                s4: a + 1,
            },
        )
        assert top.validate()
        actual = top.eliminate_dead_code()
        expected = Model(
            "top",
            inputs=[a, b], # b is unused
            outputs=[o],
            state=[s0, s2, s3, s4],
            ufs=[
                UFPlaceholder("uf0", bv2, (s3,), False),
            ],
            next_ufs=[
                UFPlaceholder("nuf0", bv2, (s4,), False),
            ],
            logic={
                o: s2 + v("uf0", bv2) + v("nuf0", bv2),
                s2: s0 + 2,
            },
            default_next={
                s0: a + 1,
                s3: a + 1,
                s4: a + 1,
            },
        )
        assert actual.validate()
        assert actual == expected
