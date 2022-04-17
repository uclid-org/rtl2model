
import pytest

import easyila.lynth.smt as smt
from easyila.model import *

class TestModelToAssertions:
    """
    Tests generating SMT assertions from a Model object.
    """

    def test_module_assertions_simple(self):
        v = smt.Variable
        bv3 = smt.BVSort(3)
        a = v("a", bv3)
        b = v("b", bv3)
        o = v("o", bv3)
        s0 = v("s0", bv3)
        s1 = v("s1", bv3)
        all_vars = [a, b, o, s0, s1]
        top = Model(
            "top",
            inputs=[a, b],
            outputs=[o],
            state=[s0, s1],
            logic={
                o: s0 + 2,
                s0: s1 & a,
            },
            default_next={
                s1: b.op_eq(1).ite(s1 + 1, s1),
            }
        )
        assert top.validate()
        # In the returned solver, each variable has a copy for the start state
        # and one in the next state.
        # Per the sygus standard, having a dot in variable names is fine
        BASE_PREFIX = "__BASE."
        STEP_PREFIX = "__STEP."
        base_s1 = s1.add_prefix(BASE_PREFIX)
        o_expr = s0.add_prefix(BASE_PREFIX) + 2
        s0_expr = base_s1 & a.add_prefix(BASE_PREFIX)
        s1_expr = b.add_prefix(BASE_PREFIX).op_eq(1).ite(base_s1 + 1, base_s1)
        exp_solver = smt.Solver(
            constraints=[
                o.add_prefix(BASE_PREFIX).op_eq(o_expr),
                s0.add_prefix(BASE_PREFIX).op_eq(s0_expr),
                s1.add_prefix(STEP_PREFIX).op_eq(s1_expr),
            ]
        )
        actual_solver = top.to_solver()
        assert actual_solver == exp_solver

    def test_module_assertions_uf(self):
        pytest.skip()

    def test_module_assertions_multiple(self):
        """Tests generating assertions across module boundaries."""
        pytest.skip()
