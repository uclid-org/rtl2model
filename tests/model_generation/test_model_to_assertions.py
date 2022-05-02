
import pytest

import easyila.lynth.smt as smt
from easyila.model import *

BASE_PREFIX = "__BASE."
STEP_PREFIX = "__STEP."

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
        top = Model(
            "top",
            inputs=[a, b],
            outputs=[o],
            state=[s0, s1],
            logic={
                o: s0 + 2,
                s0: s1 & a,
            },
            transition={
                s1: b.op_eq(1).ite(s1 + 1, s1),
            }
        )
        assert top.validate()
        # In the returned solver, each variable has a copy for the start state
        # and one in the next state.
        # Per the sygus standard, having a dot in variable names is fine
        base_a = a.add_prefix(BASE_PREFIX)
        base_b = b.add_prefix(BASE_PREFIX)
        base_o = o.add_prefix(BASE_PREFIX)
        base_s0 = s0.add_prefix(BASE_PREFIX)
        base_s1 = s1.add_prefix(BASE_PREFIX)
        step_s1 = s1.add_prefix(STEP_PREFIX)
        o_expr = base_s0 + 2
        s0_expr = base_s1 & base_a
        s1_expr = base_b.op_eq(1).ite(base_s1 + 1, base_s1)
        exp_solver = smt.Solver(
            variables=[base_a, base_b, base_o, base_s0, base_s1, step_s1],
            constraints=[
                base_o.op_eq(o_expr),
                base_s0.op_eq(s0_expr),
                step_s1.op_eq(s1_expr),
            ]
        )
        print("=== EXPECTED ===")
        print(exp_solver.get_sygus2())
        actual_solver = top.to_solver()
        print("=== ACTUAL ===")
        print(actual_solver.get_sygus2())
        assert actual_solver.get_sygus2() == exp_solver.get_sygus2()

    def test_module_assertions_uf(self):
        """
        Tests generating a solver from a model with UFs.

        s0 is a UF that depends on a and b, and has an added degree of freedom variable.
        s2 is a UF that depends on a and s1, and has NO added degree of freedom variable.
        s3' (note the prime) is a UF that depends on b and s2, and has an added degree of freedom.
        """
        v = smt.Variable
        bv3 = smt.BVSort(3)
        a = v("a", bv3)
        b = v("b", bv3)
        o = v("o", bv3)
        s1 = v("s1", bv3)
        top = Model(
            "top",
            inputs=[a, b],
            outputs=[o],
            state=[s1],
            logic={
                o: v("s0", bv3) + v("s2", bv3)
            },
            transition={
                s1: b.op_eq(v("s3", bv3)).ite(s1 + 1, s1),
            },
            ufs=[
                UFPlaceholder("s0", bv3, (a, b), True),
                UFPlaceholder("s2", bv3, (a, s1), False),
            ],
            next_ufs=[
                UFPlaceholder("s3", bv3, (b, v("s2", bv3)), True),
            ],
        )
        assert top.validate()
        base_a = a.add_prefix(BASE_PREFIX)
        base_b = b.add_prefix(BASE_PREFIX)
        base_o = o.add_prefix(BASE_PREFIX)
        base_s1 = s1.add_prefix(BASE_PREFIX)
        step_s1 = s1.add_prefix(STEP_PREFIX)
        free_s0 = v("__FREE.s0", bv3)
        uf_s0 = smt.UFTerm("s0", bv3, (a, b, free_s0))
        uf_s2 = smt.UFTerm("s2", bv3, (a, s1))
        base_s3 = v("__BASE.s3", bv3)
        free_s3 = v("__FREE.s3", bv3)
        uf_s3 = smt.UFTerm("s0", bv3, (b, v("s2", bv3), free_s3))
        exp_solver = smt.Solver(
            variables=[
                base_a, base_b, base_o, base_s1, step_s1,
                free_s0, base_s3, free_s3,
            ],
            constraints=[
                base_o.op_eq(
                    uf_s0.apply(base_a, base_b, free_s0) + uf_s2.apply(base_a, base_s1)
                ),
                step_s1.op_eq(
                    base_b.op_eq(base_s3).ite(
                        base_s1 + 1,
                        base_s1
                    )
                ),
            ]
        )
        actual_solver = top.to_solver()
        print("=== EXPECTED ===")
        print(exp_solver.get_sygus2())
        actual_solver = top.to_solver()
        print("=== ACTUAL ===")
        print(actual_solver.get_sygus2())
        assert actual_solver.get_sygus2() == exp_solver.get_sygus2()

    def test_module_assertions_hierarchy(self):
        """Tests generating assertions across module boundaries."""
        v = smt.Variable
        bv3 = smt.BVSort(3)
        a = v("a", bv3)
        b = v("b", bv3)
        o = v("o", bv3)
        s1 = v("s1", bv3)
        sub = Model(
            "sub",
            inputs=[a, b],
            outputs=[o],
            state=[s1],
            logic={o: s1 + 1},
            transition={s1: a + b},
        )
        top = Model(
            "top",
            inputs=[a, b],
            outputs=[o],
            state=[s1],
            instances={"sub": Instance(sub, {a: a, b: s1})},
            logic={o: v("sub.o", bv3)},
            transition={s1: a + b},
        )
        base_a = a.add_prefix(BASE_PREFIX)
        base_b = b.add_prefix(BASE_PREFIX)
        base_o = o.add_prefix(BASE_PREFIX)
        base_s1 = s1.add_prefix(BASE_PREFIX)
        step_s1 = s1.add_prefix(STEP_PREFIX)
        base_sub_a = a.add_prefix(BASE_PREFIX + "sub.")
        base_sub_b = b.add_prefix(BASE_PREFIX + "sub.")
        base_sub_o = o.add_prefix(BASE_PREFIX + "sub.")
        base_sub_s1 = s1.add_prefix(BASE_PREFIX + "sub.")
        step_sub_s1 = s1.add_prefix(STEP_PREFIX + "sub.")
        exp_solver = smt.Solver(
            variables=[
                base_a, base_b, base_o, base_s1, step_s1,
                base_sub_a, base_sub_b, base_sub_o,
                base_sub_s1, step_sub_s1,
            ],
            constraints=[
                base_o.op_eq(base_sub_o),
                step_s1.op_eq(base_a + base_b),
                base_sub_a.op_eq(base_a),
                base_sub_b.op_eq(base_s1),
                base_sub_o.op_eq(base_sub_s1 + 1),
                step_sub_s1.op_eq(base_sub_a + base_sub_b),
            ]
        )
