import textwrap

from easyila.model import Model
import easyila.lynth.smt as smt

class TestModelToUclid:
    """
    Tests conversion of Models to uclid modules.

    In many cases, the resulting model will have code duplicated in the `init` and
    `next` blocks, with code in the `next` block usually referencing 'd variables.
    This is necessary because uclid modules will only update outputs when `next` is
    called.

    chiselucl generates "next" variables for every firrtl register, which we do here
    as well.

    TODO compare to just `assuming` values?
    TODO does the "prime everything" approach mess with synth funs? if we make state
        variables arguments to the synth funs, it's fine because we can just prime them,
        but if we add them to the grammar then it may pose a problem
    """

    def test_model2ucl_simple(self):
        bv3 = smt.BVSort(3)
        var = smt.Variable
        i_a = var("i_a", bv3)
        i_b = var("i_b", bv3)
        o_a = var("o_a", bv3)
        o_b = var("o_b", bv3)
        s_a = var("s_a", bv3)
        s_b = var("s_b", bv3)
        model = Model(
            "top",
            inputs=[i_a, i_b],
            outputs=[o_a, o_b],
            state=[s_a, s_b],
            # TODO move s_b into the grammar of uf_b instead
            ufs=[smt.UFTerm("uf_a", bv3, ()), smt.UFTerm("uf_b", bv3, (s_b,))],
            logic={o_a: var("uf_a", bv3) + s_a, o_b: s_a + s_b, s_a: i_a | i_b},
            default_next=[{s_b: i_a[0].ite(i_a, s_b)}]
        )
        model.print()
        # TODO how to get output to appear on same cycle in uclid?
        exp_ucl = textwrap.dedent("""\
            module top {
                input i_a : bv3;
                input i_b : bv3;
                output o_a : bv3;
                output o_b : bv3;
                var s_a : bv3;
                var s_b : bv3;
                var __next_s_b : bv3;
                synthesis function uf_a() : bv3;
                synthesis function uf_b(s_b : bv3) : bv3;

                init {
                    o_a = uf_a() + s_a;
                    o_b = s_a + s_b;
                    s_a = i_a | i_b;
                }

                next {
                    // Transition functions
                    s_b' = __next_s_b;
                    // Combinatorial relations
                    o_a' = uf_a() + s_a';
                    o_b' = s_a' + s_b';
                    s_a' = i_a' | i_b';
                    __next_s_b = if (i_a'[0:0] == 1bv1) then i_a' else s_b';
                }
            }
            """)
        assert model.to_uclid().strip() == exp_ucl.strip()
