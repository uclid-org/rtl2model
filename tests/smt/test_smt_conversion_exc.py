"""
Tests that no exceptions are raised during conversions of SMT expressions
to different backends.
"""

import itertools

import pytest

import rtl2model.lynth.smt as smt

bv4 = smt.BVSort(4)
x = smt.Variable("x", bv4)
y = smt.Variable("y", bv4)
a = smt.Variable("a", smt.BoolSort())
b = smt.Variable("b", smt.BoolSort())
arr = smt.Variable("arr", smt.ArraySort(bv4, bv4))
exprs = {
    "bvvar": x,
    "bvadd": x + y,
    "bvsub": x - y,
    "bvor": x | y,
    "bvand": x & y,
    "bvnot": ~x,
    "bvxor": x ^ y,
    "extract": x[3:0],
    "concat": x.concat(y),
    "orr": x.orr(),
    "xorr": x.xorr(),
    # TODO unsigned + signed comparison ops
    "ult": x < y,
    "ule": x <= y,
    "zpad": x.zero_pad(smt.BVConst(4, 4)),
    "sext": x.sign_extend(smt.BVConst(4, 4)),
    "sll": x.sll(y),
    "srl": x.srl(y),
    "sra": x.sra(y),
    "boolvar": a,
    "or": a | b,
    "and": a & b,
    "xor": a ^ b,
    "implies": a.implies(b),
    "ite": a.ite(x, y),
    "match": x.match_const({0: a, 1: a, 2: b, 3: b}),
    "select": arr[x],
}

tf = smt.TargetFormat
formats = [tf.CVC5, tf.SYGUS2, tf.VERILOG, tf.UCLID] #, tf.JSON]

# skip = []
# TODO
# skip.extend(itertools.product(["zpad", "sext"], [tf.CVC5, tf.SYGUS2, tf.UCLID]))

class TestSMTConversionException:
    @pytest.mark.parametrize(
        "op,fmt",
        itertools.product(list(exprs.keys()), formats),
        ids=["-".join(pair) for pair in itertools.product(list(exprs.keys()), [f.name for f in formats])]
    )
    def test_conversion(self, op, fmt):
        expr = exprs[op]
        if fmt == tf.CVC5:
            ctx = smt.Solver(backend="cvc5")._cvc5_wrapper
            expr.to_cvc5(ctx)
        else:
            expr.to_target_format(fmt)
        assert True
