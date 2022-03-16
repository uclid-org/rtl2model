"""
Provides in-memory representations of SMT expressions and grammars, which can then be translated
to solver backends like CVC5 and Z3.

TODO add str methods to everything
"""

from abc import ABC, ABCMeta, abstractmethod
from dataclasses import dataclass
from enum import Enum, EnumMeta, auto
from typing import ClassVar, Dict, List, Set, Tuple, Optional

import pycvc5

import easyila.verification as v

# === BEGIN SMT Sorts ===

class Sort(ABC):
    @staticmethod
    def from_cvc5(cvc5_sort):
        if cvc5_sort.isBitVector():
            return BVSort(cvc5_sort.getBitVectorSize())
        elif cvc5_sort.isBoolean():
            return BoolSort()
        elif cvc5_sort.isFunction():
            return FunctionSort.from_cvc5(cvc5_sort)
        elif cvc5_sort.isUninterpretedSort():
            return UninterpretedSort.from_cvc5(cvc5_sort)
        raise NotImplementedError(f"Cannot convert from CVC5 sort {cvc5_sort}")

    @abstractmethod
    def _to_cvc5(self, cvc5_ctx):
        raise NotImplementedError()

    @abstractmethod
    def to_sygus2(self):
        raise NotImplementedError()

    @abstractmethod
    def to_verilog_str(self):
        raise NotImplementedError()

    @abstractmethod
    def to_uclid(self):
        raise NotImplementedError()


@dataclass(frozen=True)
class BVSort(Sort):
    bitwidth: int

    def _to_cvc5(self, cvc5_ctx):
        # No need to memoize, since the context already memoizes sorts
        # In fact, memoizing on this class is incorrect in case the context is cleared
        return cvc5_ctx.solver.mkBitVectorSort(self.bitwidth)

    def to_sygus2(self):
        return f"(_ BitVec {self.bitwidth})"

    def to_verilog_str(self):
        return f"[{int(self.bitwidth) - 1}:0]"

    def to_uclid(self):
        return f"bv{self.bitwidth}"


@dataclass(frozen=True)
class BoolSort(Sort):
    def _to_cvc5(self, cvc5_ctx):
        return cvc5_ctx.solver.getBooleanSort()

    def to_sygus2(self):
        return "Bool"

    def to_verilog_str(self):
        return ""

    def to_uclid(self):
        return "boolean"

@dataclass(frozen=True)
class FunctionSort(Sort):
    args: Tuple[Sort, ...] # argument sorts
    codomain: Sort # return sort

    @staticmethod
    def from_cvc5(cvc5_sort):
        assert cvc5_sort.isFunction()
        return FunctionSort(
            [Sort.from_cvc5(s) for s in cvc5_sort.getFunctionDomainSorts()],
            Sort.from_cvc5(cvc5_sort.getFunctionCodomainSort())
        )

    def _to_cvc5(self, cvc5_ctx):
        return cvc5_ctx.solver.mkFunctionSort([self.args._to_cvc5(cvc5_ctx)], self.codomain._to_cvc5(cvc5_ctx))

    def to_sygus2(self):
        return "(-> " + " ".join([a.to_sygus2() for a in self.args]) + self.codomain.to_sygus2() + ")"

    def to_verilog_str(self):
        raise NotImplementedError(f"Cannot convert {type(self).__name__} to verilog")

    def to_uclid(self):
        raise NotImplementedError(f"Cannot convert {type(self).__name__} to uclid")

@dataclass(frozen=True)
class UninterpretedSort(Sort):
    name: str

    @staticmethod
    def from_cvc5(cvc5_sort):
        assert cvc5_sort.isUninterpretedSort()
        return UninterpretedSort(cvc5_sort.getUninterpretedSortName())

    def _to_cvc5(self, cvc5_ctx):
        # TODO need to memoize?
        return cvc5_ctx.solver.mkUninterpretedSort(self.name)

    def to_sygus2(self):
        return self.name

    def to_verilog_str(self):
        raise NotImplementedError(f"Cannot convert {type(self).__name__} to verilog")

    def to_uclid(self):
        raise NotImplementedError(f"Cannot convert {type(self).__name__} to uclid")

# === END SMT Sorts ===

class Kind(Enum):
    # https://cvc5.github.io/docs/api/cpp/kind.html
    BVAdd   = auto()
    BVSub   = auto()
    BVOr    = auto()
    BVAnd   = auto()
    BVNot   = auto()
    BVXor   = auto()
    Or      = auto()
    And     = auto()
    Not     = auto()
    Xor     = auto()
    Implies = auto()
    Ite     = auto()
    Lambda  = auto()
    Equal   = auto()
    Exists  = auto()
    ForAll  = auto()

    def _to_cvc5(self, _cvc5_ctx):
        try:
            return _OP_KIND_MAPPING[self]
        except KeyError:
            raise NotImplementedError(f"cannot convert kind {self}")

    @staticmethod
    def from_cvc5(cvc5_kind):
        try:
            return _OP_KIND_REV_MAPPING[cvc5_kind]
        except KeyError:
            raise NotImplementedError(f"cannot convert CVC5 kind {cvc5_kind}")


# Maps our Kind class to pycvc5.Kind...
_OP_KIND_MAPPING = {
    Kind.BVAdd: pycvc5.Kind.BVAdd,
    Kind.BVSub: pycvc5.Kind.BVSub,
    Kind.BVOr: pycvc5.Kind.BVOr,
    Kind.BVAnd: pycvc5.Kind.BVAnd,
    Kind.BVNot: pycvc5.Kind.BVNot,
    Kind.BVXor: pycvc5.Kind.BVXor,
    Kind.Or: pycvc5.Kind.Or,
    Kind.And: pycvc5.Kind.And,
    Kind.Not: pycvc5.Kind.Not,
    Kind.Xor: pycvc5.Kind.Xor,
    Kind.Implies: pycvc5.Kind.Implies,
    Kind.Ite: pycvc5.Kind.Ite,
    Kind.Lambda: pycvc5.Kind.Lambda,
    Kind.Equal: pycvc5.Kind.Equal,
    Kind.Exists: pycvc5.Kind.Exists,
    Kind.ForAll: pycvc5.Kind.Forall,
}
# ...and vice versa
_OP_KIND_REV_MAPPING = {v: k for k, v in _OP_KIND_MAPPING.items()}

_OP_SYGUS_SYMBOLS = {
    Kind.BVAdd: "bvadd",
    Kind.BVSub: "bvsub",
    Kind.BVOr: "bvor",
    Kind.BVAnd: "bvand",
    Kind.BVNot: "bvnot",
    Kind.BVXor: "bvxor",
    Kind.Or: "or",
    Kind.And: "and",
    Kind.Not: "not",
    Kind.Xor: "xor",
    Kind.Equal: "eq",
    Kind.Ite: "ite",
    Kind.Exists: "exists",
    Kind.ForAll: "forall",
}


# === BEGIN SMT TERMS ===

class Term(ABC):
    def _op_type_check(self, other):
        assert isinstance(other, Term), f"cannot add {self} with {other}"
        assert hasattr(self, "sort")
        assert hasattr(other, "sort")
        assert self.sort == other.sort, f"cannot add value of sort {self.sort} to {other.sort}"

    # === OPERATOR OVERRIDES ===
    def ite(self, t_term, f_term):
        """
        Constructs an ITE expression with this variable as condition.

        If this term is of sort BV1, then an expression is automatically added to
        check if this is equal to the constant 1bv1.
        """
        if isinstance(self.sort, BVSort):
            assert self.sort.bitwidth == 1
            cond = OpTerm(Kind.Eq, (self, BVConst(1, self.sort.bitwidth)))
        else:
            assert isinstance(self.sort, BoolSort)
            cond = self
        t_term._op_type_check(f_term)
        return OpTerm(Kind.Ite, (cond, t_term, f_term))

    def __lt__(self, other):
        self._op_type_check(other)
        ...

    def __le__(self, other):
        self._op_type_check(other)
        ...
        # return OpTerm(Kind.BVLe, self, other)

    def op_eq(self, other):
        """
        We can't override __eq__ without breaking a decent amount of stuff, so
        op_eq is syntactic sugar for an equality expression instead.
        """
        self._op_type_check(other)
        return OpTerm(Kind.Equal, (self, other))

    def __ne__(self, other):
        self._op_type_check(other)
        return OpTerm(Kind.Not, (OpTerm(Kind.Equal, (self, other)),))

    def __gt__(self, other):
        self._op_type_check(other)
        ...

    def __ge__(self, other):
        self._op_type_check(other)
        ...

    def __add__(self, other):
        if isinstance(other, int):
            # Automatically generate appropriate-width constant
            assert isinstance(self.sort, BVSort)
            other = BVConst(other, self.sort.bitwidth)
        else:
            self._op_type_check(other)
        return OpTerm(Kind.BVAdd, (self, other))

    def __and__(self, other):
        self._op_type_check(other)
        if isinstance(self.sort, BoolSort):
            op = Kind.And
        else:
            op = Kind.BVAnd
        return OpTerm(op, (self, other))

    def __invert__(self):
        if isinstance(self.sort, BoolSort):
            op = Kind.Not
        else:
            op = Kind.BVNot
        return OpTerm(op, (self,))

    def __neg__(self):
        ...

    def __or__(self, other):
        self._op_type_check(other)
        if isinstance(self.sort, BoolSort):
            op = Kind.Or
        else:
            op = Kind.BVOr
        return OpTerm(op, (self, other))

    def __rshift__(self, other):
        self._op_type_check(other)
        ...

    def __sub__(self, other):
        self._op_type_check(other)
        ...

    def __xor__(self, other):
        self._op_type_check(other)
        if isinstance(self.sort, BoolSort):
            op = Kind.Xor
        else:
            op = Kind.BVXor
        return OpTerm(op, (self, other))

    # === ABSTRACT AND SHARED STATIC METHODS ===
    @staticmethod
    def from_cvc5(cvc5_term):
        from pycvc5 import Kind as k
        cvc5_kind = cvc5_term.getKind()
        if cvc5_kind == k.Variable:
            return Variable.from_cvc5(cvc5_term)
        elif cvc5_kind == k.Lambda:
            return LambdaTerm.from_cvc5(cvc5_term)
        elif cvc5_kind in (k.Exists, k.Forall):
            return QuantTerm.from_cvc5(cvc5_term)
        elif cvc5_kind == k.ConstBV:
            return BVConst.from_cvc5(cvc5_term)
        elif cvc5_kind in _OP_KIND_REV_MAPPING:
            return OpTerm.from_cvc5(cvc5_term)

        # TODO what corresponds to UFTerm?
        raise NotImplementedError("Cannot convert from CVC5 term of kind " + str(cvc5_kind))

    @property
    @abstractmethod
    def sort(self):
        raise NotImplementedError()

    @abstractmethod
    def _to_cvc5(self, cvc5_ctx):
        raise NotImplementedError()

    @abstractmethod
    def to_verilog_str(self):
        raise NotImplementedError()

    @abstractmethod
    def to_sygus2(self):
        raise NotImplementedError()

    @abstractmethod
    def to_verif_dsl(self):
        """
        Converts this term into an equivalent in the verification DSL.
        """
        raise NotImplementedError()

    # @abstractmethod
    def to_uclid(self):
        raise NotImplementedError

    @property
    @abstractmethod
    def _has_children(self):
        raise NotImplementedError()


# Needed to be able to make BoolConst sealed
class _TermMeta(ABCMeta, EnumMeta):
    pass


@dataclass(frozen=True)
class Variable(Term):
    """
    This class represents both variable declarations and variabl references.
    TODO separate them?
    """

    name: str
    _sort: Sort

    @staticmethod
    def from_cvc5(cvc5_term):
        if cvc5_term.getKind() != pycvc5.Kind.Variable:
            raise TypeError("Variable must be translated from pycvc5.Kind.Variable, instead got " + str(cvc5_term.getKind()))
        # it seems like cvc5 will wrap the variable name in |var| if there are square brackets inside
        # so we need to strip those off
        name = str(cvc5_term)
        # technically fails if NAME is length 1, but at that point we don't care anymore
        if name[0] == "|" and name[-1] == "|":
            name = name[1:-1]
        return Variable(name, Sort.from_cvc5(cvc5_term.getSort()))

    @property
    def sort(self):
        return self._sort

    def _to_cvc5(self, cvc5_ctx):
        if self in cvc5_ctx.terms:
            return cvc5_ctx.terms[self]
        else:
            v = cvc5_ctx.solver.mkVar(self.sort._to_cvc5(cvc5_ctx), self.name)
            cvc5_ctx.terms[self] = v
            return v

    def to_verilog_str(self):
        return self.name

    @property
    def _has_children(self):
        return False

    def to_sygus2(self):
        return self.name

    def to_uclid(self):
        return self.name

    def to_verif_dsl(self):
        # TODO handle booleans
        assert isinstance(self.sort, BVSort)
        return v.WireOrRegRef(self.name, self.sort.bitwidth)


BoolVariable = lambda s: Variable(s, BoolSort())
BVVariable = lambda s, w: Variable(s, BVSort(w))


@dataclass(frozen=True)
class OpTerm(Term):
    kind: Kind
    args: Tuple[Term, ...]

    @property
    def sort(self):
        # TODO better type checking
        bvops = { Kind.BVAdd, Kind.BVSub, Kind.BVOr, Kind.BVAnd, Kind.BVXor, Kind.BVNot, Kind.Implies }
        if self.kind in bvops:
            return self.args[0].sort
        if self.kind == Kind.Ite:
            return self.args[1].sort
        bitops = { Kind.Or, Kind.And, Kind.Xor, Kind.Not, Kind.Equal }
        if self.kind in bitops:
            return BoolSort()
        raise NotImplementedError(f"Cannot get Sort for kind {self.kind}")

    @staticmethod
    def from_cvc5(cvc5_term):
        """
        Translates the provided cvc5 Term object into an OpTerm.
        """
        cvc5_kind = cvc5_term.getKind()
        if cvc5_kind not in _OP_KIND_REV_MAPPING:
            raise TypeError("OpTerm cannot be translated from " + str(cvc5_kind))
        kind = Kind.from_cvc5(cvc5_kind)
        return OpTerm(kind, tuple([Term.from_cvc5(t) for t in cvc5_term]))

    def _to_cvc5(self, cvc5_ctx):
        cvc5_kind = self.kind._to_cvc5(self)
        t = cvc5_ctx.solver.mkTerm(cvc5_kind, *[v._to_cvc5(cvc5_ctx) for v in self.args])
        return t

    def to_sygus2(self):
        return "(" + _OP_SYGUS_SYMBOLS[self.kind] + " " + " ".join([a.to_sygus2() for a in self.args]) + ")"

    def to_verilog_str(self):
        v = self.kind
        def wrap(term):
            if term._has_children:
                return "(" + term.to_verilog_str() + ")"
            else:
                return term.to_verilog_str()
        unops = {
            Kind.Not: "!",
            Kind.BVNot: "~"
        }
        if v in unops:
            a0_str = wrap(self.args[0])
            return f"{unops[v].to_verilog_str()}{a0_str}"
        binops = {
            Kind.BVAdd: "+",
            Kind.BVSub: "-",
            Kind.BVOr: "|",
            Kind.BVAnd: "&",
            Kind.BVXor: "^",
            Kind.Or: "||",
            Kind.And: "&&",
            Kind.Xor: "^", # TODO check if this differs from bv xor
        }
        if v in binops:
            a0_str = wrap(self.args[0])
            a1_str = wrap(self.args[1])
            return f"{a0_str} {unops[v].to_verilog_str()} {a1_str}"
        if v == Kind.Implies:
            a0_str = wrap(self.args[0])
            a1_str = wrap(self.args[1])
            return f"!{a0_str} || {a1_str}"
        if v == Kind.Ite:
            a0_str = wrap(self.args[0])
            a1_str = wrap(self.args[1])
            a2_str = wrap(self.args[2])
            return f"{a0_str} ? {a1_str} : {a2_str}"
        raise NotImplementedError()

    @property
    def _has_children(self):
        return True

    def to_verif_dsl(self):
        o = v.Operators
        unops = {
            Kind.Not: o.Not,
            Kind.BVNot: o.BVNot
        }
        if self.kind in unops:
            return v.UnOpExpr(unops[self.kind], self.args[0].to_verif_dsl())
        binops = {
            Kind.BVAdd: o.BVAdd,
            Kind.BVSub: o.BVSub,
            Kind.BVOr: o.BVOr,
            Kind.BVAnd: o.BVAnd,
            Kind.BVXor: o.BVXor,
            Kind.Or: o.Or,
            Kind.And: o.And,
            Kind.Xor: o.Xor,
            Kind.Equal: o.Equal,
        }
        if self.kind in binops:
            return v.BinOpExpr(binops[self.kind], self.args[0].to_verif_dsl(), self.args[1].to_verif_dsl())
        # if v == kind.Implies:
        #     a0_str = wrap(self.args[0])
        #     a1_str = wrap(self.args[1])
        #     return f"!{a0_str} || {a1_str}"
        if self.kind == Kind.Ite:
            return v.TernaryExpr(self.args[0].to_verif_dsl(), self.args[1].to_verif_dsl(), self.args[2].to_verif_dsl())
        raise NotImplementedError(self.kind)

    def to_uclid(self):
        # TODO use uclid library
        unops = {
            Kind.Not: "!",
            Kind.BVNot: "~"
        }
        if self.kind in unops:
            return unops[self.kind] + self.args[0].to_uclid()
        binops = {
            Kind.BVAdd: "+",
            Kind.BVSub: "-",
            Kind.BVOr: "|",
            Kind.BVAnd: "&",
            Kind.BVXor: "^",
            Kind.Or: "||",
            Kind.And: "&&",
            Kind.Xor: "^", # TODO check if this differs from bv xor
            Kind.Implies: "==>",
        }
        if self.kind in binops:
            return self.args[0].to_uclid() + " " + binops[self.kind] + " " + self.args[1].to_uclid()
        if self.kind == Kind.Ite:
            return "if (" + self.args[0].to_uclid() + ") then " + self.args[1].to_uclid() + " else " + self.args[2].to_uclid()
        raise NotImplementedError(self.kind)

# TODO distinguish between references and declarations
# variables and UFTerms should be referenced in the same way, but obviously declared
# in different manners
@dataclass(frozen=True)
class UFTerm(Term):
    """
    A term representing an uninterpreted function of arbitrary arity.
    """
    name: str
    _sort: Sort
    params: Tuple[Variable, ...]

    @property
    def arity(self):
        return len(self.params)

    @staticmethod
    def from_cvc5(cvc5_term):
        raise NotImplementedError("Cannot convert from CVC5 UF term")

    @property
    def sort(self):
        return self._sort

    def _to_cvc5(self, cvc5_ctx):
        cvc5_ctx.solver.declareFun(
            self.name,
            [p.sort._to_cvc5(cvc5_ctx) for p in self.params],
            self.sort._to_cvc5(cvc5_ctx)
        )

    def to_verilog_str(self):
        raise NotImplementedError()

    def to_sygus2(self):
        raise NotImplementedError()

    def to_verif_dsl(self):
        raise NotImplementedError()

    # @abstractmethod
    def to_uclid(self):
        raise NotImplementedError

    @property
    def _has_children(self):
        return False


@dataclass(frozen=True)
class LambdaTerm(Term):
    params: Tuple[Variable, ...]
    body: Term

    @property
    def sort(self):
        return FunctionSort(tuple([p.sort for p in self.params]), self.body.sort)

    @staticmethod
    def from_cvc5(cvc5_term):
        if cvc5_term.getKind() == pycvc5.Kind.Lambda:
            c_params = cvc5_term[0]
            c_body = cvc5_term[1]
            return LambdaTerm(
                tuple([Variable.from_cvc5(c) for c in c_params]),
                Term.from_cvc5(c_body),
            )
        else:
            raise TypeError("LambdaTerm must be translated from pycvc5.Kind.Lambda, instead got " + str(cvc5_term.getKind()))

    def _to_cvc5(self, cvc5_ctx):
        if self in cvc5_ctx.terms:
            return cvc5_ctx.terms[self]
        else:
            cvc5_kind = pycvc5.Kind.Lambda
            # TODO this needs to be tested
            vlist = cvc5_ctx.solver.mkTerm(pycvc5.Kind.VariableList, [p._to_cvc5() for p in self.params])
            t = cvc5_ctx.solver.mkTerm(cvc5_kind, vlist, [v._to_cvc5(cvc5_ctx) for v in self.body])
            cvc5_ctx.terms[self] = t
            return t

    def to_sygus2(self):
        return "(define-fun (" + \
            " ".join([f"({p.name} {p.sort.to_sygus2()})" for p in self.params]) + ") " + \
            self.body.sort.to_sygus2() + " " + \
            self.body.to_sygus2() \
            + ")"

    def to_verilog_str(self):
        raise NotImplementedError()

    @property
    def _has_children(self):
        return True

    def to_verif_dsl(self):
        raise NotImplementedError()

    def to_uclid(self):
        return self.to_sygus2()
        # return f"(" + \
        #     ", ".join([f"{p.name} : {p.sort.to_uclid()}" for p in self.params]) + ") : " + \
        #     self.body.sort.to_uclid() + " = " + \
        #     self.body.to_uclid()


@dataclass(frozen=True)
class QuantTerm(Term):
    kind: Kind
    bound_vars: Tuple[Variable, ...]
    body: Term

    @property
    def sort(self):
        return BoolSort()

    @staticmethod
    def from_cvc5(cvc5_term):
        k = cvc5_term.getKind()
        if k not in [pycvc5.Kind.Exists, pycvc5.Kind.Forall]:
            c_params = cvc5_term[0]
            c_body = cvc5_term[1]
            return QuantTerm(
                Kind.from_cvc5(k),
                tuple([Variable.from_cvc5(c) for c in c_params]),
                Term.from_cvc5(c_body),
            )
        else:
            raise TypeError("QuantTerm must be translated from pycvc5.Kind.Exists or Forall, instead got " + str(k))

    def _to_cvc5(self, cvc5_ctx):
        if self in cvc5_ctx.terms:
            return cvc5_ctx.terms[self]
        else:
            cvc5_kind = self.kind._to_cvc5()
            # TODO this needs to be tested
            vlist = cvc5_ctx.solver.mkTerm(pycvc5.Kind.VariableList, [p._to_cvc5() for p in self.bound_vars])
            t = cvc5_ctx.solver.mkTerm(cvc5_kind, vlist, [v._to_cvc5(cvc5_ctx) for v in self.body])
            cvc5_ctx.terms[self] = t
            return t

    def to_sygus2(self):
        return "(" + self.kind.to_sygus2() + " (" + \
            " ".join([f"({p.name} {p.sort.to_sygus2()})" for p in self.bound_vars]) + ") " + \
            self.body.sort.to_sygus2() + " " + \
            self.body.to_sygus2() \
            + ")"

    def to_verilog_str(self):
        raise NotImplementedError()

    @property
    def _has_children(self):
        return True

    def to_verif_dsl(self):
        raise NotImplementedError()

    def to_uclid(self):
        return self.to_sygus2()
        # return f"(" + \
        #     ", ".join([f"{p.name} : {p.sort.to_uclid()}" for p in self.params]) + ") : " + \
        #     self.body.sort.to_uclid() + " = " + \
        #     self.body.to_uclid()


@dataclass(frozen=True)
class ApplyUF(Term):
    """
    Term representing application of an uninterpreted function on the specified inputs.
    """
    fun: "SynthFun"
    input_values: Tuple["BVConst", ...]

    @staticmethod
    def from_cvc5(cvc5_term):
        if cvc5_term.getKind() == pycvc5.Kind.ApplyUf:
            raise NotImplementedError()
        else:
            raise TypeError("ApplyUF must be translated from pycvc5.Kind.ApplyUf, instead got " + str(cvc5_term.getKind()))

    def _to_cvc5(self, cvc5_ctx):
        cvc5_kind = pycvc5.Kind.ApplyUf
        t = cvc5_ctx.solver.mkTerm(cvc5_kind, self.fun._to_cvc5(cvc5_ctx), *[v._to_cvc5(cvc5_ctx) for v in self.input_values])
        return t

    def to_sygus2(self):
        raise NotImplementedError()

    def to_verilog_str(self):
        raise NotImplementedError()

    @property
    def _has_children(self):
        return True

    def to_verif_dsl(self):
        raise NotImplementedError()


class BoolConst(Term, Enum, metaclass=_TermMeta):
    F = 0
    T = 1

    @property
    def sort(self):
        return BoolSort()

    def _to_cvc5(self, cvc5_ctx):
        if self == self.F:
            return cvc5_ctx.solver.mkFalse()
        else:
            return cvc5_ctx.solver.mkTrue()

    def to_verilog_str(self):
        return "true" if self == self.T else "false"

    @property
    def _has_children(self):
        return False

    def to_sygus2(self):
        return "true" if self == self.T else "false"

    def to_verif_dsl(self):
        return v.BoolConst(self == self.T)


@dataclass(frozen=True)
class BVConst(Term):
    val: int
    width: int

    @property
    def sort(self):
        return BVSort(self.width)

    @staticmethod
    def from_cvc5(cvc5_term):
        kind = cvc5_term.getKind()
        if kind != pycvc5.Kind.ConstBV:
            raise TypeError("BVConst must be translated from pycvc5.Kind.ConstBV, instead got " + str(kind))
        return BVConst(int(cvc5_term.getBitVectorValue(base=10)), cvc5_term.getSort().getBitVectorSize())

    def _to_cvc5(self, cvc5_ctx):
        if BVSort(self.width) in cvc5_ctx.sorts:
            return cvc5_ctx.sorts[self]
        new_sort = cvc5_ctx.solver.mkBitVector(self.width, self.val)
        return new_sort

    def to_verilog_str(self):
        return "{}'h{:x}".format(self.width, self.val)

    def to_sygus2(self):
        return "#x{:x}".format(self.val)

    @property
    def _has_children(self):
        return False

    def to_verif_dsl(self):
        return v.BVConst(self.val, self.width, v.Base.HEX)


# === END SMT TERMS ===


@dataclass
class Grammar:
    bound_vars: Tuple[Variable, ...]
    input_vars: Tuple[Variable, ...]
    """
    Maps a non-terminal Term to a list of reduction rules, each of which could either be another
    nonterminal or a variable.
    """
    terms: Dict[Term, Tuple[Term, ...]]

    @property
    def _all_terms(self) -> List[Term]:
        all_terms = []
        term_set = set()
        for term, rules in self.terms.items():
            all_terms.append(term)
            term_set.add(term)
            for subterm in rules:
                # TODO probably need some kind of recursion/stack-based approach
                # to handle fnterms that are children of other fnterms
                if subterm not in term_set:
                    term_set.add(subterm)
                    all_terms.append(subterm)
        return all_terms


@dataclass
class SynthFun:
    name: str
    bound_vars: Tuple[Variable, ...]
    return_sort: Sort
    grammar: Grammar

    def new_solver(self) -> "Solver":
        """
        Creates a new Solver instance to synthesize this function.
        """
        # sorts, variables get automatically read
        return Solver(terms=self.grammar._all_terms, synthfuns=[self])

    def _to_cvc5(self, cvc5_ctx) -> Term:
        return cvc5_ctx.synthfuns[self.name]


@dataclass
class SygusConstraint:
    term: Term


@dataclass
class Cvc5Ctx:
    solver: pycvc5.Solver
    sorts: Dict[Sort, pycvc5.Sort]
    terms: Dict[Term, pycvc5.Term]
    grammars: List[pycvc5.Grammar]
    synthfuns: Dict[str, pycvc5.Term]
    constraints: List[pycvc5.Term]

    def __post_init__(self):
        sv = self.solver
        sv.setOption("lang", "sygus2")
        sv.setOption("incremental", "false")
        sv.setLogic("BV")

    def try_add_sort(self, sort: Sort):
        if sort not in self.sorts:
            self.sorts[sort] = sort._to_cvc5(self)

    def add_term(self, term):
        # TODO handle nonterminals being used as arguments?
        k = term
        if isinstance(term, Variable):
            v = term._to_cvc5(self)
        elif isinstance(term, OpTerm):
            v = term._to_cvc5(self)
        elif isinstance(term, BoolConst):
            v = term._to_cvc5(self)
        else:
            raise Exception(f"invalid term: {term}")
        self.terms[k] = v

    def _add_grammar(self, grammar):
        g = self.solver.mkSygusGrammar(
            [v._to_cvc5(self) for v in grammar.bound_vars],
            # TODO merge nt map with variables
            [t._to_cvc5(self) for t in grammar.terms.keys()]
        )
        for t, rules in grammar.terms.items():
            g.addRules(t._to_cvc5(self), [ s._to_cvc5(self) for s in rules ])
        for v in grammar.input_vars:
            g.addAnyVariable(v._to_cvc5(self))
        self.grammars.append(g)
        return g

    def add_synthfun(self, sf):
        g = self._add_grammar(sf.grammar)
        self.synthfuns[sf.name] = self.solver.synthFun(
            sf.name,
            [v._to_cvc5(self) for v in sf.bound_vars],
            sf.return_sort._to_cvc5(self),
            g
        )

    def add_sygus_constraint(self, constraint):
        constraint_term = constraint.term._to_cvc5(self)
        self.solver.addSygusConstraint(constraint_term)
        self.constraints.append(constraint_term)


class Solver:
    sorts: Set[Sort]
    terms: List[Term]
    synthfuns: List[SynthFun]
    constraints: List[SygusConstraint]
    _cvc5_wrapper: Optional[Cvc5Ctx]

    def __init__(self, sorts=None, terms=None, synthfuns=None, constraints=None, backend="cvc5"):
        # can't make these default args, since the same instance of a default arg is shared
        # across every call to __init__
        sorts = set(sorts or set())
        terms = list(terms or [])
        synthfuns = list(synthfuns or [])
        constraints = list(constraints or [])
        self.sorts = sorts
        # This needs to be initialized one term at a time in order for the CVC5 wrapper
        # to be able to process each term 
        # The CVC5 wrapper also needs a reference to this list
        self.terms = terms
        self.synthfuns = synthfuns
        self.constraints = constraints
        if backend == "cvc5":
            self.reinit_cvc5()
        else:
            self._cvc5_wrapper = None

    def reinit_cvc5(self):
        wrapper = Cvc5Ctx(
            solver=pycvc5.Solver(),
            sorts={},
            terms={},
            grammars=[],
            synthfuns={},
            constraints=[],
        )
        # TODO Don't know why this is necessary, but it is?
        wrapper.solver.mkBitVector(8, 0)
        for sort in self.sorts:
            wrapper.try_add_sort(sort)
        for term in self.terms:
            wrapper.add_term(term)
        for sf in self.synthfuns:
            wrapper.add_synthfun(sf)
        for constraint in self.constraints:
            wrapper.add_sygus_constraint(constraint)
        self._cvc5_wrapper = wrapper

    def add_sort(self, sort: Sort) -> Sort:
        self.sorts.add(sort)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.try_add_sort(sort)
        return sort

    def add_variable(self, name: str, sort: Sort) -> Variable:
        # warn if overwriting a variable?
        newvar = Variable(name, sort)
        self.add_term(newvar)
        return newvar

    def add_term(self, term: Term) -> Term:
        self.terms.append(term)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_term(term)
        return term

    # TODO restrict this to be a term that's a predicate
    def add_sygus_constraint(self, term: Term) -> SygusConstraint:
        newconstraint = SygusConstraint(term)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_sygus_constraint(newconstraint)
        return newconstraint

    def add_synthfun(self, fn: SynthFun) -> SynthFun:
        self.synthfuns.append(fn)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_synthfun(fn)
        return fn

    def check_synth(self):
        if self._cvc5_wrapper:
            # TODO choose specific synth functions
            c_slv = self.get_cvc5_solver()
            t = list(self._cvc5_wrapper.synthfuns.values())[0]
            s = c_slv.checkSynth()
            if not s.isUnsat():
                return SynthResult(False, None)
            else:
                return SynthResult(
                    True,
                    LambdaTerm.from_cvc5(c_slv.getSynthSolution(t)),
                )
        raise NotImplementedError()

    def get_cvc5_solver(self):
        # no consistency guarantees lol
        return self._cvc5_wrapper.solver


@dataclass
class SynthResult:
    is_unsat: bool
    solution: Optional[LambdaTerm]
