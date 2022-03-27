
from abc import ABC, ABCMeta, abstractmethod
from enum import Enum, EnumMeta, auto

import pycvc5

import easyila.verification as v
from .sorts import *

class Kind(Enum):
    # https://cvc5.github.io/docs/api/cpp/kind.html
    BVAdd       = auto()
    BVSub       = auto()
    BVOr        = auto()
    BVAnd       = auto()
    BVNot       = auto()
    BVXor       = auto()
    BVExtract   = auto()
    Or          = auto()
    And         = auto()
    Not         = auto()
    Xor         = auto()
    Implies     = auto()
    Ite         = auto()
    Lambda      = auto()
    Equal       = auto()
    Exists      = auto()
    ForAll      = auto()
    Select      = auto()
    Store       = auto()

    def to_cvc5(self, _cvc5_ctx):
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

    def to_sygus2(self):
        raise NotImplementedError()


# Maps our Kind class to pycvc5.Kind...
_OP_KIND_MAPPING = {
    Kind.BVAdd:     pycvc5.Kind.BVAdd,
    Kind.BVSub:     pycvc5.Kind.BVSub,
    Kind.BVOr:      pycvc5.Kind.BVOr,
    Kind.BVAnd:     pycvc5.Kind.BVAnd,
    Kind.BVNot:     pycvc5.Kind.BVNot,
    Kind.BVXor:     pycvc5.Kind.BVXor,
    Kind.BVExtract: pycvc5.Kind.BVExtract,

    Kind.Equal:     pycvc5.Kind.Equal,
    Kind.Or:        pycvc5.Kind.Or,
    Kind.And:       pycvc5.Kind.And,
    Kind.Not:       pycvc5.Kind.Not,
    Kind.Xor:       pycvc5.Kind.Xor,
    Kind.Implies:   pycvc5.Kind.Implies,
    Kind.Ite:       pycvc5.Kind.Ite,

    Kind.Lambda:    pycvc5.Kind.Lambda,
    Kind.Exists:    pycvc5.Kind.Exists,
    Kind.ForAll:    pycvc5.Kind.Forall,

    Kind.Select:    pycvc5.Kind.Select,
    Kind.Store:     pycvc5.Kind.Store
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
    # extract is a special case
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

class Term(Translatable, ABC):
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
            cond = OpTerm(Kind.Equal, (self, BVConst(1, self.sort.bitwidth)))
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
        raise NotImplementedError()

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

    def __getitem__(self, key):
        if isinstance(self.sort, ArraySort):
            # Array indexing
            if isinstance(key, type(self.sort.idx_sort)):
                return OpTerm(Kind.Select, (self, key))
            elif isinstance(key, int):
                # Convert key to appropriate index sort
                i_key = type(self.sort.idx_sort)(key)
                return OpTerm(Kind.Select, (self, i_key))
            else:
                raise TypeError(key)
        # Bitvector indexing
        if isinstance(self.sort, BoolSort):
            width = 1
        else:
            assert isinstance(self.sort, BVSort), "only BV terms support indexing, instead term was " + str(self)
            width = self.sort.bitwidth
        wrap = lambda i: BVConst(i, width)
        if isinstance(key, int):
            return OpTerm(Kind.BVExtract, (wrap(key), wrap(key), self))
        elif isinstance(key, slice):
            hi = wrap(max(key.start, key.stop))
            lo = wrap(min(key.start, key.stop))
            return OpTerm(Kind.BVExtract, (hi, lo, self))
        raise TypeError(key)

    def __setitem__(self, key, value):
        if isinstance(self.sort, ArraySort):
            if isinstance(key, type(self.sort.idx_sort)):
                pass
            elif isinstance(key, int):
                # Convert key to appropriate index sort
                key = type(self.sort.idx_sort)(key)
            else:
                raise TypeError(key)
            if isinstance(value, type(self.sort.elem_sort)):
                pass
            elif isinstance(key, int):
                value = type(self.sort.elem_sort)(key)
            else:
                raise TypeError(key)
            return OpTerm(Kind.Store, (self, key, value))
        raise TypeError(key)

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
    This class represents variable references. To obtain a `Translatable` for a variable
    declaration, use the `get_decl()` method.
    """

    name: str
    _sort: Sort

    def to_uf(self):
        """Converts this variable to a 0-arity UFTerm."""
        return UFTerm(self.name, self.sort, ())

    def get_decl(self):
        """Gets a Translatable declaration of this variable."""
        return VarDecl(self.name, self.sort)

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

    @property
    def _has_children(self):
        return False

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if self in cvc5_ctx.terms:
                return cvc5_ctx.terms[self]
            else:
                v = cvc5_ctx.solver.mkVar(self.sort.to_cvc5(cvc5_ctx), self.name)
                cvc5_ctx.terms[self] = v
                return v
        elif tgt in (TargetFormat.SYGUS2, TargetFormat.VERILOG, TargetFormat.UCLID):
            return self.name
        elif tgt == TargetFormat.VERIF_DSL:
            # TODO handle booleans
            assert isinstance(self.sort, BVSort)
            return v.WireOrRegRef(self.name, self.sort.bitwidth)
        raise NotImplementedError("cannot convert Variable to " + str(tgt))


BoolVariable = lambda s: Variable(s, BoolSort())
BVVariable = lambda s, w: Variable(s, BVSort(w))


@dataclass(frozen=True)
class VarDecl(Translatable):
    name: str
    sort: Sort

    def get_ref(self):
        return Variable(self.name, self.sort)

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            # The CVC5 interface doesn't really distnguish between declarations
            # and references of bound variables
            return self.get_ref().to_cvc5(cvc5_ctx=kwargs["cvc5_ctx"])
        elif tgt == TargetFormat.SYGUS2:
            raise NotImplementedError()
        elif tgt == TargetFormat.VERILOG:
            raise NotImplementedError()
        elif tgt == TargetFormat.UCLID:
            # TODO need to identify inputs/outputs
            return f"var {self.name} : {self.sort.to_uclid()};"
        raise NotImplementedError("cannot convert VarDecl to " + str(tgt))


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
        elif self.kind == Kind.BVExtract:
            # TODO fix this hack: in the CVC5 API, BVExtract must first be turned into
            # an operator via Solver::mkOp(BVExtract, high, low)
            # As a workaround, we store the high/low parameters as BVConst arguments
            assert isinstance(self.args[0], BVConst)
            assert isinstance(self.args[1], BVConst)
            return BVSort(self.args[0].val - self.args[1].val + 1)
        elif self.kind == Kind.Ite:
            return self.args[1].sort
        bitops = { Kind.Or, Kind.And, Kind.Xor, Kind.Not, Kind.Equal }
        if self.kind in bitops:
            return BoolSort()
        raise NotImplementedError(f"Cannot get Sort for kind {self.kind}")

    @property
    def _has_children(self):
        return True

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

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            cvc5_kind = self.kind.to_cvc5(self)
            if self.kind == Kind.BVExtract:
                # TODO special case BVExtract, Select, and Store for from_cvc5?
                assert isinstance(self.args[0], BVConst)
                assert isinstance(self.args[1], BVConst)
                op = cvc5_ctx.solver.mkOp(cvc5_kind, self.args[0].val, self.args[1].val)
                return cvc5_ctx.solver.mkTerm(op, self.args[2].to_cvc5(cvc5_ctx))
            t = cvc5_ctx.solver.mkTerm(cvc5_kind, *[v.to_cvc5(cvc5_ctx) for v in self.args])
            return t
        elif tgt == TargetFormat.SYGUS2:
            return "(" + _OP_SYGUS_SYMBOLS[self.kind] + " " + " ".join([a.to_sygus2() for a in self.args]) + ")"
        elif tgt == TargetFormat.VERILOG:
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
                return f"{unops[v]}{a0_str}"
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
                return f"{a0_str} {unops[v]} {a1_str}"
            if v == Kind.Implies:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                return f"!{a0_str} || {a1_str}"
            if v == Kind.Ite:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                a2_str = wrap(self.args[2])
                return f"{a0_str} ? {a1_str} : {a2_str}"
            raise NotImplementedError(v)
        elif tgt == TargetFormat.VERIF_DSL:
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
        elif tgt == TargetFormat.UCLID:
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
        raise NotImplementedError("cannot convert OpTerm to " + str(tgt))


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

    @property
    def _has_children(self):
        return False

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            return cvc5_ctx.solver.declareFun(
                self.name,
                [p.sort.to_cvc5(cvc5_ctx) for p in self.params],
                self.sort.to_cvc5(cvc5_ctx)
            )
        elif tgt == TargetFormat.UCLID:
            params_s = ",".join(f"{v.name} : {v.sort.to_uclid()}" for v in self.params)
            return f"synthesis function {self.name}({params_s}) : {self.sort.to_uclid()};"
        raise NotImplementedError("cannot convert UFTerm to " + str(tgt))


@dataclass(frozen=True)
class LambdaTerm(Term):
    params: Tuple[Variable, ...]
    body: Term

    @property
    def sort(self):
        return FunctionSort(tuple([p.sort for p in self.params]), self.body.sort)

    @property
    def _has_children(self):
        return True

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

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if self in cvc5_ctx.terms:
                return cvc5_ctx.terms[self]
            else:
                cvc5_kind = pycvc5.Kind.Lambda
                # TODO this needs to be tested
                vlist = cvc5_ctx.solver.mkTerm(pycvc5.Kind.VariableList, [p.to_cvc5(cvc5_ctx) for p in self.params])
                t = cvc5_ctx.solver.mkTerm(cvc5_kind, vlist, [self.body.to_cvc5(cvc5_ctx)])
                cvc5_ctx.terms[self] = t
                return t
        elif tgt in (TargetFormat.SYGUS2, TargetFormat.UCLID):
            return "(define-fun (" + \
                " ".join([f"({p.name} {p.sort.to_sygus2()})" for p in self.params]) + ") " + \
                self.body.sort.to_sygus2() + " " + \
                self.body.to_sygus2() \
                + ")"
        # return f"(" + \
        #     ", ".join([f"{p.name} : {p.sort.to_uclid()}" for p in self.params]) + ") : " + \
        #     self.body.sort.to_uclid() + " = " + \
        #     self.body.to_uclid()
        raise NotImplementedError("cannot convert LambdaTerm to " + str(tgt))

@dataclass(frozen=True)
class QuantTerm(Term):
    kind: Kind
    bound_vars: Tuple[Variable, ...]
    body: Term

    @property
    def sort(self):
        return BoolSort()

    @property
    def _has_children(self):
        return True

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

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if self in cvc5_ctx.terms:
                return cvc5_ctx.terms[self]
            else:
                cvc5_kind = self.kind.to_cvc5(cvc5_ctx)
                # TODO this needs to be tested
                vlist = cvc5_ctx.solver.mkTerm(pycvc5.Kind.VariableList, [p.to_cvc5(cvc5_ctx) for p in self.bound_vars])
                t = cvc5_ctx.solver.mkTerm(cvc5_kind, vlist, [self.body.to_cvc5(cvc5_ctx)])
                cvc5_ctx.terms[self] = t
                return t
        elif tgt in (TargetFormat.SYGUS2, TargetFormat.UCLID):
            return "(" + self.kind.to_sygus2() + " (" + \
                " ".join([f"({p.name} {p.sort.to_sygus2()})" for p in self.bound_vars]) + ") " + \
                self.body.sort.to_sygus2() + " " + \
                self.body.to_sygus2() \
                + ")"
        raise NotImplementedError("cannot convert FunctionSort to " + str(tgt))


@dataclass(frozen=True)
class ApplyUF(Term):
    """
    Term representing application of an uninterpreted function on the specified inputs.
    """
    fun: "SynthFun"
    input_values: Tuple["BVConst", ...]

    @property
    def sort(self):
        raise NotImplementedError()

    @property
    def _has_children(self):
        return True

    @staticmethod
    def from_cvc5(cvc5_term):
        if cvc5_term.getKind() == pycvc5.Kind.ApplyUf:
            raise NotImplementedError()
        else:
            raise TypeError("ApplyUF must be translated from pycvc5.Kind.ApplyUf, instead got " + str(cvc5_term.getKind()))

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            cvc5_kind = pycvc5.Kind.ApplyUf
            t = cvc5_ctx.solver.mkTerm(cvc5_kind, self.fun.to_cvc5(cvc5_ctx), *[v.to_cvc5(cvc5_ctx) for v in self.input_values])
            return t
        raise NotImplementedError("cannot convert FunctionSort to " + str(tgt))


class BoolConst(Term, Enum, metaclass=_TermMeta):
    F = 0
    T = 1

    @property
    def sort(self):
        return BoolSort()

    @property
    def _has_children(self):
        return False

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if self == self.F:
                return cvc5_ctx.solver.mkFalse()
            else:
                return cvc5_ctx.solver.mkTrue()
        elif tgt in (TargetFormat.VERILOG, TargetFormat.SYGUS2, TargetFormat.UCLID):
            return "true" if self == self.T else "false"
        elif tgt == TargetFormat.VERIF_DSL:
            return v.BoolConst(self == self.T)
        raise NotImplementedError("cannot convert BoolConst to " + str(tgt))


@dataclass(frozen=True)
class BVConst(Term):
    val: int
    width: int

    @property
    def sort(self):
        return BVSort(self.width)

    @property
    def _has_children(self):
        return False

    @staticmethod
    def from_cvc5(cvc5_term):
        kind = cvc5_term.getKind()
        if kind != pycvc5.Kind.ConstBV:
            raise TypeError("BVConst must be translated from pycvc5.Kind.ConstBV, instead got " + str(kind))
        return BVConst(int(cvc5_term.getBitVectorValue(base=10)), cvc5_term.getSort().getBitVectorSize())

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if BVSort(self.width) in cvc5_ctx.sorts:
                return cvc5_ctx.sorts[self]
            new_sort = cvc5_ctx.solver.mkBitVector(self.width, self.val)
            return new_sort
        elif tgt == TargetFormat.SYGUS2:
            return "#x{:x}".format(self.val)
        elif tgt == TargetFormat.VERILOG:
            return "{}'h{:x}".format(self.width, self.val)
        elif tgt == TargetFormat.VERIF_DSL:
            return v.BVConst(self.val, self.width, v.Base.HEX)
        elif tgt == TargetFormat.UCLID:
            return "0x{:x}bv{}".format(self.val, self.width)
        raise NotImplementedError("cannot convert BVConst to " + str(tgt))


# === END SMT TERMS ===
