
from abc import ABC, ABCMeta, abstractmethod
from dataclasses import asdict, dataclass
from enum import Enum, EnumMeta, IntEnum, auto
import json
from typing import Callable, Dict, Optional, TypeVar, Union

import pycvc5

from .sorts import *

class Kind(Enum):
    BVAdd           = auto()
    BVSub           = auto()
    BVMul           = auto()
    BVOr            = auto()
    BVAnd           = auto()
    BVNot           = auto()
    BVXor           = auto()
    BVExtract       = auto()
    BVConcat        = auto()
    BVOrr           = auto() # OR reduction
    BVXorr          = auto() # XOR reduction
    BVUle           = auto() # Unsigned less than/equal
    BVUlt           = auto() # Unsigned less than
    BVUge           = auto() # Unsigned greater than/equal
    BVUgt           = auto() # unsigned greater than
    BVZeroPad       = auto()
    BVSignExtend    = auto()
    BVSll           = auto() # Shift left (logical)
    BVSrl           = auto() # Shift right (logical)
    BVSra           = auto() # Shift right (arithmetic)
    Or              = auto()
    And             = auto()
    Not             = auto()
    Xor             = auto()
    Implies         = auto()
    Ite             = auto()
    Match           = auto()
    Lambda          = auto()
    Equal           = auto()
    Distinct        = auto()
    Exists          = auto()
    ForAll          = auto()
    Select          = auto()
    Store           = auto()

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


# https://cvc5.github.io/docs/api/cpp/kind.html
# Maps our Kind class to pycvc5.Kind...
_OP_KIND_MAPPING = {
    Kind.BVAdd:         pycvc5.Kind.BVAdd,
    Kind.BVSub:         pycvc5.Kind.BVSub,
    Kind.BVMul:         pycvc5.Kind.BVMult,

    Kind.BVOr:          pycvc5.Kind.BVOr,
    Kind.BVAnd:         pycvc5.Kind.BVAnd,
    Kind.BVNot:         pycvc5.Kind.BVNot,
    Kind.BVXor:         pycvc5.Kind.BVXor,
    Kind.BVSll:         pycvc5.Kind.BVShl,
    Kind.BVSrl:         pycvc5.Kind.BVLshr,
    Kind.BVSra:         pycvc5.Kind.BVAshr,

    Kind.BVExtract:     pycvc5.Kind.BVExtract,
    Kind.BVConcat:      pycvc5.Kind.BVConcat,

    Kind.BVOrr:         pycvc5.Kind.BVRedor,

    Kind.BVUle:         pycvc5.Kind.BVUle,
    Kind.BVUlt:         pycvc5.Kind.BVUlt,
    Kind.BVUge:         pycvc5.Kind.BVUge,
    Kind.BVUgt:         pycvc5.Kind.BVUgt,

    Kind.BVZeroPad:     pycvc5.Kind.BVZeroExtend,
    Kind.BVSignExtend:  pycvc5.Kind.BVSignExtend,

    Kind.Equal:         pycvc5.Kind.Equal,
    Kind.Distinct:      pycvc5.Kind.Distinct,
    Kind.Or:            pycvc5.Kind.Or,
    Kind.And:           pycvc5.Kind.And,
    Kind.Not:           pycvc5.Kind.Not,
    Kind.Xor:           pycvc5.Kind.Xor,
    Kind.Implies:       pycvc5.Kind.Implies,
    Kind.Ite:           pycvc5.Kind.Ite,
    Kind.Match:         pycvc5.Kind.Match,

    Kind.Lambda:        pycvc5.Kind.Lambda,
    Kind.Exists:        pycvc5.Kind.Exists,
    Kind.ForAll:        pycvc5.Kind.Forall,

    Kind.Select:        pycvc5.Kind.Select,
    Kind.Store:         pycvc5.Kind.Store
}
# ...and vice versa
_OP_KIND_REV_MAPPING = {v: k for k, v in _OP_KIND_MAPPING.items()}

_OP_SYGUS_SYMBOLS = {
    Kind.BVAdd: "bvadd",
    Kind.BVSub: "bvsub",
    Kind.BVMul: "bvmult",
    Kind.BVOr: "bvor",
    Kind.BVAnd: "bvand",
    Kind.BVNot: "bvnot",
    Kind.BVXor: "bvxor",
    Kind.BVSll: "bvshl",
    Kind.BVSrl: "bvashr",
    Kind.BVSra: "bvlshr",
    # extract is a special case
    Kind.Or: "or",
    Kind.And: "and",
    Kind.Not: "not",
    Kind.Xor: "xor",
    Kind.Equal: "=",
    Kind.Ite: "ite",
    Kind.Implies: "=>",
    Kind.Exists: "exists",
    Kind.ForAll: "forall",
}


# === BEGIN SMT TERMS ===

_T = TypeVar("_T")

class Term(Translatable, ABC):
    def _binop_type_check(self, other, sext=False, zpad=True, cast_int=True) -> Tuple["Term", "Term"]:
        """
        Checks that two operands have the same sort.

        If sext or zpad are set, if both are bitvectors and one is shorter than the other,
        then the one with the smaller width is zero-padded/sign-extended to the appropriate width.
        If sext/zpad are set and one arg is a boolean but the other is a bitvector, the boolean will
        be upcasted with an ITE statement.

        When `cast_int` is set, if `other` is an int, it will automatically be wrapped in
        a constant of the appropriate sort.
        """
        assert not (zpad and sext), "zpad and sext cannot both be set"
        if cast_int and isinstance(other, int):
            if isinstance(other, BoolConst):
                other = other.value
            if isinstance(self.sort, BoolSort):
                assert other in (0, 1), f"cannot coerce int {other} to {self.sort}"
                return self, (BoolConst.T if other else BoolConst.F)
            elif isinstance(self.sort, BVSort):
                bitwidth = self.sort.bitwidth
                assert other < (2 ** bitwidth), f"int constant {other} exceeds max value of bv{bitwidth}"
                return self, BVConst(other, bitwidth)
        assert isinstance(other, Term), f"cannot combine {self} with {other}"
        assert hasattr(self, "sort"), repr(self)
        assert hasattr(other, "sort"), repr(other)
        s_bw = self.sort.bitwidth
        o_bw = other.sort.bitwidth
        if s_bw == o_bw:
            return self, other
        if sext:
            if s_bw > o_bw:
                if isinstance(other.sort, BoolSort):
                    return self, other.ite(BVConst((1 << o_bw) - 1, o_bw), BVConst(0, o_bw))
                return self, other.sign_extend(BVConst(s_bw - o_bw, o_bw))
            else:
                if isinstance(self.sort, BoolSort):
                    return self.ite(BVConst((1 << o_bw) - 1, o_bw), BVConst(0, o_bw)), other
                return self.sign_extend(BVConst(o_bw - s_bw, s_bw)), other
        if zpad:
            if s_bw > o_bw:
                if isinstance(other.sort, BoolSort):
                    return self, other.ite(BVConst(1, o_bw), BVConst(0, o_bw))
                return self, other.zero_pad(BVConst(s_bw - o_bw, o_bw))
            else:
                if isinstance(self.sort, BoolSort):
                    return self.ite(BVConst(1, o_bw), BVConst(0, o_bw)), other
                return self.zero_pad(BVConst(o_bw - s_bw, s_bw)), other
        assert self.sort == other.sort, f"cannot combine value {self} of sort {self.sort} to {other} of sort {other.sort}"
        return self, other

    # === OPTIMIZATIONS AND TREE TRAVERSALS ===

    def replace_vars(self, var, new_term) -> "Term":
        """
        Returns a new term tree with all references to `var` replaced by `new_term`.
        """
        if self == var:
            return new_term
        t = self
        for i, child in enumerate(self._children):
            t = t._replace_child(child.replace_vars(var, new_term), i)
        return t

    def preorder_visit_tree(self, visit_fn: Callable[["Term"], _T], shortcircuit=True) -> _T:
        """
        Calls `visit_fn` on this node, then recursively on all children.
        Returns whatever `visit_fn(self)` returns.

        If `shortcircuit` is True, then this function will return without visiting
        its children if  `visit_fn(self)` returns a falsey value.
        """
        rv = visit_fn(self)
        if not shortcircuit or bool(rv):
            for s in self._children:
                assert isinstance(s, Term), s
                self.preorder_visit_tree(visit_fn, shortcircuit)
        return rv

    def optimize(self) -> "Term":
        if isinstance(self, OpTerm):
            # This method must also traverse children!
            return self.optimize()
        t = self
        for i, child in enumerate(self._children):
            t = t._replace_child(child.optimize(), i)
        return t

    def typecheck(self) -> bool:
        """
        Performs rudimentary type checking (no scope/semantic checking).
        Returns True on success, False on failure. Short circuits.

        TODO for now, this just ensures everything in the tree is a term
        TODO error reporting
        """
        for s in self._children:
            if not isinstance(s, Term):
                print(f"type error: child term {s} is not a Term object")
                return False
            if not s.typecheck():
                return False
        return True

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
        t_term, f_term = t_term._binop_type_check(f_term)
        return OpTerm(Kind.Ite, (cond, t_term, f_term))

    def match_const(
        self,
        cases: Dict[Union[int, "BVConst"], "Term"],
        # default: Optional["Term"]=None TODO implement default
    ):
        """
        A more primitive form of an SMT match expression. SMTLIB match expressions
        perform destructuring akin to functional programming pattern matching, but
        we only support matching against constants.

        When this term takes on a certain value, the expression should evaluate to
        the corresponding value in `cases`. All keys in `cases` must be of the same
        sort as this term, or are casted if they are int.

        This match must be exhaustive, so if cases do not provide all possible values
        of this sort, then `default` must be specified. An Exception is raised if the match
        is not exhaustive.
        """
        assert isinstance(self.sort, BVSort)
        sort_max = (1 << self.sort.bitwidth) - 1
        covered = 0 # Bit set representing which cases have been covered
        args = [self] # OpTerm sees this as pairs of (case, term) occurring consecutively
        for c, term in cases.items():
            if isinstance(c, int):
                c = BVConst(c, self.sort.bitwidth)
            assert c.val <= sort_max
            if (covered & (1 << c.val)) != 0:
                # Check if the case was already set
                raise Exception(f"Match case {c.val} occurred multiple times")
            covered |= 1 << c.val
            args.append(c)
            args.append(term)
        all_covered = (1 << sort_max) - 1 # 1 bit for each possible value
        default = None
        if not default:
            assert covered != all_covered, "Match default was provided, but cases were already exhaustive"
        else:
            assert covered == all_covered, "Match was non-exhaustive"
        return OpTerm(Kind.Match, tuple(args))

    def implies(self, other):
        return OpTerm(Kind.Implies, self._binop_type_check(other))

    def __lt__(self, other):
        return OpTerm(Kind.BVUlt, self._binop_type_check(other))

    def __le__(self, other):
        return OpTerm(Kind.BVUle, self._binop_type_check(other))

    def op_eq(self, other):
        """
        We can't override __eq__ without breaking a decent amount of stuff, so
        op_eq is syntactic sugar for an equality expression instead.
        """
        return OpTerm(Kind.Equal, self._binop_type_check(other))

    def op_ne(self, other):
        return OpTerm(Kind.Distinct, self._binop_type_check(other))

    def __gt__(self, other):
        return OpTerm(Kind.BVUgt, self._binop_type_check(other))

    def __ge__(self, other):
        return OpTerm(Kind.BVUge, self._binop_type_check(other))

    def __add__(self, other):
        return OpTerm(Kind.BVAdd, self._binop_type_check(other))

    def __and__(self, other):
        if isinstance(other.sort, BoolSort):
            op = Kind.And
        else:
            op = Kind.BVAnd
        return OpTerm(op, self._binop_type_check(other))

    def __invert__(self):
        if isinstance(self.sort, BoolSort):
            op = Kind.Not
        else:
            op = Kind.BVNot
        return OpTerm(op, (self,))

    def __mul__(self, other):
        return OpTerm(Kind.BVMul, self._binop_type_check(other))

    def __neg__(self):
        raise NotImplementedError()

    def __or__(self, other):
        if isinstance(other.sort, BoolSort):
            op = Kind.Or
        else:
            op = Kind.BVOr
        return OpTerm(op, self._binop_type_check(other))

    def __lshift__(self, other):
        return self.sll(other)

    def sll(self, other):
        # TODO typecheck all shifts
        return OpTerm(Kind.BVSll, self._binop_type_check(other))

    def __rshift__(self, other):
        # Python right shift is technically arithmetic since integers
        # don't have a fixed size
        return self.sra(other)

    def srl(self, other):
        return OpTerm(Kind.BVSrl, self._binop_type_check(other))

    def sra(self, other):
        return OpTerm(Kind.BVSra, self._binop_type_check(other))

    def __sub__(self, other):
        return OpTerm(Kind.BVSub, self._binop_type_check(other))

    def __xor__(self, other):
        if isinstance(other.sort, BoolSort):
            op = Kind.Xor
        else:
            op = Kind.BVXor
        return OpTerm(op, self._binop_type_check(other))

    def __getitem__(self, key):
        if isinstance(self.sort, ArraySort):
            # Array indexing
            if isinstance(key, Term):
                if not key.sort == self.sort.idx_sort:
                    raise TypeError(f"cannot index {self} (sort {self.sort}) with {key} (sort {key.sort})")
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
            return OpTerm(Kind.BVExtract, (self, wrap(key), wrap(key)))
        elif isinstance(key, Term):
            return OpTerm(Kind.BVExtract, (self, key, key))
        elif isinstance(key, slice):
            if isinstance(key.start, int):
                hi = wrap(max(key.start, key.stop))
            else:
                hi = key.start
            if isinstance(key.stop, int):
                lo = wrap(min(key.start, key.stop))
            else:
                lo = key.stop
            return OpTerm(Kind.BVExtract, (self, hi, lo))
        raise TypeError(f"cannot index {self} with {key}")

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

    def concat(self, *others):
        return OpTerm(Kind.BVConcat, (self, *others))

    def zero_pad(self, extra_bits: "BVConst"):
        """Zero pads this term with an addition `extra_bits` bits."""
        return OpTerm(Kind.BVZeroPad, (self, extra_bits))

    def sign_extend(self, extra_bits: "BVConst"):
        """Sign extends this term with an addition `extra_bits` bits."""
        return OpTerm(Kind.BVSignExtend, (self, extra_bits))

    def orr(self):
        return OpTerm(Kind.BVOrr, (self,))

    def xorr(self):
        return OpTerm(Kind.BVXorr, (self,))

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
    def _has_children(self):
        return len(self._children) > 0

    @property
    @abstractmethod
    def _children(self):
        raise NotImplementedError()

    @abstractmethod
    def _replace_child(self, new_term, index) -> "Term":
        """
        Returns a new term with the `index`th child replaced by new_term
        """
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

    def __post_init__(self):
        assert isinstance(self.name, str) and len(self.name) > 0
        assert isinstance(self._sort, Sort), f"{self._sort} is not a Sort instance"

    def __str__(self):
        return f"{self.name}"

    def to_uf(self):
        """Converts this variable to a 0-arity UFTerm."""
        return UFTerm(self.name, self.sort, ())

    def get_decl(self, init_value=None):
        """Gets a Translatable declaration of this variable."""
        return VarDecl(self.name, self.sort, init_value=init_value)

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
    def _children(self):
        return []

    def _replace_child(self, new_term, index):
        return self

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
        elif tgt == TargetFormat.JSON:
            return json.dumps(asdict(self))
        raise NotImplementedError("cannot convert Variable to " + str(tgt))


BoolVariable = lambda s, **kwargs: Variable(s, BoolSort(), **kwargs)
BVVariable = lambda s, w, **kwargs: Variable(s, BVSort(w), **kwargs)


@dataclass(frozen=True)
class VarDecl(Translatable):
    name: str
    sort: Sort
    init_value: "BVConst" = None

    def __str__(self):
        if self.init_value is not None:
            return f"{self.name} : {self.sort}"
        else:
            return f"{self.name} : {self.sort} = {self.init_value}"

    def get_ref(self):
        return Variable(self.name, self.sort)

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        """
        Possible kwargs:
        - cvc5_ctx: a Cvc5Ctx object used to get a reference to a cvc5 solver
        - is_reg: a boolean used by verilog conversion to determine if this should be declared
                  as a reg (if false or not specified, the variable will be a wire)
        - anyconst: a boolean used by verilog conversion; when specified, it will add the
                  (* anyconst *) yosys attribute
        """
        if tgt == TargetFormat.CVC5:
            # The CVC5 interface doesn't really distnguish between declarations
            # and references of bound variables
            return self.get_ref().to_cvc5(cvc5_ctx=kwargs["cvc5_ctx"])
        elif tgt == TargetFormat.SYGUS2:
            raise NotImplementedError()
        elif tgt == TargetFormat.VERILOG:
            if isinstance(self.sort, ArraySort):
                raise NotImplementedError("VarDecl verilog array translation not supported yet")
            is_reg = kwargs.get("is_reg", False)
            decl = "reg" if is_reg else "wire"
            if self.sort.bitwidth != 1:
                decl += " " + self.sort.to_verilog_str()
            decl += f" {self.name}"
            if self.init_value is not None:
                decl += " = " + self.init_value.to_verilog_str()
            decl += ";"
            anyconst = kwargs.get("anyconst", False)
            if anyconst:
                return  "(* anyconst *) " + decl
            else:
                return decl
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
            assert isinstance(self.args[1], BVConst)
            assert isinstance(self.args[2], BVConst)
            return BVSort(self.args[1].val - self.args[2].val + 1)
        elif self.kind in (Kind.BVZeroPad, Kind.BVSignExtend):
            assert isinstance(self.args[0].sort, BVSort), repr(self.args[0])
            assert isinstance(self.args[1], BVConst), repr(self.args[1])
            return BVSort(self.args[0].sort.bitwidth + self.args[1].val)
        elif self.kind == Kind.BVConcat:
            return BVSort(sum(a.sort.bitwidth for a in self.args))
        elif self.kind == Kind.Ite:
            return self.args[1].sort
        elif self.kind == Kind.Match:
            return self.args[2].sort # Match args are (cond, c1, v1, c2, v2, ...)
        bitops = { Kind.Or, Kind.And, Kind.Xor, Kind.Not, Kind.Equal, Kind.Distinct }
        if self.kind in bitops:
            return BoolSort()
        if self.kind == Kind.Select:
            assert isinstance(self.args[0].sort, ArraySort)
            return self.args[0].sort.elem_sort
        raise NotImplementedError(f"Cannot get Sort for kind {self.kind}")

    @property
    def _children(self):
        return list(self.args)

    def _replace_child(self, new_term, index):
        new_args = list(self.args)
        new_args[index] = new_term
        return OpTerm(self.kind, tuple(new_args))

    def __str__(self):
        return self.to_verilog_str()

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
                assert isinstance(self.args[1], BVConst)
                assert isinstance(self.args[2], BVConst)
                op = cvc5_ctx.solver.mkOp(cvc5_kind, self.args[1].val, self.args[2].val)
                return cvc5_ctx.solver.mkTerm(op, self.args[0].to_cvc5(cvc5_ctx))
            elif self.kind in (Kind.BVZeroPad, Kind.BVSignExtend):
                assert isinstance(self.args[1], BVConst)
                op = cvc5_ctx.solver.mkOp(cvc5_kind, self.args[1].val)
                return cvc5_ctx.solver.mkTerm(op, self.args[0].to_cvc5(cvc5_ctx))
            elif self.kind == Kind.Match:
                # Jank workaround until I figure out how to pattern match vs constants
                a0 = self.args[0]
                # Last expression is the "else" case, so cond doesn't matter
                t = self.args[-1]
                for i in range(len(self.args) - 4, 0, -2):
                    t = a0.op_eq(self.args[i]).ite(self.args[i + 1], t)
                return t.to_cvc5(cvc5_ctx)
                # case_terms = []
                # for i in range(1, len(self.args), 2):
                #     case_terms.append(
                #         cvc5_ctx.solver.mkTerm(
                #             pycvc5.Kind.MatchCase,
                #             self.args[i].to_cvc5(cvc5_ctx),
                #             self.args[i + 1].to_cvc5(cvc5_ctx),
                #         )
                #     )
                # return cvc5_ctx.solver.mkTerm(cvc5_kind, self.args[0].to_cvc5(cvc5_ctx), *case_terms)
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
                Kind.BVNot: "~",
                Kind.BVOrr: "|",
                Kind.BVXorr: "^",
            }
            if v in unops:
                a0_str = wrap(self.args[0])
                return f"{unops[v]}{a0_str}"
            binops = {
                Kind.BVAdd: "+",
                Kind.BVSub: "-",
                Kind.BVMul: "*",
                Kind.BVOr: "|",
                Kind.BVAnd: "&",
                Kind.BVXor: "^",
                Kind.BVSll: "<<",
                Kind.BVSra: ">>",
                Kind.BVSrl: ">>>",
                Kind.BVUlt: "<",
                Kind.BVUle: "<=",
                Kind.BVUgt: ">",
                Kind.BVUge: ">=",
                Kind.Or: "||",
                Kind.And: "&&",
                Kind.Xor: "^", # TODO check if this differs from bv xor
                Kind.Equal: "==",
                Kind.Distinct: "!=",
            }
            if v in binops:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                return f"{a0_str} {binops[v]} {a1_str}"
            if v == Kind.Implies:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                return f"!{a0_str} || {a1_str}"
            if v == Kind.Ite:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                a2_str = wrap(self.args[2])
                return f"{a0_str} ? {a1_str} : {a2_str}"
            if v == Kind.Match:
                # Verilog case statements aren't expressions, so just ITE it up
                a0 = self.args[0]
                # Last expression is the "else" case, so cond doesn't matter
                t = self.args[-1]
                for i in range(len(self.args) - 4, 0, -2):
                    t = a0.op_eq(self.args[i]).ite(self.args[i + 1], t)
                return t.to_verilog_str()
            if v == Kind.BVConcat:
                return "{" + ",".join(wrap(a) for a in self.args) + "}"
            if v == Kind.BVExtract:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                a2_str = wrap(self.args[2])
                return f"{a0_str}[{a1_str}:{a2_str}]"
            if v == Kind.Select:
                a0_str = wrap(self.args[0])
                a1_str = wrap(self.args[1])
                return f"{a0_str}[{a1_str}]"
            if v == Kind.BVSignExtend:
                return f"$signed({self.args[0].to_verilog_str()})"
            if v == Kind.BVZeroPad:
                return wrap(self.args[0])
            raise NotImplementedError(v)
        elif tgt == TargetFormat.UCLID:
            def wrap(term):
                if term._has_children:
                    return "(" + term.to_uclid() + ")"
                else:
                    return term.to_uclid()
            # TODO use uclid library
            unops = {
                Kind.Not: "!",
                Kind.BVNot: "~"
            }
            if self.kind in unops:
                return unops[self.kind] + wrap(self.args[0])
            binops = {
                Kind.BVAdd: "+",
                Kind.BVSub: "-",
                Kind.BVOr: "|",
                Kind.BVAnd: "&",
                Kind.BVXor: "^",
                Kind.BVUlt: "<_u",
                Kind.BVUle: "<=_u",
                Kind.BVUgt: ">_u",
                Kind.BVUge: ">=_u",
                Kind.Equal: "==",
                Kind.Distinct: "!=",
                Kind.Or: "||",
                Kind.And: "&&",
                Kind.Xor: "^", # TODO check if this differs from bv xor
                Kind.Implies: "==>",
            }
            if self.kind in binops:
                return wrap(self.args[0]) + " " + binops[self.kind] + " " + wrap(self.args[1])
            shifts = {
                Kind.BVSll: "bv_left_shift",
                Kind.BVSra: "bv_a_right_shift",
                Kind.BVSrl: "bv_l_right_shift",
            }
            if self.kind in shifts:
                return shifts[self.kind] + "(" + self.args[0].to_uclid() + ", " + self.args[1].to_uclid() + ")"
            if self.kind == Kind.Ite:
                return "if (" + self.args[0].to_uclid() + ") then " + wrap(self.args[1]) + " else " + wrap(self.args[2])
            if self.kind == Kind.BVExtract:
                return wrap(self.args[0]) + "[" + self.args[1].to_uclid() + ":" + self.args[2].to_uclid() + "]"
            if self.kind == Kind.BVConcat:
                return " ++ ".join(wrap(a) for a in self.args)
            if self.kind == Kind.Select:
                return wrap(self.args[0]) + "[" + self.args[1].to_uclid() + "]"
            if self.kind == Kind.BVZeroPad:
                assert isinstance(self.args[1], BVConst)
                return f"bv_zero_extend({self.args[1].val}, {self.args[0].to_uclid()})"
            if self.kind == Kind.Match:
                # uclid case statements aren't expressions, so just ITE it up
                a0 = self.args[0]
                # Last expression is the "else" case, so cond doesn't matter
                t = self.args[-1]
                for i in range(len(self.args) - 4, 0, -2):
                    t = a0.op_eq(self.args[i]).ite(self.args[i + 1], t)
                return t.to_uclid()
            raise NotImplementedError(self.kind)
        raise NotImplementedError("cannot convert OpTerm to " + str(tgt))

    def optimize(self) -> Term:
        # Optimize all children first
        t = self
        for i, child in enumerate(self._children):
            t = t._replace_child(child.optimize(), i)
        assert isinstance(t, OpTerm), t
        assert self.kind == t.kind
        # Constant folding: all arguments must be constants
        # This technically isn't true for stuff like concats,
        # but this heuristic works for binops and unops
        args = t._children
        for child in args:
            if not (isinstance(child, BVConst) or isinstance(child, BoolConst)):
                return t
        # unary ops
        a0 = args[0]
        a0_bw = a0.sort.bitwidth
        a0_mask = (1 << a0.sort.bitwidth) - 1
        if self.kind == Kind.Not:
            return BoolConst.T if a0 == BoolConst.F else BoolConst.T
        if self.kind == Kind.BVNot:
            return BVConst((~a0.val) & a0_mask, a0_bw)
        # binary ops
        a1 = args[1]
        if self.kind == Kind.BVAdd:
            return BVConst((a0.val + a1.val) & a0_mask, a0_bw)
        if self.kind == Kind.BVSub:
            # TODO check wrapping behavior
            return BVConst((a0.val - a1.val) & a0_mask, a0_bw)
        if self.kind == Kind.BVOr:
            return BVConst(a0.val | a1.val, a0_bw)
        if self.kind == Kind.BVAnd:
            return BVConst(a0.val & a1.val, a0_bw)
        if self.kind == Kind.BVXor:
            return BVConst(a0.val ^ a1.val, a0_bw)
        if self.kind == Kind.BVUlt:
            return BoolConst(a0.val < a1.val)
        if self.kind == Kind.BVUle:
            return BoolConst(a0.val <= a1.val)
        if self.kind == Kind.BVUgt:
            return BoolConst(a0.val > a1.val)
        if self.kind == Kind.BVUge:
            return BoolConst(a0.val >= a1.val)
        if self.kind == Kind.Equal:
            return BoolConst(a0.val == a1.val)
        if self.kind == Kind.Distinct:
            return BoolConst(a0.val != a1.val)
        if self.kind == Kind.Or:
            return a0 or a1 # IntEnum provides this automatically
        if self.kind == Kind.And:
            return a0 and a1
        if self.kind == Kind.Xor:
            return BoolConst.T if a0 != a1 else BoolConst.F
        if self.kind == Kind.Implies:
            # p ==> q == !p || q
            return (a0 == BoolConst.F) or a1
        # Kind.BVSll: "bv_left_shift",
        # Kind.BVSra: "bv_a_right_shift",
        # Kind.BVSrl: "bv_l_right_shift",
        # if self.kind == Kind.Select:
        if self.kind == Kind.BVZeroPad:
            return BVConst(a0.val, a1.val + a0_bw)
        # if self.Kind == Kind.SignExtend:
        # ternary operators and higher
        a2 = args[2]
        if self.kind == Kind.BVExtract:
            # TODO check semantics for off-by-one in verilog/cvc?
            # also, what direction does the slice go?
            high = a1.val
            low = a2.val
            width = (high - low) + 1
            mask = ((1 << width) - 1) << low
            return BVConst((a0.val & mask) >> high, width)
        # if self.kind == Kind.BVConcat:
        # Ternary operator
        if self.kind == Kind.Ite:
            print(repr(a0))
            return a1 if bool(a0) else a2
        return t

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

    def __str__(self):
        return self.name

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
    def _children(self):
        return []

    def _replace_child(self, new_term, index):
        return self

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
    def _children(self):
        return self.body

    def _replace_child(self, new_term, index):
        if index != 0:
            raise IndexError()
        return LambdaTerm(self.params, new_term)

    def __str__(self):
        return f"({','.join(str(s) for s in self.params)}) -> {self.body}"

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
    def _children(self):
        return self.body

    def _replace_child(self, new_term, index):
        if index != 0:
            raise IndexError()
        return QuantTerm(self.kind, self.bound_vars, new_term)

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
    def _children(self):
        return list(self.input_values)

    def _replace_child(self, new_term, index):
        raise NotImplementedError()

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


class BoolConst(Term, IntEnum, metaclass=_TermMeta):
    F = 0
    T = 1

    @property
    def sort(self):
        return BoolSort()

    @property
    def _children(self):
        return []

    def _replace_child(self, new_term, index):
        return self

    def __str__(self):
        return "true" if self == self.T else "false"

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            if self == self.F:
                return cvc5_ctx.solver.mkFalse()
            else:
                return cvc5_ctx.solver.mkTrue()
        elif tgt in (TargetFormat.VERILOG, TargetFormat.SYGUS2, TargetFormat.UCLID):
            return "true" if self == self.T else "false"
        raise NotImplementedError("cannot convert BoolConst to " + str(tgt))


@dataclass(frozen=True)
class BVConst(Term):
    val: int
    width: int

    @property
    def sort(self):
        return BVSort(self.width)

    @property
    def _children(self):
        return []

    def _replace_child(self, new_term, index):
        return self

    def __str__(self):
        return f"{self.val}bv{self.width}"

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
        elif tgt == TargetFormat.UCLID:
            return "0x{:x}bv{}".format(self.val, self.width)
        raise NotImplementedError("cannot convert BVConst to " + str(tgt))


# === END SMT TERMS ===
