"""
DSL used to describe expressions for writing assumptions and assertions to inject into verilog code.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
import textwrap
from typing import List, Optional, Tuple, Sequence, Union


@dataclass
class VerificationCtx:
    # TODO elide StatementSeq to also allow [Statement] for ergonomics
    stmts: "StatementSeq"

    def to_verilog(self):
        # TODO type, semantic checking
        return self.stmts.to_verilog()


# === EXPRESSIONS ===

@dataclass
class _Op:
    verilog_symbol: str
    nargs: int = 2


class Operators:
    BVAdd = _Op("+")
    BVSub = _Op("-")
    BVOr  = _Op("|")
    BVAnd = _Op("&")
    BVGt  = _Op(">")
    BVGte = _Op(">=")
    BVLt  = _Op("<")
    BVLte = _Op("<=")
    BVEq  = _Op("==")
    BVNe  = _Op("!=")
    BVNot = _Op("~")
    BVXor = _Op("^")
    And   = _Op("&&")
    Or    = _Op("||")
    Xor   = _Op("^")
    Equal = _Op("==")
    Not   = _Op("!")


@dataclass
class ExprType:
    bitwidth: int


class Expr(ABC):
    @property
    @abstractmethod
    def rettype(self) -> ExprType:
        raise NotImplementedError

    @abstractmethod
    def to_verilog(self) -> str:
        raise NotImplementedError()

    # TODO override more operators for ergonomics
    # TODO add type checking everywhere
    def __add__(self, other):
        return BinOpExpr(Operators.BVAdd, self, other)

    def __eq__(self, other):
        if isinstance(other, Statement):
            raise TypeError("Cannot compare Expression to Statement")
        return BinOpExpr(Operators.BVEq, self, other)


# === DATATYPES ===

class Ref(Expr):
    pass


@dataclass(eq=False)
class SignalRef(Ref):
    """
    An existing named element in the design.
    """
    name: str
    width: int = 1
    path: List = field(default_factory=list)

    def rettype(self):
        return ExprType(self.width)

    def to_verilog(self):
        return ".".join(self.path) + self.name


@dataclass(eq=False)
class WireOrRegRef(Ref):
    name: str
    width: int

    def rettype(self):
        return ExprType(self.width)

    def to_verilog(self):
        return self.name


RegRef = WireOrRegRef
WireRef = WireOrRegRef


class Base(Enum):
    BIN = "b"
    DEC = "d"
    HEX = "h"
    OCT = "o"

    def format(self, n):
        fs = self.value
        if fs == "h":
            fs = "x"
        return ("{:" + fs + "}").format(n)


@dataclass(eq=False)
class BVConst(Expr):
    val: int
    width: int
    base: Base = Base.DEC

    def rettype(self):
        return ExprType(self.width)

    def to_verilog(self):
        if self.width == 0:
            # ???
            return f"{self.val}"
        else:
            return f"{self.width}'{self.base.value}{self.base.format(self.val)}"


@dataclass(eq=False)
class BoolConst(Expr):
    val: bool

    def rettype(self):
        return ExprType(self.val)

    def to_verilog(self):
        return "true" if self.val else "false"


def _maybe_add_parens(expr):
    if isinstance(expr, BinOpExpr) or isinstance(expr, UnOpExpr) or isinstance(expr, TernaryExpr):
        return "(" + expr.to_verilog() + ")"
    else:
        return expr.to_verilog()


@dataclass(eq=False)
class UnOpExpr(Expr):
    operator: _Op
    arg: Expr

    def rettype(self):
        return ExprType(0) # TODO

    def to_verilog(self):
        return self.operator.verilog_symbol + _maybe_add_parens(self.arg)


@dataclass(eq=False)
class BinOpExpr(Expr):
    operator: _Op
    lhs: Expr
    rhs: Expr

    def rettype(self):
        return ExprType(0) # TODO

    def to_verilog(self):
        lhs_str = _maybe_add_parens(self.lhs)
        rhs_str = _maybe_add_parens(self.rhs)
        return f"{lhs_str} {self.operator.verilog_symbol} {rhs_str}"


@dataclass(eq=False)
class TernaryExpr(Expr):
    cond: Expr
    t_value: Expr
    f_value: Expr

    def rettype(self):
        return ExprType(0) # TODO

    def to_verilog(self):
        cond_str = _maybe_add_parens(self.cond)
        t_str = _maybe_add_parens(self.t_value)
        f_str = _maybe_add_parens(self.f_value)
        return f"{cond_str} ? {t_str} : {f_str}"


@dataclass(eq=False)
class Slice(Expr):
    """
    Represents a bit slice from LOW to HIGH, inclusive.
    """

    high: int
    low: int
    source: Expr

    def rettype(self):
        return ExprType(self.high - self.low + 1)

    def to_verilog(self):
        return f"{self.source.to_verilog()}[{self.high}:{self.low}]"


# === STATEMENTS ===

class Statement(ABC):
    @abstractmethod
    def to_verilog(self):
        raise NotImplementedError()

    def __add__(self, other: Union["Statement", List["Statement"]]):
        if isinstance(other, Statement):
            return StatementSeq([self, other])
        elif isinstance(other, list):
            return StatementSeq([self] + other)
        else:
            raise TypeError("Cannot concatenate Statement with object of type " + str(type(other)))

@dataclass
class StatementSeq(Statement):
    stmts: Tuple[Statement, ...]

    def __init__(self, stmts: Sequence[Statement]):
        self.stmts = tuple(stmts)

    def to_verilog(self):
        return "\n".join([s.to_verilog() for s in self.stmts])


@dataclass
class Assignment(Statement):
    # TODO distinguish between reg and wire assigns
    lhs: Ref
    rhs: Expr

    def to_verilog(self):
        return f"{self.lhs.to_verilog()} = {self.rhs.to_verilog()};"


@dataclass
class Assume(Statement):
    expr: Expr
    comment: Optional[str] = None

    def to_verilog(self):
        s = f"assume ({self.expr.to_verilog()});"
        if self.comment is not None:
            s += " // " + self.comment
        return s


@dataclass
class Assert(Statement):
    expr: Expr
    comment: Optional[str] = None

    def to_verilog(self):
        s = f"assert ({self.expr.to_verilog()});"
        if self.comment is not None:
            s += " // " + self.comment
        return s


@dataclass
class RegDecl(Statement):
    """
    Register declaration.
    """
    name: str
    width: int
    # TODO allow for different expressions/const type for init_value
    # also allow array types
    init_value: Optional[int] = None
    anyconst: bool = False

    def to_verilog(self):
        s = f"reg [{self.width - 1}:0] {self.name}"
        if self.anyconst:
            s = "(* anyconst *) " + s
        if self.init_value is not None:
            s += f" = {self.init_value};"
        else:
            s += ";"
        return s

    def get_ref(self):
        return WireOrRegRef(self.name, self.width)


@dataclass
class WireDecl(Statement):
    """
    Wire declaration.
    """
    name: str
    width: int
    expr: Expr

    def to_verilog(self):
        return f"wire {self.name} [{self.width - 1}:0] = {self.expr.to_verilog()};"

    def get_ref(self):
        return WireOrRegRef(self.name, self.width)


@dataclass
class Macro(Statement):
    def to_verilog(self):
        raise NotImplementedError()


@dataclass
class IteStatement(Statement):
    cond: Expr
    t_branch: Statement
    f_branch: Optional[Statement]

    def __post_init__(self):
        if isinstance(self.t_branch, list):
            self.t_branch = StatementSeq(self.t_branch)

    def to_verilog(self):
        # don't use f-string here because of weird dedenting behavior
        s = textwrap.dedent(
            """\
            if ({}) begin
            {}
            end
            """.rstrip() # remove trailing newline
        ).format(
            self.cond.to_verilog(),
            textwrap.indent(self.t_branch.to_verilog(), '    ')
        )
        if self.f_branch is not None:
            s += "\n"
            s += textwrap.dedent(
                """\
                else begin
                {}
                end
                """.rstrip()
            ).format(textwrap.indent(self.f_branch.to_verilog(), '    '))
        return s


class Edge(Enum):
    ALL = ""
    POS = "posedge"
    NEG = "negedge"


@dataclass
class AlwaysAt(Statement):
    edge: Edge
    trigger: Expr
    body: StatementSeq

    def __init__(self, edge, trigger, body: Union[Statement, Sequence[Statement]]):
        self.edge = edge
        self.trigger = trigger
        if not isinstance(body, StatementSeq):
            if isinstance(body, list):
                self.body = StatementSeq(body)
            elif isinstance(body, Statement):
                self.body = StatementSeq([body])
        else:
            self.body = body

    def to_verilog(self):
        return textwrap.dedent(
            """\
            always @({} ({})) begin
            {}
            end
            """.rstrip()
        ).format(
            self.edge.value,
            self.trigger.to_verilog(),
            textwrap.indent(self.body.to_verilog(), '    ')
        )


# === IDIOMS ===

def counter(
    name: str,
    width: int,
    init_value: int=0,
    edge: Edge=Edge.POS,
    trigger: Ref=SignalRef("clock")
    ) -> StatementSeq:
    """
    Returns a sequence of statements that declare and add logic for a counter register.
    """
    r = RegDecl(name, width, init_value)
    add_one = Assignment(
        r.get_ref(),
        BinOpExpr(Operators.BVAdd, r.get_ref(), BVConst(1, width))
    )
    return StatementSeq([r, AlwaysAt(edge, trigger, add_one)])
