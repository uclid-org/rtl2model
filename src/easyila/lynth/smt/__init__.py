"""
Provides in-memory representations of SMT expressions and grammars, which can then be translated
to solver backends like CVC5 and Z3.

TODO add str methods to everything
"""

from abc import ABC, ABCMeta, abstractmethod
from dataclasses import dataclass
from enum import Enum, EnumMeta, auto
import textwrap
from typing import Dict, List, Set, Tuple, Optional

import pycvc5

from .sorts import *
from .terms import *


@dataclass
class Grammar:
    bound_vars: Tuple[Variable, ...]
    nonterminals: Tuple[Variable, ...]
    terms: Dict[Variable, Tuple[Term, ...]]
    """
    Maps a non-terminal Variable to a list of reduction rules, each of which could either be another
    nonterminal or a variable.
    """

    def get_sygus2(self) -> str:
        block = "(" + " ".join(f"({b.name} {b.sort.to_sygus2()})" for b in self.non_terminals) + ")"
        block += "\n("
        for key, rules in self.terms.items():
            block += f"(({key} {key.sort.to_sygus2()})"
            for rule in rules:
                block += f"  ({rule.to_sygus2()})"
            block += "\n  )"
        block += "\n)"
        return block


@dataclass
class SynthFun:
    name: str
    bound_vars: Tuple[Variable, ...]
    return_sort: Sort
    grammar: Optional[Grammar] = None

    def new_solver(self) -> "Solver":
        """
        Creates a new Solver instance to synthesize this function.
        """
        # sorts, variables get automatically read
        return Solver(synthfuns=[self])

    def apply(self, *args):
        return self.to_uf().apply(*args)

    def to_uf(self) -> UFTerm:
        return UFTerm(self.name, self.return_sort, self.bound_vars)

    def to_cvc5(self, cvc5_ctx) -> Term:
        return cvc5_ctx.synthfuns[self.name]

    def to_sygus2(self) -> str:
        args = "(" + " ".join(f"({a.name} {a.sort.to_sygus2()})" for a in self.bound_vars) + \
                ") " + self.return_sort.to_sygus2()
        if self.grammar is None:
            return f"(synth-fun {self.name} " + args + ")"
        else:
            return f"(synth-fun {self.name} {args}\n" + \
                textwrap.indent(self.grammar.get_sygus2(), "  ") + "\n)"
        raise NotImplementedError("sygus2 translation not yet implemented for synthfuns with grammar")


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
            self.sorts[sort] = sort.to_cvc5(self)

    def add_term(self, term):
        # TODO handle nonterminals being used as arguments?
        k = term
        if isinstance(term, Variable):
            v = term.to_cvc5(self)
        elif isinstance(term, OpTerm):
            v = term.to_cvc5(self)
        elif isinstance(term, BoolConst):
            v = term.to_cvc5(self)
        else:
            raise Exception(f"invalid term: {term}")
        self.terms[k] = v

    def _add_grammar(self, grammar):
        g = self.solver.mkSygusGrammar(
            [v.to_cvc5(self) for v in grammar.bound_vars],
            # TODO merge nt map with variables
            [t.to_cvc5(self) for t in grammar.terms.keys()]
        )
        for t, rules in grammar.terms.items():
            g.addRules(t.to_cvc5(self), [s.to_cvc5(self) for s in rules])
        for v in grammar.nonterminals:
            g.addAnyVariable(v.to_cvc5(self))
        self.grammars.append(g)
        return g

    def add_synthfun(self, sf):
        if sf.grammar is not None:
            g = self._add_grammar(sf.grammar)
        else:
            g = None
        self.synthfuns[sf.name] = self.solver.synthFun(
            sf.name,
            [v.to_cvc5(self) for v in sf.bound_vars],
            sf.return_sort.to_cvc5(self),
            g
        )

    def add_constraint(self, constraint):
        constraint_term = constraint.to_cvc5(self)
        self.solver.addSygusConstraint(constraint_term)
        self.constraints.append(constraint_term)


class Solver:
    """
    Wrapper class for an SMT solver.

    When a new term is added, all necessary sorts and sub-terms are added as well.
    """

    variables: List[Term]
    """A list of bound variables."""
    sorts: Set[Sort]
    terms: List[Term]
    synthfuns: List[SynthFun]
    constraints: List[Term]
    _cvc5_wrapper: Optional[Cvc5Ctx]

    def __init__(self, variables=None, sorts=None, terms=None, synthfuns=None, constraints=None, backend="cvc5"):
        # can't make these default args, since the same instance of a default arg is shared
        # across every call to __init__
        variables = list(variables or [])
        sorts = set(sorts or set())
        terms = list(terms or [])
        synthfuns = list(synthfuns or [])
        constraints = list(constraints or [])
        self.variables = variables
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
        for v in self.variables:
            wrapper.add_term(v)
        for sort in self.sorts:
            wrapper.try_add_sort(sort)
        for term in self.terms:
            wrapper.add_term(term)
        for sf in self.synthfuns:
            wrapper.add_synthfun(sf)
        for constraint in self.constraints:
            wrapper.add_constraint(constraint)
        self._cvc5_wrapper = wrapper

    def add_sort(self, sort: Sort) -> Sort:
        self.sorts.add(sort)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.try_add_sort(sort)
        return sort

    def add_variable(self, v: Variable) -> Variable:
        # self.add_term(newvar)
        self.variables.append(v)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_term(v)
        return v

    def add_term(self, term: Term) -> Term:
        self.terms.append(term)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_term(term)
        return term

    def add_constraint(self, term: Term) -> Term:
        assert isinstance(term.sort, BoolSort), f"Sygus constraint must be boolean; instead got {term}"
        self.constraints.append(term)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_constraint(term)
        return term

    def add_synthfun(self, fn: SynthFun) -> SynthFun:
        self.synthfuns.append(fn)
        if self._cvc5_wrapper:
            self._cvc5_wrapper.add_synthfun(fn)
        return fn

    def check_synth(self):
        if self._cvc5_wrapper:
            # TODO choose specific synth functions
            c_slv = self.get_cvc5_solver()
            s = c_slv.checkSynth()
            if not s.isUnsat():
                return SynthResult(False, None)
            else:
                sols = c_slv.getSynthSolutions(list(self._cvc5_wrapper.synthfuns.values()))
                sf_names = list(self._cvc5_wrapper.synthfuns.keys())
                return SynthResult(True, {sf_names[i]: LambdaTerm.from_cvc5(t) for i, t in enumerate(sols)})
        raise NotImplementedError()

    def get_cvc5_solver(self):
        """
        Returns a reference to the underlying CVC5 solver (None if another backend was configured).

        IMPORTANT: any modifications to this CVC5 solver are not reflected in this `Solver` object
        -- make changes at your own risk.
        """
        return self._cvc5_wrapper.solver

    def get_sygus2(self):
        """
        Returns a string representing a SyGuS2 (.sy) encoding the variables and assumptions
        in this solver.
        """
        text = "(set-logic QF_ABV)\n"
        for v in self.variables:
            text += v.get_decl().to_sygus2() + "\n"
        for sf in self.synthfuns:
            text += sf.to_sygus2() + "\n"
        for constraint in self.constraints:
            text += f"(constraint {constraint.to_sygus2()})\n"
        text += "(check-synth)"
        return text


@dataclass
class SynthResult:
    is_unsat: bool
    solution: Optional[Dict[str, LambdaTerm]]
