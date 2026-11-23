#!/usr/bin/env python3
"""Generate the closed Cartmell rules in CGAT.seg from CSig.py."""

from dataclasses import dataclass
from pathlib import Path
from textwrap import fill

from CSig import EQUATIONS, OPERATIONS, SORTS, ctx, sub, tm, ty


@dataclass(frozen=True)
class Rule:
    name: str
    parameters: tuple
    premises: tuple
    conclusion: str

    def render(self):
        binders = " ".join(f"({name} : {kind})" for name, kind in self.parameters + self.premises)
        signature = f"{self.name} {binders} : CDer {self.conclusion}"
        return fill(signature, width=116, subsequent_indent="      ", break_on_hyphens=False)


def judgment(sort, left, right=None):
    arguments = left if right is None else f"{left} {right}"
    match sort:
        case ("ctx",):
            symbol = "fjwf" if right is None else "fjeqcx"
            return f"({symbol} {arguments})"
        case ("Ty", context):
            symbol = "fjty" if right is None else "fjeqty"
            return f"({symbol} {context} {arguments})"
        case ("Tm", context, type_):
            symbol = "fjtm" if right is None else "fjeqtm"
            return f"({symbol} {context} {arguments} {type_})"
        case ("Sub", source, target):
            symbol = "fjsub" if right is None else "fjeqsub"
            return f"({symbol} {source} {arguments} {target})"
    raise ValueError(f"Unknown sort {sort}")


def proof(name, sort, left, right=None):
    return name, "CDer " + judgment(sort, left, right)


def parameters(levels, *tuples):
    return tuple((level, "Nat") for level in levels) + tuple(
        (name, "FA") for telescope in tuples for name, _ in telescope
    )


def bound_premises(bounds):
    return tuple((f"bound{i}", bound) for i, bound in enumerate(bounds, 1))


def instance_premises(telescope, equal=False):
    return tuple(proof(f"p{name}", sort, name, name + "'" if equal else None)
                 for name, sort in telescope)


def operation_rule(operation, equal=False):
    variables = tuple(name for name, _ in operation.telescope)
    left = " ".join((operation.symbol, *operation.levels, *variables))
    if equal:
        right_telescope = tuple((name + "'", sort) for name, sort in operation.telescope)
        right = " ".join((operation.symbol, *operation.levels, *(name + "'" for name in variables)))
        conclusion = judgment(operation.sort, f"({left})", f"({right})")
        binders = parameters(operation.levels, operation.telescope, right_telescope)
    else:
        conclusion = judgment(operation.sort, f"({left})" if variables else left)
        binders = parameters(operation.levels, operation.telescope)
    name = ("c-eq-" if equal else "c-") + operation.symbol
    premises = instance_premises(operation.telescope, equal) + bound_premises(operation.bounds)
    return Rule(name, binders, premises, conclusion)


def axiom_rule(equation):
    premises = instance_premises(equation.telescope) + bound_premises(equation.bounds) + (
        proof("left", equation.sort, equation.left),
        proof("right", equation.sort, equation.right),
    )
    return Rule("c-" + equation.name, parameters(equation.levels, equation.telescope), premises,
                judgment(equation.sort, equation.left, equation.right))


def equality_rules():
    for symbol, telescope in SORTS.items():
        sort = (symbol, *(name for name, _ in telescope))
        suffix = symbol.lower()
        yield Rule(f"c-refl-{suffix}", parameters((), telescope, (("x", sort),)),
                   (proof("h", sort, "x"),), judgment(sort, "x", "x"))
        yield Rule(f"c-sym-{suffix}", parameters((), telescope, (("x", sort), ("y", sort))),
                   (proof("h", sort, "x", "y"),), judgment(sort, "y", "x"))
        yield Rule(f"c-trans-{suffix}", parameters((), telescope, (("x", sort), ("y", sort), ("z", sort))),
                   (proof("h", sort, "x", "y"), proof("k", sort, "y", "z")), judgment(sort, "x", "z"))


def conversion_rules():
    # Reflect sort equality as equality of the sort's arguments at the left instance.
    for source, target in ((ty("G"), ty("H")), (sub("D", "G"), sub("E", "H")),
                           (tm("G", "A"), tm("H", "B"))):
        suffix, *indices = source
        right_indices = target[1:]
        telescope = SORTS[suffix]
        sort_equalities = tuple(proof(f"e{left}", argument_sort, left, right)
                                for (_, argument_sort), left, right in zip(telescope, indices, right_indices))
        binders = tuple((name, "FA") for name in (*indices, *right_indices))
        yield Rule(f"c-conv-{suffix.lower()}", binders + (("x", "FA"),),
                   sort_equalities + (proof("h", source, "x"),), judgment(target, "x"))
        yield Rule(f"c-eqconv-{suffix.lower()}", binders + (("x", "FA"), ("y", "FA")),
                   sort_equalities + (proof("h", source, "x", "y"),), judgment(target, "x", "y"))


def rules():
    yield from (operation_rule(operation) for operation in OPERATIONS)
    yield from (axiom_rule(equation) for equation in EQUATIONS)
    yield from equality_rules()
    yield from (operation_rule(operation, equal=True) for operation in OPERATIONS if operation.telescope)
    yield from conversion_rules()


def render():
    header = """-- Generated by CGen.py from CSig.py. Cartmell rules at the empty telescope.
level l ;
open Base ; open Lib[l] ; open FGAT[l] ;

data CDer : (J : FAJ) -> U l =
    """
    return header + "\n  | ".join(rule.render() for rule in rules()) + " ;\n"


if __name__ == "__main__":
    Path(__file__).with_name("CGAT.seg").write_text(render(), encoding="utf-8")
