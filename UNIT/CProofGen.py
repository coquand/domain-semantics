#!/usr/bin/env python3
"""Generate Cartmell presuppositions from the signature's sort expressions."""

from pathlib import Path
from textwrap import fill

from CGen import axiom_rule, conversion_rules, equality_rules, operation_rule, rules
from CSig import EQUATIONS, OPERATIONS, SORTS
from gen_aannot import expression, form


SYMBOLS = {operation.symbol: operation for operation in OPERATIONS}


def call(name, *arguments):
    return form((name, *arguments)) if arguments else name


def instance(template, values):
    if isinstance(template, str):
        return values.get(template, template)
    return tuple(instance(part, values) for part in template)


def operation_at(term):
    symbol, *args = (term,) if isinstance(term, str) else term
    op = SYMBOLS[symbol]
    cut = len(op.levels)
    levels, operands = args[:cut], args[cut:]
    variables = [name for name, _ in op.telescope]
    return op, levels, operands, dict(zip((*op.levels, *variables), args, strict=True))


def indices(sort, values):
    return tuple(instance(expression(index), values) for index in sort[1:])


def level_proofs(op, values, bounds):
    return [bounds[instance(expression(bound), values)] for bound in op.bounds]


def formation(term, premises, bounds):
    if isinstance(term, str) and term in premises:
        return premises[term]
    op, levels, operands, values = operation_at(term)
    return call("c-" + op.symbol, *levels, *operands,
                *(formation(arg, premises, bounds) for arg in operands), *level_proofs(op, values, bounds))


def telescope_equality(term, left, right, equalities, bounds):
    if isinstance(term, str) and term in equalities:
        return equalities[term]
    if term == "fnil":
        return call("c-refl-ctx", "fnil", "c-fnil")
    op, levels, operands, values = operation_at(term)
    return call("c-eq-" + op.symbol, *levels, *(instance(arg, left) for arg in operands),
                *(instance(arg, right) for arg in operands),
                *(telescope_equality(arg, left, right, equalities, bounds) for arg in operands),
                *level_proofs(op, instance_mapping(values, left), bounds))


def instance_mapping(values, substitution):
    return {name: instance(term, substitution) for name, term in values.items()}


def proof_tuple(*items):
    if not items:
        return "tt"
    if len(items) == 1:
        return form(items[0])
    return f"({form(items[0])}, {proof_tuple(*items[1:])})"


def hypotheses(rule):
    return [name for name, kind in rule.premises if kind.startswith("CDer ")]


def bound_map(rule):
    bounds = {expression(kind): name for name, kind in rule.premises if kind.startswith("LeN ")}
    for (_, lower, upper), strict in tuple(bounds.items()):
        if isinstance(lower, tuple) and lower[0] == "suc":
            m = lower[1]
            bounds.setdefault(("LeN", m, upper), call("lt-le", m, upper, strict))
    while True:
        available = tuple(bounds.items())
        for (_, lower, middle), first in available:
            for (_, source, upper), second in available:
                if middle == source:
                    bounds.setdefault(("LeN", lower, upper), call("leN-trans", lower, middle, upper, first, second))
        if len(bounds) == len(available):
            return bounds


def render_split(signature, cases):
    branches = []
    for rule, proof in cases:
        operands = [name for name, _ in getattr(rule, "binders", rule.parameters + rule.premises)]
        words = proof.replace("(", " ").replace(")", " ").replace(",", " ").split()
        references = {word.split(".", 1)[0] for word in words}
        recursive = [f"r-{name}" if f"r-{name}" in references else "_" for name in hypotheses(rule)]
        if any(name != "_" for name in recursive):
            operands += ["|", *recursive]
        branch = " ".join((rule.name, *operands, "->", proof))
        branches.append(fill(branch, width=114, initial_indent="  ", subsequent_indent="    ",
                             break_on_hyphens=False))
    return signature + " = split {\n" + " ;\n".join(branches) + " } ;\n"


def introduction_presuppositions(op, bounds):
    premises = {name: "p" + name for name, _ in op.telescope}
    return proof_tuple(*(formation(prefix, premises, bounds) for prefix in indices(op.sort, {})))


def equality_presuppositions(op, rule):
    left = {name: name for name, _ in op.telescope}
    right = {name: name + "'" for name in left}
    equalities = {name: "p" + name for name in left}
    bounds = bound_map(rule)
    paths = {"ctx": (".1", ".2"), "Ty": (".2.1", ".2.2"),
             "Sub": (".2.2.1", ".2.2.2"), "Tm": (".2.2.1", ".2.2.2")}

    def convert(sort, operand, typing, backwards=False):
        old = indices(sort, left)
        new = indices(sort, right)
        if old == new:
            return typing
        equations = [telescope_equality(expression(index), left, right, equalities, bounds) for index in sort[1:]]
        if backwards:
            equations = reverse_sort_equality(sort[0], old, new, equations)
            old, new = new, old
        return call("c-conv-" + sort[0].lower(), *old, *new, operand, *equations, typing)

    left_typings, right_typings = {}, {}
    for name, sort in op.telescope:
        a, b = paths[sort[0]]
        left_typings[name] = f"r-p{name}{a}"
        right_typings[right[name]] = convert(sort, right[name], f"r-p{name}{b}")
    left_term = (op.symbol, *op.levels, *left.values())
    right_term = (op.symbol, *op.levels, *right.values())
    right_proof = convert(op.sort, right_term, formation(right_term, right_typings, bounds), backwards=True)
    return proof_tuple(*(formation(prefix, left_typings, bounds) for prefix in indices(op.sort, left)),
                       formation(left_term, left_typings, bounds), right_proof)


def reverse_sort_equality(sort, old, new, equations):
    if sort != "Tm":
        return [call("c-sym-ctx", a, b, eq) for a, b, eq in zip(old, new, equations, strict=True)]
    old_context, old_type = old
    new_context, new_type = new
    context_eq, type_eq = equations
    # Invert the type equation at the old context before moving it to the new one.
    inverse_type = call("c-sym-ty", old_context, old_type, new_type, type_eq)
    if old_context != new_context:
        inverse_type = call("c-eqconv-ty", old_context, new_context, new_type, old_type, context_eq, inverse_type)
    return [call("c-sym-ctx", old_context, new_context, context_eq), inverse_type]


def render_presuppositions():
    header = """-- Generated by CProofGen.py from CSig.py. Closed Cartmell presuppositions.
level l ;
open Base ; open Lib[l] ; open TTyping[l] ; open FGAT[l] ; open CGAT[l] ;

CPJ : FAJ -> U l = split {
  fjwf G -> Top ;
  fjty G A -> CDer (fjwf G) ;
  fjtm G a A -> CDer (fjwf G) * CDer (fjty G A) ;
  fjsub D s G -> CDer (fjwf D) * CDer (fjwf G) ;
  fjeqcx G H -> CDer (fjwf G) * CDer (fjwf H) ;
  fjeqty G A B -> CDer (fjwf G) * (CDer (fjty G A) * CDer (fjty G B)) ;
  fjeqtm G a b A -> CDer (fjwf G) * (CDer (fjty G A) * (CDer (fjtm G a A) * CDer (fjtm G b A))) ;
  fjeqsub D s t G -> CDer (fjwf D) * (CDer (fjwf G) * (CDer (fjsub D s G) * CDer (fjsub D t G))) } ;

"""
    cases = []
    for op in OPERATIONS:
        rule = operation_rule(op)
        cases.append((rule, introduction_presuppositions(op, bound_map(rule))))
    for equation in EQUATIONS:
        rule = axiom_rule(equation)
        skeleton = {"Ty": ("r-left",), "Tm": ("r-left.1", "r-left.2"), "Sub": ("r-left.1", "r-left.2")}
        cases.append((rule, proof_tuple(*skeleton[equation.sort[0]], "left", "right")))
    eq_cases = {
        "ctx": (("h", "h"), ("r-h.2", "r-h.1"), ("r-h.1", "r-k.2")),
        "ty": (("r-h", "h", "h"), ("r-h.1", "r-h.2.2", "r-h.2.1"), ("r-h.1", "r-h.2.1", "r-k.2.2")),
        "tm": (("r-h.1", "r-h.2", "h", "h"), ("r-h.1", "r-h.2.1", "r-h.2.2.2", "r-h.2.2.1"),
               ("r-h.1", "r-h.2.1", "r-h.2.2.1", "r-k.2.2.2")),
        "sub": (("r-h.1", "r-h.2", "h", "h"), ("r-h.1", "r-h.2.1", "r-h.2.2.2", "r-h.2.2.1"),
                ("r-h.1", "r-h.2.1", "r-h.2.2.1", "r-k.2.2.2")),
    }
    for rule in equality_rules():
        _, method, sort = rule.name.split("-")
        cases.append((rule, proof_tuple(*eq_cases[sort][("refl", "sym", "trans").index(method)])))
    for op in OPERATIONS:
        if op.telescope:
            rule = operation_rule(op, equal=True)
            cases.append((rule, equality_presuppositions(op, rule)))
    conversion = (
        "r-eG.2",
        proof_tuple("r-eG.2", call("c-conv-ty", "G", "H", "x", "eG", "r-h.2.1"),
                    call("c-conv-ty", "G", "H", "y", "eG", "r-h.2.2")),
        proof_tuple("r-eD.2", "r-eG.2"),
        proof_tuple("r-eD.2", "r-eG.2", call("c-conv-sub", "D", "G", "E", "H", "x", "eD", "eG", "r-h.2.2.1"),
                    call("c-conv-sub", "D", "G", "E", "H", "y", "eD", "eG", "r-h.2.2.2")),
        proof_tuple("r-eG.2", call("c-conv-ty", "G", "H", "B", "eG", "r-eA.2.2")),
        proof_tuple("r-eG.2", call("c-conv-ty", "G", "H", "B", "eG", "r-eA.2.2"),
                    call("c-conv-tm", "G", "A", "H", "B", "x", "eG", "eA", "r-h.2.2.1"),
                    call("c-conv-tm", "G", "A", "H", "B", "y", "eG", "eA", "r-h.2.2.2")),
    )
    cases.extend(zip(conversion_rules(), conversion, strict=True))
    return header + render_split("cpresup : (J : FAJ) -> CDer J -> CPJ J", cases)


def render_bounds():
    header = """
c-universe-level : FA -> U l = split {
"""
    for op in OPERATIONS:
        names = " ".join((*op.levels, *(name for name, _ in op.telescope)))
        bound = "LeN n N" if op.symbol == "fuu" else "Top"
        header += f"  {op.symbol} {names} -> {bound} ;\n".replace("  ->", " ->")
    header = header.removesuffix(" ;\n") + " } ;\n"
    header += """
c-universe-bound-at : FAJ -> U l = split {
  fjty G A -> c-universe-level A ;
  fjwf G -> Top ; fjtm G a A -> Top ; fjsub D s G -> Top ;
  fjeqcx G H -> Top ; fjeqty G A B -> Top ; fjeqtm G a b A -> Top ; fjeqsub D s t G -> Top } ;

"""
    bounds = {"c-fuu": "bound1", "c-conv-ty": "r-h"}
    return header + render_split("c-universe-bound-J : (J : FAJ) -> CDer J -> c-universe-bound-at J",
                                 ((rule, bounds.get(rule.name, "tt")) for rule in rules()))


if __name__ == "__main__":
    Path(__file__).with_name("CPresup.seg").write_text(render_presuppositions() + render_bounds(), encoding="utf-8")
