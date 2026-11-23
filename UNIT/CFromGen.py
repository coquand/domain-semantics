#!/usr/bin/env python3
"""Generate direct Cartmell axiom witnesses and the reverse translation."""

from dataclasses import dataclass
from pathlib import Path
from textwrap import fill

from CGen import Rule, axiom_rule, judgment, operation_rule
from CProofGen import SYMBOLS, bound_map, call, hypotheses, instance, level_proofs, operation_at, render_split
from CSig import EQUATIONS
from gen_aannot import expression, form, judgement
from gen_annot import declarations, fields


ROOT = Path(__file__).resolve().parent

# These endpoints use conversion derived from earlier axiom instances.
CONVERTED_AXIOMS = {
    "fm-sb-id", "fm-sb-comp", "fq-lift-id", "fq-lift-comp", "fm-q-lift", "fm-q-sec",
    "fm-lam-sb", "fm-app-sb", "fm-eta", "fe-el-sb", "fm-pic-sb", "fm-uc-sb", "fm-lf-sb", "fm-lf-pic",
}


def judgment_parts(judgment_):
    match judgment_:
        case ("fjwf", g):
            return ("ctx",), g
        case ("fjeqcx", g, h):
            return ("ctx",), g, h
        case ("fjty", g, a):
            return ("Ty", g), a
        case ("fjeqty", g, a, b):
            return ("Ty", g), a, b
        case ("fjsub", d, s, g):
            return ("Sub", d, g), s
        case ("fjeqsub", d, s, t, g):
            return ("Sub", d, g), s, t
        case ("fjtm", g, a, t):
            return ("Tm", g, t), a
        case ("fjeqtm", g, a, b, t):
            return ("Tm", g, t), a, b
    raise ValueError(judgment_)


def presuppositions(judgment_):
    match judgment_:
        case ("fjwf", _):
            return ()
        case ("fjty", g, _):
            return (((), ("fjwf", g)),)
        case ("fjsub", d, _, g):
            return (((1,), ("fjwf", d)), ((2,), ("fjwf", g)))
        case ("fjtm", g, _, a):
            return (((1,), ("fjwf", g)), ((2,), ("fjty", g, a)))
        case ("fjeqcx", g, h):
            return (((1,), ("fjwf", g)), ((2,), ("fjwf", h)))
        case ("fjeqty", g, a, b):
            return (((1,), ("fjwf", g)), ((2, 1), ("fjty", g, a)), ((2, 2), ("fjty", g, b)))
        case ("fjeqsub", d, s, t, g):
            return (((1,), ("fjwf", d)), ((2, 1), ("fjwf", g)),
                    ((2, 2, 1), ("fjsub", d, s, g)), ((2, 2, 2), ("fjsub", d, t, g)))
        case ("fjeqtm", g, a, b, t):
            return (((1,), ("fjwf", g)), ((2, 1), ("fjty", g, t)),
                    ((2, 2, 1), ("fjtm", g, a, t)), ((2, 2, 2), ("fjtm", g, b, t)))
    raise ValueError(judgment_)


class MissingProof(ValueError):
    pass


def typing_node(sort, term):
    return expression(judgment(tuple(map(form, sort)), form(term)))


class InstanceProofs:
    def __init__(self, rule, recursive=False):
        self.facts = {expression(kind)[1]: f"r-{name}" if recursive else name
                      for name, kind in rule.premises if kind.startswith("CDer ")}
        for judgment_, proof in tuple(self.facts.items()):
            base = call("cpresup", judgment_, proof)
            for path, implied in presuppositions(judgment_):
                projection = "".join(f".{field}" for field in path)
                self.facts.setdefault(implied, base + projection if projection else base)
        self.bounds = bound_map(rule)
        for judgment_, proof in self.facts.items():
            if judgment_[0] == "fjty" and isinstance(judgment_[2], tuple) and judgment_[2][0] == "fuu":
                self.bounds.setdefault(("LeN", judgment_[2][1], "N"), call("c-universe-bound-J", judgment_, proof))

    def prove(self, target):
        if target in self.facts:
            return self.facts[target]
        sort, term, *other = judgment_parts(target)
        if other:
            if term != other[0]:
                raise MissingProof(target)
            typing = typing_node(sort, term)
            return call("c-refl-" + sort[0].lower(), *sort[1:], term, self.prove(typing))
        if (term if isinstance(term, str) else term[0]) not in SYMBOLS:
            raise MissingProof(target)
        op, levels, operands, values = operation_at(term)
        result_sort = (op.sort[0], *(instance(expression(index), values) for index in op.sort[1:]))
        actual = typing_node(result_sort, term)
        if actual != target:
            raise MissingProof(target)
        checked = [self.prove(instance(expression(judgment(arg_sort, name)), values))
                   for name, arg_sort in op.telescope]
        return call("c-" + op.symbol, *levels, *operands, *checked, *level_proofs(op, values, self.bounds))

    def apply(self, rule, values, name=None):
        arguments = [values[var] for var, _ in rule.parameters]
        for _, kind in rule.premises:
            premise = instance(expression(kind), values)
            arguments.append(self.prove(premise[1]) if premise[0] == "CDer" else self.bounds[premise])
        return call(rule.name if name is None else name, *arguments)


def direct_axiom_complete():
    direct = []
    needs_conversion = set()
    for equation in EQUATIONS:
        rule = axiom_rule(equation)
        given = Rule(rule.name, rule.parameters, rule.premises[:-2], rule.conclusion)
        values = {name: name for name, _ in rule.parameters}
        try:
            proof = InstanceProofs(given).apply(rule, values)
        except MissingProof:
            needs_conversion.add(equation.name)
        else:
            signature = "use-" + given.render()
            body = fill(proof, width=114, initial_indent="  ", subsequent_indent="    ", break_on_hyphens=False)
            direct.append(f"{signature} =\n{body} ;\n")
    if needs_conversion != CONVERTED_AXIOMS:
        raise ValueError(f"Conversion witness inventory changed: {sorted(needs_conversion ^ CONVERTED_AXIOMS)}")
    return """-- Generated by CFromGen.py. Axiom endpoints typed by operation formation.
level l ;
open Base ; open Lib[l] ; open TTyping[l] ; open FGAT[l] ; open CGAT[l] ; open CPresup[l] ;

""" + "\n".join(direct)


@dataclass(frozen=True)
class FullRule(Rule):
    binders: tuple


def full_rules():
    source = (ROOT / "FGAT.seg").read_text().split("data FADer : (J : FAJ) -> U l =", 1)[1].split(";", 1)[0]
    for name, declaration in declarations(source):
        binders = fields(declaration)
        parameters = tuple((name, kind) for name, kind in binders if kind in ("FA", "Nat"))
        premises = tuple((name, " ".join(kind.split()).replace("FADer", "CDer"))
                         for name, kind in binders if kind not in ("FA", "Nat"))
        yield FullRule(name, parameters, premises, judgement(declaration), tuple(binders))


def conversion_cases():
    return {
        "fs-cx": "c-conv-sub D G D' G' s r-h1 r-h2 r-h",
        "ft-cx": "c-conv-ty G D A r-h1 r-h2",
        "fe-cx": "c-eqconv-ty G D A B r-h1 r-h2",
        "fm-cx": "c-conv-tm G A D A a r-h1 (c-refl-ty G A (cpresup (fjtm G a A) r-h2).2) r-h2",
        "fm-ecx": "c-eqconv-tm G A D A a b r-h1 (c-refl-ty G A (cpresup (fjeqtm G a b A) r-h2).2.1) r-h2",
        "fm-conv": "c-conv-tm G A G B a (c-refl-ctx G (cpresup (fjtm G a A) r-h1).1) r-h2 r-h1",
        "fm-eqconv": "c-eqconv-tm G A G B a b (c-refl-ctx G (cpresup (fjeqtm G a b A) r-h1).1) r-h2 r-h1",
    }


def from_full_case(full, proof, axioms, conversions):
    if full.name in conversions:
        return conversions[full.name]
    if full.name in axioms:
        rule = axioms[full.name]
        given = Rule(rule.name, rule.parameters, rule.premises[:-2], rule.conclusion)
        values = {name: name for name, _ in rule.parameters}
        return proof.apply(given, values, "use-" + rule.name)
    sort, term, *other = judgment_parts(full.conclusion)
    if not other:
        return proof.prove(full.conclusion)
    suffix = sort[0].lower()
    if full.name == "fc-nil" or full.name.endswith("-refl"):
        return proof.prove(full.conclusion)
    if full.name.endswith("-sym"):
        return call("c-sym-" + suffix, *sort[1:], other[0], term, "r-h")
    if full.name.endswith("-trans"):
        left = expression(full.premises[0][1])[1]
        middle = judgment_parts(left)[2]
        return call("c-trans-" + suffix, *sort[1:], term, middle, other[0], "r-h1", "r-h2")
    op, levels, _, left = operation_at(term)
    op_right, levels_right, _, right = operation_at(other[0])
    if op != op_right or levels != levels_right:
        raise ValueError(full.name)
    values = left | {name + "'": right[name] for name, _ in op.telescope}
    return proof.apply(operation_rule(op, equal=True), values)


def render_from_full():
    axioms = {eq.name: axiom_rule(eq) for eq in EQUATIONS}
    conversions = conversion_cases()
    cases = []
    for rule in full_rules():
        try:
            proof = from_full_case(rule, InstanceProofs(rule, recursive=True), axioms, conversions)
        except (ValueError, KeyError) as error:
            raise ValueError(f"Cannot translate {rule.name}: {error}") from error
        cases.append((rule, proof))
    return """-- Generated by CFromGen.py. Interpret the full Ehrhard rules in CGAT.
level l ;
open Base ; open Lib[l] ; open TTyping[l] ; open FGAT[l] ; open CGAT[l] ; open CPresup[l] ;
open CAxiomBase[l] ; open CAxiomAction[l] ; open CAxiomUniv[l] ; open CAxiomProd[l] ;

""" + render_split("c-from-full : (J : FAJ) -> FADer J -> CDer J", cases)


if __name__ == "__main__":
    files = {"CAxiomBase.seg": direct_axiom_complete(), "CFromFull.seg": render_from_full()}
    for name, output in files.items():
        (ROOT / name).write_text(output, encoding="utf-8")
