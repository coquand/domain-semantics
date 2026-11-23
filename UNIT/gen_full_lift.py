"""Reuse the annotated lifting plans with the full formation frames."""

import re

import gen_aannot as leaf_lift
from gen_annot import split
from gen_full_annot import Rule, RULES, app, args, head, prefix, raw_constructors
from gen_annot import fields


SORT = {("a" + name[1:]): value for name, value in leaf_lift.SORT.items()}
DER = leaf_lift.DER
LIFT = leaf_lift.LIFT
expression = leaf_lift.expression
form = leaf_lift.form
apply = leaf_lift.apply

FORMS = {full: (fields(signature), old, keep) for full, signature, old, keep in raw_constructors()}


def raw(node):
    name = head(node)
    if name not in FORMS:
        return node
    _, old, keep = FORMS[name]
    return app(old, *(raw(args(node)[i]) for i in keep))


def lift_type(index):
    return LIFT[SORT[index[0]]] + "[" + ",".join(map(form, index[1:])) + "]"


def ref(name):
    return leaf_lift.ref(name) if name.startswith("h") else "r" + name


# The plans refer to a few typed helpers explicitly. Other rule and index
# names are read from the full declaration and require no textual rewrites.
EXPLICIT_HELPERS = {
    "at-pi": "ft-pi", "at-el": "ft-el", "apresup": "fpresup",
    "ae-trans": "fe-trans", "am-trans": "fm-trans", "aq-trans": "fq-trans",
    "ajeqty": "fjeqty", "ajeqtm": "fjeqtm", "ajeqsub": "fjeqsub",
    "gnil": "anil", "a-nil": "f-nil",
}


class FullCase(leaf_lift.Case):
    def __post_init__(self):
        self.rule = Rule(self.name, self.decl, expression)
        self.args = self.rule.parameters
        self.index = self.rule.conclusion
        self.full_index = self.rule.judgement(self.index)
        self.hypotheses = self.rule.premises
        self.ann_hypotheses = {h: self.rule.judgement(j) for h, j in self.hypotheses.items()}

    def record(self, hypothesis):
        self.used.add(hypothesis)
        return ref(hypothesis)

    def witness(self, node):
        name = head(node)
        if name not in FORMS:
            return self.bindings[name]
        fields, _, keep = FORMS[name]
        inputs = []
        for i, (child, (_, kind)) in enumerate(zip(args(node), fields, strict=True)):
            if kind == "Nat":
                inputs.append(child)
            elif i in keep:
                inputs += [form(raw(child)), self.witness(child)]
            else:
                inputs.append(self.native(child))
        return apply("e-" + name[1:], inputs) if inputs else "e-" + name[1:]

    def use(self, hypothesis, *contexts):
        j = self.hypotheses[hypothesis]
        return apply("at-" + SORT[j[0]], [*map(form, j[1:]), self.record(hypothesis), *contexts])

    def tm_type(self, hypothesis, ctx, expected, typing):
        j = self.hypotheses[hypothesis]
        return apply(SORT[j[0]] + "-at-type",
                     [*map(form, j[1:]), self.record(hypothesis), ctx, expected, typing])

    def universe(self, hypothesis, ctx):
        j = self.hypotheses[hypothesis]
        assert j[-1] == ("auu", j[-1][1], j[1]), j
        return apply(SORT[j[0]] + "-at-uu",
                     [*map(form, j[1:-1]), j[-1][1], self.record(hypothesis), ctx])

    def extension(self, label, G, A, context, lifted_type, typing):
        if A == "(gel n a)":
            A = "(ael n a)"
            lifted_type = self.witness(("fel", "n", G, "a"))
        return self.local(label, f"LiftCx[aext {G} {A}]",
                          f"at-ext {G} {A} {context} {lifted_type} {typing}")

    def local(self, name, kind, value):
        value = re.sub(r"[\w'-]+", lambda m: EXPLICIT_HELPERS.get(m[0], m[0]), value)
        # The sole literal raw constructor in a plan's local type is gnil.
        kind = re.sub(r"\bgnil\b", "anil", kind)
        return super().local(name, kind, value)

    def proof(self, h, derivation):
        j = self.ann_hypotheses[h]
        kind = DER[SORT["a" + j[0][1:]]] + leaf_lift.arguments(map(self.native, j[1:]))
        label = "p" + h[1:] if h.startswith("h") else "p" + h
        if label in dict(self.args):
            label += "-proof"
        self.premises[h] = self.local(label, kind, derivation)
        return self.premises[h]

    def render(self):
        names = set(re.findall(r"[\w'-]+", " ".join([*self.bindings.values(), *self.locals])))
        self.used.update(h for h in self.hypotheses if ref(h) in names)
        signatures, invocation, proof_args, pattern = [], [], [], []
        for name, kind in self.args:
            pattern.append(name)
            if name in self.hypotheses:
                if name in self.used:
                    signatures.append(f"({ref(name)} : {lift_type(self.hypotheses[name])})")
                    invocation.append(ref(name))
                proof_args.append(self.premises[name])
            else:
                signatures.append(f"({name} : {kind})")
                invocation.append(name)
                proof_args.append(self.bindings[name] + ".t" if kind == "GA" else name)
        term = apply(prefix(self.name), proof_args)
        result = apply("put-" + SORT[self.index[0]], [
            *map(form, self.index[1:]), *map(self.witness, self.full_index[1:]), term,
        ])
        lemma = (f"lift-{self.name}" + leaf_lift.arguments(signatures)
                 + f" : {lift_type(self.index)} =\n  {result[1:-1]}")
        if self.locals:
            lemma += "\n where {\n" + "\n".join(self.locals) + "\n }"
        recursive = [ref(h) for h in self.hypotheses]
        branch = (f"  {self.name}" + leaf_lift.arguments(pattern)
                  + (" |" + leaf_lift.arguments(recursive) if recursive else "")
                  + " -> lift-" + self.name + leaf_lift.arguments(invocation))
        return lemma + " ;\n", branch


def choose_plans(cases):
    saved = leaf_lift.CASES
    try:
        leaf_lift.CASES = {"g" + name[1:]: cases[name] for name in cases if "g" + name[1:] in saved}
        leaf_lift.init_cases()
    finally:
        leaf_lift.CASES = saved

    for name in ("ae-uu-cx", "am-uc-cx", "aq-id-cx", "aq-eps-cx"):
        p = cases[name]
        p.select(G="re.c.e", H="re.k.e")
        p.proof("e", "re.d")
    for name in ("aq-p-cx", "am-q-cx"):
        p = cases[name]
        p.select(G="re.c.e", H="re.k.e", A="rp.a", B="rp.b")
        p.proof("e", "re.d")
        p.use_proof("p", "re.c")


def render_lift():
    cases = {name: FullCase(name, decl) for name, decl in RULES}
    choose_plans(cases)
    rendered = [case.render() for case in cases.values()]
    header = """-- Generated by gen_aannot.py --full. Full annotation with strict forgetful image.
level l ;
open Base ; open Lib[l] ; open AGAT[l] ; open FGAT[l] ; open FTyping[l] ; open FPresup[l] ; open FCtx[l] ;
open FLiftExpr[l] ; open FAnnotBase[l] ;

"""
    tail = """
annotate-at (J : GAJ) (h : GADer J) : LiftAt J = fix-lift J (annotate J h) ;

annotation-section (J : GAJ) (h : GADer J) : Annotation[J] = pack-lift J (annotate J h) ;
"""
    return header + "\n".join(lemma for lemma, _ in rendered) + "\n" + split(
        "annotate : (J : GAJ) -> GADer J -> LiftJ J", [branch for _, branch in rendered]) + tail
