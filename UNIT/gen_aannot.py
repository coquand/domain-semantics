#!/usr/bin/env python3
"""Generate the derivation induction for A3 from the GAT rule signatures.

The plans below choose a common representative of each context and specify
how to align the premises. The copied annotated rule determines the result
syntax and its strict forgetful image.
"""

import argparse
import re
from dataclasses import dataclass, field

from gen_annot import ROOT, RAW, RULES, annotate_rule, annotated, fields, split

EXTRA = {"guu": 1, "guc": 1, "gid": 1, "geps": 1, "gp": 2, "gq": 2}
RAW_ARGS = {annotated(name): fields(decl) for name, decl in RAW}
SORT = {
    "gjwf": "wf", "gjty": "ty", "gjtm": "tm", "gjsub": "sub",
    "gjeqcx": "ce", "gjeqty": "te", "gjeqtm": "me", "gjeqsub": "se",
}
LIFT = {
    "wf": "LiftCx", "ty": "LiftTy", "tm": "LiftTm", "sub": "LiftSub",
    "ce": "LiftCE", "te": "LiftTE", "me": "LiftME", "se": "LiftSE",
}
DER = {
    "wf": "W", "ty": "Ty", "tm": "Tm'", "sub": "Sb",
    "ce": "CE", "te": "TE", "me": "ME", "se": "SE",
}


def expression(source):
    """Parse the application-only syntax used in the rule indices."""
    tokens = iter(re.findall(r"\(|\)|[^()\s]+", source))

    def items():
        result = []
        for token in tokens:
            if token == ")":
                break
            result.append(items() if token == "(" else token)
        return result[0] if len(result) == 1 else tuple(result)

    return items()


def form(node):
    if isinstance(node, str):
        return node
    return "(" + " ".join(map(form, node)) + ")"


def judgement(decl):
    """Return the arguments of a GDer or GADer judgement."""
    for i, char in enumerate(decl):
        if char == ":" and decl[:i].count("(") == decl[:i].count(")"):
            return expression(decl[i + 1:])[1]
    raise ValueError(decl)


def lift_type(j):
    return LIFT[SORT[j[0]]] + "[" + ",".join(map(form, j[1:])) + "]"


def raw(node):
    if isinstance(node, str):
        return "g" + node[1:] if node in RAW_ARGS else node
    head, *args = node
    parts = ("g" + head[1:], *map(raw, args[:len(RAW_ARGS[head])]))
    return parts if len(parts) > 1 else parts[0]


def arguments(items):
    return "".join(" " + item for item in items)


def apply(name, args):
    return "(" + name + arguments(args) + ")"


def ref(name):
    return "r" + name[1:]


@dataclass
class Case:
    name: str
    decl: str
    bindings: dict = field(default_factory=dict)
    premises: dict = field(default_factory=dict)
    locals: list = field(default_factory=list)
    used: set = field(default_factory=set)

    def __post_init__(self):
        self.args = fields(self.decl)
        self.ann = annotate_rule(self.name, self.decl)[len(self.name):]
        self.index = judgement(self.decl)
        self.ann_index = judgement(self.ann)
        self.hypotheses = {
            name: expression(kind)[1] for name, kind in self.args if kind.startswith("GDer")
        }
        self.ann_hypotheses = {
            name: expression(kind)[1] for name, kind in fields(self.ann) if kind.startswith("GADer")
        }

    def record(self, hypothesis):
        self.used.add(hypothesis)
        return ref(hypothesis)

    def select(self, **bindings):
        self.bindings.update(bindings)

    def witness(self, node):
        if isinstance(node, str) and node not in RAW_ARGS:
            return self.bindings[node]
        if isinstance(node, str):
            return "e-" + node[1:]
        head, *args = node
        kinds = [kind for _, kind in RAW_ARGS[head]] + ["GE"] * EXTRA.get("g" + head[1:], 0)
        return apply("e-" + head[1:], [*map(lambda x: form(raw(x)), args),
                                       *(self.witness(x) for x, kind in zip(args, kinds) if kind == "GE")])

    def native(self, node):
        if isinstance(node, str):
            return self.bindings[node] + ".t" if node in self.bindings else node
        return apply(node[0], map(self.native, node[1:]))

    def use(self, hypothesis, *contexts):
        j = self.hypotheses[hypothesis]
        return apply("at-" + SORT[j[0]], [*map(form, j[1:]), self.record(hypothesis), *contexts])

    def tm_type(self, hypothesis, ctx, expected, typing):
        j = self.hypotheses[hypothesis]
        return apply(SORT[j[0]] + "-at-type",
                     [*map(form, j[1:]), self.record(hypothesis), ctx, expected, typing])

    def use_type(self, h, ctx, typing):
        return self.proof(h, self.tm_type(h, ctx, self.witness(self.ann_hypotheses[h][-1]), typing))

    def presup(self, h, projection):
        j = self.ann_hypotheses[h]
        return f"(apresup {self.native(j)} {self.premises[h]}).{projection}"

    def universe(self, hypothesis, ctx):
        j = self.hypotheses[hypothesis]
        assert j[-1][0] == "guu"
        return apply(SORT[j[0]] + "-at-uu",
                     [*map(form, j[1:-1]), j[-1][1], self.record(hypothesis), ctx])

    def local(self, name, kind, value):
        self.locals.append(f"    {name} : {kind} = {value} ;")
        return name

    def proof(self, h, derivation):
        j = self.ann_hypotheses[h]
        kind = DER[SORT["g" + j[0][1:]]] + arguments(map(self.native, j[1:]))
        label = "p" + h[1:]
        if label in {name for name, _ in self.args}:
            label += "-proof"
        self.premises[h] = self.local(label, kind, derivation)
        return self.premises[h]

    def use_proof(self, h, *contexts):
        return self.proof(h, self.use(h, *contexts))

    def use_universe(self, h, ctx):
        return self.proof(h, self.universe(h, ctx))

    def extension(self, label, G, A, context, lifted_type, typing):
        return self.local(label, f"LiftCx[gext {G} {A}]",
                          f"at-ext {G} {A} {context} {lifted_type} {typing}")

    def render(self):
        """Emit a small checked lemma as well as its induction branch."""
        # Select explicitly referenced recursion hypotheses as well as those typed by use().
        texts = " ".join([*self.bindings.values(), *self.locals])
        names = set(re.findall(r"[\w'-]+", texts))
        self.used.update(h for h in self.hypotheses if ref(h) in names)
        recursor = [ref(h) for h in self.hypotheses]
        signature = []
        call = []
        for name, kind in self.args:
            if name in self.hypotheses:
                if name in self.used:
                    signature.append(f"({ref(name)} : {lift_type(self.hypotheses[name])})")
                    call.append(ref(name))
            else:
                signature.append(f"({name} : {kind})")
                call.append(name)
        constructor_args = [
            self.bindings[name] + ".t" if kind == "GE"
            else self.premises[name] if name in self.hypotheses
            else name
            for name, kind in self.args
        ]
        ctor = apply(annotated(self.name), constructor_args)
        result = "put-" + SORT[self.index[0]] + arguments([
            *map(form, self.index[1:]), *map(self.witness, self.ann_index[1:]), ctor,
        ])
        lemma = (f"lift-{self.name}" + arguments(signature)
                 + f" : {lift_type(self.index)} =\n  {result}")
        if self.locals:
            lemma += "\n  where {\n" + "\n".join(self.locals) + "\n  }"
        branch = ("  " + self.name + arguments(name for name, _ in self.args)
                  + (" |" + arguments(recursor) if recursor else "")
                  + f" -> lift-{self.name}" + arguments(call))
        return lemma + " ;\n", branch


CASES = {name: Case(name, decl) for name, decl in RULES}


def plan(name, bindings, proofs):
    p = CASES[name]
    p.select(**bindings)
    for h, proof in proofs.items():
        p.proof(h, proof)
    return p


def init_cases():
    plan("g-nil", {}, {})
    plan("g-ext", dict(G="r.c.e", A="r.a"), dict(h="r.d"))
    plan("gc-nil", {}, {})
    plan("gc-refl", dict(G="r.e"), dict(h="r.ok"))
    p = CASES["gc-ext"]
    p.select(G="r1.c.e", D="r1.k.e", A="r2.a", B="r2.b")
    p.proof("h1", "r1.d")
    p.use_proof("h2", "r1.c")

    for name in ("gs-id", "gs-eps", "gt-uu"):
        plan(name, dict(G="r.e"), dict(h="r.ok"))
    plan("gs-p", dict(G="r.c.e", A="r.a"), dict(h="r.d"))

    p = CASES["gs-comp"]
    p.select(T="r2.c.e", D="r2.k.e", G="r1.k.e", s="r1.x", d="r2.x")
    p.use_proof("h1", "r2.k", "r1.k")
    p.proof("h2", "r2.d")
    p = CASES["gs-lift"]
    p.select(D="r1.c.e", G="r1.k.e", s="r1.x", A="r2.a")
    p.proof("h1", "r1.d")
    p.use_proof("h2", "r1.k")
    p = CASES["gs-sec"]
    p.select(G="r1.c.e", A="r1.a", a="r2.x")
    p.proof("h1", "r1.d")
    p.proof("h2", p.tm_type("h2", "r1.c", "r1.a", "p1"))
    p = CASES["gs-cx"]
    p.select(D="r.c.e", G="r.k.e", s="r.x", **{"D'":"r0.e", "G'":"r0'.e"})
    p.proof("h0", "r0.ok")
    p.proof("h0'", "r0'.ok")
    p.use_proof("h1", "r.c", "r0")
    p.use_proof("h2", "r.k", "r0'")
    p.proof("h", "r.d")
    p = CASES["gt-pi"]
    p.select(G="r1.c.e", A="r1.a", B="r2.a")
    p.proof("h1", "r1.d")
    p.extension("ext", "G", "A", "r1.c", "r1.a", "p1")
    p.use_proof("h2", "ext")
    p = CASES["gt-el"]
    p.select(G="r.c.e", a="r.x")
    p.use_universe("h", "r.c")
    p = CASES["gt-sb"]
    p.select(D="r2.c.e", G="r2.k.e", A="r1.a", s="r2.x")
    p.use_proof("h1", "r2.k")
    p.proof("h2", "r2.d")
    for name, terms in (("gt-cx", dict(A="r2.a")), ("gm-cx", dict(a="r2.x", A="r2.t")),
                        ("ge-cx", dict(A="r2.a", B="r2.b")), ("gm-ecx", dict(a="r2.x", b="r2.y", A="r2.t"))):
        p = CASES[name]
        p.select(G="r2.c.e", D="r0.e", **terms)
        p.proof("h0", "r0.ok")
        p.use_proof("h1", "r2.c", "r0")
        p.proof("h2", "r2.d")

    # Formation and typing. Under a binder use the extension chosen by its domain.
    p = CASES["gm-lam"]
    p.select(G="r1.c.e", A="r1.a", B="r2.a", b="r3.x")
    p.proof("h1", "r1.d")
    p.extension("ext", "G", "A", "r1.c", "r1.a", "p1")
    p.use_proof("h2", "ext")
    p.use_type("h3", "ext", "p2")

    p = CASES["gm-app"]
    p.select(G="r1.c.e", A="r1.a", B="r2.a", c="r3.x", a="r4.x")
    p.proof("h1", "r1.d")
    p.extension("ext", "G", "A", "r1.c", "r1.a", "p1")
    p.use_proof("h2", "ext")
    p.use_type("h3", "r1.c", "(at-pi r1.c.e.t r1.a.t r2.a.t p1 p2)")
    p.use_type("h4", "r1.c", "p1")

    for name in ("gm-pic", "ge-el-pic", "gm-lf-pic"):
        p = CASES[name]
        p.select(G="r1.c.e", a="r1.x", b="r2.x")
        p.use_universe("h1", "r1.c")
        p.extension("ext", "G", "(gel n a)", "r1.c", "(e-el n a r1.x)", "(at-el r1.c.e.t n r1.x.t p1)")
        p.use_universe("h2", "ext")

    plan("gm-uc", dict(G="r.e"), dict(h="r.ok"))
    for name in ("gm-lf", "ge-el-lf", "gm-lf-lf", "gm-elf", "ge-el"):
        p = CASES[name]
        selected = dict(G="r.c.e", a="r.x")
        if name in ("gm-elf", "ge-el"):
            selected["a'"] = "r.y"
        p.select(**selected)
        p.use_universe("h", "r.c")
    plan("gm-q", dict(G="r.c.e", A="r.a"), dict(h="r.d"))

    p = CASES["gm-sb"]
    p.select(D="r2.c.e", G="r2.k.e", a="r1.x", A="rA.a", s="r2.x")
    p.use_proof("hA", "r2.k")
    p.use_type("h1", "r2.k", "pA")
    p.proof("h2", "r2.d")
    p = CASES["gm-conv"]
    p.select(G="r2.c.e", a="r1.x", A="r2.a", B="r2.b")
    p.proof("h2", "r2.d")
    p.use_type("h1", "r2.c", p.presup("h2", "2.1"))

    for name in ("ge-refl", "ge-sb-id"):
        plan(name, dict(G="r.c.e", A="r.a"), dict(h="r.d"))
    plan("ge-sym", dict(G="r.c.e", A="r.a", B="r.b"), dict(h="r.d"))

    p = CASES["ge-trans"]
    p.select(G="r1.c.e", A="r1.a", B="r1.b", C="r2.b")
    p.proof("h1", "r1.d")
    p.local("right", "TE r1.c.e.t r2.a.t r2.b.t", p.use("h2", "r1.c"))
    p.local("middle", "TE r1.c.e.t r1.b.t r2.a.t",
            "(ty-align G B r1.c r1.b r2.a (apresup (ajeqty r1.c.e.t r1.a.t r1.b.t) p1).2.2 "
            "(apresup (ajeqty r1.c.e.t r2.a.t r2.b.t) right).2.1)")
    p.proof("h2", "ae-trans r1.c.e.t r1.b.t r2.a.t r2.b.t middle right")

    p = CASES["ge-pi"]
    p.select(G="r1.c.e", A="r1.a", B="r2.a", **{"A'":"r1.b", "B'":"r2.b"})
    p.proof("h1", "r1.d")
    p.proof("h0", p.presup("h1", "2.1"))
    p.extension("ext", "G", "A", "r1.c", "r1.a", "p0")
    p.use_proof("h2", "ext")

    p = CASES["ge-sb"]
    p.select(D="r4.c.e", G="r4.k.e", A="r1.a", s="r4.x", **{"A'":"r1.b", "s'":"r4.y"})
    p.use_proof("h1", "r4.k")
    p.proof("h0", p.presup("h1", "2.1"))
    p.proof("h4", "r4.d")
    p.proof("h2", p.presup("h4", "2.2.1"))
    p.proof("h3", p.presup("h4", "2.2.2"))

    for name in ("ge-el-uc", "gm-lf-uc"):
        plan(name, dict(G="r.e"), dict(h="r.ok"))

    p = CASES["ge-sb-comp"]
    p.select(T="r2.c.e", D="r2.k.e", G="r1.k.e", A="r0.a", s="r1.x", d="r2.x")
    p.use_proof("h0", "r1.k")
    p.use_proof("h1", "r2.k", "r1.k")
    p.proof("h2", "r2.d")

    p = CASES["ge-pi-sb"]
    p.select(D="r3.c.e", G="r3.k.e", A="r1.a", B="r2.a", s="r3.x")
    p.use_proof("h1", "r3.k")
    p.extension("ext", "G", "A", "r3.k", "r1.a", "p1")
    p.use_proof("h2", "ext")
    p.proof("h3", "r3.d")

    plan("ge-uu-sb", dict(D="r.c.e", G="r.k.e", s="r.x"), dict(h="r.d"))
    p = CASES["ge-el-sb"]
    p.select(D="r2.c.e", G="r2.k.e", a="r1.x", s="r2.x")
    p.use_universe("h1", "r2.k")
    p.proof("h2", "r2.d")

    for name in ("gm-refl", "gm-sb-id"):
        plan(name, dict(G="r.c.e", a="r.x", A="r.t"), dict(h="r.d"))
    p = CASES["gm-sym"]
    p.select(G="r.c.e", a="r.x", b="r.y", A="r.t")
    p.proof("h", "r.d")
    p.proof("hA", p.presup("h", "2.1"))
    p = CASES["gm-trans"]
    p.select(G="r1.c.e", a="r1.x", b="r1.y", c="r2.y", A="r1.t")
    p.proof("h1", "r1.d")
    p.local("right", "ME r1.c.e.t r2.x.t r2.y.t r1.t.t",
            p.tm_type("h2", "r1.c", "r1.t", p.presup("h1", "2.1")))
    p.local("middle", "ME r1.c.e.t r1.y.t r2.x.t r1.t.t",
            "tm-align G b A r1.c r1.y r2.x r1.t " + p.presup("h1", "2.2.2")
            + " (apresup (ajeqtm r1.c.e.t r2.x.t r2.y.t r1.t.t) right).2.2.1")
    p.proof("h2", "am-trans r1.c.e.t r1.y.t r2.x.t r2.y.t r1.t.t middle right")

    p = CASES["gm-eqconv"]
    p.select(G="r2.c.e", a="r1.x", b="r1.y", A="r2.a", B="r2.b")
    p.proof("h2", "r2.d")
    p.use_type("h1", "r2.c", p.presup("h2", "2.1"))

    for name in ("gm-elam", "gm-eapp"):
        p = CASES[name]
        p.select(G="r1.c.e", A="r1.a", B="r2.a", **{"A'":"r1.b", "B'":"r2.b"})
        if name == "gm-elam":
            p.select(b="r3.x", **{"b'":"r3.y"})
        else:
            p.select(c="r3.x", a="r4.x", **{"c'":"r3.y", "a'":"r4.y"})
        p.proof("h1", "r1.d")
        p.proof("h0", p.presup("h1", "2.1"))
        p.extension("ext", "G", "A", "r1.c", "r1.a", "p0")
        p.use_proof("h2", "ext")
        if name == "gm-elam":
            p.use_type("h3", "ext", p.presup("h2", "2.1"))
        else:
            p.proof("hB", p.presup("h2", "2.1"))
            p.use_type("h3", "r1.c", "(at-pi r1.c.e.t r1.a.t r2.a.t p0 pB)")
            p.use_type("h4", "r1.c", "p0")
            p.proof("ha", p.presup("h4", "2.2.1"))

    p = CASES["gm-epic"]
    p.select(G="r1.c.e", a="r1.x", b="r2.x", **{"a'":"r1.y", "b'":"r2.y"})
    p.use_universe("h1", "r1.c")
    p.proof("h0", p.presup("h1", "2.2.1"))
    p.extension("ext", "G", "(gel n a)", "r1.c", "(e-el n a r1.x)", "(at-el r1.c.e.t n r1.x.t p0)")
    p.use_universe("h2", "ext")

    p = CASES["gm-esb"]
    p.select(D="r4.c.e", G="r4.k.e", a="r1.x", A="rA.a", s="r4.x", **{"a'":"r1.y","s'":"r4.y"})
    p.use_proof("hA", "r4.k")
    p.use_type("h1", "r4.k", "pA")
    p.proof("h0", p.presup("h1", "2.2.1"))
    p.proof("h4", "r4.d")
    p.proof("h2", p.presup("h4", "2.2.1"))
    p.proof("h3", p.presup("h4", "2.2.2"))

    for name, terms in (("gm-beta", dict(b="r1.x", a="r2.x")), ("gm-eta", dict(f="r.x"))):
        p = CASES[name]
        p.select(G="rA.c.e", A="rA.a", B="rB.a", **terms)
        p.proof("hA", "rA.d")
        p.extension("ext", "G", "A", "rA.c", "rA.a", "pA")
        p.use_proof("hB", "ext")
        if name == "gm-beta":
            p.use_type("h1", "ext", "pB")
            p.use_type("h2", "rA.c", "pA")
        else:
            p.use_type("h", "rA.c", "(at-pi rA.c.e.t rA.a.t rB.a.t pA pB)")

    p = CASES["gm-sb-comp"]
    p.select(T="r2.c.e", D="r2.k.e", G="r0.c.e", a="r0.x", A="r0.t", s="r1.x", d="r2.x")
    p.proof("h0", "r0.d")
    p.use_proof("h1", "r2.k", "r0.c")
    p.proof("h2", "r2.d")

    for name in ("gm-lam-sb", "gm-app-sb"):
        p = CASES[name]
        p.select(G="r1.c.e", A="r1.a", B="r2.a")
        p.proof("h1", "r1.d")
        p.extension("ext", "G", "A", "r1.c", "r1.a", "p1")
        p.use_proof("h2", "ext")
        if name == "gm-lam-sb":
            p.select(b="r3.x", D="r4.c.e", s="r4.x")
            p.use_type("h3", "ext", "p2")
            p.use_proof("h4", "r4.c", "r1.c")
        else:
            p.select(c="r3.x", a="r4.x", D="r5.c.e", s="r5.x")
            p.use_type("h3", "r1.c", "(at-pi r1.c.e.t r1.a.t r2.a.t p1 p2)")
            p.use_type("h4", "r1.c", "p1")
            p.use_proof("h5", "r5.c", "r1.c")

    p = CASES["gm-pic-sb"]
    p.select(G="r3.k.e", a="r1.x", b="r2.x", D="r3.c.e", s="r3.x")
    p.use_universe("h1", "r3.k")
    p.extension("ext", "G", "(gel n a)", "r3.k", "(e-el n a r1.x)", "(at-el r3.k.e.t n r1.x.t p1)")
    p.use_universe("h2", "ext")
    p.proof("h3", "r3.d")

    plan("gm-uc-sb", dict(D="r.c.e", G="r.k.e", s="r.x"), dict(h="r.d"))
    p = CASES["gm-lf-sb"]
    p.select(D="r2.c.e", G="r2.k.e", a="r1.x", s="r2.x")
    p.use_universe("h1", "r2.k")
    p.proof("h2", "r2.d")

    for name in ("gm-q-lift", "gq-p-lift"):
        p = CASES[name]
        p.select(D="r2.c.e", G="r2.k.e", A="r1.a", s="r2.x")
        p.use_proof("h1", "r2.k")
        p.proof("h2", "r2.d")
    for name in ("gm-q-sec", "gq-p-sec"):
        p = CASES[name]
        p.select(G="r1.c.e", A="r1.a", a="r2.x")
        p.proof("h1", "r1.d")
        p.use_type("h2", "r1.c", "p1")

    for name in ("gq-refl", "gq-idl", "gq-idr", "gq-eps"):
        p = CASES[name]
        p.select(D="r.c.e", G="r.k.e", s="r.x")
        if name == "gq-eps":
            p.select(G="r.c.e")
            p.local("nil", "LiftCx[gnil]", "put-wf gnil e-nil a-nil")
            p.use_proof("h", "r.c", "nil")
        else:
            p.proof("h", "r.d")

    plan("gq-sym", dict(D="r.c.e", s="r.x", t="r.y", G="r.k.e"), dict(h="r.d"))

    p = CASES["gq-trans"]
    p.select(D="r1.c.e", G="r1.k.e", s="r1.x", t="r1.y", u="r2.y")
    p.proof("h1", "r1.d")
    p.local("right", "SE r1.c.e.t r2.x.t r2.y.t r1.k.e.t", p.use("h2", "r1.c", "r1.k"))
    p.local("middle", "SE r1.c.e.t r1.y.t r2.x.t r1.k.e.t",
            "sub-align D t G r1.c r1.k r1.y r2.x " + p.presup("h1", "2.2.2")
            + " (apresup (ajeqsub r1.c.e.t r2.x.t r2.y.t r1.k.e.t) right).2.2.1")
    p.proof("h2", "aq-trans r1.c.e.t r1.y.t r2.x.t r2.y.t r1.k.e.t middle right")

    p = CASES["gq-comp"]
    p.select(T="r2.c.e", D="r2.k.e", G="r1.k.e", s="r1.x", d="r2.x", **{"s'":"r1.y","d'":"r2.y"})
    p.use_proof("h1", "r2.k", "r1.k")
    p.proof("h2", "r2.d")

    p = CASES["gq-lift"]
    p.select(D="r3.c.e", G="r3.k.e", A="r1.a", s="r3.x", **{"A'":"r1.b","s'":"r3.y"})
    p.use_proof("h1", "r3.k")
    p.proof("h0", p.presup("h1", "2.1"))
    p.proof("h3", "r3.d")
    p.proof("h2", p.presup("h3", "2.2.1"))

    p = CASES["gq-sec"]
    p.select(G="r1.c.e", A="r1.a", a="r2.x", **{"A'":"r1.b","a'":"r2.y"})
    p.proof("h1", "r1.d")
    p.proof("hA", p.presup("h1", "2.1"))
    p.use_type("h2", "r1.c", "pA")
    p.proof("ha", p.presup("h2", "2.2.1"))
    p.proof("ha'", p.presup("h2", "2.2.2"))

    p = CASES["gq-assoc"]
    p.select(Q="r3.c.e", T="r3.k.e", D="r2.k.e", G="r1.k.e", s="r1.x", d="r2.x", e="r3.x")
    p.use_proof("h1", "r2.k", "r1.k")
    p.use_proof("h2", "r3.k", "r2.k")
    p.proof("h3", "r3.d")

    for name in ("gq-lift-id", "gq-lift-p-sec-q"):
        plan(name, dict(G="r.c.e", A="r.a"), dict(h="r.d"))

    p = CASES["gq-lift-comp"]
    p.select(T="r2.c.e", D="r2.k.e", G="r1.k.e", A="r0.a", s="r1.x", d="r2.x")
    p.use_proof("h0", "r1.k")
    p.use_proof("h1", "r2.k", "r1.k")
    p.proof("h2", "r2.d")

    p = CASES["gq-sec-comp"]
    p.select(D="r3.c.e", G="r3.k.e", A="r1.a", a="r2.x", s="r3.x")
    p.use_proof("h1", "r3.k")
    p.use_type("h2", "r3.k", "p1")
    p.proof("h3", "r3.d")


def main():
    init_cases()
    rendered = [case.render() for case in CASES.values()]
    branches = [branch for _, branch in rendered]
    tail = "\n" + split("annotate : (J : GJ) -> GDer J -> LiftJ J", branches)
    tail += """
annotate-at (J : GJ) (h : GDer J) : LiftAt J = fix-lift J (annotate J h) ;

annotation-section (J : GJ) (h : GDer J) : Annotation[J] = pack-lift J (annotate J h) ;
"""
    header = """-- Generated by gen_aannot.py. Annotation with strict forgetful image.
level l ;
open Base ; open Lib[l] ; open GAT[l] ; open AGAT[l] ; open APresup[l] ; open ACtx[l] ;
open ALiftExpr[l] ; open AAnnotBase[l] ;

"""
    (ROOT / "AAnnot.seg").write_text(header + "\n".join(lemma for lemma, _ in rendered) + tail)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="generate the full-annotation Seg files")
    if parser.parse_args().full:
        from gen_full_annot import generate_full

        generate_full(expression, form)
    else:
        main()
