#!/usr/bin/env python3
"""Generate full sort annotations and their erasure from the bounded AGAT."""

from textwrap import fill

from gen_annot import ROOT, data, declarations, fields, split


AGAT = (ROOT / "AGAT.seg").read_text()


def constructors(header):
    return declarations(AGAT.split(header + " =", 1)[1].split(";", 1)[0])


RAW = constructors("data GA")
JUDGEMENTS = constructors("data GAJ")
RULES = constructors("data GADer : (J : GAJ) -> U l")


def app(head, *args):
    return (head, *args) if args else head


def apply(function, *args):
    return " ".join((function, *args))


def prefix(name):
    return "f" + name[1:]


def right_index(decl, expression):
    """Return the conclusion of a constructor after its top-level binders."""
    depth = 0
    for index, char in enumerate(decl):
        if char == ":" and depth == 0:
            return expression(decl[index + 1:])[1]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
    raise ValueError(decl)


def head(node):
    return node if isinstance(node, str) else node[0]


def args(node):
    return () if isinstance(node, str) else node[1:]


class Rule:
    """Recover the frame of each constructor in an inherited rule index."""

    def __init__(self, name, declaration, expression):
        self.name = name
        self.parameters = fields(declaration)
        self.premises = {
            name: expression(kind)[1]
            for name, kind in self.parameters
            if kind.startswith("GADer")
        }
        self.conclusion = right_index(declaration, expression)
        self.term_types = {}
        self.sub_endpoints = {}
        for premise in self.premises.values():
            match premise:
                case ("ajtm", g, a, t):
                    self.term_types.setdefault(a, (g, t))
                case ("ajeqtm", g, a, b, t):
                    for term in (a, b):
                        self.term_types.setdefault(term, (g, t))
                case ("ajsub", d, s, g):
                    self.sub_endpoints.setdefault(s, (d, g))
                case ("ajeqsub", d, s, t, g):
                    for sub in (s, t):
                        self.sub_endpoints.setdefault(sub, (d, g))

    def context(self, node):
        match node:
            case "anil":
                return "fnil"
            case ("aext", raw_g, a):
                g = self.context(raw_g)
                return app("fext", g, self.type(a, g))
            case str():
                return node
        raise ValueError((self.name, "context", node))

    def type(self, node, g):
        match node:
            case ("auu", n, x):
                return app("fuu", n, self.context(x))
            case ("api", a, b):
                domain = self.type(a, g)
                return app("fpi", g, domain, self.type(b, app("fext", g, domain)))
            case ("ael", n, a):
                return app("fel", n, g, self.term(a, g)[0])
            case ("asb", a, s):
                sub, source, target = self.sub(s, g)
                return app("ftsb", source, target, self.type(a, target), sub)
            case str():
                return node
        raise ValueError((self.name, "type", node, g))

    def term(self, node, g):
        match node:
            case ("alam", a, b, body):
                domain = self.type(a, g)
                extension = app("fext", g, domain)
                codomain = self.type(b, extension)
                return (
                    app("flam", g, domain, codomain, self.term(body, extension)[0]),
                    app("fpi", g, domain, codomain),
                )
            case ("aapp", a, b, function, argument):
                domain = self.type(a, g)
                extension = app("fext", g, domain)
                codomain = self.type(b, extension)
                arg = self.term(argument, g)[0]
                return (
                    app("fapp", g, domain, codomain, self.term(function, g)[0], arg),
                    app("ftsb", g, extension, codomain, app("fsec", g, domain, arg)),
                )
            case ("apic", n, a, b):
                domain = self.term(a, g)[0]
                extension = app("fext", g, app("fel", n, g, domain))
                return app("fpic", n, g, domain, self.term(b, extension)[0]), app("fuu", n, g)
            case ("auc", m, n, x):
                origin = self.context(x)
                return app("fuc", m, n, origin), app("fuu", n, origin)
            case ("alf", m, n, a):
                # Lift the original body in its original binder in lift/product.
                if self.name == "am-lf-pic" and a == "b":
                    g = self.context(self.term_types[a][0])
                return app("flf", m, n, g, self.term(a, g)[0]), app("fuu", n, g)
            case ("aq", x, a):
                origin = self.context(x)
                domain = self.type(a, origin)
                extension = app("fext", origin, domain)
                return (
                    app("fq", origin, domain),
                    app("ftsb", extension, origin, domain, app("fp", origin, domain)),
                )
            case ("asb", a, s):
                sub, source, target = self.sub(s, g)
                term, operand_type = self.term(a, target)
                if operand_type is None:
                    raise ValueError((self.name, "missing type for term action", node))
                return (
                    app("fmsb", source, target, operand_type, term, sub),
                    app("ftsb", source, target, operand_type, sub),
                )
            case str():
                if node in self.term_types:
                    origin, ty = self.term_types[node]
                    return node, self.type(ty, self.context(origin))
                return node, None
        raise ValueError((self.name, "term", node, g))

    def sub(self, node, d=None, g=None):
        match node:
            case ("aid", x):
                origin = self.context(x)
                return app("fid", origin), origin, origin
            case ("aeps", x):
                origin = self.context(x)
                return app("feps", origin), origin, "fnil"
            case ("ap", x, a):
                origin = self.context(x)
                domain = self.type(a, origin)
                return app("fp", origin, domain), app("fext", origin, domain), origin
            case ("alift", a, s):
                sub, source, target = self.sub(s)
                domain = self.type(a, target)
                return (
                    app("flift", source, target, domain, sub),
                    app("fext", source, app("ftsb", source, target, domain, sub)),
                    app("fext", target, domain),
                )
            case ("asec", a, x):
                if d is None:
                    raise ValueError((self.name, "missing source for section", node))
                domain = self.type(a, d)
                return app("fsec", d, domain, self.term(x, d)[0]), d, app("fext", d, domain)
            case ("acomp", s, e):
                right, source, middle = self.sub(e, d)
                left, _, target = self.sub(s, middle, g)
                return app("fcomp", source, middle, target, left, right), source, target
            case str():
                if node in self.sub_endpoints:
                    source, target = map(self.context, self.sub_endpoints[node])
                    return node, source, target
                if d is not None and g is not None:
                    return node, d, g
        raise ValueError((self.name, "substitution", node, d, g))

    def judgement(self, node):
        match node:
            case ("ajwf", g):
                return app("fjwf", self.context(g))
            case ("ajeqcx", g, d):
                return app("fjeqcx", self.context(g), self.context(d))
            case ("ajty", x, a):
                g = self.context(x)
                return app("fjty", g, self.type(a, g))
            case ("ajeqty", x, a, b):
                g = self.context(x)
                return app("fjeqty", g, self.type(a, g), self.type(b, g))
            case ("ajtm", x, a, t):
                g = self.context(x)
                return app("fjtm", g, self.term(a, g)[0], self.type(t, g))
            case ("ajeqtm", x, a, b, t):
                g = self.context(x)
                return app("fjeqtm", g, self.term(a, g)[0], self.term(b, g)[0], self.type(t, g))
            case ("ajsub", x, s, y):
                d, g = self.context(x), self.context(y)
                return app("fjsub", d, self.sub(s, d, g)[0], g)
            case ("ajeqsub", x, s, t, y):
                d, g = self.context(x), self.context(y)
                return app("fjeqsub", d, self.sub(s, d, g)[0], self.sub(t, d, g)[0], g)
        raise ValueError((self.name, "judgement", node))


# The new context arguments are inserted after the external level indices.
# Each retained operand points to its position in the new constructor.
RAW_FIELDS = {
    "api": ("fpi", "(G A B : FA)", (1, 2)),
    "ael": ("fel", "(n : Nat) (G a : FA)", (0, 2)),
    "alam": ("flam", "(G A B b : FA)", (1, 2, 3)),
    "aapp": ("fapp", "(G A B c a : FA)", (1, 2, 3, 4)),
    "apic": ("fpic", "(n : Nat) (G a b : FA)", (0, 2, 3)),
    "alf": ("flf", "(m n : Nat) (G a : FA)", (0, 1, 3)),
    "acomp": ("fcomp", "(T D G s d : FA)", (3, 4)),
    "alift": ("flift", "(D G A s : FA)", (2, 3)),
    "asec": ("fsec", "(G A a : FA)", (1, 2)),
}

ACTIONS = (
    ("ftsb", "(D G A s : FA)", (2, 3)),
    ("fmsb", "(D G A a s : FA)", (3, 4)),
)


def raw_constructors():
    for old_name, decl in RAW:
        if old_name == "asb":
            yield from ((name, sig, old_name, keep) for name, sig, keep in ACTIONS)
        else:
            name, sig, keep = RAW_FIELDS.get(
                old_name, (prefix(old_name), decl.strip().replace("GA", "FA"), tuple(range(len(fields(decl)))))
            )
            yield name, sig, old_name, keep


# Specify each single-coordinate rule by its left formation constructor and
# the changed argument of the resulting expression.
CONGRUENCES = (
    ("fe-pi-context", "at-pi", "G"),
    ("fe-el-context", "at-el", "G"),
    ("fe-sb-source", "at-sb", "D"),
    ("fe-sb-target", "at-sb", "G"),
    ("fm-lam-context", "am-lam", "G"),
    ("fm-app-context", "am-app", "G"),
    ("fm-pic-context", "am-pic", "G"),
    ("fm-lf-context", "am-lf", "G"),
    ("fm-sb-source", "am-sb", "D"),
    ("fm-sb-target", "am-sb", "G"),
    ("fm-sb-type", "am-sb", "A"),
    ("fq-comp-source", "as-comp", "T"),
    ("fq-comp-middle", "as-comp", "D"),
    ("fq-comp-target", "as-comp", "G"),
    ("fq-lift-source", "as-lift", "D"),
    ("fq-lift-target", "as-lift", "G"),
    ("fq-sec-context", "as-sec", "G"),
)


def equality_index(index, coordinate, changed):
    sort, source, expr, *tail = index
    # Only the top-level argument changes. Types and endpoints stay on the left.
    assert args(expr).count(coordinate) == 1, (index, coordinate)
    updated = app(head(expr), *(changed if item == coordinate else item for item in args(expr)))
    return app({"fjty": "fjeqty", "fjtm": "fjeqtm", "fjsub": "fjeqsub"}[sort], source, expr, updated, *tail)


def argument_types(rule, form):
    return [
        (name, "FADer " + form(rule.judgement(rule.premises[name]))
         if name in rule.premises else "FA" if kind == "GA" else kind)
        for name, kind in rule.parameters
    ]


def signature(name, params, conclusion, form):
    binders = [f"({var} : {kind})" for var, kind in params]
    return fill(apply(name, *binders, ": FADer " + form(conclusion)), width=112, subsequent_indent="      ")


def render_fgat(rules, form):
    declarations = [
        signature(prefix(rule.name), argument_types(rule, form), rule.judgement(rule.conclusion), form)
        for rule in rules.values()
    ]
    for name, intro, coordinate in CONGRUENCES:
        rule = rules[intro]
        updated = coordinate + "'"
        params = argument_types(rule, form)
        assert updated not in dict(params)
        change = app("fjeqty", "G", coordinate, updated) if coordinate == "A" else app("fjeqcx", coordinate, updated)
        params += [(updated, "FA"), ("e", "FADer " + form(change))]
        declarations.append(signature(name, params, equality_index(rule.judgement(rule.conclusion), coordinate, updated), form))

    raw = list(raw_constructors())
    raw_bound = [
        apply(name, *(var for var, _ in fields(sig))) + (" -> LeN n N" if name == "fuu" else " -> Top")
        for name, sig, _, _ in raw
    ]
    judgement_bound = [
        apply(prefix(name), *(var for var, _ in fields(sig))) + (" -> f-universe-level A" if name == "ajty" else " -> Top")
        for name, sig in JUDGEMENTS
    ]
    bound = []
    for rule in rules.values():
        lhs = apply(prefix(rule.name), *(var for var, _ in rule.parameters))
        tail = {"at-uu": " -> nb", "at-cx": " | rh0 rh1 rh2 -> rh2"}.get(rule.name, " -> tt")
        bound.append(lhs + tail)
    for name, intro, coordinate in CONGRUENCES:
        bound.append(apply(name, *(var for var, _ in rules[intro].parameters), coordinate + "'", "e -> tt"))

    parts = [
        "-- Generated by gen_aannot.py --full from AGAT.seg and the sort frames in PLAN-ANNOT-FULL.md.",
        "level l ;\nopen Base ; open Lib[l] ;",
        data("data FA", [apply(name, sig).rstrip() for name, sig, _, _ in raw]),
        data("data FAJ", [prefix(name) + sig.replace("GA", "FA").rstrip() for name, sig in JUDGEMENTS]),
        data("data FADer : (J : FAJ) -> U l", declarations),
        split("f-universe-level : FA -> U l", ["  " + case for case in raw_bound]),
        split("f-universe-bound-at : FAJ -> U l", ["  " + case for case in judgement_bound]),
        split("f-universe-bound-J : (J : FAJ) -> FADer J -> f-universe-bound-at J", ["  " + case for case in bound]),
        "f-universe-bound (G X : FA) (n : Nat) (h : FADer (fjty G (fuu n X))) : LeN n N =\n"
        "  f-universe-bound-J (fjty G (fuu n X)) h ;",
    ]
    return "\n\n".join(part.rstrip() for part in parts) + "\n"


def erased_formation(rule):
    return apply(
        rule.name,
        *(f"(ff {var})" if kind == "GA" else "r" + var if var in rule.premises else var
          for var, kind in rule.parameters),
    )


def render_forget(rules, form):
    raw_cases = []
    for name, sig, old_name, keep in raw_constructors():
        params = fields(sig)
        erased = ["r" + var if kind == "FA" else var for var, kind in params]
        recursive = [erasure for erasure, (_, kind) in zip(erased, params) if kind == "FA"]
        lhs = apply(name, *(var for var, _ in params), *(["|", *recursive] if recursive else []))
        raw_cases.append("  " + lhs + " -> " + apply(old_name, *(erased[i] for i in keep)))
    judgements = [
        "  " + apply(prefix(name), *(var for var, _ in fields(sig)))
        + " -> " + apply(name, *(f"(ff {var})" for var, _ in fields(sig)))
        for name, sig in JUDGEMENTS
    ]
    cases = []
    for rule in rules.values():
        lhs = apply(prefix(rule.name), *(var for var, _ in rule.parameters))
        if rule.premises:
            lhs = apply(lhs, "|", *("r" + var for var in rule.premises))
        cases.append("  " + lhs + " -> " + erased_formation(rule))
    for name, intro, coordinate in CONGRUENCES:
        rule = rules[intro]
        lhs = apply(name, *(var for var, _ in rule.parameters), coordinate + "'", "e",
                    "|", *("r" + var for var in rule.premises), "re")
        j, *operands = rule.judgement(rule.conclusion)
        refl = {"fjty": "ae-refl", "fjtm": "am-refl", "fjsub": "aq-refl"}[j]
        rhs = apply(refl, *(f"(ff {form(node)})" for node in operands), "(" + erased_formation(rule) + ")")
        cases.append("  " + lhs + " ->\n    " + rhs)

    return "\n\n".join((
        "-- Generated by gen_aannot.py --full. Forget the additional sort arguments.",
        "level l ;\nopen Base ; open AGAT[l] ; open FGAT[l] ;",
        split("ff : FA -> GA", raw_cases).rstrip(),
        split("ffJ : FAJ -> GAJ", judgements).rstrip(),
        split("forget-full : (J : FAJ) -> FADer J -> GADer (ffJ J)", cases).rstrip(),
    )) + "\n"


def frame_cases(formations, sort, render, default):
    for name, sig, _, _ in raw_constructors():
        formation = formations.get(name)
        if formation is not None and formation[1][0] == sort:
            rule, index, expr = formation
            yield "  " + apply(name, *args(expr)) + " -> " + render(rule, index)
        else:
            yield "  " + apply(name, *(var for var, _ in fields(sig))) + " -> " + default


def product(items, join):
    if len(items) == 1:
        return items[0]
    return join(items[0], product(items[1:], join))


def render_generation(rules, form):
    formations = {}
    by_rule = {}
    for rule in rules.values():
        index = rule.judgement(rule.conclusion)
        if index[0] in ("fjty", "fjtm", "fjsub") and isinstance(index[2], tuple):
            expr = index[2]
            formations[head(expr)] = (rule, index, expr)
            by_rule[rule.name] = (index, expr)

    def premise_types(rule, index):
        params = [kind for _, kind in argument_types(rule, form) if kind != "FA" and kind != "Nat"]
        return product(params, lambda a, b: f"{a} * ({b})")

    families = []
    for sort, label, indices in (
        ("fjty", "Ty", (("ty-context", 1),)),
        ("fjtm", "Tm", (("tm-context", 1), ("tm-type", 3))),
        ("fjsub", "Sub", (("sub-source", 1), ("sub-target", 3))),
    ):
        families.append(split(f"{label}Intro : FA -> U l",
                              frame_cases(formations, sort, premise_types, "Empty")))
        for name, index in indices:
            families.append(split(f"{name} : FA -> FA", frame_cases(
                formations, sort, lambda _, j: form(j[index]), "fnil")))

    frames = r"""
TyGen (G A : FA) : U l = TyIntro A * CE (ty-context A) G ;
TmGen (G a A : FA) : U l = TmIntro a * (CE (tm-context a) G * TE G (tm-type a) A) ;
SubGen (D s G : FA) : U l = SubIntro s * (CE (sub-source s) D * CE (sub-target s) G) ;

intro-ty (A : FA) (h : Ty (ty-context A) A) (p : TyIntro A) : TyGen (ty-context A) A =
  (p,cx-refl (fpresup (fjty (ty-context A) A) h)) ;

intro-tm (a : FA) (h : Tm' (tm-context a) a (tm-type a)) (p : TmIntro a) : TmGen (tm-context a) a (tm-type a) =
  (p,(cx-refl q.1,ty-refl q.2))
 where { q : FPJ (fjtm (tm-context a) a (tm-type a)) = fpresup (fjtm (tm-context a) a (tm-type a)) h ; } ;

intro-sub (s : FA) (h : Sb (sub-source s) s (sub-target s)) (p : SubIntro s) : SubGen (sub-source s) s (sub-target s) =
  (p,(cx-refl q.1,cx-refl q.2))
 where { q : FPJ (fjsub (sub-source s) s (sub-target s)) = fpresup (fjsub (sub-source s) s (sub-target s)) h ; } ;

TypingGen : FAJ -> U l = split {
  fjty G A -> TyGen G A ; fjtm G a A -> TmGen G a A ; fjsub D s G -> SubGen D s G ;
  fjwf G -> Top ; fjeqcx G D -> Top ; fjeqty G A B -> Top ; fjeqtm G a b A -> Top ; fjeqsub D s t G -> Top } ;
"""
    conversion = {
        "at-cx": "| r0 r1 r -> (r.1,f-cx-trans (ty-context A) G D r.2 h1)",
        "am-conv": "| r r2 -> (r.1,(r.2.1,ty-trans r.2.2 h2))",
        "am-cx": "| r0 r1 r -> (r.1,(f-cx-trans (tm-context a) G D r.2.1 h1,te-cx h0 h1 r.2.2))",
        "as-cx": "| r0 r0' r1 r2 r -> (r.1,(f-cx-trans (sub-source s) D D' r.2.1 h1,f-cx-trans (sub-target s) G G' r.2.2 h2))",
    }
    cases = []
    for rule in rules.values():
        native = prefix(rule.name)
        lhs = apply(native, *(var for var, _ in rule.parameters))
        if rule.name in by_rule:
            index, expr = by_rule[rule.name]
            intro = {"fjty": "ty", "fjtm": "tm", "fjsub": "sub"}[index[0]]
            premises = [name for name, kind in rule.parameters if kind not in ("GA", "Nat")]
            packed = product(premises, lambda a, b: f"({a},{b})")
            proof = "(" + lhs + ")"
            cases.append("  " + lhs + " -> " + apply("intro-" + intro, form(expr), proof, packed))
        else:
            body = conversion.get(rule.name, "-> tt")
            cases.append("  " + lhs + " " + body)
    for name, intro, coordinate in CONGRUENCES:
        cases.append("  " + apply(name, *(var for var, _ in rules[intro].parameters), coordinate + "'", "e -> tt"))

    endpoints = """
gen-ty (G A : FA) (h : Ty G A) : TyGen G A = gen-typing (fjty G A) h ;
gen-tm (G a A : FA) (h : Tm' G a A) : TmGen G a A = gen-typing (fjtm G a A) h ;
gen-sub (D s G : FA) (h : Sb D s G) : SubGen D s G = gen-typing (fjsub D s G) h ;
"""
    return "\n\n".join((
        "-- Generated by gen_aannot.py --full. Recover recorded introduction frames through conversion.",
        "level l ;\nopen Base ; open Lib[l] ; open FGAT[l] ; open FTyping[l] ; open FPresup[l] ; open FCtx[l] ;",
        *(family.rstrip() for family in families),
        frames.strip(),
        split("gen-typing : (J : FAJ) -> FADer J -> TypingGen J", cases).rstrip(),
        endpoints.strip(),
    )) + "\n"


def generate_full(expression, form):
    from gen_full_coherence import render_shapes, render_coherence
    from gen_full_expr import render_expr
    from gen_full_lift import render_lift

    rules = {name: Rule(name, decl, expression) for name, decl in RULES}
    (ROOT / "FGAT.seg").write_text(render_fgat(rules, form))
    (ROOT / "FForget.seg").write_text(render_forget(rules, form))
    (ROOT / "FGen.seg").write_text(render_generation(rules, form))
    (ROOT / "FShape.seg").write_text(render_shapes())
    (ROOT / "FCoherence.seg").write_text(render_coherence())
    (ROOT / "FLiftExpr.seg").write_text(render_expr())
    (ROOT / "FAnnot.seg").write_text(render_lift())
