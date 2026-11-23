#!/usr/bin/env python3
"""Generate AGAT.seg and AForget.seg from the bounded GAT rule declarations."""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = (ROOT / "GAT.seg").read_text()

# One entry per occurrence in the declaration, from premises to conclusion.
# Only the six leaves get extra fields. The generator checks the counts.
ANNOTATIONS = {
    "gs-id": ("G",),
    "gs-eps": ("G",),
    "gs-p": ("G A",),
    "gt-uu": ("G",),
    "gt-el": ("G",),
    "gm-pic": ("G", "(gext G (gel n a))", "G"),
    "gm-uc": ("G", "G"),
    "gm-lf": ("G", "G"),
    "gm-q": ("G A", "G A"),
    "ge-el": ("G",),
    "ge-el-lf": ("G",),
    "ge-el-pic": ("G", "(gext G (gel n a))"),
    "ge-el-uc": ("G", "G"),
    "ge-sb-id": ("G",),
    "ge-uu-sb": ("G", "D"),
    "ge-el-sb": ("G",),
    "gm-epic": ("G", "G", "(gext G (gel n a))", "G"),
    "gm-elf": ("G", "G"),
    "gm-eta": ("G A",) * 4,
    "gm-lf-pic": ("G", "(gext G (gel n a))", "G"),
    "gm-lf-uc": ("G", "G", "G"),
    "gm-lf-lf": ("G", "G"),
    "gm-sb-id": ("G",),
    "gm-pic-sb": ("G", "(gext G (gel n a))", "D"),
    "gm-uc-sb": ("G", "D", "D"),
    "gm-lf-sb": ("G", "D"),
    "gm-q-lift": ("G A", "D (gsb A s)", "D (gsb A s)"),
    "gm-q-sec": ("G A",),
    "gq-idl": ("G",),
    "gq-idr": ("D",),
    "gq-eps": ("G",),
    "gq-lift-id": ("G", "G", "(gext G A)"),
    "gq-p-lift": ("G A", "D (gsb A s)"),
    "gq-p-sec": ("G A", "G"),
    "gq-lift-p-sec-q": ("G A", "G A", "G A", "(gext G A)"),
}

LEAF = re.compile(r"(?<![\w-])(?:guu \w+|guc \w+ \w+|gid|geps|gp|gq)(?![\w-])")
WORD = re.compile(r"[\w'-]+")
PREAMBLE = "level l ;\nopen Base ; open Lib[l] ;"
RAW_LEAVES = {
    "guu": "(G : GA)",
    "guc": "(G : GA)",
    "gid": "(G : GA)",
    "geps": "(G : GA)",
    "gp": "(G A : GA)",
    "gq": "(G A : GA)",
}


def declarations(section):
    """Read constructor names and their declarations, without comments."""
    return re.findall(
        r"^ *(?:\| )?(\w[\w-]*)([^\n]*(?:\n[ ]{6,}[^\n]*)*)",
        re.sub(r"--[^\n]*", "", section),
        re.M,
    )


def block(start, end):
    return SOURCE.split(start, 1)[1].split(end, 1)[0]


RAW = declarations(block("data GE =", ";"))
JUDGEMENTS = declarations(block("data GJ =", ";"))
RULES = declarations(block("data GDer : (J : GJ) -> U l =", ";"))
NAMES = {name for name, _ in RAW + JUDGEMENTS + RULES}


def annotated(text):
    def rename(match):
        name = match[0]
        if name == "GE":
            return "GA"
        if name == "GJ":
            return "GAJ"
        if name == "GDer":
            return "GADer"
        return "a" + name[1:] if name in NAMES else name

    return WORD.sub(rename, text)


def annotate_rule(name, declaration):
    annotations = ANNOTATIONS.get(name, ())
    matches = list(LEAF.finditer(declaration))
    if len(matches) != len(annotations):
        raise ValueError(f"{name} has {len(matches)} leaves and {len(annotations)} annotations")
    for match, context in reversed(list(zip(matches, annotations))):
        # Universe and code leaves are already parenthesized where applied.
        expression = f"{match[0]} {context}"
        if match[0] in RAW_LEAVES:
            expression = f"({expression})"
        declaration = declaration[:match.start()] + expression + declaration[match.end():]
    return annotated(name + declaration).rstrip()


def data(header, entries):
    return header + " =\n    " + "\n  | ".join(entries) + " ;\n"


CONGRUENCES = {
    "ae-uu-cx": (
        "(G H : GA) (n : Nat) (e : GADer (ajeqcx G H)) (nb : LeN n N) :\n"
        "      GADer (ajeqty G (auu n G) (auu n H))",
        "ge-refl (fg G) (guu n) (gt-uu (fg G) n (gpresup (gjeqcx (fg G) (fg H)) re).1 nb)",
    ),
    "am-uc-cx": (
        "(G H : GA) (m n : Nat) (e : GADer (ajeqcx G H)) (lt : LeN (suc m) n) (nb : LeN n N) :\n"
        "      GADer (ajeqtm G (auc m n G) (auc m n H) (auu n G))",
        "gm-refl (fg G) (guc m n) (guu n) (gm-uc (fg G) m n (gpresup (gjeqcx (fg G) (fg H)) re).1 lt nb)",
    ),
    "aq-id-cx": (
        "(G H : GA) (e : GADer (ajeqcx G H)) : GADer (ajeqsub G (aid G) (aid H) G)",
        "gq-refl (fg G) gid (fg G) (gs-id (fg G) (gpresup (gjeqcx (fg G) (fg H)) re).1)",
    ),
    "aq-eps-cx": (
        "(G H : GA) (e : GADer (ajeqcx G H)) : GADer (ajeqsub G (aeps G) (aeps H) anil)",
        "gq-refl (fg G) geps gnil (gs-eps (fg G) (gpresup (gjeqcx (fg G) (fg H)) re).1)",
    ),
    "aq-p-cx": (
        "(G H A B : GA) (e : GADer (ajeqcx G H)) (p : GADer (ajeqty G A B)) :\n"
        "      GADer (ajeqsub (aext G A) (ap G A) (ap H B) G)",
        "gq-refl (gext (fg G) (fg A)) gp (fg G) (gs-p (fg G) (fg A) (gpresup (gjeqty (fg G) (fg A) (fg B)) rp).2.1)",
    ),
    "am-q-cx": (
        "(G H A B : GA) (e : GADer (ajeqcx G H)) (p : GADer (ajeqty G A B)) :\n"
        "      GADer (ajeqtm (aext G A) (aq G A) (aq H B) (asb A (ap G A)))",
        "gm-refl (gext (fg G) (fg A)) gq (gsb (fg A) gp) (gm-q (fg G) (fg A) (gpresup (gjeqty (fg G) (fg A) (fg B)) rp).2.1)",
    ),
}


def fields(declaration):
    result = []
    depth = 0
    for position, char in enumerate(declaration):
        if char == "(":
            if depth == 0:
                start = position + 1
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                names, kind = declaration[start:position].split(":", 1)
                result.extend((name, kind.strip()) for name in names.split())
        elif char == ":" and depth == 0:
            break
    return result


def variables(arguments):
    return "".join(" " + name for name, _ in arguments)


def forget_case(name, declaration):
    args = fields(declaration)
    recursive = "".join(" r" + field for field, kind in args if kind.startswith("GDer"))
    induction = " |" + recursive if recursive else ""
    body = "".join(
        f" (fg {field})" if kind == "GE" else f" r{field}" if kind.startswith("GDer") else f" {field}"
        for field, kind in args
    )
    return f"  {annotated(name)}{variables(args)}{induction} -> {name}{body}"


def split(signature, cases):
    return signature + " = split {\n" + " ;\n".join(cases) + " } ;\n"


def generate_agat():
    raw = [
        annotated((name + decl).rstrip()) + (" " + RAW_LEAVES[name] if name in RAW_LEAVES else "")
        for name, decl in RAW
    ]
    rules = [annotate_rule(name, decl) for name, decl in RULES]
    rules.extend(f"{name} {decl}" for name, (decl, _) in CONGRUENCES.items())
    bound_cases = []
    for name, decl in RULES:
        args = variables(fields(decl))
        rhs = {"gt-uu": "nb", "gt-cx": "r2"}.get(name, "tt")
        induction = " | r0 r1 r2" if name == "gt-cx" else ""
        bound_cases.append(f"  {annotated(name)}{args}{induction} -> {rhs}")
    bound_cases.extend(f"  {name}{variables(fields(decl))} -> tt" for name, (decl, _) in CONGRUENCES.items())
    raw_bound = [
        f"  {annotated(name)}{variables(fields(decl))}"
        + (" G A" if name in ("gp", "gq") else " G" if name in RAW_LEAVES else "")
        + (" -> LeN n N" if name == "guu" else " -> Top")
        for name, decl in RAW
    ]
    judgement_bound = [
        f"  {annotated(name)}{variables(fields(decl))}"
        + (" -> a-universe-level A" if name == "gjty" else " -> Top")
        for name, decl in JUDGEMENTS
    ]
    return (
        "-- Generated by gen_annot.py from GAT.seg and the rule shapes in PLAN-ANNOT-A0.md.\n"
        "-- The six leaves carry context arguments. All other constructors mirror GAT.\n\n"
        + PREAMBLE
        + "\n\n"
        + data("data GA", raw)
        + "\n"
        + data("data GAJ", [annotated(name + decl).rstrip() for name, decl in JUDGEMENTS])
        + "\n"
        + data("data GADer : (J : GAJ) -> U l", rules)
        + "\n-- Recover the bound even when the annotation has been transported.\n"
        + split("a-universe-level : GA -> U l", raw_bound)
        + split("a-universe-bound-at : GAJ -> U l", judgement_bound)
        + split("a-universe-bound-J : (J : GAJ) -> GADer J -> a-universe-bound-at J", bound_cases)
        + "a-universe-bound (G X : GA) (n : Nat) (h : GADer (ajty G (auu n X))) : LeN n N =\n"
        + "  a-universe-bound-J (ajty G (auu n X)) h ;\n"
    )


def generate_forget():
    raw = []
    for name, decl in RAW:
        args = fields(decl)
        recursive = [field for field, kind in args if kind == "GE"]
        induction = "".join(" r" + field for field in recursive)
        extras = " G A" if name in ("gp", "gq") else " G" if name in RAW_LEAVES else ""
        body = "".join(" " + ("r" if field in recursive else "") + field for field, _ in args)
        raw.append(f"  {annotated(name)}{variables(args)}{extras}" + (f" |{induction}" if induction else "") + f" -> {name}{body}")
    judgements = [
        f"  {annotated(name)}{variables(fields(decl))} -> {name}"
        + "".join(f" (fg {field})" for field, _ in fields(decl))
        for name, decl in JUDGEMENTS
    ]
    rules = [forget_case(name, decl) for name, decl in RULES]
    for name, (decl, body) in CONGRUENCES.items():
        args = fields(decl)
        induction = "".join(" r" + field for field, kind in args if kind.startswith("GADer"))
        rules.append(f"  {name}{variables(args)} |{induction} ->\n    {body}")
    return (
        "-- Generated by gen_annot.py. Forget context annotations and preserve derivability.\n\n"
        + PREAMBLE + " open GAT[l] ; open GPresup[l] ; open AGAT[l] ;\n\n"
        + split("fg : GA -> GE", raw) + "\n"
        + split("fgJ : GAJ -> GJ", judgements) + "\n"
        + split("forget : (J : GAJ) -> GADer J -> GDer (fgJ J)", rules)
    )


if __name__ == "__main__":
    for filename, render in (("AGAT.seg", generate_agat), ("AForget.seg", generate_forget)):
        (ROOT / filename).write_text(render())
