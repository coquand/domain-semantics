# Π-injectivity and subject reduction for `U : U`, by domain theory

An Agda formalisation of a dependent type theory with a universe `U : U` and
dependent function (`Π`) types, and a **domain-theoretic** proof of two
syntactic metatheorems about it:

- **Π-injectivity** — if `Γ ⊢ Π(x:A₀)B₀ = Π(x:A₁)B₁ : U` then
  `Γ ⊢ A₀ = A₁ : U` and `Γ, x:A₀ ⊢ B₀ = B₁ : U`;
- **subject reduction** — if `Γ ⊢ M : A` and `M ⤳₁ N` then `Γ ⊢ N : A`.

Because the theory is type-in-type (`U : U`) it is logically inconsistent and
has no normalisation, so the usual syntactic route (confluence + normal forms)
is unavailable. Instead the results are obtained **semantically**: we build a
domain-theoretic model (finite elements of a Scott domain), define a logical
relation linking the model to the syntax, prove **adequacy** (every well-typed
term is valid), and read both metatheorems off the logical relation by
evaluating at the bottom environment. This is the method of Coquand–Huber,
*An adequacy theorem for dependent type theory*, Arch. Math. Logic 57 (2018).

The development is machine-checked with Agda (`--without-K --exact-split`),
**with no postulates, no holes, and no `TERMINATING` / `NO_POSITIVITY`
pragmas** — every definition passes Agda's termination and positivity checkers
as written. The information order `u ≤ v` and the semantic membership `u : a`
(and the validity relation) are built by **stage stratification** — a family of
relations indexed by a stage `n`, each obtained from the one below, collapsed by
a stability lemma — so the kernel is structurally well-founded by construction
and needs no pragma to convince the checker. A self-contained mathematical
write-up is in [`pi-u-rules.tex`](pi-u-rules.tex) (built:
[`pi-u-rules.pdf`](pi-u-rules.pdf)).

This `MIN/` development is the current, complete one. (The repository also
contains an element-level identity type, and a self-contained formalisation of
Colson's ultimate-obstination theorem; see the end.)

## Main results — where they are proved

| Result | File | Name |
|---|---|---|
| **Π-injectivity** | [`MIN/PiInjectivity.agda`](MIN/PiInjectivity.agda) | `piInjectivity`, `piConv` |
| **Subject reduction** | [`MIN/SubjectReduction.agda`](MIN/SubjectReduction.agda) | `subject-red1` |

Both are corollaries of **adequacy**, proved in
[`MIN/AdequacyValue.agda`](MIN/AdequacyValue.agda):

- `adequacySub2`  — `Γ ⊢ M : A` ⟹ `Val2 …` (typing implies validity);
- `adequacyEqSub2` — `Γ ⊢ M = N : A` ⟹ `EqVal2 …` (conversion implies equality validity).

`piConv` runs `adequacyEqSub2` at the bottom environment and reads the head
reduction and component conversions out of the resulting `EqValTyPi`; subject
reduction inverts `Lam` typing through `piInjectivity` in the β case.

## Where everything lives (`MIN/`)

**Syntax and rules**
- `RawSyntax.agda` — terms (`Var, U, Pi, Lam, App`) and substitution.
- `TypingRules.agda` — typing `HasType` and conversion `ConvTm`.
- `Reduction.agda` — head reduction `HeadRed1` / `Red`.

**Domain model (finite elements)** — the order `u ≤ v` and membership `u : a`
- `PaperOrder.agda` — order `≤` (`LeCode`), compatibility `Comp`, `Coherent`,
  supremum `Sup`, evaluation `EvalFun`. A thin re-export of the stratified
  construction in `LeqStage{,Comp,Props,Props2,Stable,Order,Bridge,Interface,Eval2}.agda`.
- `PaperTyping.agda` — membership `FinMem` (`u : a`) with its unfolding,
  projection, and closure/monotonicity properties. A thin re-export of the
  stratified construction in `FinMemStage{,Stable,Shift,Unfold,Props}.agda`.
- `PaperSemantics.agda` — re-exports the two above.

**Logical relation (validity)** — stage-stratified
- `Validity.agda`, `ValidityStratified.agda`, `ValidityMono.agda`,
  `ValidityProps.agda`, `ValidityStability.agda`, `ValidityLevels.agda`,
  `ValidityHeadRed.agda`, `ValidityPublic.agda` — the predicates
  `Val2 / ValTy2 / EqVal2 / EqValTy2` and their properties (monotonicity,
  supremum, stability, …).
- `AdequacyRecords.agda` — the validity record types and their builders.

**Adequacy**
- `AdequacyValue.agda` — the two adequacy theorems above (the mutual driver).
- `AdequacyBundle.agda` and `Adequacy{VE,Pi,Lam,App,ArgCore,FunCore,AppInj,Beta,Funext,Cases,Helpers,HeadRed}.agda`
  — per-rule combinators feeding the driver.

**Supporting infrastructure**
- `Basic.agda` (prelude), `RawSemantics.agda` (evaluation `EvalRel`,
  environments), `Selection.agda`, `EvalSubstitution.agda`,
  `SubstitutionLemma.agda`, `LemmaForTS.agda`, `TypingSemantics.agda`
  (`convSound'`), `Rank.agda`, `SelectionRank.agda`.

## Building

Requires Agda `2.9.0` (no external library). Type-check the two entry points:

```sh
agda --without-K MIN/PiInjectivity.agda
agda --without-K MIN/SubjectReduction.agda
```

Type-checking `MIN/PiInjectivity.agda` exercises the whole cone (model,
logical relation, adequacy, injectivity); `MIN/SubjectReduction.agda` checks
the remaining subject-reduction layer on top of it. A clean rebuild of the
subject-reduction entry point covers 54 source files and finishes with no
errors, no warnings, and no termination/positivity pragmas anywhere in the
cone.

## Also in this repository: the element-level identity type (`ID/`)

The same method is extended with Martin-Löf's element-level identity type
`Id A a b`, its constructor `Ref`, and the fully-dependent eliminator `J`
(with motive `C : (x y : A) → Id A x y → U` and base
`d : (x : A) → C x x (Ref x)`). It lives in the [`ID/`](ID/) subdirectory
and is machine-checked with no postulates, no holes, and no
termination/positivity pragmas.

| Result | Entry point | Name |
|---|---|---|
| Adequacy | [`ID/Adequacy/Value.agda`](ID/Adequacy/Value.agda) | `adequacySub2`, `adequacyEqSub2` |
| Π-injectivity | [`ID/PiInjectivity.agda`](ID/PiInjectivity.agda) | `piInjectivity` |
| **Id-injectivity** | [`ID/IdInjectivity.agda`](ID/IdInjectivity.agda) | `idInjectivity` |
| **Subject reduction** | [`ID/SubjectReduction.agda`](ID/SubjectReduction.agda) | `subject-red1` |

The `J` case of adequacy is the based-J driver
([`ID/Adequacy/JApp.agda`](ID/Adequacy/JApp.agda),
[`JAppCross.agda`](ID/Adequacy/JAppCross.agda),
[`JAppCongr.agda`](ID/Adequacy/JAppCongr.agda)). A short write-up of the
identity-type rules together with the injectivity and subject-reduction
statements is [`ID/id-rules.tex`](ID/id-rules.tex) (built:
[`ID/id-rules.pdf`](ID/id-rules.pdf)). Type-check the two metatheorem entry
points with, e.g.,

```sh
agda --without-K ID/IdInjectivity.agda
agda --without-K ID/SubjectReduction.agda
```

## Also in this repository: Colson's ultimate obstination (`OBSTINATION/`)

A self-contained Agda formalisation of Thierry Coquand's note *Une preuve
directe du Théorème d'Ultime Obstination* ([`min1.pdf`](min1.pdf)) — a direct
constructive proof of Colson's 1989 ultimate-obstination theorem, with the
corollary that **denotations of primitive-recursive terms are computable**. It
is independent of the `MIN/` machinery: the domain is just the lazy naturals
(`Sᵏ(0)`, `Sᵏ(⊥)`, `S^ω(⊥)`), with no universe, codes, or logical relation.
Every module is `--safe --without-K --exact-split` with no postulates, holes,
or pragmas. Full details in [`OBSTINATION/README.md`](OBSTINATION/README.md).

| Result | Entry point | Name |
|---|---|---|
| **Ultimate obstination (Proposition 1)** | [`OBSTINATION/Prop1.agda`](OBSTINATION/Prop1.agda) | `prop1` |
| Computability of the extension | [`OBSTINATION/Computable.agda`](OBSTINATION/Computable.agda) | `fhat`, `fhat-diag` |
| **`min` at `S^ω(⊥)`** | [`OBSTINATION/PredMin.agda`](OBSTINATION/PredMin.agda) | `min-inf` |
| **`MP1` for every primitive recursive term** | [`OBSTINATION/TrTermMP1.agda`](OBSTINATION/TrTermMP1.agda) | `traceOf-MP1np` |
| **The value at `(S^ω⊥, …, S^ω⊥)`** | [`OBSTINATION/PRInfMP1.agda`](OBSTINATION/PRInfMP1.agda) | `prValMP`, `prValMP-lub` |

`prop1 : (p : PR)(A : Tup) → Wf p (length A) → UO (evalF p) A` proves ultimate
obstination by induction on the primitive-recursive term `p`; from the witness
one reads off the value of the Scott-continuous extension `f̂` at any point
(`uoValue`), so `f̂` is computable — including at the infinite diagonal
`(S^ω⊥, …, S^ω⊥)`. Strikingly, a primitive-recursive `min` returns `⊥` (not
`S^ω⊥`) on `(S^ω⊥, S^ω⊥)` — the obstination made concrete and machine-checked.
A high-level write-up is
[`OBSTINATION/obstination.tex`](OBSTINATION/obstination.tex) (built:
[`OBSTINATION/obstination.pdf`](OBSTINATION/obstination.pdf)). Type-check the
headline results with:

```sh
agda --safe --without-K --exact-split OBSTINATION/Prop1.agda
agda --safe --without-K --exact-split OBSTINATION/PredMin.agda
```

### The trace, and the value at the infinite point

A second, independent route to the same computability result goes through the
**trace** of a term — the record of which variable the computation demands at
each step and of what it has produced. This is the notion of trace of an email
from Coquand to Colson of 1991 (it is *not* R. David's notion of trace, which
labels each cell of the value with the argument cells used to produce it); the
difference is spelled out in §2.2 of the write-up.

- [`OBSTINATION/TrTermMP1.agda`](OBSTINATION/TrTermMP1.agda) —
  `traceOf-MP1np : (q : PR)(n : Nat) → Wf q n → MP1T n (traceOf q n wf)`: the
  trace of **every** primitive recursive term satisfies the invariant `MP1`
  (the demand is eventually constant, and the value sequence has a verdict).
  Proposition 1 is *not* used.
- [`OBSTINATION/PRInfMP1.agda`](OBSTINATION/PRInfMP1.agda) — `prValMP` computes
  `f(S^ω⊥, …, S^ω⊥)` from `MP1` alone, and `prValMP-lub` proves it is the least
  upper bound of the diagonal chain `f(S^m⊥, …, S^m⊥)`.

The write-up is
[`OBSTINATION/prinf.tex`](OBSTINATION/prinf.tex) (built:
**[`OBSTINATION/prinf.pdf`](OBSTINATION/prinf.pdf)**); its last section asks
what survives under mutual recursion. Type-check with:

```sh
agda --safe --without-K --exact-split OBSTINATION/TrTermMP1.agda
agda --safe --without-K --exact-split OBSTINATION/PRInfMP1.agda
```
