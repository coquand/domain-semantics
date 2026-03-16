# Adequacy for Dependent Type Theory with U : U

Agda formalisation of the logical-relation core of the adequacy proof
for dependent type theory, adapted to a single-universe setting (U : U).

Based on:

> Coquand & Huber, "An Adequacy Theorem for Dependent Type Theory",
> Archive for Mathematical Logic, 2018.

## Files

### Foundation

- **`Basic.agda`** — Base types (`Top`, `Empty`, `Nat`, `Pair`, `Sigma`),
  natural number operations (`max`, `Le`, `Le-refl`), lists, and
  finite elements (`FinEl`: `Bot`, `UCode`, `FunEl`, `PiCode`) with rank `rk`.
  **0 postulates.**

- **`Selection.agda`** — `Edge`, `EdgeIn`, `Selection` (compatible
  sub-multisets), `CoherentWith`, `CoherentFun-edge-key`,
  `singleton-selection`, and lookup lemmas.
  **0 postulates.**

### Domain model

- **`PaperSemantics.agda`** — Trusted kernel. Sup-based evaluation
  `EvalFun`, decidable ordering `leFinEl`/`leFun`, propositional ordering
  `LeCode`/`LeFunCode`, `Coherent`/`CoherentFun`/`CoherentFunTail`,
  `FinMem`/`FinMemAllU`, finitary projection `pCode`, monotonicity and
  compatibility lemmas (`LeCode-refl`, `LeCode-trans`, `Comp-down`,
  `EvalFun-mon-arg`, `finMem-upward`, `finMemUCode-Sup`, etc.).
  Note: `Coherent (PiCode a f)` uses `CoherentFunTail f` (not
  `CoherentFun f`), allowing `PiCode a nil` to be coherent.
  **0 postulates.**

### Syntax and raw semantics

- **`RawSyntax.agda`** — Expressions (`Expr`: `Var`, `U`, `Pi`, `Lam`, `App`),
  de Bruijn indices (`Fin`), substitution (`subst1`), weakening (`wkExpr`),
  renaming.
  **0 postulates.**

- **`RawSemantics.agda`** — Selection-based `EvalRel` with coherence
  bundling. One-edge form for `App`. `Pi-edgewise`, `Lam-edgewise`,
  `EvalRel-coh`, `EvalRel-mon-env`, `EvalRel-Comp`, `EvalRel-Comp-ext`,
  `EvalRel-Sup`, `EvalRel-down-App`.
  **0 postulates.**

- **`EvalSubstitution.agda`** — `EvalRel-ren`, `EvalRel-wk`, `SubRel`,
  `EvalRel-subst` (general substitution theorem),
  `EvalRel-subst1-backward`.
  **0 postulates.**

### Typing

- **`TypingRules.agda`** — `Ctx`, `HasType`, `ConvTm`, `WfCtx`.
  `ty-App`/`conv-App-fun`/`conv-App-arg`/`conv-funext` carry
  `HasType G A U` premise.

- **`Reduction.agda`** — Contextual reduction (`Red`, `HeadRed`).
  `HeadRed` is a data type; `Red` wraps it with phantom context/type.
  `Red-hr` extracts `HeadRed` from `Red`.
  **0 postulates.**

### Semantic invariants and lemmas

- **`LemmaForTS.agda`** — Key intermediate lemmas for the typing
  semantics proof. Defines `Fits` (well-typed environments), `Typed`,
  `InvTyp`, `InvConv`. Contains:
  - `Lam-L1` — Lambda inversion with typed keys
  - `Pi-L1` — Pi inversion with typed keys
  - `InvTyp-Lam` — Lam case of InvTyp
  - `InvTyp-Pi` — Pi case of InvTyp
  - `InvTyp-App` — App case of InvTyp
  - `InvConv-beta` — Beta conversion
  - `InvConv-funext` — Function extensionality conversion
  - `InvConv-App-fun`, `InvConv-App-arg` — Congruence conversions
  - Helper infrastructure: `mapEdges`, `replaceKeys`, `replaceVals`,
    `replaceKeys-selection-body`, `EvalFun-edge-le`.
  **0 postulates.**

- **`TypingSemantics.agda`** — `theorem1` (typing soundness) and
  `convSound` (soundness of conversion). Imports definitions and
  lemmas from `LemmaForTS`; all cases proved by delegation.
  **0 postulates.**

- **`SubstitutionLemma.agda`** — Renaming, substitution, presupposition,
  context conversion for the typing judgement. `typing-ConvTm` extracts
  `HasType` from `ConvTm`.
  **0 postulates.**

### Validity and adequacy

- **`Validity.agda`** — Logical relation for validity: `Val`/`EqVal`,
  `ValTy`/`EqValTy`, `ValPi`/`EqValPi`. Transport lemmas
  (`downVal`, `upVal`, `restrictVal`).
  **0 postulates.**

- **`Adequacy.agda`** — Two-context adequacy with source-env semantics.
  **0 postulates.**

- **`Validity2.agda`** — Bundled logical relation `Val2`/`EqVal2` with
  `Top` at leaves. `ValTyPi2` stores `Red` (head reduction), enabling
  extraction of `HeadRed` from `Val2` at `PiCode`.
  **0 postulates.**

- **`Adequacy2.agda`** — Bundled adequacy producing `Val2`/`EqVal2`.
  **7 postulates** (Lam, App, beta, Pi, funext, App-fun, App-arg).

### Pi injectivity

- **`PiInjectivity.agda`** — Corollary 6, part 1 (paper p.661):
  from `ConvTm G A₀ (Pi B₁ F₁) U`, extract `HeadRed A₀ (Pi B₀ F₀)`.
  Strategy: `botEnv` + `PiCode Bot nil` + `convSound'` + `adequacySub2`
  + `Val2` extraction. Parts 2–3 (domain/codomain `ConvTm`) require
  `HasType`/`ConvTm` at leaves (future work).
  **0 postulates.**

## Technical notes

- **Spartan Agda:** `--without-K --exact-split` (no `--type-in-type`)
- **U : U** works because `rk UCode = 0` and `FinMem UCode UCode = Top`,
  so self-membership never triggers recursive rank-based calls.
- The step-indexed recursion is driven by finite-element rank, not by
  a universe hierarchy.
- The development does not require `--type-in-type`; all files compile
  with standard universe checking.

## Postulate summary

| File | Postulates |
|------|-----------|
| Basic, Selection, PaperSemantics | 0 |
| RawSyntax, RawSemantics, EvalSubstitution | 0 |
| Reduction | 0 |
| LemmaForTS, TypingSemantics | 0 |
| SubstitutionLemma | 0 |
| Validity, Adequacy | 0 |
| Validity2 | 0 |
| Adequacy2 | 7 (Lam, App, beta, Pi, funext, App-fun, App-arg) |
| PiInjectivity | 0 |
