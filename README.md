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
  `LeCode`/`LeFunCode`, `Coherent`/`CoherentFun`, `FinMem`/`FinMemAllU`,
  finitary projection `pCode`, monotonicity and compatibility lemmas
  (`LeCode-refl`, `LeCode-trans`, `Comp-down`, `EvalFun-mon-arg`,
  `finMem-upward`, `finMemUCode-Sup`, etc.).
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

- **`Reduction.agda`** — Axioms for contextual reduction (`Red`).
  Postulates: `Red`, `Red-wk`, `red-to-conv`, `Red-refl`, `Red-trans`,
  `Red-beta-expand`, `Red-Pi-inj`, `Red-from-conv`.

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

### Validity and adequacy

- **`Validity.agda`** — Logical relation for validity: `Val`/`EqVal`,
  `ValTy`/`EqValTy`, `ValPi`/`EqValPi`. Transport lemmas
  (`downVal`, `upVal`, `restrictVal`). Postulates for `Red` interaction
  (`Val-Red`, `Val-conv-type`).

- **`Adequacy.agda`** — Two-context adequacy with source-env semantics.
  Several postulates remain (selection-based restructuring in progress).

### Other

- **`bakupRS.agda`** — Backup of an earlier version of `RawSemantics`.

## Technical notes

- **Spartan Agda:** `--without-K --exact-split --type-in-type`
- **U : U** works because `rk UCode = 0` and `FinMem UCode UCode = Top`,
  so self-membership never triggers recursive rank-based calls.
- The step-indexed recursion is driven by finite-element rank, not by
  a universe hierarchy.

## Postulate summary

| File | Postulates |
|------|-----------|
| Basic, Selection, PaperSemantics | 0 |
| RawSyntax, RawSemantics, EvalSubstitution | 0 |
| LemmaForTS | 0 |
| Reduction | 8 (axioms for contextual reduction) |
| TypingSemantics | 0 |
| Validity | ~8 (Red interaction) |
| Adequacy | ~11 (in progress) |
