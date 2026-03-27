# Adequacy for Dependent Type Theory with U : U and Prop : U

Agda formalisation of the logical-relation core of the adequacy proof
for dependent type theory, adapted to a single-universe setting (U : U).

Based on:

> Coquand & Huber, "An Adequacy Theorem for Dependent Type Theory",
> Archive for Mathematical Logic, 2018.

## Files

### Foundation

- **`Basic.agda`** — Base types (`Top`, `Empty`, `Nat`, `Pair`, `Sigma`),
  natural number operations (`max`, `Le`, `Le-refl`), lists, and
  finite elements (`FinEl`: `Bot`, `UCode`, `PropCode`, `FunEl`, `PiCode`) with rank `rk`.
  **0 postulates.**

- **`Selection.agda`** — `Edge`, `EdgeIn`, `Selection` (compatible
  sub-multisets), `CoherentWith`, `CoherentFun-edge-key`,
  `singleton-selection`, and lookup lemmas.
  **0 postulates.**

### Domain model

- **`PaperSemantics.agda`** — Trusted kernel. Sup-based evaluation
  `EvalFun`, decidable ordering `leFinEl`/`leFun`, propositional ordering
  `LeCode`/`LeFunCode`, `Coherent`/`CoherentFun`/`CoherentFunTail`,
  `FinMem`/`FinMemAllU`/`FinMemAllProp`, monotonicity and
  compatibility lemmas (`LeCode-refl`, `LeCode-trans`, `Comp-down`,
  `EvalFun-mon-arg`, `finMem-upward`, `finMemUCode-Sup`, etc.).
  Prop-specific lemmas: `EvalFun-in-PropCode`, `FinMem-Prop-Bot`
  (inhabitants of Prop-typed codes are Bot), `FinMem-Prop-to-U`
  (Prop subtyping), `LeCode-PropCode-cases`.
  Note: `Coherent (PiCode a f)` uses `CoherentFunTail f` (not
  `CoherentFun f`), allowing `PiCode a nil` to be coherent.
  **0 postulates.**

### Syntax and raw semantics

- **`RawSyntax.agda`** — Expressions (`Expr`: `Var`, `U`, `Prop`, `Pi`, `Lam`, `App`),
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
  Includes `ty-Prop`, `ty-Prop-U` (Prop subtyping), `ty-Pi-Prop`
  (Pi in Prop), and `conv-Prop` (proof-irrelevance).
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
  - `InvTyp-Pi-Prop` — Pi-Prop case of InvTyp (codomain in PropCode)
  - `InvTyp-App` — App case of InvTyp
  - `InvConv-beta` — Beta conversion
  - `InvConv-funext` — Function extensionality conversion
  - `InvConv-App-fun`, `InvConv-App-arg` — Congruence conversions
  - Helper infrastructure: `mapEdges`, `replaceKeys`, `replaceVals`,
    `replaceKeys-selection-body`, `EvalFun-edge-le`.
  **0 postulates.**

- **`TypingSemantics.agda`** — `theorem1` (typing soundness) and
  `convSound` (soundness of conversion). Includes the proof-irrelevance
  case (`conv-Prop`): if `A : Prop` and `M : A`, then all finite
  approximations of `M` are `Bot`, so `EvalRel M rho u` implies `u = Bot`.
  Uses `Prop-collapse` and `FinMem-Prop-Bot`.
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

- **`Validity2.agda`** — Bundled logical relation `Val2`/`EqVal2` with
  `Top` at leaves. `ValTyPi2` stores `Red` (head reduction),
  `HasType` for domain/codomain, and `ConvTm` for domain/codomain
  equality in `EqValTyPi2`.
  **0 postulates.**

- **`Adequacy2.agda`** — Bundled adequacy producing `Val2`/`EqVal2`.
  Uses the paper's two-substitution approach (Theorem 2, p.660) with
  `adequacyConvSub2` for cross-substitution equality.
  **0 postulates.**

### Pi injectivity

- **`PiInjectivity.agda`** — Corollary 6 (paper p.661), full Pi injectivity:
  - `piHeadRed`: from `ConvTm G A₀ (Pi B₁ F₁) U`, extract
    `HeadRed A₀ (Pi B₀ F₀)` (part 1).
  - `piConv`: additionally extract `ConvTm G B₀ B₁ U` (part 2)
    and `ConvTm (extend G B₀) F₀ F₁ U` (part 3).
  - `piInjectivity`: from `ConvTm G (Pi A₀ B₀) (Pi A₁ B₁) U`,
    extract `ConvTm G A₀ A₁ U` and `ConvTm (extend G A₀) B₀ B₁ U`.
  Strategy: `botEnv` + `PiCode Bot nil` + `convSound'` +
  `adequacyEqSub2` + `EqValTyPi2` extraction + `Red-unique-Pi`.
  **0 postulates.**

### Subject reduction

- **`SubjectReduction.agda`** — Subject reduction for single-step
  head reduction:
  - `subject-red1`: `HasType G M A → HeadRed1 M N → HasType G N A`.
  - `ty-Lam-body`: Lam body extraction through conversion. Given
    `HasType G (Lam A M) T` and `ConvTm G T (Pi A₀ B₀) U`, produce
    `HasType (extend G A₀) M B₀`. Uses `piInjectivity` for the
    `ty-Lam` case and `piConv` to eliminate the `ty-Prop-U` case
    (conversion from `U` to a Pi type is impossible since `U` is
    a head normal form distinct from `Pi`).
  **0 postulates.**

## Documentation

- **`rules.tex`** / **`rules.pdf`** — LaTeX presentation of the typing
  and conversion rules, head reduction, and the full Pi injectivity
  theorem (Corollary 6, parts 1–3 and the Pi–Pi corollary) with
  proof outline.

- **`sigma-validity.tex`** / **`sigma-validity.pdf`** — Informal
  description of how the validity proof extends to Sigma types.
  Documents the uniform definition using code projections
  ($w.1$, $w.2$), the type-equality transport lemma, and the
  4-step head-reduction transport argument (IH on first projection,
  edge function for type equality, IH on second projection,
  transport). Explains why the head-reduction lemma must return
  EqVal (not just Val): the equality edge is needed to bridge
  $B[M'.1]$ and $B[M.1]$.

## Technical notes

- **Spartan Agda:** `--without-K --exact-split` (no `--type-in-type`)
- **Sup simplification:** Cross-constructor `Sup` returns `Bot`
  (e.g. `Sup UCode (FunEl _) = Sup PropCode UCode = Bot`),
  matching the fact that cross-constructor `Comp` is `Empty`.
- **U : U** works because `rk UCode = 0` and `FinMem UCode UCode = Top`,
  so self-membership never triggers recursive rank-based calls.
- **Prop : U** with proof-irrelevance. `PropCode` is incompatible with
  `UCode` in the ordering but `FinMem PropCode UCode = Top`. The key
  semantic lemma `FinMem-Prop-Bot` shows that inhabitants of Prop-typed
  codes collapse to `Bot`, validating proof-irrelevance.
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
| Validity | 0 |
| Validity2 | 0 |
| Adequacy2 | 0 |
| PiInjectivity | 0 |
| SubjectReduction | 0 |
