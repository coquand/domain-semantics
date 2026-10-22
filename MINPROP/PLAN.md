# MINPROP — Π + U + Prop ⊆ U with definitional proof irrelevance, pragma-free

Goal: port the Prop extension of commit `392a0bd` (2026-03-25; old kernel, 8 files
with TERMINATING / NO_POSITIVITY_CHECK) onto MIN/'s stratified, pragma-free kernel.

Acceptance:
`~/.cabal/bin/agda-2.9.0 --without-K MINPROP/PiInjectivity.agda` and
`MINPROP/SubjectReduction.agda` exit 0; no `postulate`, no `{!`, no
TERMINATING / NON_TERMINATING / NO_POSITIVITY_CHECK / REWRITE anywhere in MINPROP/;
each file < 20s.

## 0. The object theory (fixed before starting)

These are exactly the Prop rules of `SigmaProp/TypingRulesSigma.agda`, with Σ removed.

| rule | statement |
|---|---|
| `ty-Prop`      | `G wf  ⊢  Prop : U` |
| `ty-Prop-U`    | `A : Prop  ⊢  A : U`   (Prop ⊆ U, cumulativity) |
| `ty-Pi-Prop`   | `A : U,  G.A ⊢ B : Prop  ⊢  Π A B : Prop`   (impredicative: A may be Prop or U) |
| `conv-Prop`    | `A : Prop, M : A, N : A  ⊢  M = N : A`   (definitional proof irrelevance) |
| `conv-Prop-U`  | `M = N : Prop  ⊢  M = N : U` |
| `conv-Pi-Prop` | `A = A' : U,  B = B' : Prop  ⊢  Π A B = Π A' B' : Prop` |

`Prop : U` is the only typing rule for Prop; there is no `Prop : Prop`.
- MIN/ already has `U : U`, so the theory is inconsistent (Girard). That is
  irrelevant here: adequacy, Π-injectivity and subject reduction do not need
  consistency.
- Impredicativity adds nothing new: the domain already handles Π with
  domain `U`.

Sanity checks on the rules:
- `conv-Prop` can never identify two *types*. A type's type is `U` or `Prop`, and
  neither is a Prop: semantically, `UCode ∉ PropCode` and `PropCode ∉ PropCode`.
  So Π-injectivity cannot be broken by irrelevance.
- Cumulativity puts `A : U` through `ty-Prop-U`. Inverting `Lam : T`
  therefore also needs the no-confusion fact `Prop ≢ Π A B`, which comes from
  adequacy (`PropCode` and `PiCode` are distinct codes).

## 1. Semantic design (from the old proof, checked against MIN's kernel)

- `FinEl` gets a new atom `PropCode`, with `RANK PropCode = 0`. Order:
  - `PropCode ≤ PropCode` only;
  - `Comp` and `Sup` behave as for `UCode`.
- Membership (staged `buildMemStage`). The swap expands to `Bot ∈ PropCode`.
  - `PropCode ∈ UCode`
  - `u ∈ PropCode` iff
    - `u = Bot` (a neutral proposition), or
    - `u = PiCode a f` with `a ∈ U`, `AllProp f a` and `CoherentFunTail f`.
  - `AllProp` is a new structural mutual component, the same shape as
    `finMemAllU`: every edge has its key in `a` and its value in `PropCode`. All its
    recursion drops to the predecessor bundle, so foetus accepts it.
- **Collapse lemma** (the heart of irrelevance):
  `u ∈ a → a ≤ a' → a' ∈ PropCode → u ≡ Bot`.
  - The old proof is `Prop-collapse`, which uses `CFTcons.val-nbot`: a coherent
    function's edge values are non-Bot.
  - `val-nbot` exists in MIN (`Domain/OrderStage.agda:129`), so the argument carries over.
- Soundness: `conv-Prop` is sound because `InvConv` asks for `EvalRel M ⇔ EvalRel N`.
  By `InvTyp` and the collapse, every approximant of a proof is `Bot`, and
  `EvalRel-bot` gives `EvalRel N rho Bot`.
- Validity: `Val2`/`EqVal2` at `a = PropCode` mirror the `UCode` (type-level)
  clauses. At a Prop *code* the term-level relation is trivial at `u = Bot`.
  (PropCode, UCode) must be **informative**, not `Top`: see memory
  `project_propcode_ucode_fix`, since `ty-conv` needs it.
- Precedent: CAST/ added the code `IdCode`, which is proof-irrelevant and whose only
  member is Bot, to this same staged kernel without pragmas.

## 2. Phases, with feasibility gates (stop and report at a failed gate)

**P0 Setup**
- Copy MIN/'s PiInjectivity + SubjectReduction cone into MINPROP/, renaming
  `MIN.` → `MINPROP.`.
- Leave out: OLD/, RankInterp*, RankCouple, RankSandwich*, unless they turn out
  to be in the cone; also Confluence (optional later).
- Baseline compile, with timings per file.

**P1 Kernel (GATE 1)** — `Domain/*`
1. `Basic`: `PropCode`; `Order*`: the LeCode/Comp/Sup/leFinEl clauses. These are mechanical.
2. `MemStage`: PropCode clauses and `finMemAllProp'`. Then the
   `MemUnfold`/`MemStable`/`MemShift`/`MemProps` accessors and stability for the new
   clauses, and the `Membership` iso accessors (`finMem-propU-*`).
3. New lemmas:
   - `Prop⊆U` (`u ∈ PropCode → u ∈ UCode`; also `AllProp → AllU`);
   - closure of PropCode under compatible Sup;
   - `EvalFun-in-PropCode`;
   - **collapse**.

   **GATE 1 = collapse proved in the staged kernel.** This is the real
   feasibility point. It is the one place where staging could get in the way, through
   EvalFun monotonicity and the sup-closure at stage n.

**P2 Syntax** — `Raw`: `Prop`; then `Substitution`, `Typing` (the 6 rules above),
`Reduction` (`Prop` is a whnf and nothing reduces it).

**P3 Model (GATE 2)** — `Eval` (`EvalRel Prop` = `≤ PropCode`), `Selection`,
`EvalSubstitution`, `SoundnessLemmas`/`Soundness`:
- `InvTyp` for ty-Prop, ty-Prop-U and ty-Pi-Prop;
- `InvConv` for conv-Prop (via collapse), conv-Prop-U and conv-Pi-Prop.

**GATE 2 = theorem1 + convSound complete.**

**P4 Validity** — `Core` (Val2/EqVal2/ValTy2 PropCode clauses, with the informative
(PropCode, UCode) bundling), then `Mono`, `Props`, `HeadRed`, `Stability`, `Levels`,
`Stratified`, `Public`.

**P5 Adequacy** — new-rule cases plus PropCode branches in the existing case splits
(`Bundle`, `Cases`, `Value`, `VE`, `Pi`, `Lam`, `App`, …). conv-Prop is closed by
collapse plus `EqVal2-Bot`, as in the old `Adequacy2.agda:926`.

**P6 (GATE 3)**
- `PiInjectivity`: unchanged statement, re-checked.
- `SubjectReduction`: port the cumulativity handling from
  `SigmaProp/SubjectReduction5.agda`, adding the `Prop ≢ Π` no-confusion lemma.
- Final greps; per-file timings.

## 3. Risks

- **R1 Volume.** Every exhaustive FinEl match grows from 4 to 5 constructors. MIN/
  has about 1500 `UCode` mentions in 25k lines. This is mechanical, and CAST/ shows
  the same scale is manageable. Mitigation: catch-all clauses where `--exact-split`
  allows them.
- **R2 Compile time.** The big files (`SoundnessLemmas` 1.8k lines, `Bundle` 1.4k,
  `Props` 1.4k, `Mono` 1.1k) may go over 20s. Mitigation: split files, use
  `opaque`, and pass `_` arguments (memory `feedback_agda_perf_metas_copies`).
- **R3 Staging.** `AllProp` at stage n must commute with stability and shift exactly
  as `AllU` does. This is expected (same shape), but it is only confirmed at GATE 1.
- **R4 Cumulativity in inversion lemmas.** Any MIN/ lemma that inverts
  `HasType G X U` now also meets `ty-Prop-U`. Each such lemma gets one extra
  case, which goes through the Prop inversion.

## 4. Status log

- 2026-10-21 (later): added rule `conv-U-Prop` (A, B : Prop, A = B : U ==> A = B : Prop).
  Cases: ren/subst/typing-ConvTm, convSound' (approximants from the U-conversion),
  adequacyEqSub2 = `adqeq-U-to-Prop` of the IH.  All targets still exit 0, 0 pragmas/warnings.

- 2026-10-21: **DONE.** `PiInjectivity.agda` and `SubjectReduction.agda` exit 0 under
  `agda-2.9.0 --without-K`; 0 postulates / holes / pragmas in MINPROP/ (58 files,
  `--without-K` [+ `--exact-split`] only); fresh build of the whole cone 14.9s, max
  file 1.6s (`Adequacy/Cases`); 0 warnings.  Gates 1-3 all passed.
  Design deviation from section 1 (simpler): no `AllProp` bundle field.  Prop codes
  are given by a STRUCTURAL, stage-free predicate `IsProp` (MemStage):
  `u : PropCode := u : U  /\ IsProp u`, so Prop <= U is a projection and
  stability/shift of the PropCode clauses reduce to the UCode ones.
  New files: `Domain/PropCodes` (IsProp closed under Sup / EvalFun, downward
  closed), `Domain/Collapse` (prop-collapse: u : a, IsProp a ==> u = Bot),
  `Model/SoundnessProp` (InvTyp-Prop-U, InvConv-Prop, InvTyp-Pi-Prop),
  `Adequacy/Prop` (the six rule combinators; Pi-into-Prop reuses Pi-into-U on the
  U-weakened premises), `NoConfusion` (U, Prop, Pi pairwise non-convertible).

- 2026-10-21: plan written. Precedents checked: old Prop proof `392a0bd`
  (collapse uses `val-nbot`, present in MIN); CAST/IdCode, which compiles pragma-free
  today. Not started.
