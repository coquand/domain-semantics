# ✅ DONE (2026-05-21 session 2) — kernel ORDER finished

**`MIN/PaperOrder.agda` now has 0 TERMINATING pragmas (was 11); `agda-2.9.0 --without-K
MIN/PiInjectivity.agda` exits 0.** PaperOrder is a 38-line re-export shim over 6 new pragma-free
files: `LeqStageComp`, `LeqStageProps2` (stage-indexed block 905 + Comp-down/Comp-value/
Coherent-EvalFun/LeCode-Comp), `LeqStageOrder` (LeqC collapses), `LeqStageBridge` (re-founded
EvalFun/LeCode/LeFunCode + bridges), `LeqStageInterface` (public props), `LeqStageEval2`
(leFinEl:=leiC, comp-EvalFun, EvalFun-append-eq). Cone untouched: LeCode/LeFunCode kept structural
(definitional unfolding preserved), `leFinEl := leiC` and `EvalFun` via `EvalFun-step` firing on
`leiC` (so Selection/PaperTyping's EvalFun-step+leFinEl uses still work). See memory
`project-leqstage-progress` for the full record. Backup of old PaperOrder: /tmp/PaperOrder.agda.session2.bak.

**NEXT TARGET = TYPING:** eliminate `MIN/PaperTyping.agda`'s 3 FinMem `{-# TERMINATING #-}` pragmas
(FinMem / FinMemFun / FinMemAllU) by the same stage-n + stability method, now resting on the
stable `≤`/`Coherent`. See `project-kernel-stratification-method` (instance 1: `Pi a f :_{n+1} U`).

---

# (historical) NEXT SESSION — finish the kernel ORDER (eliminate the 11 `PaperOrder` pragmas)

## THE GOAL (one sentence)
Finish the stage-stratified order so that **`MIN/PaperOrder.agda` has zero `TERMINATING`
pragmas** (currently **11**): complete the per-stage property pack in `MIN/LeqStageProps.agda`,
collapse it to the public order in `MIN/LeqStageStable.agda`, then **re-found PaperOrder's
`LeCode`/`leFinEl`/`EvalFun` on the LeqStage trilogy** (with `EvalFun` an *ordinary structural*
function so it still reduces normally) and refactor the cone to use `LeCode` abstractly.

**The session AFTER this one = typing**: `MIN/PaperTyping.agda` (3 pragmas; `FinMem`/`FinMemFun`/
`FinMemAllU`), same stage-`n`+stability method, built on top of the now-stable `≤`/`Coherent`.

## THE BIG IDEA (already validated this session — do NOT relitigate)
The genuine non-termination is the **`EvalFun ↔ order` cycle**: `EvalFun g u = sup{v : (u',v)∈g,
u'≤u}` needs the order to decide which pairs fire; the order `f ≤ h` needs `EvalFun` to compare
function values. Naively stage-collapsing the *value-returning* `EvalFun` breaks downstream
definitional reduction (the "collapse problem"). **Fix: define the order INDEPENDENTLY of the
public `EvalFun`**, stage-stratified (its own internal stage-eval `ev`, never re-exported). Then
the public `EvalFun` is re-founded as an *ordinary structural* recursion over the finished
decision `leiC` — it reduces normally, so NO collapse problem. Stratifying the **Set-valued**
order is invisible (like `Val2`); only `EvalFun` (value-valued) had the collapse risk, and we
dodge it by making it structural.

See memory: `project-leqstage-progress`, `kernel-stratification-method`, `adequacy-reindex-done`.

## WHAT IS DONE (the `MIN/LeqStage*` trilogy — all compile, 0 pragma / 0 postulate)
Build check: `~/.cabal/bin/agda-2.9.0 --without-K MIN/LeqStageStable.agda` (exit 0, ~few s).

### `MIN/LeqStage.agda` (394 ln) — DEFINITION
- structural primitives `append`, `Sup`, `RANK`/`RANKFun` (inlined — CANNOT import `Rank.agda`:
  it imports `PaperSemantics`, which will import this file ⇒ cycle).
- `Comp`/`CompFun`/`CompStepFun`/`CompStepStep`, `NotBot`, `Coherent`/`CoherentFun`/`CFTcons`/
  `CoherentFunTail`/`CoherentWith`, `cft-from-cf` — **copied verbatim from PaperOrder**
  (pragma-free, order-independent: they never mention `leFinEl`/`EvalFun`). These are here so
  the `Coherent`-conditioned order props can be stated/proved in LeqStageProps.
- `evCombine : Nat → FinEl → FinEl → FinEl` (`zero _ r = r`; `suc _ w r = Sup w r`) — the
  per-pair "include in the Sup iff the key fired" step (lifted to top level so RANK-lemmas can
  reason about it).
- `record OrderBundle { leq ; leqf ; lei ; lef ; ev }` (Set order / Set fun-order / Nat decision /
  Nat fun-decision / internal eval), `trivBundle` (Stage 0 base: atoms only), `buildOrderStage`
  (level-`suc n` from level-`n`), `Stage : Nat → OrderBundle`, public `LeqC`/`leiC` at the
  canonical level `suc (max (RANK u) (RANK v))`, public `module OB (n) = OrderBundle (Stage n)`.
  - **NO-LAG (critical):** `leqf'`/`lef'` evaluate the codomain via the **same-stage** `ev'`
    (not the predecessor `evP`); otherwise stage-`suc m` comparison under-resolves rank-`m`
    arguments and stability gets an off-by-one. Keep it.
- `RANK` toolkit: `Le-max-lub`, `max-mono`, `RANK-append`, `RANK-Sup`, `RANK-evCombine`,
  `RANK-ev` (`RANK (OB.ev n h u) ≤ RANKFun h`).

### `MIN/LeqStageProps.agda` (167 ln) — PER-STAGE PROPERTIES (by induction on `n`)
- `isPos-min` (private).
- **Decidability** (DONE): `lei-sound`/`lef-sound`, `lei-complete`/`lef-complete` —
  `isPos (OB.lei n u v) ↔ OB.leq n u v`, mutual induction on `(stage n, structure)`.
- **Sup-lub** (DONE, self-contained, NO Coherent): `leq-Bot-any`, `leqf-append-combine`,
  `leq-Sup-lub : (n)(a b c) → OB.leq n a c → OB.leq n b c → OB.leq n (Sup a b) c`.
  This validated the stage-port pattern.

### `MIN/LeqStageStable.agda` (316 ln) — COLLAPSE / STABILITY
- helpers `Eq-trans`, `min-cong`, `evCombine-cong`, `max-Le-l/r`, `RANKFun-cons-key/-val/-tail`.
- `record StabPack n { ev-st ; lei-st ; lef-st }`, `goodStab : (n) → StabPack n`
  (stability of `ev`/`lei`/`lef` across stages, by induction on `n`; thresholds:
  ev-st `Le (suc (max (RANKFun h)(RANK u))) n`, lei-st `Le (max (RANK u)(RANK v)) n`,
  lef-st `Le (suc (max (RANKFun g)(RANKFun h))) n`). Proved DIRECTLY (no-lag ⇒ no monotonicity
  needed). The suc-step uses only `ih.lei-st`; same-stage `evS`/`lefS`/`leiS` are SEPARATE
  structural recursions.
- `leq-stable-fwd`/`-bwd` (Set-order one-step, via lei-st + decidability),
  `plus`/`Le-plus`/`Le-gap`, `leq-lift`/`leq-lower`/`leq-shift` (stage-shift between any two
  stages ≥ canonical — mirrors `ValidityLevels.shiftVTy`), `leqC-from`/`leqC-to`,
  and public `Leq-Bot`, `leiC-sound`, `leiC-complete`.

## REMAINING WORK — in order

### STEP A — finish the `LeqStageProps` per-stage pack (THE BULK, ~300-400 ln)
Port PaperOrder's big mutual order block **lines 905-1140** + its coherence deps **~700-900**,
stage-indexed. Do it as **one big mutual block by induction on `(n, structure)`** (same style as
the `lei-sound` decidability block — NOT necessarily a record pack). The properties (all
**conditional on `Coherent`/`Comp`**, as confirmed: refl fails for incoherent `g` because `ev g u`
collapses to `Bot`):

Port these (PaperOrder name → stage-indexed name `…-n`), with their exact case structure:
- `Coherent-EvalFun` / `Coherent-EvalFun-step` (ev of a coherent fun at a coherent arg is
  coherent) — PaperOrder block ~860-900. NEEDS `Coherent-Sup`.
- `Comp-value-EvalFun` (the fired value is `Comp` with the rest of the eval) — block ~705-880.
- `coherentWith-to-compStepFun`, `CoherentFunTail-append`, `Coherent-Sup`, `EvalFun-append-eq`,
  `Sup-assoc` — supporting (block 10, ~705-880).
- `LeCode-refl`/`LeFunCode-refl`/`LeFunCode-refl-head-step`/`LeFunCode-cons-lift`,
  `EvalFun-cons-mono`/`-step`, `LeCode-Sup-left`/`-right`, `LeCode-trans`/`LeFunCode-trans`/
  `LeFunCode-nil-any`, `EvalFun-mon`/`-step`, `EvalFun-mon-arg`, `LeFunCode-append-left`/`-right`,
  `LeFunCode-append-combine` (already have its analogue `leqf-append-combine`) — block 905-1140.

**Stage-port rules (mechanical):**
1. `LeCode → OB.leq n` ; `LeFunCode → OB.leqf n` ; `leFinEl → OB.lei n` ; `EvalFun g u →
   OB.ev (suc n) g u` (SAME stage, no-lag) ; `EvalFun-step` is folded into `evCombine` already.
2. Add a stage arg `n` and a `Le (RANK <arg>) n` (resp. `Le (suc (RANK …)) n`) side-condition to
   each lemma — copy the threshold shapes from `goodStab`/`leq-Sup-lub`.
3. **Recursion into an `ev`-result or a sub-component (smaller RANK)** — e.g.
   `LeCode (snd p) (EvalFun h (fst p))`, `LeCode-refl (fst p) …`, `LeCode-trans (snd p)
   (EvalFun h ..) (EvalFun k ..)` — recurses at the **predecessor stage `n`** (i.e. inside a
   `suc n` clause you call the lemma at `n`). This is what makes it structural in `n`.
   Same-stage recursion is allowed only on a **structural sub-term** (FinFun list tail).
4. `OB.leq n …` does NOT reduce for abstract `n` ⇒ **case-split `n` into `zero`/`suc m`** wherever
   a clause needs `leq'`/`lei'` to fire or an input to reduce to `Empty` for an absurd `()`
   (see `leq-Sup-lub` for the pattern; use `leq-Bot-any n c` for `leq n Bot c` results).
5. `--exact-split`: enumerate clauses (no overlapping catch-alls).

Sanity target per lemma: `~/.cabal/bin/agda-2.9.0 --without-K MIN/LeqStageProps.agda` exit 0,
no `[TerminationIssue]`, no `CoverageNoExactSplit`.

### STEP B — public properties in `LeqStageStable` (small)
For each per-stage prop, derive the public `LeqC` version by `leq-shift`-ing all inputs to a
common stage `K = suc (max … all RANKs …)`, applying the per-stage prop at `K`, shifting the
result back. Pattern = `leiC-sound`/`leqC-from`/`leqC-to` already in the file; multi-element
ones mirror `ValidityLevels.downValTy2-pub`. Deliver: `Leq-refl`, `Leq-trans`, `Leq-Sup-left`,
`Leq-Sup-right` (and `Leq-Sup-lub` is stage-uniform — direct). Optionally the extensional-form
equivalence `f ≤ g ⇔ ∀x. ev f x ≤ ev g x` (user: "prove at some point").

### STEP C — re-found `PaperOrder` on the trilogy (eliminate the 11 pragmas)
Goal: `PaperOrder` keeps its public interface name-for-name but with pragma-free definitions.
- `LeCode := LeqC`, `LeFunCode := <the leqf collapse>`, `leFinEl := leiC` (import from LeqStage*).
- **`EvalFun` becomes ORDINARY STRUCTURAL** over `leiC` (this is the payoff — reduces normally):
  ```
  EvalFun nil u = Bot
  EvalFun (cons p ps) u = evCombine (leiC (fst p) u) (snd p) (EvalFun ps u)
  ```
  Structural on the list; `leiC` is a finished function (concrete args → 0/1, abstract → stuck,
  same as old `leFinEl`). NO pragma, NO collapse problem. Verify `EvalFun (cons p ps) u` still
  unfolds (the cone relies on this — Selection.agda has 89 uses).
- `leFinEl-sound`/`-complete` := `leiC-sound`/`-complete`.
- The order lemmas (`LeCode-refl`/`-trans`/`-Sup-left`/`-right`/`-Sup-lub`) := the public props
  from Step B. `Coherent-EvalFun`/`Comp-value-EvalFun`/`EvalFun-mon`/`EvalFun-append-eq` etc.:
  re-prove on the new structural `EvalFun` (relate it to `ev`/`leqC`; or transfer from Step A).
- **`LeCode-Comp`** (`Coherent w → LeCode u w → LeCode v w → Comp u v`) — prove HERE (in the
  re-founding), where `Comp`/`Coherent` and `LeCode := LeqC` are all in scope. This is the
  order↔`Comp` bridge that could NOT live in LeqStageProps.
- The remaining pragma'd blocks (`comp-Sup`, `Comp-sym`/`-refl`/`-down`, `LeCode-trans-to-Bot`,
  `LeCode-Bot-Comp`) — check which still fail termination after `EvalFun` is structural; some
  may now pass pragma-free (run the delete-the-pragma test). Re-prove the rest.
- **Refactor the cone** so it uses `LeCode` ONLY via abstract properties (user confirmed). Grep
  for any site that pattern-matches `LeCode`'s definition; replace with property calls.

### STEP D — verify
`grep -c "{-# TERMINATING" MIN/PaperOrder.agda` → **0**. Then full cone:
`~/.cabal/bin/agda-2.9.0 --without-K MIN/PiInjectivity.agda` exit 0 (clean ~11s), 0 holes.

## PITFALLS
- Don't import `Rank.agda` into LeqStage (cycle). Primitives are inlined.
- Keep NO-LAG (`ev'` same-stage in `leqf'`/`lef'`).
- `OB.leq n` is stuck for abstract `n` ⇒ split `n`.
- `EvalFun` MUST stay structural in the re-founding (don't collapse it via `Stage`).
- `--without-K --exact-split`; binary `~/.cabal/bin/agda-2.9.0` (NOT plain `agda`).
- Timeouts: `perl -e 'alarm 60; exec @ARGV' ~/.cabal/bin/agda-2.9.0 --without-K MIN/<F>.agda`.

## ORIENTATION
- This handoff + memory `project-leqstage-progress` (precise port recipe), `kernel-stratification-method`.
- PaperOrder port sources: order block **905-1140**, coherence deps **~700-900**.
- DON'T touch `MIN/PaperSemantics.agda` (6-line re-export shim).
- Backups: `/tmp/LeqStage.full.bak` (pre-split monolith), `/tmp/PaperOrder.agda.bak`,
  `/tmp/PaperTyping.agda.bak`.
