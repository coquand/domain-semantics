# NEXT SESSION — eliminate the last pragmas: kernel order/typing via stage-`n` stratification

## THE GOAL (one sentence)
Make `MIN/PiInjectivity.agda` derivable with **zero `TERMINATING` pragmas anywhere in its cone**, by
stratifying the domain kernel — first the order `≤` (`MIN/PaperOrder.agda`, 11 pragmas), then typing
`:` (`MIN/PaperTyping.agda`, 3 pragmas) — with the "define at stage `n`, prove monotonicity, derive
stability" method.

## WHERE WE ARE (everything else is already pragma-free)
The entire adequacy + validity + syntax/soundness layer of the PiInjectivity cone is pragma-free:
- Value driver `MIN/AdequacyValue.agda` is a pragma-free **structural** proof; `PiInjectivity` +
  `AdequacyDriver` import the value recursors from it (not the old monolithic `MIN/Adequacy.agda`,
  now dead). conv-beta is stated on the **contractum** + β head-expand (see
  `NEXT_SESSION_ADEQUACY_VALUE_DRIVER.md` / memory `adequacy-beta-contractum`).
- `MIN/SubstitutionLemma.agda`, `MIN/TypingSemantics.agda` (`theorem1`), `MIN/RawSemantics.agda`,
  `MIN/Validity.agda` had **unnecessary/stale** pragmas — all deleted, all compile clean. (The
  conv-Pi GREY PREMISES added earlier made the substitution/presupposition layer structural.)

**The ONLY remaining pragmas in the cone are in the domain kernel**, now split into two files:

### `MIN/PaperOrder.agda` — 11 pragmas (the `≤` layer) — DO THIS FIRST
Genuinely non-structural because `leFun`/`LeFunCode` recurse `LeCode (snd p) (EvalFun h (fst p))` —
`EvalFun h (fst p)` is a *computed* code, not a structural subterm. Pragma'd blocks:
1. `leFinEl` / `leFun` / `EvalFun` / `EvalFun-step` / `LeCode` / `LeFunCode`  (the order itself, ex.2)
2. `leFinEl-sound`,  3. `leFinEl-complete`  (decidable-order soundness/completeness)
4. `comp-Sup`,  5. `Comp-sym`,  6. `Comp-refl`,  7. `LeCode-trans-to-Bot`,  8. `LeCode-Bot-Comp`,
   9. `Comp-down`  (compatibility/order lemmas)
10. block headed by `Comp-value-EvalFun` (… `Sup-assoc`, `EvalFun-append-eq`, `Coherent-Sup`,
    `CoherentFunTail-append`, `CoherentFun-append`, `Coherent-EvalFun`)
11. block headed by `LeCode-refl` (… big order/coherence lemma block)
(`Comp` itself is ALREADY pragma-free; `Coherent` is ALREADY pragma-free — structural — kept in this file.)

### `MIN/PaperTyping.agda` — 3 pragmas (the `:` layer) — DO THIS SECOND
`open import MIN.PaperOrder public` then:
1. `FinMem` / `FinMemFun` / `FinMemAllU`  (membership/typing `_:_n_`, ex.1; recurses through
   `FinMem (snd p) (EvalFun f (fst p))`)
2. block headed by `FinMem-coh-u` (`FinMem-coh-u`, `FinMem-a-in-U`, `FinMem-coh-a`, `coh-from-aU`)
3. block headed by `finMemUCode-Sup` (… `EvalFun-in-UCode`, `finMem-Sup-right/-left`,
   `finMemFun-Sup-*`, `finMem-EvalFun-*`)
(The trailing `finMem-upward`/`finMemFun-upward`/`FinMemFun-append`/`FinMem-Sup-element`/`finMem-Sup-both`
are ALREADY pragma-free.)

`MIN/PaperSemantics.agda` is now a 6-line re-export shim (`open import MIN.PaperTyping public`), so all
~15 importers keep working unchanged — DO NOT add content there.

## WHY THIS ORDER WORKS (verified dependency layering — no mutual entanglement)
- `LeCode`/`leFinEl`/`EvalFun`  ⊥  `Comp`  (two independent primitive blocks; neither references the
  other, neither references `Coherent` or `FinMem`).
- `Coherent → Comp`/`NotBot`  (one-way; already structural / pragma-free).
- `FinMem → Coherent` + `EvalFun`  (one-way; never the reverse — confirmed by grep, comment-stripped).
So **`≤_n` can be stratified in complete isolation** (PaperOrder needs nothing above it), and **`:_n`
is built on top** of an already-stratified `≤_n`/`Coherent`. They are never solved simultaneously.

## THE METHOD (user's examples 1–3 — internalize)
> Define the property at stage `n` extensionally; prove the required properties (incl. **monotonicity**)
> hold at `n+1` assuming they hold at `n`; then derive **stability**: for `u,a ∈ D_n`,
> `P_n(u,a) ↔ P_{n+1}(u,a)`. The stability proof uses that a function value `f` has a finite
> representation `(u₁,v₁),…,(uₘ,vₘ)` with `uᵢ :_n a`, `vᵢ :_n U`.

Concretely for the order (ex.2):
```
Pi a f ≤_{n+1} Pi b g   :=   a ≤_n b   ∧   ∀x. f x ≤_n g x      (schematically)
u :_{n+1} (Pi a f) U    :=   a :_n U   ∧   (∀x ∃y≤x. y :_n a ∧ f x = f y)   ∧   ∀x. f x :_n U   (ex.1)
```
Define `≤_n`, `:_n` by induction on `n`; the recursion through `EvalFun` now lands at stage `n` (a
strictly smaller index) → structural in `n`, no pragma. Prove monotonicity (`u :_n a`, `a'≤a:U` ⟹
`u :_n a'`, etc.) then stability (`u,a ∈ D_n ⟹ (u :_n a ↔ u :_{n+1} a)`). Re-export the *stable*
(stage-collapsed) `≤` / `:` so the rest of the cone (which uses plain `LeCode`/`FinMem`) is unaffected
— exactly the GoodStage pattern.

## TEMPLATE / SCAFFOLDING ALREADY IN THE REPO (reuse, don't reinvent)
The GoodStage work already did this **one level up** (for the `Val/EqVal` logical relation). Study and
mirror:
- `MIN/Rank.agda`, `MIN/SelectionRank.agda` — the iterative-stage RANK measure. **NOTE:** the syntactic
  `rk`/`rkFun` from `MIN.Basic` is the WRONG notion (PaperOrder's own header comment + the (Sigma)
  `RankCounterexamples*` say so) — use the *iterative-stage* RANK.
- `MIN/ValidityStratified.agda`, `MIN/ValidityLevels.agda`, `MIN/ValidityMono.agda` — `Val_n` by
  induction on `n`, monotonicity pack, stability. The kernel `≤_n`/`:_n` is the same shape, smaller.
- Memory notes: `project-rank-stratification-plan`, `project-goodstage-mono-done`,
  `project-goodstage-pivot` (full plan docs `NEXT_SESSION_RANK_STRATIFICATION.md`,
  `NEXT_SESSION_GOODSTAGE.md`).

## TOOLING (unchanged)
- Binary: `~/.cabal/bin/agda-2.9.0 --without-K` (NOT plain `agda`). Interfaces in `_build/2.9.0/agda/MIN/`.
- Timeout heuristic: `perl -e 'alarm 10; exec @ARGV' ~/.cabal/bin/agda-2.9.0 --without-K MIN/<F>.agda`
  (macOS has no `timeout`). A single file blowing past ~10s usually signals a structure mismatch.
- Cheap "is this pragma even needed?" test (paid off 4× this session): delete the pragma, recompile;
  if it still checks, the pragma was stale. **Do this first on each of the 14** before assuming
  stratification is needed — some may be removable outright now.
- Verify end-to-end: `~/.cabal/bin/agda-2.9.0 --without-K MIN/PiInjectivity.agda` (clean cone ≈ 11s),
  then `grep -rn "{-# *TERMINATING" MIN/PaperOrder.agda MIN/PaperTyping.agda` → goal is NONE.

## SUGGESTED PLAN
0. (cheap) Re-run the delete-the-pragma test on each of the 11+3 — keep any that turn out unnecessary.
1. Stratify `≤` in `PaperOrder`: `LeCode_n`/`leFun_n`/`EvalFun` indexed by `n`; monotonicity; stability;
   re-export stable `LeCode`. Then the 11 order lemmas follow at the stable level (or are re-proved on
   `≤_n`). Keep `PaperOrder`'s public interface (`LeCode`, `Comp`, `Sup`, `Coherent`, …) name-for-name
   so `PaperTyping` + the cone are unaffected.
2. Stratify `:` in `PaperTyping`: `FinMem_n` on top of stable `≤`/`Coherent`; monotonicity; stability;
   re-export stable `FinMem`.
3. Confirm cone → PiInjectivity is pragma-free.

## DON'T
- Don't touch the adequacy/validity/substitution layer (done, pragma-free) or `MIN/PaperSemantics.agda`
  (it's just the shim).
- Don't try to stratify `≤` and `:` together — the split exists precisely so they're separate problems.
- Don't use syntactic `rk` as the measure (it's provably wrong here).
