# NEXT SESSION — full BCDE: Π-injectivity + Tarski/Russell equivalence

## Goal
Formalise the BCDE system (bcde.pdf: internal levels, level products `[α]A`,
constraint products `[ψ]A`, universes `U_l`, App. C collapse) with
1. Π-injectivity (via domain adequacy, as in `BCDE3/`), and
2. the Russell ⇔ Tarski equivalence (as in `ERT/` / `ERTUU/`, paper §4).

Standing rules: `--without-K --exact-split`, `agda-2.9.0 --safe`, no
postulates/holes/pragmas, ≤20 s per file; run from `~/DOMAIN`.

## UPDATE 2026-09-28 (latest): T_P side DONE — Sterbac 4.15 / 4.18 / 4.19 for BCDE
Guard η `conv-GLam-eta` added to T_R/T_T/T_P (user's choice; not in bcde.pdf, needed by the
NF route's diagonal lemma).  `GrdNoConf` (guard-β-aware injectivity/no-confusion), `PTyping`,
`StripDeriv` (4.15), `RussellInversion`, `Coerce`, `JoinProps`, `StripUniqNF` (4.18),
`SectionR` (4.19), `StripUniqNFTest`.  See README top.  Possible further work: a paper
write-up (as `ERT/sec43.tex`), T_T ⇔ T_P directly, non-cumulative variant, Σ/Id/N.

## UPDATE 2026-09-28: step 3 DONE in BCDE4 — full BCDE goal reached
Russell ⇔ Tarski with levels, guards, level products, cumulative universes:
Lemma 4.6 (`EraseDeriv`), Lemma 4.10 (`Uniqueness`), Theorem 4.13 (`Equivalence`),
plus Π/[α]/U-injectivity (`Main`) and loop decidability (`LC/Loop`).  See README top.
Possible further work: T_P / §4.3–4.4 analogues (Thm 4.15, 4.18/4.19 as in Sterbac),
a non-cumulative variant, Σ/Id/N.

## UPDATE 2026-09-28 (later): steps 1 and 2 DONE
* Step 1 (level equality) done in `BCDE2/` (kept, U : U) and carried over.
* Step 2 (`U_l`) done in `BCDE3/`: cumulative Russell universes (App. B),
  separate `IsType` with large `[α]A`, `[ψ]A`; model `U_l ↦ UCode (lcode l)`;
  relation clause `RValU` remembers the level; `Main.UInj` (U-injectivity)
  alongside `PiInj`, `LPiInj`.  Build ≈23 s, max module 1.7 s.
* NEXT: step 3 (Tarski T_P with levels + Russell ⇔ Tarski), in a copy `BCDE4/`
  or directly on `BCDE3/`.  Tarski with cumulativity needs the lifts
  `T^m_l` (App. A); decide the Tarski formulation first.

## Where we were (2026-09-28, before steps 1–2) — read `BCDE3/README.md` first
`~/.cabal/bin/agda-2.9.0 --safe BCDE3/All.agda`: clean, ≈22 s total.
* Russell `U : U` + levels + `[α]A`/`⟨α⟩u`/`t l` (β, η) + `[ψ]A`/`⟨ψ⟩t` + ∅ + collapse.
* Level-substitution lemma `RussellLsub` (`lsubD-*`, `lsubCtx-inst`, `lsub1-liftL`).
* Model: codes `LevTy`, `LevEl k`, `LPiCode f`; levels coded by `D : LDecAll`
  (canonical `lcode`); guards read the ambient theory of the target context.
* Adequacy driver over all level substitutions z (`Adeq/Driver.agda`).
* Bezem–Coquand loop checking `LC/` ⇒ `decValid`, `ldecAll`; `Main.agda`:
  `adequacy`, `PiInj`, `LPiInj` (loop-free contexts), no parameters.

## Gaps w.r.t. BCDE
1. ~~**Invariance under level equality**~~ **DONE 2026-09-28** — rules
   `conv-cong-LApp-lvl` (instance conversion as premise; paper form
   `RussellLeq.mk-conv-cong-LApp-lvl`), `conv-Grd-equiv`, `conv-GLam-equiv`
   (`Levels.EquivC`); syntactic lemma `RussellLeq.leq-HasType`; relation fields
   `RValTyLPi.edgeLE`, `RValLPi.appLE` (analogues of Π's `edgeE`/`appE`);
   driver `adqLv` (level variation, into targets with `l = l'` added:
   `Level.LvTy`/`LvTm`); `Adeq/Relevel`.  Clean build ≈22.5 s, max module
   1.6 s.  The old notes follow for the record.
   Old notes — missing rules:
   `Γ ⊢ l = l'` ⇒ `t l ≡ t l'`, and `ψ ⇔ ψ'` valid ⇒ `[ψ]A ≡ [ψ']A`,
   `⟨ψ⟩t ≡ ⟨ψ'⟩t`. Previous attempt: `conv-cong-LApp-lvl` was REMOVED because the
   relation fields `LEdgeEq2`/`LAppEq2` (level variation) were unprovable —
   root cause: `A[l/α] ≡ A[l'/α]` was NOT derivable (guards carry syntactically
   different constraints). Plan: add the guard/level congruences, prove a
   **level-equality substitution lemma** (z, z' pointwise valid-equal ⇒
   `Γz ⊢ Az ≡ Az'`, by induction like `RussellLsub`), then re-add the relation
   fields. Semantics should be easy: guards evaluate by validity (same for
   equivalent ψ) and `lcode` is canonical (same code for equal levels).
   Check this FIRST — it is the only step not yet de-risked.
2. **Universes `U_l`** (bcde.pdf App. B, Russell): `U_l : U_{l⁺}`, Π in
   `U_{l∨m}`, `[α]A`'s universe, check cumulative or not in the paper.
   Model options: all `U_l` ↦ one U code (as ERTUU: U ↦ level-0 code) —
   enough for Π-inj; but **U-injectivity** (`U_l ≡ U_m ⇒ l = m`), needed for
   Tarski/Russell, wants `U_l ↦ UCode (lcode l)` (Sterbac `Injectivity` used a
   levelled UCode). Design question: membership between UCode's with
   canonical-but-unordered codes. Decide before coding; signal early.
3. **Tarski/Russell**: port `ERT/` (T_P, erasure, section, Thm 4.13/4.15,
   4.18/4.19 via `StripUniqNF` — η-coercions + type Joins, no normalisation)
   to levels/guards/level products. Needs Π-inj, U-inj, no-confusion, and the
   inversion lemmas. Note `ERT/Gap417.agda`: paper's Lemma 4.17 proof has a
   cumulativity gap (closed in the NF route) — re-check with `U_l`.
   Tarski side needs El/codes for `[α]A` and `[ψ]A` (`El([ψ]a) = [ψ]El a`, …).

## Suggested order
1. ~~Level-equality congruence + substitution lemma + model/relation (gap 1).~~ DONE
2. `U_l` (gap 2) — Russell side + adequacy + U-injectivity.
3. Tarski theory T_P with levels + Russell⇔Tarski (gap 3).
Keep collapse: injectivity statements take `LoopFree (lctx G)`.

## References
bcde.pdf (system, Fig. 12–14, App. B/C), paper1.pdf §3–4 (domain technique,
Russell/Tarski), loopalg1.pdf (loop checking), `ERT/NEXT_SESSION_43.md`,
`ERTUU/README.md`, memory `project_bcde_constraint_products.md`.
