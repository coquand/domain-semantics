# PLAN-TR: sterbac4 §5, T_Tarski <=> T_Russell, in Unit (seg)

Decided 2026-11-22 (user): Tarski <=> Russell in Unit.  Pi-injectivity is NOT
needed (Russell is annotated; Fig. 5: only U-inj and U != Pi for T_Tarski).
Prototype: ERT/ (Agda, scoped) EraseDeriv, Uniqueness, UniquenessTermPartial,
LiftBack, Equivalence (paper Lemmas 21-28 = sterbac1 4.6-4.13).

## Done
* Levelled filter domain LTypes LConsistency LTyping LFilter LSoundF
  (univ n; membership ignores levels; consistency forbids two levels).
* TSem, TSound (soundness of T_Tarski), TRed (head reduction, unused so far).
* TInv: uu-inj (Thm 9), pi-uu-noconf (Thm 10), uc-inj, uc-pic-noconf.
* TPresup (Lemmas 22-24), TSubLib.cxconv-* (Lemma 24 general).

## Design
* Russell raw syntax = TSyntax.Tm restricted to var/pi/lam/app/uu (reuse
  substitution and its laws).  Russell judgements: new family RDer (A.3).
* Erasure er : Tm -> Tm (el, lf dropped; pic -> pi; uc m n -> U_m).

## Files
1. RTyping.seg   Russell judgements (A.3)                      [ ]
2. ErR.seg       erasure, raw lemmas, Lemma 21                 [ ]
3. TGen.seg      generation lemmas for T_Tarski typing         [ ]
4. TUniq*.seg    Lemma 25, 26, Corollary 27                    [ ]
5. TSection.seg  Theorem 28 (section of erasure)               [ ]
