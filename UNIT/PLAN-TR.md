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
* STRICT LIFTS (user decision 2026-11-22): t^n_m and Russell cumulativity need
  m < n (with t^n_n, t^0_0 a and a break uniqueness).  All §4 files adapted.
* RTyping (A.3), ErR (Lemma 21), TGen (generation) DONE.

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

## Lemma 25 design (2026-11-22)
Prototype ERT/UniquenessTermPartial.agda (type-uniq, uniq-El, term-uniq;
recursion on both derivations).  In seg: strong induction on
N = size(left) + size(right) of the raw terms, statements together:
  Q(A, B)   G |- A, G |- B, |A| = |B|                  => G |- A = B
  E(B, a)   G |- B, G |- a : U_n, |B| = |a|            => G |- B = T_n a
  T(u0, u1) G |- u0 : A0, G |- u1 : A1, |u0| = |u1|    => same type and
            convertible, or common lift (CommonLift, with LiftStep =
            trivial (k = n, u = v) | proper (k <= n, u = t^n_k v))
Calls: Q(X, T_n b) -> E(X, b); Q(T_n a, Y) -> E(Y, a); E(T_l a1, a2) ->
T(a1, a2); E(_, t a'') -> E(_, a''); E(Pi A B, Pi_l a b) -> E(A,a), E(B,b);
T(t a, u1) -> T(a, u1); T(u0, t a) -> T(u0, a); binders: Q/T on parts.
All decrease N.  Generation lemmas (TGen.seg) instead of recursion on
derivations: no recursion through tm-conv.
