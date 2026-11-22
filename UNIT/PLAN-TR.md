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
* Lemma 25, Lemma 26, Corollary 27 DONE 2026-11-22 (TUniqBase, TUniqComb,
  TUniq; 771 lines, 0.35 s in GATCheck.seg, also in All.seg):
  ty-uniq / el-uniq / tm-uniq (25.1-3), res-same (26), er-inj (27).
* Theorem 28 DONE 2026-11-22 (TSection.seg, 466 lines, GATCheck 0.39 s, in
  All.seg): sec / thm28 (existence, (J' : Jf) * erJ J' = J * Der J') and
  cxer, un-ty, un-tm, un-eqty, un-eqtm (uniqueness up to conversion).
  §5 of sterbac4 is complete in Unit.

## Design
* Russell raw syntax = TSyntax.Tm restricted to var/pi/lam/app/uu (reuse
  substitution and its laws).  Russell judgements: new family RDer (A.3).
* Erasure er : Tm -> Tm (el, lf dropped; pic -> pi; uc m n -> U_m).

## Files
1. RTyping.seg   Russell judgements (A.3)                      [x]
2. ErR.seg       erasure, raw lemmas, Lemma 21                 [x]
3. TGen.seg      generation lemmas for T_Tarski typing         [x]
4. TUniq*.seg    Lemma 25, 26, Corollary 27                    [x]
5. TSection.seg  Theorem 28 (section of erasure)               [x]

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

## Lemma 25 as formalised (2026-11-22), differences from the design above
* lft k n v (TUniqBase) = v if k = n, lf k n v if k < n (ifB on eqN); all
  case splits on k <= n go through le-elim.  Laws lft-tm/cong/el/lft/pic/uc.
  Replaces the prototype's LiftStep (trivial | proper).
* CLU[G, u0, u1, n0, n1]: ONE code v : U_k with u_i = lft k n_i v : U_n_i
  (paper: v0 = v1 : U_k; equivalent by lft-cong).  CL adds A_i = U_n_i.
* Pi-code case: common level K = max ka kb, common code
  Pi_K(t^K_ka va, t^K_kb vb) (picV); no trichotomy on ka, kb.
* Right lift case = res-sym of the left one (lf-left).
* Measure: fuel N >= sz(left) + sz(right); uniq : (N : Nat) -> Hyp N.
  TUniq.seg is generated: python3 gen_tuniq.py > TUniq.seg (from UNIT/);
  regenerate if TSyntax.Tm changes (9x9 shape dispatch for T, E and Q).

## Theorem 28 as formalised (2026-11-22)
* Statement proved by induction on RDer: SecJ J = LCx[ctx J] * AllJ J, where
  AllJ J says: for EVERY Tarski context D with CtxOk D and |D| = ctx J, J lifts
  into D (records LTy, LTm, LEqTy, LEqTm: Tarski terms + erasure equations +
  derivation in D).  Quantifying over the target context removes the
  prototype's Stage A (ERT/LiftBack: moving derivations between
  erasure-equal contexts); binder cases just extend D by the lifted domain.
* Premise types are aligned by ty-uniq (Lemma 25.1) (helpers tu, co-tm,
  co-eqtm, cu-tm, cu-eqtm); term-equality transitivity uses er-inj (Cor 27).
* Uniqueness: cxer (well-formed contexts with equal erasure are CxEq, by
  ty-uniq + cxconv-ty), then un-* via cxconv-* and ty-uniq / er-inj.
