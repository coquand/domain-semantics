{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Prop1
--
-- Proposition 1 (min1.pdf p.2): every element of PR satisfies ultimate
-- obstination.  Formally, at every point of its own arity.
--
-- `Wf p n` says a PR term p is well-formed of arity n:
--   * zerf     -- any arity;
--   * proj i   -- needs i < n;
--   * succ     -- needs n >= 1 (uses only coordinate 0);
--   * comp g hs-- g of arity (length hs), each h_j of arity n;
--   * prec g h -- n = suc m, g of arity m, h of arity suc (suc m).
--
-- `prop1` is the induction on PR.  The base cases are `Prop1Base`.  The
-- inductive cases (composition, primitive recursion) are stated in the
-- literature with `UOall` sub-hypotheses, which a plain induction cannot
-- supply -- a sub-term is obstinate only at its OWN arity.  We bridge this
-- with the arity guard: the induction hypothesis gives the arity-restricted
-- `UOn`, `guard` pads it to a total obstinate function, and the guarded
-- recursion / composition agrees with the concrete interpreter on the
-- ambient-length region (`PrecGuard`, `Prop1Comp`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Prop1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Stability using (stable)
open import OBSTINATION.GProj using (UO-pointwise-len)
open import OBSTINATION.Prop1Base using (prop1-zerf ; prop1-succ ; prop1-proj)
open import OBSTINATION.Arity using
  (UOn ; guard ; guard-uoall ; guard-mono ; guard-stable)
open import OBSTINATION.PrecFun using (RecData ; mkRecData ; PF)
open import OBSTINATION.PrecGuard using (PF-guard-eq)
open import OBSTINATION.PrecAll using (prop1-prec-generic)
open import OBSTINATION.Prop1Comp using (AllUOn ; prop1-comp-guard)

------------------------------------------------------------------------
-- Well-formedness of arity n
------------------------------------------------------------------------

mutual
  Wf : PR -> Nat -> Set
  Wf zerf        n = Top
  Wf (proj i)    n = LeN (suc i) n
  Wf succ        n = LeN (suc zero) n
  Wf (comp g hs) n = Pair (Wf g (length hs)) (AllWf hs n)
  Wf (prec g h)  n =
    Sigma Nat (\ m -> Pair (Eq n (suc m)) (Pair (Wf g m) (Wf h (suc (suc m)))))

  AllWf : List PR -> Nat -> Set
  AllWf nil         n = Top
  AllWf (cons h hs) n = Pair (Wf h n) (AllWf hs n)

------------------------------------------------------------------------
-- Proposition 1
------------------------------------------------------------------------

mutual
  prop1 : (p : PR) (A : Tup) -> Wf p (length A) -> UO (evalF p) A
  prop1 zerf     A          wf = prop1-zerf A
  prop1 (proj i) A          wf = prop1-proj i A wf
  prop1 succ     nil        wf = Empty-elim wf
  prop1 succ     (cons a A') wf = prop1-succ a A'
  prop1 (comp g hs) A wf =
    prop1-comp-guard g hs (length A)
      (\ A' e -> prop1 g A' (Eq-transport (Wf g) (Eq-sym e) (fst wf)))
      (allUOn hs (length A) (snd wf)) A refl
  prop1 (prec g h) nil        (mkSigma m (mkSigma () _))
  prop1 (prec g h) (cons a Y) (mkSigma m (mkSigma lenEq (mkSigma wfg wfh))) =
    UO-pointwise-len transport (prop1-prec-generic rd a Y)
    where
      lenYm : Eq (length Y) m
      lenYm = suc-inj lenEq
      Gg : FTup -> FEl
      Gg = guard m (evalF g)
      Hg : FTup -> FEl
      Hg = guard (suc (suc m)) (evalF h)
      uonG : UOn m (evalF g)
      uonG A' e = prop1 g A' (Eq-transport (Wf g) (Eq-sym e) wfg)
      uonH : UOn (suc (suc m)) (evalF h)
      uonH A' e = prop1 h A' (Eq-transport (Wf h) (Eq-sym e) wfh)
      rd : RecData
      rd = mkRecData Gg Hg
             (guard-mono   m           (evalF g) (evalF-mono g))
             (guard-mono   (suc (suc m)) (evalF h) (evalF-mono h))
             (guard-stable (suc (suc m)) (evalF h) (stable h))
             (guard-uoall  m           (evalF g) uonG)
             (guard-uoall  (suc (suc m)) (evalF h) uonH)
      transport : (X : FTup) -> Eq (length X) (length (cons a Y)) ->
                  Eq (PF Gg Hg X) (evalF (prec g h) X)
      transport X e =
        PF-guard-eq g h m X (Eq-trans e (Eq-cong suc lenYm))

  allUOn : (hs : List PR) (n : Nat) -> AllWf hs n -> AllUOn hs n
  allUOn nil         n aw = tt
  allUOn (cons h hs) n aw =
    mkSigma (\ A' e -> prop1 h A' (Eq-transport (Wf h) (Eq-sym e) (fst aw)))
            (allUOn hs n (snd aw))
