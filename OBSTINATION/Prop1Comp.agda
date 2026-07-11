{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Prop1Comp
--
-- The composition case of Proposition 1, driven by ARITY-guarded inner
-- functions.  At the top level a sub-term  g  (resp. each  h_j) is only
-- obstinate at tuples of its own arity, so `evalF g` is not `UOall`.  We
-- pad with the arity guard: `guard n (evalF h_j)` is total and obstinate
-- (guard-uoall) and monotone (guard-mono), hence a `UOFun`, and equals
-- `evalF h_j` on the ambient-length region.  Feeding the generic
-- `CompDispatch.prop1-compose` these guarded inner functions and a guarded
-- outer  g,  then transporting along the pointwise agreement, yields
-- obstination of  comp g hs  at every ambient-length point.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Prop1Comp where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Meet using (cons-eq)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.GProj using (UO-pointwise-len)
open import OBSTINATION.CompPull using (UOFun ; ufn ; mapU ; compFn)
open import OBSTINATION.CompDispatch using (prop1-compose)
open import OBSTINATION.Arity using (UOn ; guard ; guard-eq ; guard-uoall ; guard-mono)

------------------------------------------------------------------------
-- Arity-restricted obstination of a whole argument list.
------------------------------------------------------------------------

AllUOn : List PR -> Nat -> Set
AllUOn nil         n = Top
AllUOn (cons h hs) n = Pair (UOn n (evalF h)) (AllUOn hs n)

-- Every inner function guarded to a total UOFun.
bundleGuard : (hs : List PR) (n : Nat) -> AllUOn hs n -> List UOFun
bundleGuard nil         n au = nil
bundleGuard (cons h hs) n au =
  cons (mkSigma (guard n (evalF h))
          (mkSigma (guard-uoall n (evalF h) (fst au))
                   (guard-mono  n (evalF h) (evalF-mono h))))
       (bundleGuard hs n (snd au))

-- On the ambient-length region the guarded action is exactly mapE.
mapU-bundleGuard-eq : (hs : List PR) (n : Nat) (au : AllUOn hs n) (X : FTup) ->
  Eq (length X) n -> Eq (mapU (bundleGuard hs n au) X) (mapE hs X)
mapU-bundleGuard-eq nil         n au X lenX = refl
mapU-bundleGuard-eq (cons h hs) n au X lenX =
  cons-eq (guard-eq n (evalF h) X lenX) (mapU-bundleGuard-eq hs n (snd au) X lenX)

mapE-length : (hs : List PR) (X : FTup) -> Eq (length (mapE hs X)) (length hs)
mapE-length nil         X = refl
mapE-length (cons h hs) X = Eq-cong suc (mapE-length hs X)

------------------------------------------------------------------------
-- The composition case at a point of the correct arity.
------------------------------------------------------------------------

prop1-comp-guard : (g : PR) (hs : List PR) (n : Nat) ->
  UOn (length hs) (evalF g) -> AllUOn hs n -> (A : Tup) -> Eq (length A) n ->
  UO (evalF (comp g hs)) A
prop1-comp-guard g hs n uong au A lenA = UO-pointwise-len agree composed
  where
    Gg : FTup -> FEl
    Gg = guard (length hs) (evalF g)
    uoGg : UOall Gg
    uoGg = guard-uoall (length hs) (evalF g) uong
    fs : List UOFun
    fs = bundleGuard hs n au
    composed : UO (compFn Gg fs) A
    composed = prop1-compose Gg uoGg fs A
    agree : (X : FTup) -> Eq (length X) (length A) ->
            Eq (compFn Gg fs X) (evalF (comp g hs) X)
    agree X lenXA =
      Eq-trans (Eq-cong Gg (mapU-bundleGuard-eq hs n au X lenXn))
               (guard-eq (length hs) (evalF g) (mapE hs X) (mapE-length hs X))
      where
        lenXn : Eq (length X) n
        lenXn = Eq-trans lenXA lenA
