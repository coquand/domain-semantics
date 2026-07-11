{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecGuard
--
-- Bridging the arity-guarded recursion back to the concrete interpreter.
--
-- The top-level `prop1` interprets  prec g h  at arity  suc m  by feeding
-- the abstract recursion the ARITY-GUARDED base and step
--   Gg = guard m (evalF g),   Hg = guard (suc (suc m)) (evalF h),
-- which are total and obstinate.  On tuples of the ambient length the
-- guards coincide with  evalF g / evalF h,  so the guarded recursion
-- `precFun Gg Hg` coincides with the concrete `precF g h`, whenever the
-- tail Y has length m (`precFun-guard-eq`).  Its tuple form `PF-guard-eq`
-- is what the pointwise transport in `prop1` consumes.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecGuard where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR using (PR ; prec ; evalF ; precF)
open import OBSTINATION.PrecFun using (precFun ; PF)
open import OBSTINATION.Arity using (guard ; guard-eq)

precFun-guard-eq : (g h : PR) (m : Nat) (a : FEl) (Y : FTup) -> Eq (length Y) m ->
  Eq (precFun (guard m (evalF g)) (guard (suc (suc m)) (evalF h)) a Y)
     (precF g h a Y)
precFun-guard-eq g h m (fbot zero)    Y lenY = refl
precFun-guard-eq g h m (fbot (suc j)) Y lenY =
  Eq-trans (guard-eq (suc (suc m)) (evalF h) T lenT)
           (Eq-cong (\ r -> evalF h (cons (fbot j) (cons r Y)))
             (precFun-guard-eq g h m (fbot j) Y lenY))
  where
    recL = precFun (guard m (evalF g)) (guard (suc (suc m)) (evalF h)) (fbot j) Y
    T    = cons (fbot j) (cons recL Y)
    lenT : Eq (length T) (suc (suc m))
    lenT = Eq-cong (\ z -> suc (suc z)) lenY
precFun-guard-eq g h m (fcpl zero)    Y lenY = guard-eq m (evalF g) Y lenY
precFun-guard-eq g h m (fcpl (suc j)) Y lenY =
  Eq-trans (guard-eq (suc (suc m)) (evalF h) T lenT)
           (Eq-cong (\ r -> evalF h (cons (fcpl j) (cons r Y)))
             (precFun-guard-eq g h m (fcpl j) Y lenY))
  where
    recL = precFun (guard m (evalF g)) (guard (suc (suc m)) (evalF h)) (fcpl j) Y
    T    = cons (fcpl j) (cons recL Y)
    lenT : Eq (length T) (suc (suc m))
    lenT = Eq-cong (\ z -> suc (suc z)) lenY

-- Tuple form: agreement of PF on the ambient-length region  (length X = suc m).
PF-guard-eq : (g h : PR) (m : Nat) (X : FTup) -> Eq (length X) (suc m) ->
  Eq (PF (guard m (evalF g)) (guard (suc (suc m)) (evalF h)) X)
     (evalF (prec g h) X)
PF-guard-eq g h m nil        ()
PF-guard-eq g h m (cons a Y) lenX = precFun-guard-eq g h m a Y (suc-inj lenX)
