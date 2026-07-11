{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecCpl0
--
-- Primitive recursion, the base sub-case where the recursion argument
-- is 0:  f(0, Y) = g(Y).  So f's obstination at (0, Y) lifts g's
-- obstination at Y, shifting the witness coordinate i to i+1 (the extra
-- leading coordinate is pinned to the complete 0, which forces X(0)=0
-- on the region and hence f(X) = g(X[0])).
--
-- The coordinate shift is definitional (getF (suc i) (cons a xs) =
-- getF i xs, del (suc i) (cons a xs) = cons a (del i xs), etc.); X(0)=0
-- comes from the below/del condition at coordinate 0.
--
-- (This is the  x = 0  branch of the eventual  prop1-prec  dispatch.)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecCpl0 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Prop1Base using (fcpl-max)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

module _ (rd : RecData) where
  open RecData rd

  prec-lift-cpl0 : (Y : Tup) ->
    UO G Y -> UO (PF G H) (cons (cpl zero) Y)
  -- Case 1
  prec-lift-cpl0 Y (uo1 (mkSigma Y0 (mkSigma belowY (mkSigma m univG)))) =
    uo1 (mkSigma (cons (fcpl zero) Y0)
          (mkSigma (mkSigma (LeD-refl (cpl zero)) belowY) (mkSigma m univ)))
    where
      univ : (X : FTup) -> LeFTup (cons (fcpl zero) Y0) X ->
             Eq (PF G H X) (fcpl m)
      univ nil ()
      univ (cons x xs) leX =
        Eq-transport (\ w -> Eq (PF G H (cons w xs)) (fcpl m))
          (Eq-sym (fcpl-max zero x (fst leX))) (univG xs (snd leX))
  -- Case 2
  prec-lift-cpl0 Y
    (uo2 (mkSigma Y0 (mkSigma belowY (mkSigma m (mkSigma i (mkSigma irange
      (mkSigma incomplY (mkSigma eqY0inv univG)))))))) =
    uo2 (mkSigma (cons (fcpl zero) Y0)
          (mkSigma (mkSigma (LeD-refl (cpl zero)) belowY)
            (mkSigma m (mkSigma (suc i) (mkSigma irange
              (mkSigma incomplY (mkSigma eqY0inv univ)))))))
    where
      univ : (X : FTup) -> Eq (length X) (length (cons (fcpl zero) Y0)) ->
             Eq (getF (suc i) X) (getF (suc i) (cons (fcpl zero) Y0)) ->
             LeFTup (del (suc i) (cons (fcpl zero) Y0)) (del (suc i) X) ->
             Eq (PF G H X) (fbot m)
      univ nil ()
      univ (cons x xs) lenX coordX delX =
        Eq-transport (\ w -> Eq (PF G H (cons w xs)) (fbot m))
          (Eq-sym (fcpl-max zero x (fst delX)))
          (univG xs (suc-inj lenX) coordX (snd delX))
  -- Case 3
  prec-lift-cpl0 Y
    (uo3 (mkSigma Y0 (mkSigma belowY (mkSigma i (mkSigma eqinfY
      (mkSigma k (mkSigma eqY0 (mkSigma phi (mkSigma phiok univG))))))))) =
    uo3 (mkSigma (cons (fcpl zero) Y0)
          (mkSigma (mkSigma (LeD-refl (cpl zero)) belowY)
            (mkSigma (suc i) (mkSigma eqinfY (mkSigma k (mkSigma eqY0
              (mkSigma phi (mkSigma phiok univ))))))))
    where
      univ : (X : FTup) (p : Nat) -> Eq (length X) (length (cons (fcpl zero) Y0)) ->
             LeN k p -> Eq (getF (suc i) X) (fbot p) ->
             LeFTup (del (suc i) (cons (fcpl zero) Y0)) (del (suc i) X) ->
             Eq (PF G H X) (fbot (phi p))
      univ nil p ()
      univ (cons x xs) p lenX pk coordX delX =
        Eq-transport (\ w -> Eq (PF G H (cons w xs)) (fbot (phi p)))
          (Eq-sym (fcpl-max zero x (fst delX)))
          (univG xs p (suc-inj lenX) pk coordX (snd delX))
