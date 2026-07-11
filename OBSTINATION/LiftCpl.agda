{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.LiftCpl
--
-- Lifting obstination over a complete leading coordinate.  If the tail
-- function  zs |-> f (cons (fcpl c) zs)  satisfies ultimate obstination
-- at Y, then f itself satisfies it at  cons (cpl c) Y.
--
-- Because S^c(0) is complete (maximal), the extra leading coordinate is
-- pinned to it on the whole region (fcpl-max), so f (cons x xs) reduces
-- to the tail function at xs, and the tail's witness coordinate is simply
-- shifted up by one.  This is the inverse of PrecUnshift's `unshift-cpl`,
-- and the c-general form of PrecCpl0's `prec-lift-cpl0`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.LiftCpl where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Prop1Base using (fcpl-max)

lift-cpl : (f : FTup -> FEl) (c : Nat) (Y : Tup) ->
  UO (\ zs -> f (cons (fcpl c) zs)) Y -> UO f (cons (cpl c) Y)
-- Case 1
lift-cpl f c Y (uo1 (mkSigma Y0 (mkSigma belowY (mkSigma m univG)))) =
  uo1 (mkSigma (cons (fcpl c) Y0)
        (mkSigma (mkSigma (LeD-refl (cpl c)) belowY) (mkSigma m univ)))
  where
    univ : (X : FTup) -> LeFTup (cons (fcpl c) Y0) X -> Eq (f X) (fcpl m)
    univ nil ()
    univ (cons x xs) leX =
      Eq-transport (\ w -> Eq (f (cons w xs)) (fcpl m))
        (Eq-sym (fcpl-max c x (fst leX))) (univG xs (snd leX))
-- Case 2
lift-cpl f c Y
  (uo2 (mkSigma Y0 (mkSigma belowY (mkSigma m (mkSigma i (mkSigma irange
    (mkSigma incomplY (mkSigma eqY0inv univG)))))))) =
  uo2 (mkSigma (cons (fcpl c) Y0)
        (mkSigma (mkSigma (LeD-refl (cpl c)) belowY)
          (mkSigma m (mkSigma (suc i) (mkSigma irange
            (mkSigma incomplY (mkSigma eqY0inv univ)))))))
  where
    univ : (X : FTup) -> Eq (length X) (length (cons (fcpl c) Y0)) ->
           Eq (getF (suc i) X) (getF (suc i) (cons (fcpl c) Y0)) ->
           LeFTup (del (suc i) (cons (fcpl c) Y0)) (del (suc i) X) ->
           Eq (f X) (fbot m)
    univ nil ()
    univ (cons x xs) lenX coordX delX =
      Eq-transport (\ w -> Eq (f (cons w xs)) (fbot m))
        (Eq-sym (fcpl-max c x (fst delX)))
        (univG xs (suc-inj lenX) coordX (snd delX))
-- Case 3
lift-cpl f c Y
  (uo3 (mkSigma Y0 (mkSigma belowY (mkSigma i (mkSigma eqinfY
    (mkSigma k (mkSigma eqY0 (mkSigma phi (mkSigma phiok univG))))))))) =
  uo3 (mkSigma (cons (fcpl c) Y0)
        (mkSigma (mkSigma (LeD-refl (cpl c)) belowY)
          (mkSigma (suc i) (mkSigma eqinfY (mkSigma k (mkSigma eqY0
            (mkSigma phi (mkSigma phiok univ))))))))
  where
    univ : (X : FTup) (p : Nat) -> Eq (length X) (length (cons (fcpl c) Y0)) ->
           LeN k p -> Eq (getF (suc i) X) (fbot p) ->
           LeFTup (del (suc i) (cons (fcpl c) Y0)) (del (suc i) X) ->
           Eq (f X) (fbot (phi p))
    univ nil p ()
    univ (cons x xs) p lenX pk coordX delX =
      Eq-transport (\ w -> Eq (f (cons w xs)) (fbot (phi p)))
        (Eq-sym (fcpl-max c x (fst delX)))
        (univG xs p (suc-inj lenX) pk coordX (snd delX))
