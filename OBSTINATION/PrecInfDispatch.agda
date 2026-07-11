{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfDispatch
--
-- Primitive recursion at the infinite first argument, top-level glue
-- (min1.pdf p.3).  Read off  k0 = height of h's approximant at coordinate
-- 1 of  Q = (S^w b, S^w b, Y),  then decide  S^{k0}(bot) <= u_{k0}:
--
--   * NO  -> first principal case (finite Kleene limit)      -- PrecInfFirst
--   * YES -> second principal case (recursion reaches k0)     -- PrecInfSecond
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfDispatch where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Refine using (Below-length ; get-inf-in-range)
open import OBSTINATION.USeq using (uSeq)
open import OBSTINATION.PrecInfExtract using (approx ; approx-below ; below-inf-fbot)
open import OBSTINATION.PrecInfFirst using (first-principal)
open import OBSTINATION.PrecInfSecond using (second-principal)
open import OBSTINATION.PrecFun using (RecData ; PF)

module _ (rd : RecData) where
  open RecData rd

  prop1-prec-inf : (Y : Tup) ->
    UO (PF G H) (cons inf Y)
  prop1-prec-inf Y = route (LeD-dec (bot k0) (uSeq rd Y k0))
    where
      Q : Tup
      Q = cons inf (cons inf Y)
      uQ : UO (H) Q
      uQ = uoh Q
      belB0 : Below (approx uQ) Q
      belB0 = approx-below uQ
      irng1 : LeN (suc (suc zero)) (length (approx uQ))
      irng1 = Eq-transport (\ n -> LeN (suc (suc zero)) n) (Eq-sym (Below-length belB0))
                (get-inf-in-range (suc zero) Q refl)
      ke = below-inf-fbot (suc zero) (approx uQ) Q belB0 refl irng1
      k0 : Nat
      k0 = fst ke
      eqk0 : Eq (getF (suc zero) (approx uQ)) (fbot k0)
      eqk0 = snd ke

      route : Dec (LeD (bot k0) (uSeq rd Y k0)) -> UO (PF G H) (cons inf Y)
      route (yes le) = second-principal rd Y uQ k0 eqk0 le
      route (no nle) = first-principal rd Y k0 nle
