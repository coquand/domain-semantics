{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/T3PFix.agda
--
-- (T3) for conversion relative to the single principle PFix of the
-- plan (MAHLO/FixHyp): PFix gives the fixed point of Gamma
-- (fixpoint-of-pfix), and MAHLOALG/T3 is instantiated with it.
------------------------------------------------------------------------

open import MAHLO.Concrete.Instance using (concreteTM)
open import MAHLO.FixHyp concreteTM using (PFix ; fixpoint-of-pfix)

module MAHLOALG.T3PFix (P0 : PFix) where

open import MAHLOALG.T3 (fixpoint-of-pfix P0) public
