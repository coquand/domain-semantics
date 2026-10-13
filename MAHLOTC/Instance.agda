{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Instance.agda
--
-- Closing (T3): the hypotheses TCHyp of the type checker are inhabited
-- by domain-6c's decidable conversion (MAHLOALG/T3.agda) and InjHyp
-- (MAHLOINJ/Final.agda).  So type checking for the bidirectional
-- fragment is decidable relative to the fixed point only (and hence to
-- PFix, via Concrete/Sound.fixpoint-of-pfix).
------------------------------------------------------------------------

open import MAHLO.Fixpoint using (Fixpoint)
open import MAHLO.Concrete.Instance using (concreteTM)

module MAHLOTC.Instance (Fx : Fixpoint concreteTM) where

open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOTC.Base
import MAHLO.Concrete.DecEq as CD
import MAHLOALG.T3 Fx as T3
open import MAHLOINJ.Final using (injHyp)

private
  dec : {P : Set} -> CD.Dec P -> Dec P
  dec (CD.yes p) = yes p
  dec (CD.no k) = no k

tcHyp : TCHyp
tcHyp = record
  { inj = injHyp
  ; decTyEq = \ hA hA' -> dec (T3.decTyEq hA hA')
  ; decPi = \ hC -> dec (T3.decPi hC)
  ; decSig = \ hC -> dec (T3.decSig hC)
  ; decU = \ hC -> dec (T3.decU hC) }

open import MAHLOTC.Frag
open import MAHLOTC.Check tcHyp public using (decHasType ; decHasType' ; decIsType ; decWfCtx)
