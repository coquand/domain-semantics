{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Build
--
-- Bounded list construction:  buildB r h  =  < h 0 , h 1 , ... , h (r-1) >
-- where the family h is only defined below the bound r.
--
-- This is how a tuple of r results is assembled from the r verdicts of a
-- joint obstination witness (`PropertyVec.UOfam`), whose components are
-- given as  (i : Nat) -> LeN (suc i) r -> ...  .  The recursion shifts the
-- family, exactly as in `UOfam-build`, so no Fin / Vec is needed.
--
-- Spartan: plain Lists indexed into by Nat, no indexed inductive types.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Build where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples

------------------------------------------------------------------------
-- The construction and its length
------------------------------------------------------------------------

buildB : {X : Set} (r : Nat) -> ((i : Nat) -> LeN (suc i) r -> X) -> List X
buildB zero     h = nil
buildB (suc r') h = cons (h zero tt) (buildB r' (\ i lt -> h (suc i) lt))

length-buildB : {X : Set} (r : Nat) (h : (i : Nat) -> LeN (suc i) r -> X) ->
  Eq (length (buildB r h)) r
length-buildB zero     h = refl
length-buildB (suc r') h = Eq-cong suc (length-buildB r' (\ i lt -> h (suc i) lt))

------------------------------------------------------------------------
-- Transfer of the pointwise order and of pointwise equality
--
-- Stated at D, which is where they are used (the Kleene sequence of the
-- mutual iteration lives in Tup = List D).
------------------------------------------------------------------------

buildB-LeTup : (r : Nat) (h1 h2 : (i : Nat) -> LeN (suc i) r -> D) ->
  ((i : Nat) (lt : LeN (suc i) r) -> LeD (h1 i lt) (h2 i lt)) ->
  LeTup (buildB r h1) (buildB r h2)
buildB-LeTup zero     h1 h2 pw = tt
buildB-LeTup (suc r') h1 h2 pw =
  mkSigma (pw zero tt)
    (buildB-LeTup r' (\ i lt -> h1 (suc i) lt) (\ i lt -> h2 (suc i) lt)
      (\ i lt -> pw (suc i) lt))

buildB-Eq : {X : Set} (r : Nat) (h1 h2 : (i : Nat) -> LeN (suc i) r -> X) ->
  ((i : Nat) (lt : LeN (suc i) r) -> Eq (h1 i lt) (h2 i lt)) ->
  Eq (buildB r h1) (buildB r h2)
buildB-Eq zero     h1 h2 pw = refl
buildB-Eq (suc r') h1 h2 pw =
  cons-eqL (pw zero tt)
    (buildB-Eq r' (\ i lt -> h1 (suc i) lt) (\ i lt -> h2 (suc i) lt)
      (\ i lt -> pw (suc i) lt))
  where
    cons-eqL : {X : Set} {x y : X} {A B : List X} ->
               Eq x y -> Eq A B -> Eq (cons x A) (cons y B)
    cons-eqL refl refl = refl
