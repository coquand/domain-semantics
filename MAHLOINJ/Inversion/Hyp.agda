{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Inversion/Hyp.agda
--
-- The semantic facts used by inversion of typing (plan Lemma 18) and
-- subject reduction, as a record of hypotheses, to be discharged by
-- the model side of P3.
--
-- Only what is used is assumed:
--   * Pi- and Sigma-injectivity for TyEq   (subject reduction);
--   * a code U(f,g) is not equal, as a type, to a Pi, a Sigma or Nat
--     (inversion through the subsumption rule ty-sub).
-- In particular U(f,g) /= V is NOT assumed (V and the codes share a
-- code in the erased model); inversion never needs it.
-- Not assumed, and not needed: injectivity of U(f,g), and the other
-- disjointness facts between Pi, Sigma, Nat, V.
--
-- NOT assumable: any disjointness of Fhat / Ghat from the type heads.
-- By delta, Fhat f g A F = f A F : V, and f A F may beta-reduce to any
-- small type (e.g. f = \A F. Pi A F gives Fhat f g A F = Pi A F).
-- Fhat/Ghat never occur as the canonical type in an inversion lemma.
------------------------------------------------------------------------

module MAHLOINJ.Inversion.Hyp where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing

record InjHyp : Set where
  field
    Pi-inj  : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
              TyEq G (PiB A B) (PiB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
    Sig-inj : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
              TyEq G (SigmaB A B) (SigmaB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
    U-Pi    : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} ->
              TyEq G (Ucode f g) (PiB A B) -> Empty
    U-Sig   : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} ->
              TyEq G (Ucode f g) (SigmaB A B) -> Empty
    U-Nat   : {n : Num} {G : Ctx n} {f g : Expr n} -> TyEq G (Ucode f g) Nat -> Empty
