{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Hyp.agda
--
-- The only hypotheses of uniqueness / section / equivalence: Pi- and
-- Sigma-injectivity for Tarski type equality.  Inhabited by the Tarski
-- adequacy (domain-6c).  Nothing else is needed: no-confusion is
-- MAHLORT/TNoConf (hypothesis-free), and U-injectivity is never used
-- because T^ is unannotated.
------------------------------------------------------------------------

module MAHLORT.Hyp where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping

record TInj : Set where
  field
    Pi-inj  : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
              TyEq G (PiB A B) (PiB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
    Sig-inj : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
              TyEq G (SigmaB A B) (SigmaB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
