{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- Reduction.agda
--
-- Axioms for contextual reduction (Red).
--
-- Red G M N A means M reduces to N at type A in context G.
-- These are postulated properties used by Validity and Adequacy.
------------------------------------------------------------------------

module Reduction where

import Basic as S
open S using (Nat ; suc ; Pair ; Eq)
open import RawSyntax using (Expr ; Pi ; App ; Lam ; U ; wkExpr ; subst1 ;
  Sub ; substExpr)
open import TypingRules using (Ctx ; extend ; ConvTm)

postulate
  Red : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set
  Red-wk : {n : Nat} {G : Ctx n} {M N A C : Expr n} -> Red G M N A ->
    Red (extend G C) (wkExpr M) (wkExpr N) (wkExpr A)
  red-to-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    Red G M N A -> ConvTm G M N A
  -- Reflexivity
  Red-refl : {n : Nat} {G : Ctx n} {M A : Expr n} -> Red G M M A
  -- Transitivity
  Red-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n} ->
    Red G M N A -> Red G N P A -> Red G M P A
  -- Beta expansion: if (subst1 M N) reduces to P, then App (Lam A M) N does too
  Red-beta-expand : {n : Nat} {G : Ctx n} {A : Expr n}
    {M : Expr (suc n)} {N P T : Expr n} ->
    Red G (subst1 M N) P T -> Red G (App (Lam A M) N) P T
  -- Pi-injectivity: Red G (Pi A B) (Pi A' B') U implies A = A' and B = B'
  Red-Pi-inj : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {B B' : Expr (suc n)} ->
    Red G (Pi A B) (Pi A' B') U ->
    Pair (Eq A A') (Eq B B')
  -- Conversion to Red
  Red-from-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A -> Red G M N A
  -- Substitution
  Red-subst : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {M N A : Expr n} (sigma : Sub m n) ->
    Red G M N A -> Red H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A)
