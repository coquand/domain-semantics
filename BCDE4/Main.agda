{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Main
--
-- The results with the level-code parameter discharged: the level
-- codes  D : LDecAll  are built from the Bezem–Coquand decision
-- procedure for the level theory (BCDE4.LC.Decide.ldecAll), so the
-- adequacy theorem and the injectivity corollaries hold outright.
------------------------------------------------------------------------

module BCDE4.Main where

open import BCDE4.Basic using (Pair)
open import BCDE4.Levels using (LoopFree ; LExpr ; Valid)
open import BCDE4.LC.Decide using (ldecAll)
open import BCDE4.RussellSyntax using (Expr ; Pi ; LPi ; U)
open import BCDE4.RussellTyping
open import BCDE4.Dom.Basic using (Nat ; suc)
import BCDE4.Adeq.Stmt ldecAll as St
import BCDE4.Adeq.Driver ldecAll as Dr
import BCDE4.PiInjectivityR ldecAll as PI

-- the fundamental theorem, at every level substitution and at the identity
adequacy : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> St.Adq G M A
adequacy = Dr.adqTm0

conv-adequacy : {g : Nat} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> St.AdqE1 G M N A
conv-adequacy = Dr.adqCTm0

-- Π-, [α]- and U-injectivity in loop-free contexts
PiInj : {n : Nat} {G : Ctx n} {C0 C1 : Expr n} {B0 B1 : Expr (suc n)} ->
  LoopFree (lctx G) -> ConvTy G (Pi C0 B0) (Pi C1 B1) ->
  Pair (ConvTy G C0 C1) (ConvTy (extend G C0) B0 B1)
PiInj = PI.PiInj-R

LPiInj : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
  LoopFree (lctx G) -> ConvTy G (LPi A0) (LPi A1) -> ConvTy (addL G) A0 A1
LPiInj = PI.LPiInj-R

UInj : {n : Nat} {G : Ctx n} {l m : LExpr} ->
  LoopFree (lctx G) -> ConvTy G (U l) (U m) -> Valid (lctx G) l m
UInj = PI.UInj-R
