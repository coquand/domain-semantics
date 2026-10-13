{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/All.agda
--
-- (T3), soundness half: the untyped conversion algorithm of plan
-- Sec. "Soundness of the conversion algorithm" (lfsigma Sec. 3 with
-- iota, delta, constructors, rec) is sound for conversion of terms
-- (Thm algsound) and of types.  Unconditional (uses MAHLOINJ/Final).
--
--   Alg      the algorithm, as judgements
--   Eval     soundness of weak-head evaluation (constructive split at
--            delta steps by derivation data)
--   Sound    the simultaneous induction (see its header for the
--            corrected proof of Thm algsound)
------------------------------------------------------------------------

module MAHLOINJ.Algo.All where

open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Algo.Alg public
open import MAHLOINJ.Algo.Sound using (sEq ; sTy)

algsound : {n : Num} {G : Ctx n} {t t' C : Expr n} ->
  HasType G t C -> HasType G t' C -> AlgEq t t' -> ConvTm G t t' C
algsound ht ht' R = sEq R ht ht'

algsound-ty : {n : Num} {G : Ctx n} {A A' : Expr n} ->
  IsType G A -> IsType G A' -> AlgEq A A' -> TyEq G A A'
algsound-ty iA iA' R = sTy R iA iA'
