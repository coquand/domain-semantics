{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Wf.agda
--
-- Presupposition, first part: a type or a term lives in a well-formed
-- context, and the types of the variables of a well-formed context are
-- types.
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Wf where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken

mutual
  wfTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx G
  wfTy (isty-V w) = w
  wfTy (isty-el h) = wfTm h
  wfTy (isty-Pi hA hB) = wfTy hA
  wfTy (isty-Sigma hA hB) = wfTy hA

  wfTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> WfCtx G
  wfTm (ty-var w) = w
  wfTm (ty-conv h q) = wfTm h
  wfTm (ty-sub h) = wfTm h
  wfTm (ty-Pi u hA hB) = wfTm hA
  wfTm (ty-Sigma u hA hB) = wfTm hA
  wfTm (ty-Nat-V w) = w
  wfTm (ty-Nat-U h) = wfTm h
  wfTm (ty-Ucode hf hg) = wfTm hf
  wfTm (ty-Fhat hf hg hA hB) = wfTm hf
  wfTm (ty-Ghat hf hg hA hB hc) = wfTm hf
  wfTm (ty-Lam hA hB ht) = wfTy hA
  wfTm (ty-App hA hB ht ha) = wfTy hA
  wfTm (ty-Pair hA hB ht hu) = wfTy hA
  wfTm (ty-Fst hA hB ht) = wfTy hA
  wfTm (ty-Snd hA hB ht) = wfTy hA
  wfTm (ty-Zero w) = w
  wfTm (ty-Suc h) = wfTm h
  wfTm (ty-Rec hC hz hs hk) = wfTm hz

lookupTy : {n : Num} {G : Ctx n} -> WfCtx G -> (i : Fin n) -> IsType G (lookup G i)
lookupTy (wf-extend hA) fzero = wkTy hA hA
lookupTy (wf-extend hA) (fsuc i) = wkTy hA (lookupTy (wfTy hA) i)

-- some closed types
NatTy : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G Nat
NatTy w = isty-el (ty-Nat-V w)
