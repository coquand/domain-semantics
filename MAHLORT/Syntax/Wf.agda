{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Wf.agda
--
-- Every judgement of MAHLORT/TarskiTyping has a well-formed context;
-- the types of the context entries are types.  Port of MAHLOINJ.
------------------------------------------------------------------------

module MAHLORT.Syntax.Wf where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken

mutual
  wfTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx G
  wfTy (isty-V w) = w
  wfTy (isty-ElV h) = wfTm h
  wfTy (isty-TyU hf hg) = wfTm hf
  wfTy (isty-ElU h) = wfTm h
  wfTy (isty-Pi hA hB) = wfTy hA
  wfTy (isty-Sigma hA hB) = wfTy hA
  wfTy (isty-Nat w) = w

  wfTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> WfCtx G
  wfTm (ty-var w) = w
  wfTm (ty-conv h q) = wfTm h
  wfTm (ty-Lam hA hB ht) = wfTy hA
  wfTm (ty-App hA hB ht ha) = wfTy hA
  wfTm (ty-Pair hA hB ha hb) = wfTy hA
  wfTm (ty-Fst hA hB ht) = wfTy hA
  wfTm (ty-Snd hA hB ht) = wfTy hA
  wfTm (ty-Zero w) = w
  wfTm (ty-Suc h) = wfTm h
  wfTm (ty-Rec hC hz hs hk) = wfTm hz
  wfTm (ty-PiV ha hb) = wfTm ha
  wfTm (ty-SigV ha hb) = wfTm ha
  wfTm (ty-NatV w) = w
  wfTm (ty-UV hf hg) = wfTm hf
  wfTm (ty-PiU ha hb) = wfTm ha
  wfTm (ty-SigU ha hb) = wfTm ha
  wfTm (ty-NatU hU) = wfTy hU
  wfTm (ty-Fhat hf hg ha hb) = wfTm hf
  wfTm (ty-Ghat hf hg ha hb hc) = wfTm hf
  wfTm (ty-That h) = wfTm h

lookupTy : {n : Num} {G : Ctx n} -> WfCtx G -> (i : Fin n) -> IsType G (lookup G i)
lookupTy (wf-extend hA) fzero = wkTy hA hA
lookupTy (wf-extend hA) (fsuc i) = wkTy hA (lookupTy (wfTy hA) i)

NatTy : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G Nat
NatTy w = isty-Nat w

-- the subuniverse of a code:  IsType (TyU f g)  gives  f : OpF, g : OpG f
invTyU : {n : Num} {G : Ctx n} {f g : Expr n} -> IsType G (TyU f g) ->
         HasType G f OpF * HasType G g (OpG f)
invTyU (isty-TyU hf hg) = hf , hg
