{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Adequacy3.agda
--
-- Thin wrapper around Adequacy2: produces Validity3's Val2/EqVal2
-- (= Pair HasType/ConvTm with Validity2's Val2/EqVal2).
--
-- The inner layer (Adequacy2) is completely unchanged.
-- This file just pairs the HasType/ConvTm from the substitution lemma
-- with the inner adequacy output.
--
-- 0 postulates.
------------------------------------------------------------------------

module Adequacy3 where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ;
              fst ; snd ; Pair ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun)
open import RawSyntax using (Expr ; Sub ; substExpr)
open import TypingRules using (Ctx ; HasType ; ConvTm ; WfCtx)
open import RawSemantics using (EnvApprox ; EvalRel ; CoherentEnv)
open import SubstitutionLemma using (WtSub ; subst-HasType ; subst-ConvTm ;
  typing-ConvTm ; typing-WfCtx ; WtConvSub ; subst-ConvTm-cross)
open import LemmaForTS using (Fits)
open import PaperSemantics using (FinMem)

-- Import inner layer
import Adequacy2 as A2
open A2 using (ValidSub2 ; ValidSub2-empty ; idSub-WtSub ; ValidConvSub2)

-- Import both validity layers
import Validity2 as V2
import Validity3 as V3

------------------------------------------------------------------------
-- adequacySub3: produces V3.Val2 = Pair HasType (V2.Val2)
------------------------------------------------------------------------

adequacySub3 : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M A : Expr g} ->
  HasType G M A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  V3.Val2 H (substExpr sigma M) (substExpr sigma A) u a
adequacySub3 d sigma rho crho vs fits wtsub wfH u hu a evA fm =
  mkSigma (subst-HasType wtsub wfH d)
          (A2.adequacySub2 d sigma rho crho vs fits wtsub wfH u hu a evA fm)

------------------------------------------------------------------------
-- adequacyEqSub3: produces V3.EqVal2 = Pair ConvTm (V2.EqVal2)
------------------------------------------------------------------------

adequacyEqSub3 : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M N A : Expr g} ->
  ConvTm G M N A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  V3.EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a
adequacyEqSub3 d sigma rho crho vs fits wtsub wfH u hu a evA fm =
  mkSigma (subst-ConvTm wtsub wfH d)
          (A2.adequacyEqSub2 d sigma rho crho vs fits wtsub wfH u hu a evA fm)

------------------------------------------------------------------------
-- adequacyConvSub3: cross-substitution, produces V3.EqVal2
------------------------------------------------------------------------

adequacyConvSub3 : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M A : Expr g} ->
  HasType G M A ->
  (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' ->
  WtConvSub H G sigma sigma' ->
  WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  V3.EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a
adequacyConvSub3 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  mkSigma (subst-ConvTm-cross d wtsub wtsub' wcs wfH)
          (A2.adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm)
