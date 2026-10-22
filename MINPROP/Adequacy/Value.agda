{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MINPROP.Adequacy.Value.agda
--
-- The VALUE-ONLY fundamental theorem, as a clean proof by CASE ANALYSIS on
-- the derivation + STRUCTURAL INDUCTION on its subderivations:
--
--   adequacySub2     : HasType G M A   -> Val2   H (sM)      (sA) u a
--   adequacyConvSub2 : HasType G M A   -> EqVal2 H (sM)(s'M) (sA) u a
--   adequacyEqSub2   : ConvTm  G M N A -> EqVal2 H (sM)(sN)  (sA) u a
--
-- Every informative clause dispatches to a per-case combinator that lives
-- in its OWN file and is parameterised by the recursors / IH values.  The
-- only recursive calls in this mutual block's SCC are the three functions
-- applied to SUBDERIVATIONS (or to the conv-Pi premises dA/dB/dB', which are
-- now genuine subterms) -- so the block is structural.
--
-- This replaces the monolithic MINPROP.Adequacy as the source of the
-- value-only recursors used by the bundled driver and by PiInjectivity.
------------------------------------------------------------------------

module MINPROP.Adequacy.Value where

import MINPROP.Domain.Basic as S
open S using (Nat ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode)
open import MINPROP.Syntax.Raw using (Expr ; U ; Prop ; Pi ; Lam ; App ; Fin ; Sub ; substExpr ; subst1)
open import MINPROP.Domain.Kernel using (LeCode ; LeCode-refl ; FinMem ; FinMem-a-in-U)
open import MINPROP.Model.Eval using (EnvApprox ; EvalRel ; EvalRel-coh ; CoherentEnv)
open import MINPROP.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-U ; ty-Pi ; ty-Lam ; ty-App ; ty-conv ;
  ty-Prop ; ty-Prop-U ; ty-Pi-Prop ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Pi ; conv-beta ;
  conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Prop ; conv-Prop-U ; conv-Pi-Prop ; conv-U-Prop)
open import MINPROP.Model.Soundness using (convSound ; convSound-inv)
open import MINPROP.Model.SoundnessLemmas using (Fits)
open import MINPROP.Validity.Core using (FinMem-Coherent)
open import MINPROP.Syntax.Substitution using (WtSub ; WtConvSub)
open import MINPROP.Adequacy.HeadRed
open import MINPROP.Adequacy.Bundle
open import MINPROP.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import MINPROP.Adequacy.App using (adequacySub2-App ; adequacyV-ty-App)
open import MINPROP.Adequacy.Lam using (adequacyV-ty-Lam)
open import MINPROP.Adequacy.Beta using (adequacyEqSub2-beta)
open import MINPROP.Adequacy.Funext using (adequacyEqSub2-funext)
open import MINPROP.Adequacy.FunCore using (adequacyEqSub2-App-fun)
open import MINPROP.Adequacy.ArgCore using (adequacyEqSub2-App-arg)
open import MINPROP.Adequacy.VE using (AdqE1)
open import MINPROP.Adequacy.Prop using (valProp-PU ; adq-Prop-U ; adqconv-Prop-U ; adqeq-Prop-U ;
  adq-U-to-Prop ; adqconv-U-to-Prop ; adqeq-U-to-Prop ;
  adqconv-ty-Pi-full ; adqeq-conv-Pi-full ; adqeq-conv-Prop)

mutual

  adequacySub2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {M A : Expr g} ->
    HasType G M A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (substExpr sigma M) (substExpr sigma A) u a
  adequacySub2 (ty-var {i = i} _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    vs i u (fst hu) (snd hu) a evA fm
  adequacySub2 (ty-U _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    valU-UU wfH u a (snd hu) (snd evA) fm
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in Val2-EqValTy2-fwd u UCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu PropCode evA' fm
        aU    = FinMem-a-in-U u PropCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 PropCode aU eqAB
    in Val2-EqValTy2-fwd u PropCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacySub2 (ty-conv {A = A} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in Val2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty val
  adequacySub2 (ty-Prop _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    valProp-PU wfH u a (snd hu) (snd evA) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adq-Prop-U d (adequacySub2 d) sigma rho crho vs fits wtsub wfH u hu a evA fm
  adequacySub2 (ty-Pi-Prop {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adq-U-to-Prop IH-PiU sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      IH-PiU : Adq G (Pi A B) U
      IH-PiU {h} {H} = adequacy-ty-Pi-full {h = h} {H = H} d1 (ty-Prop-U d2) (adequacySub2 d1)
                         (adq-Prop-U d2 (adequacySub2 d2)) (adqconv-Prop-U d2 (adequacyConvSub2 d2))
  adequacySub2 (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    IH-Pi sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      IH-Pi : Adq G (Pi A B) U
      IH-Pi {h} {H} = adequacy-ty-Pi-full {h = h} {H = H} d1 d2 (adequacySub2 d1) (adequacySub2 d2) (adequacyConvSub2 d2)
  adequacySub2 (ty-Lam {G = G} {A = A} {B = B} {M = M} d1 d2 d3) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    IH-Lam sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      IH-Pi : Adq G (Pi A B) U
      IH-Pi {h} {H} = adequacy-ty-Pi-full {h = h} {H = H} d1 d2 (adequacySub2 d1) (adequacySub2 d2) (adequacyConvSub2 d2)
      IH-Lam : Adq G (Lam A M) (Pi A B)
      IH-Lam {h} {H} = adequacy-ty-Lam-full {h = h} {H = H} d1 d2 d3 (adequacySub2 d1) IH-Pi (adequacySub2 d3) (adequacyConvSub2 d3)
  adequacySub2 (ty-App {f = f} {a = a} dA dB df da) sigma rho crho vs fits wtsub wfH u hu a' evA fm =
    adequacySub2-App dA dB df da (adequacySub2 df) (adequacySub2 da) (adequacySub2 dB) sigma rho crho vs fits wtsub wfH
      u (EvalRel-coh (App f a) rho u hu) hu a' evA fm

  adequacyConvSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a
  adequacyConvSub2 (ty-var {i = i} _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    vcs i u (fst hu) (snd hu) a evA fm
  adequacyConvSub2 (ty-U _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (valU-UU wfH u a (snd hu) (snd evA) fm)
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in EqVal2-EqValTy2-fwd u UCode tt eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode evA' fm
        aU    = FinMem-a-in-U u PropCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 PropCode aU eqAB
    in EqVal2-EqValTy2-fwd u PropCode tt eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl g) evA fm = tt
  adequacyConvSub2 (ty-conv {A = A} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty ih
  adequacyConvSub2 (ty-Prop _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (valProp-PU wfH u a (snd hu) (snd evA) fm)
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adqconv-Prop-U d (adequacyConvSub2 d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm
  adequacyConvSub2 (ty-Pi-Prop {G = G} {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adqconv-U-to-Prop IHc-PiU sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm
    where
      IHc-PiU : AdqConv G (Pi A B) U
      IHc-PiU {h} {H} = adqconv-ty-Pi-full {G = G} d1 (ty-Prop-U d2) (adequacyConvSub2 d1)
                          (adqconv-Prop-U d2 (adequacyConvSub2 d2)) {h = h} {H = H}
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode evA fm =
    adequacyV-ty-Pi d1 d2 (adequacyConvSub2 d1) (adequacyConvSub2 d2)
      sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f0 hu evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu UCode evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Lam {G = G} {A = A} {B = B} {M = M} d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (PiCode b f0) evA fm =
    adequacyV-ty-Lam d1 d2 d3 (adequacySub2 d1) IH-Lam (adequacyConvSub2 d1) (adequacyConvSub2 d2) (adequacyConvSub2 d3)
      sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH g0 hu b f0 evA fm
    where
      IH-Pi : Adq G (Pi A B) U
      IH-Pi {h} {H} = adequacy-ty-Pi-full {h = h} {H = H} d1 d2 (adequacySub2 d1) (adequacySub2 d2) (adequacyConvSub2 d2)
      IH-Lam : Adq G (Lam A M) (Pi A B)
      IH-Lam {h} {H} = adequacy-ty-Lam-full {h = h} {H = H} d1 d2 d3 (adequacySub2 d1) IH-Pi (adequacySub2 d3) (adequacyConvSub2 d3)
  adequacyConvSub2 (ty-App dA dB df da) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyV-ty-App dA dB df da (adequacySub2 da) (adequacySub2 dB) (adequacyConvSub2 df) (adequacyConvSub2 da)
      sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

  adequacyEqSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a
  adequacyEqSub2 (conv-refl d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 d sigma rho crho vs fits wtsub wfH u hu a evA fm)
  adequacyEqSub2 (conv-sym {A = Asrc} d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN = convSound-inv d rho fits u hu
        cu' = FinMem-Coherent u a fm
        ca  = EvalRel-coh Asrc rho a evA
        eq  = adequacyEqSub2 d sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-sym u a cu' ca eq
  adequacyEqSub2 (conv-trans {A = A} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN = convSound d1 rho fits u hu
        cu  = FinMem-Coherent u a fm
        ca  = EvalRel-coh A rho a evA
        eq1 = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu a evA fm
        eq2 = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-trans u a cu ca eq1 eq2
  adequacyEqSub2 (conv-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u UCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in EqVal2-EqValTy2-fwd u UCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu PropCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u PropCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 PropCode aU eqAB
    in EqVal2-EqValTy2-fwd u PropCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacyEqSub2 (conv-conv {A = A} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty eq
  adequacyEqSub2 (conv-beta d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-beta d1 d2 d3 d4 (adequacySub2 d3) (adequacySub2 d4)
      sigma rho crho vs fits wtsub wfH u hu a evA fm
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f) hu Bot evA ()
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f) hu (FunEl _) evA ()
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f) hu (PiCode _ _) evA ()
  adequacyEqSub2 (conv-Pi dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f) hu UCode evA fm =
    adequacyEqSub2-Pi-core d1 d2 (adequacySub2 dA) (adequacyEqSub2 d1) (adequacyEqSub2 d2)
      (adequacyConvSub2 dB) (adequacyConvSub2 dB')
      sigma rho crho vs fits wtsub wfH b f hu evA fm
  adequacyEqSub2 (conv-Prop {N = N} dA dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adqeq-conv-Prop {N = N} dA dM sigma rho crho vs fits wtsub wfH u hu a evA fm
  adequacyEqSub2 (conv-Prop-U {N = N} d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adqeq-Prop-U {N = N} d (adequacyEqSub2 d) sigma rho crho vs fits wtsub wfH u hu a evA fm
  adequacyEqSub2 (conv-Pi-Prop {G = G} {A = A} {A' = A'} {B = B} {B' = B'} dA dB dB' d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adqeq-U-to-Prop {N = Pi A' B'} IHe-PiU sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      IHe-PiU : AdqE1 G (Pi A B) (Pi A' B') U
      IHe-PiU {h} {H} = adqeq-conv-Pi-full {G = G} d1 (conv-Prop-U d2) (adequacySub2 dA) (adequacyEqSub2 d1)
                          (adqeq-Prop-U d2 (adequacyEqSub2 d2))
                          (adqconv-Prop-U dB (adequacyConvSub2 dB)) (adqconv-Prop-U dB' (adequacyConvSub2 dB'))
                          {h = h} {H = H}
  adequacyEqSub2 (conv-U-Prop {B = B} dA dB d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adqeq-U-to-Prop {N = B} (adequacyEqSub2 d) sigma rho crho vs fits wtsub wfH u hu a evA fm
  adequacyEqSub2 (conv-funext dA d df dg) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH
      (adequacySub2 df) (adequacySub2 dg) (adequacyEqSub2 d) (adequacySub2 dA) u hu a evA fm
  adequacyEqSub2 (conv-App-fun dA dB dff' da) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH
      (adequacySub2 da) (adequacySub2 dB) (adequacyEqSub2 dff') u hu a evA fm
  adequacyEqSub2 (conv-App-arg dA dB df daa') sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH
      (adequacySub2 df) (adequacySub2 dB) (adequacyEqSub2 daa') u hu a evA fm
