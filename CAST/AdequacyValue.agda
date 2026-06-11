{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.AdequacyValue.agda
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
-- This replaces the monolithic CAST.Adequacy as the source of the
-- value-only recursors used by the bundled driver and by PiInjectivity.
------------------------------------------------------------------------

module CAST.AdequacyValue where

import CAST.Basic as S
open S using (Nat ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode)
open import CAST.RawSyntax using (Expr ; U ; Pi ; Lam ; App ; Fin ; Sub ; substExpr ; subst1)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ; FinMem-a-in-U ; FinMem-coh-u ; Coherent)
open import CAST.RawSemantics using (EnvApprox ; EvalRel ; EvalRel-coh ; EvalRel-down ; CoherentEnv)
open import CAST.TypingRules using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-U ; ty-Pi ; ty-Lam ; ty-App ; ty-conv ;
  ty-Id ; ty-refl ; ty-sym ; ty-pi1 ; ty-pi2 ; ty-cast ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Pi ; conv-beta ;
  conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Id ; conv-cast-refl ; conv-Id-irr ; conv-cast-cong ; conv-pi1 ; conv-pi2 ;
  conv-cast-Pi)
open import CAST.ValidityPublic using (Val2-Bot ; EqVal2-Bot)
open import CAST.TypingSemantics using (convSound ; convSound-inv ; theorem1 ; convSound')
open import CAST.LemmaForTS using (Fits ; InvConv)
open import CAST.Validity using (FinMem-Coherent)
open import CAST.SubstitutionLemma using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm)
open import CAST.AdequacyCastDriver using (castVal-pub ; castEqVal-pub ; castRefl-pub)
open import CAST.AdequacyCastV using (adequacyEqSub2-coePi)
open import CAST.AdequacyHeadRed
open import CAST.AdequacyBundle
open import CAST.AdequacyPi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import CAST.AdequacyApp using (adequacySub2-App ; adequacyV-ty-App)
open import CAST.AdequacyLam using (adequacyV-ty-Lam)
open import CAST.AdequacyBeta using (adequacyEqSub2-beta)
open import CAST.AdequacyFunext using (adequacyEqSub2-funext)
open import CAST.AdequacyFunCore using (adequacyEqSub2-App-fun)
open import CAST.AdequacyArgCore using (adequacyEqSub2-App-arg)

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
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacySub2 (ty-conv {A = A} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in Val2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty val
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
  -- ty-conv at type-code IdCode: Val2 there is Top
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (IdCode _ _) evA fm = tt
  -- Id A B : U.  value Bot → trivial; value IdCode → Top (fm forces type UCode)
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu Bot evA ()
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu UCode evA fm = tt
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (FunEl _) evA ()
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (PiCode _ _) evA ()
  adequacySub2 (ty-Id _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (IdCode _ _) evA ()
  -- proofs refl/sym/pi1/pi2: value forced to Bot
  adequacySub2 (ty-refl _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
  adequacySub2 (ty-refl _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-refl _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-refl _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-refl _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  adequacySub2 (ty-sym _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
  adequacySub2 (ty-sym _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-sym _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-sym _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-sym _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  adequacySub2 (ty-pi1 _ _ _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
  adequacySub2 (ty-pi1 _ _ _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-pi1 _ _ _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-pi1 _ _ _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-pi1 _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  adequacySub2 (ty-pi2 _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
  adequacySub2 (ty-pi2 _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-pi2 _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-pi2 _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-pi2 _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  -- cast:  cast A B p M : B.  The guarded value u ≤ v (an M-value); re-type v
  -- in A via theorem1 to (v', c), apply the public castVal wrapper.
  adequacySub2 (ty-cast {A = A} {B = B} {p = p} {M = M} dA dB dp dM) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    castVal-pub _ _ _ _ u v' c a le-u-v' fm fm-v'-c cohv'
      (subst-HasType wtsub wfH dA) (subst-HasType wtsub wfH dB)
      (subst-HasType wtsub wfH dp) (subst-HasType wtsub wfH dM)
      valtyA valtyB IH-M
    where
      cu     = fst hu
      v      = fst (snd hu)
      le-u-v = fst (snd (snd hu))
      evM-v  = fst (snd (snd (snd hu)))
      typedM = theorem1 dM rho fits v evM-v
      v'      = fst typedM
      c       = fst (snd typedM)
      le-v-v' = fst (snd (snd typedM))
      evM-v'  = fst (snd (snd (snd typedM)))
      fm-v'-c = fst (snd (snd (snd (snd typedM))))
      evA-c   = snd (snd (snd (snd (snd typedM))))
      cohv'   = FinMem-coh-u v' c fm-v'-c
      le-u-v' = LeCode-trans u v v' cu (EvalRel-coh M rho v evM-v) cohv' le-u-v le-v-v'
      cU      = FinMem-a-in-U v' c fm-v'-c
      aU      = FinMem-a-in-U u a fm
      evU     = mkSigma tt (LeCode-refl UCode tt)
      IH-M    = adequacySub2 dM sigma rho crho vs fits wtsub wfH v' evM-v' c evA-c fm-v'-c
      valtyA  = Val2-U-to-ValTy2 c cU (adequacySub2 dA sigma rho crho vs fits wtsub wfH c evA-c UCode evU cU)
      valtyB  = Val2-U-to-ValTy2 a aU (adequacySub2 dB sigma rho crho vs fits wtsub wfH a evA UCode evU aU)

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
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl g) evA fm = tt
  adequacyConvSub2 (ty-conv {A = A} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty ih
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
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (IdCode _ _) evA fm = tt
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) hu Bot evA ()
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) hu UCode evA fm = tt
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Id _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) hu (IdCode _ _) evA ()
  adequacyConvSub2 (ty-refl _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-refl _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-refl _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-refl _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-refl _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) () a evA fm
  adequacyConvSub2 (ty-sym _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-sym _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-sym _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-sym _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-sym _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) () a evA fm
  adequacyConvSub2 (ty-pi1 _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-pi1 _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-pi1 _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-pi1 _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-pi1 _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) () a evA fm
  adequacyConvSub2 (ty-pi2 _ _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2 (ty-pi2 _ _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-pi2 _ _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-pi2 _ _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-pi2 _ _ _ _ _ _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _) () a evA fm
  adequacyConvSub2 (ty-cast {A = A} {B = B} {p = p} {M = M} dA dB dp dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    castEqVal-pub _ _ _ _ _ _ _ _ u v' c a le-u-v' fm fm-v'-c cohv'
      (subst-HasType wtsub wfH dA) (subst-HasType wtsub wfH dB)
      (subst-HasType wtsub wfH dp) (subst-HasType wtsub wfH dM)
      (subst-HasType wtsub' wfH dA) (subst-HasType wtsub' wfH dB)
      (subst-HasType wtsub' wfH dp) (subst-HasType wtsub' wfH dM)
      eqtyA eqtyB IH-M
    where
      cu     = fst hu
      v      = fst (snd hu)
      le-u-v = fst (snd (snd hu))
      evM-v  = fst (snd (snd (snd hu)))
      typedM = theorem1 dM rho fits v evM-v
      v'      = fst typedM
      c       = fst (snd typedM)
      le-v-v' = fst (snd (snd typedM))
      evM-v'  = fst (snd (snd (snd typedM)))
      fm-v'-c = fst (snd (snd (snd (snd typedM))))
      evA-c   = snd (snd (snd (snd (snd typedM))))
      cohv'   = FinMem-coh-u v' c fm-v'-c
      le-u-v' = LeCode-trans u v v' cu (EvalRel-coh M rho v evM-v) cohv' le-u-v le-v-v'
      cU      = FinMem-a-in-U v' c fm-v'-c
      aU      = FinMem-a-in-U u a fm
      evU     = mkSigma tt (LeCode-refl UCode tt)
      IH-M    = adequacyConvSub2 dM sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH v' evM-v' c evA-c fm-v'-c
      eqtyA   = EqVal2-U-to-EqValTy2 c cU (adequacyConvSub2 dA sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH c evA-c UCode evU cU)
      eqtyB   = EqVal2-U-to-EqValTy2 a aU (adequacyConvSub2 dB sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH a evA UCode evU aU)

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
  adequacyEqSub2 (conv-funext dA d df dg) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH
      (adequacySub2 df) (adequacySub2 dg) (adequacyEqSub2 d) (adequacySub2 dA) u hu a evA fm
  adequacyEqSub2 (conv-App-fun dA dB dff' da) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH
      (adequacySub2 da) (adequacySub2 dB) (adequacyEqSub2 dff') u hu a evA fm
  adequacyEqSub2 (conv-App-arg dA dB df daa') sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH
      (adequacySub2 df) (adequacySub2 dB) (adequacyEqSub2 daa') u hu a evA fm
  -- conv-conv at type-code IdCode: EqVal2 there is Top
  adequacyEqSub2 (conv-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (IdCode _ _) evA fm = tt
  -- conv-Id: Id A B ≡ Id A' B' : U  (value Bot/IdCode, like ty-Id)
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu Bot evA ()
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu UCode evA fm = tt
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (FunEl _) evA ()
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (PiCode _ _) evA ()
  adequacyEqSub2 (conv-Id _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) hu (IdCode _ _) evA ()
  -- conv-pi1: pi1 p ≡ pi1 p' : Id A C  (value Bot-only, definitionally)
  adequacyEqSub2 (conv-pi1 _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-pi1 _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacyEqSub2 (conv-pi1 _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacyEqSub2 (conv-pi1 _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacyEqSub2 (conv-pi1 _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  -- conv-pi2: pi2 p N ≡ pi2 p' N'  (value Bot-only, definitionally)
  adequacyEqSub2 (conv-pi2 _ _ _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-pi2 _ _ _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacyEqSub2 (conv-pi2 _ _ _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacyEqSub2 (conv-pi2 _ _ _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacyEqSub2 (conv-pi2 _ _ _ _ _ _ _ _ _ _ _ _) sigma rho crho vs fits wtsub wfH (IdCode _ _) () a evA fm
  -- conv-Id-irr: proof irrelevance; the type is Id A B, so EqVal2 at every
  -- reachable type-code (Bot, IdCode) is Top, and UCode/FunEl/PiCode are absurd
  adequacyEqSub2 (conv-Id-irr _ _) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-Id-irr _ _) sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-Id-irr _ _) sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-Id-irr _ _) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-Id-irr _ _) sigma rho crho vs fits wtsub wfH u hu (IdCode _ _) evA fm = tt
  -- conv-cast-refl / conv-cast-cong: cast-related; not yet discharged
  adequacyEqSub2 (conv-cast-refl {A = A} {B = B} {M = M0} dA dB dM0 dAB) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    castRefl-pub _ _ _ _ u u a a (LeCode-refl u cu) (LeCode-refl a ca) fm fm cu
      dArefl dBrefl drefl dM0refl eqtyAB vtB IH-M
    where
      cu      = fst hu
      v       = fst (snd hu)
      le-u-v  = fst (snd (snd hu))
      evM0-v  = fst (snd (snd (snd hu)))
      ca      = EvalRel-coh B rho a evA
      evM0-u  = EvalRel-down M0 rho v u crho cu evM0-v le-u-v
      evA-A-a = convSound-inv dAB rho fits a evA        -- EvalRel A rho a
      aU      = FinMem-a-in-U u a fm
      evU     = mkSigma tt (LeCode-refl UCode tt)
      dArefl  = subst-HasType wtsub wfH dA
      dBrefl  = subst-HasType wtsub wfH dB
      dM0refl = subst-HasType wtsub wfH dM0
      convAB-sub = subst-ConvTm wtsub wfH dAB
      drefl   = ty-conv (ty-refl dArefl)
                  (conv-Id dArefl dArefl dArefl dBrefl (conv-refl dArefl) convAB-sub)
                  (ty-Id dArefl dBrefl)
      IH-M    = adequacySub2 dM0 sigma rho crho vs fits wtsub wfH u evM0-u a evA-A-a fm
      eqtyAB  = EqVal2-U-to-EqValTy2 a aU
                  (adequacyEqSub2 dAB sigma rho crho vs fits wtsub wfH a evA-A-a UCode evU aU)
      vtB     = Val2-U-to-ValTy2 a aU
                  (adequacySub2 dB sigma rho crho vs fits wtsub wfH a evA UCode evU aU)
  adequacyEqSub2 (conv-cast-cong {A = A} {B = B} {A' = A'} {B' = B'} {p = p} {p' = p'} {M = M} {M' = M'} dA dB dp dM dA' dB' dp' dM' dAA' dBB' dMM') sigma rho crho vs fits wtsub wfH u hu a evA fm =
    castEqVal-pub _ _ _ _ _ _ _ _ u v' c a le-u-v' fm fm-v'-c cohv'
      (subst-HasType wtsub wfH dA) (subst-HasType wtsub wfH dB)
      (subst-HasType wtsub wfH dp) (subst-HasType wtsub wfH dM)
      (subst-HasType wtsub wfH dA') (subst-HasType wtsub wfH dB')
      (subst-HasType wtsub wfH dp') (subst-HasType wtsub wfH dM')
      eqtyA eqtyB IH-M
    where
      cu     = fst hu
      v      = fst (snd hu)
      le-u-v = fst (snd (snd hu))
      evM-v  = fst (snd (snd (snd hu)))
      typedM = theorem1 dM rho fits v evM-v
      v'      = fst typedM
      c       = fst (snd typedM)
      le-v-v' = fst (snd (snd typedM))
      evM-v'  = fst (snd (snd (snd typedM)))
      fm-v'-c = fst (snd (snd (snd (snd typedM))))
      evA-c   = snd (snd (snd (snd (snd typedM))))
      cohv'   = FinMem-coh-u v' c fm-v'-c
      le-u-v' = LeCode-trans u v v' cu (EvalRel-coh M rho v evM-v) cohv' le-u-v le-v-v'
      cU      = FinMem-a-in-U v' c fm-v'-c
      aU      = FinMem-a-in-U u a fm
      evU     = mkSigma tt (LeCode-refl UCode tt)
      IH-M    = adequacyEqSub2 dMM' sigma rho crho vs fits wtsub wfH v' evM-v' c evA-c fm-v'-c
      eqtyA   = EqVal2-U-to-EqValTy2 c cU (adequacyEqSub2 dAA' sigma rho crho vs fits wtsub wfH c evA-c UCode evU cU)
      eqtyB   = EqVal2-U-to-EqValTy2 a aU (adequacyEqSub2 dBB' sigma rho crho vs fits wtsub wfH a evA UCode evU aU)
  -- conv-cast-Pi: coe-Pi head-expansion; depends on the bundled cast wrapper
  adequacyEqSub2 (conv-cast-Pi dA dB dC dD dp dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-coePi dA dB dC dD dp dM dN
      (adequacySub2 dA) (adequacySub2 dB) (adequacyConvSub2 dB)
      (adequacySub2 dC) (adequacySub2 dD) (adequacyConvSub2 dD)
      (adequacySub2 dM) (adequacySub2 dN)
      sigma rho crho vs fits wtsub wfH u hu a evA fm
