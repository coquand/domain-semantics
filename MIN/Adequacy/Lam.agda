{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyLam.agda  (MIN/ -- PROTOTYPE)
--
-- Standalone, NON-RECURSIVE combinators for the ty-Lam rule, factored out
-- of Adequacy.agda's mutual block.  Two combinators:
--
--   adequacy-ty-Lam  : the single-substitution Val2 of  Lam A M : Pi A B
--                      (port of adequacySub2-Lam).
--   adequacyV-ty-Lam : the two-substitution (cross) EqVal2 of Lam A M
--                      (port of the  adequacyConvSub2 (ty-Lam ...)  clause).
--
-- Both take the premises' adequacy IHs as EXPLICIT parameters.  Crucially,
-- the original clauses recurse on CONSTRUCTED derivations (ty-Pi d1 d2,
-- ty-Lam d1 d2 d3) and on the same derivation through a different mutual
-- function -- neither is structurally smaller, which is exactly why the
-- old definition was not structurally recursive.  Here those become parameters:
--   adequacySub2 (ty-Pi d1 d2)   -> IH-Pi  : Adq G (Pi A B) U
--   adequacySub2 (ty-Lam d1 d2 d3) -> IH-Lam : Adq G (Lam A M) (Pi A B)
--   transportVal2 d1 d2          -> transportVal2'  IH-A   (domain single IH)
--   transportEqVal2 d1 d2        -> transportEqVal2' IH-A
--   adequacyConvSub2 (ty-Pi d1 d2) -> adequacyV-ty-Pi (...) (Pi-type cross)
-- so neither combinator recurses; no postulate.
------------------------------------------------------------------------

module MIN.Adequacy.Lam where

open import MIN.Adequacy.HeadRed
open import MIN.Adequacy.Pi using (Adq ; AdqConv ; transportVal2' ; transportEqVal2' ;
  Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import MIN.Adequacy.VE using (adequacyV-ty-Pi)

import MIN.Domain.Basic as S
open S using (Nat ; zero ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ;
  FunEl ; PiCode ; FinFun)
open import MIN.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; coh-from-aU ;
  FinMem ; FinMem-coh-u ; EvalFun ; cft-from-cf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import MIN.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-coh ; EvalRel-mon-env ; EnvLe-refl)
open import MIN.Syntax.Raw using (Expr ; U ; Pi ; Lam ; subst1 ; Sub ; liftSub ; substExpr)
open import MIN.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-Pi ; ty-conv ; conv-refl ; conv-sym ; conv-conv ; conv-beta)
open import MIN.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; liftSub-WtSub ;
  subst-ConvTm-cross ; typing-type ; typing-ConvTm ; subst1-cong-ConvTm ; ctx-conv-HasType)
open import MIN.Model.SoundnessLemmas using (Fits)
open import MIN.Syntax.Reduction using (headred-refl ; headred-step ; headred-beta)
open import MIN.Model.Selection using (FinMem-Selection ; FinMem-Selection-codomain ; Coherent-Selection)
open import MIN.Model.EvalSubstitution using (EvalRel-Pi-body)

------------------------------------------------------------------------
-- adequacy-ty-Lam : single-substitution Val2 for  Lam A M : Pi A B.
-- Port of adequacySub2-Lam.  IH params:
--   IH-A  : Adq G A U                 (domain, for transportVal2'/Sup)
--   IH-Pi : Adq G (Pi A B) U          (the Pi-type's own single-sub validity)
--   IH-M  : Adq (extend G A) M B      (codomain term, for the App value)
--   IH-cM : AdqConv (extend G A) M B  (codomain term cross, for the App eq)
------------------------------------------------------------------------

adequacy-ty-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U -> HasType (extend G A) M B ->
    Adq G A U -> Adq G (Pi A B) U -> Adq (extend G A) M B -> AdqConv (extend G A) M B ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) ->
    EvalRel (Lam A M) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    Val2 H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
           (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
           (FunEl g0) (PiCode b f0)
adequacy-ty-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3 IH-A IH-Pi IH-M IH-cM
    sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
  mk-ValPi (snd valTyPi) (record
    { domA0 = sA ; codB0 = sB
    ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_lam htB_lam))
    ; cohG = cg ; fmG = fmg ; appV = piAppVal ; appE = piAppEq })
  where
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sM   = substExpr (liftSub sigma) M
    fmg  = finMem-funel-fun g0 b f0 fm
    cg   = finMem-funel-coh g0 b f0 fm
    pU   = finMem-funel-wf g0 b f0 fm
    bU   = finMem-piU-dom b f0 pU
    allU = finMem-piU-allU b f0 pU
    cf0  = finMem-piU-cft b f0 pU
    cb   = coh-from-aU b bU
    evAb = fst (snd evA)
    a_lam = fst hu
    bodyLam = snd (snd (snd (snd hu)))
    evU  = mkSigma tt (LeCode-refl UCode tt)
    htA_lam = subst-HasType wtsub wfH d1
    htB_lam = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA_lam) d2
    htM_lam = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA_lam) d3
    valTyPi = IH-Pi sigma rho crho vs fits wtsub wfH (PiCode b f0) evA UCode evU pU
    piAppVal : PiAppVal2 H (Lam sA sM) sA sB b f0 g0
    piAppVal u' v' sel N htN valN =
      let cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
          fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
          fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
          w         = bodyLam u' v' sel
          x         = fst w
          le_x_u'   = fst (snd w)
          fm_x_al   = fst (snd (snd w))
          evM_x_v'  = snd (snd (snd w))
          cx        = FinMem-coh-u x a_lam fm_x_al
          envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
          fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho'     = mkSigma crho cu'
          hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                        transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'       = ValidSub2-extend sigma N rho u' vs hyp0
          wtsub'    = extSub-WtSub wtsub wfH d1 htN
          ih        = IH-M (extSub sigma N) (extendEnv rho u')
                        crho' vs' fits' wtsub' wfH v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M      = S.Eq-sym (substExpr-comp sigma M N)
          eq_B      = S.Eq-sym (substExpr-comp sigma B N)
          ih'       = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u')) eq_B ih
          ih''      = S.Eq-transport (\ E -> Val2 H E (subst1 sB N) v' (EvalFun f0 u')) eq_M ih'
      in Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl)
           (conv-beta htA_lam htB_lam htM_lam htN) ih''
    piAppEq : PiAppEq2 H (Lam sA sM) sA sB b f0 g0
    piAppEq u' v' sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1     = Val2-from-EqVal2-first u' b eqvalN
          valN2     = Val2-from-EqVal2-second u' b eqvalN
          cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
          fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
          fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
          w         = bodyLam u' v' sel
          x         = fst w
          le_x_u'   = fst (snd w)
          fm_x_al   = fst (snd (snd w))
          evM_x_v'  = snd (snd (snd w))
          cx        = FinMem-coh-u x a_lam fm_x_al
          envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
          fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho'     = mkSigma crho cu'
          wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
          wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
          hyp0_N1   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                        transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          hyp0_N2   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                        transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'_N1    = ValidSub2-extend sigma N1 rho u' vs hyp0_N1
          vs'_N2    = ValidSub2-extend sigma N2 rho u' vs hyp0_N2
          vcs_ext   = ValidConvSub2-extend sigma sigma N1 N2 rho u'
                        (ValidConvSub2-refl {G = G} vs)
                        (transportEqVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b eqvalN)
          wcs_ext   = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
          raw       = IH-cM (extSub sigma N1) (extSub sigma N2) (extendEnv rho u')
                        crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                        v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M1     = S.Eq-sym (substExpr-comp sigma M N1)
          eq_M2     = S.Eq-sym (substExpr-comp sigma M N2)
          eq_B1     = S.Eq-sym (substExpr-comp sigma B N1)
          raw'      = S.Eq-transport (\ T -> EqVal2 H (subst1 sM N1) T (subst1 sB N1) v' (EvalFun f0 u')) eq_M2
                        (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) M) (subst1 sB N1) v' (EvalFun f0 u')) eq_M1
                          (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u')) eq_B1 raw))
          cvBeta2   = conv-beta htA_lam htB_lam htM_lam htN2
          cvB21     = subst1-cong-ConvTm htA_lam htB_lam htN2 htN1 (conv-sym cvN)
          htB1      = typing-type (snd (typing-ConvTm (conv-beta htA_lam htB_lam htM_lam htN1)))
          cvBeta2'  = conv-conv cvBeta2 cvB21 htB1
      in EqVal2-headred-expand v' (EvalFun f0 u')
           (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
           (conv-beta htA_lam htB_lam htM_lam htN1) cvBeta2' raw'

------------------------------------------------------------------------
-- adequacyV-ty-Lam : two-substitution (cross) EqVal2 for Lam A M.
-- Port of the  adequacyConvSub2 (ty-Lam ...)  main clause.  IH params:
--   IH-A   : Adq G A U                          (domain single, transports)
--   IH-Lam : Adq G (Lam A M) (Pi A B)           (the Lam's own single-sub
--            validity at sigma AND sigma' -- replaces adequacySub2 (ty-Lam))
--   IH-cA  : AdqConv G A U                      (domain cross)
--   IH-cB  : AdqConv (extend G A) B U           (codomain TYPE cross; feeds
--            adequacyV-ty-Pi to rebuild the Pi-type cross from subterms)
--   IH-cM  : AdqConv (extend G A) M B           (codomain term cross)
------------------------------------------------------------------------

adequacyV-ty-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U -> HasType (extend G A) M B ->
    Adq G A U -> Adq G (Lam A M) (Pi A B) ->
    AdqConv G A U -> AdqConv (extend G A) B U -> AdqConv (extend G A) M B ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
    (g0 : FinFun) ->
    EvalRel (Lam A M) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    EqVal2 H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
             (Lam (substExpr sigma' A) (substExpr (liftSub sigma') M))
             (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (FunEl g0) (PiCode b f0)
adequacyV-ty-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH g0 hu b f0 evA fm =
  mk-EqValPi valTyPi rvalPiL rvalPiR reqvalPi
  where
    sA = substExpr sigma A ; sA' = substExpr sigma' A
    sB = substExpr (liftSub sigma) B ; sB' = substExpr (liftSub sigma') B
    sM0 = substExpr (liftSub sigma) M ; sM'0 = substExpr (liftSub sigma') M
    fmg = finMem-funel-fun g0 b f0 fm ; cg = finMem-funel-coh g0 b f0 fm ; pU = finMem-funel-wf g0 b f0 fm
    bU = finMem-piU-dom b f0 pU ; allU = finMem-piU-allU b f0 pU ; cf0 = finMem-piU-cft b f0 pU
    cb = coh-from-aU b bU ; evU0 = mkSigma tt (LeCode-refl UCode tt)
    htA0 = subst-HasType wtsub wfH d1 ; htA'0 = subst-HasType wtsub' wfH d1
    htB0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d2
    htB'0 = subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2
    htM0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d3
    htM'0 = subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d3
    convA0 = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
    a_lam = fst hu ; bodyLam = snd (snd (snd (snd hu)))
    evAb = fst (snd evA)
    leftVal2 = IH-Lam sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
    valTyPi = valPi-ty leftVal2 ; rvalPiL = un-ValPi leftVal2
    rightVal2' = IH-Lam sigma' rho crho vs' fits wtsub' wfH (FunEl g0) hu (PiCode b f0) evA fm
    eqPi_raw = adequacyV-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f0 evA evU0 pU
    eqTyPi = EqVal2-U-to-EqValTy2 (PiCode b f0) pU eqPi_raw
    eqTyPi_sym = EqValTy2-sym (PiCode b f0) (coh-from-aU (PiCode b f0) pU) eqTyPi
    rightVal2 = Val2-type-transport (FunEl g0) (PiCode b f0) eqTyPi_sym rightVal2'
    rvalPiR = un-ValPi rightVal2
    buildAppEV : PiAppEqVal2 H (Lam sA sM0) (Lam sA' sM'0) sA sB b f0 g0
    buildAppEV u' v' sel P htP valP =
      let ctg = cft-from-cf g0 cg ; cu' = Coherent-Selection sel ctg
          fm_u'_b = FinMem-Selection b f0 sel fmg ctg cb bU
          fm_v'_ef = FinMem-Selection-codomain b f0 sel fmg ctg cf0 allU
          w = bodyLam u' v' sel ; x = fst w ; le_x_u' = fst (snd w)
          fm_x_al = fst (snd (snd w)) ; evM_x_v' = snd (snd (snd w))
          cx = FinMem-coh-u x a_lam fm_x_al
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
          fits' = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho' = mkSigma crho cu'
          hyp0_s = \ u'' cu'' le a1 evA1 fm1 -> transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1
          vs_ext = ValidSub2-extend sigma P rho u' vs hyp0_s
          wtsub_ext = extSub-WtSub wtsub wfH d1 htP
          eqA_domA = EqVal2-U-to-EqValTy2 b bU (IH-cA sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evU0 bU)
          valP' = Val2-EqValTy2-fwd u' b cb eqA_domA valP
          hyp0_s' = \ u'' cu'' le a1 evA1 fm1 -> transportVal2' IH-A sigma' rho crho vs' fits wtsub' wfH b bU evAb u' fm_u'_b P valP' u'' cu'' le a1 evA1 fm1
          vs'_ext = ValidSub2-extend sigma' P rho u' vs' hyp0_s'
          htP' = ty-conv htP convA0 htA'0
          wtsub'_ext = extSub-WtSub wtsub' wfH d1 htP'
          hyp0_conv = \ u'' cu'' le a1 evA1 fm1 -> Val2-to-EqVal2 u'' a1 (transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1)
          vcs_ext = ValidConvSub2-extend sigma sigma' P P rho u' vcs hyp0_conv
          wcs_ext = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
          ihM_raw = IH-cM (extSub sigma P) (extSub sigma' P) (extendEnv rho u')
                      crho' vs_ext vs'_ext vcs_ext fits' wtsub_ext wtsub'_ext wcs_ext wfH
                      v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M = S.Eq-sym (substExpr-comp sigma M P) ; eq_M' = S.Eq-sym (substExpr-comp sigma' M P)
          eq_B = S.Eq-sym (substExpr-comp sigma B P) ; eq_B' = S.Eq-sym (substExpr-comp sigma' B P)
          ihM = S.Eq-transport (\ T -> EqVal2 H (subst1 sM0 P) T (subst1 sB P) v' (EvalFun f0 u')) eq_M'
                  (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) M) (subst1 sB P) v' (EvalFun f0 u')) eq_M
                    (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u')) eq_B ihM_raw))
          convBP_raw = subst-ConvTm-cross d2 wtsub_ext wtsub'_ext wcs_ext wfH
          convBP = S.Eq-transport (\ T -> ConvTm H (subst1 sB P) T U) eq_B'
                     (S.Eq-transport (\ T -> ConvTm H T (substExpr (extSub sigma' P) B) U) eq_B convBP_raw)
          cv_left = conv-beta htA0 htB0 htM0 htP
          cv_right' = conv-beta htA'0 htB'0 htM'0 htP'
          htBP = typing-type (snd (typing-ConvTm cv_left))
          cv_right = conv-conv cv_right' (conv-sym convBP) htBP
      in EqVal2-headred-expand v' (EvalFun f0 u')
           (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
           cv_left cv_right ihM
    reqvalPi : REqValPi H (Lam sA sM0) (Lam sA' sM'0) (Pi sA sB) g0 b f0
    reqvalPi = record { domA0 = sA ; codB0 = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA0 htB0))
      ; cohG = cg ; fmG = fmg ; appEV = buildAppEV }

------------------------------------------------------------------------
-- lamTypeTwoSub : the TYPE two-substitution of  Lam A M : Pi A B, i.e.
-- EqValTy2 (Pi A B)[σ] (Pi A B)[σ'] at the type's value.  Since Pi A B : U,
-- this is the Pi-type cross (adequacyV-ty-Pi) re-read as a type equality.
-- EvalRel (Pi A B) rho a forces a ∈ {Bot (trivial), PiCode b f0}.
------------------------------------------------------------------------

lamTypeTwoSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqConv G A U -> AdqConv (extend G A) B U ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem a UCode ->
  EqValTy2 H (substExpr sigma (Pi A B)) (substExpr sigma' (Pi A B)) a
lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wtcs wfH Bot _ _ = tt
lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wtcs wfH (PiCode b f0) evA piU =
  EqVal2-U-to-EqValTy2 (PiCode b f0) piU
    (adequacyV-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wtcs wfH
       b f0 evA (mkSigma tt (LeCode-refl UCode tt)) piU)
lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wtcs wfH UCode () _
lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wtcs wfH (FunEl _) () _
