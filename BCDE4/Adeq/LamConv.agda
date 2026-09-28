{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.LamConv  (T_R version of MIN adequacyV-ty-Lam)
--
-- Two-substitution validity of λ(A,B,b) at Π(A,B): the two λ's are
-- valid (Adq-Lam at σ and σ'; the second is transported to the type
-- Π(A,B)[σ] along the two-substitution validity of the product), and
-- pointwise their applications β-reduce to b[σ,P] and b[σ',P], which
-- the body's two-substitution IH relates.
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.LamConv (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D
open import BCDE4.Adeq.Pi D using (transportVal2')
open import BCDE4.Adeq.Lam D using (Adq-Lam ; beta-ann)

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; coh-from-aU ; EvalFun ;
  FinMem ; FinMem-coh-u ; cft-from-cf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import BCDE4.Model.Eval D using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-mon-env ; EnvLe-refl)
open import BCDE4.Model.EvalSubstitution D using (EvalRel-Pi-body)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (Selection ; FinMem-Selection ; FinMem-Selection-codomain ; Coherent-Selection)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; Lam ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  liftSub-WtSub ; isType-Pi ; subst1-WtSub ; isType-WfCtx ; ctx-conv-ConvTy)
open import BCDE4.RussellMetaCong using (subst-cong-IsType ; liftSub-ConvTmSub)
open import BCDE4.RussellReduction using (headred-refl ; headred-step ; headred-beta)

open import BCDE4.Levels using (LCtx ; LSub ; lidS)
private variable
  TL : LCtx
  θ : LSub

adequacyV-ty-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B M : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) M B ->
    AdqTy G A -> AdqConvTy G A -> AdqTy G (Pi A B) -> AdqConvTy G (Pi A B) ->
    Adq (extend G A) M B -> AdqConv (extend G A) M B ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
    (g0 : FinFun) ->
    EvalRel (strip (Lam A B M)) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) ->
    EvalRel (strip (Pi A B)) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    EqVal2 H (substExpr sigma (Lam A B M)) (substExpr sigma' (Lam A B M))
             (substExpr sigma (Pi A B)) (FunEl g0) (PiCode b f0)
adequacyV-ty-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH g0 hu b f0 evA fm =
  mk-EqValPi valTyPi rvalPiL rvalPiR reqvalPi
  where
    sA = substExpr sigma A ; sA' = substExpr sigma' A
    sB = substExpr (liftSub sigma) B ; sB' = substExpr (liftSub sigma') B
    sM0 = substExpr (liftSub sigma) M ; sM'0 = substExpr (liftSub sigma') M
    fmg = finMem-funel-fun g0 b f0 fm ; cg = finMem-funel-coh g0 b f0 fm ; pU = finMem-funel-wf g0 b f0 fm
    bU = finMem-piU-dom b f0 pU ; allU = finMem-piU-allU b f0 pU ; cf0 = finMem-piU-cft b f0 pU
    cb = coh-from-aU b bU
    htA0 = subst-IsType wtsub wfH d1 ; htA'0 = subst-IsType wtsub' wfH d1
    htB0 = subst-IsType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d2
    htB'0 = subst-IsType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2
    htM0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d3
    htM'0 = subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d3
    -- syntactic two-substitution conversions of the annotations
    convA0 : ConvTy H sA sA'
    convA0 = subst-cong-IsType wcs wfH d1
    convB0 : ConvTy (extend H sA) sB sB'
    convB0 = subst-cong-IsType (liftSub-ConvTmSub wcs wfH d1) (wf-extend htA0) d2
    convB0' : ConvTy (extend H sA') sB' sB
    convB0' = ctx-conv-ConvTy htA0 htA'0 convA0 (conv-Ty-sym convB0)
    a_lam = fst hu ; bodyLam = snd (snd (snd (snd hu)))
    evAb = fst (snd evA)
    rflA = conv-Ty-refl d1 ; rflB = conv-Ty-refl d2
    leftVal2 = Adq-Lam d1 d2 d3 rflA rflB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH
                 (FunEl g0) hu (PiCode b f0) evA fm
    valTyPi = valPi-ty leftVal2 ; rvalPiL = un-ValPi leftVal2
    rightVal2' = Adq-Lam d1 d2 d3 rflA rflB IH-A IH-Pi IH-M IH-cM sigma' rho crho vs' fits wtsub' wfH
                   (FunEl g0) hu (PiCode b f0) evA fm
    eqTyPi = IH-cPi sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) evA pU
    eqTyPi-sym = EqValTy2-sym (PiCode b f0) (coh-from-aU (PiCode b f0) pU) eqTyPi
    rightVal2 = Val2-type-transport (FunEl g0) (PiCode b f0) eqTyPi-sym rightVal2'
    rvalPiR = un-ValPi rightVal2

    buildAppEV : PiAppEqVal2 H (Lam sA sB sM0) (Lam sA' sB' sM'0) sA sB b f0 g0
    buildAppEV u' v' sel {A1} {A2} {B1} {B2} an1 an2 P htP valP =
      let ctg = cft-from-cf g0 cg ; cu' = Coherent-Selection sel ctg
          fm_u'_b = FinMem-Selection b f0 sel fmg ctg cb bU
          fm_v'_ef = FinMem-Selection-codomain b f0 sel fmg ctg cf0 allU
          w = bodyLam u' v' sel ; x = fst w ; le_x_u' = fst (snd w)
          fm_x_al = fst (snd (snd w)) ; evM_x_v' = snd (snd (snd w))
          cx = FinMem-coh-u x a_lam fm_x_al
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env (strip M) (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body (strip A) (strip B) rho b f0 u' crho cu' evA
          fits' = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho' = mkSigma crho cu'
          hyp0_s = \ u'' cu'' le a1 evA1 fm1 -> transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1
          vs_ext = ValidSub2-extend {A = A} sigma P rho u' vs hyp0_s
          wtsub_ext = extSub-WtSub {A = A} wtsub htP
          eqA_domA = IH-cA sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb bU
          valP' = Val2-EqValTy2-fwd u' b cb eqA_domA valP
          hyp0_s' = \ u'' cu'' le a1 evA1 fm1 -> transportVal2' {G = G} {A = A} IH-A sigma' rho crho vs' fits wtsub' wfH b bU evAb u' fm_u'_b P valP' u'' cu'' le a1 evA1 fm1
          vs'_ext = ValidSub2-extend {A = A} sigma' P rho u' vs' hyp0_s'
          htP' = ty-conv htP convA0
          wtsub'_ext = extSub-WtSub {A = A} wtsub' htP'
          hyp0_conv = \ u'' cu'' le a1 evA1 fm1 -> Val2-to-EqVal2 u'' a1 (transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1)
          vcs_ext = ValidConvSub2-extend {A = A} sigma sigma' P P rho u' vcs hyp0_conv
          wcs_ext = extSub-WtConvSub {A = A} wcs (conv-refl htP)
          ihM_raw = IH-cM (extSub sigma P) (extSub sigma' P) (extendEnv rho u')
                      crho' vs_ext vs'_ext vcs_ext fits' wtsub_ext wtsub'_ext wcs_ext wfH
                      v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          ihM = S.Eq-transport (\ T -> EqVal2 H (subst1 sM0 P) T (subst1 sB P) v' (EvalFun f0 u'))
                  (S.Eq-sym (substExpr-comp sigma' M P))
                  (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) M) (subst1 sB P) v' (EvalFun f0 u'))
                     (S.Eq-sym (substExpr-comp sigma M P))
                     (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u'))
                        (S.Eq-sym (substExpr-comp sigma B P)) ihM_raw))
          cv_left = beta-ann htA0 htB0 htM0 an1 htP
          an2' = Ann-back an2 (conv-Ty-sym convA0) convB0'
          convBP : ConvTy H (subst1 sB' P) (subst1 sB P)
          convBP = conv-Ty-sym (subst-ConvTy (subst1-WtSub htA0 htP) (isType-WfCtx htA0) convB0)
          cv_right = conv-conv (beta-ann htA'0 htB'0 htM'0 an2' htP') convBP
      in EqVal2-headred-expand v' (EvalFun f0 u')
           (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
           cv_left cv_right ihM

    reqvalPi : REqValPi H (Lam sA sB sM0) (Lam sA' sB' sM'0) (Pi sA sB) g0 b f0
    reqvalPi = record { domA0 = sA ; codB0 = sB ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA0 htB0))
      ; cohG = cg ; fmG = fmg ; appEV = buildAppEV }

AdqConv-Lam : {g : Nat} {G : Ctx g} {A : Expr g} {B M : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) M B ->
  AdqTy G A -> AdqConvTy G A -> AdqTy G (Pi A B) -> AdqConvTy G (Pi A B) ->
  Adq (extend G A) M B -> AdqConv (extend G A) M B ->
  AdqConv G (Lam A B M) (Pi A B)
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH Bot hu a evA fm = EqVal2-Bot a
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (UCode _) () a evA fm
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (PiCode _ _) () a evA fm
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl g0) hu Bot evA fm = tt
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl g0) hu (UCode _) () fm
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl g0) hu (FunEl _) () fm
AdqConv-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl g0) hu (PiCode b f0) evA fm =
  adequacyV-ty-Lam d1 d2 d3 IH-A IH-cA IH-Pi IH-cPi IH-M IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH g0 hu b f0 evA fm
