{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Adequacy5Cases.agda
--
-- Helper for Hole 6: ty-MkPair cross-sub at (PairCode, SigmaCode).
-- Takes IH and sigEdgeEq as explicit arguments to avoid opacity.
------------------------------------------------------------------------

module Adequacy5Cases where
open import Adequacy5HeadRed public

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ; codeFst ; codeSnd)
open import PaperSemanticsSigma using (LeCode ; LeCode-refl ;
  Coherent ; CoherentFun ; CoherentFunTail ; EvalFun ;
  Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ;
  FinMem ; FinMemFun ; FinMemAllU ;
  FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ;
  coh-from-aU ; FinMem-coh-u ; cft-from-cf ;
  NotBot ; absurdEl)
open import ReductionSigma using (Red ; mkRed ; Red-refl ; HeadRed ;
  headred-step ; headred-beta ; headred-refl ; subst-subst1-comm ;
  headred-beta-fst ; headred-beta-snd)
open import RawSemanticsSigma using (EnvApprox ; extendEnv ;
  EvalRel ; Sigma-edgewise ; EvalRel-coh ; CoherentEnv ;
  EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr ; subst1Sub)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; extend ;
  HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  conv-refl ; conv-sym ; conv-conv ; conv-beta-fst ; conv-beta-snd)
open import ValiditySigma using (Selection ; Coherent-Selection ; Coherent-Selection-val ; FinMem-Coherent)
open import ValiditySigma using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import SelectionSigma using (FinMemAllU-Selection ; selectionBelow ;
  FinMem-Selection ; FinMem-Selection-codomain)
open import EvalSubstitutionSigma using (EvalRel-subst1-backward ; EvalRel-body-EvalFun ;
  EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import Validity5SymTrans using (EqVal2-trans)
open import Validity5Fwd using (Val2-EqValTy2-fwd ; EqValTy2-sym)
open import TypingSemanticsSigma using (convSound' ; theorem1)
open import SubstitutionLemmaSigma using (typing-ConvTm ; WtSub ;
  subst-HasType ; subst-ConvTm ; liftSub-WtSub ;
  typing-WfCtx ; typing-type ;
  subst1-cong-ConvTm ; WtConvSub ; subst-ConvTm-cross)
open import LemmaForTSSigma using (Fits)

------------------------------------------------------------------------
-- Hole 6: ty-MkPair cross-sub at (PairCode u' v', SigmaCode b f)
------------------------------------------------------------------------

tyMkPair-conv-case :
  {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {M N : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType G M A -> HasType G N (subst1 B M) ->
  (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' ->
  WtConvSub H G sigma sigma' ->
  WfCtx H ->
  (u' v' : FinEl) -> EvalRel (MkPair M N) rho (PairCode u' v') ->
  (b : FinEl) -> (f : FinFun) -> EvalRel (SigmaE A B) rho (SigmaCode b f) ->
  FinMem (PairCode u' v') (SigmaCode b f) ->
  -- Left Val2 (opaque whole)
  Val2 H (MkPair (substExpr sigma M) (substExpr sigma N))
         (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
         (PairCode u' v') (SigmaCode b f) ->
  -- Right Val2 (opaque whole, already type-transported to sigma-type)
  Val2 H (MkPair (substExpr sigma' M) (substExpr sigma' N))
         (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
         (PairCode u' v') (SigmaCode b f) ->
  -- IH: adequacyConvSub2 at G
  ({M0 A0 : Expr g} -> HasType G M0 A0 ->
    (u : FinEl) -> EvalRel M0 rho u ->
    (a : FinEl) -> EvalRel A0 rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M0) (substExpr sigma' M0) (substExpr sigma A0) u a) ->
  -- sigEdgeEq
  SigmaEdgeEq2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f ->
  -- Right-side HasType for Fst (MkPair sM' sN') : sA
  HasType H (Fst (MkPair (substExpr sigma' M) (substExpr sigma' N))) (substExpr sigma A) ->
  -- Right-side snd ConvTm at correct type
  ConvTm H (Snd (MkPair (substExpr sigma' M) (substExpr sigma' N)))
           (substExpr sigma' N)
           (subst1 (substExpr (liftSub sigma) B) (Fst (MkPair (substExpr sigma' M) (substExpr sigma' N)))) ->
  -- Result
  EqVal2 H (MkPair (substExpr sigma M) (substExpr sigma N))
           (MkPair (substExpr sigma' M) (substExpr sigma' N))
           (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
           (PairCode u' v') (SigmaCode b f)
tyMkPair-conv-case {H = H} {A = A} {B = B} {M = M0} {N = N0}
    d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    u' v' hu b f evA fm leftVal2 rightVal2 adConvSub2 sigEdgeEq htFstR cvSndR =
  mkSigma (fst leftVal2) (mkSigma (snd leftVal2) (mkSigma (snd rightVal2) reqvalSig))
  where
    sA = substExpr sigma A ; sA' = substExpr sigma' A
    sB = substExpr (liftSub sigma) B
    sM = substExpr sigma M0 ; sM' = substExpr sigma' M0
    sN = substExpr sigma N0 ; sN' = substExpr sigma' N0
    evM = fst (snd hu) ; evN = snd (snd hu) ; evA_b = fst (snd evA)
    fm_u'_b = fst (fst fm) ; fm_v'_ef = snd (fst fm)
    cu' = fst (fst (fst (snd fm)))
    pSigU = snd (snd fm) ; bU_sig = fst pSigU ; allU_sig = fst (snd pSigU)
    cf_sig = snd (snd pSigU) ; cb_sig = coh-from-aU b bU_sig
    htA0 = subst-HasType wtsub wfH d1 ; htA'0 = subst-HasType wtsub' wfH d1
    htB0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d2
    htM0s = subst-HasType wtsub wfH d3 ; htM'0s = subst-HasType wtsub' wfH d3
    htN0s = S.Eq-transport (HasType _ sN) (S.Eq-sym (subst-subst1-comm sigma B M0)) (subst-HasType wtsub wfH d4)
    htSig0 = ty-Sigma htA0 htB0
    convA0 = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
    htM'0_sA = ty-conv htM'0s (conv-sym convA0) htA0
    convMM' = subst-ConvTm-cross d3 wtsub wtsub' wcs wfH
    htMkPairL = ty-MkPair htA0 htB0 htM0s htN0s
    htFstL = ty-Fst htA0 htB0 htMkPairL
    -- eqMM' at (u', b)
    eqMM' = adConvSub2 d3 u' evM b evA_b fm_u'_b
    val_M = Val2-from-EqVal2-first u' b eqMM'
    val_M' = Val2-from-EqVal2-second u' b eqMM'
    -- Fst betas
    hr-fst-L = headred-step (headred-beta-fst {M = sM} {N = sN}) headred-refl
    hr-fst-R = headred-step (headred-beta-fst {M = sM'} {N = sN'}) headred-refl
    cv-fst-L = conv-beta-fst htA0 htB0 htM0s htN0s
    cv-fst-R' = conv-beta-fst htA'0 (subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2) htM'0s
                  (S.Eq-transport (HasType _ sN') (S.Eq-sym (subst-subst1-comm sigma' B M0)) (subst-HasType wtsub' wfH d4))
    cv-fst-R = conv-conv cv-fst-R' (conv-sym convA0) htA0
    valFstL = Val2-beta-expand u' b hr-fst-L cv-fst-L val_M
    valFstR = Val2-beta-expand u' b hr-fst-R cv-fst-R val_M'
    eqFst = EqVal2-headred-expand u' b hr-fst-L hr-fst-R cv-fst-L cv-fst-R eqMM'
    -- Snd
    sew0 = Sigma-edgewise A B rho b f evA
    evBM_ef = EvalRel-subst1-backward B M0 rho u' (EvalFun f u') crho evM
                (EvalRel-body-EvalFun B rho u' (fst (snd (snd sew0))) f crho cu' (snd (fst sew0)) (snd (snd (snd (snd sew0)))))
    eqNN' = S.Eq-transport (\ T -> EqVal2 H sN sN' T v' (EvalFun f u'))
              (S.Eq-sym (subst-subst1-comm sigma B M0))
              (adConvSub2 d4 v' evN (EvalFun f u') evBM_ef fm_v'_ef)
    val_N = Val2-from-EqVal2-first v' (EvalFun f u') eqNN'
    val_N' = Val2-from-EqVal2-second v' (EvalFun f u') eqNN'
    -- Selection
    sb0 = selectionBelow f u' cf_sig cu'
    u-f = fst sb0 ; v-f = fst (snd sb0) ; sel-f = fst (snd (snd sb0))
    le-uf = fst (snd (snd (snd sb0))) ; eq-ef = snd (snd (snd (snd sb0)))
    fmu-f = FinMemAllU-Selection b sel-f allU_sig cf_sig cb_sig bU_sig
    -- Snd betas and type transports
    hr-snd-L = headred-step (headred-beta-snd {M = sM} {N = sN}) headred-refl
    hr-snd-R = headred-step (headred-beta-snd {M = sM'} {N = sN'}) headred-refl
    cv-snd-L = conv-beta-snd htA0 htB0 htM0s htN0s
    -- Left snd transport
    eqL = EqVal2-headred-expand u' b headred-refl hr-fst-L (conv-refl htM0s) cv-fst-L (Val2-to-EqVal2 u' b val_M)
    eqTyL = S.Eq-transport (EqValTy2 H (subst1 sB sM) (subst1 sB (Fst (MkPair sM sN)))) (S.Eq-sym eq-ef)
              (sigEdgeEq u-f v-f sel-f sM (Fst (MkPair sM sN)) htM0s htFstL (conv-sym cv-fst-L)
                (restrictEqVal2 _ sM (Fst (MkPair sM sN)) sA u' u-f b le-uf fmu-f fm_u'_b eqL))
    valSndM = Val2-type-transport v' (EvalFun f u') eqTyL
                (Val2-beta-expand v' (EvalFun f u') hr-snd-L cv-snd-L val_N)
    -- Right snd: sM→sM' transport
    eqMM'_uf = restrictEqVal2 _ sM sM' sA u' u-f b le-uf fmu-f fm_u'_b eqMM'
    eqTyMM' = S.Eq-transport (EqValTy2 H (subst1 sB sM) (subst1 sB sM')) (S.Eq-sym eq-ef)
                (sigEdgeEq u-f v-f sel-f sM sM' htM0s htM'0_sA convMM' eqMM'_uf)
    val_N'_sM' = Val2-type-transport v' (EvalFun f u') eqTyMM' val_N'
    -- Right snd: sM'→Fst(MkPair sM' sN') transport
    eqR = EqVal2-headred-expand u' b headred-refl hr-fst-R (conv-refl htM'0_sA) cv-fst-R (Val2-to-EqVal2 u' b val_M')
    eqTyR = S.Eq-transport (EqValTy2 H (subst1 sB sM') (subst1 sB (Fst (MkPair sM' sN')))) (S.Eq-sym eq-ef)
              (sigEdgeEq u-f v-f sel-f sM' (Fst (MkPair sM' sN')) htM'0_sA htFstR (conv-sym cv-fst-R)
                (restrictEqVal2 _ sM' (Fst (MkPair sM' sN')) sA u' u-f b le-uf fmu-f fm_u'_b eqR))
    valSndR = Val2-beta-expand v' (EvalFun f u') hr-snd-R cvSndR
                (Val2-type-transport v' (EvalFun f u') eqTyR val_N'_sM')
    -- Record
    reqvalSig : REqValSigma H (MkPair sM sN) (MkPair sM' sN') (SigmaE sA sB) (PairCode u' v') b f
    reqvalSig = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
      ; htFstM = htFstL ; htFstN = htFstR ; cohW1 = cu' ; fmW1 = fm_u'_b
      ; valFstM = valFstL ; valSndM = valSndM ; valFstN = valFstR ; valSndN = valSndR ; eqFst = eqFst }

------------------------------------------------------------------------
-- adequacyEqSub2-App-fun-core-body
-- Factored out of mutual block. Takes adequacySub2 and adequacyEqSub2 as IH.
------------------------------------------------------------------------

adequacyEqSub2-App-fun-core-body : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
  HasType (extend G A) B U ->
  ConvTm G f f' (Pi A B) ->
  HasType G a A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u1 : FinEl) ->
  (v0 : FinEl) -> EvalRel a rho v0 ->
  EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
  -- IH: adequacySub2
  ({g0 : Nat} {G0 : Ctx g0} {M0 A0 : Expr g0} -> HasType G0 M0 A0 ->
    (sigma0 : Sub h g0) -> (rho0 : EnvApprox g0) ->
    CoherentEnv rho0 -> ValidSub2 H G0 sigma0 rho0 -> Fits G0 rho0 ->
    WtSub H G0 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0) ->
  -- IH: adequacyEqSub2
  ({g0 : Nat} {G0 : Ctx g0} {M0 N0 A0 : Expr g0} -> ConvTm G0 M0 N0 A0 ->
    (sigma0 : Sub h g0) -> (rho0 : EnvApprox g0) ->
    CoherentEnv rho0 -> ValidSub2 H G0 sigma0 rho0 -> Fits G0 rho0 ->
    WtSub H G0 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    EqVal2 H (substExpr sigma0 M0) (substExpr sigma0 N0) (substExpr sigma0 A0) u a0) ->
  -- Val2-U-to-ValTy2
  ({n0 : Nat} {G0 : Ctx n0} {M0 : Expr n0} ->
    (b : FinEl) -> FinMem b UCode -> Val2 G0 M0 U b UCode -> ValTy2 G0 M0 b) ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma f') (substExpr sigma a))
           (substExpr sigma (subst1 B a))
           u1 ac1
adequacyEqSub2-App-fun-core-body {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
  dB dff' da sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  adSub2 adEqSub2 v2u2vt2 =
  S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf' sa) T u1 ac1) (S.Eq-sym eq-sBA) transported
  where
    sf   = substExpr sigma f0
    sf'  = substExpr sigma f'
    sa   = substExpr sigma a
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sBA  = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    sing     = cons (mkSigma v0 u1) nil
    cv0      = EvalRel-coh a rho v0 evA_v0

    -- Enlarge function via convSound'
    invTyp-f = fst (convSound' dff' rho fits)
    typed_f  = invTyp-f (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    -- Function's EqVal2 via IH
    eqval_fun = adEqSub2 dff' sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

    -- Dispatch on (ub, ap) — only (FunEl, PiCode) is non-absurd
    appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
      FinMem ub ap ->
      EqVal2 H sf sf' (Pi sA sB) ub ap ->
      EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
    appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
    appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
    appEqVal-dispatch PropCode     ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba eqvba
    appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba eqvba
    appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
      let le_u1_vsel = fst lf
          fmg_big  = fst fmba
          cg_big   = fst (snd fmba)
          piU      = snd (snd fmba)
          b_piU    = fst piU
          allU_fpi = fst (snd piU)
          cf_pi    = snd (snd piU)
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sb
          v_sel    = fst (snd sb)
          sel_big  = fst (snd (snd sb))
          le_usel  = fst (snd (snd (snd sb)))
          eq_vsel  = snd (snd (snd (snd sb)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

          -- Argument Val2
          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = adSub2 da sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

          -- Extract EqValPi2 from EqVal2 at (FunEl, PiCode)
          eqvpi_fun = snd (snd (snd eqvba))
          A0_eqfun  = REqValPi.domA0 eqvpi_fun
          B0_eqfun  = REqValPi.codB0 eqvpi_fun
          red_eqfun = REqValPi.red eqvpi_fun
          uniq_eqfun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_eqfun))
          eqA_eqfun = fst uniq_eqfun
          eqB_eqfun = snd uniq_eqfun
          paeqv_fun = REqValPi.appEV eqvpi_fun

          -- Transport argument type
          val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_arg
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun (subst-HasType wtsub wfH da)

          -- Apply PiAppEqVal2
          eqval_app_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_arg'
          eqval_app : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_app = S.Eq-transport
            (\ X -> EqVal2 H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_eqfun) eqval_app_raw

          -- Transport chain
          ef_usel  = EvalFun f_pi u_sel
          cft_fpi  = cf_pi
          le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
          evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
          c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
          c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
          evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
          comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
          c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1
          sup_code = Sup ac1 ef_usel
          c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
          le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
          le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
          sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
          fm_u1_sup = finMem-upward u1 ac1 sup_code le_ac_sup c_ac c_sup fm1 sup_U
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          fm_vsel_sup = finMem-upward v_sel ef_usel sup_code le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

          -- ValTy2 at Sup
          evU      = mkSigma tt (LeCode-refl UCode tt)
          fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
          v_fwd    = fst fwd_ac
          evA_vfwd = fst (snd fwd_ac)
          evB_vfwd = snd (snd fwd_ac)
          typed_a_fwd = theorem1 da rho fits v_fwd evA_vfwd
          v_fwd'   = fst typed_a_fwd
          a_fit    = fst (snd typed_a_fwd)
          le_vfwd  = fst (snd (snd typed_a_fwd))
          evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
          fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
          evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
          cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
          cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
          envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
          evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                        ac1 evB_vfwd envle_fwd
          fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
          crho_ext = mkSigma crho cv_fwd'
          dA_loc   = wfCtx-domain (typing-WfCtx dB)
          htA_loc  = subst-HasType wtsub wfH dA_loc
          wtsub_ext = extSub-WtSub wtsub wfH dA_loc (subst-HasType wtsub wfH da)
          wfH_ext  = wf-extend htA_loc
          hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
            in adSub2 da sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (adSub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                          crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
          eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

          fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
          v_fwd_ef = fst fwd_ef
          evA_vfef = fst (snd fwd_ef)
          evB_vfef = snd (snd fwd_ef)
          typed_a_ef = theorem1 da rho fits v_fwd_ef evA_vfef
          v_fwd_ef' = fst typed_a_ef
          a_fit_ef  = fst (snd typed_a_ef)
          le_vfef   = fst (snd (snd typed_a_ef))
          evA_vfef' = fst (snd (snd (snd typed_a_ef)))
          fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
          evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
          cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
          cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
          envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
          evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                        ef_usel evB_vfef envle_ef
          fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
          crho_ef   = mkSigma crho cv_fef'
          hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
            in adSub2 da sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (adSub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

          vt_sup   = ValTy2-Sup H (subst1 sB sa) ac1 ef_usel
                       comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
          eqval_up   = upEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel ef_usel sup_code
                         le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup eqval_app vt_sup
          eqval_res  = restrictEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel u1 sup_code
                         le_u1_vsel' fm_u1_sup fm_vsel_sup eqval_up
          eqval_down = downEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1
                         ac1 sup_code le_ac_sup fm1 c_ac sup_U eqval_res
      in eqval_down

    transported : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_fun

------------------------------------------------------------------------
-- adequacySub2-App-core-body
-- Factored out of mutual block. Takes adequacySub2 as IH.
------------------------------------------------------------------------

adequacySub2-App-core-body : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
  {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
  HasType G0 A U -> HasType (extend G0 A) B U ->
  HasType G0 f' (Pi A B) -> HasType G0 a A ->
  (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
  CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
  WtSub H G0 sigma -> WfCtx H ->
  (u1 : FinEl) -> Coherent u1 ->
  (v0 : FinEl) -> EvalRel a rho v0 ->
  EvalRel f' rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
  -- IH: adequacySub2
  ({g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (sigma0 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 -> ValidSub2 H G1 sigma0 rho0 -> Fits G1 rho0 ->
    WtSub H G1 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0) ->
  -- Val2-U-to-ValTy2
  ({n0 : Nat} {G0 : Ctx n0} {M0 : Expr n0} ->
    (b : FinEl) -> FinMem b UCode -> Val2 G0 M0 U b UCode -> ValTy2 G0 M0 b) ->
  -- app-transport-Val2
  ({n0 : Nat} {H0 : Ctx n0} {M0 A0 : Expr n0} ->
    (ac10 ef0 : FinEl) -> Comp ac10 ef0 ->
    FinMem ac10 UCode -> FinMem ef0 UCode ->
    (vs0 u10 : FinEl) -> FinMem vs0 ef0 -> FinMem u10 ac10 -> LeCode u10 vs0 ->
    ValTy2 H0 A0 ac10 -> ValTy2 H0 A0 ef0 ->
    Val2 H0 M0 A0 vs0 ef0 -> Val2 H0 M0 A0 u10 ac10) ->
  Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u1 ac1
adequacySub2-App-core-body {H = H} {A = A} {B = B} {f' = f'} {a = a}
  dA dB d1 d2 sigma rho crho vs fits wtsub wfH u1 cu1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  adSub2 v2u2vt2 appTransV =
  S.Eq-transport (\ T -> Val2 H (App sf sa) T u1 ac1) (S.Eq-sym eq-sBA) transported
  where
    sf  = substExpr sigma f'
    sa  = substExpr sigma a
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) B
    sBA = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    sing     = cons (mkSigma v0 u1) nil
    cv0      = EvalRel-coh a rho v0 evA_v0

    -- Enlarge function via theorem1
    typed_f  = theorem1 d1 rho fits (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    -- Function's Val2
    val_fun  = adSub2 d1 sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

    -- Dispatch on (ub, ap)
    appVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel f' rho ub -> EvalRel (Pi A B) rho ap ->
      FinMem ub ap ->
      Val2 H sf (Pi sA sB) ub ap ->
      Val2 H (App sf sa) (subst1 sB sa) u1 ac1
    appVal-dispatch Bot          ap    () evFb evPab fmba valba
    appVal-dispatch UCode        ap    () evFb evPab fmba valba
    appVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
    appVal-dispatch PropCode     ap    () evFb evPab fmba valba
    appVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba valba
    appVal-dispatch (PairCode _ _) ap  () evFb evPab fmba valba
    appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
    appVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
      let le_u1_vsel = fst lf
          fmg_big  = fst fmba
          cg_big   = fst (snd fmba)
          piU      = snd (snd fmba)
          b_piU    = fst piU
          allU_fpi = fst (snd piU)
          cf_pi    = snd (snd piU)
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sb
          v_sel    = fst (snd sb)
          sel_big  = fst (snd (snd sb))
          le_usel  = fst (snd (snd (snd sb)))
          eq_vsel  = snd (snd (snd (snd sb)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

          -- Argument Val2
          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = adSub2 d2 sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

          -- Extract PiAppVal2 from function's Val2
          vpi_fun  = snd valba
          A0_fun   = RValPi.domA0 vpi_fun
          B0_fun   = RValPi.codB0 vpi_fun
          red_fun  = RValPi.red vpi_fun
          uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_fun))
          eqA_fun  = fst uniq_fun
          eqB_fun  = snd uniq_fun
          pav_fun  = RValPi.appV vpi_fun

          -- Transport argument type
          val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_fun val_arg
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH d2)

          -- Apply PiAppVal2
          val_app_raw = pav_fun u_sel v_sel sel_big sa ht_sa_A0 val_arg'
          val_app : Val2 H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          val_app = S.Eq-transport
            (\ X -> Val2 H (App sf sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_fun) val_app_raw

          -- Transport: (v_sel, EvalFun f_pi u_sel) -> (u1, ac1)
          ef_usel  = EvalFun f_pi u_sel
          cft_fpi  = cf_pi
          le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
          evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
          c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
          c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
          evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
          comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel

          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi

          -- ValTy2 at ac1
          evU      = mkSigma tt (LeCode-refl UCode tt)
          fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
          v_fwd    = fst fwd_ac
          evA_vfwd = fst (snd fwd_ac)
          evB_vfwd = snd (snd fwd_ac)
          typed_a_fwd = theorem1 d2 rho fits v_fwd evA_vfwd
          v_fwd'   = fst typed_a_fwd
          a_fit    = fst (snd typed_a_fwd)
          le_vfwd  = fst (snd (snd typed_a_fwd))
          evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
          fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
          evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
          cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
          cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
          envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
          evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                        ac1 evB_vfwd envle_fwd
          fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
          crho_ext = mkSigma crho cv_fwd'
          hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
            in adSub2 d2 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          wtsub_ext = extSub-WtSub wtsub wfH dA (subst-HasType wtsub wfH d2)
          wfH_ext  = wf-extend (subst-HasType wtsub wfH dA)
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (adSub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                          crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
          eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

          -- ValTy2 at ef_usel
          fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
          v_fwd_ef = fst fwd_ef
          evA_vfef = fst (snd fwd_ef)
          evB_vfef = snd (snd fwd_ef)
          typed_a_ef = theorem1 d2 rho fits v_fwd_ef evA_vfef
          v_fwd_ef' = fst typed_a_ef
          a_fit_ef  = fst (snd typed_a_ef)
          le_vfef   = fst (snd (snd typed_a_ef))
          evA_vfef' = fst (snd (snd (snd typed_a_ef)))
          fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
          evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
          cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
          cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
          envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
          evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                        ef_usel evB_vfef envle_ef
          fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
          crho_ef   = mkSigma crho cv_fef'
          hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
            in adSub2 d2 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (adSub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

      in appTransV ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app

    transported : Val2 H (App sf sa) (subst1 sB sa) u1 ac1
    transported = appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

------------------------------------------------------------------------
-- adequacyConvSub2-App-core-body
-- Factored out of mutual block. Takes adequacySub2 and adequacyConvSub2 as IH.
------------------------------------------------------------------------

adequacyConvSub2-App-core-body : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType G f (Pi A B) -> HasType G a A ->
  (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' ->
  WtConvSub H G sigma sigma' -> WfCtx H ->
  (u1 : FinEl) ->
  (v0 : FinEl) -> EvalRel a rho v0 ->
  EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
  -- IH: adequacySub2
  ({g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (sigma0 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 -> ValidSub2 H G1 sigma0 rho0 -> Fits G1 rho0 ->
    WtSub H G1 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0) ->
  -- IH: adequacyConvSub2
  ({g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (s1 s2 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 ->
    ValidSub2 H G1 s1 rho0 -> ValidSub2 H G1 s2 rho0 ->
    ValidConvSub2 H G1 s1 s2 rho0 ->
    Fits G1 rho0 ->
    WtSub H G1 s1 -> WtSub H G1 s2 ->
    WtConvSub H G1 s1 s2 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    EqVal2 H (substExpr s1 M0) (substExpr s2 M0) (substExpr s1 A0) u a0) ->
  -- Val2-U-to-ValTy2
  ({n0 : Nat} {G0 : Ctx n0} {M0 : Expr n0} ->
    (b : FinEl) -> FinMem b UCode -> Val2 G0 M0 U b UCode -> ValTy2 G0 M0 b) ->
  -- app-transport-EqVal2
  ({n0 : Nat} {H0 : Ctx n0} {M10 M20 A0 : Expr n0} ->
    (ac10 ef0 : FinEl) -> Comp ac10 ef0 ->
    FinMem ac10 UCode -> FinMem ef0 UCode ->
    (vs0 u10 : FinEl) -> FinMem vs0 ef0 -> FinMem u10 ac10 -> LeCode u10 vs0 ->
    ValTy2 H0 A0 ac10 -> ValTy2 H0 A0 ef0 ->
    EqVal2 H0 M10 M20 A0 vs0 ef0 -> EqVal2 H0 M10 M20 A0 u10 ac10) ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma' f) (substExpr sigma' a))
           (substExpr sigma (subst1 B a))
           u1 ac1
adequacyConvSub2-App-core-body {H = H} {A = A} {B = B} {f = f0} {a = a}
  d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
  u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  adSub2 adConvSub2 v2u2vt2 appTransE =
  S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf' sa') T u1 ac1) (S.Eq-sym eq-sBA) transported
  where
    sf   = substExpr sigma f0
    sf'  = substExpr sigma' f0
    sa   = substExpr sigma a
    sa'  = substExpr sigma' a
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sBA  = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    sing = cons (mkSigma v0 u1) nil
    cv0  = EvalRel-coh a rho v0 evA_v0

    -- Enlarge function via theorem1
    typed_f  = theorem1 d3 rho fits (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    -- EqVal2 for f at two subs
    eqval_f = adConvSub2 d3 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                u_big evF_big a_pi evPi fm_big

    -- Dispatch on (ub, ap)
    appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
      FinMem ub ap ->
      EqVal2 H sf sf' (Pi sA sB) ub ap ->
      EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
    appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
    appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
    appEqVal-dispatch PropCode     ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba eqvba
    appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba eqvba
    appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
      let le_u1_vsel = fst lf
          fmg_big  = fst fmba
          cg_big   = fst (snd fmba)
          piU      = snd (snd fmba)
          b_piU    = fst piU
          allU_fpi = fst (snd piU)
          cf_pi    = snd (snd piU)
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sb
          v_sel    = fst (snd sb)
          sel_big  = fst (snd (snd sb))
          le_usel  = fst (snd (snd (snd sb)))
          eq_vsel  = snd (snd (snd (snd sb)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          cv_sel   = Coherent-Selection-val sel_big (cft-from-cf g_big cg_big)

          -- Argument evaluation data
          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU

          -- Common coherence
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel

          -- ===== FUNCTION VARIATION: App sf sa vs App sf' sa =====
          eqvpi_fun = snd (snd (snd eqvba))
          A0_eqfun  = REqValPi.domA0 eqvpi_fun
          B0_eqfun  = REqValPi.codB0 eqvpi_fun
          red_eqfun = REqValPi.red eqvpi_fun
          uniq_eqfun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_eqfun))
          eqA_eqfun = fst uniq_eqfun
          eqB_eqfun = snd uniq_eqfun
          paeqv_fun = REqValPi.appEV eqvpi_fun

          -- Val2 for sa at sA
          val_sa = adSub2 d4 sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi
          val_sa_A0 = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_sa
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun (subst-HasType wtsub wfH d4)

          -- Apply PiAppEqVal2
          eqval_fun_var_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_sa_A0
          eqval_fun_var : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_fun_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_eqfun) eqval_fun_var_raw

          -- ===== ARGUMENT VARIATION: App sf' sa vs App sf' sa' =====
          vpi_sf'  = fst (snd (snd eqvba))
          A0_sf'   = RValPi.domA0 vpi_sf'
          B0_sf'   = RValPi.codB0 vpi_sf'
          red_sf'  = RValPi.red vpi_sf'
          uniq_sf' = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_sf'))
          eqA_sf'  = fst uniq_sf'
          eqB_sf'  = snd uniq_sf'
          pae_sf'  = RValPi.appE vpi_sf'

          -- HasType and ConvTm for arguments
          htSa     = subst-HasType wtsub wfH d4
          htSa'raw = subst-HasType wtsub' wfH d4
          cvAA'    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
          htSA     = subst-HasType wtsub wfH d1
          htSa'sA  = ty-conv htSa'raw (conv-sym cvAA') htSA
          cvSaSa'  = subst-ConvTm-cross d4 wtsub wtsub' wcs wfH

          -- Transport to A0_sf'
          htSa_A0    = S.Eq-transport (\ X -> HasType H sa X) eqA_sf' htSa
          htSa'_A0   = S.Eq-transport (\ X -> HasType H sa' X) eqA_sf' htSa'sA
          cvSaSa'_A0 = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_sf' cvSaSa'

          -- EqVal2 for sa vs sa' via adConvSub2
          eqval_arg = adConvSub2 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                        u_sel evA_usel b_pi evA_bpi fm_usel_bpi
          eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_sf' eqval_arg

          -- Apply PiAppEq2
          eqval_arg_var_raw = pae_sf' u_sel v_sel sel_big sa sa' htSa_A0 htSa'_A0 cvSaSa'_A0 eqval_arg_A0
          eqval_arg_var : EqVal2 H (App sf' sa) (App sf' sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_arg_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf' sa) (App sf' sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_sf') eqval_arg_var_raw

          -- ===== COMBINE via EqVal2-trans =====
          eqval_combined = EqVal2-trans v_sel (EvalFun f_pi u_sel) cv_sel c_efusel eqval_fun_var eqval_arg_var

          -- ===== TRANSPORT CHAIN =====
          ef_usel  = EvalFun f_pi u_sel
          cft_fpi  = cf_pi
          le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
          evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
          c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
          evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
          comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
          c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1
          sup_code = Sup ac1 ef_usel
          c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
          le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
          le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
          sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
          fm_u1_sup = finMem-upward u1 ac1 sup_code le_ac_sup c_ac c_sup fm1 sup_U
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          fm_vsel_sup = finMem-upward v_sel ef_usel sup_code le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

          -- ValTy2 at Sup
          evU      = mkSigma tt (LeCode-refl UCode tt)
          fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
          v_fwd    = fst fwd_ac
          evA_vfwd = fst (snd fwd_ac)
          evB_vfwd = snd (snd fwd_ac)
          typed_a_fwd = theorem1 d4 rho fits v_fwd evA_vfwd
          v_fwd'   = fst typed_a_fwd
          a_fit    = fst (snd typed_a_fwd)
          le_vfwd  = fst (snd (snd typed_a_fwd))
          evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
          fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
          evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
          cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
          cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
          envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
          evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                        ac1 evB_vfwd envle_fwd
          fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
          crho_ext = mkSigma crho cv_fwd'
          htA_loc  = subst-HasType wtsub wfH d1
          wtsub_ext = extSub-WtSub wtsub wfH d1 htSa
          hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
            in adSub2 d4 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (adSub2 d2 (extSub sigma sa) (extendEnv rho v_fwd')
                          crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
          eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

          fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
          v_fwd_ef = fst fwd_ef
          evA_vfef = fst (snd fwd_ef)
          evB_vfef = snd (snd fwd_ef)
          typed_a_ef = theorem1 d4 rho fits v_fwd_ef evA_vfef
          v_fwd_ef' = fst typed_a_ef
          a_fit_ef  = fst (snd typed_a_ef)
          le_vfef   = fst (snd (snd typed_a_ef))
          evA_vfef' = fst (snd (snd (snd typed_a_ef)))
          fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
          evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
          cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
          cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
          envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
          evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                        ef_usel evB_vfef envle_ef
          fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
          crho_ef   = mkSigma crho cv_fef'
          hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
            let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
            in adSub2 d4 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (adSub2 d2 (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

      in appTransE ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

    transported : EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f
