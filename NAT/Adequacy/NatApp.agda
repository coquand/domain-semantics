{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Adequacy.NatApp.agda
--
-- The value-level / non-dependent-codomain application core for the Nat
-- eliminator.  Given the succ-branch function b : Pi NatT (wkExpr C) (a
-- G-subterm, with its single-sub IH) applied to an argument value, and the
-- motive C's IH, produces the Val2 of the application at the non-dependent
-- type C.  This is what both conv-case-suc (argument a G-subterm m) and
-- ty-Case's SucEl branch (argument the SEMANTIC predecessor) head-expand onto.
--
-- It is a port of Adequacy.Cases.adequacySub2-App-core-body with:
--   * codomain B fixed to wkExpr C (non-dependent): the IHB-based vt_ac/vt_ef
--     forwarding collapses to IH-C + EvalRel-Pi-body + EvalRel-unwk;
--   * the argument decoupled from a G-level expression: supplied as an
--     H-level term N + typing + a "value provider" argVal.
-- No postulates.
------------------------------------------------------------------------

module NAT.Adequacy.NatApp where

open import NAT.Adequacy.HeadRed
open import NAT.Adequacy.Pi using (Adq ; Val2-U-to-ValTy2)
open import NAT.Adequacy.App using (app-transport-Val2 ; app-transport-EqVal2)
open import NAT.Adequacy.Records using (RValPiP ; un-ValPi ; REqValPiP ; un-REqValPi ; eqvalPi-snd)

import NAT.Domain.Basic as S
open S using (Nat ; suc ; max ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ;
  NatCode ; ZeroEl ; SucEl ; FinFun ; nil ; cons ; Eq ; refl ; Eq-cong ; Eq-trans ; Eq-transport ; Eq-sym)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; CoherentFunTail ; CFTcons ;
  EvalFun ; Comp ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMem-a-in-U ;
  coh-from-aU ; FinMem-coh-u ; cft-from-cf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open CFTcons
open import NAT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ;
  EvalRel-Comp ; EvalRel-down)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; App ; NatT ; subst1 ; subst1Sub ; Sub ; liftSub ;
  substExpr ; wkExpr)
open import NAT.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx)
open import NAT.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val)
open import NAT.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import NAT.Model.Selection using (selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain)
open import NAT.Model.EvalSubstitution using (EvalRel-Pi-body ; EvalRel-unwk)
open import NAT.Model.Soundness using (theorem1)
open import NAT.Model.SoundnessLemmas using (Fits)
open import NAT.Syntax.Substitution using (WtSub ; subst-HasType ; subst1-wk)
open import NAT.Syntax.Raw using (subst-wk-comm)
open import NAT.Syntax.Reduction using (Red ; mkRed ; Red-refl)
open import NAT.Validity.Stratified using (Red3)

------------------------------------------------------------------------
-- adequacyV-app-Nat
------------------------------------------------------------------------

adequacyV-app-Nat : {h g : Nat} {H : Ctx h} {G : Ctx g} {C b : Expr g} ->
  HasType G C U -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G C U -> Adq G b (Pi NatT (wkExpr C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (v u1 : FinEl) ->
  EvalRel b rho (FunEl (cons (mkSigma v u1) nil)) ->
  (N : Expr h) -> HasType H N NatT ->
  ((u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
     Val2 H N NatT u' a') ->
  (ac1 : FinEl) -> EvalRel C rho ac1 -> FinMem u1 ac1 ->
  Val2 H (App (substExpr sigma b) N) (substExpr sigma C) u1 ac1
adequacyV-app-Nat {H = H} {G = G} {C = C} {b = b}
  dC db IHC IHb sigma rho crho vs fits wtsub wfH v u1 evF_sing N htN argVal ac1 evAc1 fm1 =
  S.Eq-transport (\ T -> Val2 H (App sf N) T u1 ac1) eq-sBN transported
  where
    sf  = substExpr sigma b
    sC  = substExpr sigma C
    sA  = substExpr sigma NatT       -- = NatT
    sB  = substExpr (liftSub sigma) (wkExpr C)
    sing = cons (mkSigma v u1) nil
    cv0  = key-coh (EvalRel-coh b rho (FunEl sing) evF_sing)

    eq-sBN : Eq (subst1 sB N) sC
    eq-sBN = Eq-trans (Eq-cong (\ X -> substExpr (subst1Sub N) X) (subst-wk-comm sigma C))
                      (subst1-wk sC N)

    appVal-dispatch : (ub ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel b rho ub -> EvalRel (Pi NatT (wkExpr C)) rho ap ->
      FinMem ub ap ->
      Val2 H sf (Pi sA sB) ub ap ->
      Val2 H (App sf N) (subst1 sB N) u1 ac1
    appVal-dispatch Bot          ap () evFb evPab fmba valba
    appVal-dispatch UCode        ap () evFb evPab fmba valba
    appVal-dispatch (PiCode _ _) ap () evFb evPab fmba valba
    appVal-dispatch (FunEl g_big) Bot          lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) UCode        lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) NatCode      lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) ZeroEl       lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) (SucEl _)    lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
      let le_u1_vsel = fst lf
          fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
          piU      = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU    = finMem-piU-dom b_pi f_pi piU
          allU_fpi = finMem-piU-allU b_pi f_pi piU
          cf_pi    = finMem-piU-cft b_pi f_pi piU
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sbel     = selectionBelow g_big v (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sbel
          v_sel    = fst (snd sbel)
          sel_big  = fst (snd (snd sbel))
          le_usel  = fst (snd (snd (snd sbel)))
          eq_vsel  = snd (snd (snd (snd sbel)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = argVal u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          vpi_fun  = un-ValPi valba
          A0_fun   = RValPiP.domA0 vpi_fun
          B0_fun   = RValPiP.codB0 vpi_fun
          red_fun  = RValPiP.red vpi_fun
          uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_fun))
          eqA_fun  = fst uniq_fun
          eqB_fun  = snd uniq_fun
          pav_fun  = RValPiP.appV vpi_fun
          val_arg' = S.Eq-transport (\ X -> Val2 H N X u_sel b_pi) eqA_fun val_arg
          ht_N_A0  = S.Eq-transport (\ X -> HasType H N X) eqA_fun htN
          val_app_raw = pav_fun u_sel v_sel sel_big N ht_N_A0 val_arg'
          val_app : Val2 H (App sf N) (subst1 sB N) v_sel (EvalFun f_pi u_sel)
          val_app = S.Eq-transport
            (\ X -> Val2 H (App sf N) (subst1 X N) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_fun) val_app_raw
          ef_usel  = EvalFun f_pi u_sel
          evCod_ef = EvalRel-Pi-body NatT (wkExpr C) rho b_pi f_pi u_sel crho cu_sel evPab
          evC_ef   = EvalRel-unwk C rho u_sel ef_usel evCod_ef
          comp_ac_ef = EvalRel-Comp C rho crho ac1 ef_usel evAc1 evC_ef
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          evU      = mkSigma tt (LeCode-refl UCode tt)
          vt_ac_C  = Val2-U-to-ValTy2 ac1 ac1_U
                       (IHC sigma rho crho vs fits wtsub wfH ac1 evAc1 UCode evU ac1_U)
          vt_ef_C  = Val2-U-to-ValTy2 ef_usel ef_uselU
                       (IHC sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) (S.Eq-sym eq-sBN) vt_ac_C
          vt_ef    = S.Eq-transport (\ T -> ValTy2 H T ef_usel) (S.Eq-sym eq-sBN) vt_ef_C
      in app-transport-Val2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app

    transported : Val2 H (App sf N) (subst1 sB N) u1 ac1
    transported =
      let typed_f = theorem1 db rho fits (FunEl sing) evF_sing
          u_big   = fst typed_f
          a_pi    = fst (snd typed_f)
          le_sing = fst (snd (snd typed_f))
          evF_big = fst (snd (snd (snd typed_f)))
          fm_big  = fst (snd (snd (snd (snd typed_f))))
          evPi    = snd (snd (snd (snd (snd typed_f))))
          val_fun = IHb sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big
      in appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

------------------------------------------------------------------------
-- adequacyVE-app-Nat : the EqVal2 cross version.  Function FL=σb vs FR
-- (FR a free H-term -- σ'b for ty-Case cross, σb' for conv-Case), arguments
-- NL vs NR (H-level), both varying.  Composes the function-variation (appEV of
-- the function's cross-validity) with the argument-variation (appE of FR's
-- single validity) via EqVal2-trans.  Port of AppInj's inj core, codomain
-- non-dependent (IH-C + EvalRel-Pi-body + unwk), arguments decoupled.
------------------------------------------------------------------------

adequacyVE-app-Nat : {h g : Nat} {H : Ctx h} {G : Ctx g} {C b : Expr g}
  {FR NL NR : Expr h} ->
  HasType G C U -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G C U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (v u1 : FinEl) ->
  EvalRel b rho (FunEl (cons (mkSigma v u1) nil)) ->
  ((ub ap : FinEl) -> EvalRel b rho ub -> EvalRel (Pi NatT (wkExpr C)) rho ap -> FinMem ub ap ->
    EqVal2 H (substExpr sigma b) FR (substExpr sigma (Pi NatT (wkExpr C))) ub ap) ->
  HasType H NL NatT -> HasType H NR NatT -> ConvTm H NL NR NatT ->
  ((u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
     Val2 H NL NatT u' a') ->
  ((u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
     EqVal2 H NL NR NatT u' a') ->
  (ac1 : FinEl) -> EvalRel C rho ac1 -> FinMem u1 ac1 ->
  EqVal2 H (App (substExpr sigma b) NL) (App FR NR) (substExpr sigma C) u1 ac1
adequacyVE-app-Nat {H = H} {G = G} {C = C} {b = b} {FR = FR} {NL = NL} {NR = NR}
  dC db IHC sigma rho crho vs fits wtsub wfH v u1 evF_sing funcross
  htNL htNR cvNLNR argValL argEq ac1 evAc1 fm1 =
  S.Eq-transport (\ T -> EqVal2 H (App sf NL) (App FR NR) T u1 ac1) eq-sBN transported
  where
    sf  = substExpr sigma b
    sC  = substExpr sigma C
    sA  = substExpr sigma NatT
    sB  = substExpr (liftSub sigma) (wkExpr C)
    sing = cons (mkSigma v u1) nil
    cv0  = key-coh (EvalRel-coh b rho (FunEl sing) evF_sing)

    eq-sBN : Eq (subst1 sB NL) sC
    eq-sBN = Eq-trans (Eq-cong (\ X -> substExpr (subst1Sub NL) X) (subst-wk-comm sigma C))
                      (subst1-wk sC NL)

    appEqVal-dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
      EvalRel b rho ub -> EvalRel (Pi NatT (wkExpr C)) rho ap -> FinMem ub ap ->
      EqVal2 H sf FR (Pi sA sB) ub ap ->
      EqVal2 H (App sf NL) (App FR NR) (subst1 sB NL) u1 ac1
    appEqVal-dispatch Bot          ap () evFb evPab fmba eqvba
    appEqVal-dispatch UCode        ap () evFb evPab fmba eqvba
    appEqVal-dispatch (PiCode _ _) ap () evFb evPab fmba eqvba
    appEqVal-dispatch (FunEl g_big) Bot         lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) UCode       lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (FunEl _)   lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) NatCode     lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) ZeroEl      lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (SucEl _)   lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
      let le_u1_vsel = fst lf
          fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
          piU      = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU    = finMem-piU-dom b_pi f_pi piU
          allU_fpi = finMem-piU-allU b_pi f_pi piU
          cf_pi    = finMem-piU-cft b_pi f_pi piU
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sbel     = selectionBelow g_big v (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sbel
          v_sel    = fst (snd sbel)
          sel_big  = fst (snd (snd sbel))
          le_usel  = fst (snd (snd (snd sbel)))
          eq_vsel  = snd (snd (snd (snd sbel)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          cv_sel   = Coherent-Selection-val sel_big (cft-from-cf g_big cg_big)
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
          -- function variation: App sf NL vs App FR NL
          eqvpi_fun = un-REqValPi eqvba
          eqA_ef   = fst (Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr (REqValPiP.red eqvpi_fun))))
          eqB_ef   = snd (Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr (REqValPiP.red eqvpi_fun))))
          paeqv    = REqValPiP.appEV eqvpi_fun
          val_NL   = argValL u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          val_NL_A0 = S.Eq-transport (\ X -> Val2 H NL X u_sel b_pi) eqA_ef val_NL
          htNL_A0  = S.Eq-transport (\ X -> HasType H NL X) eqA_ef htNL
          eqval_fun_raw = paeqv u_sel v_sel sel_big NL htNL_A0 val_NL_A0
          eqval_fun_var : EqVal2 H (App sf NL) (App FR NL) (subst1 sB NL) v_sel (EvalFun f_pi u_sel)
          eqval_fun_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf NL) (App FR NL) (subst1 X NL) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_ef) eqval_fun_raw
          -- argument variation: App FR NL vs App FR NR
          vpi_FR   = eqvalPi-snd eqvba
          eqA_FR   = fst (Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr (RValPiP.red vpi_FR))))
          eqB_FR   = snd (Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr (RValPiP.red vpi_FR))))
          pae_FR   = RValPiP.appE vpi_FR
          htNL_AFR = S.Eq-transport (\ X -> HasType H NL X) eqA_FR htNL
          htNR_AFR = S.Eq-transport (\ X -> HasType H NR X) eqA_FR htNR
          cvNLNR_AFR = S.Eq-transport (\ X -> ConvTm H NL NR X) eqA_FR cvNLNR
          eqval_arg = argEq u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H NL NR X u_sel b_pi) eqA_FR eqval_arg
          eqval_arg_raw = pae_FR u_sel v_sel sel_big NL NR htNL_AFR htNR_AFR cvNLNR_AFR eqval_arg_A0
          eqval_arg_var : EqVal2 H (App FR NL) (App FR NR) (subst1 sB NL) v_sel (EvalFun f_pi u_sel)
          eqval_arg_var = S.Eq-transport
            (\ X -> EqVal2 H (App FR NL) (App FR NR) (subst1 X NL) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_FR) eqval_arg_raw
          eqval_combined = EqVal2-trans v_sel (EvalFun f_pi u_sel) cv_sel c_efusel
                             eqval_fun_var eqval_arg_var
          ef_usel  = EvalFun f_pi u_sel
          evCod_ef = EvalRel-Pi-body NatT (wkExpr C) rho b_pi f_pi u_sel crho cu_sel evPab
          evC_ef   = EvalRel-unwk C rho u_sel ef_usel evCod_ef
          comp_ac_ef = EvalRel-Comp C rho crho ac1 ef_usel evAc1 evC_ef
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          evU      = mkSigma tt (LeCode-refl UCode tt)
          vt_ac_C  = Val2-U-to-ValTy2 ac1 ac1_U
                       (IHC sigma rho crho vs fits wtsub wfH ac1 evAc1 UCode evU ac1_U)
          vt_ef_C  = Val2-U-to-ValTy2 ef_usel ef_uselU
                       (IHC sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) (S.Eq-sym eq-sBN) vt_ac_C
          vt_ef    = S.Eq-transport (\ T -> ValTy2 H T ef_usel) (S.Eq-sym eq-sBN) vt_ef_C
      in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

    transported : EqVal2 H (App sf NL) (App FR NR) (subst1 sB NL) u1 ac1
    transported =
      let typed_f = theorem1 db rho fits (FunEl sing) evF_sing
          u_big   = fst typed_f
          a_pi    = fst (snd typed_f)
          le_sing = fst (snd (snd typed_f))
          evF_big = fst (snd (snd (snd typed_f)))
          fm_big  = fst (snd (snd (snd (snd typed_f))))
          evPi    = snd (snd (snd (snd (snd typed_f))))
          eqval_f = funcross u_big a_pi evF_big evPi fm_big
      in appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f
