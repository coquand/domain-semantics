{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Adequacy.YCross.agda
--
-- The EqVal2 ("twin") adequacy for the fixpoint  Y g, covering the three
-- driver dispatches:
--   * adequacyConvSub2 (ty-Y …)     — cross-substitution  Y σg  vs  Y σ'g
--   * adequacyEqSub2  (conv-Y …)     — unfolding   Y σg = App σg (Y σg)
--   * adequacyEqSub2  (conv-Y-cong …)— congruence  Y σg  vs  Y σg'
--
-- The cross and congruence cases share a single EqVal2 App-core (the
-- contractum  App F1 (Y F1)  vs  App F2 (Y F2)), built by a Kleene-stage
-- recursion (adequacyEqV-Y-approx) that mirrors the value YCore.  F1 is
-- always  substExpr σ gg; only F2, the second function term, and the
-- function-side EqVal2 differ between the two cases (driver-supplied).
--
-- 0 postulates, 0 TERMINATING.
------------------------------------------------------------------------

module NAT.Adequacy.YCross where

open import NAT.Adequacy.HeadRed
open import NAT.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2)
open import NAT.Adequacy.VE using (AdqE1)
open import NAT.Adequacy.App using (app-transport-EqVal2)
open import NAT.Adequacy.YCore using (adequacyV-Y-approx)

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ; List ; nil ; cons)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; CoherentFun ; CoherentFunTail ;
  EvalFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ;
  finMemUCode-Sup ; finMem-upward ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; NotBot ; absurdEl ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ;
  finMem-funel-wf)
open import NAT.Syntax.Reduction using (Red ; mkRed ; Red-refl ; HeadRed ; headred-step ; headred-refl ;
  headred-Y ; subst-subst1-comm)
open import NAT.Domain.Membership using (finMem-bot-from)
open import NAT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ;
  EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ; Approx)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; Lam ; App ; Y ; Fin ; fzero ; fsuc ; wkExpr ;
  subst1 ; Sub ; liftSub ; substExpr)
open import NAT.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Y ; conv-refl ; conv-sym ; conv-conv ; conv-Y ; conv-Y-cong)
open import NAT.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val ;
  FinMem-Coherent)
open import NAT.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import NAT.Model.Selection using (FinMemAllU-Selection ; selectionBelow ; FinMem-Selection ;
  FinMem-Selection-codomain)
open import NAT.Model.EvalSubstitution using (EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import NAT.Model.Soundness using (convSound ; convSound-inv ; convSound' ; theorem1)
open import NAT.Syntax.Substitution using (typing-ConvTm ; WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm ;
  subst-ConvTm-cross ; liftSub-WtSub ; typing-WfCtx ; typing-type ; wk-HasType ; subst1-wk)
open import NAT.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- adequacyEqV-Y-App-core : EqVal2 of the contractum  App F1 (Y F1)  vs
-- App F2 (Y F2), where F1 = substExpr σ gg.
------------------------------------------------------------------------

adequacyEqV-Y-App-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (F2 : Expr h) ->
  HasType H (Y F2) (substExpr sigma A) ->
  ConvTm H (substExpr sigma (Y gg)) (Y F2) (substExpr sigma A) ->
  (u1 : FinEl) ->
  (v0 : FinEl) -> (j : Nat) ->
  Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) j v0 ->
  EvalRel gg rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel A rho ac1 -> FinMem u1 ac1 ->
  Adq G A U ->
  ((ub : FinEl) -> EvalRel gg rho ub -> (ap : FinEl) -> EvalRel (Pi A (wkExpr A)) rho ap -> FinMem ub ap ->
     EqVal2 H (substExpr sigma gg) F2
       (Pi (substExpr sigma A) (substExpr (liftSub sigma) (wkExpr A))) ub ap) ->
  ((u' : FinEl) ->
    Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) j u' ->
    (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' ->
    Val2 H (substExpr sigma (Y gg)) (substExpr sigma A) u' a') ->
  ((u' : FinEl) ->
    Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) j u' ->
    (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' ->
    EqVal2 H (substExpr sigma (Y gg)) (Y F2) (substExpr sigma A) u' a') ->
  EqVal2 H (App (substExpr sigma gg) (substExpr sigma (Y gg)))
           (App F2 (Y F2)) (substExpr sigma A) u1 ac1
adequacyEqV-Y-App-core {H = H} {A = A} {gg = gg}
  aU dg sigma rho crho vs fits wtsub wfH F2 htF2 cvF1F2 u1 v0 j apj evF_sing ac1 evA_ac1 fm1
  IHA funcEq valArg eqArg =
  S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App F2 (Y F2)) T u1 ac1) eq-sBA-sA
    (S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App F2 (Y F2)) T u1 ac1) (S.Eq-sym eq-sBA) transported)
  where
    sf  = substExpr sigma gg
    sa  = substExpr sigma (Y gg)
    sa' = Y F2
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) (wkExpr A)
    sBA = substExpr sigma (subst1 (wkExpr A) (Y gg))
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma (wkExpr A) (Y gg))
    eq-sBA-sA : Eq sBA sA
    eq-sBA-sA = S.Eq-cong (substExpr sigma) (subst1-wk A (Y gg))
    eq-sBsa-sA : Eq (subst1 sB sa) sA
    eq-sBsa-sA = Eq-trans (S.Eq-sym eq-sBA) eq-sBA-sA

    htF1 : HasType H sa sA
    htF1 = subst-HasType wtsub wfH (ty-Y aU dg)

    evA_v0 : EvalRel (Y gg) rho v0
    evA_v0 = mkSigma j apj
    evAc1 : EvalRel (subst1 (wkExpr A) (Y gg)) rho ac1
    evAc1 = S.Eq-transport (\ T -> EvalRel T rho ac1) (S.Eq-sym (subst1-wk A (Y gg))) evA_ac1

    sing = cons (mkSigma v0 u1) nil
    cv0  = EvalRel-coh (Y gg) rho v0 evA_v0

    -- Value of the argument Y F1 at a down-closed u' ≤ v0 (stage j).
    yValArg : (u' : FinEl) -> Coherent u' -> LeCode u' v0 ->
      (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' -> Val2 H sa sA u' a'
    yValArg Bot cu' le' a' evA' fm' = Val2-Bot a'
    yValArg UCode cu' le' a' evA' fm' =
      valArg UCode (snd (EvalRel-down (Y gg) rho v0 UCode crho cu' evA_v0 le')) a' evA' fm'
    yValArg (FunEl g0) cu' le' a' evA' fm' =
      valArg (FunEl g0) (snd (EvalRel-down (Y gg) rho v0 (FunEl g0) crho cu' evA_v0 le')) a' evA' fm'
    yValArg (PiCode a0 f0) cu' le' a' evA' fm' =
      valArg (PiCode a0 f0) (snd (EvalRel-down (Y gg) rho v0 (PiCode a0 f0) crho cu' evA_v0 le')) a' evA' fm'
    yValArg NatCode cu' le' a' evA' fm' =
      valArg NatCode (snd (EvalRel-down (Y gg) rho v0 NatCode crho cu' evA_v0 le')) a' evA' fm'
    yValArg ZeroEl cu' le' a' evA' fm' =
      valArg ZeroEl (snd (EvalRel-down (Y gg) rho v0 ZeroEl crho cu' evA_v0 le')) a' evA' fm'
    yValArg (SucEl w0) cu' le' a' evA' fm' =
      valArg (SucEl w0) (snd (EvalRel-down (Y gg) rho v0 (SucEl w0) crho cu' evA_v0 le')) a' evA' fm'

    -- EqVal2 of the argument  Y F1 vs Y F2  at a down-closed u' (stage j).
    yEqArg : (u' : FinEl) -> Coherent u' -> LeCode u' v0 ->
      (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' -> EqVal2 H sa sa' sA u' a'
    yEqArg Bot cu' le' a' evA' fm' = EqVal2-Bot a'
    yEqArg UCode cu' le' a' evA' fm' =
      eqArg UCode (snd (EvalRel-down (Y gg) rho v0 UCode crho cu' evA_v0 le')) a' evA' fm'
    yEqArg (FunEl g0) cu' le' a' evA' fm' =
      eqArg (FunEl g0) (snd (EvalRel-down (Y gg) rho v0 (FunEl g0) crho cu' evA_v0 le')) a' evA' fm'
    yEqArg (PiCode a0 f0) cu' le' a' evA' fm' =
      eqArg (PiCode a0 f0) (snd (EvalRel-down (Y gg) rho v0 (PiCode a0 f0) crho cu' evA_v0 le')) a' evA' fm'
    yEqArg NatCode cu' le' a' evA' fm' =
      eqArg NatCode (snd (EvalRel-down (Y gg) rho v0 NatCode crho cu' evA_v0 le')) a' evA' fm'
    yEqArg ZeroEl cu' le' a' evA' fm' =
      eqArg ZeroEl (snd (EvalRel-down (Y gg) rho v0 ZeroEl crho cu' evA_v0 le')) a' evA' fm'
    yEqArg (SucEl w0) cu' le' a' evA' fm' =
      eqArg (SucEl w0) (snd (EvalRel-down (Y gg) rho v0 (SucEl w0) crho cu' evA_v0 le')) a' evA' fm'

    typed_f  = theorem1 dg rho fits (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    eqval_f = funcEq u_big evF_big a_pi evPi fm_big

    appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel gg rho ub -> EvalRel (Pi A (wkExpr A)) rho ap ->
      FinMem ub ap ->
      EqVal2 H sf F2 (Pi sA sB) ub ap ->
      EqVal2 H (App sf sa) (App F2 sa') (subst1 sB sa) u1 ac1
    appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
    appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
    appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
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

          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel

          -- ===== FUNCTION VARIATION =====
          eqvpi_fun = un-REqValPi eqvba
          red_eqfun = REqValPi.red eqvpi_fun
          uniq_eqfun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_eqfun))
          eqA_eqfun = fst uniq_eqfun
          eqB_eqfun = snd uniq_eqfun
          paeqv_fun = REqValPi.appEV eqvpi_fun

          val_sa = yValArg u_sel cu_sel le_usel b_pi evA_bpi fm_usel_bpi
          val_sa_A0 = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_sa
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun htF1

          eqval_fun_var_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_sa_A0
          eqval_fun_var : EqVal2 H (App sf sa) (App F2 sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_fun_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf sa) (App F2 sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_eqfun) eqval_fun_var_raw

          -- ===== ARGUMENT VARIATION =====
          vpi_sf'  = eqvalPi-snd eqvba
          red_sf'  = RValPi.red vpi_sf'
          uniq_sf' = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_sf'))
          eqA_sf'  = fst uniq_sf'
          eqB_sf'  = snd uniq_sf'
          pae_sf'  = RValPi.appE vpi_sf'

          htSa_A0    = S.Eq-transport (\ X -> HasType H sa X) eqA_sf' htF1
          htSa'_A0   = S.Eq-transport (\ X -> HasType H sa' X) eqA_sf' htF2
          cvSaSa'_A0 = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_sf' cvF1F2

          eqval_arg = yEqArg u_sel cu_sel le_usel b_pi evA_bpi fm_usel_bpi
          eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_sf' eqval_arg

          eqval_arg_var_raw = pae_sf' u_sel v_sel sel_big sa sa' htSa_A0 htSa'_A0 cvSaSa'_A0 eqval_arg_A0
          eqval_arg_var : EqVal2 H (App F2 sa) (App F2 sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_arg_var = S.Eq-transport
            (\ X -> EqVal2 H (App F2 sa) (App F2 sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_sf') eqval_arg_var_raw

          eqval_combined = EqVal2-trans v_sel (EvalFun f_pi u_sel) cv_sel c_efusel eqval_fun_var eqval_arg_var

          -- ===== TRANSPORT CHAIN =====
          ef_usel  = EvalFun f_pi u_sel
          le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cf_pi cu_sel cv0
          evBa_efv = EvalRel-Pi-app-type A (wkExpr A) (Y gg) rho b_pi f_pi v0 crho evPab evA_v0
          evBa_efusel = EvalRel-down (subst1 (wkExpr A) (Y gg)) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
          comp_ac_ef = EvalRel-Comp (subst1 (wkExpr A) (Y gg)) rho crho ac1 ef_usel evAc1 evBa_efusel
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi

          evU      = mkSigma tt (LeCode-refl UCode tt)
          evA_efusel = S.Eq-transport (\ T -> EvalRel T rho ef_usel) (subst1-wk A (Y gg)) evBa_efusel
          vtA_ac   = Val2-U-to-ValTy2 ac1 ac1_U
                       (IHA sigma rho crho vs fits wtsub wfH ac1 evA_ac1 UCode evU ac1_U)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) (S.Eq-sym eq-sBsa-sA) vtA_ac
          vtA_ef   = Val2-U-to-ValTy2 ef_usel ef_uselU
                       (IHA sigma rho crho vs fits wtsub wfH ef_usel evA_efusel UCode evU ef_uselU)
          vt_ef    = S.Eq-transport (\ T -> ValTy2 H T ef_usel) (S.Eq-sym eq-sBsa-sA) vtA_ef

      in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

    transported : EqVal2 H (App sf sa) (App F2 sa') (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f

------------------------------------------------------------------------
-- adequacyEqV-Y-approx : EqVal2  Y σg  vs  Y F2  by structural recursion
-- on the Kleene index n.  Shared by the cross- and congruence-drivers.
------------------------------------------------------------------------

adequacyEqV-Y-approx : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (F2 : Expr h) ->
  HasType H (Y F2) (substExpr sigma A) ->
  ConvTm H (substExpr sigma (Y gg)) (Y F2) (substExpr sigma A) ->
  ConvTm H (Y F2) (App F2 (Y F2)) (substExpr sigma A) ->
  Adq G gg (Pi A (wkExpr A)) -> Adq G A U ->
  ((ub : FinEl) -> EvalRel gg rho ub -> (ap : FinEl) -> EvalRel (Pi A (wkExpr A)) rho ap -> FinMem ub ap ->
     EqVal2 H (substExpr sigma gg) F2
       (Pi (substExpr sigma A) (substExpr (liftSub sigma) (wkExpr A))) ub ap) ->
  (n : Nat) -> (u : FinEl) ->
  Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) n u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma (Y gg)) (Y F2) (substExpr sigma A) u a
adequacyEqV-Y-approx {H = H} {A = A} {gg = gg} aU dg sigma rho crho vs fits wtsub wfH
  F2 htF2 cvF1F2 cvY2 IHg IHA funcEq zero u ap a evA fm =
  restrictEqVal2 H (substExpr sigma (Y gg)) (Y F2) (substExpr sigma A) Bot u a
    (snd ap) fm (finMem-bot-from a (FinMem-a-in-U u a fm)) (EqVal2-Bot a)
adequacyEqV-Y-approx {H = H} {A = A} {gg = gg} aU dg sigma rho crho vs fits wtsub wfH
  F2 htF2 cvF1F2 cvY2 IHg IHA funcEq (suc j) u ap a evA fm =
  let v0   = fst ap
      apj  = fst (snd ap)
      edge = snd (snd ap)
      valApp = adequacyEqV-Y-App-core aU dg sigma rho crho vs fits wtsub wfH
                 F2 htF2 cvF1F2 u v0 j apj edge a evA fm IHA funcEq
                 (adequacyV-Y-approx aU dg sigma rho crho vs fits wtsub wfH IHg IHA j)
                 (adequacyEqV-Y-approx aU dg sigma rho crho vs fits wtsub wfH
                    F2 htF2 cvF1F2 cvY2 IHg IHA funcEq j)
  in EqVal2-headred-expand u a (headred-step headred-Y headred-refl)
       (headred-step headred-Y headred-refl)
       (subst-ConvTm wtsub wfH (conv-Y aU dg)) cvY2 valApp

------------------------------------------------------------------------
-- Driver 1: cross-substitution  adequacyConvSub2 (ty-Y …)
------------------------------------------------------------------------

adequacyConvV-Y : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  Adq G gg (Pi A (wkExpr A)) -> Adq G A U -> AdqConv G gg (Pi A (wkExpr A)) ->
  (sigma sigma' : Sub h g) -> (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (Y gg) rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma (Y gg)) (substExpr sigma' (Y gg)) (substExpr sigma A) u a
adequacyConvV-Y {H = H} {A = A} {gg = gg} aU dg IHg IHA IHfc
  sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  adequacyEqV-Y-approx aU dg sigma rho crho vs fits wtsub wfH
    (substExpr sigma' gg) htF2 cvF1F2 cvY2 IHg IHA funcEq
    (fst hu) u (snd hu) a evA fm
  where
    cvAA'  = subst-ConvTm-cross aU wtsub wtsub' wcs wfH
    htsA   = subst-HasType wtsub wfH aU
    htF2   = ty-conv (subst-HasType wtsub' wfH (ty-Y aU dg)) (conv-sym cvAA') htsA
    cvF1F2 = subst-ConvTm-cross (ty-Y aU dg) wtsub wtsub' wcs wfH
    cvY2   = conv-conv (subst-ConvTm wtsub' wfH (conv-Y aU dg)) (conv-sym cvAA') htsA
    funcEq : (ub : FinEl) -> EvalRel gg rho ub -> (ap : FinEl) ->
      EvalRel (Pi A (wkExpr A)) rho ap -> FinMem ub ap ->
      EqVal2 H (substExpr sigma gg) (substExpr sigma' gg)
        (Pi (substExpr sigma A) (substExpr (liftSub sigma) (wkExpr A))) ub ap
    funcEq ub evFb ap evPab fmba =
      IHfc sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH ub evFb ap evPab fmba

------------------------------------------------------------------------
-- Driver 2: congruence  adequacyEqSub2 (conv-Y-cong …)
------------------------------------------------------------------------

adequacyEqV-Y-cong : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg gg' : Expr g} ->
  HasType G A U -> ConvTm G gg gg' (Pi A (wkExpr A)) ->
  Adq G A U -> AdqE1 G gg gg' (Pi A (wkExpr A)) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Y gg) rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma (Y gg)) (substExpr sigma (Y gg')) (substExpr sigma A) u a
adequacyEqV-Y-cong {H = H} {G = G} {A = A} {gg = gg} {gg' = gg'} aU dcvg IHA IHfe
  sigma rho crho vs fits wtsub wfH u hu a evA fm =
  adequacyEqV-Y-approx aU dg sigma rho crho vs fits wtsub wfH
    (substExpr sigma gg') htF2 cvF1F2 cvY2 IHg IHA funcEq
    (fst hu) u (snd hu) a evA fm
  where
    dg     = fst (typing-ConvTm dcvg)
    dg'    = snd (typing-ConvTm dcvg)
    htF2   = subst-HasType wtsub wfH (ty-Y aU dg')
    cvF1F2 = subst-ConvTm wtsub wfH (conv-Y-cong aU dcvg)
    cvY2   = subst-ConvTm wtsub wfH (conv-Y aU dg')
    IHg : Adq G gg (Pi A (wkExpr A))
    IHg s r cr v fi wt wf uu hh aa eA fmm =
      Val2-from-EqVal2-first uu aa (IHfe s r cr v fi wt wf uu hh aa eA fmm)
    funcEq : (ub : FinEl) -> EvalRel gg rho ub -> (ap : FinEl) ->
      EvalRel (Pi A (wkExpr A)) rho ap -> FinMem ub ap ->
      EqVal2 H (substExpr sigma gg) (substExpr sigma gg')
        (Pi (substExpr sigma A) (substExpr (liftSub sigma) (wkExpr A))) ub ap
    funcEq ub evFb ap evPab fmba =
      IHfe sigma rho crho vs fits wtsub wfH ub evFb ap evPab fmba

------------------------------------------------------------------------
-- Driver 3: unfolding  adequacyEqSub2 (conv-Y …)
------------------------------------------------------------------------

adequacyEqV-Y-unfold : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  Adq G gg (Pi A (wkExpr A)) -> Adq G A U ->
  (sigma : Sub h g) -> (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Y gg) rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma (Y gg)) (substExpr sigma (App gg (Y gg))) (substExpr sigma A) u a
adequacyEqV-Y-unfold {H = H} {A = A} {gg = gg} aU dg IHg IHA
  sigma rho crho vs fits wtsub wfH u hu a evA fm =
  let valY = adequacyV-Y-approx aU dg sigma rho crho vs fits wtsub wfH IHg IHA
               (fst hu) u (snd hu) a evA fm
      cvY  = subst-ConvTm wtsub wfH (conv-Y aU dg)
      hr   = headred-step headred-Y headred-refl
      valApp = Val2-headred-contract u a hr cvY valY
      htApp = subst-HasType wtsub wfH (snd (typing-ConvTm (conv-Y aU dg)))
  in EqVal2-headred-expand u a hr headred-refl cvY (conv-refl htApp)
       (Val2-to-EqVal2 u a valApp)
