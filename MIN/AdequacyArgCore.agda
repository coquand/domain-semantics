{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyArgCore.agda  (MIN/ -- PROTOTYPE)
--
-- Standalone, recursor-parameterised SINGLE-substitution combinator for
-- the conv-App-arg congruence rule, factored out of Adequacy.agda's
-- TERMINATING mutual block.
--
--   adequacyEqSub2-App-arg-core-body / adequacyEqSub2-App-arg
--     : the single-sub conversion  App f a = App f a' : subst1 B a
--       (the "Y" piece of the bundled conv-App-arg recipe).
--
-- The original recurses on adequacySub2 (df, dB) and adequacyEqSub2 (daa');
-- here those are recursor PARAMETERS, so the combinator is non-recursive:
-- no pragma, no postulate.
------------------------------------------------------------------------

module MIN.AdequacyArgCore where
open import MIN.AdequacyHeadRed

open import MIN.AdequacyApp using (app-transport-EqVal2)
open import MIN.AdequacyPi using (Val2-U-to-ValTy2 ; Adq)
open import MIN.AdequacyVE using (AdqE1)

import MIN.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons)
open import MIN.PaperSemantics using (LeCode ; LeCode-refl ; Coherent ; CoherentFun ; CoherentFunTail ;
  EvalFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ;
  finMemUCode-Sup ; finMem-upward ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; NotBot ; absurdEl ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import MIN.Reduction using (Red ; mkRed ; Red-refl ; HeadRed ; headred-step ; headred-beta ;
  headred-refl ; subst-subst1-comm)
open import MIN.RawSemantics using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ;
  EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import MIN.RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; Fin ; fzero ; fsuc ; wkExpr ;
  subst1 ; Sub ; liftSub ; substExpr ; subst1Sub)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ; ty-var ;
  ty-conv ; ty-U ; conv-refl ; conv-sym ; conv-conv)
open import MIN.Validity using (Selection ; Coherent-Selection ; Coherent-Selection-val ; FinMem-Coherent)
open import MIN.Validity using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import MIN.Selection using (FinMemAllU-Selection ; selectionBelow ; FinMem-Selection ;
  FinMem-Selection-codomain)
open import MIN.EvalSubstitution using (EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import MIN.TypingSemantics using (convSound' ; theorem1)
open import MIN.SubstitutionLemma using (typing-ConvTm ; WtSub ; subst-HasType ; subst-ConvTm ;
  liftSub-WtSub ; typing-WfCtx ; typing-type ; WtConvSub)
open import MIN.LemmaForTS using (Fits)

------------------------------------------------------------------------
-- Recursor types (single-sub HasType / single-sub ConvTm).
------------------------------------------------------------------------

AdSub2RecL : {h : Nat} -> Ctx h -> Set
AdSub2RecL {h} H =
  {g0 : Nat} {G0 : Ctx g0} {M0 A0 : Expr g0} -> HasType G0 M0 A0 ->
    (sigma0 : Sub h g0) -> (rho0 : EnvApprox g0) ->
    CoherentEnv rho0 -> ValidSub2 H G0 sigma0 rho0 -> Fits G0 rho0 ->
    WtSub H G0 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0

AdEqSub2Rec : {h : Nat} -> Ctx h -> Set
AdEqSub2Rec {h} H =
  {g0 : Nat} {G0 : Ctx g0} {M0 N0 A0 : Expr g0} -> ConvTm G0 M0 N0 A0 ->
    (sigma0 : Sub h g0) -> (rho0 : EnvApprox g0) ->
    CoherentEnv rho0 -> ValidSub2 H G0 sigma0 rho0 -> Fits G0 rho0 ->
    WtSub H G0 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    EqVal2 H (substExpr sigma0 M0) (substExpr sigma0 N0) (substExpr sigma0 A0) u a0

------------------------------------------------------------------------
-- adequacyEqSub2-App-arg-core-body : the "selected" (u1, v0, ...) case.
-- Faithful port of Adequacy.agda's adequacyEqSub2-App-arg-core with the
-- adequacySub2/adequacyEqSub2 recursions replaced by the params adSub2/adEqSub2.
------------------------------------------------------------------------

adequacyEqSub2-App-arg-core-body : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
  HasType (extend G A) B U ->
  HasType G f (Pi A B) ->
  ConvTm G a a' A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u1 : FinEl) ->
  (v0 : FinEl) -> EvalRel a rho v0 ->
  EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
  Adq G f (Pi A B) -> Adq (extend G A) B U -> AdqE1 G a a' A ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma f) (substExpr sigma a'))
           (substExpr sigma (subst1 B a))
           u1 ac1
adequacyEqSub2-App-arg-core-body {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
  dB df daa' sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  IHfv IHBv IHaae =
  S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf sa') T u1 ac1) (S.Eq-sym eq-sBA) transported
  where
    sf   = substExpr sigma f0
    sa   = substExpr sigma a
    sa'  = substExpr sigma a'
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sBA  = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    sing     = cons (mkSigma v0 u1) nil
    cv0      = EvalRel-coh a rho v0 evA_v0

    typed_f  = theorem1 df rho fits (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    val_fun  = IHfv sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

    val_sa : (u' : FinEl) -> EvalRel a rho u' ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val2 H sa sA u' a_arg
    val_sa u' evA_u' a_arg evA_aarg fm_u'_a =
      Val2-from-EqVal2-first u' a_arg
        (IHaae sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a)

    invTyp_a = fst (convSound' daa' rho fits)

    appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
      FinMem ub ap ->
      Val2 H sf (Pi sA sB) ub ap ->
      EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
    appEqVal-dispatch Bot          ap    () evFb evPab fmba valba
    appEqVal-dispatch UCode        ap    () evFb evPab fmba valba
    appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
    appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
    appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
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

          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          eqval_arg = IHaae sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

          vpi_fun  = un-ValPi valba
          A0_fun   = RValPi.domA0 vpi_fun
          B0_fun   = RValPi.codB0 vpi_fun
          red_fun  = RValPi.red vpi_fun
          uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_fun))
          eqA_fun  = fst uniq_fun
          eqB_fun  = snd uniq_fun
          pae_fun  = RValPi.appE vpi_fun

          eqval_arg' = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_fun eqval_arg
          ht_sa_A0   = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH (fst (typing-ConvTm daa')))
          ht_sa'_A0  = S.Eq-transport (\ X -> HasType H sa' X) eqA_fun (subst-HasType wtsub wfH (snd (typing-ConvTm daa')))
          cv_aa'_A0  = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_fun (subst-ConvTm wtsub wfH daa')

          eqval_app_raw : EqVal2 H (App sf sa) (App sf sa') (subst1 B0_fun sa) v_sel (EvalFun f_pi u_sel)
          eqval_app_raw = pae_fun u_sel v_sel sel_big sa sa' ht_sa_A0 ht_sa'_A0 cv_aa'_A0 eqval_arg'
          eqval_app : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_app = S.Eq-transport
            (\ X -> EqVal2 H (App sf sa) (App sf sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_fun) eqval_app_raw

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

          evU      = mkSigma tt (LeCode-refl UCode tt)
          fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
          v_fwd    = fst fwd_ac
          evA_vfwd = fst (snd fwd_ac)
          evB_vfwd = snd (snd fwd_ac)
          typed_a_fwd = invTyp_a v_fwd evA_vfwd
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
            in val_sa u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          dA_loc   = wfCtx-domain (typing-WfCtx dB)
          htA_loc  = subst-HasType wtsub wfH dA_loc
          htSa_loc = subst-HasType wtsub wfH (fst (typing-ConvTm daa'))
          wtsub_ext = extSub-WtSub wtsub wfH dA_loc htSa_loc
          wfH_ext  = wf-extend htA_loc
          vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                        (IHBv (extSub sigma sa) (extendEnv rho v_fwd')
                          crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
          eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

          fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
          v_fwd_ef = fst fwd_ef
          evA_vfef = fst (snd fwd_ef)
          evB_vfef = snd (snd fwd_ef)
          typed_a_ef = invTyp_a v_fwd_ef evA_vfef
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
            in val_sa u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                        (IHBv (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

      in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_app

    transported : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

------------------------------------------------------------------------
-- adequacyEqSub2-App-arg : the full dispatch over (u, ac).
------------------------------------------------------------------------

adequacyEqSub2-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
  HasType (extend G A) B U ->
  HasType G f (Pi A B) ->
  ConvTm G a a' A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  Adq G f (Pi A B) -> Adq (extend G A) B U -> AdqE1 G a a' A ->
  (u : FinEl) -> EvalRel (App f a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma f) (substExpr sigma a'))
           (substExpr sigma (subst1 B a))
           u ac
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae Bot ev ac evAc fm = EqVal2-Bot ac
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae UCode ev Bot evAc ()
adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae UCode ev UCode evAc fm =
  adequacyEqSub2-App-arg-core-body {H = H} dB df daa' sigma rho crho vs fits wtsub wfH UCode
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm IHfv IHBv IHaae
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae UCode ev (FunEl _) evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae UCode ev (PiCode _ _) evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (PiCode _ _) ev Bot evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (PiCode _ _) ev (FunEl _) evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (PiCode _ _) ev (PiCode _ _) evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (FunEl _) ev Bot evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (FunEl _) ev UCode evAc ()
adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (FunEl _) ev (FunEl _) evAc ()
adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (PiCode b0pc f0pc) ev UCode evAc fm =
  adequacyEqSub2-App-arg-core-body {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm IHfv IHBv IHaae
adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH IHfv IHBv IHaae (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
  adequacyEqSub2-App-arg-core-body {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (FunEl gfe)
    (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm IHfv IHBv IHaae
