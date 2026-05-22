{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyAppInj.agda  (MIN/ -- PROTOTYPE)
--
-- The "injection variant" of the ty-App cross machinery: instead of
-- calling the value-only recursors on the FUNCTION and ARGUMENT typings
-- (d3 / d4), it takes their per-substitution VALIDITY as CALLBACK
-- parameters.  This is the one genuinely-missing piece for pragma-free
-- adequacy (NEXT_SESSION_ADEQUACY_PRAGMAFREE.md): the conv-rules
-- (conv-beta / conv-App-fun / conv-App-arg) feed the function/argument a
-- validity sourced from a closure lemma or the bundled equality
-- extractor on a genuine SUBTERM, never the recursor on a constructed
-- node / typing presupposition.
--
-- The CODOMAIN B is always a genuine subterm (dB) in every rule, so its
-- recursor calls (adSub2 / adConvSub2 on d2) are KEPT as recursor
-- parameters -- they remain structural for the eventual driver.
--
-- The callbacks are at the body's fixed sigma (and sigma' for the
-- cross), so this file needs neither the bundled TySub machinery nor the
-- bundled validity types: the bundled->callback bridging (via the
-- combinator's TySub and AdqE2-to-AdqV2-left) happens in AdequacyBundle.
--
-- No TERMINATING, no postulates.
------------------------------------------------------------------------

module MIN.AdequacyAppInj where

open import MIN.AdequacyHeadRed

import MIN.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons)
open import MIN.PaperSemantics using (LeCode ; LeCode-refl ; Coherent ; CoherentFun ; CoherentFunTail ; EvalFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; NotBot ; absurdEl ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import MIN.Reduction using (Red ; mkRed ; Red-refl ; HeadRed ; headred-step ; headred-beta ; headred-refl ; subst-subst1-comm)
open import MIN.RawSemantics using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ; EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import MIN.RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; Fin ; fzero ; fsuc ; wkExpr ; subst1 ; Sub ; liftSub ; substExpr ; subst1Sub)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ; ty-var ; ty-conv ; ty-U ; conv-refl ; conv-sym ; conv-conv)
open import MIN.Validity using (Selection ; Coherent-Selection ; Coherent-Selection-val ; FinMem-Coherent)
open import MIN.Validity using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import MIN.Selection using (FinMemAllU-Selection ; selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain)
open import MIN.EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-body-EvalFun ; EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import MIN.TypingSemantics using (convSound' ; theorem1)
open import MIN.SubstitutionLemma using (typing-ConvTm ; WtSub ; subst-HasType ; subst-ConvTm ; liftSub-WtSub ; typing-WfCtx ; typing-type ; subst1-cong-ConvTm ; WtConvSub ; subst-ConvTm-cross)
open import MIN.LemmaForTS using (Fits)
open import MIN.AdequacyApp using (AdSub2Rec ; AdConvSub2Rec ; app-transport-EqVal2)
open import MIN.AdequacyPi using (Val2-U-to-ValTy2)

------------------------------------------------------------------------
-- adequacyConvSub2-App-core-body-inj
--
-- Verbatim port of AdequacyCases.adequacyConvSub2-App-core-body, with the
-- FUNCTION cross (adConvSub2 d3) and ARGUMENT single/cross (adSub2 d4 /
-- adConvSub2 d4) replaced by the callbacks  funcross / argsingle / argcross.
-- The CODOMAIN single (adSub2 d2) is KEPT as the adSub2 recursor parameter.
------------------------------------------------------------------------

adequacyConvSub2-App-core-body-inj : {h g : Nat} {H : Ctx h} {G : Ctx g}
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
  -- IH: adequacySub2 (KEPT recursor -- used only on the codomain d2)
  ({g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (sigma0 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 -> ValidSub2 H G1 sigma0 rho0 -> Fits G1 rho0 ->
    WtSub H G1 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0) ->
  -- funcross : function's cross at (sigma, sigma')
  ((ub ap : FinEl) -> EvalRel f rho ub -> EvalRel (Pi A B) rho ap -> FinMem ub ap ->
    EqVal2 H (substExpr sigma f) (substExpr sigma' f) (substExpr sigma (Pi A B)) ub ap) ->
  -- argsingle : argument's single at sigma
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    Val2 H (substExpr sigma a) (substExpr sigma A) u0 b0) ->
  -- argcross : argument's cross at (sigma, sigma')
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    EqVal2 H (substExpr sigma a) (substExpr sigma' a) (substExpr sigma A) u0 b0) ->
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
adequacyConvSub2-App-core-body-inj {H = H} {A = A} {B = B} {f = f0} {a = a}
  d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
  u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  adSub2 funcross argsingle argcross v2u2vt2 appTransE =
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

    -- EqVal2 for f at two subs (was: adConvSub2 d3 ...)
    eqval_f = funcross u_big a_pi evF_big evPi fm_big

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

          -- Argument evaluation data
          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU

          -- Common coherence
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel

          -- ===== FUNCTION VARIATION: App sf sa vs App sf' sa =====
          eqvpi_fun = un-REqValPi eqvba
          A0_eqfun  = REqValPi.domA0 eqvpi_fun
          B0_eqfun  = REqValPi.codB0 eqvpi_fun
          red_eqfun = REqValPi.red eqvpi_fun
          uniq_eqfun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_eqfun))
          eqA_eqfun = fst uniq_eqfun
          eqB_eqfun = snd uniq_eqfun
          paeqv_fun = REqValPi.appEV eqvpi_fun

          -- Val2 for sa at sA (was: adSub2 d4 ...)
          val_sa = argsingle u_sel b_pi evA_usel evA_bpi fm_usel_bpi
          val_sa_A0 = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_sa
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun (subst-HasType wtsub wfH d4)

          -- Apply PiAppEqVal2
          eqval_fun_var_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_sa_A0
          eqval_fun_var : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          eqval_fun_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_eqfun) eqval_fun_var_raw

          -- ===== ARGUMENT VARIATION: App sf' sa vs App sf' sa' =====
          vpi_sf'  = eqvalPi-snd eqvba
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

          -- EqVal2 for sa vs sa' (was: adConvSub2 d4 ...)
          eqval_arg = argcross u_sel b_pi evA_usel evA_bpi fm_usel_bpi
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
            in argsingle u' a_arg evA_u' evA_aarg fm_u'_a
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
            in argsingle u' a_arg evA_u' evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (adSub2 d2 (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

      in appTransE ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

    transported : EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f

------------------------------------------------------------------------
-- adequacyV-ty-App-inj : value-only cross EqVal2 of App f a : subst1 B a,
-- dispatching on the App value / type value and feeding the callbacks to
-- adequacyConvSub2-App-core-body-inj.  Port of AdequacyApp.adequacyV-ty-App.
------------------------------------------------------------------------

adequacyV-ty-App-inj : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType G f (Pi A B) -> HasType G a A ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  ((ub ap : FinEl) -> EvalRel f rho ub -> EvalRel (Pi A B) rho ap -> FinMem ub ap ->
    EqVal2 H (substExpr sigma f) (substExpr sigma' f) (substExpr sigma (Pi A B)) ub ap) ->
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    Val2 H (substExpr sigma a) (substExpr sigma A) u0 b0) ->
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    EqVal2 H (substExpr sigma a) (substExpr sigma' a) (substExpr sigma A) u0 b0) ->
  (u : FinEl) -> EvalRel (App f a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (App f a)) (substExpr sigma' (App f a)) (substExpr sigma (subst1 B a)) u ac
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross Bot hu a evA fm =
  EqVal2-Bot a
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross UCode hu Bot evA ()
adequacyV-ty-App-inj {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross UCode hu UCode evA fm =
  adequacyConvSub2-App-core-body-inj {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    UCode (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
    adSub2 funcross argsingle argcross Val2-U-to-ValTy2 app-transport-EqVal2
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross UCode hu (FunEl _) evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross UCode hu (PiCode _ _) evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (PiCode _ _) hu Bot evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (PiCode _ _) hu (FunEl _) evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (PiCode _ _) hu (PiCode _ _) evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (FunEl _) hu Bot evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (FunEl _) hu UCode evA ()
adequacyV-ty-App-inj dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (FunEl _) hu (FunEl _) evA ()
adequacyV-ty-App-inj {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (PiCode b0pc f0pc) hu UCode evA fm =
  adequacyConvSub2-App-core-body-inj {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
    adSub2 funcross argsingle argcross Val2-U-to-ValTy2 app-transport-EqVal2
adequacyV-ty-App-inj {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da adSub2 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH funcross argsingle argcross (FunEl gfe) hu (PiCode bacfe facfe) evA fm =
  adequacyConvSub2-App-core-body-inj {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    (FunEl gfe) (fst hu) (fst (snd hu)) (snd (snd hu)) (PiCode bacfe facfe) evA fm
    adSub2 funcross argsingle argcross Val2-U-to-ValTy2 app-transport-EqVal2

------------------------------------------------------------------------
-- adequacyV-subst1-cod-inj : the un-curried, callback variant of
-- AdequacyApp.adequacyV-subst1-cod (popl18 Lemma 3.20, equality part).
-- The ARGUMENT single/cross recursor calls (adSub2 da @sigma / @sigma',
-- adConvSub2 da) become the callbacks argsingleS / argsingleS' / argcross;
-- the CODOMAIN cross (adConvSub2 dB) is KEPT as the adConvSub2 recursor.
-- The result is the body of AdqConv un-curried at a specific (H, sigma, sigma').
------------------------------------------------------------------------

adequacyV-subst1-cod-inj : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G a A ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  -- argsingleS : argument single at sigma
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    Val2 H (substExpr sigma a) (substExpr sigma A) u0 b0) ->
  -- argsingleS' : argument single at sigma'
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    Val2 H (substExpr sigma' a) (substExpr sigma' A) u0 b0) ->
  -- argcross : argument cross at (sigma, sigma')
  ((u0 b0 : FinEl) -> EvalRel a rho u0 -> EvalRel A rho b0 -> FinMem u0 b0 ->
    EqVal2 H (substExpr sigma a) (substExpr sigma' a) (substExpr sigma A) u0 b0) ->
  -- adConvSub2 : KEPT recursor -- used only on the codomain dB
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
  (u : FinEl) -> EvalRel (subst1 B a) rho u ->
  (ac : FinEl) -> EvalRel U rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (subst1 B a)) (substExpr sigma' (subst1 B a)) U u ac
adequacyV-subst1-cod-inj {H = H} {G = G} {A = A} {B = B} {a = a} dA dB da
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    argsingleS argsingleS' argcross adConvSub2 u hu ac evU fm =
  r4
  where
    fwd      = EvalRel-subst1-forward B a rho u crho hu
    v_fwd    = fst fwd
    evA_vfwd = fst (snd fwd)
    evB_vfwd = snd (snd fwd)
    typed_a  = theorem1 da rho fits v_fwd evA_vfwd
    v_fwd'   = fst typed_a
    a_fit    = fst (snd typed_a)
    le_vfwd  = fst (snd (snd typed_a))
    evA_vfwd' = fst (snd (snd (snd typed_a)))
    fm_vfwd' = fst (snd (snd (snd (snd typed_a))))
    evA_afit = snd (snd (snd (snd (snd typed_a))))
    cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
    cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
    envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
    evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd') u evB_vfwd envle_fwd
    crho_ext = mkSigma crho cv_fwd'
    fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
    sa  = substExpr sigma a
    sa' = substExpr sigma' a
    sB  = substExpr (liftSub sigma) B
    sB' = substExpr (liftSub sigma') B
    hyp_s = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
      in argsingleS u' a_arg evA_u' evA_aarg fm_u'_a
    vs_ext = ValidSub2-extend sigma sa rho v_fwd' vs hyp_s
    hyp_s' = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
      in argsingleS' u' a_arg evA_u' evA_aarg fm_u'_a
    vs'_ext = ValidSub2-extend sigma' sa' rho v_fwd' vs' hyp_s'
    hyp_c = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
      in argcross u' a_arg evA_u' evA_aarg fm_u'_a
    vcs_ext = ValidConvSub2-extend sigma sigma' sa sa' rho v_fwd' vcs hyp_c
    htSa  = subst-HasType wtsub wfH da
    htSa' = subst-HasType wtsub' wfH da
    cvSa  = subst-ConvTm-cross da wtsub wtsub' wcs wfH
    wtsub_ext  = extSub-WtSub wtsub wfH dA htSa
    wtsub'_ext = extSub-WtSub wtsub' wfH dA htSa'
    wcs_ext    = extSub-WtConvSub wtsub wcs wfH dA cvSa
    raw = adConvSub2 dB (extSub sigma sa) (extSub sigma' sa') (extendEnv rho v_fwd')
            crho_ext vs_ext vs'_ext vcs_ext fits_ext wtsub_ext wtsub'_ext wcs_ext wfH
            u evB_vfwd' ac evU fm
    r1 = S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' sa') B) U u ac)
           (S.Eq-sym (substExpr-comp sigma B sa)) raw
    r2 = S.Eq-transport (\ T -> EqVal2 H (subst1 sB sa) T U u ac)
           (S.Eq-sym (substExpr-comp sigma' B sa')) r1
    r3 = S.Eq-transport (\ T -> EqVal2 H T (subst1 sB' sa') U u ac)
           (subst-subst1-comm sigma B a) r2
    r4 = S.Eq-transport (\ T -> EqVal2 H (substExpr sigma (subst1 B a)) T U u ac)
           (subst-subst1-comm sigma' B a) r3
