{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.Cases.agda
--
-- Helper for Hole 6: ty-MkPair cross-sub at (PairCode, SigmaCode).
-- Takes IH and sigEdgeEq as explicit arguments to avoid opacity.
------------------------------------------------------------------------

module ID.Adequacy.Cases where
open import ID.Adequacy.HeadRed public
open import ID.Adequacy.Pi using (Adq ; AdqConv)
open import ID.Adequacy.VE using (AdqE1)

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; CoherentFun ; CoherentFunTail ; EvalFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; NotBot ; absurdEl ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import ID.Syntax.Reduction using (Red ; mkRed ; Red-refl ; HeadRed ; headred-step ; headred-beta ; headred-refl ; subst-subst1-comm)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ; EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import ID.Syntax.Raw using (Expr ; Var ; U ; Pi ; Lam ; App ; Fin ; fzero ; fsuc ; wkExpr ; subst1 ; Sub ; liftSub ; substExpr ; subst1Sub)
  renaming ()
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ; ty-var ; ty-conv ; ty-U ; conv-refl ; conv-sym ; conv-conv)
open import ID.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val ; FinMem-Coherent)
open import ID.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import ID.Model.Selection using (FinMemAllU-Selection ; selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain)
open import ID.Model.EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-body-EvalFun ; EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import ID.Model.Soundness using (convSound' ; theorem1)
open import ID.Syntax.Substitution using (typing-ConvTm ; WtSub ; subst-HasType ; subst-ConvTm ; liftSub-WtSub ; typing-WfCtx ; typing-type ; subst1-cong-ConvTm ; WtConvSub ; subst-ConvTm-cross)
open import ID.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- Hole 6: ty-MkPair cross-sub at (PairCode u' v', SigmaCode b f)
------------------------------------------------------------------------

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
  -- IH VALUES: adequacySub2 (arg, codomain) + adequacyEqSub2 (function conversion)
  Adq G a A -> Adq (extend G A) B U -> AdqE1 G f f' (Pi A B) ->
  -- Val2-U-to-ValTy2
  ({n0 : Nat} {G0 : Ctx n0} {M0 : Expr n0} ->
    (b : FinEl) -> FinMem b UCode -> Val2 G0 M0 U b UCode -> ValTy2 G0 M0 b) ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma f') (substExpr sigma a))
           (substExpr sigma (subst1 B a))
           u1 ac1
adequacyEqSub2-App-fun-core-body {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
  dB dff' da sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
  IHa IHB IHffe v2u2vt2 =
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
    eqval_fun = IHffe sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

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

          -- Argument Val2
          evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = IHa sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

          -- Extract EqValPi2 from EqVal2 at (FunEl, PiCode)
          eqvpi_fun = un-REqValPi eqvba
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
            in IHa sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (IHB (extSub sigma sa) (extendEnv rho v_fwd')
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
            in IHa sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (IHB (extSub sigma sa) (extendEnv rho v_fwd_ef')
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
  -- IH VALUES: adequacySub2 on the function / argument / codomain subterms
  Adq G0 f' (Pi A B) -> Adq G0 a A -> Adq (extend G0 A) B U ->
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
  IHf IHa IHB v2u2vt2 appTransV =
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
    val_fun  = IHf sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

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
    appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
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
          val_arg  = IHa sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

          -- Extract PiAppVal2 from function's Val2
          vpi_fun  = un-ValPi valba
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
            in IHa sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          wtsub_ext = extSub-WtSub wtsub wfH dA (subst-HasType wtsub wfH d2)
          wfH_ext  = wf-extend (subst-HasType wtsub wfH dA)
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (IHB (extSub sigma sa) (extendEnv rho v_fwd')
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
            in IHa sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (IHB (extSub sigma sa) (extendEnv rho v_fwd_ef')
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
  -- IH VALUES: adequacySub2 (arg, codomain) + adequacyConvSub2 (function, arg)
  Adq G a A -> Adq (extend G A) B U -> AdqConv G f (Pi A B) -> AdqConv G a A ->
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
  IHav IHBv IHfc IHac v2u2vt2 appTransE =
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
    eqval_f = IHfc sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
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

          -- Val2 for sa at sA
          val_sa = IHav sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi
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

          -- EqVal2 for sa vs sa' via adConvSub2
          eqval_arg = IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
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
            in IHav sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
          vt_ac_raw = v2u2vt2 ac1 ac1_U
                        (IHBv (extSub sigma sa) (extendEnv rho v_fwd')
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
            in IHav sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
          vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
          vt_ef_raw = v2u2vt2 ef_usel ef_uselU
                        (IHBv (extSub sigma sa) (extendEnv rho v_fwd_ef')
                          crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
          vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

      in appTransE ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

    transported : EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
    transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f
