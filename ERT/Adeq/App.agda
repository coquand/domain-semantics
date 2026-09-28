{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Adeq.App  (T_R version of MIN/Adequacy/App.agda + the App
-- core bodies of MIN/Adequacy/Cases.agda)
--
-- The application rule
--
--   Γ ⊢ A type   Γ.A ⊢ B type   Γ ⊢ c : Π(A,B)   Γ ⊢ a : A
--   ──────────────────────────────────────────────────────────
--   Γ ⊢ app(A,B,c,a) : B[a]
--
-- one substitution (Adq-App) and two substitutions (AdqConv-App).
-- Non-recursive: the IHs of the premises are parameters.
--
-- The value of the function is enlarged (soundness), a selection edge
-- below the argument value is chosen, the record clause of the function
-- (appV / appEV / appE) is applied there, and the result is transported
-- to the given pair of codes along their Sup.  The application's own
-- annotations (σA, σB) are the record's (Ann-refl); on the σ' side of the
-- two-substitution case they are convertible to them.
--
-- No postulates.
------------------------------------------------------------------------

module ERT.Adeq.App where

open import ERT.Adeq.HeadRed
open import ERT.Adeq.Stmt
open import ERT.Adeq.Pi using (app-transport-Val2 ; app-transport-EqVal2)

import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0 ; nil ; cons)
open import ERT.Dom.Kernel using (LeCode ; Coherent ; Comp ; EvalFun ;
  FinMem ; FinMem-a-in-U ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg)
open import ERT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ;
  CoherentEnv ; EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe-refl)
open import ERT.Model.EvalSubstitution using (EvalRel-subst1-forward ; EvalRel-Pi-app-type)
open import ERT.Model.SoundnessLemmas using (Fits)
open import ERT.Model.Selection using (Selection ; selectionBelow ; Coherent-Selection ;
  Coherent-Selection-val ; FinMem-Selection ; FinMem-Selection-codomain)
open import ERT.Model.Strip using (strip ; stripCtx ; strip-subst1)
import ERT.Model.Core as C
open import ERT.RussellSyntax using (Expr ; U ; Pi ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import ERT.RussellTyping
open import ERT.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; liftSub-WtSub ;
  subst-subst1)
open import ERT.RussellMetaCong using (subst-cong-IsType ; subst-cong-HasType ; liftSub-ConvTmSub)
open import ERT.RussellReduction using (headred-refl ; mkRed ; Red-unique-Pi)

------------------------------------------------------------------------
-- The record clauses of a function at the literal product it is typed
-- with: the record's (domA0, codB0) are the product's components.
------------------------------------------------------------------------

private
  fixV : {n : Nat} {H : Ctx n} {M A A0 : Expr n} {B B0 : Expr (suc n)} {b : FinEl} {f g : FinFun} ->
    Eq A A0 -> Eq B B0 -> PiAppVal2 H M A0 B0 b f g -> PiAppVal2 H M A B b f g
  fixV refl refl p = p

  fixE : {n : Nat} {H : Ctx n} {M A A0 : Expr n} {B B0 : Expr (suc n)} {b : FinEl} {f g : FinFun} ->
    Eq A A0 -> Eq B B0 -> PiAppEq2 H M A0 B0 b f g -> PiAppEq2 H M A B b f g
  fixE refl refl p = p

  fixEV : {n : Nat} {H : Ctx n} {M N A A0 : Expr n} {B B0 : Expr (suc n)} {b : FinEl} {f g : FinFun} ->
    Eq A A0 -> Eq B B0 -> PiAppEqVal2 H M N A0 B0 b f g -> PiAppEqVal2 H M N A B b f g
  fixEV refl refl p = p

  uniq : {n : Nat} {H : Ctx n} {A A0 : Expr n} {B B0 : Expr (suc n)} ->
    Red3 H (Pi A B) (Pi A0 B0) -> Pair (Eq A A0) (Eq B B0)
  uniq {H = H} r = Red-unique-Pi {G = H} (mkRed headred-refl) (mkRed (Red3.hr r))

  appV-at : {n : Nat} {H : Ctx n} {M A : Expr n} {B : Expr (suc n)} {g : FinFun} {b : FinEl} {f : FinFun} ->
    RValPi H M (Pi A B) g b f -> PiAppVal2 H M A B b f g
  appV-at {g = g} {b = b} {f = f} r = let e = uniq (RValPi.red r) in fixV {b = b} {f = f} {g = g} (fst e) (snd e) (RValPi.appV r)

  appE-at : {n : Nat} {H : Ctx n} {M A : Expr n} {B : Expr (suc n)} {g : FinFun} {b : FinEl} {f : FinFun} ->
    RValPi H M (Pi A B) g b f -> PiAppEq2 H M A B b f g
  appE-at {g = g} {b = b} {f = f} r = let e = uniq (RValPi.red r) in fixE {b = b} {f = f} {g = g} (fst e) (snd e) (RValPi.appE r)

  appEV-at : {n : Nat} {H : Ctx n} {M N A : Expr n} {B : Expr (suc n)} {g : FinFun} {b : FinEl} {f : FinFun} ->
    REqValPi H M N (Pi A B) g b f -> PiAppEqVal2 H M N A B b f g
  appEV-at {g = g} {b = b} {f = f} r = let e = uniq (REqValPi.red r) in fixEV {b = b} {f = f} {g = g} (fst e) (snd e) (REqValPi.appEV r)

  evSubst1 : {n : Nat} (B : Expr (suc n)) (a : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    EvalRel (strip (subst1 B a)) rho u -> EvalRel (C.subst1 (strip B) (strip a)) rho u
  evSubst1 B a rho u ev = S.Eq-transport (\ X -> EvalRel X rho u) (strip-subst1 B a) ev

------------------------------------------------------------------------
-- The codomain type B[σa] is valid at every value of B[a]: extend σ by
-- σa (whose validity comes from its IH, after enlarging its value by
-- soundness) and use the IH of B.
------------------------------------------------------------------------

codTy : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {a : Expr g} ->
  HasType G a A -> Adq G a A -> AdqTy (extend G A) B ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (w : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho w -> FinMem w U0 ->
  ValTy2 H (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) w
codTy {H = H} {A = A} {B = B} {a = a} da IHa IHB sigma rho crho vs fits wtsub wfH w evw wU =
  S.Eq-transport (\ T -> ValTy2 H T w) (S.Eq-sym (substExpr-comp sigma B sa)) raw
  where
    sa       = substExpr sigma a
    fwd      = EvalRel-subst1-forward (strip B) (strip a) rho w crho evw
    v_fwd    = fst fwd
    evA_vfwd = fst (snd fwd)
    evB_vfwd = snd (snd fwd)
    typed_a  = typedVal da rho fits v_fwd evA_vfwd
    v_fwd'   = fst typed_a
    a_fit    = fst (snd typed_a)
    le_vfwd  = fst (snd (snd typed_a))
    evA_vfwd' = fst (snd (snd (snd typed_a)))
    fm_vfwd' = fst (snd (snd (snd (snd typed_a))))
    evA_afit = snd (snd (snd (snd (snd typed_a))))
    cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
    cv_fwd   = EvalRel-coh (strip a) rho v_fwd evA_vfwd
    envle    = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
    evB'     = EvalRel-mon-env (strip B) (extendEnv rho v_fwd) (extendEnv rho v_fwd') w evB_vfwd envle
    fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
    crho_ext = mkSigma crho cv_fwd'
    hyp      = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      IHa sigma rho crho vs fits wtsub wfH u'
        (EvalRel-down (strip a) rho v_fwd' u' crho cu' evA_vfwd' le_u') a_arg evA_aarg fm_u'_a
    vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp
    wt_ext   = extSub-WtSub {A = A} wtsub (subst-HasType wtsub wfH da)
    raw      = IHB (extSub sigma sa) (extendEnv rho v_fwd') crho_ext vs_ext fits_ext wt_ext wfH w evB' wU

------------------------------------------------------------------------
-- One substitution: the informative core, at a value u1 of the
-- application given by a singleton graph of the function.
------------------------------------------------------------------------

private
  core-V : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c a : Expr g} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> HasType G a A ->
    Adq G c (Pi A B) -> Adq G a A -> AdqTy (extend G A) B ->
    (sigma : Sub h g) (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (u1 v0 : FinEl) -> EvalRel (strip a) rho v0 ->
    EvalRel (strip c) rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
    Val2 H (substExpr sigma (App A B c a))
           (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) u1 ac1
  core-V {H = H} {A = A} {B = B} {c = c} {a = a} dA dB dc da IHc IHa IHB
    sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun
    where
      sc  = substExpr sigma c
      sa  = substExpr sigma a
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      hsA = subst-IsType wtsub wfH dA
      hsB = subst-IsType (liftSub-WtSub wtsub wfH dA) (wf-extend hsA) dB
      sing = cons (mkSigma v0 u1) nil
      cv0  = EvalRel-coh (strip a) rho v0 evA_v0
      typed_f = typedVal dc rho fits (FunEl sing) evF_sing
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))
      val_fun = IHc sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip c) rho ub -> EvalRel (strip (Pi A B)) rho ap -> FinMem ub ap ->
        Val2 H sc (Pi sA sB) ub ap ->
        Val2 H (App sA sB sc sa) (subst1 sB sa) u1 ac1
      dispatch Bot           ap           () evFb evPab fmba valba
      dispatch (UCode _)     ap           () evFb evPab fmba valba
      dispatch (PiCode _ _)  ap           () evFb evPab fmba valba
      dispatch (FunEl g_big) Bot          lf evFb evPab () valba
      dispatch (FunEl g_big) (UCode _)    lf evFb evPab () valba
      dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () valba
      dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
        let le_u1_vsel = fst lf
            fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
            cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
            ctg      = cft-from-cf g_big cg_big
            piU      = finMem-funel-wf g_big b_pi f_pi fmba
            b_piU    = finMem-piU-dom b_pi f_pi piU
            allU_fpi = finMem-piU-allU b_pi f_pi piU
            cf_pi    = finMem-piU-cft b_pi f_pi piU
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 ctg cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big ctg
            evA_usel = EvalRel-down (strip a) rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big ctg cb_pi b_piU
            val_arg  = IHa sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi
            val_app  = appV-at (un-ValPi valba) u_sel v_sel sel_big (Ann-refl hsA hsB)
                         sa (subst-HasType wtsub wfH da) val_arg
            ef_usel  = EvalFun f_pi u_sel
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cf_pi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type (strip A) (strip B) (strip a) rho b_pi f_pi v0 crho evPab evA_v0
            c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
            evBa_ef  = EvalRel-down (C.subst1 (strip B) (strip a)) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (C.subst1 (strip B) (strip a)) rho crho ac1 ef_usel evAc1 evBa_ef
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big ctg cf_pi allU_fpi
            vt_ac    = codTy da IHa IHB sigma rho crho vs fits wtsub wfH ac1 evAc1 ac1_U
            vt_ef    = codTy da IHa IHB sigma rho crho vs fits wtsub wfH ef_usel evBa_ef ef_uselU
        in app-transport-Val2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app

------------------------------------------------------------------------
-- Two substitutions: the informative core.  Vary the function first
-- (appEV of the function's two-substitution record, which also changes
-- the annotations to the σ' ones), then the argument (appE of σ'c).
------------------------------------------------------------------------

private
  core-C : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c a : Expr g} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> HasType G a A ->
    Adq G a A -> AdqTy (extend G A) B -> AdqConv G c (Pi A B) -> AdqConv G a A ->
    (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
    Fits (stripCtx G) rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
    (u1 v0 : FinEl) -> EvalRel (strip a) rho v0 ->
    EvalRel (strip c) rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (substExpr sigma (App A B c a)) (substExpr sigma' (App A B c a))
           (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) u1 ac1
  core-C {H = H} {A = A} {B = B} {c = c} {a = a} dA dB dc da IHa IHB IHcc IHac
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f
    where
      sc   = substExpr sigma c
      sc'  = substExpr sigma' c
      sa   = substExpr sigma a
      sa'  = substExpr sigma' a
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      hsA  = subst-IsType wtsub wfH dA
      hsB  = subst-IsType (liftSub-WtSub wtsub wfH dA) (wf-extend hsA) dB
      cAA' : ConvTy H sA sA'
      cAA' = subst-cong-IsType wcs wfH dA
      cBB' : ConvTy (extend H sA) sB sB'
      cBB' = subst-cong-IsType (liftSub-ConvTmSub wcs wfH dA) (wf-extend hsA) dB
      ann' : Ann H sA sB sA' sB'
      ann' = mkAnn (conv-Ty-sym cAA') (conv-Ty-sym cBB')
      htSa   = subst-HasType wtsub wfH da
      htSa'  = ty-conv (subst-HasType wtsub' wfH da) (conv-Ty-sym cAA')
      cvSa   = subst-cong-HasType wcs wfH da
      sing = cons (mkSigma v0 u1) nil
      cv0  = EvalRel-coh (strip a) rho v0 evA_v0
      typed_f = typedVal dc rho fits (FunEl sing) evF_sing
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))
      eqval_f = IHcc sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u_big evF_big a_pi evPi fm_big

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip c) rho ub -> EvalRel (strip (Pi A B)) rho ap -> FinMem ub ap ->
        EqVal2 H sc sc' (Pi sA sB) ub ap ->
        EqVal2 H (App sA sB sc sa) (App sA' sB' sc' sa') (subst1 sB sa) u1 ac1
      dispatch Bot           ap           () evFb evPab fmba eqvba
      dispatch (UCode _)     ap           () evFb evPab fmba eqvba
      dispatch (PiCode _ _)  ap           () evFb evPab fmba eqvba
      dispatch (FunEl g_big) Bot          lf evFb evPab () eqvba
      dispatch (FunEl g_big) (UCode _)    lf evFb evPab () eqvba
      dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () eqvba
      dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
        let le_u1_vsel = fst lf
            fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
            cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
            ctg      = cft-from-cf g_big cg_big
            piU      = finMem-funel-wf g_big b_pi f_pi fmba
            b_piU    = finMem-piU-dom b_pi f_pi piU
            allU_fpi = finMem-piU-allU b_pi f_pi piU
            cf_pi    = finMem-piU-cft b_pi f_pi piU
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 ctg cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big ctg
            cv_sel   = Coherent-Selection-val sel_big ctg
            evA_usel = EvalRel-down (strip a) rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big ctg cb_pi b_piU
            c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
            -- the function varies (and the annotations with it)
            val_sa   = IHa sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi
            eq_fun   = appEV-at (un-REqValPi eqvba) u_sel v_sel sel_big (Ann-refl hsA hsB) ann'
                         sa htSa val_sa
            -- then the argument
            eq_arg0  = IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                         u_sel evA_usel b_pi evA_bpi fm_usel_bpi
            eq_arg   = appE-at (eqvalPi-snd eqvba) u_sel v_sel sel_big ann' ann'
                         sa sa' htSa htSa' cvSa eq_arg0
            eq_app   = EqVal2-trans v_sel (EvalFun f_pi u_sel) cv_sel c_efusel eq_fun eq_arg
            ef_usel  = EvalFun f_pi u_sel
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cf_pi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type (strip A) (strip B) (strip a) rho b_pi f_pi v0 crho evPab evA_v0
            evBa_ef  = EvalRel-down (C.subst1 (strip B) (strip a)) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (C.subst1 (strip B) (strip a)) rho crho ac1 ef_usel evAc1 evBa_ef
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big ctg cf_pi allU_fpi
            vt_ac    = codTy da IHa IHB sigma rho crho vs fits wtsub wfH ac1 evAc1 ac1_U
            vt_ef    = codTy da IHa IHB sigma rho crho vs fits wtsub wfH ef_usel evBa_ef ef_uselU
        in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eq_app

------------------------------------------------------------------------
-- The full statements: dispatch over the values (u, ac) of the
-- application and of its type.
------------------------------------------------------------------------

Adq-App : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c a : Expr g} ->
  IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> HasType G a A ->
  Adq G c (Pi A B) -> Adq G a A -> AdqTy (extend G A) B ->
  Adq G (App A B c a) (subst1 B a)
Adq-App {A = A} {B = B} {c = c} {a = a} dA dB dc da IHc IHa IHB {H = H} sigma rho crho vs fits wtsub wfH u hu ac evA fm =
  S.Eq-transport (\ T -> Val2 H (substExpr sigma (App A B c a)) T u ac)
    (S.Eq-sym (subst-subst1 sigma B a)) (go u hu ac (evSubst1 B a rho ac evA) fm)
  where
    T0 = subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)
    body : (u1 : FinEl) -> Sigma FinEl (\ v -> Pair (EvalRel (strip a) rho v)
             (EvalRel (strip c) rho (FunEl (cons (mkSigma v u1) nil)))) ->
           (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
           Val2 H (substExpr sigma (App A B c a)) T0 u1 ac1
    body u1 ev ac1 ev1 fm1 =
      core-V dA dB dc da IHc IHa IHB sigma rho crho vs fits wtsub wfH u1
        (fst ev) (fst (snd ev)) (snd (snd ev)) ac1 ev1 fm1
    go : (u : FinEl) -> EvalRel (strip (App A B c a)) rho u ->
         (ac : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac -> FinMem u ac ->
         Val2 H (substExpr sigma (App A B c a)) T0 u ac
    go Bot          hu ac          ev fm = Val2-Bot ac
    go (UCode _)    hu Bot         ev fm = tt
    go (UCode lu)   hu (UCode lk)  ev fm = body (UCode lu) hu (UCode lk) ev fm
    go (UCode _)    hu (FunEl _)   ev ()
    go (UCode _)    hu (PiCode _ _) ev ()
    go (PiCode _ _) hu Bot         ev ()
    go (PiCode b f) hu (UCode lk)  ev fm = body (PiCode b f) hu (UCode lk) ev fm
    go (PiCode _ _) hu (FunEl _)   ev ()
    go (PiCode _ _) hu (PiCode _ _) ev ()
    go (FunEl _)    hu Bot         ev ()
    go (FunEl _)    hu (UCode _)   ev ()
    go (FunEl _)    hu (FunEl _)   ev ()
    go (FunEl g)    hu (PiCode b f) ev fm = body (FunEl g) hu (PiCode b f) ev fm

AdqConv-App : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c a : Expr g} ->
  IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> HasType G a A ->
  Adq G a A -> AdqTy (extend G A) B ->
  AdqConv G c (Pi A B) -> AdqConv G a A ->
  AdqConv G (App A B c a) (subst1 B a)
AdqConv-App {A = A} {B = B} {c = c} {a = a} dA dB dc da IHa IHB IHcc IHac
    {H = H} sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu ac evA fm =
  S.Eq-transport (\ T -> EqVal2 H (substExpr sigma (App A B c a)) (substExpr sigma' (App A B c a)) T u ac)
    (S.Eq-sym (subst-subst1 sigma B a)) (go u hu ac (evSubst1 B a rho ac evA) fm)
  where
    T0 = subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)
    body : (u1 : FinEl) -> Sigma FinEl (\ v -> Pair (EvalRel (strip a) rho v)
             (EvalRel (strip c) rho (FunEl (cons (mkSigma v u1) nil)))) ->
           (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
           EqVal2 H (substExpr sigma (App A B c a)) (substExpr sigma' (App A B c a)) T0 u1 ac1
    body u1 ev ac1 ev1 fm1 =
      core-C dA dB dc da IHa IHB IHcc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
        u1 (fst ev) (fst (snd ev)) (snd (snd ev)) ac1 ev1 fm1
    go : (u : FinEl) -> EvalRel (strip (App A B c a)) rho u ->
         (ac : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac -> FinMem u ac ->
         EqVal2 H (substExpr sigma (App A B c a)) (substExpr sigma' (App A B c a)) T0 u ac
    go Bot          hu ac          ev fm = EqVal2-Bot ac
    go (UCode _)    hu Bot         ev fm = tt
    go (UCode lu)   hu (UCode lk)  ev fm = body (UCode lu) hu (UCode lk) ev fm
    go (UCode _)    hu (FunEl _)   ev ()
    go (UCode _)    hu (PiCode _ _) ev ()
    go (PiCode _ _) hu Bot         ev ()
    go (PiCode b f) hu (UCode lk)  ev fm = body (PiCode b f) hu (UCode lk) ev fm
    go (PiCode _ _) hu (FunEl _)   ev ()
    go (PiCode _ _) hu (PiCode _ _) ev ()
    go (FunEl _)    hu Bot         ev ()
    go (FunEl _)    hu (UCode _)   ev ()
    go (FunEl _)    hu (FunEl _)   ev ()
    go (FunEl g)    hu (PiCode b f) ev fm = body (FunEl g) hu (PiCode b f) ev fm
