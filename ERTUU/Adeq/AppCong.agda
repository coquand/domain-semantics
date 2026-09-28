{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Adeq.AppCong  (T_R version of MIN/Adequacy/ArgCore.agda and
-- MIN/Adequacy/FunCore.agda + the App-fun core body of Cases.agda)
--
-- The congruence combinators for application:
--
--   AdqE1-App-arg : c a = c a'  with ARBITRARY annotations (A1,B1),
--                   (A2,B2) convertible to (A,B).  Covers T_R's
--                   conv-cong-App-arg (both annotations = (A,B)) and
--                   conv-cong-App-Ty (a = a').
--   AdqE1-App-fun : c a = c' a.
--
-- Both enlarge the function's value with the soundness theorem, select
-- the edge below the argument, apply the Π-record's application clause
-- (appE resp. appEV) and move the result along the Sup of the two codes
-- of the codomain type (app-transport-EqVal2).  Non-recursive: the IHs
-- are parameters.
--
-- No postulates.
------------------------------------------------------------------------

module ERTUU.Adeq.AppCong where

open import ERTUU.Adeq.HeadRed
open import ERTUU.Adeq.Stmt
open import ERTUU.Adeq.Pi using (app-transport-EqVal2)

import ERTUU.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0 ; cons ; nil)
open import ERTUU.Dom.Kernel using (LeCode ; Coherent ; EvalFun ; Comp ; CoherentFun ; FinMemFun ;
  FinMem ; FinMem-a-in-U ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon-arg ; EvalFun-in-UCode ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import ERTUU.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ;
  CoherentEnv ; EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe-refl)
open import ERTUU.Model.EvalSubstitution using (EvalRel-subst1-forward ; EvalRel-Pi-app-type)
open import ERTUU.Model.SoundnessLemmas using (Fits)
open import ERTUU.Model.Selection using (Selection ; selectionBelow ; Coherent-Selection ;
  FinMem-Selection ; FinMem-Selection-codomain)
open import ERTUU.Model.Strip using (strip ; stripCtx ; strip-subst1)
import ERTUU.Model.Core as C
open import ERTUU.RussellSyntax using (Expr ; U ; Pi ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import ERTUU.RussellTyping
open import ERTUU.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  subst-ConvTm ; liftSub-WtSub ; subst-subst1 ; presup-l-ConvTm ; presup-r-ConvTm)
open import ERTUU.RussellReduction using (headred-refl ; mkRed ; Red-unique-Pi)

------------------------------------------------------------------------
-- Annotations under substitution, and along equalities of the domain
------------------------------------------------------------------------

private
  ann-sub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A1 : Expr g} {B B1 : Expr (suc g)}
    {sigma : Sub h g} -> WtSub H G sigma -> WfCtx H -> IsType G A ->
    Ann G A B A1 B1 ->
    Ann H (substExpr sigma A) (substExpr (liftSub sigma) B)
          (substExpr sigma A1) (substExpr (liftSub sigma) B1)
  ann-sub wt wfH dA an =
    mkAnn (subst-ConvTy wt wfH (Ann.annA an))
          (subst-ConvTy (liftSub-WtSub wt wfH dA) (wf-extend (subst-IsType wt wfH dA)) (Ann.annB an))

  ann-eq : {n : Nat} {H : Ctx n} {X A0 A1 : Expr n} {Y B0 B1 : Expr (suc n)} ->
    Eq X A0 -> Eq Y B0 -> Ann H X Y A1 B1 -> Ann H A0 B0 A1 B1
  ann-eq S.refl S.refl an = an

  ev-subst1 : {n : Nat} (B : Expr (suc n)) (a : Expr n) {rho : EnvApprox n} {u : FinEl} ->
    EvalRel (strip (subst1 B a)) rho u -> EvalRel (C.subst1 (strip B) (strip a)) rho u
  ev-subst1 B a ev = S.Eq-transport (\ T -> EvalRel T _ _) (strip-subst1 B a) ev

------------------------------------------------------------------------
-- The codomain type B[a] is a valid type at every code of its value
-- (applies the codomain IH at the substitution extended by the argument).
------------------------------------------------------------------------

codVT : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {a : Expr g} ->
  HasType G a A -> AdqTy (extend G A) B ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  ((u' : FinEl) -> EvalRel (strip a) rho u' ->
   (a_arg : FinEl) -> EvalRel (strip A) rho a_arg -> FinMem u' a_arg ->
   Val2 H (substExpr sigma a) (substExpr sigma A) u' a_arg) ->
  (c : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho c -> FinMem c U0 ->
  ValTy2 H (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) c
codVT {H = H} {A = A} {B = B} {a = a} da IHB sigma rho crho vs fits wtsub wfH val_sa c evc cU =
  S.Eq-transport (\ T -> ValTy2 H T c) (S.Eq-sym (substExpr-comp sigma B sa)) vt_raw
  where
    sa       = substExpr sigma a
    fwd      = EvalRel-subst1-forward (strip B) (strip a) rho c crho evc
    v_fwd    = fst fwd
    evA_vfwd = fst (snd fwd)
    evB_vfwd = snd (snd fwd)
    typed    = typedVal da rho fits v_fwd evA_vfwd
    v_fwd'   = fst typed
    a_fit    = fst (snd typed)
    le_vfwd  = fst (snd (snd typed))
    evA_vfwd' = fst (snd (snd (snd typed)))
    fm_vfwd' = fst (snd (snd (snd (snd typed))))
    evA_afit = snd (snd (snd (snd (snd typed))))
    cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
    cv_fwd   = EvalRel-coh (strip a) rho v_fwd evA_vfwd
    envle    = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
    evB'     = EvalRel-mon-env (strip B) (extendEnv rho v_fwd) (extendEnv rho v_fwd') c evB_vfwd envle
    fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
    crho_ext = mkSigma crho cv_fwd'
    hyp      = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
                 val_sa u' (EvalRel-down (strip a) rho v_fwd' u' crho cu' evA_vfwd' le_u') a_arg evA_aarg fm_u'_a
    vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp
    wt_ext   = extSub-WtSub {A = A} wtsub (subst-HasType wtsub wfH da)
    vt_raw   = IHB (extSub sigma sa) (extendEnv rho v_fwd') crho_ext vs_ext fits_ext wt_ext wfH c evB' cU

------------------------------------------------------------------------
-- The shared tail: from the application's validity at the selected pair
-- (v_sel, EvalFun f_pi u_sel) to the one at (u1, ac1).
------------------------------------------------------------------------

private
  tailT : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {a : Expr g}
    {M1 M2 : Expr h} ->
    HasType G a A -> AdqTy (extend G A) B ->
    (sigma : Sub h g) (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    ((u' : FinEl) -> EvalRel (strip a) rho u' ->
     (a_arg : FinEl) -> EvalRel (strip A) rho a_arg -> FinMem u' a_arg ->
     Val2 H (substExpr sigma a) (substExpr sigma A) u' a_arg) ->
    (u1 v0 : FinEl) -> EvalRel (strip a) rho v0 ->
    (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
    (b_pi : FinEl) (f_pi : FinFun) -> EvalRel (strip (Pi A B)) rho (PiCode b_pi f_pi) ->
    FinMem (PiCode b_pi f_pi) U0 ->
    (g_big : FinFun) -> CoherentFun g_big -> FinMemFun g_big b_pi f_pi ->
    (u_sel v_sel : FinEl) -> Selection g_big u_sel v_sel -> LeCode u_sel v0 ->
    LeCode u1 v_sel ->
    EqVal2 H M1 M2 (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) v_sel (EvalFun f_pi u_sel) ->
    EqVal2 H M1 M2 (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) u1 ac1
  tailT {H = H} {A = A} {B = B} {a = a} da IHB sigma rho crho vs fits wtsub wfH val_sa
        u1 v0 evA_v0 ac1 evAc1 fm1 b_pi f_pi evPab piU g_big cg_big fmg_big u_sel v_sel sel_big le_usel le_u1_vsel eqval_app =
    app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1 fm_vsel_ef fm1 le_u1_vsel vt_ac vt_ef eqval_app
    where
      allU_fpi = finMem-piU-allU b_pi f_pi piU
      cf_pi    = finMem-piU-cft b_pi f_pi piU
      cv0      = EvalRel-coh (strip a) rho v0 evA_v0
      cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
      ef_usel  = EvalFun f_pi u_sel
      le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cf_pi cu_sel cv0
      evBa_efv = EvalRel-Pi-app-type (strip A) (strip B) (strip a) rho b_pi f_pi v0 crho evPab evA_v0
      c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
      evBa_ef  = EvalRel-down (C.subst1 (strip B) (strip a)) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
      comp_ac_ef = EvalRel-Comp (C.subst1 (strip B) (strip a)) rho crho ac1 ef_usel evAc1 evBa_ef
      ac1_U    = FinMem-a-in-U u1 ac1 fm1
      ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
      fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
      vt_ac    = codVT da IHB sigma rho crho vs fits wtsub wfH val_sa ac1 evAc1 ac1_U
      vt_ef    = codVT da IHB sigma rho crho vs fits wtsub wfH val_sa ef_usel evBa_ef ef_uselU

------------------------------------------------------------------------
-- App-fun : c a = c' a.  Uses the appEV clause of the function's
-- equality record.
------------------------------------------------------------------------

private
  funCore : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c c' a : Expr g} ->
    IsType G A -> IsType (extend G A) B -> ConvTm G c c' (Pi A B) -> HasType G a A ->
    AdqE1 G c c' (Pi A B) -> Adq G a A -> AdqTy (extend G A) B ->
    (sigma : Sub h g) (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (u1 v0 : FinEl) -> EvalRel (strip a) rho v0 ->
    EvalRel (strip c) rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma A) (substExpr (liftSub sigma) B) (substExpr sigma c) (substExpr sigma a))
             (App (substExpr sigma A) (substExpr (liftSub sigma) B) (substExpr sigma c') (substExpr sigma a))
             (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) u1 ac1
  funCore {H = H} {G = G} {A = A} {B = B} {c = c} {c' = c'} {a = a} dA dB dcc' da IHcc IHa IHB
      sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big (IHcc sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big)
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sc  = substExpr sigma c
      sc' = substExpr sigma c'
      sa  = substExpr sigma a
      dsA = subst-IsType wtsub wfH dA
      dsB = subst-IsType (liftSub-WtSub wtsub wfH dA) (wf-extend dsA) dB
      sing = cons (mkSigma v0 u1) nil
      cv0  = EvalRel-coh (strip a) rho v0 evA_v0
      typed_f = typedVal (presup-l-ConvTm dcc') rho fits (FunEl sing) evF_sing
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))
      val_sa  = IHa sigma rho crho vs fits wtsub wfH

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip c) rho ub -> EvalRel (strip (Pi A B)) rho ap -> FinMem ub ap ->
        EqVal2 H sc sc' (Pi sA sB) ub ap ->
        EqVal2 H (App sA sB sc sa) (App sA sB sc' sa) (subst1 sB sa) u1 ac1
      dispatch Bot           ap () evFb evPab fmba eqv
      dispatch (UCode _)     ap () evFb evPab fmba eqv
      dispatch (PiCode _ _)  ap () evFb evPab fmba eqv
      dispatch (FunEl g_big) Bot          lf evFb evPab () eqv
      dispatch (FunEl g_big) (UCode _)    lf evFb evPab () eqv
      dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () eqv
      dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqv =
        tailT da IHB sigma rho crho vs fits wtsub wfH val_sa u1 v0 evA_v0 ac1 evAc1 fm1
          b_pi f_pi evPab piU g_big cg_big fmg_big u_sel v_sel sel_big le_usel le_u1_vsel eqval_app
        where
          fmg_big = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big  = finMem-funel-coh g_big b_pi f_pi fmba
          piU     = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU   = finMem-piU-dom b_pi f_pi piU
          cb_pi   = coh-from-aU b_pi b_piU
          evA_bpi = fst (snd evPab)
          sb      = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel   = fst sb
          v_sel   = fst (snd sb)
          sel_big = fst (snd (snd sb))
          le_usel = fst (snd (snd (snd sb)))
          le_u1_vsel = S.Eq-transport (LeCode u1) (snd (snd (snd (snd sb)))) (fst lf)
          cu_sel  = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          evA_usel = EvalRel-down (strip a) rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg = val_sa u_sel evA_usel b_pi evA_bpi fm_usel
          core    = un-REqValPi eqv
          uniq    = Red-unique-Pi {G = H} (mkRed headred-refl) (mkRed (Red3.hr (REqValPi.red core)))
          eqA     = fst uniq
          eqB     = snd uniq
          an      = ann-eq eqA eqB (Ann-refl dsA dsB)
          val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA val_arg
          ht_sa   = S.Eq-transport (\ X -> HasType H sa X) eqA (subst-HasType wtsub wfH da)
          raw     = REqValPi.appEV core u_sel v_sel sel_big an an sa ht_sa val_arg'
          eqval_app = S.Eq-transport
            (\ X -> EqVal2 H (App sA sB sc sa) (App sA sB sc' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB) raw

AdqE1-App-fun : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c c' a : Expr g} ->
  IsType G A -> IsType (extend G A) B -> ConvTm G c c' (Pi A B) -> HasType G a A ->
  AdqE1 G c c' (Pi A B) -> Adq G a A -> AdqTy (extend G A) B ->
  AdqE1 G (App A B c a) (App A B c' a) (subst1 B a)
AdqE1-App-fun dA dB dcc' da IHcc IHa IHB sigma rho crho vs fits wt wfH Bot ev ac evAc fm = EqVal2-Bot ac
AdqE1-App-fun {B = B} {a = a} dA dB dcc' da IHcc IHa IHB {H = H} sigma rho crho vs fits wt wfH (UCode lu) ev ac evAc fm =
  EqVal2-transport-A {u = UCode lu} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (funCore dA dB dcc' da IHcc IHa IHB sigma rho crho vs fits wt wfH (UCode lu)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)
AdqE1-App-fun {B = B} {a = a} dA dB dcc' da IHcc IHa IHB {H = H} sigma rho crho vs fits wt wfH (FunEl g0) ev ac evAc fm =
  EqVal2-transport-A {u = FunEl g0} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (funCore dA dB dcc' da IHcc IHa IHB sigma rho crho vs fits wt wfH (FunEl g0)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)
AdqE1-App-fun {B = B} {a = a} dA dB dcc' da IHcc IHa IHB {H = H} sigma rho crho vs fits wt wfH (PiCode b0 f0) ev ac evAc fm =
  EqVal2-transport-A {u = PiCode b0 f0} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (funCore dA dB dcc' da IHcc IHa IHB sigma rho crho vs fits wt wfH (PiCode b0 f0)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)

------------------------------------------------------------------------
-- App-arg : c a = c a', with arbitrary annotations convertible to (A,B)
-- on each side.  Uses the appE clause of the function's record, which
-- takes the two annotation pairs independently.
------------------------------------------------------------------------

private
  argCore : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A1 A2 : Expr g} {B B1 B2 : Expr (suc g)} {c a a' : Expr g} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> ConvTm G a a' A ->
    Ann G A B A1 B1 -> Ann G A B A2 B2 ->
    Adq G c (Pi A B) -> AdqTy (extend G A) B -> AdqE1 G a a' A ->
    (sigma : Sub h g) (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (u1 v0 : FinEl) -> EvalRel (strip a) rho v0 ->
    EvalRel (strip c) rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (C.subst1 (strip B) (strip a)) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma A1) (substExpr (liftSub sigma) B1) (substExpr sigma c) (substExpr sigma a))
             (App (substExpr sigma A2) (substExpr (liftSub sigma) B2) (substExpr sigma c) (substExpr sigma a'))
             (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)) u1 ac1
  argCore {H = H} {G = G} {A = A} {A1 = A1} {A2 = A2} {B = B} {B1 = B1} {B2 = B2} {c = c} {a = a} {a' = a'}
      dA dB dc daa' an1 an2 IHc IHB IHaa
      sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big (IHc sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big)
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sA1 = substExpr sigma A1
      sB1 = substExpr (liftSub sigma) B1
      sA2 = substExpr sigma A2
      sB2 = substExpr (liftSub sigma) B2
      sc  = substExpr sigma c
      sa  = substExpr sigma a
      sa' = substExpr sigma a'
      da  = presup-l-ConvTm daa'
      da' = presup-r-ConvTm daa'
      sing = cons (mkSigma v0 u1) nil
      cv0  = EvalRel-coh (strip a) rho v0 evA_v0
      typed_f = typedVal dc rho fits (FunEl sing) evF_sing
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))
      eqv_sa  = IHaa sigma rho crho vs fits wtsub wfH
      val_sa  = \ u' ev' a_arg evA fm -> Val2-from-EqVal2-first u' a_arg (eqv_sa u' ev' a_arg evA fm)

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip c) rho ub -> EvalRel (strip (Pi A B)) rho ap -> FinMem ub ap ->
        Val2 H sc (Pi sA sB) ub ap ->
        EqVal2 H (App sA1 sB1 sc sa) (App sA2 sB2 sc sa') (subst1 sB sa) u1 ac1
      dispatch Bot           ap () evFb evPab fmba val
      dispatch (UCode _)     ap () evFb evPab fmba val
      dispatch (PiCode _ _)  ap () evFb evPab fmba val
      dispatch (FunEl g_big) Bot          lf evFb evPab () val
      dispatch (FunEl g_big) (UCode _)    lf evFb evPab () val
      dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () val
      dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba val =
        tailT da IHB sigma rho crho vs fits wtsub wfH val_sa u1 v0 evA_v0 ac1 evAc1 fm1
          b_pi f_pi evPab piU g_big cg_big fmg_big u_sel v_sel sel_big le_usel le_u1_vsel eqval_app
        where
          fmg_big = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big  = finMem-funel-coh g_big b_pi f_pi fmba
          piU     = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU   = finMem-piU-dom b_pi f_pi piU
          cb_pi   = coh-from-aU b_pi b_piU
          evA_bpi = fst (snd evPab)
          sb      = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel   = fst sb
          v_sel   = fst (snd sb)
          sel_big = fst (snd (snd sb))
          le_usel = fst (snd (snd (snd sb)))
          le_u1_vsel = S.Eq-transport (LeCode u1) (snd (snd (snd (snd sb)))) (fst lf)
          cu_sel  = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          evA_usel = EvalRel-down (strip a) rho v0 u_sel crho cu_sel evA_v0 le_usel
          fm_usel = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          eqv_arg = eqv_sa u_sel evA_usel b_pi evA_bpi fm_usel
          core    = un-ValPi val
          uniq    = Red-unique-Pi {G = H} (mkRed headred-refl) (mkRed (Red3.hr (RValPi.red core)))
          eqA     = fst uniq
          eqB     = snd uniq
          an1'    = ann-eq eqA eqB (ann-sub wtsub wfH dA an1)
          an2'    = ann-eq eqA eqB (ann-sub wtsub wfH dA an2)
          eqv_arg' = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA eqv_arg
          ht_sa   = S.Eq-transport (\ X -> HasType H sa X) eqA (subst-HasType wtsub wfH da)
          ht_sa'  = S.Eq-transport (\ X -> HasType H sa' X) eqA (subst-HasType wtsub wfH da')
          cv_aa'  = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA (subst-ConvTm wtsub wfH daa')
          raw     = RValPi.appE core u_sel v_sel sel_big an1' an2' sa sa' ht_sa ht_sa' cv_aa' eqv_arg'
          eqval_app = S.Eq-transport
            (\ X -> EqVal2 H (App sA1 sB1 sc sa) (App sA2 sB2 sc sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB) raw

AdqE1-App-arg : {g : Nat} {G : Ctx g} {A A1 A2 : Expr g} {B B1 B2 : Expr (suc g)} {c a a' : Expr g} ->
  IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> ConvTm G a a' A ->
  Ann G A B A1 B1 -> Ann G A B A2 B2 ->
  Adq G c (Pi A B) -> AdqTy (extend G A) B -> AdqE1 G a a' A ->
  AdqE1 G (App A1 B1 c a) (App A2 B2 c a') (subst1 B a)
AdqE1-App-arg dA dB dc daa' an1 an2 IHc IHB IHaa sigma rho crho vs fits wt wfH Bot ev ac evAc fm = EqVal2-Bot ac
AdqE1-App-arg {B = B} {a = a} dA dB dc daa' an1 an2 IHc IHB IHaa {H = H} sigma rho crho vs fits wt wfH (UCode lu) ev ac evAc fm =
  EqVal2-transport-A {u = UCode lu} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (argCore dA dB dc daa' an1 an2 IHc IHB IHaa sigma rho crho vs fits wt wfH (UCode lu)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)
AdqE1-App-arg {B = B} {a = a} dA dB dc daa' an1 an2 IHc IHB IHaa {H = H} sigma rho crho vs fits wt wfH (FunEl g0) ev ac evAc fm =
  EqVal2-transport-A {u = FunEl g0} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (argCore dA dB dc daa' an1 an2 IHc IHB IHaa sigma rho crho vs fits wt wfH (FunEl g0)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)
AdqE1-App-arg {B = B} {a = a} dA dB dc daa' an1 an2 IHc IHB IHaa {H = H} sigma rho crho vs fits wt wfH (PiCode b0 f0) ev ac evAc fm =
  EqVal2-transport-A {u = PiCode b0 f0} {a = ac} (S.Eq-sym (subst-subst1 sigma B a))
    (argCore dA dB dc daa' an1 an2 IHc IHB IHaa sigma rho crho vs fits wt wfH (PiCode b0 f0)
       (fst ev) (fst (snd ev)) (snd (snd ev)) ac (ev-subst1 B a evAc) fm)
