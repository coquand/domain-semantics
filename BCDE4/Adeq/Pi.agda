{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Pi  (T_R version of MIN/Adequacy/Pi.agda)
--
-- The Π-formation combinator, in type form: from the induction
-- hypotheses for the domain A and the codomain B (both as types),
-- the product Π(A,B) is a valid type.  Non-recursive: the IHs are
-- parameters, so the driver stays structural.
--
-- Also: transport of validity along the Sup of two codes of the same
-- type (transportVal2' / transportEqVal2'), used by every binder case.
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Pi (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; Comp ;
  Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ;
  FinMem ; FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ;
  coh-from-aU ; FinMem-coh-u ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft)
open import BCDE4.Model.Eval D using (EnvApprox ; extendEnv ; EvalRel ;
  CoherentEnv ; EvalRel-Comp ; EvalRel-mon-env ; EnvLe-refl)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; subst1 ; Sub ; liftSub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; liftSub-WtSub ; isType-Pi)
open import BCDE4.RussellReduction using (headred-refl)

open import BCDE4.Levels using (LCtx ; LSub ; lidS)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- Sup transport (uses only the public property lemmas)
------------------------------------------------------------------------

sup-transport-Val2 : {n : Nat} {H : Ctx n} {N A : Expr n}
  (b a_arg : FinEl) -> Comp b a_arg -> FinMem b U0 -> FinMem a_arg U0 ->
  (u0 u' : FinEl) -> FinMem u0 b -> Coherent u' -> LeCode u' u0 -> FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg -> Val2 H N A u0 b -> Val2 H N A u' a_arg
sup-transport-Val2 {H = H} {N = N} {A = A} b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN =
  let cb       = coh-from-aU b bU
      ca_arg   = coh-from-aU a_arg a_argU
      sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
      c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
      le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
      le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
      fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
      vtA_sup  = ValTy2-Sup H A b a_arg comp_b_a bU a_argU vtA_b vtA_a
      val1     = upVal2 H N A u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
      val2     = restrictVal2 H N A u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
  in downVal2 H N A u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2

sup-transport-EqVal2 : {n : Nat} {H : Ctx n} {N1 N2 A : Expr n}
  (b a_arg : FinEl) -> Comp b a_arg -> FinMem b U0 -> FinMem a_arg U0 ->
  (u0 u' : FinEl) -> FinMem u0 b -> Coherent u' -> LeCode u' u0 -> FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg -> EqVal2 H N1 N2 A u0 b -> EqVal2 H N1 N2 A u' a_arg
sup-transport-EqVal2 {H = H} {N1 = N1} {N2 = N2} {A = A} b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN =
  let cb       = coh-from-aU b bU
      ca_arg   = coh-from-aU a_arg a_argU
      sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
      c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
      le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
      le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
      fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
      vtA_sup  = ValTy2-Sup H A b a_arg comp_b_a bU a_argU vtA_b vtA_a
      eq1      = upEqVal2 H N1 N2 A u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup eqN vtA_sup
      eq2      = restrictEqVal2 H N1 N2 A u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup eq1
  in downEqVal2 H N1 N2 A u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU eq2

------------------------------------------------------------------------
-- Transport along Sup, parameterised by the domain IH
------------------------------------------------------------------------

transportVal2' : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  AdqTy G A ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) -> FinMem b U0 -> EvalRel (strip A) rho b ->
  (u0 : FinEl) -> FinMem u0 b ->
  (N : Expr h) -> Val2 H N (substExpr sigma A) u0 b ->
  (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
  (a_arg : FinEl) -> EvalRel (strip A) rho a_arg -> FinMem u' a_arg ->
  Val2 H N (substExpr sigma A) u' a_arg
transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
  let comp_b_a = EvalRel-Comp (strip A) rho crho b a_arg evAb evA_arg
      a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
      vtA_b    = IH-A sigma rho crho vs fits wtsub wfH b evAb bU
      vtA_a    = IH-A sigma rho crho vs fits wtsub wfH a_arg evA_arg a_argU
  in sup-transport-Val2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN

transportEqVal2' : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {N1 N2 : Expr h} ->
  AdqTy G A ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) -> FinMem b U0 -> EvalRel (strip A) rho b ->
  (u0 : FinEl) -> FinMem u0 b ->
  EqVal2 H N1 N2 (substExpr sigma A) u0 b ->
  (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
  (a_arg : FinEl) -> EvalRel (strip A) rho a_arg -> FinMem u' a_arg ->
  EqVal2 H N1 N2 (substExpr sigma A) u' a_arg
transportEqVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
  let comp_b_a = EvalRel-Comp (strip A) rho crho b a_arg evAb evA_arg
      a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
      vtA_b    = IH-A sigma rho crho vs fits wtsub wfH b evAb bU
      vtA_a    = IH-A sigma rho crho vs fits wtsub wfH a_arg evA_arg a_argU
  in sup-transport-EqVal2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN

------------------------------------------------------------------------
-- The Π combinator.  The codomain IHs are used inside the edge
-- realizers at the EXTENDED substitution `extSub sigma N`.
------------------------------------------------------------------------

adequacy-ty-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B ->
  AdqTy G A -> AdqTy (extend G A) B -> AdqConvTy (extend G A) B ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (strip (Pi A B)) rho (PiCode b f) ->
  FinMem (PiCode b f) U0 ->
  ValTy2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) (PiCode b f)
adequacy-ty-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH b f hu fm =
  mk-ValTyPi (record
    { domA = sA ; codB = sB
    ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
    ; cohF = cf ; fmAllU = allU ; htA = htA ; htB = htB ; valA = valTyA
    ; edgeV = buildEdgeVal ; edgeE = buildEdgeEq })
  where
    sA    = substExpr sigma A
    sB    = substExpr (liftSub sigma) B
    bU    = finMem-piU-dom b f fm
    allU  = finMem-piU-allU b f fm
    cf    = finMem-piU-cft b f fm
    cb    = coh-from-aU b bU
    evAb  = fst (snd hu)
    htA   = subst-IsType wtsub wfH d1
    htB   = subst-IsType (liftSub-WtSub wtsub wfH d1) (wf-extend htA) d2
    valTyA = IH-A sigma rho crho vs fits wtsub wfH b evAb bU

    buildEdgeVal : PiEdgeVal2 H sA sB b f
    buildEdgeVal u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          a'pi     = fst (snd (snd hu))
          bodyPi   = snd (snd (snd (snd hu)))
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env (strip B) (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend {A = A} sigma N rho u0 vs hyp0
          wtsub'   = extSub-WtSub {A = A} wtsub htN
          ih       = IH-B (extSub sigma N) (extendEnv rho u0) crho' vs' fits' wtsub' wfH v0 evB_u0_v0 fm_v0_U
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih

    buildEdgeEq : PiEdgeEq2 H sA sB b f
    buildEdgeEq u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          a'pi     = fst (snd (snd hu))
          bodyPi   = snd (snd (snd (snd hu)))
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env (strip B) (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend {A = A} sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub {A = A} wtsub htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend {A = A} sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub {A = A} wtsub htN2
          vcs_ext  = ValidConvSub2-extend {A = A} sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub {A = A} (WtConvSub-refl {G = G} wtsub) cvN
          raw      = IH-Bc (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB_u0_v0 fm_v0_U
      in S.Eq-transport (\ T -> EqValTy2 H (subst1 sB N1) T v0) (S.Eq-sym (substExpr-comp sigma B N2))
           (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma N2) B) v0)
              (S.Eq-sym (substExpr-comp sigma B N1)) raw)

------------------------------------------------------------------------
-- The full type statement for a product, and its universe form.
------------------------------------------------------------------------

AdqTy-Pi : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B ->
  AdqTy G A -> AdqTy (extend G A) B -> AdqConvTy (extend G A) B ->
  AdqTy G (Pi A B)
AdqTy-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH Bot          hu fm = tt
AdqTy-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (UCode _)    () fm
AdqTy-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (FunEl _)    () fm
AdqTy-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (PiCode b f) hu fm =
  adequacy-ty-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH b f hu fm

------------------------------------------------------------------------
-- Sup transport along the codomain of an application: from a validity at
-- the selected pair (v_sel, EvalFun f u_sel) to one at (u1, ac1), with
-- u1 <= v_sel and ac1 compatible with the edge value.
------------------------------------------------------------------------

app-transport-Val2 : {n : Nat} {H : Ctx n} {M A : Expr n}
  (ac1 ef_usel : FinEl) -> Comp ac1 ef_usel ->
  FinMem ac1 U0 -> FinMem ef_usel U0 ->
  (v_sel u1 : FinEl) -> FinMem v_sel ef_usel -> FinMem u1 ac1 -> LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  Val2 H M A v_sel ef_usel -> Val2 H M A u1 ac1
app-transport-Val2 {H = H} {M = M} {A = A} ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
  fm_vsel_ef fm_u1_ac le_u1_vsel vt_ac vt_ef val_app =
  let c_ac     = coh-from-aU ac1 ac1_U
      c_ef     = coh-from-aU ef_usel ef_uselU
      sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
      c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_ef
      fm_u1_sup = finMem-upward u1 ac1 (Sup ac1 ef_usel) le_ac_sup c_ac c_sup fm_u1_ac sup_U
      fm_vsel_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      vt_sup   = ValTy2-Sup H A ac1 ef_usel comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
      val_up   = upVal2 H M A v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup val_app vt_sup
      val_res  = restrictVal2 H M A v_sel u1 (Sup ac1 ef_usel) le_u1_vsel fm_u1_sup fm_vsel_sup val_up
  in downVal2 H M A u1 ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U val_res

app-transport-EqVal2 : {n : Nat} {H : Ctx n} {M1 M2 A : Expr n}
  (ac1 ef_usel : FinEl) -> Comp ac1 ef_usel ->
  FinMem ac1 U0 -> FinMem ef_usel U0 ->
  (v_sel u1 : FinEl) -> FinMem v_sel ef_usel -> FinMem u1 ac1 -> LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  EqVal2 H M1 M2 A v_sel ef_usel -> EqVal2 H M1 M2 A u1 ac1
app-transport-EqVal2 {H = H} {M1 = M1} {M2 = M2} {A = A} ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
  fm_vsel_ef fm_u1_ac le_u1_vsel vt_ac vt_ef eq_app =
  let c_ac     = coh-from-aU ac1 ac1_U
      c_ef     = coh-from-aU ef_usel ef_uselU
      sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
      c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_ef
      fm_u1_sup = finMem-upward u1 ac1 (Sup ac1 ef_usel) le_ac_sup c_ac c_sup fm_u1_ac sup_U
      fm_vsel_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      vt_sup   = ValTy2-Sup H A ac1 ef_usel comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
      eq_up    = upEqVal2 H M1 M2 A v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup eq_app vt_sup
      eq_res   = restrictEqVal2 H M1 M2 A v_sel u1 (Sup ac1 ef_usel) le_u1_vsel fm_u1_sup fm_vsel_sup eq_up
  in downEqVal2 H M1 M2 A u1 ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U eq_res
