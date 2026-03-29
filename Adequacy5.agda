{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Adequacy5.agda
--
-- Main adequacy mutual block for Pi + Sigma + U.
-- 0 postulates.
------------------------------------------------------------------------

module Adequacy5 where
open import Adequacy5HeadRed public
open import Adequacy5Cases using (tyMkPair-conv-case ;
  adequacyEqSub2-App-fun-core-body ; adequacySub2-App-core-body ;
  adequacyConvSub2-App-core-body)

import Validity5Lemmas as V5L

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ; codeFst ; codeSnd)
open import PaperSemanticsSigma using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; Comp ; Comp-down ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; EvalFun ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  LeFunCode ; LeFunCode-refl ;
  FinMem ; FinMemFun ; FinMemAllU ; FinMemAllProp ;
  FinMem-a-in-U ; finMemUCode-Sup ;
  finMem-upward ; finMem-Sup-left ; finMem-Sup-right ; coh-from-aU ;
  FinMem-coh-u ; cft-from-cf ; CoherentFunTail ; CoherentFunTail-append ;
  mkCFT ; NotBot ; FinMem-Prop-Bot ; FinMem-Prop-Bot-FunEl ;
  FinMem-Prop-to-U ; FinMem-U-to-PropCode ; absurdEl)
open import ReductionSigma using (Red ; mkRed ; Red-refl ; Red-hr ; HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma ;
  headred-step ; headred-beta ; headred-refl ; subst-subst1-comm ;
  headred-beta-fst ; headred-beta-snd ; headred-fst ; headred-snd ;
  idSub ; substExpr-id ; HeadRed1-det)
open import RawSemanticsSigma using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ; Pi-edgewise ; Sigma-edgewise ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr ; subst1Sub)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; empty ; extend ; lookup ;
  HasType ; ConvTm ; WfCtx ; wf-empty ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Sigma ; conv-beta-fst ; conv-beta-snd ; conv-pair-eta ;
  conv-MkPair-fst ; conv-MkPair-snd ; conv-Fst ; conv-Snd ;
  conv-Prop ; conv-Prop-U ; conv-Pi-Prop)
open import ValiditySigma using (Edge ; EdgeIn ; here ; there ;
  Red-unique-Pi ; Red-unique-Sigma ;
  FinMem-Coherent ;
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ;
  bU-from-cf-fmU)
open import ValiditySigma using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import SelectionSigma using (FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow)
open import TypingSemanticsSigma using (convSound ; convSound-inv ; convSound' ; theorem1 ;
  conv-Prop-chain ; LeCode-Bot-eq ; mkFstEv ; mkSndEv)
open import LemmaForTSSigma using (Fits ; Typed ; Fits-CoherentEnv)
open import EvalSubstitutionSigma using (EvalRel-subst1-backward ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-Pi-app-type ; EvalRel-Pi-body ; EvalRel-subst1-forward ;
  EvalRel-body-EvalFun)
open import RawSyntaxSigma using (Ren ; liftRen ; renExpr ; wkRen)
open import SubstitutionLemmaSigma using (typing-ConvTm ; WtSub ;
  subst-HasType ; subst-ConvTm ; liftSub-WtSub ; subst1-WtSub ;
  typing-WfCtx ; typing-type ; ctx-conv-HasType ; ctx-conv-ConvTm ;
  subst1-cong-ConvTm ; wk-HasType ; wk-ConvTm ;
  WtConvSub ; subst-ConvTm-cross ; liftSub-WtConvSub)

------------------------------------------------------------------------
-- sup-transport / app-transport helpers (used by mutual block)
-- Also defined in Adequacy5Helpers for Adequacy5Cases.
------------------------------------------------------------------------

sup-transport-Val2 : {n : Nat} {H : Ctx n} {N A : Expr n}
  (b a_arg : FinEl) ->
  Comp b a_arg ->
  FinMem b UCode -> FinMem a_arg UCode ->
  (u0 u' : FinEl) ->
  FinMem u0 b -> Coherent u' -> LeCode u' u0 ->
  FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg ->
  Val2 H N A u0 b ->
  Val2 H N A u' a_arg
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
      val1     = upVal2 H N A u0 b (Sup b a_arg)
                   le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      val2     = restrictVal2 H N A u0 u' (Sup b a_arg)
                   le_u'_u0 fm_u'_sup fm_u_sup val1
      val3     = downVal2 H N A u'
                   a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
  in val3

sup-transport-EqVal2 : {n : Nat} {H : Ctx n} {N1 N2 A : Expr n}
  (b a_arg : FinEl) ->
  Comp b a_arg ->
  FinMem b UCode -> FinMem a_arg UCode ->
  (u0 u' : FinEl) ->
  FinMem u0 b -> Coherent u' -> LeCode u' u0 ->
  FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg ->
  EqVal2 H N1 N2 A u0 b ->
  EqVal2 H N1 N2 A u' a_arg
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
      eq1      = upEqVal2 H N1 N2 A u0 b (Sup b a_arg)
                   le_b_sup fm_u0_b fm_u0_sup cb c_sup eqN vtA_sup
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      eq2      = restrictEqVal2 H N1 N2 A u0 u' (Sup b a_arg)
                   le_u'_u0 fm_u'_sup fm_u_sup eq1
      eq3      = downEqVal2 H N1 N2 A u' a_arg (Sup b a_arg)
                   le_a_sup fm_u'_a ca_arg sup_bU eq2
  in eq3

app-transport-Val2 : {n : Nat} {H : Ctx n} {M A : Expr n}
  (ac1 ef_usel : FinEl) ->
  Comp ac1 ef_usel ->
  FinMem ac1 UCode -> FinMem ef_usel UCode ->
  (v_sel u1 : FinEl) ->
  FinMem v_sel ef_usel -> FinMem u1 ac1 ->
  LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  Val2 H M A v_sel ef_usel ->
  Val2 H M A u1 ac1
app-transport-Val2 {H = H} {M = M} {A = A}
  ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
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
      val_up   = upVal2 H M A v_sel ef_usel (Sup ac1 ef_usel)
                   le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup val_app vt_sup
      val_res  = restrictVal2 H M A v_sel u1 (Sup ac1 ef_usel)
                   le_u1_vsel fm_u1_sup fm_vsel_sup val_up
      val_down = downVal2 H M A u1
                   ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U val_res
  in val_down

app-transport-EqVal2 : {n : Nat} {H : Ctx n} {M1 M2 A : Expr n}
  (ac1 ef_usel : FinEl) ->
  Comp ac1 ef_usel ->
  FinMem ac1 UCode -> FinMem ef_usel UCode ->
  (v_sel u1 : FinEl) ->
  FinMem v_sel ef_usel -> FinMem u1 ac1 ->
  LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  EqVal2 H M1 M2 A v_sel ef_usel ->
  EqVal2 H M1 M2 A u1 ac1
app-transport-EqVal2 {H = H} {M1 = M1} {M2 = M2} {A = A}
  ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
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
      eq_up    = upEqVal2 H M1 M2 A v_sel ef_usel (Sup ac1 ef_usel)
                   le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup eq_app vt_sup
      fm_v_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      eq_res   = restrictEqVal2 H M1 M2 A v_sel u1 (Sup ac1 ef_usel)
                   le_u1_vsel fm_u1_sup fm_v_sup eq_up
      eq_down  = downEqVal2 H M1 M2 A u1
                   ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U eq_res
  in eq_down

------------------------------------------------------------------------
-- Part 6: Main mutual block
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Main bundled adequacy theorem
  adequacySub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (substExpr sigma M) (substExpr sigma A) u a

  -- Bundled adequacy for conversion
  adequacyEqSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

  -- Two-substitution adequacy
  adequacyConvSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' ->
    WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a

  ----------------------------------------------------------------------
  -- adequacySub2-Prop-U-PiCode: stub for ty-Prop-U at PiCode
  -- TODO: needs full construction of ValTyPi2 from Prop typing
  adequacySub2-Prop-U-PiCode : {h g : Nat} {H : Ctx h} {G : Ctx g} {M : Expr g} ->
    HasType G M Prop ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (a' : FinEl) -> (f' : FinFun) ->
    EvalRel M rho (PiCode a' f') -> FinMem (PiCode a' f') UCode ->
    Val2 H (substExpr sigma M) (substExpr sigma U) (PiCode a' f') UCode
  adequacySub2-Prop-U-PiCode d sigma rho crho vs fits wtsub wfH a' f' hu fm =
    adequacySub2-Prop-U-PiCode-aux d S.refl sigma rho crho vs fits wtsub wfH a' f' hu fm

  -- Auxiliary: takes HasType G M A with proof A ≡ Prop, enabling case split
  adequacySub2-Prop-U-PiCode-aux : {h g : Nat} {H : Ctx h} {G : Ctx g} {M A : Expr g} ->
    HasType G M A -> S.Eq A Prop ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (a' : FinEl) -> (f' : FinFun) ->
    EvalRel M rho (PiCode a' f') -> FinMem (PiCode a' f') UCode ->
    Val2 H (substExpr sigma M) (substExpr sigma U) (PiCode a' f') UCode
  -- ty-Pi-Prop: M = Pi A B, direct via adequacySub2-Pi
  adequacySub2-Prop-U-PiCode-aux (ty-Pi-Prop d1 d2) S.refl sigma rho crho vs fits wtsub wfH a' f' hu fm =
    adequacySub2-Pi d1 (ty-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu (mkSigma tt (LeCode-refl UCode tt)) fm
  -- Remaining cases (ty-var, ty-conv, ty-App, ty-Fst, ty-Snd):
  -- These require ValTyPi2 H sM a' f' = Red H sM (Pi A B) U × HasType × semantic data.
  -- Val2 at (PiCode a' f', UCode) is ValTyPi2, independent of the type expression.
  -- But ValidSub2 only provides Val2 at PropCode, which is Top.
  -- Solution requires either strengthened ValidSub2 or canonical forms lemma.
  -- M : Prop and evaluates to PiCode a' f'. Typed data gives u' ≥ PiCode a' f'
  -- with FinMem u' a_t and a_t ≤ PropCode. For a_t = Bot: u' = Bot contradiction.
  -- For a_t = PropCode: FinMem (PiCode _) PropCode is non-empty → need proof irrelevance.
  adequacySub2-Prop-U-PiCode-aux d eq sigma rho crho vs fits wtsub wfH a' f' hu fm =
    let d' = S.Eq-transport (HasType _ _) eq d
    in adequacySub2-Prop-U-PiCode-aux2 d' sigma rho crho vs fits wtsub wfH a' f' fm
         (theorem1 d' rho fits (PiCode a' f') hu)
    where
      adequacySub2-Prop-U-PiCode-aux2 : {h' g' : Nat} {H' : Ctx h'} {G' : Ctx g'} {M' : Expr g'} ->
        HasType G' M' Prop ->
        (sigma' : Sub h' g') -> (rho' : EnvApprox g') ->
        CoherentEnv rho' -> ValidSub2 H' G' sigma' rho' -> Fits G' rho' ->
        WtSub H' G' sigma' -> WfCtx H' ->
        (a0 : FinEl) -> (f0 : FinFun) ->
        FinMem (PiCode a0 f0) UCode ->
        Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
          Pair (LeCode (PiCode a0 f0) u')
          (Pair (EvalRel M' rho' u')
          (Pair (FinMem u' a_t) (EvalRel Prop rho' a_t))))) ->
        Val2 H' (substExpr sigma' M') (substExpr sigma' U) (PiCode a0 f0) UCode
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma Bot (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma UCode (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 {H' = H'} {M' = M'} d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
          let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
              val_bg_prop = adequacySub2 d' sigma' rho' crho' vs' fits' wtsub' wfH'
                              (PiCode b g) hu' PropCode (mkSigma tt tt) fmBG
              vtU    = mkRed3 headred-refl (conv-refl (ty-U wfH'))
              val_bg = mkSigma vtU (snd val_bg_prop)
          in restrictVal2 H' (substExpr sigma' M') U (PiCode b g) (PiCode a0 f0) UCode
               le fm0 fmBG_U val_bg

  ----------------------------------------------------------------------
  -- adequacySub2: ty-var
  ----------------------------------------------------------------------

  adequacySub2 (ty-var {G = G} {i = i} _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    vs i u (fst hu) (snd hu) a evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-U
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-U _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    tyU2-helper u a (snd hu) (snd evA) fm
    where
      tyU2-helper : (u0 a0 : FinEl) -> LeCode u0 UCode -> LeCode a0 UCode ->
        FinMem u0 a0 -> Val2 H (substExpr sigma U) (substExpr sigma U) u0 a0
      tyU2-helper u0 Bot          _  _  _   = tt
      tyU2-helper Bot UCode        _  _  _   = tt
      tyU2-helper UCode UCode       _  _  _   = mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (mkRed3 headred-refl (conv-refl (ty-U wfH)))
      tyU2-helper PropCode UCode   () _  _
      tyU2-helper (FunEl _)    UCode () _  _
      tyU2-helper (PiCode _ _) UCode () _  _
      tyU2-helper (SigmaCode _ _) UCode () _  _
      tyU2-helper (PairCode _ _) UCode () _  _
      tyU2-helper u0 (FunEl _)    _  () _
      tyU2-helper u0 (PiCode _ _) _  () _
      tyU2-helper u0 (SigmaCode _ _) _ () _
      tyU2-helper u0 (PairCode _ _) _ () _
      tyU2-helper u0 PropCode      _  () _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Prop
  -- EvalRel Prop rho u means u ≤ PropCode.
  -- EvalRel U rho a means a ≤ UCode.
  -- FinMem u a with u ≤ PropCode and a ≤ UCode.
  -- Val2 H Prop U u a: since substExpr sigma Prop = Prop,
  -- this is the same structure as ty-U but with PropCode.
  -- PropCode ≤ UCode is Empty, so u can only be Bot.
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Prop _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacySub2-Prop u a (snd hu) (snd evA) fm
    where
      adequacySub2-Prop : (u a : FinEl) -> LeCode u PropCode -> LeCode a UCode ->
        FinMem u a -> Val2 H (substExpr sigma Prop) (substExpr sigma U) u a
      adequacySub2-Prop Bot a _ _ _ = Val2-Bot a
      adequacySub2-Prop UCode _ () _ _
      adequacySub2-Prop PropCode Bot _ _ ()
      adequacySub2-Prop PropCode UCode _ _ _ = mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (mkRed3 headred-refl (conv-refl (ty-Prop wfH)))
      adequacySub2-Prop PropCode PropCode _ () _
      adequacySub2-Prop PropCode (FunEl _) _ () _
      adequacySub2-Prop PropCode (PiCode _ _) _ () _
      adequacySub2-Prop PropCode (SigmaCode _ _) _ () _
      adequacySub2-Prop PropCode (PairCode _ _) _ () _
      adequacySub2-Prop (FunEl _) _ () _ _
      adequacySub2-Prop (PiCode _ _) _ () _ _
      adequacySub2-Prop (SigmaCode _ _) _ () _ _
      adequacySub2-Prop (PairCode _ _) _ () _ _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Prop-U
  -- If HasType G M Prop then HasType G M U.
  -- EvalRel M rho u, EvalRel U rho a (so a ≤ UCode).
  -- Need Val2 H sM U u a. Since M also has type Prop,
  -- EvalRel Prop rho a' gives a' ≤ PropCode. But we evaluate at U, not Prop.
  -- We just delegate to adequacySub2 on the underlying d.
  -- But d : HasType G M Prop, so type is Prop, not U.
  -- We need: Val2 H sM U u a from Val2 H sM Prop u a'.
  -- Actually: ty-Prop-U means M : Prop implies M : U.
  -- The type of M is U (the conclusion), so we evaluate at type U.
  -- But the premise is M : Prop.
  -- Since EvalRel Prop rho a' means a' ≤ PropCode,
  -- and Val2 at PropCode = Top, the IH gives tt.
  -- We need Val2 at (u, a) where a comes from U.
  -- This is the same as ty-U essentially - u ≤ UCode (from M : Prop, u ≤ PropCode ≤ ... no).
  -- Actually u comes from EvalRel M rho u, not from the type.
  -- For ty-Prop-U, the evaluation of M at rho gives u.
  -- The type is U, so a evaluates from U, meaning a ≤ UCode.
  -- We can use the IH at type Prop: adequacySub2 d sigma ... u hu PropCode evProp fm'
  -- where evProp : EvalRel Prop rho PropCode.
  -- But FinMem u PropCode may fail.
  -- Alternatively: ty-Prop-U behaves like ty-conv from Prop to U.
  -- Let's handle it as a conv case.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH Bot hu UCode evA fm =
    tt
  adequacySub2 {H = H} {M = M} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    absurd-UCode-at-Prop (theorem1 d rho fits UCode hu)
    where
      absurd-UCode-at-Prop :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
          Pair (LeCode UCode u') (Pair (EvalRel M rho u') (Pair (FinMem u' a') (EvalRel Prop rho a'))))) ->
        Val2 H (substExpr sigma M) (substExpr sigma U) UCode UCode
      absurd-UCode-at-Prop (mkSigma Bot (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma (PiCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma Bot (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma UCode (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma PropCode (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma (FunEl _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma (PiCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop (mkSigma UCode (mkSigma (PairCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
  adequacySub2 {H = H} {M = M} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    absurd-PropCode-at-Prop (theorem1 d rho fits PropCode hu)
    where
      absurd-PropCode-at-Prop :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
          Pair (LeCode PropCode u') (Pair (EvalRel M rho u') (Pair (FinMem u' a') (EvalRel Prop rho a'))))) ->
        Val2 H (substExpr sigma M) (substExpr sigma U) PropCode UCode
      absurd-PropCode-at-Prop (mkSigma Bot (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma UCode (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma (PiCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma Bot (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma UCode (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma PropCode (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma (FunEl _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma (PiCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop (mkSigma PropCode (mkSigma (PairCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA ()
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu UCode evA fm =
    adequacySub2-Prop-U-PiCode d sigma rho crho vs fits wtsub wfH a' f' hu fm
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (SigmaCode a' f') hu UCode evA fm =
    let typed = theorem1 d rho fits (SigmaCode a' f') hu
        u'   = fst typed
        a''  = fst (snd typed)
        le   = fst (snd (snd typed))
        fm'  = fst (snd (snd (snd (snd typed))))
        evP  = snd (snd (snd (snd (snd typed))))
    in SigmaCode-Prop-absurd a'' u' le fm' (snd evP)
    where
      SigmaCode-Prop-absurd : (a'' u' : FinEl) -> LeCode (SigmaCode a' f') u' ->
        FinMem u' a'' -> LeCode a'' PropCode -> _
      SigmaCode-Prop-absurd Bot u' le fm' _ =
        let eq = FinMem-Prop-Bot u' Bot fm' tt
        in absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode a' f') x) eq le)
      SigmaCode-Prop-absurd PropCode (SigmaCode _ _) le () _
      SigmaCode-Prop-absurd UCode _ _ _ ()
      SigmaCode-Prop-absurd (FunEl _) _ _ _ ()
      SigmaCode-Prop-absurd (PiCode _ _) _ _ _ ()
      SigmaCode-Prop-absurd (SigmaCode _ _) _ _ _ ()
      SigmaCode-Prop-absurd (PairCode _ _) _ _ _ ()
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA ()
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (FunEl _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma _ ()) fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-conv (extended with SigmaCode/PairCode/PropCode)
  ----------------------------------------------------------------------

  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in Val2-EqValTy2-fwd u UCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        pU    = FinMem-a-in-U (PiCode a' f') PropCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU pU
        eqvty = EqVal2-U-to-EqValTy2 PropCode pU eqAB
    in Val2-EqValTy2-fwd (PiCode a' f') PropCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in Val2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl g) hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a'' f'') hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode a'' f'') hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (SigmaCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA' fm
        aU    = FinMem-a-in-U (PairCode u' v') (SigmaCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (SigmaCode b' f') aU eqAB
    in Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b' f') (EvalRel-coh A rho (SigmaCode b' f') evA') eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl g) hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a'' f'') hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode a'' f'') hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  -- adequacySub2: ty-Pi (same as original)
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu UCode evA fm =
    adequacySub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (FunEl _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PiCode _ _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu PropCode (mkSigma _ ())
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (SigmaCode _ _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PairCode _ _) evA ()

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Pi-Prop
  -- Pi A B : Prop, so type is Prop. EvalRel Prop rho a means a ≤ PropCode.
  -- Val2 at PropCode = Top, so return tt.
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Pi-Prop {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    -- a ≤ PropCode. Val2 H (Pi sA sB) Prop u a.
    -- For a = Bot: tt. For a = PropCode: Val2 at PropCode = Top = tt.
    -- Other values of a are impossible (a ≤ PropCode).
    adequacySub2-at-Prop u a hu (snd evA) fm
    where
      adequacySub2-at-Prop : (u a : FinEl) -> EvalRel (Pi A B) rho u -> LeCode a PropCode -> FinMem u a -> Val2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) Prop u a
      adequacySub2-at-Prop u Bot _ _ fm = tt
      adequacySub2-at-Prop u UCode _ () _
      adequacySub2-at-Prop (PiCode a' f') PropCode hu' _ fm₁ =
        let piAtU = adequacySub2-Pi d1 (ty-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu'
                      (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode a' f') fm₁)
            vtProp = mkRed3 headred-refl (conv-refl (ty-Prop wfH))
        in mkSigma vtProp (snd piAtU)
      adequacySub2-at-Prop Bot PropCode _ _ fm = tt
      adequacySub2-at-Prop UCode PropCode _ _ ()
      adequacySub2-at-Prop PropCode PropCode _ _ ()
      adequacySub2-at-Prop (FunEl _) PropCode _ _ ()
      adequacySub2-at-Prop (SigmaCode _ _) PropCode _ _ ()
      adequacySub2-at-Prop (PairCode _ _) PropCode _ _ ()
      adequacySub2-at-Prop u (FunEl _) _ () _
      adequacySub2-at-Prop u (PiCode _ _) _ () _
      adequacySub2-at-Prop u (SigmaCode _ _) _ () _
      adequacySub2-at-Prop u (PairCode _ _) _ () _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Sigma
  -- Mirrors ty-Pi: SigmaCode b f at UCode
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode _ _) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu UCode evA fm =
    adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (FunEl _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PiCode _ _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu PropCode evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (SigmaCode _ _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PairCode _ _) evA ()

  ----------------------------------------------------------------------
  -- adequacySub2: ty-MkPair
  -- MkPair M N : Sigma A B. MkPair evaluates to PairCode u v or Bot.
  -- Val2 at (PairCode, SigmaCode) = Top, and Val2 at (Bot, _) = Top.
  -- So this case is always tt.
  ----------------------------------------------------------------------

  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH PropCode () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu Bot evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu UCode evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu PropCode evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (FunEl _) evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PiCode _ _) evA fm = tt
  adequacySub2 (ty-MkPair {A = A} {B = B} d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b0 f0) evA fm =
    adequacySub2-MkPair d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u' v' hu b0 f0 evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Fst
  -- Fst M : A. Val2 H (Fst sM) sA u a.
  -- u comes from EvalRel (Fst M) rho u.
  -- a comes from EvalRel A rho a.
  -- Since A : U, a is a type code.
  -- The key insight: for most (u,a) pairs, Val2 is Top.
  -- The non-trivial cases are same as ty-App.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PiCode a' f') (fst hu) (snd hu) PropCode evA fm
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b0 f0) evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PairCode u' v') (fst hu) (snd hu) (SigmaCode b0 f0) evA fm
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- ty-Fst at UCode: Val2 H (Fst sM) sA u UCode. Trivial for PropCode/PairCode.
  -- Hard cases (FunEl/PiCode/SigmaCode/UCode) need Red evidence for Fst M.
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH PropCode (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH UCode (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  adequacySub2 {H = H} (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PiCode a' f') (fst hu) (snd hu) UCode evA fm
  adequacySub2 {H = H} (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode a' f') hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode a' f') (fst hu) (snd hu) UCode evA fm
  -- Actually this is getting too complex. Let me use a simpler approach.
  -- For ty-Fst at (u, PiCode b f): Val2 = Pair ValTyPi2 ValPi2 or Top depending on u.
  -- This requires the full App-like machinery. Since this is an IN PROGRESS file,
  -- let me use the fact that for the specific cases we can delegate.
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode b f) evA fm = tt
  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl g) hu (PiCode b f) evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (FunEl g) (fst hu) (snd hu) (PiCode b f) evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Snd (mirrors ty-Fst)
  -- Snd M : subst1 B (Fst M). Similar structure.
  -- For most (u,a) combinations, Val2 = Top.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PiCode a' f') (fst hu) (snd hu) PropCode evA fm
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PairCode _ _) (fst hu) (snd hu) (SigmaCode _ _) evA fm
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- ty-Snd at UCode: Val2 H (Snd sM) (subst1 sB (Fst sM)) u UCode. Trivial for PropCode/PairCode.
  -- Hard cases (FunEl/PiCode/SigmaCode/UCode) need Red evidence for Snd M.
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH PropCode (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH UCode (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PiCode _ _) (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm =
    adequacySub2-Snd-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode _ _) (fst hu) (snd hu) UCode evA fm
  adequacySub2 (ty-Snd {A = A} dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PiCode b f) evA fm =
    let evA' = theorem1 (ty-Snd dA dB dM) rho fits u hu
    in adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH u hu b f evA fm evA'

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Lam (same as original, extended absurd cases)
  ----------------------------------------------------------------------

  adequacySub2 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH PropCode () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (PairCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu Bot evA fm = tt
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu UCode () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (FunEl h) () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu PropCode () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (SigmaCode _ _) () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (PairCode _ _) () fm
  adequacySub2 {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3)
    sigma rho crho vs fits wtsub wfH (FunEl g) hu (PiCode b f0) evA fm =
    adequacySub2-Lam d1 d2 d3 sigma rho crho vs fits wtsub wfH g hu b f0 evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-App (same as original, extended absurd cases)
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH Bot hu ac evAc fm =
    Val2-Bot ac
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH UCode ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode tt ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl g') (EvalRel-coh (App f' a) rho (FunEl g') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b0' f0') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0' f0') (EvalRel-coh (App f' a) rho (PiCode b0' f0') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b0' f0') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b0' f0') (EvalRel-coh (App f' a) rho (SigmaCode b0' f0') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH PropCode ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode (EvalRel-coh (App f' a) rho PropCode ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (PairCode u' v') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode u' v') (EvalRel-coh (App f' a) rho (PairCode u' v') ev) ev ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-refl
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-refl d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 d sigma rho crho vs fits wtsub wfH u hu a evA fm)

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-sym
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN  = convSound-inv d rho fits u hu
        cu'  = FinMem-Coherent u a fm
        ca   = EvalRel-coh Asrc rho a evA
        eq   = adequacyEqSub2 d sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-sym u a cu' ca eq

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-trans
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN  = convSound d1 rho fits u hu
        cu   = FinMem-Coherent u a fm
        ca   = EvalRel-coh A rho a evA
        eq1  = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu a evA fm
        eq2  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-trans u a cu ca eq1 eq2

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-conv (extended with SigmaCode/PairCode/PropCode)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u UCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in EqVal2-EqValTy2-fwd u UCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        fmPropU : FinMem PropCode UCode
        fmPropU = tt
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU fmPropU
        eqvty = EqVal2-U-to-EqValTy2 PropCode fmPropU eqAB
    in EqVal2-EqValTy2-fwd (PiCode a' f') PropCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv {A = A} d1 d2 _) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (SigmaCode b' f') evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U (PairCode u' v') (SigmaCode b' f') fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (SigmaCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd (PairCode u' v') (SigmaCode b' f') (EvalRel-coh A rho (SigmaCode b' f') evA') eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-beta {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
    adequacyEqSub2-beta d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u hu ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Prop
  -- Conv at type Prop. Val2 at PropCode = Top.
  -- a evaluates from Prop, so a ≤ PropCode.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Prop {M = M} {N = N} {A = A} dP dM dN) sigma rho crho vs fits wtsub wfH u0 hu a evA fm =
    adequacyEqSub2-at-Prop u0 a hu evA fm
    where
      -- A : Prop. If a = UCode, derive absurdity from theorem1 dP.
      ucode-absurd : (u0' : FinEl) -> EvalRel A rho UCode -> FinMem u0' UCode ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u0' UCode
      ucode-absurd u0' evA_U fm0 =
        let typed = theorem1 dP rho fits UCode evA_U
            u' = fst typed
            a_t = fst (snd typed)
            le_uc_u' = fst (snd (snd typed))
            fm_u'_at = fst (snd (snd (snd (snd typed))))
            evP = snd (snd (snd (snd (snd typed))))
        in ucode-split a_t u' le_uc_u' fm_u'_at (snd evP)
        where
          ucode-split : (a_t u' : FinEl) -> LeCode UCode u' ->
            FinMem u' a_t -> LeCode a_t PropCode -> _
          ucode-split Bot u' le fm_u' _ =
            let eq = FinMem-Prop-Bot u' Bot fm_u' tt
            in absurdEl (S.Eq-transport (\ x -> LeCode UCode x) eq le)
          ucode-split PropCode UCode le () _
          ucode-split UCode _ _ _ ()
          ucode-split (FunEl _) _ _ _ ()
          ucode-split (PiCode _ _) _ _ _ ()
          ucode-split (SigmaCode _ _) _ _ _ ()
          ucode-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-Prop : (u0' a' : FinEl) -> EvalRel M rho u0' -> EvalRel A rho a' -> FinMem u0' a' ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u0' a'
      adequacyEqSub2-at-Prop u0' Bot _ _ fm0 = tt
      adequacyEqSub2-at-Prop u0' UCode _ evA_U fm0 = ucode-absurd u0' evA_U fm0
      adequacyEqSub2-at-Prop (PiCode a0' f0') PropCode hu0 evA_P fm0 =
        let mkSigma u' (mkSigma a1 (mkSigma le_u (mkSigma hu' (mkSigma fm1 evA1)))) = theorem1 dM rho fits (PiCode a0' f0') hu0
            mkSigma a2 (mkSigma b (mkSigma le_a (mkSigma evA2 (mkSigma fm2 evProp)))) = theorem1 dP rho fits a1 evA1
            eq = LeCode-Bot-eq (PiCode a0' f0') u' le_u (conv-Prop-chain u' a1 a2 b fm1 le_a fm2 (snd evProp))
        in S.Eq-transport (\ x -> EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) x PropCode) (S.Eq-sym eq) tt
      adequacyEqSub2-at-Prop Bot PropCode _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode PropCode _ _ ()
      adequacyEqSub2-at-Prop PropCode PropCode _ _ ()
      adequacyEqSub2-at-Prop (FunEl _) PropCode _ _ ()
      adequacyEqSub2-at-Prop (SigmaCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop (PairCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop u0' (FunEl _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop Bot (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop PropCode (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (FunEl g0) (PiCode b0 f0) _ evA_pi fm0 =
        -- FunEl at PiCode at Prop is absurd: FinMem-Prop-Bot-FunEl
        let typed = theorem1 dP rho fits (PiCode b0 f0) evA_pi
            u'    = fst typed
            a_t   = fst (snd typed)
            le'   = fst (snd (snd typed))
            fm'   = fst (snd (snd (snd (snd typed))))
            evP   = snd (snd (snd (snd (snd typed))))
            piU   = snd (snd fm0)  -- FinMem (PiCode b0 f0) UCode
        in funel-pi-split a_t u' le' fm' (snd evP) piU
        where
          funel-pi-split : (a_t u' : FinEl) -> LeCode (PiCode b0 f0) u' ->
            FinMem u' a_t -> LeCode a_t PropCode ->
            FinMem (PiCode b0 f0) UCode -> _
          funel-pi-split Bot u' le' fm' _ piU =
            let eq = FinMem-Prop-Bot u' Bot fm' tt
            in absurdEl (S.Eq-transport (\ x -> LeCode (PiCode b0 f0) x) eq le')
          funel-pi-split PropCode u' le' fm' _ piU =
            let piP = FinMem-U-to-PropCode (PiCode b0 f0) u' piU le' fm'
                eq  = FinMem-Prop-Bot-FunEl g0 b0 f0 fm0 piP
            in absurdEl (S.Eq-transport NotBot eq tt)
          funel-pi-split UCode _ _ _ ()
          funel-pi-split (FunEl _) _ _ _ ()
          funel-pi-split (PiCode _ _) _ _ _ ()
          funel-pi-split (SigmaCode _ _) _ _ _ ()
          funel-pi-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-Prop (PiCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (SigmaCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PairCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop Bot (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop PropCode (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (FunEl _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PiCode _ _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (SigmaCode _ _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PairCode u0p v0p) (SigmaCode sb sf) hu0 evA_S fm0 =
        let mkSigma u' (mkSigma a1 (mkSigma le_u (mkSigma hu' (mkSigma fm1 evA1)))) = theorem1 dM rho fits (PairCode u0p v0p) hu0
            mkSigma a2 (mkSigma b' (mkSigma le_a (mkSigma evA2 (mkSigma fm2 evProp)))) = theorem1 dP rho fits a1 evA1
            eq = LeCode-Bot-eq (PairCode u0p v0p) u' le_u (conv-Prop-chain u' a1 a2 b' fm1 le_a fm2 (snd evProp))
        in S.Eq-transport (\ x -> EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) x (SigmaCode sb sf)) (S.Eq-sym eq) tt
      adequacyEqSub2-at-Prop u0' (PairCode _ _) _ _ fm0 = tt

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Prop-U
  -- ConvTm G M N Prop implies ConvTm G M N U.
  -- Type is U. Same structure as conv-conv from Prop to U.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-Prop-U d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      adequacyEqSub2-at-U-from-Prop : {h g : Nat} {H : Ctx h} {G : Ctx g} {M N : Expr g} ->
        ConvTm G M N Prop ->
        (sigma : Sub h g) -> (rho : EnvApprox g) ->
        CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
        WtSub H G sigma -> WfCtx H ->
        (u : FinEl) -> EvalRel M rho u ->
        (a : FinEl) -> EvalRel U rho a -> FinMem u a ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) U u a
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH Bot hu UCode evA fm = tt
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
        let htM_U = ty-Prop-U (fst (typing-ConvTm d))
            htN_U = ty-Prop-U (snd (typing-ConvTm d))
            evN   = convSound d rho fits PropCode hu
            valM  = adequacySub2 htM_U sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm
            valN  = adequacySub2 htN_U sigma rho crho vs fits wtsub wfH PropCode evN UCode evA fm
        in mkSigma (fst valM) (mkSigma (snd valM) (mkSigma (snd valN) (mkSigma (snd valM) (snd valN))))
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
      -- M : Prop → non-Bot u leads to absurdity via theorem1.
      -- UCode: u' ≥ UCode, FinMem UCode PropCode = Empty → absurd.
      -- FunEl: u' ≥ FunEl, FinMem (FunEl _) PropCode = Empty → absurd.
      -- SigmaCode: u' ≥ SigmaCode, FinMem (SigmaCode _) PropCode = Empty → absurd.
      -- PiCode: u' ≥ PiCode, FinMem (PiCode _) PropCode non-empty → hard case.
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits UCode hu
        in ucode-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          ucode-split : (a_t u' : FinEl) -> LeCode UCode u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          ucode-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode UCode x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          ucode-split PropCode UCode le () _
          ucode-split UCode _ _ _ ()
          ucode-split (FunEl _) _ _ _ ()
          ucode-split (PiCode _ _) _ _ _ ()
          ucode-split (SigmaCode _ _) _ _ _ ()
          ucode-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (FunEl g0) hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits (FunEl g0) hu
        in funel-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          funel-split : (a_t u' : FinEl) -> LeCode (FunEl g0) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          funel-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode (FunEl g0) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          funel-split PropCode (FunEl _) le () _
          funel-split UCode _ _ _ ()
          funel-split (FunEl _) _ _ _ ()
          funel-split (PiCode _ _) _ _ _ ()
          funel-split (SigmaCode _ _) _ _ _ ()
          funel-split (PairCode _ _) _ _ _ ()
      -- PiCode: u' ≥ PiCode, a_t = PropCode → FinMem (PiCode _) PropCode non-empty → hard
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (PiCode a0 f0) hu UCode evA fm =
        adequacyEqSub2-Prop-U-PiCode-aux' d sigma rho crho vs fits wtsub wfH a0 f0 fm
          (theorem1 (fst (typing-ConvTm d)) rho fits (PiCode a0 f0) hu)
        where
          adequacyEqSub2-Prop-U-PiCode-aux' :
            {h' g' : Nat} {H' : Ctx h'} {G' : Ctx g'} {M' N' : Expr g'} ->
            ConvTm G' M' N' Prop ->
            (sigma' : Sub h' g') -> (rho' : EnvApprox g') ->
            CoherentEnv rho' -> ValidSub2 H' G' sigma' rho' -> Fits G' rho' ->
            WtSub H' G' sigma' -> WfCtx H' ->
            (a0' : FinEl) -> (f0' : FinFun) ->
            FinMem (PiCode a0' f0') UCode ->
            Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
              Pair (LeCode (PiCode a0' f0') u')
              (Pair (EvalRel M' rho' u')
              (Pair (FinMem u' a_t) (EvalRel Prop rho' a_t))))) ->
            EqVal2 H' (substExpr sigma' M') (substExpr sigma' N') U (PiCode a0' f0') UCode
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma Bot (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma UCode (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma PropCode (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' {H' = H'} {M' = M'} {N' = N'} d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
              let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
                  eq_bg = adequacyEqSub2 (conv-Prop-U d') sigma' rho' crho' vs' fits' wtsub' wfH'
                            (PiCode b g) hu' UCode (mkSigma tt tt) fmBG_U
              in restrictEqVal2 H' (substExpr sigma' M') (substExpr sigma' N') U
                   (PiCode b g) (PiCode a0' f0') UCode le fm0 fmBG_U eq_bg
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (SigmaCode a0 f0) hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits (SigmaCode a0 f0) hu
        in sigma-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          sigma-split : (a_t u' : FinEl) -> LeCode (SigmaCode a0 f0) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          sigma-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode a0 f0) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          sigma-split PropCode (SigmaCode _ _) le () _
          sigma-split UCode _ _ _ ()
          sigma-split (FunEl _) _ _ _ ()
          sigma-split (PiCode _ _) _ _ _ ()
          sigma-split (SigmaCode _ _) _ _ _ ()
          sigma-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (FunEl _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) (mkSigma _ ()) fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Pi-Prop
  -- ConvTm at Prop type. Val2 at PropCode = Top.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Pi-Prop {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-at-Prop-gen u a hu (snd evA) fm
    where
      adequacyEqSub2-at-Prop-gen : (u a : FinEl) -> EvalRel (Pi A B) rho u -> LeCode a PropCode -> FinMem u a ->
        EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
                 (Pi (substExpr sigma A') (substExpr (liftSub sigma) B')) Prop u a
      adequacyEqSub2-at-Prop-gen u Bot _ _ fm = tt
      adequacyEqSub2-at-Prop-gen u UCode _ () _
      adequacyEqSub2-at-Prop-gen (PiCode a' f') PropCode hu' _ fm₁ =
          let eq_at_U = adequacyEqSub2-Pi d1 (conv-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu'
                          (mkSigma tt (LeCode-refl UCode tt)) (FinMem-Prop-to-U (PiCode a' f') fm₁)
          in mkSigma (mkRed3 headred-refl (conv-refl (ty-Prop wfH))) (snd eq_at_U)
      adequacyEqSub2-at-Prop-gen Bot PropCode _ _ fm = tt
      adequacyEqSub2-at-Prop-gen UCode PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen PropCode PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (FunEl _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (SigmaCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (PairCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen u (FunEl _) _ () _
      adequacyEqSub2-at-Prop-gen u (PiCode _ _) _ () _
      adequacyEqSub2-at-Prop-gen u (SigmaCode _ _) _ () _
      adequacyEqSub2-at-Prop-gen u (PairCode _ _) _ () _

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Pi (same as original, extended absurd)
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu Bot evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (FunEl _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PiCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu PropCode (mkSigma _ ()) fm
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (SigmaCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PairCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu UCode evA fm =
    adequacyEqSub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Sigma
  -- Mirrors conv-Pi. ConvTm G (Sigma A B) (Sigma A' B') U.
  -- Val2/EqVal2 at SigmaCode = Top for most u.
  -- At (SigmaCode b f, UCode): need ValTySigma2 etc.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Sigma {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (PiCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu Bot evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (FunEl _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PiCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu PropCode evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (SigmaCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PairCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu UCode evA fm =
    adequacyEqSub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta-fst
  -- Fst(MkPair M N) = M. Type A.
  -- Val2 approach: get Val2 for MkPair M N at Sigma type (= Top at PairCode,SigmaCode).
  -- Instead: adequacySub2 on M : A gives Val2, then headred-expand.
  ----------------------------------------------------------------------

  -- conv-beta-fst: Fst(MkPair M N) = M : A. Use convSound to get EvalRel M from EvalRel (Fst(MkPair M N)).
  adequacyEqSub2 {H = H} (conv-beta-fst {B = B} {M = M} {N = N} dA dB dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let evM = convSound (conv-beta-fst dA dB dM dN) rho fits u hu
        val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH u evM a evA fm
        eqval_diag = Val2-to-EqVal2 u a val_M
        htA' = subst-HasType wtsub wfH dA
        htB' = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA') dB
        htM' = subst-HasType wtsub wfH dM
        htN_raw = subst-HasType wtsub wfH dN
        htN' = S.Eq-transport (HasType H (substExpr sigma N)) (S.Eq-sym (subst-subst1-comm sigma B M)) htN_raw
    in EqVal2-headred-expand u a (headred-step headred-beta-fst headred-refl) headred-refl
         (conv-beta-fst htA' htB' htM' htN') (conv-refl htM') eqval_diag

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta-snd
  -- Snd(MkPair M N) = N. Type subst1 B M.
  ----------------------------------------------------------------------

  -- conv-beta-snd: Snd(MkPair M N) = N : B[M]. Use convSound to get EvalRel N from EvalRel (Snd(MkPair M N)).
  adequacyEqSub2 {H = H} (conv-beta-snd {B = B} {M = M} {N = N} dA dB dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let evN = convSound (conv-beta-snd dA dB dM dN) rho fits u hu
        val_N = adequacySub2 dN sigma rho crho vs fits wtsub wfH u evN a evA fm
        eqval_diag = Val2-to-EqVal2 u a val_N
        htA' = subst-HasType wtsub wfH dA
        htB' = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA') dB
        htM' = subst-HasType wtsub wfH dM
        htN_raw = subst-HasType wtsub wfH dN
        htN' = S.Eq-transport (HasType H (substExpr sigma N)) (S.Eq-sym (subst-subst1-comm sigma B M)) htN_raw
        cv_snd = S.Eq-transport (ConvTm H (Snd (MkPair (substExpr sigma M) (substExpr sigma N))) (substExpr sigma N)) (subst-subst1-comm sigma B M)
                   (conv-beta-snd htA' htB' htM' htN')
        cv_refl = S.Eq-transport (ConvTm H (substExpr sigma N) (substExpr sigma N)) (subst-subst1-comm sigma B M)
                   (conv-refl htN')
    in EqVal2-headred-expand u a (headred-step headred-beta-snd headred-refl) headred-refl
         cv_snd cv_refl eqval_diag

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-pair-eta
  -- MkPair(Fst M)(Snd M) = M : Sigma A B.
  -- Type is Sigma A B, so a = SigmaCode or Bot.
  -- Val2/EqVal2 at SigmaCode = Top. So return tt.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 {H = H} (conv-pair-eta {A = A} {B = B} {M = M0} dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm =
    mkSigma vtySigL (mkSigma rvalSigL (mkSigma rvalSigR reqvalSig))
    where
      sA = substExpr sigma A ; sB = substExpr (liftSub sigma) B ; sM0 = substExpr sigma M0
      evFstM = fst (snd hu) ; evSndM = snd (snd hu) ; evA_b = fst (snd evA)
      fm_u'_b = fst (fst fm) ; fm_v'_ef = snd (fst fm) ; cu' = fst (fst (fst (snd fm)))
      pSigU = snd (snd fm) ; bU_sig = fst pSigU ; allU_sig = fst (snd pSigU)
      cf_sig = snd (snd pSigU) ; cb_sig = coh-from-aU b bU_sig
      evU0 : EvalRel U rho UCode
      evU0 = mkSigma tt (LeCode-refl UCode tt)
      htA0 = subst-HasType wtsub wfH dA
      htB0 = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA0) dB
      htM_sig = subst-HasType wtsub wfH dM
      htSig0 = ty-Sigma htA0 htB0
      htFstM0 = ty-Fst htA0 htB0 htM_sig
      htSndM0 = S.Eq-transport (HasType _ (Snd sM0)) (S.Eq-sym (subst-subst1-comm sigma B (Fst M0)))
                  (subst-HasType wtsub wfH (ty-Snd dA dB dM))
      htMkPairEta = ty-MkPair htA0 htB0 htFstM0 htSndM0
      htFstEta = ty-Fst htA0 htB0 htMkPairEta
      sigEdgeEq0 = getSigmaEdgeEq dA dB sigma rho crho vs fits wtsub wfH b f evA pSigU
      -- Left Val2 (opaque)
      leftVal2 = adequacySub2 (ty-MkPair dA dB (ty-Fst dA dB dM) (ty-Snd dA dB dM))
                   sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm
      vtySigL = fst leftVal2 ; rvalSigL = snd leftVal2
      -- Core values
      val_Fst = adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u' evFstM b evA_b fm_u'_b
      sew0 = Sigma-edgewise A B rho b f evA
      evBFstM_ef = EvalRel-subst1-backward B (Fst M0) rho u' (EvalFun f u') crho evFstM
                     (EvalRel-body-EvalFun B rho u' (fst (snd (snd sew0))) f crho cu' (snd (fst sew0)) (snd (snd (snd (snd sew0)))))
      val_Snd = S.Eq-transport (\ T -> Val2 _ (Snd sM0) T v' (EvalFun f u'))
                  (S.Eq-sym (subst-subst1-comm sigma B (Fst M0)))
                  (adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH v' evSndM (EvalFun f u') evBFstM_ef fm_v'_ef)
      -- Selection
      sb0 = selectionBelow f u' cf_sig cu'
      u-f = fst sb0 ; v-f = fst (snd sb0) ; sel-f = fst (snd (snd sb0))
      le-uf = fst (snd (snd (snd sb0))) ; eq-ef = snd (snd (snd (snd sb0)))
      fmu-f = FinMemAllU-Selection b sel-f allU_sig cf_sig cb_sig bU_sig
      -- LHS betas
      hr-fst-eta = headred-step (headred-beta-fst {M = Fst sM0} {N = Snd sM0}) headred-refl
      cv-fst-eta = conv-beta-fst htA0 htB0 htFstM0 htSndM0
      hr-snd-eta = headred-step (headred-beta-snd {M = Fst sM0} {N = Snd sM0}) headred-refl
      cv-snd-eta = conv-beta-snd htA0 htB0 htFstM0 htSndM0
      -- Type transport for LHS snd
      eqFst_diag = Val2-to-EqVal2 u' b val_Fst
      eq_fst_eta = EqVal2-headred-expand u' b headred-refl hr-fst-eta (conv-refl htFstM0) cv-fst-eta eqFst_diag
      eqTy_ef = S.Eq-transport (EqValTy2 _ (subst1 sB (Fst sM0)) (subst1 sB (Fst (MkPair (Fst sM0) (Snd sM0)))))
                  (S.Eq-sym eq-ef) (sigEdgeEq0 u-f v-f sel-f (Fst sM0) (Fst (MkPair (Fst sM0) (Snd sM0)))
                    htFstM0 htFstEta (conv-sym cv-fst-eta) (restrictEqVal2 _ (Fst sM0) (Fst (MkPair (Fst sM0) (Snd sM0))) sA u' u-f b le-uf fmu-f fm_u'_b eq_fst_eta))
      valFstL = Val2-beta-expand u' b hr-fst-eta cv-fst-eta val_Fst
      valSndL = Val2-type-transport v' (EvalFun f u') eqTy_ef
                  (Val2-beta-expand v' (EvalFun f u') hr-snd-eta cv-snd-eta val_Snd)
      eqFst = EqVal2-headred-expand u' b hr-fst-eta headred-refl cv-fst-eta (conv-refl htFstM0) eqFst_diag
      -- Right RValSigma (M itself, no beta needed)
      rvalSigR : RValSigma _ sM0 (SigmaE sA sB) (PairCode u' v') b f
      rvalSigR = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFst = htFstM0 ; cohW1 = cu' ; fmW1 = fm_u'_b ; valFst = val_Fst ; valSnd = val_Snd }
      reqvalSig : REqValSigma _ (MkPair (Fst sM0) (Snd sM0)) sM0 (SigmaE sA sB) (PairCode u' v') b f
      reqvalSig = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFstM = htFstEta ; htFstN = htFstM0 ; cohW1 = cu' ; fmW1 = fm_u'_b
        ; valFstM = valFstL ; valSndM = valSndL ; valFstN = val_Fst ; valSndN = val_Snd ; eqFst = eqFst }

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-MkPair-fst, conv-MkPair-snd
  -- Congruence for MkPair. Type is Sigma A B.
  -- EqVal2 at SigmaCode = Top.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst {A = A} {B = B} {M = M0} {M' = M'0} {N = N0} dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm =
    mkSigma vtySigL (mkSigma rvalSigL (mkSigma rvalSigR reqvalSig))
    where
      sA = substExpr sigma A ; sB = substExpr (liftSub sigma) B
      sM = substExpr sigma M0 ; sM' = substExpr sigma M'0 ; sN = substExpr sigma N0
      evM = fst (snd hu) ; evN = snd (snd hu) ; evA_b = fst (snd evA)
      fm_u'_b = fst (fst fm) ; fm_v'_ef = snd (fst fm) ; cu' = fst (fst (fst (snd fm)))
      pSigU = snd (snd fm) ; bU_sig = fst pSigU ; allU_sig = fst (snd pSigU)
      cf_sig = snd (snd pSigU) ; cb_sig = coh-from-aU b bU_sig ; evU0 = mkSigma tt (LeCode-refl UCode tt)
      dM0 = fst (typing-ConvTm dMM') ; dM'0 = snd (typing-ConvTm dMM')
      htA0 = subst-HasType wtsub wfH dA
      htB0 = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA0) dB
      htM0s = subst-HasType wtsub wfH dM0 ; htM'0s = subst-HasType wtsub wfH dM'0
      htN_BM = S.Eq-transport (HasType _ sN) (S.Eq-sym (subst-subst1-comm sigma B M0)) (subst-HasType wtsub wfH dN)
      htSig0 = ty-Sigma htA0 htB0
      -- Right N typing: need HasType H sN (subst1 sB sM')
      cvBM = S.Eq-transport (\ T -> ConvTm _ (subst1 sB sM) T U) (S.Eq-sym (subst-subst1-comm sigma B M'0))
               (S.Eq-transport (\ T -> ConvTm _ T (substExpr sigma (subst1 B M'0)) U) (S.Eq-sym (subst-subst1-comm sigma B M0))
                 (subst-ConvTm wtsub wfH (subst1-cong-ConvTm dA dB dM0 dM'0 dMM')))
      htBM' = S.Eq-transport (\ T -> HasType _ T U) (S.Eq-sym (subst-subst1-comm sigma B M'0))
                (subst-HasType wtsub wfH (snd (typing-ConvTm (subst1-cong-ConvTm dA dB dM0 dM'0 dMM'))))
      htN_BM' = ty-conv htN_BM cvBM htBM'
      htMkPairL = ty-MkPair htA0 htB0 htM0s htN_BM
      htMkPairR = ty-MkPair htA0 htB0 htM'0s htN_BM'
      htFstL = ty-Fst htA0 htB0 htMkPairL ; htFstR = ty-Fst htA0 htB0 htMkPairR
      vtySig = snd (adequacySub2-Sigma dA dB sigma rho crho vs fits wtsub wfH b f evA evU0 pSigU)
      sigEdgeEq0 = getSigmaEdgeEq dA dB sigma rho crho vs fits wtsub wfH b f evA pSigU
      -- Left Val2 (opaque)
      leftVal2 = adequacySub2 (ty-MkPair dA dB dM0 dN) sigma rho crho vs fits wtsub wfH
                   (PairCode u' v') hu (SigmaCode b f) evA fm
      vtySigL = fst leftVal2 ; rvalSigL = snd leftVal2
      -- Fst values
      val_M = adequacySub2 dM0 sigma rho crho vs fits wtsub wfH u' evM b evA_b fm_u'_b
      eqMM'_val = adequacyEqSub2 dMM' sigma rho crho vs fits wtsub wfH u' evM b evA_b fm_u'_b
      val_M' = Val2-from-EqVal2-second u' b eqMM'_val
      hr-fst-L = headred-step (headred-beta-fst {M = sM} {N = sN}) headred-refl
      hr-fst-R = headred-step (headred-beta-fst {M = sM'} {N = sN}) headred-refl
      cv-fst-L = conv-beta-fst htA0 htB0 htM0s htN_BM
      cv-fst-R = conv-beta-fst htA0 htB0 htM'0s htN_BM'
      valFstL = Val2-beta-expand u' b hr-fst-L cv-fst-L val_M
      valFstR = Val2-beta-expand u' b hr-fst-R cv-fst-R val_M'
      eqFst = EqVal2-headred-expand u' b hr-fst-L hr-fst-R cv-fst-L cv-fst-R eqMM'_val
      -- Selection
      sb0 = selectionBelow f u' cf_sig cu'
      u-f = fst sb0 ; v-f = fst (snd sb0) ; sel-f = fst (snd (snd sb0))
      le-uf = fst (snd (snd (snd sb0))) ; eq-ef = snd (snd (snd (snd sb0)))
      fmu-f = FinMemAllU-Selection b sel-f allU_sig cf_sig cb_sig bU_sig
      -- Snd betas
      hr-snd-L = headred-step (headred-beta-snd {M = sM} {N = sN}) headred-refl
      hr-snd-R = headred-step (headred-beta-snd {M = sM'} {N = sN}) headred-refl
      cv-snd-L = conv-beta-snd htA0 htB0 htM0s htN_BM
      cv-snd-R = conv-beta-snd htA0 htB0 htM'0s htN_BM'
      -- Snd eval
      sew0 = Sigma-edgewise A B rho b f evA
      evB_u'_ef = EvalRel-body-EvalFun B rho u' (fst (snd (snd sew0))) f crho cu' (snd (fst sew0)) (snd (snd (snd (snd sew0))))
      evBM_ef = EvalRel-subst1-backward B M0 rho u' (EvalFun f u') crho evM evB_u'_ef
      val_N_BM = S.Eq-transport (\ T -> Val2 _ sN T v' (EvalFun f u'))
                   (S.Eq-sym (subst-subst1-comm sigma B M0))
                   (adequacySub2 dN sigma rho crho vs fits wtsub wfH v' evN (EvalFun f u') evBM_ef fm_v'_ef)
      -- Type transport helpers
      buildSndTypeEq0 : (X : Expr _) -> HasType _ X sA -> HasType _ (Fst (MkPair X sN)) sA ->
        HeadRed (Fst (MkPair X sN)) X -> ConvTm _ (Fst (MkPair X sN)) X sA -> Val2 _ X sA u' b ->
        EqValTy2 _ (subst1 sB X) (subst1 sB (Fst (MkPair X sN))) (EvalFun f u')
      buildSndTypeEq0 X htX htFstX hr cv valX =
        let eq0 = EqVal2-headred-expand u' b headred-refl hr (conv-refl htX) cv (Val2-to-EqVal2 u' b valX)
        in S.Eq-transport (EqValTy2 _ (subst1 sB X) (subst1 sB (Fst (MkPair X sN)))) (S.Eq-sym eq-ef)
             (sigEdgeEq0 u-f v-f sel-f X (Fst (MkPair X sN)) htX htFstX (conv-sym cv)
               (restrictEqVal2 _ X (Fst (MkPair X sN)) sA u' u-f b le-uf fmu-f fm_u'_b eq0))
      eqTyL = buildSndTypeEq0 sM htM0s htFstL hr-fst-L cv-fst-L val_M
      eqTyR = buildSndTypeEq0 sM' htM'0s htFstR hr-fst-R cv-fst-R val_M'
      -- M→M' type transport for snd
      eqMM'_uf = restrictEqVal2 _ sM sM' sA u' u-f b le-uf fmu-f fm_u'_b eqMM'_val
      eqTyMM' = S.Eq-transport (EqValTy2 _ (subst1 sB sM) (subst1 sB sM')) (S.Eq-sym eq-ef)
                  (sigEdgeEq0 u-f v-f sel-f sM sM' htM0s htM'0s
                    (subst-ConvTm wtsub wfH dMM') eqMM'_uf)
      val_N_BM' = Val2-type-transport v' (EvalFun f u') eqTyMM' val_N_BM
      -- valSnd
      valSndM = Val2-type-transport v' (EvalFun f u') eqTyL
                  (Val2-beta-expand v' (EvalFun f u') hr-snd-L cv-snd-L val_N_BM)
      valSndR = Val2-type-transport v' (EvalFun f u') eqTyR
                  (Val2-beta-expand v' (EvalFun f u') hr-snd-R cv-snd-R val_N_BM')
      rvalSigR : RValSigma _ (MkPair sM' sN) (SigmaE sA sB) (PairCode u' v') b f
      rvalSigR = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFst = htFstR ; cohW1 = cu' ; fmW1 = fm_u'_b ; valFst = valFstR ; valSnd = valSndR }
      reqvalSig : REqValSigma _ (MkPair sM sN) (MkPair sM' sN) (SigmaE sA sB) (PairCode u' v') b f
      reqvalSig = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFstM = htFstL ; htFstN = htFstR ; cohW1 = cu' ; fmW1 = fm_u'_b
        ; valFstM = valFstL ; valSndM = valSndM ; valFstN = valFstR ; valSndN = valSndR ; eqFst = eqFst }

  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd {A = A} {B = B} {M = M0} {N = N0} {N' = N'0} dA dB dM dNN') sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm =
    mkSigma vtySigL (mkSigma rvalSigL (mkSigma rvalSigR reqvalSig))
    where
      sA = substExpr sigma A ; sB = substExpr (liftSub sigma) B
      sM = substExpr sigma M0 ; sN = substExpr sigma N0 ; sN' = substExpr sigma N'0
      evM = fst (snd hu) ; evN = snd (snd hu) ; evA_b = fst (snd evA)
      fm_u'_b = fst (fst fm) ; fm_v'_ef = snd (fst fm)
      cu' = fst (fst (fst (snd fm)))
      pSigU = snd (snd fm) ; bU_sig = fst pSigU ; allU_sig = fst (snd pSigU)
      cf_sig = snd (snd pSigU) ; cb_sig = coh-from-aU b bU_sig
      dN0 = fst (typing-ConvTm dNN') ; dN'0 = snd (typing-ConvTm dNN')
      htA0 = subst-HasType wtsub wfH dA
      htB0 = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA0) dB
      htM0 = subst-HasType wtsub wfH dM
      htN0 = S.Eq-transport (HasType _ sN) (S.Eq-sym (subst-subst1-comm sigma B M0)) (subst-HasType wtsub wfH dN0)
      htN'0s = S.Eq-transport (HasType _ sN') (S.Eq-sym (subst-subst1-comm sigma B M0)) (subst-HasType wtsub wfH dN'0)
      htSig0 = ty-Sigma htA0 htB0
      htMkPairL = ty-MkPair htA0 htB0 htM0 htN0
      htMkPairR = ty-MkPair htA0 htB0 htM0 htN'0s
      htFstL = ty-Fst htA0 htB0 htMkPairL ; htFstR = ty-Fst htA0 htB0 htMkPairR
      -- Left Val2 (opaque)
      leftVal2 = adequacySub2 (ty-MkPair dA dB dM dN0) sigma rho crho vs fits wtsub wfH
                   (PairCode u' v') hu (SigmaCode b f) evA fm
      vtySigL = fst leftVal2 ; rvalSigL = snd leftVal2
      -- vtySig from adequacySub2-Sigma (known fields)
      evU0 = mkSigma tt (LeCode-refl UCode tt)
      vtySig = snd (adequacySub2-Sigma dA dB sigma rho crho vs fits wtsub wfH b f evA evU0 pSigU)
      sigEdgeEq0 = getSigmaEdgeEq dA dB sigma rho crho vs fits wtsub wfH b f evA pSigU
      -- Shared Fst value
      val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH u' evM b evA_b fm_u'_b
      -- EqVal2 for N = N'
      sew0 = Sigma-edgewise A B rho b f evA
      evB_u'_ef = EvalRel-body-EvalFun B rho u' (fst (snd (snd sew0))) f crho cu' (snd (fst sew0)) (snd (snd (snd (snd sew0))))
      evBM_ef = EvalRel-subst1-backward B M0 rho u' (EvalFun f u') crho evM evB_u'_ef
      eqNN' = S.Eq-transport (\ T -> EqVal2 _ sN sN' T v' (EvalFun f u'))
                (S.Eq-sym (subst-subst1-comm sigma B M0))
                (adequacyEqSub2 dNN' sigma rho crho vs fits wtsub wfH v' evN (EvalFun f u') evBM_ef fm_v'_ef)
      -- Selection data
      sb0 = selectionBelow f u' cf_sig cu'
      u-f = fst sb0 ; v-f = fst (snd sb0) ; sel-f = fst (snd (snd sb0))
      le-uf = fst (snd (snd (snd sb0))) ; eq-ef = snd (snd (snd (snd sb0)))
      fmu-f = FinMemAllU-Selection b sel-f allU_sig cf_sig cb_sig bU_sig
      -- Fst betas
      hr-fst-L = headred-step (headred-beta-fst {M = sM} {N = sN}) headred-refl
      hr-fst-R = headred-step (headred-beta-fst {M = sM} {N = sN'}) headred-refl
      cv-fst-L = conv-beta-fst htA0 htB0 htM0 htN0
      cv-fst-R = conv-beta-fst htA0 htB0 htM0 htN'0s
      -- Snd betas
      hr-snd-L = headred-step (headred-beta-snd {M = sM} {N = sN}) headred-refl
      hr-snd-R = headred-step (headred-beta-snd {M = sM} {N = sN'}) headred-refl
      cv-snd-L = conv-beta-snd htA0 htB0 htM0 htN0
      cv-snd-R = conv-beta-snd htA0 htB0 htM0 htN'0s
      -- valFst
      valFstL = Val2-beta-expand u' b hr-fst-L cv-fst-L val_M
      valFstR = Val2-beta-expand u' b hr-fst-R cv-fst-R val_M
      -- eqFst (diagonal)
      eqM_diag = Val2-to-EqVal2 u' b val_M
      eqFst = EqVal2-headred-expand u' b hr-fst-L hr-fst-R cv-fst-L cv-fst-R eqM_diag
      -- Type transport helper
      buildSndTypeEq0 : (X : Expr _) -> HasType _ (Fst (MkPair sM X)) sA ->
        HeadRed (Fst (MkPair sM X)) sM -> ConvTm _ (Fst (MkPair sM X)) sM sA ->
        EqValTy2 _ (subst1 sB sM) (subst1 sB (Fst (MkPair sM X))) (EvalFun f u')
      buildSndTypeEq0 X htFstX hr cv =
        let eq0 = EqVal2-headred-expand u' b headred-refl hr (conv-refl htM0) cv eqM_diag
        in S.Eq-transport (EqValTy2 _ (subst1 sB sM) (subst1 sB (Fst (MkPair sM X))))
             (S.Eq-sym eq-ef) (sigEdgeEq0 u-f v-f sel-f sM (Fst (MkPair sM X)) htM0 htFstX (conv-sym cv)
               (restrictEqVal2 _ sM (Fst (MkPair sM X)) sA u' u-f b le-uf fmu-f fm_u'_b eq0))
      eqTyL = buildSndTypeEq0 sN htFstL hr-fst-L cv-fst-L
      eqTyR = buildSndTypeEq0 sN' htFstR hr-fst-R cv-fst-R
      -- valSndM, valSndN
      valSndM = Val2-type-transport v' (EvalFun f u') eqTyL
                  (Val2-beta-expand v' (EvalFun f u') hr-snd-L cv-snd-L (Val2-from-EqVal2-first v' (EvalFun f u') eqNN'))
      valSndR = Val2-type-transport v' (EvalFun f u') eqTyR
                  (Val2-beta-expand v' (EvalFun f u') hr-snd-R cv-snd-R (Val2-from-EqVal2-second v' (EvalFun f u') eqNN'))
      -- Right RValSigma
      rvalSigR : RValSigma _ (MkPair sM sN') (SigmaE sA sB) (PairCode u' v') b f
      rvalSigR = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFst = htFstR ; cohW1 = cu' ; fmW1 = fm_u'_b ; valFst = valFstR ; valSnd = valSndR }
      -- REqValSigma
      reqvalSig : REqValSigma _ (MkPair sM sN) (MkPair sM sN') (SigmaE sA sB) (PairCode u' v') b f
      reqvalSig = record { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig0)
        ; htFstM = htFstL ; htFstN = htFstR ; cohW1 = cu' ; fmW1 = fm_u'_b
        ; valFstM = valFstL ; valSndM = valSndM ; valFstN = valFstR ; valSndN = valSndR ; eqFst = eqFst }

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Fst
  -- Fst M = Fst M' : A. Standard congruence.
  ----------------------------------------------------------------------

  -- conv-Fst: Fst M = Fst M' : A. Type is A : U. Most (u,a) trivial.
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    adequacyEqSub2-Fst-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PiCode a' f') (fst hu) (snd hu) PropCode evA fm
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm =
    adequacyEqSub2-Fst-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PairCode _ _) (fst hu) (snd hu) (SigmaCode _ _) evA fm
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- conv-Fst at UCode: requires ValTy2/EqValTy2 for Fst M, Fst M'
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    let htM = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        evFstM' = convSound (conv-Fst dA dB dMM') rho fits UCode hu
        evU = mkSigma tt (LeCode-refl UCode tt)
        valA  = adequacySub2 dA sigma rho crho vs fits wtsub wfH UCode evA UCode evU tt
        valFM = adequacySub2 (ty-Fst dA dB htM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm
        valFM' = adequacySub2 (ty-Fst dA dB htM') sigma rho crho vs fits wtsub wfH UCode evFstM' UCode evA fm
    in mkSigma (snd valA) (mkSigma (snd valFM) (mkSigma (snd valFM') (mkSigma (snd valFM) (snd valFM'))))
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    let htM = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        evFstM' = convSound (conv-Fst dA dB dMM') rho fits PropCode hu
        evU = mkSigma tt (LeCode-refl UCode tt)
        valA  = adequacySub2 dA sigma rho crho vs fits wtsub wfH UCode evA UCode evU tt
        valFM = adequacySub2 (ty-Fst dA dB htM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm
        valFM' = adequacySub2 (ty-Fst dA dB htM') sigma rho crho vs fits wtsub wfH PropCode evFstM' UCode evA fm
    in mkSigma (snd valA) (mkSigma (snd valFM) (mkSigma (snd valFM') (mkSigma (snd valFM) (snd valFM'))))
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  -- conv-Fst at (FunEl, UCode): ValTy2/EqValTy2 at FunEl = Top
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  -- conv-Fst at (PiCode/SigmaCode, UCode): hard, need ValTyPi2/ValTySigma2 for Fst M
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm =
    adequacyEqSub2-Fst-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PiCode _ _) (fst hu) (snd hu) UCode evA fm
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm =
    adequacyEqSub2-Fst-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) (fst hu) (snd hu) UCode evA fm
  -- conv-Fst at PiCode: only non-trivial when u = FunEl
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  -- conv-Fst at (FunEl, PiCode): hard, need full Pi semantics for Fst M
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (PiCode _ _) evA fm =
    adequacyEqSub2-Fst-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (FunEl _) (fst hu) (snd hu) (PiCode _ _) evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Snd
  -- Snd M = Snd M' : subst1 B (Fst M). Similar to conv-Fst.
  ----------------------------------------------------------------------

  -- conv-Snd: Snd M = Snd M' : subst1 B (Fst M). Type is subst1 B (Fst M) : U. Most (u,a) trivial.
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    adequacyEqSub2-Snd-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PiCode a' f') (fst hu) (snd hu) PropCode evA fm
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm =
    adequacyEqSub2-Snd-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PairCode _ _) (fst hu) (snd hu) (SigmaCode _ _) evA fm
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- conv-Snd at UCode: requires ValTy2/EqValTy2 for Snd M, Snd M'
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    let htM = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        evSndM' = convSound (conv-Snd dA dB dMM') rho fits UCode hu
        evU = mkSigma tt (LeCode-refl UCode tt)
        dBFst = typing-type (ty-Snd dA dB htM)
        valT  = adequacySub2 dBFst sigma rho crho vs fits wtsub wfH UCode evA UCode evU tt
        valSM = adequacySub2 (ty-Snd dA dB htM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm
        cvFst  = conv-Fst dA dB dMM'
        htFstM = ty-Fst dA dB htM
        htFstM' = ty-Fst dA dB htM'
        cvBFst = subst1-cong-ConvTm dA dB htFstM htFstM' cvFst
        htSndM'_conv = ty-conv (ty-Snd dA dB htM') (conv-sym cvBFst) dBFst
        valSM' = adequacySub2 htSndM'_conv sigma rho crho vs fits wtsub wfH UCode evSndM' UCode evA fm
    in mkSigma (snd valT) (mkSigma (snd valSM) (mkSigma (snd valSM') (mkSigma (snd valSM) (snd valSM'))))
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    let htM = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        evSndM' = convSound (conv-Snd dA dB dMM') rho fits PropCode hu
        evU = mkSigma tt (LeCode-refl UCode tt)
        dBFst = typing-type (ty-Snd dA dB htM)
        valT  = adequacySub2 dBFst sigma rho crho vs fits wtsub wfH UCode evA UCode evU tt
        valSM = adequacySub2 (ty-Snd dA dB htM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm
        cvFst  = conv-Fst dA dB dMM'
        htFstM = ty-Fst dA dB htM
        htFstM' = ty-Fst dA dB htM'
        cvBFst = subst1-cong-ConvTm dA dB htFstM htFstM' cvFst
        htSndM'_conv = ty-conv (ty-Snd dA dB htM') (conv-sym cvBFst) dBFst
        valSM' = adequacySub2 htSndM'_conv sigma rho crho vs fits wtsub wfH PropCode evSndM' UCode evA fm
    in mkSigma (snd valT) (mkSigma (snd valSM) (mkSigma (snd valSM') (mkSigma (snd valSM) (snd valSM'))))
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  -- conv-Snd at (FunEl, UCode): Val2 at FunEl/UCode = Top
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  -- conv-Snd at (PiCode/SigmaCode, UCode): hard, need ValTyPi2/ValTySigma2 for Snd M
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm =
    adequacyEqSub2-Snd-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (PiCode _ _) (fst hu) (snd hu) UCode evA fm
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm =
    adequacyEqSub2-Snd-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) (fst hu) (snd hu) UCode evA fm
  -- conv-Snd at PiCode: only non-trivial when u = FunEl
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  -- conv-Snd at (FunEl, PiCode): hard, need full Pi semantics for Snd M
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (PiCode _ _) evA fm =
    adequacyEqSub2-Snd-from-EqValPair2 dA dB dMM' sigma rho crho vs fits wtsub wfH (FunEl _) (fst hu) (snd hu) (PiCode _ _) evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-funext (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-funext dA d1 d2 d3) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-funext dA d1 d2 d3 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-fun (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-fun _ dB d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-fun dB d1 d2 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-arg (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-arg _ dB d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-arg dB d1 d2 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- Stub helpers (delegating to the full implementations)
  -- These are placeholders that use the structure from Adequacy2.agda
  -- adapted for the Sigma extension.
  ----------------------------------------------------------------------

  -- Val2 at U b UCode extractor (local version for mutual block)
  Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
    (b : FinEl) -> FinMem b UCode ->
    Val2 G M U b UCode -> ValTy2 G M b
  Val2-U-to-ValTy2 Bot _ _ = tt
  Val2-U-to-ValTy2 UCode _ v = snd v
  Val2-U-to-ValTy2 PropCode _ v = snd v
  Val2-U-to-ValTy2 (PiCode _ _) _ v = snd v
  Val2-U-to-ValTy2 (SigmaCode _ _) _ v = snd v
  Val2-U-to-ValTy2 (FunEl _) () _
  Val2-U-to-ValTy2 (PairCode _ _) () _

  EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G M v0
  EqVal2-U-to-ValTy2-fst Bot _ _ = tt
  EqVal2-U-to-ValTy2-fst UCode _ ev = fst (snd ev)
  EqVal2-U-to-ValTy2-fst PropCode _ ev = fst (snd ev)
  EqVal2-U-to-ValTy2-fst (PiCode _ _) _ ev = fst (snd ev)
  EqVal2-U-to-ValTy2-fst (SigmaCode _ _) _ ev = fst (snd ev)
  EqVal2-U-to-ValTy2-fst (FunEl _) () _
  EqVal2-U-to-ValTy2-fst (PairCode _ _) () _

  EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G N v0
  EqVal2-U-to-ValTy2-snd Bot _ _ = tt
  EqVal2-U-to-ValTy2-snd UCode _ ev = fst (snd (snd ev))
  EqVal2-U-to-ValTy2-snd PropCode _ ev = fst (snd (snd ev))
  EqVal2-U-to-ValTy2-snd (PiCode _ _) _ ev = fst (snd (snd ev))
  EqVal2-U-to-ValTy2-snd (SigmaCode _ _) _ ev = fst (snd (snd ev))
  EqVal2-U-to-ValTy2-snd (FunEl _) () _
  EqVal2-U-to-ValTy2-snd (PairCode _ _) () _

  EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> EqValTy2 G M N v0
  EqVal2-U-to-EqValTy2 Bot _ _ = tt
  EqVal2-U-to-EqValTy2 UCode _ ev = snd (snd (snd ev))
  EqVal2-U-to-EqValTy2 PropCode _ ev = snd (snd (snd ev))
  EqVal2-U-to-EqValTy2 (PiCode _ _) _ ev = snd (snd (snd ev))
  EqVal2-U-to-EqValTy2 (SigmaCode _ _) _ ev = snd (snd (snd ev))
  EqVal2-U-to-EqValTy2 (FunEl _) () _
  EqVal2-U-to-EqValTy2 (PairCode _ _) () _

  -- transportVal2: transport Val2 H N sA u0 b to Val2 H N sA u' a_arg
  transportVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> FinMem b UCode ->
    EvalRel A rho b ->
    (u0 : FinEl) -> FinMem u0 b ->
    (N : Expr h) -> Val2 H N (substExpr sigma A) u0 b ->
    (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
    (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
    Val2 H N (substExpr sigma A) u' a_arg
  transportVal2 {H = H} {A = A} d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
    let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
        a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtA_b    = Val2-U-to-ValTy2 b bU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
        vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
    in sup-transport-Val2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN

  -- transportEqVal2: transport EqVal2 H N1 N2 sA u0 b to EqVal2 H N1 N2 sA u' a_arg
  transportEqVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {N1 N2 : Expr h} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> FinMem b UCode ->
    EvalRel A rho b ->
    (u0 : FinEl) -> FinMem u0 b ->
    EqVal2 H N1 N2 (substExpr sigma A) u0 b ->
    (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
    (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
    EqVal2 H N1 N2 (substExpr sigma A) u' a_arg
  transportEqVal2 {H = H} {A = A} d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
    let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
        a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtA_b    = Val2-U-to-ValTy2 b bU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
        vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
    in sup-transport-EqVal2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN

  -- Sigma Pi helpers (stubs - to be filled with full proofs)
  adequacySub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    Val2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) U (PiCode b f) UCode
  adequacySub2-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm =
    let sA    = substExpr sigma A
        sB    = substExpr (liftSub sigma) B
        bU    = fst fm
        allU  = fst (snd fm)
        cf    = snd (snd fm)
        cb    = coh-from-aU b bU
        evAb  = fst (snd hu)
        valTyA = Val2-U-to-ValTy2 b bU
                   (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode
                     (mkSigma tt (LeCode-refl UCode tt)) bU)
        htA  = subst-HasType wtsub wfH d1
        htB  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend (subst-HasType wtsub wfH d1)) d2
    in mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (record
         { domA = sA ; codB = sB
         ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA htB))
         ; cohF = cf ; fmAllU = allU ; htA = htA ; htB = htB ; valA = valTyA
         ; edgeV = buildPiEdgeVal2 d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm
         ; edgeE = buildPiEdgeEq2 d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm })

  -- buildPiEdgeVal2: PiEdgeVal2 for the Pi case
  buildPiEdgeVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeVal2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeVal2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm u0 v0 sel N htN valN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        bodyPi   = snd (snd (snd (snd hu)))
        fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
        fm_v0_U  = FinMem-Selection-UCode b sel allU cf
        cu0      = FinMem-coh-u u0 b fm_u0_b
        w        = bodyPi u0 v0 sel
        x        = fst w
        le_x_u0  = fst (snd w)
        fm_x_a'  = fst (snd (snd w))
        evB_x_v0 = snd (snd (snd w))
        cx       = FinMem-coh-u x a'pi fm_x_a'
        envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
        evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
        fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
        crho'    = mkSigma crho cu0
        htA      = subst-HasType wtsub wfH d1
        hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
        wtsub'   = extSub-WtSub wtsub wfH d1 htN
        evU      = mkSigma tt (LeCode-refl UCode tt)
        ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evU fm_v0_U)
    in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih

  -- buildPiEdgeEq2: PiEdgeEq2 for the Pi case
  buildPiEdgeEq2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeEq2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeEq2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        bodyPi   = snd (snd (snd (snd hu)))
        fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
        fm_v0_U  = FinMem-Selection-UCode b sel allU cf
        cu0      = FinMem-coh-u u0 b fm_u0_b
        valN1    = Val2-from-EqVal2-first u0 b eqvalN
        valN2    = Val2-from-EqVal2-second u0 b eqvalN
        w        = bodyPi u0 v0 sel
        x        = fst w
        le_x_u0  = fst (snd w)
        fm_x_a'  = fst (snd (snd w))
        evB_x_v0 = snd (snd (snd w))
        cx       = FinMem-coh-u x a'pi fm_x_a'
        envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
        evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
        fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
        crho'    = mkSigma crho cu0
        htA      = subst-HasType wtsub wfH d1
        -- IH for N1
        hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
        evU      = mkSigma tt (LeCode-refl UCode tt)
        wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
        wfH'     = wfH
        vtN1     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N1) (extendEnv rho u0)
                       crho' vs'_N1 fits' wtsub'_N1 wfH' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN1'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N1)) vtN1
        -- IH for N2
        hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
        wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
        vtN2     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N2 fits' wtsub'_N2 wfH' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN2'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N2)) vtN2
        -- Use adequacyConvSub2 on d2
        vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                     (ValidConvSub2-refl {G = G} vs)
                     (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
        wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
        raw      = adequacyConvSub2 d2 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                     crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH'
                     v0 evB_u0_v0 UCode evU fm_v0_U
        raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                     (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
    in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

  adequacySub2-Sigma : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b f) ->
    EvalRel U rho UCode ->
    FinMem (SigmaCode b f) UCode ->
    Val2 H (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B)) U (SigmaCode b f) UCode
  adequacySub2-Sigma {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm =
    let sA    = substExpr sigma A
        sB    = substExpr (liftSub sigma) B
        bU    = fst fm
        allU  = fst (snd fm)
        cf    = snd (snd fm)
        cb    = coh-from-aU b bU
        evAb  = fst (snd hu)
        valTyA = Val2-U-to-ValTy2 b bU
                   (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode
                     (mkSigma tt (LeCode-refl UCode tt)) bU)
        htA  = subst-HasType wtsub wfH d1
        htB  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend (subst-HasType wtsub wfH d1)) d2
        buildEdgeVal : SigmaEdgeVal2 H sA sB b f
        buildEdgeVal u0 v0 sel N htN valN =
          let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
              fm_v0_U  = FinMem-Selection-UCode b sel allU cf
              cu0      = FinMem-coh-u u0 b fm_u0_b
              w        = snd (snd (snd (snd hu))) u0 v0 sel
              x        = fst w
              le_x_u0  = fst (snd w)
              fm_x_a'  = fst (snd (snd w))
              evB_x_v0 = snd (snd (snd w))
              cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
              envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
              evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
              fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
              crho'    = mkSigma crho cu0
              hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
              wtsub'   = extSub-WtSub wtsub wfH d1 htN
              evU      = mkSigma tt (LeCode-refl UCode tt)
              ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                           (adequacySub2 d2 (extSub sigma N) (extendEnv rho u0)
                             crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evU fm_v0_U)
          in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih
        buildEdgeEq : SigmaEdgeEq2 H sA sB b f
        buildEdgeEq u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
          let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
              fm_v0_U  = FinMem-Selection-UCode b sel allU cf
              cu0      = FinMem-coh-u u0 b fm_u0_b
              valN1    = Val2-from-EqVal2-first u0 b eqvalN
              valN2    = Val2-from-EqVal2-second u0 b eqvalN
              w        = snd (snd (snd (snd hu))) u0 v0 sel
              x        = fst w
              le_x_u0  = fst (snd w)
              fm_x_a'  = fst (snd (snd w))
              evB_x_v0 = snd (snd (snd w))
              cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
              envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
              evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
              fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
              crho'    = mkSigma crho cu0
              evU      = mkSigma tt (LeCode-refl UCode tt)
              hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
              wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
              hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
              wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
              vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                           (ValidConvSub2-refl {G = G} vs)
                           (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
              wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
              raw      = adequacyConvSub2 d2 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                           crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                           v0 evB_u0_v0 UCode evU fm_v0_U
              raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                           (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
          in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'
    in mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (record
         { domA = sA ; codB = sB
         ; red = mkRed3 headred-refl (conv-refl (ty-Sigma htA htB))
         ; cohF = cf ; fmAllU = allU ; fmBU = bU ; htA = htA ; htB = htB ; valA = valTyA
         ; edgeV = buildEdgeVal ; edgeE = buildEdgeEq })

  -- Helper: extract SigmaEdgeEq2 with known domA=sA, codB=sB
  getSigmaEdgeEq : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b f) ->
    FinMem (SigmaCode b f) UCode ->
    SigmaEdgeEq2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  getSigmaEdgeEq d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm =
    RValTySigma.edgeE (snd (adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f hu
      (mkSigma tt (LeCode-refl UCode tt)) fm))

  adequacySub2-MkPair : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M0 N0 : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M0 A -> HasType G N0 (subst1 B M0) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u' v' : FinEl) ->
    EvalRel (MkPair M0 N0) rho (PairCode u' v') ->
    (b0 : FinEl) -> (f0 : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b0 f0) ->
    FinMem (PairCode u' v') (SigmaCode b0 f0) ->
    Val2 H (MkPair (substExpr sigma M0) (substExpr sigma N0))
           (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
           (PairCode u' v') (SigmaCode b0 f0)
  adequacySub2-MkPair {H = H} {G = G} {A = A} {B = B} {M0 = M0} {N0 = N0}
      d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u' v' hu b0 f0 evA fm =
    mkSigma vtySig (record
        { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl htSig)
        ; htFst = htFst ; cohW1 = cu' ; fmW1 = fm_u'_b0
        ; valFst = val_fst ; valSnd = val_snd })
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sM  = substExpr sigma M0
      sN  = substExpr sigma N0
      evM = fst (snd hu)
      evN = snd (snd hu)
      evA_b0 = fst (snd evA)
      fm_u'_b0 = fst (fst fm)
      fm_v'_ef = snd (fst fm)
      cu' = fst (fst (fst (snd fm)))
      pSigU = snd (snd fm)
      cf0_sig = snd (snd pSigU)
      allU_sig = fst (snd pSigU)
      bU_sig = fst pSigU
      evU  = mkSigma tt (LeCode-refl UCode tt)
      -- Typing
      htA_loc = subst-HasType wtsub wfH d1
      htB_loc = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA_loc) d2
      htM_loc = subst-HasType wtsub wfH d3
      htN_raw = subst-HasType wtsub wfH d4
      htN_loc = S.Eq-transport (HasType H sN) (S.Eq-sym (subst-subst1-comm sigma B M0)) htN_raw
      htSig   = ty-Sigma htA_loc htB_loc
      htMkPair = ty-MkPair htA_loc htB_loc htM_loc htN_loc
      htFst   = ty-Fst htA_loc htB_loc htMkPair
      -- RValTySigma from adequacySub2-Sigma (now checkable since defined above)
      vtySig = snd (adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b0 f0 evA evU pSigU)
      sigEdgeEq0 = getSigmaEdgeEq d1 d2 sigma rho crho vs fits wtsub wfH b0 f0 evA pSigU
      -- Fst: Val2 H sM sA u' b0 → Val2 H (Fst (MkPair sM sN)) sA u' b0
      val_M = adequacySub2 d3 sigma rho crho vs fits wtsub wfH u' evM b0 evA_b0 fm_u'_b0
      hr-fst : HeadRed (Fst (MkPair sM sN)) sM
      hr-fst = headred-step (headred-beta-fst {M = sM} {N = sN}) headred-refl
      cv-fst = conv-beta-fst htA_loc htB_loc htM_loc htN_loc
      val_fst = Val2-beta-expand u' b0 hr-fst cv-fst val_M
      eq_fst = V5L.Val2-beta-expand u' b0 hr-fst cv-fst val_M
      -- Snd: derive EvalRel B (extendEnv rho u') (EvalFun f0 u') from Sigma-edgewise
      sew = Sigma-edgewise A B rho b0 f0 evA
      cf0_sew = snd (fst sew)
      a'_sew  = fst (snd (snd sew))
      wf_sew  = snd (snd (snd (snd sew)))
      evB_u'_ef = EvalRel-body-EvalFun B rho u' a'_sew f0 crho cu' cf0_sew wf_sew
      evBM_ef   = EvalRel-subst1-backward B M0 rho u' (EvalFun f0 u') crho evM evB_u'_ef
      val_N_raw = adequacySub2 d4 sigma rho crho vs fits wtsub wfH v' evN (EvalFun f0 u') evBM_ef fm_v'_ef
      val_N_sM = S.Eq-transport (\ T -> Val2 H sN T v' (EvalFun f0 u'))
                   (S.Eq-sym (subst-subst1-comm sigma B M0)) val_N_raw
      -- Beta-expand Snd (MkPair sM sN) →* sN at type (subst1 sB sM)
      hr-snd : HeadRed (Snd (MkPair sM sN)) sN
      hr-snd = headred-step (headred-beta-snd {M = sM} {N = sN}) headred-refl
      cv-snd-sM = conv-beta-snd htA_loc htB_loc htM_loc htN_loc
      val_snd_sM = Val2-beta-expand v' (EvalFun f0 u') hr-snd cv-snd-sM val_N_sM
      -- Transport type from (subst1 sB sM) to (subst1 sB (Fst (MkPair sM sN)))
      cb_sig = coh-from-aU b0 bU_sig
      sb = selectionBelow f0 u' cf0_sig cu'
      u-f = fst sb
      v-f = fst (snd sb)
      sel-f = fst (snd (snd sb))
      le-uf = fst (snd (snd (snd sb)))
      eq-ef = snd (snd (snd (snd sb)))
      fmu-f = FinMemAllU-Selection b0 sel-f allU_sig cf0_sig cb_sig bU_sig
      eq_fst_uf = restrictEqVal2 H sM (Fst (MkPair sM sN)) sA u' u-f b0 le-uf fmu-f fm_u'_b0 eq_fst
      eqTyB_vf = sigEdgeEq0 u-f v-f sel-f
                    sM (Fst (MkPair sM sN)) htM_loc htFst (conv-sym cv-fst) eq_fst_uf
      eqTyB_ef = S.Eq-transport (EqValTy2 H (subst1 sB sM) (subst1 sB (Fst (MkPair sM sN))))
                   (S.Eq-sym eq-ef) eqTyB_vf
      val_snd = Val2-type-transport v' (EvalFun f0 u') eqTyB_ef val_snd_sM

  adequacySub2-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
      {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} ->
      HasType G A U -> HasType (extend G A) B U ->
      HasType (extend G A) M B ->
      (sigma : Sub h g) -> (rho : EnvApprox g) ->
      CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
      WtSub H G sigma -> WfCtx H ->
      (g0 : FinFun) ->
      EvalRel (Lam A M) rho (FunEl g0) ->
      (b : FinEl) -> (f0 : FinFun) ->
      EvalRel (Pi A B) rho (PiCode b f0) ->
      FinMem (FunEl g0) (PiCode b f0) ->
      Val2 H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
             (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (FunEl g0) (PiCode b f0)
  adequacySub2-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3
      sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
    mkSigma (snd valTyPi) (record
      { domA0 = sA ; codB0 = sB
      ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_lam htB_lam))
      ; cohG = cg ; fmG = fmg ; appV = piAppVal ; appE = piAppEq })
    where
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sM   = substExpr (liftSub sigma) M
      fmg  = fst fm
      cg   = fst (snd fm)
      pU   = snd (snd fm)
      bU   = fst pU
      allU = fst (snd pU)
      cf0  = snd (snd pU)
      cb   = coh-from-aU b bU
      evAb = fst (snd evA)
      a_lam = fst hu
      bodyLam = snd (snd (snd (snd hu)))
      evU  = mkSigma tt (LeCode-refl UCode tt)
      htA_lam = subst-HasType wtsub wfH d1
      htB_lam = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA_lam) d2
      htM_lam = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA_lam) d3
      valTyPi = adequacySub2 (ty-Pi d1 d2) sigma rho crho vs fits wtsub wfH
                  (PiCode b f0) evA UCode evU pU
      piAppVal : PiAppVal2 H (Lam sA sM) sA sB b f0 g0
      piAppVal u' v' sel N htN valN =
        let cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u' v' sel
            x         = fst w
            le_x_u'   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v'  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
            evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
            evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
            crho'     = mkSigma crho cu'
            hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'       = ValidSub2-extend sigma N rho u' vs hyp0
            wtsub'    = extSub-WtSub wtsub wfH d1 htN
            ih        = adequacySub2 d3 (extSub sigma N) (extendEnv rho u')
                          crho' vs' fits' wtsub' wfH v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M      = S.Eq-sym (substExpr-comp sigma M N)
            eq_B      = S.Eq-sym (substExpr-comp sigma B N)
            ih'       = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u')) eq_B ih
            ih''      = S.Eq-transport (\ E -> Val2 H E (subst1 sB N) v' (EvalFun f0 u')) eq_M ih'
        in Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl)
             (conv-beta htA_lam htB_lam htM_lam htN) ih''
      piAppEq : PiAppEq2 H (Lam sA sM) sA sB b f0 g0
      piAppEq u' v' sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1     = Val2-from-EqVal2-first u' b eqvalN
            valN2     = Val2-from-EqVal2-second u' b eqvalN
            cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u' v' sel
            x         = fst w
            le_x_u'   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v'  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
            evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
            evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
            crho'     = mkSigma crho cu'
            wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
            wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
            hyp0_N1   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            hyp0_N2   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'_N1    = ValidSub2-extend sigma N1 rho u' vs hyp0_N1
            vs'_N2    = ValidSub2-extend sigma N2 rho u' vs hyp0_N2
            vcs_ext   = ValidConvSub2-extend sigma sigma N1 N2 rho u'
                          (ValidConvSub2-refl {G = G} vs)
                          (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b eqvalN)
            wcs_ext   = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
            raw       = adequacyConvSub2 d3 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u')
                          crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                          v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M1     = S.Eq-sym (substExpr-comp sigma M N1)
            eq_M2     = S.Eq-sym (substExpr-comp sigma M N2)
            eq_B1     = S.Eq-sym (substExpr-comp sigma B N1)
            raw'      = S.Eq-transport (\ T -> EqVal2 H (subst1 sM N1) T (subst1 sB N1) v' (EvalFun f0 u')) eq_M2
                          (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) M) (subst1 sB N1) v' (EvalFun f0 u')) eq_M1
                            (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u')) eq_B1 raw))
            cvBeta2   = conv-beta htA_lam htB_lam htM_lam htN2
            cvB21     = subst1-cong-ConvTm htA_lam htB_lam htN2 htN1 (conv-sym cvN)
            htB1      = typing-type (snd (typing-ConvTm (conv-beta htA_lam htB_lam htM_lam htN1)))
            cvBeta2'  = conv-conv cvBeta2 cvB21 htB1
        in EqVal2-headred-expand v' (EvalFun f0 u')
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
             (conv-beta htA_lam htB_lam htM_lam htN1) cvBeta2' raw'

  adequacySub2-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
    WtSub H G0 sigma -> WfCtx H ->
    (u : FinEl) -> Coherent u ->
    EvalRel (App f' a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u ac
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev Bot evAc fm = tt
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev UCode evAc fm =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev PropCode evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1 ev1 PropCode evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) PropCode evAc1 fm1
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev UCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev Bot evAc ()
  -- SigmaCode at UCode: delegate to App-core (handles all (u1, ac1) pairs)
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode a0s f0s) cu ev UCode evAc fm =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode a0s f0s) cu
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev UCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode u0p v0p) cu ev (SigmaCode b0s f0s) evAc fm =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode u0p v0p) cu
      (fst ev) (fst (snd ev)) (snd (snd ev)) (SigmaCode b0s f0s) evAc fm
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev Bot evAc ()
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev UCode evAc fm =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH Bot cu ev ac evAc fm = Val2-Bot ac
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1 ev1 UCode evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) UCode evAc1 fm1
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1 ev1 (PiCode bacfe facfe) evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (PiCode bacfe facfe) evAc1 fm1

  -- Extract Val2 for Fst sM from M's ValPair2 via theorem1 + adequacySub2 dM.
  -- Works for any (u, a) where u is non-Bot and the result is non-trivial.
  -- The approach: decompose hu to get EvalRel M rho (PairCode u v),
  -- enlarge via theorem1 dM, call adequacySub2 dM at (PairCode, SigmaCode),
  -- extract Val2 (Fst sM) from ValPair2, restrict from enlarged u₀ to u.
  adequacySub2-Fst-from-ValPair2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> (v_snd : FinEl) -> EvalRel M rho (PairCode u v_snd) ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (Fst (substExpr sigma M)) (substExpr sigma A) u a
  adequacySub2-Fst-from-ValPair2 {H = H} {A = A} {B = B} {M = M}
    dA dB dM sigma rho crho vs fits wtsub wfH u v_snd evM_pair a evA fm =
    let -- Enlarge M via theorem1
        typed_M = theorem1 dM rho fits (PairCode u v_snd) evM_pair
        u_big   = fst typed_M
        a_sig   = fst (snd typed_M)
        le_pair = fst (snd (snd typed_M))
        evM_big = fst (snd (snd (snd typed_M)))
        fm_big  = fst (snd (snd (snd (snd typed_M))))
        evSig   = snd (snd (snd (snd (snd typed_M))))
    in fst-dispatch u_big a_sig le_pair evM_big fm_big evSig
    where
      sM = substExpr sigma M
      sA = substExpr sigma A
      -- Only (PairCode, SigmaCode) is productive; all others are absurd
      fst-dispatch : (u_big a_sig : FinEl) ->
        LeCode (PairCode u v_snd) u_big ->
        EvalRel M rho u_big -> FinMem u_big a_sig ->
        EvalRel (SigmaE A B) rho a_sig ->
        Val2 H (Fst sM) sA u a
      -- u_big = Bot/UCode/PropCode/FunEl/PiCode/SigmaCode: LeCode (PairCode _ _) u_big = Empty
      fst-dispatch Bot _ () _ _ _
      fst-dispatch UCode _ () _ _ _
      fst-dispatch PropCode _ () _ _ _
      fst-dispatch (FunEl _) _ () _ _ _
      fst-dispatch (PiCode _ _) _ () _ _ _
      fst-dispatch (SigmaCode _ _) _ () _ _ _
      -- PairCode: dispatch on a_sig
      fst-dispatch (PairCode u0 v0) Bot _ _ () _
      fst-dispatch (PairCode u0 v0) UCode _ _ () _
      fst-dispatch (PairCode u0 v0) PropCode _ _ () _
      fst-dispatch (PairCode u0 v0) (FunEl _) _ _ () _
      fst-dispatch (PairCode u0 v0) (PiCode _ _) _ _ () _
      fst-dispatch (PairCode u0 v0) (PairCode _ _) _ _ () _
      -- PairCode, SigmaCode: the productive case
      fst-dispatch (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig =
        let -- Get ValPair2 from adequacySub2 dM
            val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH
                      (PairCode u0 v0) evM_big (SigmaCode b0 f0) evSig fm_big
            -- val_M : Pair (RValTySigma H (SigmaE sA sB) b0 f0) (RValSigma H sM (SigmaE sA sB) (PairCode u0 v0) b0 f0)
            vsig   = snd val_M
            red_sig = RValSigma.red vsig
            val_fst_raw = RValSigma.valFst vsig
            -- domA = sA by Red3-unique-Sigma (SigmaE sA sB is head normal form)
            htA_f = subst-HasType wtsub wfH dA
            htB_f = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA_f) dB
            mkSigma eqA _ = Red3-unique-Sigma red_sig (mkRed3 headred-refl (conv-refl (ty-Sigma htA_f htB_f)))
            val_fst = S.Eq-transport (\ X -> Val2 H (Fst sM) X u0 b0) eqA val_fst_raw
            -- LeCode u u0 (first component of PairCode ordering)
            le_u = fst le_pair
            -- FinMem u0 b0 from FinMem (PairCode u0 v0) (SigmaCode b0 f0)
            fm_u0_b0 = fst (fst fm_big)
            -- EvalRel A rho b0 from evSig
            evA_b0 = fst (snd evSig)
            -- Get ValTy2 sA at b0 for transport
            evU = mkSigma tt (LeCode-refl UCode tt)
            fm_b0_U = fst (snd (snd fm_big))
            valTy_b0 = Val2-U-to-ValTy2 b0 fm_b0_U
                         (adequacySub2 dA sigma rho crho vs fits wtsub wfH b0 evA_b0 UCode evU fm_b0_U)
            -- Get ValTy2 sA at a for transport
            fm_a_U = FinMem-a-in-U u a fm
            valTy_a = Val2-U-to-ValTy2 a fm_a_U
                        (adequacySub2 dA sigma rho crho vs fits wtsub wfH a evA UCode evU fm_a_U)
            -- Transport val_fst from (u0, b0) to (u, a) via sup-transport-Val2
            cb0 = coh-from-aU b0 fm_b0_U
            ca  = coh-from-aU a fm_a_U
            cu  = FinMem-Coherent u a fm
            comp_b0_a = EvalRel-Comp A rho crho b0 a evA_b0 evA
        in sup-transport-Val2 {H = H} {N = Fst sM} {A = sA}
             b0 a comp_b0_a fm_b0_U fm_a_U
             u0 u fm_u0_b0 cu le_u fm
             valTy_b0 valTy_a val_fst

  -- adequacySub2-Snd-from-ValPair2: extract Snd from PairCode evaluation of M
  -- Mirrors adequacySub2-Fst-from-ValPair2 but extracts valSnd + type transport
  adequacySub2-Snd-from-ValPair2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (v : FinEl) -> (u_fst : FinEl) -> EvalRel M rho (PairCode u_fst v) ->
    (a : FinEl) -> EvalRel (subst1 B (Fst M)) rho a -> FinMem v a ->
    Val2 H (Snd (substExpr sigma M)) (substExpr sigma (subst1 B (Fst M))) v a
  adequacySub2-Snd-from-ValPair2 {H = H} {A = A} {B = B} {M = M}
    dA dB dM sigma rho crho vs fits wtsub wfH v u_fst evM_pair a evBFst fm =
    let typed_M = theorem1 dM rho fits (PairCode u_fst v) evM_pair
        u_big   = fst typed_M
        a_sig   = fst (snd typed_M)
        le_pair = fst (snd (snd typed_M))
        evM_big = fst (snd (snd (snd typed_M)))
        fm_big  = fst (snd (snd (snd (snd typed_M))))
        evSig   = snd (snd (snd (snd (snd typed_M))))
    in snd-dispatch u_big a_sig le_pair evM_big fm_big evSig
    where
      sM = substExpr sigma M
      sBFst = substExpr sigma (subst1 B (Fst M))
      snd-dispatch : (u_big a_sig : FinEl) ->
        LeCode (PairCode u_fst v) u_big ->
        EvalRel M rho u_big -> FinMem u_big a_sig ->
        EvalRel (SigmaE A B) rho a_sig ->
        Val2 H (Snd sM) sBFst v a
      snd-dispatch Bot _ () _ _ _
      snd-dispatch UCode _ () _ _ _
      snd-dispatch PropCode _ () _ _ _
      snd-dispatch (FunEl _) _ () _ _ _
      snd-dispatch (PiCode _ _) _ () _ _ _
      snd-dispatch (SigmaCode _ _) _ () _ _ _
      snd-dispatch (PairCode u0 v0) Bot _ _ () _
      snd-dispatch (PairCode u0 v0) UCode _ _ () _
      snd-dispatch (PairCode u0 v0) PropCode _ _ () _
      snd-dispatch (PairCode u0 v0) (FunEl _) _ _ () _
      snd-dispatch (PairCode u0 v0) (PiCode _ _) _ _ () _
      snd-dispatch (PairCode u0 v0) (PairCode _ _) _ _ () _
      snd-dispatch (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig =
        let val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH
                      (PairCode u0 v0) evM_big (SigmaCode b0 f0) evSig fm_big
            vsig    = snd val_M
            red_sig = RValSigma.red vsig
            htA_s = subst-HasType wtsub wfH dA
            htB_s = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA_s) dB
            mkSigma eqA eqB = Red3-unique-Sigma red_sig
                                (mkRed3 headred-refl (conv-refl (ty-Sigma htA_s htB_s)))
            -- valSnd at (v0, EvalFun f0 u0) with type subst1 codB (Fst sM)
            val_snd_raw = RValSigma.valSnd vsig
            -- Transport codB to sB via eqB, domA to sA via eqA
            sA = substExpr sigma A
            sB = substExpr (liftSub sigma) B
            val_snd_typed = S.Eq-transport
              (\ X -> Val2 H (Snd sM) (subst1 X (Fst sM)) v0 (EvalFun f0 u0)) eqB
              val_snd_raw
            -- We need EvalRel (subst1 B (Fst M)) rho (EvalFun f0 u0) for the type
            sew = Sigma-edgewise A B rho b0 f0 evSig
            cf0_sew = snd (fst sew)
            a'_sew  = fst (snd (snd sew))
            wf_sew  = snd (snd (snd (snd sew)))
            cu0     = fst (fst (fst (snd fm_big)))
            evB_ef  = EvalRel-body-EvalFun B rho u0 a'_sew f0 crho cu0 cf0_sew wf_sew
            evFst_u0 : EvalRel (Fst M) rho u0
            evFst_u0 = mkFstEv M rho u0 v0 evM_big
            evBFst_ef = EvalRel-subst1-backward B (Fst M) rho u0 (EvalFun f0 u0) crho evFst_u0 evB_ef
            -- FinMem v0 (EvalFun f0 u0)
            fm_v0_ef = snd (fst fm_big)
            -- Get ValTy2 at (EvalFun f0 u0) and at a for transport
            dBFst = typing-type (ty-Snd dA dB dM)
            evU = mkSigma tt (LeCode-refl UCode tt)
            fm_ef_U = FinMem-a-in-U v0 (EvalFun f0 u0) fm_v0_ef
            valTy_ef = Val2-U-to-ValTy2 (EvalFun f0 u0) fm_ef_U
                         (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH
                           (EvalFun f0 u0) evBFst_ef UCode evU fm_ef_U)
            fm_a_U = FinMem-a-in-U v a fm
            valTy_a = Val2-U-to-ValTy2 a fm_a_U
                        (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH a evBFst UCode evU fm_a_U)
            -- LeCode v v0
            le_v = snd le_pair
            cv = FinMem-Coherent v a fm
            comp_ef_a = EvalRel-Comp (subst1 B (Fst M)) rho crho (EvalFun f0 u0) a evBFst_ef evBFst
            eq_sBFst = subst-subst1-comm sigma B (Fst M)
            val_snd_final = S.Eq-transport (\ T -> Val2 H (Snd sM) T v0 (EvalFun f0 u0)) eq_sBFst val_snd_typed
        in sup-transport-Val2 {H = H} {N = Snd sM} {A = sBFst}
             (EvalFun f0 u0) a comp_ef_a fm_ef_U fm_a_U
             v0 v fm_v0_ef cv le_v fm
             valTy_ef valTy_a val_snd_final

  adequacySub2-Snd-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (Snd M) rho u ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (subst1 B (Fst M)) rho (PiCode b f) -> FinMem u (PiCode b f) ->
    Typed (Snd M) (subst1 B (Fst M)) rho u ->
    Val2 H (Snd (substExpr sigma M)) (substExpr sigma (subst1 B (Fst M))) u (PiCode b f)
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH Bot hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH UCode hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH PropCode hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PiCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PairCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi {H = H} {A = A} {B = B} {M = M} dA dB dM sigma rho crho vs fits wtsub wfH (FunEl gu) hu b f evA fm typed =
    let u'      = fst typed
        a'      = fst (snd typed)
        le'     = fst (snd (snd typed))
        evSnd'  = fst (snd (snd (snd typed)))
        fm'     = fst (snd (snd (snd (snd typed))))
        evBFst' = snd (snd (snd (snd (snd typed))))
        dBFst   = typing-type (ty-Snd dA dB dM)
        val_snd = adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u' evSnd' a' evBFst' fm'
        evU0    = mkSigma tt (LeCode-refl UCode tt)
        fm_a'_U = FinMem-a-in-U u' a' fm'
        valTy_a' = Val2-U-to-ValTy2 a' fm_a'_U
                     (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH a' evBFst' UCode evU0 fm_a'_U)
        fm_pf_U = FinMem-a-in-U (FunEl gu) (PiCode b f) fm
        valTy_pf = Val2-U-to-ValTy2 (PiCode b f) fm_pf_U
                     (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH (PiCode b f) evA UCode evU0 fm_pf_U)
        cv      = FinMem-Coherent (FunEl gu) (PiCode b f) fm
        comp    = EvalRel-Comp (subst1 B (Fst M)) rho crho a' (PiCode b f) evBFst' evA
    in sup-transport-Val2 {H = H} {N = Snd (substExpr sigma M)} {A = substExpr sigma (subst1 B (Fst M))}
         a' (PiCode b f) comp fm_a'_U fm_pf_U
         u' (FunEl gu) fm' cv le' fm
         valTy_a' valTy_pf val_snd

  -- adequacyEqSub2-Fst-from-EqValPair2: EqVal2 for Fst from PairCode evaluation of M, M'
  -- Pattern: theorem1 on M and M', enlarge to (PairCode, SigmaCode), call adequacyEqSub2,
  -- extract eqFst from REqValSigma, transport to target codes.
  adequacyEqSub2-Fst-from-EqValPair2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M M' : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    ConvTm G M M' (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> (v_snd : FinEl) -> EvalRel M rho (PairCode u v_snd) ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (Fst (substExpr sigma M)) (Fst (substExpr sigma M')) (substExpr sigma A) u a
  adequacyEqSub2-Fst-from-EqValPair2 {H = H} {A = A} {B = B} {M = M} {M' = M'}
    dA dB dMM' sigma rho crho vs fits wtsub wfH u v_snd evM_pair a evA fm =
    let htM  = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        -- Get M' evaluation via convSound
        evM'_pair_raw = convSound dMM' rho fits (PairCode u v_snd) evM_pair
        -- theorem1 on M to enlarge
        typed_M = theorem1 htM rho fits (PairCode u v_snd) evM_pair
    in fst-eq-dispatch (fst typed_M) (fst (snd typed_M))
         (fst (snd (snd typed_M))) (fst (snd (snd (snd typed_M))))
         (fst (snd (snd (snd (snd typed_M))))) (snd (snd (snd (snd (snd typed_M)))))
    where
      sM  = substExpr sigma M
      sM' = substExpr sigma M'
      sA  = substExpr sigma A
      fst-eq-dispatch : (u_big a_sig : FinEl) ->
        LeCode (PairCode u v_snd) u_big ->
        EvalRel M rho u_big -> FinMem u_big a_sig ->
        EvalRel (SigmaE A B) rho a_sig ->
        EqVal2 H (Fst sM) (Fst sM') sA u a
      fst-eq-dispatch Bot _ () _ _ _
      fst-eq-dispatch UCode _ () _ _ _
      fst-eq-dispatch PropCode _ () _ _ _
      fst-eq-dispatch (FunEl _) _ () _ _ _
      fst-eq-dispatch (PiCode _ _) _ () _ _ _
      fst-eq-dispatch (SigmaCode _ _) _ () _ _ _
      fst-eq-dispatch (PairCode u0 v0) Bot _ _ () _
      fst-eq-dispatch (PairCode u0 v0) UCode _ _ () _
      fst-eq-dispatch (PairCode u0 v0) PropCode _ _ () _
      fst-eq-dispatch (PairCode u0 v0) (FunEl _) _ _ () _
      fst-eq-dispatch (PairCode u0 v0) (PiCode _ _) _ _ () _
      fst-eq-dispatch (PairCode u0 v0) (PairCode _ _) _ _ () _
      fst-eq-dispatch (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig =
        let -- Get M' eval at enlarged code via convSound
            evM'_big = convSound dMM' rho fits (PairCode u0 v0) evM_big
            -- Call adequacyEqSub2 at (PairCode, SigmaCode) to get REqValSigma
            eq_M = adequacyEqSub2 dMM' sigma rho crho vs fits wtsub wfH
                     (PairCode u0 v0) evM_big (SigmaCode b0 f0) evSig fm_big
            -- eq_M : Pair (RValTySigma ...) (Pair (RValSigma M ...) (Pair (RValSigma M' ...) (REqValSigma ...)))
            eqsig  = snd (snd (snd eq_M))
            eq_fst_raw = REqValSigma.eqFst eqsig
            red_sig = REqValSigma.red eqsig
            -- Transport domA to sA
            htA_f = subst-HasType wtsub wfH dA
            htB_f = subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend htA_f) dB
            mkSigma eqA _ = Red3-unique-Sigma red_sig (mkRed3 headred-refl (conv-refl (ty-Sigma htA_f htB_f)))
            eq_fst = S.Eq-transport (\ X -> EqVal2 H (Fst sM) (Fst sM') X (codeFst (PairCode u0 v0)) b0) eqA eq_fst_raw
            -- Transport from (u0, b0) to (u, a) via sup-transport-EqVal2
            le_u = fst le_pair
            fm_u0_b0 = fst (fst fm_big)
            evA_b0 = fst (snd evSig)
            evU = mkSigma tt (LeCode-refl UCode tt)
            fm_b0_U = fst (snd (snd fm_big))
            valTy_b0 = Val2-U-to-ValTy2 b0 fm_b0_U
                          (adequacySub2 dA sigma rho crho vs fits wtsub wfH b0 evA_b0 UCode evU fm_b0_U)
            fm_a_U = FinMem-a-in-U u a fm
            valTy_a = Val2-U-to-ValTy2 a fm_a_U
                        (adequacySub2 dA sigma rho crho vs fits wtsub wfH a evA UCode evU fm_a_U)
            cb0 = coh-from-aU b0 fm_b0_U
            ca  = coh-from-aU a fm_a_U
            cu  = FinMem-Coherent u a fm
            comp_b0_a = EvalRel-Comp A rho crho b0 a evA_b0 evA
        in sup-transport-EqVal2 {H = H} {N1 = Fst sM} {N2 = Fst sM'} {A = sA}
             b0 a comp_b0_a fm_b0_U fm_a_U
             u0 u fm_u0_b0 cu le_u fm
             valTy_b0 valTy_a eq_fst

  -- adequacyEqSub2-Snd-from-EqValPair2: EqVal2 for Snd from PairCode evaluation of M, M'
  -- Pattern: theorem1 to enlarge, construct Snd eval at enlarged code,
  -- recursively call adequacyEqSub2 (conv-Snd ...) at enlarged codes,
  -- then sup-transport to target codes.
  adequacyEqSub2-Snd-from-EqValPair2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M M' : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    ConvTm G M M' (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (v : FinEl) -> (u_fst : FinEl) -> EvalRel M rho (PairCode u_fst v) ->
    (a : FinEl) -> EvalRel (subst1 B (Fst M)) rho a -> FinMem v a ->
    EqVal2 H (Snd (substExpr sigma M)) (Snd (substExpr sigma M'))
             (substExpr sigma (subst1 B (Fst M))) v a
  adequacyEqSub2-Snd-from-EqValPair2 {H = H} {A = A} {B = B} {M = M} {M' = M'}
    dA dB dMM' sigma rho crho vs fits wtsub wfH v u_fst evM_pair a evBFst fm =
    let htM  = fst (typing-ConvTm dMM')
        htM' = snd (typing-ConvTm dMM')
        typed_M = theorem1 htM rho fits (PairCode u_fst v) evM_pair
    in snd-eq-dispatch (fst typed_M) (fst (snd typed_M))
         (fst (snd (snd typed_M))) (fst (snd (snd (snd typed_M))))
         (fst (snd (snd (snd (snd typed_M))))) (snd (snd (snd (snd (snd typed_M)))))
    where
      sM  = substExpr sigma M
      sM' = substExpr sigma M'
      sBFstM = substExpr sigma (subst1 B (Fst M))
      snd-eq-dispatch : (u_big a_sig : FinEl) ->
        LeCode (PairCode u_fst v) u_big ->
        EvalRel M rho u_big -> FinMem u_big a_sig ->
        EvalRel (SigmaE A B) rho a_sig ->
        EqVal2 H (Snd sM) (Snd sM') sBFstM v a
      snd-eq-dispatch Bot _ () _ _ _
      snd-eq-dispatch UCode _ () _ _ _
      snd-eq-dispatch PropCode _ () _ _ _
      snd-eq-dispatch (FunEl _) _ () _ _ _
      snd-eq-dispatch (PiCode _ _) _ () _ _ _
      snd-eq-dispatch (SigmaCode _ _) _ () _ _ _
      snd-eq-dispatch (PairCode u0 v0) Bot _ _ () _
      snd-eq-dispatch (PairCode u0 v0) UCode _ _ () _
      snd-eq-dispatch (PairCode u0 v0) PropCode _ _ () _
      snd-eq-dispatch (PairCode u0 v0) (FunEl _) _ _ () _
      snd-eq-dispatch (PairCode u0 v0) (PiCode _ _) _ _ () _
      snd-eq-dispatch (PairCode u0 v0) (PairCode _ _) _ _ () _
      snd-eq-dispatch (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig =
        let -- Construct EvalRel (Snd M) rho v0
            evSnd_v0 = mkSndEv M rho u0 v0 evM_big
            -- Construct EvalRel (subst1 B (Fst M)) rho (EvalFun f0 u0) from Sigma semantics
            sew = Sigma-edgewise A B rho b0 f0 evSig
            cf0_sew = snd (fst sew)
            a'_sew  = fst (snd (snd sew))
            wf_sew  = snd (snd (snd (snd sew)))
            cu0     = fst (fst (fst (snd fm_big)))
            evB_ef  = EvalRel-body-EvalFun B rho u0 a'_sew f0 crho cu0 cf0_sew wf_sew
            evFst_u0 = mkFstEv M rho u0 v0 evM_big
            evBFst_ef = EvalRel-subst1-backward B (Fst M) rho u0 (EvalFun f0 u0) crho evFst_u0 evB_ef
            -- FinMem v0 (EvalFun f0 u0)
            fm_v0_ef = snd (fst fm_big)
            -- Recursively call adequacyEqSub2 (conv-Snd) at enlarged codes
            cvSnd = conv-Snd dA dB dMM'
            eq_snd = adequacyEqSub2 cvSnd sigma rho crho vs fits wtsub wfH
                           v0 evSnd_v0 (EvalFun f0 u0) evBFst_ef fm_v0_ef
            -- Transport from (v0, EvalFun f0 u0) to (v, a) via sup-transport-EqVal2
            le_v = snd le_pair
            cv = FinMem-Coherent v a fm
            htM_loc = fst (typing-ConvTm dMM')
            dBFst = typing-type (ty-Snd dA dB htM_loc)
            evU = mkSigma tt (LeCode-refl UCode tt)
            fm_ef_U = FinMem-a-in-U v0 (EvalFun f0 u0) fm_v0_ef
            valTy_ef = Val2-U-to-ValTy2 (EvalFun f0 u0) fm_ef_U
                         (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH
                           (EvalFun f0 u0) evBFst_ef UCode evU fm_ef_U)
            fm_a_U = FinMem-a-in-U v a fm
            valTy_a = Val2-U-to-ValTy2 a fm_a_U
                        (adequacySub2 dBFst sigma rho crho vs fits wtsub wfH a evBFst UCode evU fm_a_U)
            comp_ef_a = EvalRel-Comp (subst1 B (Fst M)) rho crho (EvalFun f0 u0) a evBFst_ef evBFst
        in sup-transport-EqVal2 {H = H} {N1 = Snd sM} {N2 = Snd sM'} {A = sBFstM}
             (EvalFun f0 u0) a comp_ef_a fm_ef_U fm_a_U
             v0 v fm_v0_ef cv le_v fm
             valTy_ef valTy_a eq_snd

  adequacyEqSub2-beta : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} {a : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType (extend G A) M B -> HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App (Lam A M) a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (substExpr sigma (App (Lam A M) a))
             (substExpr sigma (subst1 M a))
             (substExpr sigma (subst1 B a)) u ac
  adequacyEqSub2-beta {H = H} {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
    let val_app = adequacySub2 (ty-App d1 d2 (ty-Lam d1 d2 d3) d4)
                    sigma rho crho vs fits wtsub wfH u hu ac evAc fm
        sA   = substExpr sigma A
        sB   = substExpr (liftSub sigma) B
        sM0  = substExpr (liftSub sigma) M
        sa   = substExpr sigma a0
        htA  = subst-HasType wtsub wfH d1
        htB  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA) d2
        htM  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA) d3
        hta  = subst-HasType wtsub wfH d4
        beta-hr : HeadRed (App (Lam sA sM0) sa) (substExpr sigma (subst1 M a0))
        beta-hr = S.Eq-transport
                    (\ X -> HeadRed (App (Lam sA sM0) sa) X)
                    (subst-subst1-comm sigma M a0)
                    (headred-step headred-beta headred-refl)
        cv-beta : ConvTm H (App (Lam sA sM0) sa) (substExpr sigma (subst1 M a0))
                           (substExpr sigma (subst1 B a0))
        cv-beta = S.Eq-transport
                    (\ X -> ConvTm H (App (Lam sA sM0) sa) X (substExpr sigma (subst1 B a0)))
                    (subst-subst1-comm sigma M a0)
                    (S.Eq-transport
                      (\ X -> ConvTm H (App (Lam sA sM0) sa) (subst1 sM0 sa) X)
                      (subst-subst1-comm sigma B a0)
                      (conv-beta htA htB htM hta))
        val_subst = Val2-headred-contract u ac beta-hr cv-beta val_app
        eqval_diag = Val2-to-EqVal2 u ac val_subst
        ht-subst = snd (typing-ConvTm cv-beta)
    in EqVal2-headred-expand u ac beta-hr headred-refl cv-beta (conv-refl ht-subst) eqval_diag

  adequacyEqSub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G A A' U ->
    ConvTm (extend G A) B B' U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (Pi (substExpr sigma A') (substExpr (liftSub sigma) B'))
             U (PiCode b f) UCode
  adequacyEqSub2-Pi {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 sigma rho crho vs fits wtsub wfH b f hu evU fm =
    let valTyU : ValTy2 H U UCode
        valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))
    in mkSigma valTyU (mkSigma valTyPiAB (mkSigma valTyPiA'B' eqValTyPi))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma A'
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma) B'
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      a'pi = fst (snd (snd hu))
      bodyPi = snd (snd (snd (snd hu)))

      eqD1 = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evUU bU
      valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
      valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
      eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

      trVal : (u0 : FinEl) -> FinMem u0 b ->
        (N : Expr _) -> Val2 H N sA u0 b ->
        (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H N sA u' a_arg
      trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
        let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
            a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
            vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                         (adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evUU a_argU)
            vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
            ca_arg   = EvalRel-coh A rho a_arg evA_arg
            sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
            c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
            le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
            le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
            fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
            fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
            val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
            val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
            val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
        in val3

      -- Build codomain validity for B (first side)
      buildEdgeValB2 : PiEdgeVal2 H sA sB b f
      buildEdgeValB2 u0 v0 sel N htN valN =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
             (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

      buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
      buildEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1    = Val2-from-EqVal2-first u0 b eqvalN
            valN2    = Val2-from-EqVal2-second u0 b eqvalN
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB_conv  = fst (typing-ConvTm d2)
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
            raw      = adequacyConvSub2 dB_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      -- B' validity
      buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
      buildEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
        let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N
                           (Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A') u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
             (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

      -- B' edge equality (simplified)
      buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
      buildEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB'_conv = snd (typing-ConvTm d2)
            htA_loc  = subst-HasType wtsub wfH dA_conv
            convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
            htN1_A   = ty-conv htN1_A' convA'A htA_loc
            htN2_A   = ty-conv htN2_A' convA'A htA_loc
            cvN_A    = conv-conv cvN_A' convA'A htA_loc
            eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
            valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
            valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
            evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB'_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
            raw      = adequacyConvSub2 dB'_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB'_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
      buildEdgeEqTyBB'2 u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
            ih       = adequacyEqSub2 d2 (extSub sigma P) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
            eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                         (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                           (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
        in eqvt

      htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
      htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

      valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
      valTyPiAB = record
        { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
        ; cohF = cf ; fmAllU = allU ; htA = htA_AB ; htB = htB_AB
        ; valA = valTyA ; edgeV = buildEdgeValB2 ; edgeE = buildEdgeEqB2 }

      htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
      htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
      htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

      valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
      valTyPiA'B' = record
        { domA = sA' ; codB = sB' ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
        ; cohF = cf ; fmAllU = allU ; htA = htA_A'B' ; htB = htB_A'B'
        ; valA = valTyA' ; edgeV = buildEdgeValB'2 ; edgeE = buildEdgeEqB'2 }

      convA_sub  = subst-ConvTm wtsub wfH d1
      convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

      eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
      eqValTyPi = mkSigma valTyPiAB (mkSigma valTyPiA'B' (record
        { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
        ; redM = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
        ; redN = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
        ; cohF = cf ; fmAllU = allU
        ; convA = convA_sub ; convB = convB_sub
        ; eqA = eqValTyAA' ; edgeET = buildEdgeEqTyBB'2 }))


  adequacyEqSub2-Sigma : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G A A' U ->
    ConvTm (extend G A) B B' U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b f) ->
    EvalRel U rho UCode ->
    FinMem (SigmaCode b f) UCode ->
    EqVal2 H (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
             (SigmaE (substExpr sigma A') (substExpr (liftSub sigma) B'))
             U (SigmaCode b f) UCode
  -- Mirrors adequacyEqSub2-Pi with SigmaEdge functions.
  adequacyEqSub2-Sigma {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 sigma rho crho vs fits wtsub wfH b f hu evU fm =
    let valTyU : ValTy2 H U UCode
        valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))
    in mkSigma valTyU (mkSigma valTySigmaAB (mkSigma valTySigmaA'B' eqValTySigma))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma A'
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma) B'
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      a'sig = fst (snd (snd hu))
      bodySigma = snd (snd (snd (snd hu)))

      eqD1 = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evUU bU
      valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
      valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
      eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

      trVal : (u0 : FinEl) -> FinMem u0 b ->
        (N : Expr _) -> Val2 H N sA u0 b ->
        (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H N sA u' a_arg
      trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
        let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
            a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
            vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                         (adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evUU a_argU)
            vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
            ca_arg   = EvalRel-coh A rho a_arg evA_arg
            sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
            c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
            le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
            le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
            fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
            fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
            val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
            val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
            val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
        in val3

      -- Build codomain validity for B (first side)
      buildSigmaEdgeValB2 : SigmaEdgeVal2 H sA sB b f
      buildSigmaEdgeValB2 u0 v0 sel N htN valN =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
             (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

      buildSigmaEdgeEqB2 : SigmaEdgeEq2 H sA sB b f
      buildSigmaEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1    = Val2-from-EqVal2-first u0 b eqvalN
            valN2    = Val2-from-EqVal2-second u0 b eqvalN
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB_conv  = fst (typing-ConvTm d2)
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
            raw      = adequacyConvSub2 dB_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      -- B' validity (primed side)
      buildSigmaEdgeValB'2 : SigmaEdgeVal2 H sA' sB' b f
      buildSigmaEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
        let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N
                           (Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A') u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
             (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

      -- B' edge equality (primed side)
      buildSigmaEdgeEqB'2 : SigmaEdgeEq2 H sA' sB' b f
      buildSigmaEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB'_conv = snd (typing-ConvTm d2)
            htA_loc  = subst-HasType wtsub wfH dA_conv
            convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
            htN1_A   = ty-conv htN1_A' convA'A htA_loc
            htN2_A   = ty-conv htN2_A' convA'A htA_loc
            cvN_A    = conv-conv cvN_A' convA'A htA_loc
            eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
            valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
            valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
            evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB'_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
            raw      = adequacyConvSub2 dB'_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB'_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      buildSigmaEdgeEqTyBB'2 : SigmaEdgeEqTy2 H sA sB sB' b f
      buildSigmaEdgeEqTyBB'2 u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
            ih       = adequacyEqSub2 d2 (extSub sigma P) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
            eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                         (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                           (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
        in eqvt

      htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
      htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

      valTySigmaAB : ValTy2 H (SigmaE sA sB) (SigmaCode b f)
      valTySigmaAB = record
        { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Sigma htA_AB htB_AB))
        ; cohF = cf ; fmAllU = allU ; fmBU = bU ; htA = htA_AB ; htB = htB_AB
        ; valA = valTyA ; edgeV = buildSigmaEdgeValB2 ; edgeE = buildSigmaEdgeEqB2 }

      htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
      htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
      htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

      valTySigmaA'B' : ValTy2 H (SigmaE sA' sB') (SigmaCode b f)
      valTySigmaA'B' = record
        { domA = sA' ; codB = sB' ; red = mkRed3 headred-refl (conv-refl (ty-Sigma htA_A'B' htB_A'B'))
        ; cohF = cf ; fmAllU = allU ; fmBU = bU ; htA = htA_A'B' ; htB = htB_A'B'
        ; valA = valTyA' ; edgeV = buildSigmaEdgeValB'2 ; edgeE = buildSigmaEdgeEqB'2 }

      convA_sub  = subst-ConvTm wtsub wfH d1
      convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

      eqValTySigma : EqValTy2 H (SigmaE sA sB) (SigmaE sA' sB') (SigmaCode b f)
      eqValTySigma = mkSigma valTySigmaAB (mkSigma valTySigmaA'B' (record
        { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
        ; redM = mkRed3 headred-refl (conv-refl (ty-Sigma htA_AB htB_AB))
        ; redN = mkRed3 headred-refl (conv-refl (ty-Sigma htA_A'B' htB_A'B'))
        ; cohF = cf ; fmAllU = allU
        ; convA = convA_sub ; convB = convB_sub
        ; eqA = eqValTyAA' ; edgeET = buildSigmaEdgeEqTyBB'2 }))


  adequacyEqSub2-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
    HasType G A U ->
    ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                         (App (wkExpr g') (Var fzero)) B ->
    HasType G f (Pi A B) ->
    HasType G g' (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel f rho u ->
    (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma f) (substExpr sigma g')
            (substExpr sigma (Pi A B)) u a
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH Bot hu (PiCode b f0) evA fm = tt
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH UCode hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH PropCode hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext {H = H} {G = G} {A = A} {B = B} {f = f} {g' = g'} dA d df dg sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm =
    let val_sf = adequacySub2 df sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
        evG    = convSound (conv-funext dA d df dg) rho fits (FunEl g0) hu
        val_sg = adequacySub2 dg sigma rho crho vs fits wtsub wfH (FunEl g0) evG (PiCode b f0) evA fm
        valTyPi = fst val_sf
        valPi_sf = snd val_sf
        valPi_sg = snd val_sg
    in mkSigma valTyPi (mkSigma valPi_sf (mkSigma valPi_sg
         (record { domA0 = substExpr sigma A
                 ; codB0 = substExpr (liftSub sigma) B
                 ; red = mkRed3 headred-refl (conv-refl (ty-Pi (subst-HasType wtsub wfH dA) (subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend (subst-HasType wtsub wfH dA)) (typing-Pi-codomain dA df))))
                 ; cohG = RValPi.cohG valPi_sf
                 ; fmG = RValPi.fmG valPi_sf
                 ; appEV = buildEqBody valPi_sf })))
    where
      sA'   = substExpr sigma A
      sB'   = substExpr (liftSub sigma) B
      htBU' = typing-Pi-codomain dA df
      fmg'  = fst fm
      cg'   = fst (snd fm)
      pU'   = snd (snd fm)
      bU'   = fst pU'
      allU' = fst (snd pU')
      cf0'  = snd (snd pU')
      cb'   = coh-from-aU b bU'
      evAb' = fst (snd evA)
      ctg0' = cft-from-cf g0 cg'

      -- Core: build EqVal2 for non-Bot v0, taking ev_app as parameter
      buildEqBodyCore : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        Coherent u0 ->
        EvalRel (App (wkExpr f) (Var fzero)) (extendEnv rho u0) v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      buildEqBodyCore u0 v0 sel cu0 ev_app P htP valP =
        let fm_u0_b   = FinMem-Selection b f0 sel fmg' ctg0' cb' bU'
            fm_v0_ef  = FinMem-Selection-codomain b f0 sel fmg' ctg0' cf0' allU'
            evB_ef    = EvalRel-Pi-body A B rho b f0 u0 crho cu0 evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb'))
            crho'     = mkSigma crho cu0
            hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 dA htBU' sigma rho crho vs fits wtsub wfH b bU' evAb' u0 fm_u0_b P valP u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'       = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'    = extSub-WtSub wtsub wfH dA htP
            raw       = adequacyEqSub2 d (extSub sigma P) (extendEnv rho u0) crho' vs' fits' wtsub' wfH
                          v0 ev_app (EvalFun f0 u0) evB_ef fm_v0_ef
            eq_f_wk   = substExpr-wk sigma f P
            eq_g_wk   = substExpr-wk sigma g' P
            eq_B_comp = S.Eq-sym (substExpr-comp sigma B P)
            raw'      = S.Eq-transport (\ T -> EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) T v0 (EvalFun f0 u0)) eq_B_comp
                          (S.Eq-transport (\ X -> EqVal2 H (App (substExpr sigma f) P) (App X P) (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_g_wk
                            (S.Eq-transport (\ X -> EqVal2 H (App X P) _ (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_f_wk raw))
        in raw'

      -- Build singleton eval data and call core (for each concrete v0)
      mkEvAppAndCall : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        Coherent u0 -> Coherent v0 -> NotBot v0 ->
        EvalRel (App (wkExpr f) (Var fzero)) (extendEnv rho u0) v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      mkEvAppAndCall u0 v0 sel cu0 cv0 nbv0 ev_app P htP valP =
        buildEqBodyCore u0 v0 sel cu0 ev_app P htP valP

      mkSingEvApp : (u0 : FinEl) (v0 : FinEl) -> Coherent u0 -> Coherent v0 -> NotBot v0 ->
        LeCode v0 (EvalFun g0 u0) ->
        EvalRel f rho (FunEl (cons (mkSigma u0 v0) nil))
      mkSingEvApp u0 v0 cu0 cv0 nbv0 le_v0 =
        let c_sing    = mkCFT cu0 cv0 nbv0 tt tt
        in EvalRel-down f rho (FunEl g0) (FunEl (cons (mkSigma u0 v0) nil))
                          crho c_sing hu (mkSigma le_v0 tt)

      buildEqBody : _ -> (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      buildEqBody _ u0 Bot sel P htP valP = EqVal2-Bot (EvalFun f0 u0)
      buildEqBody vps u0 UCode sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 UCode cu0 tt tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 UCode) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 UCode sel cu0 ev_app P htP valP
      buildEqBody vps u0 PropCode sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 PropCode cu0 tt tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 PropCode) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 PropCode sel cu0 ev_app P htP valP
      buildEqBody vps u0 (FunEl g1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (FunEl g1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (FunEl g1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (FunEl g1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (PiCode a1 f1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (PiCode a1 f1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (PiCode a1 f1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (PiCode a1 f1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (SigmaCode a1 f1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (SigmaCode a1 f1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (SigmaCode a1 f1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (SigmaCode a1 f1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (PairCode u1 v1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (PairCode u1 v1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (PairCode u1 v1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (PairCode u1 v1) sel cu0 ev_app P htP valP

  adequacyEqSub2-App-fun-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
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
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-fun-core {H = H}
    dB dff' da sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    adequacyEqSub2-App-fun-core-body {H = H}
      dB dff' da sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
      (\ d s r cr vss fi ws wH u ev a evA fm -> adequacySub2 d s r cr vss fi ws wH u ev a evA fm)
      (\ d s r cr vss fi ws wH u ev a evA fm -> adequacyEqSub2 d s r cr vss fi ws wH u ev a evA fm)
      (\ b fm v -> Val2-U-to-ValTy2 b fm v)

  adequacyEqSub2-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev Bot evAc ()
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH UCode ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH UCode
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev PropCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) PropCode evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev PropCode evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev Bot evAc fm = tt
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH PropCode
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode b0sc f0sc) ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode b0sc f0sc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev UCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PairCode u0p v0p) ev (SigmaCode b0s f0s) evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PairCode u0p v0p)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (SigmaCode b0s f0s) evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  adequacyEqSub2-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev Bot evAc ()
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH UCode ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH UCode
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev PropCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) PropCode evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev PropCode evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev Bot evAc fm = tt
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH PropCode
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode b0sc f0sc) ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode b0sc f0sc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev UCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PairCode u0p v0p) ev (SigmaCode b0s f0s) evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PairCode u0p v0p)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (SigmaCode b0s f0s) evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PairCode _ _) evAc fm = tt
  -- PiCode/UCode and FunEl/PiCode
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  -- Core App-arg helper
  adequacyEqSub2-App-arg-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
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
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-arg-core {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
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

      -- Enlarge function via theorem1 (df : HasType)
      typed_f  = theorem1 df rho fits (FunEl sing) evF_sing
      u_big    = fst typed_f
      a_pi     = fst (snd typed_f)
      le_sing  = fst (snd (snd typed_f))
      evF_big  = fst (snd (snd (snd typed_f)))
      fm_big   = fst (snd (snd (snd (snd typed_f))))
      evPi     = snd (snd (snd (snd (snd typed_f))))

      -- Function's Val2
      val_fun  = adequacySub2 df sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

      -- Helper: Val2 for sa via Val2-from-EqVal2-first
      val_sa : (u' : FinEl) -> EvalRel a rho u' ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H sa sA u' a_arg
      val_sa u' evA_u' a_arg evA_aarg fm_u'_a =
        Val2-from-EqVal2-first u' a_arg
          (adequacyEqSub2 daa' sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a)

      -- InvTyp for a from convSound' daa'
      invTyp_a = fst (convSound' daa' rho fits)

      -- Dispatch on (ub, ap)
      appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        Val2 H sf (Pi sA sB) ub ap ->
        EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
      appEqVal-dispatch Bot          ap    () evFb evPab fmba valba
      appEqVal-dispatch UCode        ap    () evFb evPab fmba valba
      appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
      appEqVal-dispatch PropCode     ap    () evFb evPab fmba valba
      appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba valba
      appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba valba
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
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

            -- Argument EqVal2 via adequacyEqSub2 daa'
            evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
            eqval_arg = adequacyEqSub2 daa' sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract PiAppEq2 from function's Val2 at (FunEl, PiCode)
            -- Val2 = Pair ValTyPi2 ValPi2
            vpi_fun  = snd valba
            A0_fun   = RValPi.domA0 vpi_fun
            B0_fun   = RValPi.codB0 vpi_fun
            red_fun  = RValPi.red vpi_fun
            uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_fun))
            eqA_fun  = fst uniq_fun
            eqB_fun  = snd uniq_fun
            pae_fun  = RValPi.appE vpi_fun

            -- Transport argument types
            eqval_arg' = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_fun eqval_arg
            ht_sa_A0   = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH (fst (typing-ConvTm daa')))
            ht_sa'_A0  = S.Eq-transport (\ X -> HasType H sa' X) eqA_fun (subst-HasType wtsub wfH (snd (typing-ConvTm daa')))
            cv_aa'_A0  = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_fun (subst-ConvTm wtsub wfH daa')

            -- Apply PiAppEq2
            eqval_app_raw : EqVal2 H (App sf sa) (App sf sa') (subst1 B0_fun sa) v_sel (EvalFun f_pi u_sel)
            eqval_app_raw = pae_fun u_sel v_sel sel_big sa sa' ht_sa_A0 ht_sa'_A0 cv_aa'_A0 eqval_arg'
            eqval_app : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            eqval_app = S.Eq-transport
              (\ X -> EqVal2 H (App sf sa) (App sf sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_fun) eqval_app_raw

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
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
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
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

        in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_app

      transported : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
      transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

  -- Also define adequacySub2-App-core (needed by adequacySub2-App)
  adequacySub2-App-core : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
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
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u1 ac1
  adequacySub2-App-core {H = H}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH u1 cu1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    adequacySub2-App-core-body {H = H}
      dA dB d1 d2 sigma rho crho vs fits wtsub wfH u1 cu1 v0 evA_v0 evF_sing ac1 evAc1 fm1
      (\ d s r cr vss fi ws wH u ev a evA fm -> adequacySub2 d s r cr vss fi ws wH u ev a evA fm)
      (\ b fm v -> Val2-U-to-ValTy2 b fm v)
      (\ ac ef comp acU efU vs0 u10 fmv fmu le vtac vtef val -> app-transport-Val2 ac ef comp acU efU vs0 u10 fmv fmu le vtac vtef val)

  ----------------------------------------------------------------------
  -- adequacyConvSub2 cases (stubs)
  ----------------------------------------------------------------------

  -- Core helper for adequacyConvSub2 ty-App
  adequacyConvSub2-App-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
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
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma' f) (substExpr sigma' a))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyConvSub2-App-core {H = H}
    d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    adequacyConvSub2-App-core-body {H = H}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      u1 v0 evA_v0 evF_sing ac1 evAc1 fm1
      (\ d s r cr vss fi ws wH u ev a evA fm -> adequacySub2 d s r cr vss fi ws wH u ev a evA fm)
      (\ d s1 s2 r cr vss vss' vcss fi ws ws' wcs' wH u ev a evA fm -> adequacyConvSub2 d s1 s2 r cr vss vss' vcss fi ws ws' wcs' wH u ev a evA fm)
      (\ b fm v -> Val2-U-to-ValTy2 b fm v)
      (\ ac ef comp acU efU vs0 u10 fmv fmu le vtac vtef eq -> app-transport-EqVal2 ac ef comp acU efU vs0 u10 fmv fmu le vtac vtef eq)

  adequacyConvSub2 (ty-var {G = G} {i = i} _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    vcs i u (fst hu) (snd hu) a evA fm

  adequacyConvSub2 (ty-U wfG) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 (ty-U wfG) sigma rho crho vs fits wtsub wfH u hu a evA fm)

  adequacyConvSub2 (ty-Prop wfG) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 (ty-Prop wfG) sigma rho crho vs fits wtsub wfH u hu a evA fm)

  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu UCode evA fm = tt
  adequacyConvSub2 {M = M} (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
    absurd-UCode-at-Prop-conv (theorem1 d rho fits UCode hu)
    where
      absurd-UCode-at-Prop-conv :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
          Pair (LeCode UCode u') (Pair (EvalRel M rho u') (Pair (FinMem u' a') (EvalRel Prop rho a'))))) -> _
      absurd-UCode-at-Prop-conv (mkSigma Bot (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma (PiCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma Bot (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma UCode (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma PropCode (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma (FunEl _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma (PiCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-UCode-at-Prop-conv (mkSigma UCode (mkSigma (PairCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))

  adequacyConvSub2 {M = M} (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm =
    absurd-PropCode-at-Prop-conv (theorem1 d rho fits PropCode hu)
    where
      absurd-PropCode-at-Prop-conv :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
          Pair (LeCode PropCode u') (Pair (EvalRel M rho u') (Pair (FinMem u' a') (EvalRel Prop rho a'))))) -> _
      absurd-PropCode-at-Prop-conv (mkSigma Bot (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma UCode (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma (PiCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma Bot (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma UCode (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma PropCode (mkSigma _ (mkSigma _ (mkSigma () _)))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma (FunEl _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma (PiCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))
      absurd-PropCode-at-Prop-conv (mkSigma PropCode (mkSigma (PairCode _ _) (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ ()))))))

  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA ()
  adequacyConvSub2 {H = H} {M = M} (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu UCode evA fm =
    convSub2-Prop-U-PiCode-aux (theorem1 d rho fits (PiCode a' f') hu)
    where
      convSub2-Prop-U-PiCode-aux :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
          Pair (LeCode (PiCode a' f') u')
          (Pair (EvalRel M rho u')
          (Pair (FinMem u' a_t) (EvalRel Prop rho a_t))))) ->
        EqVal2 H (substExpr sigma M) (substExpr sigma' M) U (PiCode a' f') UCode
      convSub2-Prop-U-PiCode-aux (mkSigma Bot (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma UCode (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
        let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
            eq_bg_prop = adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                      (PiCode b g) hu' PropCode (mkSigma tt tt) fmBG
            vtU = mkRed3 headred-refl (conv-refl (ty-U wfH))
            eq_bg = mkSigma vtU (snd eq_bg_prop)
        in restrictEqVal2 H (substExpr sigma M) (substExpr sigma' M) U
             (PiCode b g) (PiCode a' f') UCode le fm fmBG_U eq_bg
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu UCode evA fm =
    let typed = theorem1 d rho fits (SigmaCode _ _) hu
    in sigma-split-cs (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
    where
      sigma-split-cs : (a_t u' : FinEl) -> LeCode (SigmaCode _ _) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
      sigma-split-cs Bot u' le fm_u' _ =
        absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode _ _) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
      sigma-split-cs PropCode (SigmaCode _ _) le () _
      sigma-split-cs UCode _ _ _ ()
      sigma-split-cs (FunEl _) _ _ _ ()
      sigma-split-cs (PiCode _ _) _ _ _ ()
      sigma-split-cs (SigmaCode _ _) _ _ _ ()
      sigma-split-cs (PairCode _ _) _ _ _ ()
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode _ _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) (mkSigma _ ()) fm

  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 UCode aU eqAB
    in EqVal2-EqValTy2-fwd u UCode tt eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl g) evA fm = tt
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA' fm
        pU    = FinMem-a-in-U (PiCode a' f') PropCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH PropCode evA' UCode evU pU
        eqvty = EqVal2-U-to-EqValTy2 PropCode pU eqAB
    in EqVal2-EqValTy2-fwd (PiCode a' f') PropCode tt eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu PropCode evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (PiCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv {A = A} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (SigmaCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (SigmaCode b' f') evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (SigmaCode b' f') evA' fm
        aU    = FinMem-a-in-U (PairCode u' v') (SigmaCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b' f') evA' UCode evU aU
        eqvty = EqVal2-U-to-EqValTy2 (SigmaCode b' f') aU eqAB
    in EqVal2-EqValTy2-fwd (PairCode u' v') (SigmaCode b' f') (EvalRel-coh A rho (SigmaCode b' f') evA') eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) evA fm = tt

  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu PropCode (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Pi {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode evA fm =
    mkSigma (fst valTyPi_s) (mkSigma (snd valTyPi_s) (mkSigma (snd valTyPi_s') (mkSigma (snd valTyPi_s) (mkSigma (snd valTyPi_s') eqValTyPi))))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      bodyPi = snd (snd (snd (snd hu)))

      valTyPi_s  = adequacySub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f0 hu evA fm
      valTyPi_s' = adequacySub2-Pi d1 d2 sigma' rho crho vs' fits wtsub' wfH b f0 hu evA fm

      eqD1 = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evUU bU
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

      htA_loc  = subst-HasType wtsub wfH d1
      htA'_loc = subst-HasType wtsub' wfH d1
      convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      wtsub_lift  = liftSub-WtSub wtsub wfH d1
      wtsub'_lift_raw = liftSub-WtSub wtsub' wfH d1
      wtsub'_lift : WtSub (extend H sA) (extend G A) (liftSub sigma')
      wtsub'_lift = \ i -> ctx-conv-HasType htA'_loc htA_loc (conv-sym convA) (wtsub'_lift_raw i)
      wcs_lift    = liftSub-WtConvSub wtsub wcs wfH d1
      wfH_ext     = wf-extend htA_loc
      convB       = subst-ConvTm-cross d2 wtsub_lift wtsub'_lift wcs_lift wfH_ext

      buildEdgeCrossBB' : PiEdgeEqTy2 H sA sB sB' b f0
      buildEdgeCrossBB' u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            evU'     = mkSigma tt (LeCode-refl UCode tt)
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext   = ValidSub2-extend sigma P rho u0 vs hyp0
            valP'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valP
            hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext'  = ValidSub2-extend sigma' P rho u0 vs' hyp0'
            hyp0_eq  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         Val2-to-EqVal2 u' a_arg
                           (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a)
            vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs hyp0_eq
            wtsub_ext  = extSub-WtSub wtsub wfH d1 htP
            htP'       = ty-conv htP convA htA'_loc
            wtsub_ext' = extSub-WtSub wtsub' wfH d1 htP'
            wcs_ext  = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
            raw      = adequacyConvSub2 d2 (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                         crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                         v0 evB_u0_v0 UCode evU' fm_v0_U
            eq_B1    = S.Eq-sym (substExpr-comp sigma B P)
            eq_B2    = S.Eq-sym (substExpr-comp sigma' B P)
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB P) T U v0 UCode) eq_B2
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) B) U v0 UCode) eq_B1 raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      htB_loc  = subst-HasType wtsub_lift wfH_ext d2
      wfH_ext'    = wf-extend htA'_loc
      htB'_loc_raw = subst-HasType wtsub'_lift_raw wfH_ext' d2
      htPiM    = ty-Pi htA_loc htB_loc
      htPiN    = ty-Pi htA'_loc htB'_loc_raw

      eqValTyPi : REqValTyPi H (Pi sA sB) (Pi sA' sB') b f0
      eqValTyPi = record
        { domA   = sA
        ; codB   = sB
        ; domA'  = sA'
        ; codB'  = sB'
        ; redM   = mkRed3 headred-refl (conv-refl htPiM)
        ; redN   = mkRed3 headred-refl (conv-refl htPiN)
        ; cohF   = cf
        ; fmAllU = allU
        ; convA  = convA
        ; convB  = convB
        ; eqA    = eqValTyAA'
        ; edgeET = buildEdgeCrossBB'
        }


  adequacyConvSub2 {H = H} (ty-Pi-Prop {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-at-Prop-PP u a hu (snd evA) fm
    where
      adequacyConvSub2-at-Prop-PP : (u0 a0 : FinEl) -> EvalRel (Pi A B) rho u0 -> LeCode a0 PropCode -> FinMem u0 a0 ->
        EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) (Pi (substExpr sigma' A) (substExpr (liftSub sigma') B)) Prop u0 a0
      adequacyConvSub2-at-Prop-PP u0 Bot _ _ fm0 = tt
      adequacyConvSub2-at-Prop-PP u0 UCode _ () _
      adequacyConvSub2-at-Prop-PP Bot PropCode _ _ fm0 = tt
      adequacyConvSub2-at-Prop-PP UCode PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP PropCode PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (FunEl _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (SigmaCode _ _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (PairCode _ _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (PiCode a' f') PropCode hu' _ fm0 =
        let atU = adequacyConvSub2 (ty-Pi d1 (ty-Prop-U d2)) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu' UCode
                    (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode a' f') fm0)
            vtProp = mkRed3 headred-refl (conv-refl (ty-Prop wfH))
        in mkSigma vtProp (snd atU)
      adequacyConvSub2-at-Prop-PP u0 (FunEl _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (PiCode _ _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (SigmaCode _ _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (PairCode _ _) _ () _

  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu UCode evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu PropCode evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (PiCode b f0) evA fm =
    mkSigma valTyPi (mkSigma rvalPiL (mkSigma rvalPiR reqvalPi))
    where
      sA = substExpr sigma A ; sA' = substExpr sigma' A
      sB = substExpr (liftSub sigma) B ; sB' = substExpr (liftSub sigma') B
      sM0 = substExpr (liftSub sigma) M ; sM'0 = substExpr (liftSub sigma') M
      fmg = fst fm ; cg = fst (snd fm) ; pU = snd (snd fm)
      bU = fst pU ; allU = fst (snd pU) ; cf0 = snd (snd pU)
      cb = coh-from-aU b bU ; evU0 = mkSigma tt (LeCode-refl UCode tt)
      htA0 = subst-HasType wtsub wfH d1 ; htA'0 = subst-HasType wtsub' wfH d1
      htB0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d2
      htB'0 = subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2
      htM0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d3
      htM'0 = subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d3
      convA0 = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      a_lam = fst hu ; bodyLam = snd (snd (snd (snd hu)))
      evAb = fst (snd evA)
      -- Left Val2 (opaque)
      leftVal2 = adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
      valTyPi = fst leftVal2 ; rvalPiL = snd leftVal2
      -- Right Val2 — type-transport from (Pi sA' sB') to (Pi sA sB)
      rightVal2' = adequacySub2 (ty-Lam d1 d2 d3) sigma' rho crho vs' fits wtsub' wfH (FunEl g0) hu (PiCode b f0) evA fm
      eqPi_raw = adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) evA UCode evU0 pU
      eqTyPi = EqVal2-U-to-EqValTy2 (PiCode b f0) pU eqPi_raw
      eqTyPi_sym = EqValTy2-sym (PiCode b f0) (coh-from-aU (PiCode b f0) pU) eqTyPi
      rightVal2 = Val2-type-transport (FunEl g0) (PiCode b f0) eqTyPi_sym rightVal2'
      rvalPiR = snd rightVal2
      -- REqValPi: appEV from Remarks argument
      buildAppEV : PiAppEqVal2 H (Lam sA sM0) (Lam sA' sM'0) sA sB b f0 g0
      buildAppEV u' v' sel P htP valP =
        let ctg = cft-from-cf g0 cg ; cu' = Coherent-Selection sel ctg
            fm_u'_b = FinMem-Selection b f0 sel fmg ctg cb bU
            fm_v'_ef = FinMem-Selection-codomain b f0 sel fmg ctg cf0 allU
            w = bodyLam u' v' sel ; x = fst w ; le_x_u' = fst (snd w)
            fm_x_al = fst (snd (snd w)) ; evM_x_v' = snd (snd (snd w))
            cx = FinMem-coh-u x a_lam fm_x_al
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
            evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
            evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
            fits' = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
            crho' = mkSigma crho cu'
            -- Extended subs for sigma at P
            hyp0_s = \ u'' cu'' le a1 evA1 fm1 -> transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1
            vs_ext = ValidSub2-extend sigma P rho u' vs hyp0_s
            wtsub_ext = extSub-WtSub wtsub wfH d1 htP
            -- Extended subs for sigma' at P (need Val2 H P sA' u' b)
            eqA_domA = EqVal2-U-to-EqValTy2 b bU (adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evU0 bU)
            valP' = Val2-EqValTy2-fwd u' b cb eqA_domA valP
            hyp0_s' = \ u'' cu'' le a1 evA1 fm1 -> transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u' fm_u'_b P valP' u'' cu'' le a1 evA1 fm1
            vs'_ext = ValidSub2-extend sigma' P rho u' vs' hyp0_s'
            htP' = ty-conv htP convA0 htA'0
            wtsub'_ext = extSub-WtSub wtsub' wfH d1 htP'
            -- Extended conv subs
            hyp0_conv = \ u'' cu'' le a1 evA1 fm1 -> Val2-to-EqVal2 u'' a1 (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b P valP u'' cu'' le a1 evA1 fm1)
            vcs_ext = ValidConvSub2-extend sigma sigma' P P rho u' vcs hyp0_conv
            wcs_ext = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
            -- IH on body
            ihM_raw = adequacyConvSub2 d3 (extSub sigma P) (extSub sigma' P) (extendEnv rho u')
                        crho' vs_ext vs'_ext vcs_ext fits' wtsub_ext wtsub'_ext wcs_ext wfH
                        v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M = S.Eq-sym (substExpr-comp sigma M P) ; eq_M' = S.Eq-sym (substExpr-comp sigma' M P)
            eq_B = S.Eq-sym (substExpr-comp sigma B P) ; eq_B' = S.Eq-sym (substExpr-comp sigma' B P)
            ihM = S.Eq-transport (\ T -> EqVal2 H (subst1 sM0 P) T (subst1 sB P) v' (EvalFun f0 u')) eq_M'
                    (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) M) (subst1 sB P) v' (EvalFun f0 u')) eq_M
                      (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u')) eq_B ihM_raw))
            -- Type ConvTm for right beta
            convBP_raw = subst-ConvTm-cross d2 wtsub_ext wtsub'_ext wcs_ext wfH
            convBP = S.Eq-transport (\ T -> ConvTm H (subst1 sB P) T U) eq_B'
                       (S.Eq-transport (\ T -> ConvTm H T (substExpr (extSub sigma' P) B) U) eq_B convBP_raw)
            -- Beta-expand both sides
            cv_left = conv-beta htA0 htB0 htM0 htP
            cv_right' = conv-beta htA'0 htB'0 htM'0 htP'
            htBP = typing-type (snd (typing-ConvTm cv_left))
            cv_right = conv-conv cv_right' (conv-sym convBP) htBP
        in EqVal2-headred-expand v' (EvalFun f0 u')
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
             cv_left cv_right ihM
      reqvalPi : REqValPi H (Lam sA sM0) (Lam sA' sM'0) (Pi sA sB) g0 b f0
      reqvalPi = record { domA0 = sA ; codB0 = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA0 htB0))
        ; cohG = cg ; fmG = fmg ; appEV = buildAppEV }
  -- ty-App: decompose into function variation + argument variation + EqVal2-trans
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu Bot evA ()
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      UCode (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu Bot evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (PiCode _ _) evA ()
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b0pc f0pc) hu PropCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) PropCode evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu Bot evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu Bot evA fm = tt
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      PropCode (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu Bot evA fm = tt
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b0sc f0sc) hu UCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (SigmaCode b0sc f0sc) (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu Bot evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (SigmaCode b' f') evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (PairCode u' v') (fst hu) (fst (snd hu)) (snd (snd hu)) (SigmaCode b' f') evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b0pc f0pc) hu UCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl gfe) hu (PiCode bacfe facfe) evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (FunEl gfe) (fst hu) (fst (snd hu)) (snd (snd hu)) (PiCode bacfe facfe) evA fm

  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu PropCode evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Sigma {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu UCode evA fm =
    mkSigma (fst valTySig_s) (mkSigma (snd valTySig_s) (mkSigma (snd valTySig_s') (mkSigma (snd valTySig_s) (mkSigma (snd valTySig_s') eqValTySigma))))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)

      valTySig_s  = adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f0 hu evA fm
      valTySig_s' = adequacySub2-Sigma d1 d2 sigma' rho crho vs' fits wtsub' wfH b f0 hu evA fm

      eqD1 = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evUU bU
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

      htA_loc  = subst-HasType wtsub wfH d1
      htA'_loc = subst-HasType wtsub' wfH d1
      convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      wtsub_lift  = liftSub-WtSub wtsub wfH d1
      wtsub'_lift_raw = liftSub-WtSub wtsub' wfH d1
      wtsub'_lift : WtSub (extend H sA) (extend G A) (liftSub sigma')
      wtsub'_lift = \ i -> ctx-conv-HasType htA'_loc htA_loc (conv-sym convA) (wtsub'_lift_raw i)
      wcs_lift    = liftSub-WtConvSub wtsub wcs wfH d1
      wfH_ext     = wf-extend htA_loc
      convB       = subst-ConvTm-cross d2 wtsub_lift wtsub'_lift wcs_lift wfH_ext

      buildEdgeCrossBB' : SigmaEdgeEqTy2 H sA sB sB' b f0
      buildEdgeCrossBB' u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = snd (snd (snd (snd hu))) u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            evU'     = mkSigma tt (LeCode-refl UCode tt)
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext   = ValidSub2-extend sigma P rho u0 vs hyp0
            valP'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valP
            hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext'  = ValidSub2-extend sigma' P rho u0 vs' hyp0'
            hyp0_eq  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         Val2-to-EqVal2 u' a_arg
                           (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a)
            vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs hyp0_eq
            wtsub_ext  = extSub-WtSub wtsub wfH d1 htP
            htP'       = ty-conv htP convA htA'_loc
            wtsub_ext' = extSub-WtSub wtsub' wfH d1 htP'
            wcs_ext  = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
            raw      = adequacyConvSub2 d2 (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                         crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                         v0 evB_u0_v0 UCode evU' fm_v0_U
            eq_B1    = S.Eq-sym (substExpr-comp sigma B P)
            eq_B2    = S.Eq-sym (substExpr-comp sigma' B P)
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB P) T U v0 UCode) eq_B2
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) B) U v0 UCode) eq_B1 raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      htB_loc  = subst-HasType wtsub_lift wfH_ext d2
      wfH_ext'    = wf-extend htA'_loc
      htB'_loc_raw = subst-HasType wtsub'_lift_raw wfH_ext' d2
      htSigM    = ty-Sigma htA_loc htB_loc
      htSigN    = ty-Sigma htA'_loc htB'_loc_raw

      eqValTySigma : REqValTySigma H (SigmaE sA sB) (SigmaE sA' sB') b f0
      eqValTySigma = record
        { domA   = sA
        ; codB   = sB
        ; domA'  = sA'
        ; codB'  = sB'
        ; redM   = mkRed3 headred-refl (conv-refl htSigM)
        ; redN   = mkRed3 headred-refl (conv-refl htSigN)
        ; cohF   = cf
        ; fmAllU = allU
        ; convA  = convA
        ; convB  = convB
        ; eqA    = eqValTyAA'
        ; edgeET = buildEdgeCrossBB'
        }
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu Bot evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu UCode evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu PropCode evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 {H = H} (ty-MkPair {A = A} {B = B} {M = M0} {N = N0} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (SigmaCode b0s f0s) evA fm =
    let evU0 = mkSigma tt (LeCode-refl UCode tt)
        pSigU = snd (snd fm)
        sA = substExpr sigma A ; sA' = substExpr sigma' A
        sB = substExpr (liftSub sigma) B
        sM' = substExpr sigma' M0 ; sN' = substExpr sigma' N0
        htA0 = subst-HasType wtsub wfH d1 ; htA'0 = subst-HasType wtsub' wfH d1
        htB0 = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend htA0) d2
        htM'0s = subst-HasType wtsub' wfH d3
        convA0 = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
        htM'0_sA = ty-conv htM'0s (conv-sym convA0) htA0
        convMM' = subst-ConvTm-cross d3 wtsub wtsub' wcs wfH
        -- Left Val2
        leftVal2 = adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH
                     (PairCode u' v') hu (SigmaCode b0s f0s) evA fm
        -- Right Val2 with type-transport
        rightVal2' = adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma' rho crho vs' fits wtsub' wfH
                       (PairCode u' v') hu (SigmaCode b0s f0s) evA fm
        eqTySig = EqVal2-U-to-EqValTy2 (SigmaCode b0s f0s) pSigU
                    (adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                      (SigmaCode b0s f0s) evA UCode evU0 pSigU)
        rightVal2 = Val2-type-transport (PairCode u' v') (SigmaCode b0s f0s)
                      (EqValTy2-sym (SigmaCode b0s f0s) (coh-from-aU (SigmaCode b0s f0s) pSigU) eqTySig)
                      rightVal2'
        -- htFstR: HasType H (Fst (MkPair sM' sN')) sA
        htSig0 = ty-Sigma htA0 htB0
        htFstR = ty-Fst htA0 htB0 (ty-conv
                   (ty-MkPair htA'0 (subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2) htM'0s
                     (S.Eq-transport (HasType _ sN') (S.Eq-sym (subst-subst1-comm sigma' B M0)) (subst-HasType wtsub' wfH d4)))
                   (conv-sym (subst-ConvTm-cross (ty-Sigma d1 d2) wtsub wtsub' wcs wfH)) htSig0)
        -- cvSndR: ConvTm H (Snd (MkPair sM' sN')) sN' (subst1 sB (Fst (MkPair sM' sN')))
        htN0s = S.Eq-transport (HasType _ (substExpr sigma N0)) (S.Eq-sym (subst-subst1-comm sigma B M0)) (subst-HasType wtsub wfH d4)
        convBMM' = subst1-cong-ConvTm htA0 htB0 (subst-HasType wtsub wfH d3) htM'0_sA convMM'
        htBsM' = snd (typing-ConvTm convBMM')
        cvNN' = S.Eq-transport (\ T -> ConvTm H (substExpr sigma N0) (substExpr sigma' N0) T) (S.Eq-sym (subst-subst1-comm sigma B M0))
                  (subst-ConvTm-cross d4 wtsub wtsub' wcs wfH)
        htN'_sBsM'2 = ty-conv (snd (typing-ConvTm cvNN')) convBMM' htBsM'
        cv-fst-R' = conv-beta-fst htA'0 (subst-HasType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA'0) d2) htM'0s
                      (S.Eq-transport (HasType _ sN') (S.Eq-sym (subst-subst1-comm sigma' B M0)) (subst-HasType wtsub' wfH d4))
        cv-fst-R = conv-conv cv-fst-R' (conv-sym convA0) htA0
        cvM'_FstR = conv-sym cv-fst-R
        convBFstR = subst1-cong-ConvTm htA0 htB0 htM'0_sA htFstR cvM'_FstR
        cvSndR = conv-conv (conv-beta-snd htA0 htB0 htM'0_sA htN'_sBsM'2)
                   convBFstR (snd (typing-ConvTm convBFstR))
    in tyMkPair-conv-case d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
         u' v' hu b0s f0s evA fm leftVal2 rightVal2
         (\ {M0} {A0} d u ev a evA' fm' -> adequacyConvSub2 {H = H} {M = M0} {A = A0} d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u ev a evA' fm')
         (getSigmaEdgeEq d1 d2 sigma rho crho vs fits wtsub wfH b0s f0s evA pSigU)
         htFstR cvSndR
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  adequacyConvSub2 (ty-Fst dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-Fst-Snd (ty-Fst dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

  adequacyConvSub2 (ty-Snd dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-Fst-Snd (ty-Snd dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

  -- adequacyConvSub2-Fst-Snd: cross-sub helper for Fst/Snd
  -- Uses adequacySub2 from both sigma sides and type equality from adequacyConvSub2 on the type
  adequacyConvSub2-Fst-Snd : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu PropCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (SigmaCode _ _) evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (SigmaCode _ _) evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu UCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a0 f0) hu UCode evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a0 f0) hu UCode evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode a0 f0) hu UCode evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode a0 f0) hu UCode evA fm
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b f) evA fm =
    adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b f) evA fm

  -- Pipe operator for theorem1 result
  _|>_ : {A B : Set} -> A -> (A -> B) -> B
  x |> f = f x

------------------------------------------------------------------------
-- Part 8: Closed-term corollary
------------------------------------------------------------------------

adequacy2 : {M A : Expr zero} ->
  HasType empty M A ->
  (rho : EnvApprox zero) ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val2 empty M A u a
adequacy2 {M} {A} d emptyEnv u hu a evA fm =
  let wfEmpty = typing-WfCtx d
      wsId    = idSub-WtSub wfEmpty
  in Val2-transport-M {u = u} {a = a} (substExpr-id M)
       (Val2-transport-A {u = u} {a = a} (substExpr-id A)
         (adequacySub2 d idSub emptyEnv tt (ValidSub2-empty idSub emptyEnv) tt wsId wfEmpty u hu a evA fm))
