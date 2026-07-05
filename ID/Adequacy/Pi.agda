{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyPi.agda  (MIN/ — PROTOTYPE)
--
-- Prototype of the "one combinator per typing rule" refactor of the
-- adequacy fundamental lemma, on the ty-Pi rule.
--
-- The combinator `adequacy-ty-Pi` is NON-RECURSIVE: it takes the
-- induction hypotheses for the premises (the FULLY GENERAL adequacy
-- statements for the domain d1 and codomain d2) as explicit parameters,
-- and produces the property for the conclusion.  Because it never calls
-- adequacy* itself, it is structural.  The driver (the
-- mutual block in Adequacy) would dispatch:
--
--   adequacySub2 (ty-Pi d1 d2) sigma rho ... =
--     adequacy-ty-Pi d1 d2 (adequacySub2 d1) (adequacySub2 d2)
--                          (adequacyConvSub2 d2) sigma rho ...
--
-- where `adequacySub2 d1`, `adequacySub2 d2`, `adequacyConvSub2 d2` are
-- the curried recursive calls on the structural sub-derivations d1, d2.
--
-- This file is self-contained (it re-derives the few non-recursive
-- helpers it needs) so the prototype does not disturb Adequacy.agda.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.Pi where

open import ID.Adequacy.HeadRed

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; Comp ;
  Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ;
  FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ;
  coh-from-aU ; FinMem-coh-u ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ;
  CoherentEnv ; EvalRel-Comp ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; subst1 ; Sub ; liftSub ; substExpr)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-U ; ty-Pi ; conv-refl)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; liftSub-WtSub)
open import ID.Model.EvalSubstitution using (EvalRel-unwk ; EvalRel-Pi-body)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Syntax.Reduction using (headred-refl)
open import ID.Model.Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode)

------------------------------------------------------------------------
-- The fully general adequacy statements (the IH shapes).
------------------------------------------------------------------------

-- soundness statement for a HasType derivation G |- M : A
Adq : {g : Nat} (G : Ctx g) (M A : Expr g) -> Set
Adq {g} G M A =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val2 H (substExpr sigma M) (substExpr sigma A) u a

-- two-substitution (conversion) statement for G |- M : A
AdqConv : {g : Nat} (G : Ctx g) (M A : Expr g) -> Set
AdqConv {g} G M A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a

------------------------------------------------------------------------
-- Non-recursive helpers (copied from Adequacy; they use only the public
-- property lemmas, so they carry no recursion).  In the real refactor
-- these live in a shared base module.
------------------------------------------------------------------------

sup-transport-Val2 : {n : Nat} {H : Ctx n} {N A : Expr n}
  (b a_arg : FinEl) -> Comp b a_arg -> FinMem b UCode -> FinMem a_arg UCode ->
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
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      val2     = restrictVal2 H N A u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u_sup val1
      val3     = downVal2 H N A u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
  in val3

sup-transport-EqVal2 : {n : Nat} {H : Ctx n} {N1 N2 A : Expr n}
  (b a_arg : FinEl) -> Comp b a_arg -> FinMem b UCode -> FinMem a_arg UCode ->
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
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      eq2      = restrictEqVal2 H N1 N2 A u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u_sup eq1
      eq3      = downEqVal2 H N1 N2 A u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU eq2
  in eq3

Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
  (u : FinEl) -> FinMem u UCode -> Val2 G M U u UCode -> ValTy2 G M u
Val2-U-to-ValTy2 Bot _ _ = tt
Val2-U-to-ValTy2 UCode _ v = snd v
Val2-U-to-ValTy2 (PiCode _ _) _ v = snd v
Val2-U-to-ValTy2 (IdCode _ _ _) _ v = snd v
Val2-U-to-ValTy2 (FunEl _) () _

EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N : Expr n}
  (u : FinEl) -> FinMem u UCode -> EqVal2 G M N U u UCode -> EqValTy2 G M N u
EqVal2-U-to-EqValTy2 Bot _ _ = tt
EqVal2-U-to-EqValTy2 UCode _ ev = snd (snd (snd ev))
EqVal2-U-to-EqValTy2 (PiCode _ _) _ ev = snd (snd (snd ev))
EqVal2-U-to-EqValTy2 (IdCode _ _ _) _ ev = snd (snd (snd ev))
EqVal2-U-to-EqValTy2 (FunEl _) () _

------------------------------------------------------------------------
-- transport along Sup, parameterized by the DOMAIN IH (replaces the
-- `adequacySub2 d1` calls in the original transportVal2/transportEqVal2).
------------------------------------------------------------------------

transportVal2' : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) -> FinMem b UCode -> EvalRel A rho b ->
  (u0 : FinEl) -> FinMem u0 b ->
  (N : Expr h) -> Val2 H N (substExpr sigma A) u0 b ->
  (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
  (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
  Val2 H N (substExpr sigma A) u' a_arg
transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
  let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
      a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
      evU      = mkSigma tt (LeCode-refl UCode tt)
      vtA_b    = Val2-U-to-ValTy2 b bU (IH-A sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
      vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (IH-A sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
  in sup-transport-Val2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN

transportEqVal2' : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {N1 N2 : Expr h} ->
  Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) -> FinMem b UCode -> EvalRel A rho b ->
  (u0 : FinEl) -> FinMem u0 b ->
  EqVal2 H N1 N2 (substExpr sigma A) u0 b ->
  (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
  (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
  EqVal2 H N1 N2 (substExpr sigma A) u' a_arg
transportEqVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
  let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
      a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
      evU      = mkSigma tt (LeCode-refl UCode tt)
      vtA_b    = Val2-U-to-ValTy2 b bU (IH-A sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
      vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (IH-A sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
  in sup-transport-EqVal2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN

------------------------------------------------------------------------
-- The ty-Pi combinator.  NON-RECURSIVE: domain IH = IH-A, codomain IHs
-- = IH-B (Val) and IH-Bc (conversion).  Note IH-B is used INSIDE the
-- edge realizers (buildEdgeVal / buildEdgeEq) at an EXTENDED substitution
-- `extSub sigma N` and environment `extendEnv rho u0` — which is exactly
-- why the IH must be the fully general (quantified) statement.
------------------------------------------------------------------------

adequacy-ty-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  Adq G A U -> Adq (extend G A) B U -> AdqConv (extend G A) B U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) ->
  EvalRel U rho UCode ->
  FinMem (PiCode b f) UCode ->
  Val2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) U (PiCode b f) UCode
adequacy-ty-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH b f hu evA fm =
  mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (mk-ValTyPi (record
    { domA = sA ; codB = sB
    ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA htB))
    ; cohF = cf ; fmAllU = allU ; htA = htA ; htB = htB ; valA = valTyA
    ; edgeV = buildEdgeVal ; edgeE = buildEdgeEq }))
  where
    sA    = substExpr sigma A
    sB    = substExpr (liftSub sigma) B
    bU    = finMem-piU-dom b f fm
    allU  = finMem-piU-allU b f fm
    cf    = finMem-piU-cft b f fm
    cb    = coh-from-aU b bU
    evAb  = fst (snd hu)
    htA   = subst-HasType wtsub wfH d1
    htB   = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend (subst-HasType wtsub wfH d1)) d2
    valTyA = Val2-U-to-ValTy2 b bU
               (IH-A sigma rho crho vs fits wtsub wfH b evAb UCode (mkSigma tt (LeCode-refl UCode tt)) bU)

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
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH d1 htN
          evU      = mkSigma tt (LeCode-refl UCode tt)
          ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                       (IH-B (extSub sigma N) (extendEnv rho u0) crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evU fm_v0_U)
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
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          evU      = mkSigma tt (LeCode-refl UCode tt)
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
          vtN1     = Val2-U-to-ValTy2 v0 fm_v0_U
                       (IH-B (extSub sigma N1) (extendEnv rho u0) crho' vs'_N1 fits' wtsub'_N1 wfH v0 evB_u0_v0 UCode evU fm_v0_U)
          vtN1'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N1)) vtN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
          raw      = IH-Bc (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB_u0_v0 UCode evU fm_v0_U
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'
