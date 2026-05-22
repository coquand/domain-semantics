{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyApp.agda  (MIN/ -- PROTOTYPE)
--
-- Standalone value-only CROSS combinator for the ty-App rule, factored
-- out of Adequacy.agda's mutual block.
--
--   adequacyV-ty-App : the two-substitution (cross) EqVal2 of  App f a
--                      : subst1 B a   (port of  adequacyConvSub2 (ty-App ...)).
--
-- The heavy lifting already lives in AdequacyCases.adequacyConvSub2-App-core-body,
-- which is ALREADY parameterised by the adequacy recursors (adSub2 single /
-- adConvSub2 cross) -- and inside it every recursor call is on a SUBTERM
-- (d1=A, d2=B, d3=f, d4=a), so no constructed-derivation recursion occurs.
-- This file just supplies the App's value/argument evaluation dispatch and
-- threads the recursors + the two transport helpers.  No postulate.
------------------------------------------------------------------------

module MIN.AdequacyApp where

open import MIN.AdequacyHeadRed
open import MIN.AdequacyCases using (adequacyConvSub2-App-core-body ; adequacySub2-App-core-body)
open import MIN.AdequacyPi using (Adq ; AdqConv ; Val2-U-to-ValTy2)

import MIN.Basic as S
open S using (Nat ; zero ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ;
  FinFun ; List ; nil ; cons)
open import MIN.PaperSemantics using (LeCode ; Coherent ; coh-from-aU ; FinMem ; FinMem-coh-u ;
  Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ;
  finMemUCode-Sup ; finMem-upward)
open import MIN.RawSemantics using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-coh ; EvalRel-mon-env ; EvalRel-down ; EnvLe-refl)
open import MIN.RawSyntax using (Expr ; U ; App ; Pi ; subst1 ; Sub ; liftSub ; substExpr)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; WfCtx)
open import MIN.SubstitutionLemma using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm-cross)
open import MIN.LemmaForTS using (Fits)
open import MIN.TypingSemantics using (theorem1)
open import MIN.EvalSubstitution using (EvalRel-subst1-forward)
open import MIN.Reduction using (subst-subst1-comm)

------------------------------------------------------------------------
-- app-transport-EqVal2 : the Sup-transport along the App codomain.  Copy of
-- Adequacy.agda's top-level helper (uses only the public property lemmas).
------------------------------------------------------------------------

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
      eq_res   = restrictEqVal2 H M1 M2 A v_sel u1 (Sup ac1 ef_usel)
                   le_u1_vsel fm_u1_sup fm_vsel_sup eq_up
      eq_down  = downEqVal2 H M1 M2 A u1
                   ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U eq_res
  in eq_down

------------------------------------------------------------------------
-- The recursor parameter types (the FULL single-sub / cross adequacy
-- functions, as consumed by adequacyConvSub2-App-core-body).
------------------------------------------------------------------------

AdSub2Rec : {h : Nat} -> Ctx h -> Set
AdSub2Rec {h} H =
  {g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (sigma0 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 -> ValidSub2 H G1 sigma0 rho0 -> Fits G1 rho0 ->
    WtSub H G1 sigma0 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    Val2 H (substExpr sigma0 M0) (substExpr sigma0 A0) u a0

AdConvSub2Rec : {h : Nat} -> Ctx h -> Set
AdConvSub2Rec {h} H =
  {g1 : Nat} {G1 : Ctx g1} {M0 A0 : Expr g1} -> HasType G1 M0 A0 ->
    (s1 s2 : Sub h g1) -> (rho0 : EnvApprox g1) ->
    CoherentEnv rho0 ->
    ValidSub2 H G1 s1 rho0 -> ValidSub2 H G1 s2 rho0 ->
    ValidConvSub2 H G1 s1 s2 rho0 ->
    Fits G1 rho0 ->
    WtSub H G1 s1 -> WtSub H G1 s2 ->
    WtConvSub H G1 s1 s2 -> WfCtx H ->
    (u : FinEl) -> EvalRel M0 rho0 u ->
    (a0 : FinEl) -> EvalRel A0 rho0 a0 -> FinMem u a0 ->
    EqVal2 H (substExpr s1 M0) (substExpr s2 M0) (substExpr s1 A0) u a0

------------------------------------------------------------------------
-- adequacyV-ty-App : value-only cross EqVal2 of App f a : subst1 B a.
-- Port of  adequacyConvSub2 (ty-App dA dB df da)  dispatch.
------------------------------------------------------------------------

adequacyV-ty-App : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType G f (Pi A B) -> HasType G a A ->
  Adq G a A -> Adq (extend G A) B U -> AdqConv G f (Pi A B) -> AdqConv G a A ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (App f a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (App f a)) (substExpr sigma' (App f a)) (substExpr sigma (subst1 B a)) u ac
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
  EqVal2-Bot a
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu Bot evA ()
adequacyV-ty-App {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
  adequacyConvSub2-App-core-body {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    UCode (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
    IHav IHBv IHfc IHac Val2-U-to-ValTy2 app-transport-EqVal2
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (FunEl _) evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (PiCode _ _) evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu Bot evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (FunEl _) evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (PiCode _ _) evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu Bot evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA ()
adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (FunEl _) evA ()
adequacyV-ty-App {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b0pc f0pc) hu UCode evA fm =
  adequacyConvSub2-App-core-body {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
    IHav IHBv IHfc IHac Val2-U-to-ValTy2 app-transport-EqVal2
adequacyV-ty-App {H = H} {A = A} {B = B} {f = f0} {a = a} dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl gfe) hu (PiCode bacfe facfe) evA fm =
  adequacyConvSub2-App-core-body {H = H} {A = A} {B = B} {f = f0} {a = a}
    dA dB df da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    (FunEl gfe) (fst hu) (fst (snd hu)) (snd (snd hu)) (PiCode bacfe facfe) evA fm
    IHav IHBv IHfc IHac Val2-U-to-ValTy2 app-transport-EqVal2

------------------------------------------------------------------------
-- adequacyV-subst1-cod : the MIN analogue of popl18 Lemma 3.20 (Single
-- Substitution), the equality / two-substitution part (3.20(2)):
--   Γ,A ⊨ B : U   and   Γ ⊨ a : A   ⟹   Γ ⊨ B[a] : U   (as a CROSS validity).
-- This is what the application case of the fundamental theorem needs to give
-- the substituted codomain type its validity, WITHOUT recursing on a
-- constructed derivation: it is a separate lemma, built by applying the
-- codomain's cross IH (on the SUBTERM dB) at the substitution EXTENDED by the
-- argument's value -- precisely the paper's "apply (σ, t[σ])" construction.
-- Structural in dB, da; takes the (H-polymorphic) recursors as parameters.
------------------------------------------------------------------------

adequacyV-subst1-cod : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G a A ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdConvSub2Rec H2) ->
  AdqConv G (subst1 B a) U
adequacyV-subst1-cod {G = G} {A = A} {B = B} {a = a} dA dB da adSub2 adConvSub2
    {H = H} sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu ac evU fm =
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
      in adSub2 da sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
    vs_ext = ValidSub2-extend sigma sa rho v_fwd' vs hyp_s
    hyp_s' = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
      in adSub2 da sigma' rho crho vs' fits wtsub' wfH u' evA_u' a_arg evA_aarg fm_u'_a
    vs'_ext = ValidSub2-extend sigma' sa' rho v_fwd' vs' hyp_s'
    hyp_c = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
      let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
      in adConvSub2 da sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u' evA_u' a_arg evA_aarg fm_u'_a
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

------------------------------------------------------------------------
-- app-transport-Val2 : the single-sub Sup-transport along the App codomain
-- (copy of Adequacy.agda's top-level helper; uses only public lemmas).
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- adequacySub2-App : the single-sub value matrix dispatcher for ty-App,
-- factored from Adequacy.agda.  Dispatches on (u, ac), calling the
-- recursor-parameterised AdequacyCases.adequacySub2-App-core-body for the
-- informative cases.  Takes the single-sub recursor adSub2 as a parameter
-- (the App enlargement applies it at the SUBTERMS A/B/f/a, at varying
-- values) -- so the driver stays structural through call-graph composition.
------------------------------------------------------------------------

adequacySub2-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
  {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
  HasType G0 A U -> HasType (extend G0 A) B U ->
  HasType G0 f' (Pi A B) -> HasType G0 a A ->
  Adq G0 f' (Pi A B) -> Adq G0 a A -> Adq (extend G0 A) B U ->
  (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
  CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
  WtSub H G0 sigma -> WfCtx H ->
  (u : FinEl) -> Coherent u ->
  EvalRel (App f' a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u ac
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH UCode cu ev Bot evAc fm = tt
adequacySub2-App {H = H} dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH UCode cu ev UCode evAc fm =
  adequacySub2-App-core-body {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
    IHf IHa IHB Val2-U-to-ValTy2 app-transport-Val2
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH UCode cu ev (FunEl _) evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH UCode cu ev (PiCode _ _) evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev Bot evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (FunEl _) evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (PiCode _ _) evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (FunEl _) cu ev Bot evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (FunEl _) cu ev UCode evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (FunEl _) evAc ()
adequacySub2-App dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH Bot cu ev ac evAc fm = Val2-Bot ac
adequacySub2-App {H = H} dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1 ev1 UCode evAc1 fm1 =
  adequacySub2-App-core-body {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1
    (fst ev1) (fst (snd ev1)) (snd (snd ev1)) UCode evAc1 fm1
    IHf IHa IHB Val2-U-to-ValTy2 app-transport-Val2
adequacySub2-App {H = H} dA dB d1 d2 IHf IHa IHB sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1 ev1 (PiCode bacfe facfe) evAc1 fm1 =
  adequacySub2-App-core-body {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1
    (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (PiCode bacfe facfe) evAc1 fm1
    IHf IHa IHB Val2-U-to-ValTy2 app-transport-Val2
