{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyBeta.agda  (MIN/ -- PROTOTYPE)
--
-- Structural (pragma-free) combinator for the conv-beta computation rule.
--
--   adequacyEqSub2-beta : the single-sub conversion
--       App (Lam A M) a = subst1 M a : subst1 B a
--
-- KEY DESIGN (per the corrected math): conv-beta's premises are
--   d1:A:U, d2:B:U, d3:M:B, d4:a:A -- NONE of which is a derivation of the
-- redex  App (Lam A M) a.  The OLD version manufactured a derivation
--   ty-App d1 d2 (ty-Lam d1 d2 d3) d4
-- and recursed adequacySub2 on it -- a non-subterm, which is exactly why the
-- TERMINATING pragma was load-bearing.
--
-- Instead we state the obligation on the CONTRACTUM:  subst1 M a : subst1 B a
-- is adequate by the SINGLE-SUBSTITUTION lemma applied to d3 (M:B) and d4 (a:A)
-- -- both genuine subterms -- and the redex's value coincides with the
-- contractum's (beta is a head reduction), so the conversion is obtained by a
-- final beta head-EXPANSION of the diagonal.  No fabricated derivation; every
-- recursive call is on d3/d4 (via the IH VALUES IH-M / IH-a).  No pragma.
--
-- The single-substitution VALUE lemma is  adequacyV-subst1-term  below.  Its
-- only subtlety is the codomain: applying IH-M needs M and B evaluated at the
-- SAME extended environment.  We forward both  subst1 M a  (term) and
-- subst1 B a  (type), obtaining two approximations  v_u, v_B  of  a's value;
-- their common upper bound  w = Sup v_u v_B  (an evaluation of a, via
-- EvalRel-Sup) lets EvalRel-mon-env push both M and B up to  extendEnv rho w,
-- where IH-M applies directly.  (Standard popl18 single substitution: the value
-- of a redex is the value of its contractum.)
------------------------------------------------------------------------

module MIN.AdequacyBeta where
open import MIN.AdequacyHeadRed

open import MIN.AdequacyPi using (Adq)

import MIN.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl)
open import MIN.PaperSemantics using (FinMem ; Comp ; Sup ; Coherent-Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ; FinMem-coh-u)
open import MIN.RawSemantics using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-coh ; EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ; EvalRel-mon-env ; EnvLe-refl)
open import MIN.RawSyntax using (Expr ; U ; Pi ; Lam ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  conv-beta ; conv-refl)
open import MIN.Reduction using (HeadRed ; headred-step ; headred-beta ; headred-refl ; subst-subst1-comm)
open import MIN.SubstitutionLemma using (WtSub ; subst-HasType ; liftSub-WtSub ; typing-ConvTm)
open import MIN.TypingSemantics using (convSound ; theorem1)
open import MIN.EvalSubstitution using (EvalRel-subst1-forward)
open import MIN.LemmaForTS using (Fits)

------------------------------------------------------------------------
-- adequacyV-subst1-term : the term-level SINGLE-SUBSTITUTION value lemma
-- (popl18 Lemma 3.20 (Single Substitution), the VALUE part for a TERM at a
-- non-U codomain).  Builds  Val2 (subst1 M a : subst1 B a)  from the codomain
-- term's IH (IH-M = adequacySub2 d3) at the substitution extended by a's value,
-- plus the argument's IH (IH-a = adequacySub2 d4) for the extension's validity.
-- Structural in d1/d3/d4 (its callers pass IH VALUES, not recursors).
------------------------------------------------------------------------

adequacyV-subst1-term : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} {a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType (extend G A) M B -> HasType G a A ->
  Adq (extend G A) M B -> Adq G a A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (subst1 M a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  Val2 H (substExpr sigma (subst1 M a)) (substExpr sigma (subst1 B a)) u ac
adequacyV-subst1-term {H = H} {G = G} {A = A} {B = B} {M = M} {a = a0}
  dA dB dM da IH-M IH-a sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  r4
  where
    -- forward the contractum term  subst1 M a  at u
    fwdM     = EvalRel-subst1-forward M a0 rho u crho hu
    v_u      = fst fwdM
    evA_vu   = fst (snd fwdM)             -- EvalRel a rho v_u
    evM_vu   = snd (snd fwdM)             -- EvalRel M (extendEnv rho v_u) u
    -- forward the codomain type  subst1 B a  at ac
    fwdB     = EvalRel-subst1-forward B a0 rho ac crho evAc
    v_B      = fst fwdB
    evA_vB   = fst (snd fwdB)             -- EvalRel a rho v_B
    evB_vB   = snd (snd fwdB)             -- EvalRel B (extendEnv rho v_B) ac
    -- common upper bound  w = Sup v_u v_B  (an evaluation of a)
    cv_u     = EvalRel-coh a0 rho v_u evA_vu
    cv_B     = EvalRel-coh a0 rho v_B evA_vB
    comp_uB  = EvalRel-Comp a0 rho crho v_u v_B evA_vu evA_vB
    w        = Sup v_u v_B
    cw       = Coherent-Sup v_u v_B comp_uB cv_u cv_B
    evA_w    = EvalRel-Sup a0 rho v_u v_B crho cv_u cv_B comp_uB evA_vu evA_vB
    le_uw    = LeCode-Sup-left v_u v_B comp_uB cv_u cv_B
    le_Bw    = LeCode-Sup-right v_u v_B comp_uB cv_u cv_B
    -- typed enlargement of w (for the extended Fits / ValidSub2)
    typed_a  = theorem1 da rho fits w evA_w
    w'       = fst typed_a
    a_fit    = fst (snd typed_a)
    le_ww'   = fst (snd (snd typed_a))
    evA_w'   = fst (snd (snd (snd typed_a)))
    fm_w'    = fst (snd (snd (snd (snd typed_a))))
    evA_afit = snd (snd (snd (snd (snd typed_a))))
    cw'      = FinMem-coh-u w' a_fit fm_w'
    -- push M and B up to  extendEnv rho w'  (two mon-env steps each: v -> w -> w')
    envle_uw  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_u (mkSigma cw le_uw))
    evM_w     = EvalRel-mon-env M (extendEnv rho v_u) (extendEnv rho w) u evM_vu envle_uw
    envle_ww' = mkSigma (EnvLe-refl rho crho) (mkSigma cw (mkSigma cw' le_ww'))
    evM_w'    = EvalRel-mon-env M (extendEnv rho w) (extendEnv rho w') u evM_w envle_ww'
    envle_Bw  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_B (mkSigma cw le_Bw))
    evB_w     = EvalRel-mon-env B (extendEnv rho v_B) (extendEnv rho w) ac evB_vB envle_Bw
    evB_w'    = EvalRel-mon-env B (extendEnv rho w) (extendEnv rho w') ac evB_w envle_ww'
    -- extend the substitution by  a[sigma]  at semantic value  w'
    sa       = substExpr sigma a0
    sM       = substExpr (liftSub sigma) M
    sB       = substExpr (liftSub sigma) B
    crho_ext = mkSigma crho cw'
    fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_w' evA_afit))
    hyp_s    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
                 let evA_u' = EvalRel-down a0 rho w' u' crho cu' evA_w' le_u'
                 in IH-a sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
    vs_ext   = ValidSub2-extend sigma sa rho w' vs hyp_s
    htSa     = subst-HasType wtsub wfH da
    wtsub_ext = extSub-WtSub wtsub wfH dA htSa
    -- apply the codomain term's IH at the extended substitution / environment
    raw      = IH-M (extSub sigma sa) (extendEnv rho w')
                 crho_ext vs_ext fits_ext wtsub_ext wfH u evM_w' ac evB_w' fm
    -- transport  substExpr (extSub sigma sa) X  ->  substExpr sigma (subst1 X a)
    r1 = S.Eq-transport (\ T -> Val2 H T (substExpr (extSub sigma sa) B) u ac)
           (S.Eq-sym (substExpr-comp sigma M sa)) raw
    r2 = S.Eq-transport (\ T -> Val2 H (subst1 sM sa) T u ac)
           (S.Eq-sym (substExpr-comp sigma B sa)) r1
    r3 = S.Eq-transport (\ T -> Val2 H T (subst1 sB sa) u ac)
           (subst-subst1-comm sigma M a0) r2
    r4 = S.Eq-transport (\ T -> Val2 H (substExpr sigma (subst1 M a0)) T u ac)
           (subst-subst1-comm sigma B a0) r3

------------------------------------------------------------------------
-- adequacyEqSub2-beta : full single-sub conversion for the beta rule.  The
-- contractum's value (from adequacyV-subst1-term) is taken on the diagonal and
-- beta head-EXPANDED back into  App (Lam A M) a = subst1 M a.  Takes the
-- codomain/argument IH VALUES (IH-M = adequacySub2 d3, IH-a = adequacySub2 d4);
-- the redex's evaluation hu is transported to the contractum via convSound.
------------------------------------------------------------------------

adequacyEqSub2-beta : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} {a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U ->
  HasType (extend G A) M B -> HasType G a A ->
  Adq (extend G A) M B -> Adq G a A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (App (Lam A M) a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (App (Lam A M) a))
           (substExpr sigma (subst1 M a))
           (substExpr sigma (subst1 B a)) u ac
adequacyEqSub2-beta {H = H} {A = A} {B = B} {M = M} {a = a0}
  d1 d2 d3 d4 IH-M IH-a sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let hu_c     = convSound (conv-beta d1 d2 d3 d4) rho fits u hu
      val_subst = adequacyV-subst1-term d1 d2 d3 d4 IH-M IH-a
                    sigma rho crho vs fits wtsub wfH u hu_c ac evAc fm
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
      eqval_diag = Val2-to-EqVal2 u ac val_subst
      ht-subst   = snd (typing-ConvTm cv-beta)
  in EqVal2-headred-expand u ac beta-hr headred-refl cv-beta (conv-refl ht-subst) eqval_diag
