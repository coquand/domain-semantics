{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Adeq.Beta  (T_R version of MIN/Adequacy/Beta.agda)
--
--   Adq-subst1 : single substitution M[a] : B[a] is valid, from the
--                validity of M (at the substitution extended by a's
--                value) and of a;
--   AdqE1-beta : app(A,B,λ(A,B,M),a) = M[a] : B[a], by head expansion
--                of the contractum's validity.
--
-- No postulates.
------------------------------------------------------------------------

module ERT.Adeq.Beta where

open import ERT.Adeq.HeadRed
open import ERT.Adeq.Stmt

import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import ERT.Dom.Kernel using (LeCode ; Coherent ; Sup ; Coherent-Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ; FinMem ; FinMem-coh-u)
open import ERT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-coh ; EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ; EvalRel-mon-env ; EnvLe-refl)
open import ERT.Model.EvalSubstitution using (EvalRel-subst1-forward)
open import ERT.Model.SoundnessLemmas using (Fits)
open import ERT.Model.Strip using (strip ; stripCtx ; strip-subst1)
import ERT.Model.Core as C
open import ERT.RussellSyntax using (Expr ; U ; Pi ; Lam ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import ERT.RussellTyping
open import ERT.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  liftSub-WtSub ; subst-subst1 ; typing-ConvTm)
open import ERT.RussellReduction using (HeadRed ; headred-refl ; headred-step ; headred-beta)

private
  evS : {n : Nat} (M : Expr (suc n)) (a : Expr n) {rho : EnvApprox n} {u : FinEl} ->
    EvalRel (strip (subst1 M a)) rho u -> EvalRel (C.subst1 (strip M) (strip a)) rho u
  evS M a ev = S.Eq-transport (\ X -> EvalRel X _ _) (strip-subst1 M a) ev

------------------------------------------------------------------------
-- Single substitution
------------------------------------------------------------------------

Adq-subst1 : {g : Nat} {G : Ctx g} {A : Expr g} {B M : Expr (suc g)} {a : Expr g} ->
  IsType G A -> HasType G a A ->
  Adq (extend G A) M B -> Adq G a A ->
  Adq G (subst1 M a) (subst1 B a)
Adq-subst1 {G = G} {A = A} {B = B} {M = M} {a = a0}
  dA da IH-M IH-a {H = H} sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  r4
  where
    fwdM     = EvalRel-subst1-forward (strip M) (strip a0) rho u crho (evS M a0 hu)
    v_u      = fst fwdM
    evA_vu   = fst (snd fwdM)
    evM_vu   = snd (snd fwdM)
    fwdB     = EvalRel-subst1-forward (strip B) (strip a0) rho ac crho (evS B a0 evAc)
    v_B      = fst fwdB
    evA_vB   = fst (snd fwdB)
    evB_vB   = snd (snd fwdB)
    cv_u     = EvalRel-coh (strip a0) rho v_u evA_vu
    cv_B     = EvalRel-coh (strip a0) rho v_B evA_vB
    comp_uB  = EvalRel-Comp (strip a0) rho crho v_u v_B evA_vu evA_vB
    w        = Sup v_u v_B
    cw       = Coherent-Sup v_u v_B comp_uB cv_u cv_B
    evA_w    = EvalRel-Sup (strip a0) rho v_u v_B crho cv_u cv_B comp_uB evA_vu evA_vB
    le_uw    = LeCode-Sup-left v_u v_B comp_uB cv_u cv_B
    le_Bw    = LeCode-Sup-right v_u v_B comp_uB cv_u cv_B
    typed_a  = typedVal da rho fits w evA_w
    w'       = fst typed_a
    a_fit    = fst (snd typed_a)
    le_ww'   = fst (snd (snd typed_a))
    evA_w'   = fst (snd (snd (snd typed_a)))
    fm_w'    = fst (snd (snd (snd (snd typed_a))))
    evA_afit = snd (snd (snd (snd (snd typed_a))))
    cw'      = FinMem-coh-u w' a_fit fm_w'
    envle_uw  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_u (mkSigma cw le_uw))
    evM_w     = EvalRel-mon-env (strip M) (extendEnv rho v_u) (extendEnv rho w) u evM_vu envle_uw
    envle_ww' = mkSigma (EnvLe-refl rho crho) (mkSigma cw (mkSigma cw' le_ww'))
    evM_w'    = EvalRel-mon-env (strip M) (extendEnv rho w) (extendEnv rho w') u evM_w envle_ww'
    envle_Bw  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_B (mkSigma cw le_Bw))
    evB_w     = EvalRel-mon-env (strip B) (extendEnv rho v_B) (extendEnv rho w) ac evB_vB envle_Bw
    evB_w'    = EvalRel-mon-env (strip B) (extendEnv rho w) (extendEnv rho w') ac evB_w envle_ww'
    sa       = substExpr sigma a0
    sM       = substExpr (liftSub sigma) M
    sB       = substExpr (liftSub sigma) B
    crho_ext = mkSigma crho cw'
    fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_w' evA_afit))
    hyp_s    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
                 let evA_u' = EvalRel-down (strip a0) rho w' u' crho cu' evA_w' le_u'
                 in IH-a sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
    vs_ext   = ValidSub2-extend sigma sa rho w' vs hyp_s
    wtsub_ext = extSub-WtSub {A = A} wtsub (subst-HasType wtsub wfH da)
    raw      = IH-M (extSub sigma sa) (extendEnv rho w')
                 crho_ext vs_ext fits_ext wtsub_ext wfH u evM_w' ac evB_w' fm
    r1 = S.Eq-transport (\ T -> Val2 H T (substExpr (extSub sigma sa) B) u ac)
           (S.Eq-sym (substExpr-comp sigma M sa)) raw
    r2 = S.Eq-transport (\ T -> Val2 H (subst1 sM sa) T u ac)
           (S.Eq-sym (substExpr-comp sigma B sa)) r1
    r3 = S.Eq-transport (\ T -> Val2 H T (subst1 sB sa) u ac)
           (S.Eq-sym (subst-subst1 sigma M a0)) r2
    r4 = S.Eq-transport (\ T -> Val2 H (substExpr sigma (subst1 M a0)) T u ac)
           (S.Eq-sym (subst-subst1 sigma B a0)) r3

------------------------------------------------------------------------
-- β
------------------------------------------------------------------------

AdqE1-beta : {g : Nat} {G : Ctx g} {A : Expr g} {B M : Expr (suc g)} {a : Expr g} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) M B -> HasType G a A ->
  Adq (extend G A) M B -> Adq G a A ->
  AdqE1 G (App A B (Lam A B M) a) (subst1 M a) (subst1 B a)
AdqE1-beta {A = A} {B = B} {M = M} {a = a0}
  d1 d2 d3 d4 IH-M IH-a {H = H} sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let hu_c     = evFwd-Tm (conv-beta d1 d2 d3 d4) rho fits u hu
      val_subst = Adq-subst1 d1 d4 IH-M IH-a sigma rho crho vs fits wtsub wfH u hu_c ac evAc fm
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sM0  = substExpr (liftSub sigma) M
      sa   = substExpr sigma a0
      wsL  = liftSub-WtSub wtsub wfH d1
      htA  = subst-IsType wtsub wfH d1
      htB  = subst-IsType wsL (wf-extend htA) d2
      htM  = subst-HasType wsL (wf-extend htA) d3
      hta  = subst-HasType wtsub wfH d4
      eqM  = S.Eq-sym (subst-subst1 sigma M a0)
      beta-hr : HeadRed (App sA sB (Lam sA sB sM0) sa) (substExpr sigma (subst1 M a0))
      beta-hr = S.Eq-transport (\ X -> HeadRed (App sA sB (Lam sA sB sM0) sa) X) eqM
                  (headred-step headred-beta headred-refl)
      cv-beta : ConvTm H (App sA sB (Lam sA sB sM0) sa) (substExpr sigma (subst1 M a0))
                         (substExpr sigma (subst1 B a0))
      cv-beta = S.Eq-transport (\ X -> ConvTm H (App sA sB (Lam sA sB sM0) sa) X (substExpr sigma (subst1 B a0)))
                  eqM
                  (S.Eq-transport (\ X -> ConvTm H (App sA sB (Lam sA sB sM0) sa) (subst1 sM0 sa) X)
                     (S.Eq-sym (subst-subst1 sigma B a0))
                     (conv-beta htA htB htM hta))
      ht-subst = snd (typing-ConvTm cv-beta)
  in EqVal2-headred-expand u ac beta-hr headred-refl cv-beta (conv-refl ht-subst)
       (Val2-to-EqVal2 u ac val_subst)
