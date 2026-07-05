{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JCase.agda
--
-- Adequacy combinators for the based-J eliminator.
--
--   conv-J-beta : adequacyEqSub2-J-beta : AdqE1-like for
--                 J C d (Ref a) = d : App C a
--
-- conv-J-beta is the exact analogue of conv-beta (Adequacy/Beta.agda): the
-- proof is a LITERAL `Ref a`, so `headred-J` fires directly and the reduct
-- d's value is head-EXPANDED back into the J-redex.
--
-- (ty-J / conv-J -- the general-proof crux -- are TODO.)
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JCase where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq)

import ID.Domain.Basic as S
open S using (Nat ; tt ; mkSigma ; fst ; snd ; FinEl)
open import ID.Domain.Kernel using (FinMem)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; CoherentEnv)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; App ; Id ; Ref ; J ; subst1 ; Sub ; substExpr ; motiveTy ; baseTy)
open import ID.Syntax.Typing using (Ctx ; HasType ; ConvTm ; WfCtx ; conv-J-beta ; conv-refl)
open import ID.Syntax.Reduction using (HeadRed ; headred-step ; headred-J ; headred-refl)
open import ID.Syntax.Substitution using (WtSub ; subst-HasType ; subst-ConvTm ; typing-ConvTm)
open import ID.Model.Soundness using (convSound)
open import ID.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- conv-J-beta : J C d (Ref a) = d : App C a.
------------------------------------------------------------------------

-- ML J-β: J C d (Ref a0) = App d a0 : App³ C a0 a0 (Ref a0).  Head-expand the
-- reduct (App d a0)'s validity back into the J-redex (headred-J now ⇒ App d a0).
adequacyEqSub2-J-beta : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a0 C d : Expr g} ->
  HasType G A U -> HasType G a0 A ->
  HasType G C (motiveTy A) -> HasType G d (baseTy A C) ->
  Adq G (App d a0) (App (App (App C a0) a0) (Ref a0)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (J C d (Ref a0)) rho u ->
  (ac : FinEl) -> EvalRel (App (App (App C a0) a0) (Ref a0)) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (J C d (Ref a0))) (substExpr sigma (App d a0))
           (substExpr sigma (App (App (App C a0) a0) (Ref a0))) u ac
adequacyEqSub2-J-beta {A = A} {a0 = a0} {C = C} {d = d} dA da0 dC dd IH-reduct
    sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let cvb    = conv-J-beta dA da0 dC dd
      hu_c   = convSound cvb rho fits u hu                          -- EvalRel (App d a0) rho u
      val_r  = IH-reduct sigma rho crho vs fits wtsub wfH u hu_c ac evAc fm
      j-hr   = headred-step headred-J headred-refl                   -- HeadRed (J sC sd (Ref sa0)) (App sd sa0)
      cv-J   = subst-ConvTm wtsub wfH cvb
      eqdiag = Val2-to-EqVal2 u ac val_r
      ht-r   = snd (typing-ConvTm cv-J)
  in EqVal2-headred-expand u ac j-hr headred-refl cv-J (conv-refl ht-r) eqdiag
