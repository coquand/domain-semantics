{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyFunCore.agda  (NAT/ -- PROTOTYPE)
--
-- Full (u, ac) dispatch around the already-factored single-sub App-fun
-- core (AdequacyCases.adequacyEqSub2-App-fun-core-body), supplying the
-- recursors.  This is the "Y" piece of the bundled conv-App-fun recipe:
--   App f a = App f' a : subst1 B a   (single substitution).
-- Non-recursive: no postulate.
------------------------------------------------------------------------

module NAT.Adequacy.FunCore where
open import NAT.Adequacy.HeadRed

open import NAT.Adequacy.Cases using (adequacyEqSub2-App-fun-core-body)
open import NAT.Adequacy.App using (AdSub2Rec)
open import NAT.Adequacy.ArgCore using (AdEqSub2Rec)
open import NAT.Adequacy.Pi using (Val2-U-to-ValTy2 ; Adq)
open import NAT.Adequacy.VE using (AdqE1)

import NAT.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl)
open import NAT.Domain.Kernel using (FinMem)
open import NAT.Model.Eval using (EnvApprox ; EvalRel ; CoherentEnv)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; App ; subst1 ; Sub ; substExpr)
open import NAT.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx)
open import NAT.Syntax.Substitution using (WtSub)
open import NAT.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- adequacyEqSub2-App-fun : the full dispatch over (u, ac).
------------------------------------------------------------------------

adequacyEqSub2-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
  HasType (extend G A) B U ->
  ConvTm G f f' (Pi A B) ->
  HasType G a A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  Adq G a A -> Adq (extend G A) B U -> AdqE1 G f f' (Pi A B) ->
  (u : FinEl) -> EvalRel (App f a) rho u ->
  (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
  EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
           (App (substExpr sigma f') (substExpr sigma a))
           (substExpr sigma (subst1 B a))
           u ac
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe Bot ev ac evAc fm = EqVal2-Bot ac
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe UCode ev Bot evAc ()
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe UCode ev UCode evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH UCode
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm IHa IHB IHffe Val2-U-to-ValTy2
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe UCode ev (FunEl _) evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe UCode ev (PiCode _ _) evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (PiCode _ _) ev Bot evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (PiCode _ _) ev (FunEl _) evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (PiCode _ _) ev (PiCode _ _) evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (FunEl _) ev Bot evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (FunEl _) ev UCode evAc ()
adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (FunEl _) ev (FunEl _) evAc ()
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (PiCode b0pc f0pc) ev UCode evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm IHa IHB IHffe Val2-U-to-ValTy2
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (FunEl gfe)
    (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm IHa IHB IHffe Val2-U-to-ValTy2
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ Bot _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ (FunEl _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ (PiCode _ _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ NatCode _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ ZeroEl _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ NatCode _ (SucEl _) _ ()
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe NatCode ev UCode evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH NatCode
    (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm IHa IHB IHffe Val2-U-to-ValTy2
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ Bot _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ UCode _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ (FunEl _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ (PiCode _ _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ ZeroEl _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ ZeroEl _ (SucEl _) _ ()
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe ZeroEl ev NatCode evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH ZeroEl
    (fst ev) (fst (snd ev)) (snd (snd ev)) NatCode evAc fm IHa IHB IHffe Val2-U-to-ValTy2
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ Bot _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ UCode _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ (FunEl _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ (PiCode _ _) _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ ZeroEl _ ()
adequacyEqSub2-App-fun _ _ _ _ _ _ _ _ _ _ _ _ _ (SucEl vsuc) _ (SucEl _) _ ()
adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH IHa IHB IHffe (SucEl vsuc) ev NatCode evAc fm =
  adequacyEqSub2-App-fun-core-body {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (SucEl vsuc)
    (fst ev) (fst (snd ev)) (snd (snd ev)) NatCode evAc fm IHa IHB IHffe Val2-U-to-ValTy2
