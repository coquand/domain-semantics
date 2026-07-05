{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JEndpoint.agda
--
-- The App³-motive CROSS adequacy for the based-J eliminator: the EqVal2/
-- two-substitution mirror of JMotive.adq-motiveApp3.  Produces
--   AdqConv G (App (App (App C a) b) p) U
-- from the cross (AdqConv) IHs of the endpoints C, a, b, p (plus the single
-- Adq IHs reused for the codomain-formation).  Built as three cross
-- applications (adqConv-App', an eta of App.adequacyV-ty-App), threading the
-- partial-application cross validity per level, exactly like adq-motiveApp3
-- threads the single validity.
--
-- This is THE endpoint EqValTy2 provider for the RefEl case of the ty-J
-- value driver: instantiated at G = extended H with the three argument slots
-- as variables and the two substitutions (wit0,wit0,Ref wit0) vs (a,b,p), it
-- yields  App³ sC wit0 wit0 (Ref wit0) ~ App³ sC sa sb sp.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JEndpoint where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv)
open import ID.Adequacy.Bundle using (adequacy-ty-Pi-full)
open import ID.Adequacy.IdCase using (adequacy-ty-Id-full)
open import ID.Adequacy.AdqWk using (adqU ; adqConvU ; adqVar ; adqConvVar ; adq-wk ; adqConv-wk)
open import ID.Adequacy.App using (adequacyV-ty-App)
open import ID.Adequacy.JMotive using (adq-motiveTail)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
  Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong)
open import ID.Syntax.Raw using (Expr ; Var ; U ; Pi ; Id ; App ; wkExpr ; Sub ; substExpr ; subst1 ;
  subst1Sub ; fzero ; fsuc ; motiveTy ; Eq-cong2-Expr ; Eq-cong3-Expr ; subst-wk-comm)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; EvalRel-coh ; CoherentEnv)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; WfCtx ;
  ty-U ; ty-Pi ; ty-Id ; ty-App ; ty-var ; wf-extend)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; wk-HasType ; subst1-wk ; motiveTail-formation)

------------------------------------------------------------------------
-- Cross single-application, as a clean AdqConv (eta of adequacyV-ty-App).
------------------------------------------------------------------------

adqConv-App' : {g : Nat} {G : Ctx g} {A' : Expr g} {B' : Expr (suc g)} (f a' : Expr g) ->
  HasType G A' U -> HasType (extend G A') B' U -> HasType G f (Pi A' B') -> HasType G a' A' ->
  Adq G a' A' -> Adq (extend G A') B' U -> AdqConv G f (Pi A' B') -> AdqConv G a' A' ->
  AdqConv G (App f a') (subst1 B' a')
adqConv-App' f a' dA dB df da IHav IHBv IHfc IHac sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  adequacyV-ty-App dA dB df da IHav IHBv IHfc IHac
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

------------------------------------------------------------------------
-- Transport an AdqConv along a type equality (cross mirror of
-- JMotive.adq-transport-type).
------------------------------------------------------------------------

adqConv-transport-type : {g : Nat} {G : Ctx g} {T T' : Expr g} (M : Expr g) ->
  Eq T T' -> AdqConv G M T -> AdqConv G M T'
adqConv-transport-type M eq IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  Eq-transport (\ TT -> EqVal2 _ (substExpr sigma M) (substExpr sigma' M) (substExpr sigma TT) u a) eq
    (IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a
       (Eq-transport (\ TT -> EvalRel TT rho a) (Eq-sym eq) evA) fm)

------------------------------------------------------------------------
-- adqEq-motiveApp3 : the cross mirror of JMotive.adq-motiveApp3.
------------------------------------------------------------------------

adqEq-motiveApp3 : {g : Nat} {G : Ctx g} {A C a b p : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) -> HasType G a A -> HasType G b A -> HasType G p (Id A a b) ->
  Adq G A U -> AdqConv G A U ->
  AdqConv G C (motiveTy A) ->
  Adq G a A -> AdqConv G a A -> Adq G b A -> AdqConv G b A ->
  Adq G p (Id A a b) -> AdqConv G p (Id A a b) ->
  AdqConv G (App (App (App C a) b) p) U
adqEq-motiveApp3 {g} {G} {A} {C} {a} {b} {p} dA dC da db dp
  IHA IHcA IHcC IHa IHca IHb IHcb IHp IHcp =
  adqConv-App' (App (App C a) b) p dId dUId htCab dp IHp adqU appCab IHcp
  where
    dmTail = motiveTail-formation dA
    -- level 2 codomain B2 = Pi (Id A↑ a↑ x) U
    dwkA = wk-HasType dA dA
    dwka = wk-HasType dA da
    dv0  = ty-var {i = fzero} (wf-extend dA)
    dIdBody = ty-Id dwkA dwka dv0
    dU-B2   = ty-U (wf-extend dIdBody)
    dB2 = ty-Pi dIdBody dU-B2
    adq-B2 : Adq (extend G A) (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U) U
    adq-B2 {h1} {H1} = adequacy-ty-Pi-full {h = h1} {H = H1} dIdBody dU-B2 IH-IdB2 adqU adqConvU
      where
        IH-IdB2 : Adq (extend G A) (Id (wkExpr A) (wkExpr a) (Var fzero)) U
        IH-IdB2 {h2} {H2} = adequacy-ty-Id-full {h = h2} {H = H2} dwkA dwka dv0
                              (adq-wk A A U IHA) (adq-wk A a A IHa) (adqVar fzero)
    -- endpoints
    dId  = ty-Id dA da db
    dUId = ty-U (wf-extend dId)
    lem1 : Eq (subst1 (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U)) a)
              (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    lem1 = Eq-cong2-Expr Pi (subst1-wk A a)
             (Eq-cong2-Expr Pi
               (Eq-cong3-Expr Id
                  (Eq-trans (subst-wk-comm (subst1Sub a) (wkExpr A)) (Eq-cong wkExpr (subst1-wk A a)))
                  refl refl)
               refl)
    lem2 : Eq (subst1 (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U) b) (Pi (Id A a b) U)
    lem2 = Eq-cong2-Expr Pi (Eq-cong3-Expr Id (subst1-wk A b) (subst1-wk a b) refl) refl
    -- level 1: App C a
    appCa-raw : AdqConv G (App C a) (subst1 (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U)) a)
    appCa-raw = adqConv-App' C a dA dmTail dC da IHa (adq-motiveTail dA IHA IHcA) IHcC IHca
    appCa : AdqConv G (App C a) (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    appCa = adqConv-transport-type (App C a) lem1 appCa-raw
    htCa : HasType G (App C a) (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    htCa = Eq-transport (\ T -> HasType G (App C a) T) lem1 (ty-App dA dmTail dC da)
    -- level 2: App (App C a) b
    appCab-raw : AdqConv G (App (App C a) b) (subst1 (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U) b)
    appCab-raw = adqConv-App' (App C a) b dA dB2 htCa db IHb adq-B2 appCa IHcb
    appCab : AdqConv G (App (App C a) b) (Pi (Id A a b) U)
    appCab = adqConv-transport-type (App (App C a) b) lem2 appCab-raw
    htCab : HasType G (App (App C a) b) (Pi (Id A a b) U)
    htCab = Eq-transport (\ T -> HasType G (App (App C a) b) T) lem2 (ty-App dA dB2 htCa db)
