{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JMotive.agda
--
-- The App³-motive adequacy machinery for the based-J eliminator.
--
--   adqConv-ty-Pi-full : the CROSS (AdqConv) Pi type-former, wrapping
--                        AdequacyVE.adequacyV-ty-Pi with the code dispatch
--                        (the standalone form of adequacyConvSub2 (ty-Pi)).
--   adq-motiveTail     : Adq (extend G A) (motive tail) U -- the codomain of
--                        motiveTy's first Pi, built purely from A's adequacy
--                        via the Pi/Id type-formers + the AdqWk weakening/
--                        variable lemmas (NO constructed-derivation recursion).
--
-- No postulates.  Not in the Value.agda SCC.
------------------------------------------------------------------------

module ID.Adequacy.JMotive where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv)
open import ID.Adequacy.Bundle using (adequacy-ty-Pi-full)
open import ID.Adequacy.IdCase using (adequacy-ty-Id-full ; adequacyV-ty-Id-full)
open import ID.Adequacy.VE using (adequacyV-ty-Pi)
open import ID.Adequacy.AdqWk using (adqU ; adqConvU ; adqVar ; adqConvVar ; adq-wk ; adqConv-wk)
open import ID.Adequacy.App using (adequacySub2-App)

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
-- Cross Pi type-former (standalone AdqConv G (Pi A B) U).
------------------------------------------------------------------------

adqConv-ty-Pi-full : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqConv G A U -> AdqConv (extend G A) B U ->
  AdqConv G (Pi A B) U
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu Bot evA fm = tt
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (FunEl _) evA ()
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
adqConv-ty-Pi-full d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode evA fm =
  adequacyV-ty-Pi d1 d2 ca cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f0 hu evA fm

------------------------------------------------------------------------
-- adq-motiveTail : the codomain of motiveTy A's first Pi, valid at U.
--   motiveTy A = Pi A (Pi A↑ (Pi (Id A↑↑ (Var 1) (Var 0)) U))
--   mTail  A   =        Pi A↑ (Pi (Id A↑↑ (Var 1) (Var 0)) U)   in (extend G A)
------------------------------------------------------------------------

adq-motiveTail : {g : Nat} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U -> AdqConv G A U ->
  Adq (extend G A) (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U)) U
adq-motiveTail {g} {G} {A} dA IHA IHcA {h} {H} =
  adequacy-ty-Pi-full {h = h} {H = H} d1 d2 IH-A IH-B IH-Bc
  where
    d1  = wk-HasType dA dA                                  -- HasType (extend G A) (wkExpr A) U
    dA2 = wk-HasType d1 d1                                  -- HasType Γ2 (wkExpr (wkExpr A)) U
    dv1 = ty-var {i = fsuc fzero} (wf-extend d1)            -- Var 1 : wkExpr (wkExpr A)
    dv0 = ty-var {i = fzero} (wf-extend d1)                 -- Var 0 : wkExpr (wkExpr A)
    dId = ty-Id dA2 dv1 dv0                                 -- HasType Γ2 (Id ..) U
    dU2 = ty-U (wf-extend dId)                              -- HasType (extend Γ2 (Id..)) U U
    d2  = ty-Pi dId dU2                                     -- HasType Γ2 (Pi (Id..) U) U
    IH-A   = adq-wk A A U IHA                               -- Adq (extend G A) (wkExpr A) U
    IHA2   = adq-wk (wkExpr A) (wkExpr A) U (adq-wk A A U IHA)          -- Adq Γ2 (wkExpr (wkExpr A)) U
    IHcA2  = adqConv-wk (wkExpr A) (wkExpr A) U (adqConv-wk A A U IHcA) -- AdqConv Γ2 (wkExpr (wkExpr A)) U
    IH-Id : Adq (extend (extend G A) (wkExpr A)) (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U
    IH-Id {h1} {H1} = adequacy-ty-Id-full {h = h1} {H = H1} dA2 dv1 dv0 IHA2 (adqVar (fsuc fzero)) (adqVar fzero)
    IHc-Id : AdqConv (extend (extend G A) (wkExpr A)) (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U
    IHc-Id {h1} {H1} = adequacyV-ty-Id-full {h = h1} {H = H1} dA2 dv1 dv0 IHcA2 (adqConvVar (fsuc fzero)) (adqConvVar fzero)
    IH-B : Adq (extend (extend G A) (wkExpr A)) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U) U
    IH-B {h1} {H1} = adequacy-ty-Pi-full {h = h1} {H = H1} dId dU2 IH-Id adqU adqConvU
    IH-Bc  = adqConv-ty-Pi-full dId dU2 IHc-Id adqConvU

------------------------------------------------------------------------
-- Transport an adequacy along a type equality.
------------------------------------------------------------------------

adq-transport-type : {g : Nat} {G : Ctx g} {T T' : Expr g} (M : Expr g) ->
  Eq T T' -> Adq G M T -> Adq G M T'
adq-transport-type M eq IH {h} {H} sigma rho crho vs fits wtsub wfH u hu a evA fm =
  Eq-transport (\ TT -> Val2 H (substExpr sigma M) (substExpr sigma TT) u a) eq
    (IH sigma rho crho vs fits wtsub wfH u hu a
       (Eq-transport (\ TT -> EvalRel TT rho a) (Eq-sym eq) evA) fm)

------------------------------------------------------------------------
-- A single application, as a clean Adq (eta-expansion of adequacySub2-App).
------------------------------------------------------------------------

adq-App' : {g : Nat} {G : Ctx g} {A' : Expr g} {B' : Expr (suc g)} (f a' : Expr g) ->
  HasType G A' U -> HasType (extend G A') B' U -> HasType G f (Pi A' B') -> HasType G a' A' ->
  Adq G f (Pi A' B') -> Adq G a' A' -> Adq (extend G A') B' U ->
  Adq G (App f a') (subst1 B' a')
adq-App' f a' dA dB df da IHf IHa IHB {h} {H} sigma rho crho vs fits wtsub wfH u hu a evA fm =
  adequacySub2-App dA dB df da IHf IHa IHB sigma rho crho vs fits wtsub wfH
    u (EvalRel-coh (App f a') rho u hu) hu a evA fm

------------------------------------------------------------------------
-- adq-motiveApp3 : the J result type  App (App (App C a) b) p : U, valid.
-- Ports Substitution.ty-motiveApp3 to the adequacy level (three adq-App',
-- transported by lem1 / lem2, codomains from adq-motiveTail / adq-B2 / adqU).
------------------------------------------------------------------------

adq-motiveApp3 : {g : Nat} {G : Ctx g} {A C a b p : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) -> HasType G a A -> HasType G b A -> HasType G p (Id A a b) ->
  Adq G A U -> AdqConv G A U -> Adq G C (motiveTy A) -> Adq G a A -> Adq G b A -> Adq G p (Id A a b) ->
  Adq G (App (App (App C a) b) p) U
adq-motiveApp3 {g} {G} {A} {C} {a} {b} {p} dA dC da db dp IHA IHcA IHC IHa IHb IHp =
  adq-App' (App (App C a) b) p dId dUId htCab dp appCab IHp adqU
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
    appCa-raw : Adq G (App C a) (subst1 (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U)) a)
    appCa-raw = adq-App' C a dA dmTail dC da IHC IHa (adq-motiveTail dA IHA IHcA)
    appCa : Adq G (App C a) (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    appCa = adq-transport-type (App C a) lem1 appCa-raw
    htCa : HasType G (App C a) (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    htCa = Eq-transport (\ T -> HasType G (App C a) T) lem1 (ty-App dA dmTail dC da)
    -- level 2: App (App C a) b
    appCab-raw : Adq G (App (App C a) b) (subst1 (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U) b)
    appCab-raw = adq-App' (App C a) b dA dB2 htCa db appCa IHb adq-B2
    appCab : Adq G (App (App C a) b) (Pi (Id A a b) U)
    appCab = adq-transport-type (App (App C a) b) lem2 appCab-raw
    htCab : HasType G (App (App C a) b) (Pi (Id A a b) U)
    htCab = Eq-transport (\ T -> HasType G (App (App C a) b) T) lem2 (ty-App dA dB2 htCa db)
