{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JDriver.agda
--
-- The based-J eliminator adequacy driver (value + cross + conv cores),
-- parameterised by the mutual recursors, mirroring
-- NAT.Adequacy.NatCaseDep.  Consumes the App3-motive machinery from
-- ID.Adequacy.JMotive and the enriched Id records (endEqL/endEqR).
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JDriver where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import ID.Adequacy.App using (adequacySub2-App ; app-transport-Val2 ; app-transport-EqVal2)
open import ID.Adequacy.VE using (AdqE1)
open import ID.Adequacy.AdqWk using (adqU ; adqConvU ; adqVar ; adqConvVar ; adq-wk ; adqConv-wk)
open import ID.Adequacy.JMotive using (adq-App' ; adq-motiveApp3 ; adq-transport-type)
open import ID.Adequacy.RefCase using (adequacy-ty-Ref-full)
open import ID.Adequacy.Records using (RValPiP ; un-ValPi ; REqValPiP ; un-REqValPi ;
  RValIdP ; un-ValId ; REqValIdP ; un-EqValId)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; Sigma ; Pair ; nil ; cons ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ;
  Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ; FinMem-coh-u ;
  FinMem-a-in-U ; Coherent ; coh-from-aU ; finMem-bot-from)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ; JBranch)
open import ID.Syntax.Raw using (Expr ; Var ; U ; Pi ; App ; Id ; Ref ; J ; fzero ; fsuc ;
  Sub ; substExpr ; subst1 ; wkExpr ; wkRen ; renExpr ; motiveTy ; baseTy ; ren-motiveTy ;
  Eq-cong2-Expr)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-U ; ty-var ; ty-Ref ; ty-App)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; wk-HasType ; subst1-wk ; ty-baseBody)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Model.Soundness using (theorem1)

------------------------------------------------------------------------
-- adq-baseBody : the codomain of baseTy A C (= C x x (Ref x)) is valid at U
-- in the extended context.  Ports Substitution.ty-baseBody to adequacy via
-- adq-motiveApp3 at (wkExpr A, wkExpr C, Var 0, Var 0, Ref (Var 0)).
------------------------------------------------------------------------

adq-baseBody : {g : Nat} {G : Ctx g} {A C : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) ->
  Adq G A U -> AdqConv G A U -> Adq G C (motiveTy A) ->
  Adq (extend G A)
      (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero))) U
adq-baseBody {g} {G} {A} {C} dA dC IHA IHcA IHC =
  adq-motiveApp3 dA1 htC1 htx htx (ty-Ref dA1 htx)
    IHA1 IHcA1 IHC1 (adqVar fzero) (adqVar fzero) IHRef
  where
    dA1  = wk-HasType dA dA
    htx  = ty-var {i = fzero} (wf-extend dA)
    htC1 = Eq-transport (\ T -> HasType (extend G A) (wkExpr C) T) (ren-motiveTy wkRen A) (wk-HasType dA dC)
    IHA1  = adq-wk A A U IHA
    IHcA1 = adqConv-wk A A U IHcA
    IHC1 : Adq (extend G A) (wkExpr C) (motiveTy (wkExpr A))
    IHC1 = adq-transport-type (wkExpr C) (ren-motiveTy wkRen A) (adq-wk A C (motiveTy A) IHC)
    IHRef : Adq (extend G A) (Ref (Var fzero)) (Id (wkExpr A) (Var fzero) (Var fzero))
    IHRef {h1} {H1} = adequacy-ty-Ref-full {h = h1} {H = H1} {A = wkExpr A} {a = Var fzero} dA1 htx IHA1 (adqVar fzero)

------------------------------------------------------------------------
-- adq-reduct-Jbeta : the reduct  App d a0 : App3 C a0 a0 (Ref a0)  of the
-- J beta-rule, valid.  A single application of d to a0 (adq-App'), codomain
-- adq-baseBody, transported by the baseBody beta-equality.  Supplied to
-- JCase.adequacyEqSub2-J-beta for the conv-J-beta hole.
------------------------------------------------------------------------

adq-reduct-Jbeta : {g : Nat} {G : Ctx g} {A a0 C d : Expr g} ->
  HasType G A U -> HasType G a0 A -> HasType G C (motiveTy A) -> HasType G d (baseTy A C) ->
  Adq G A U -> AdqConv G A U -> Adq G C (motiveTy A) -> Adq G d (baseTy A C) -> Adq G a0 A ->
  Adq G (App d a0) (App (App (App C a0) a0) (Ref a0))
adq-reduct-Jbeta {g} {G} {A} {a0} {C} {d} dA da0 dC dd IHA IHcA IHC IHd IHa0 =
  adq-transport-type (App d a0) baseβ
    (adq-App' d a0 dA (ty-baseBody dA dC) dd da0 IHd IHa0 (adq-baseBody dA dC IHA IHcA IHC))
  where
    baseβ : Eq (subst1 (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero))) a0)
               (App (App (App C a0) a0) (Ref a0))
    baseβ = Eq-cong2-Expr App
              (Eq-cong2-Expr App (Eq-cong2-Expr App (subst1-wk C a0) refl) refl) refl

------------------------------------------------------------------------
-- adequacyV-ty-J : the value-only driver for ty-J.  Dispatches on the proof
-- value w = fst hu:  Bot -> restrictVal2 / Val2-Bot;  RefEl wit -> head-expand
-- the reduct App d wit0 (d's Pi-edge applied to the witness) transported along
-- the motive endpoint EqValTy2.  Takes the mutual recursors as (Adq/AdqConv)
-- IH parameters.
--
-- WIP (session 14): the SKELETON below type-checks -- Bot branch + the full
-- proof-value dispatch are DONE and validated (the substExpr shapes, recursor
-- IH types, and the Val2 goal all elaborate).  Only `refCore` (the RefEl crux:
-- d's Pi-edge applied to the witness + the App3-motive endpoint EqValTy2) is a
-- hole.  Kept commented so JDriver stays importable (conv-J-beta win); re-open
-- and fill refCore next session (see NEXT_SESSION_ID.md session-15 block).
------------------------------------------------------------------------

{-
adequacyV-ty-J : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b C d p : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> HasType G C (motiveTy A) ->
  HasType G d (baseTy A C) -> HasType G p (Id A a b) ->
  Adq G A U -> AdqConv G A U -> Adq G a A -> Adq G b A -> Adq G C (motiveTy A) ->
  Adq G d (baseTy A C) -> Adq G p (Id A a b) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (J C d p) rho u ->
  (at : FinEl) -> EvalRel (App (App (App C a) b) p) rho at -> FinMem u at ->
  Val2 H (substExpr sigma (J C d p))
         (substExpr sigma (App (App (App C a) b) p)) u at
adequacyV-ty-J {H = H} {G = G} {A = A} {a = a} {b = b} {C = C} {d = d} {p = p}
  dA da db dC dd dp IHA IHcA IHa IHb IHC IHd IHp sigma rho crho vs fits wtsub wfH u hu at evA fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sC = substExpr sigma C ; sd = substExpr sigma d ; sp = substExpr sigma p
    sA = substExpr sigma A ; sa = substExpr sigma a ; sb = substExpr sigma b
    at_U = FinMem-a-in-U u at fm

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    branchBot jb =
      restrictVal2 H (J sC sd sp) (App (App (App sC sa) sb) sp) Bot u at (snd jb) fm
        (finMem-bot-from at at_U) (Val2-Bot at)

    refCore : (wit : FinEl) -> EvalRel p rho (RefEl wit) ->
      EvalRel d rho (FunEl (cons (mkSigma wit u) nil)) ->
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    refCore wit evP jb = {!!}

    branch : (w : FinEl) -> EvalRel p rho w -> JBranch C d rho u w ->
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    branch Bot            evP jb = branchBot jb
    branch UCode          evP ()
    branch (FunEl _)      evP ()
    branch (PiCode _ _)   evP ()
    branch (IdCode _ _ _) evP ()
    branch (RefEl wit)    evP jb = refCore wit evP jb
-}
