{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.AdqWk.agda
--
-- Foundational plain-`Adq` / `AdqConv` combinators the J motive machinery
-- needs but that were previously only available for the mutual-block
-- recursors:
--
--   adqU / adqConvU   : the U type-former's adequacy as a standalone value.
--   adqVar / adqConvVar : variable adequacy (the ty-var clause, standalone).
--   adq-wk / adqConv-wk : WEAKENING adequacy
--       Adq G M A -> Adq (extend G X) (wkExpr M) (wkExpr A)
--     built by REINSTANTIATING the given adequacy at the tail substitution
--     (\ i -> sigma (fsuc i)) and the tail environment (EnvApprox (suc g) is
--     always extendEnv rho z) -- the sanctioned technique (cf. NAT adq-subSucC),
--     NOT by recursing `adequacySub2` on a constructed derivation.
--
-- No postulates.  Nothing here is in the Value.agda SCC.
------------------------------------------------------------------------

module ID.Adequacy.AdqWk where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv)
open import ID.Adequacy.Bundle using (valU-UU)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Eq ; refl ; Eq-transport ; Eq-sym)
open import ID.Syntax.Raw using (Expr ; Var ; U ; wkExpr ; Sub ; substExpr ; Fin ; fzero ; fsuc ;
  wkRen ; renExpr ; subst-ren)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv)
open import ID.Model.EvalSubstitution using (EvalRel-wk ; EvalRel-unwk)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub)
open import ID.Model.SoundnessLemmas using (Fits ; Fits-tail)

------------------------------------------------------------------------
-- U type-former, standalone.
------------------------------------------------------------------------

adqU : {g : Nat} {G : Ctx g} -> Adq G U U
adqU sigma rho crho vs fits wtsub wfH u hu a evA fm =
  valU-UU wfH u a (snd hu) (snd evA) fm

adqConvU : {g : Nat} {G : Ctx g} -> AdqConv G U U
adqConvU sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  Val2-to-EqVal2 u a (valU-UU wfH u a (snd hu) (snd evA) fm)

------------------------------------------------------------------------
-- Variable adequacy (the ty-var clause, standalone).
------------------------------------------------------------------------

adqVar : {g : Nat} {G : Ctx g} (i : Fin g) -> Adq G (Var i) (lookup G i)
adqVar i sigma rho crho vs fits wtsub wfH u hu a evA fm =
  vs i u (fst hu) (snd hu) a evA fm

adqConvVar : {g : Nat} {G : Ctx g} (i : Fin g) -> AdqConv G (Var i) (lookup G i)
adqConvVar i sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  vcs i u (fst hu) (snd hu) a evA fm

------------------------------------------------------------------------
-- Weakening adequacy (single substitution).
------------------------------------------------------------------------

adq-wk : {g : Nat} {G : Ctx g} (X M A : Expr g) ->
  Adq G M A -> Adq (extend G X) (wkExpr M) (wkExpr A)
adq-wk {g} {G} X M A IH {h} {H} sigma (extendEnv rho0 z) crho vs fits wtsub wfH u hu a evA fm =
  Eq-transport (\ TM -> Val2 H TM (substExpr sigma (wkExpr A)) u a)
    (Eq-sym (subst-ren sigma wkRen M))
    (Eq-transport (\ TA -> Val2 H (substExpr tail M) TA u a)
      (Eq-sym (subst-ren sigma wkRen A))
      res)
  where
    tail : Sub h g
    tail = \ i -> sigma (fsuc i)
    hu0 : EvalRel M rho0 u
    hu0 = EvalRel-unwk M rho0 z u hu
    evA0 : EvalRel A rho0 a
    evA0 = EvalRel-unwk A rho0 z a evA
    vs0 : ValidSub2 H G tail rho0
    vs0 i u' cu' le' a' evA' fm' =
      Eq-transport (\ T -> Val2 H (sigma (fsuc i)) T u' a')
        (subst-ren sigma wkRen (lookup G i))
        (vs (fsuc i) u' cu' le' a' (EvalRel-wk (lookup G i) rho0 z a' evA') fm')
    wtsub0 : WtSub H G tail
    wtsub0 i = Eq-transport (\ T -> HasType H (sigma (fsuc i)) T)
                 (subst-ren sigma wkRen (lookup G i)) (wtsub (fsuc i))
    res : Val2 H (substExpr tail M) (substExpr tail A) u a
    res = IH tail rho0 (fst crho) vs0 (fst fits) wtsub0 wfH u hu0 a evA0 fm

------------------------------------------------------------------------
-- Weakening adequacy (cross / two-substitution).
------------------------------------------------------------------------

adqConv-wk : {g : Nat} {G : Ctx g} (X M A : Expr g) ->
  AdqConv G M A -> AdqConv (extend G X) (wkExpr M) (wkExpr A)
adqConv-wk {g} {G} X M A IH {h} {H} sigma sigma' (extendEnv rho0 z) crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  Eq-transport (\ TM -> EqVal2 H TM (substExpr sigma' (wkExpr M)) (substExpr sigma (wkExpr A)) u a)
    (Eq-sym (subst-ren sigma wkRen M))
    (Eq-transport (\ TM' -> EqVal2 H (substExpr tail M) TM' (substExpr sigma (wkExpr A)) u a)
      (Eq-sym (subst-ren sigma' wkRen M))
      (Eq-transport (\ TA -> EqVal2 H (substExpr tail M) (substExpr tail' M) TA u a)
        (Eq-sym (subst-ren sigma wkRen A))
        res))
  where
    tail : Sub h g
    tail = \ i -> sigma (fsuc i)
    tail' : Sub h g
    tail' = \ i -> sigma' (fsuc i)
    hu0 : EvalRel M rho0 u
    hu0 = EvalRel-unwk M rho0 z u hu
    evA0 : EvalRel A rho0 a
    evA0 = EvalRel-unwk A rho0 z a evA
    vs0 : ValidSub2 H G tail rho0
    vs0 i u' cu' le' a' evA' fm' =
      Eq-transport (\ T -> Val2 H (sigma (fsuc i)) T u' a')
        (subst-ren sigma wkRen (lookup G i))
        (vs (fsuc i) u' cu' le' a' (EvalRel-wk (lookup G i) rho0 z a' evA') fm')
    vs0' : ValidSub2 H G tail' rho0
    vs0' i u' cu' le' a' evA' fm' =
      Eq-transport (\ T -> Val2 H (sigma' (fsuc i)) T u' a')
        (subst-ren sigma' wkRen (lookup G i))
        (vs' (fsuc i) u' cu' le' a' (EvalRel-wk (lookup G i) rho0 z a' evA') fm')
    vcs0 : ValidConvSub2 H G tail tail' rho0
    vcs0 i u' cu' le' a' evA' fm' =
      Eq-transport (\ T -> EqVal2 H (sigma (fsuc i)) (sigma' (fsuc i)) T u' a')
        (subst-ren sigma wkRen (lookup G i))
        (vcs (fsuc i) u' cu' le' a' (EvalRel-wk (lookup G i) rho0 z a' evA') fm')
    wtsub0 : WtSub H G tail
    wtsub0 i = Eq-transport (\ T -> HasType H (sigma (fsuc i)) T)
                 (subst-ren sigma wkRen (lookup G i)) (wtsub (fsuc i))
    wtsub0' : WtSub H G tail'
    wtsub0' i = Eq-transport (\ T -> HasType H (sigma' (fsuc i)) T)
                  (subst-ren sigma' wkRen (lookup G i)) (wtsub' (fsuc i))
    wcs0 : WtConvSub H G tail tail'
    wcs0 i = Eq-transport (\ T -> ConvTm H (sigma (fsuc i)) (sigma' (fsuc i)) T)
               (subst-ren sigma wkRen (lookup G i)) (wcs (fsuc i))
    res : EqVal2 H (substExpr tail M) (substExpr tail' M) (substExpr tail A) u a
    res = IH tail tail' rho0 (fst crho) vs0 vs0' vcs0 (fst fits) wtsub0 wtsub0' wcs0 wfH u hu0 a evA0 fm
