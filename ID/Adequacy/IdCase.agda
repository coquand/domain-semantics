{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.IdCase.agda
--
-- The adequacy combinators for the Id-TYPE former:
--
--   ty-Id   : adequacy-ty-Id-full    : Adq G (Id A a b) U          (single sub)
--   ty-Id   : adequacyV-ty-Id-full   : AdqConv G (Id A a b) U      (same term, two subs)
--   conv-Id : adequacyEqSub2-Id-full : AdqE1 G (Id A a b) (Id A' a' b') U
--
-- Id has NO Selection edges (unlike Pi): the RValTyId record just carries the
-- domain-type validity `valA` plus the two endpoints at membership level.  So
-- the combinators are short -- each builds one `RValTyIdP` / `REqValTyIdP`
-- record through the public (un)builders `mk-ValTyId` / `mk-EqValTyId`.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.IdCase where

import ID.Domain.Basic as S
open S using (Nat ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl)
open import ID.Syntax.Raw using (Expr ; U ; Id ; Sub ; substExpr)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; FinMem ; Coherent ;
  finMem-idU-dom ; finMem-idU-lhs ; finMem-idU-rhs)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; EvalRel-coh ; CoherentEnv)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ;
  ty-U ; ty-Id ; ty-conv ; conv-refl)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm ;
  subst-ConvTm-cross ; typing-ConvTm)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import ID.Adequacy.VE using (AdqE1)
open import ID.Syntax.Reduction using (headred-refl)

------------------------------------------------------------------------
-- ty-Id : single-substitution value.  Informative core at (IdCode t l r, UCode).
------------------------------------------------------------------------

adequacy-ty-Id-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> Adq G A U -> Adq G a A -> Adq G b A ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (t l r : FinEl) ->
  EvalRel (Id A a b) rho (IdCode t l r) -> EvalRel U rho UCode -> FinMem (IdCode t l r) UCode ->
  Val2 H (substExpr sigma (Id A a b)) (substExpr sigma U) (IdCode t l r) UCode
adequacy-ty-Id-core {A = A} {a = a} {b = b} dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH t l r hu evU fm =
  mkSigma redU (mk-ValTyId (record
    { domA = sA ; lhs = sa ; rhs = sb
    ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htR))
    ; htA = htA ; htL = htL ; htR = htR
    ; valA = valA ; valL = finMem-idU-lhs t l r fm ; valR = finMem-idU-rhs t l r fm
    ; valLlog = IH-a sigma rho crho vs fits wtsub wfH l (fst (snd (snd hu))) t evAt (finMem-idU-lhs t l r fm)
    ; valRlog = IH-b sigma rho crho vs fits wtsub wfH r (snd (snd (snd hu))) t evAt (finMem-idU-rhs t l r fm) }))
  where
    sA   = substExpr sigma A
    sa   = substExpr sigma a
    sb   = substExpr sigma b
    tU   = finMem-idU-dom t l r fm
    evAt = fst (snd hu)
    evUU = mkSigma tt (LeCode-refl UCode tt)
    htA  = subst-HasType wtsub wfH dA
    htL  = subst-HasType wtsub wfH da
    htR  = subst-HasType wtsub wfH db
    redU = mkRed3 headred-refl (conv-refl (ty-U wfH))
    valA = Val2-U-to-ValTy2 t tU (IH-A sigma rho crho vs fits wtsub wfH t evAt UCode evUU tU)

adequacy-ty-Id-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> Adq G A U -> Adq G a A -> Adq G b A ->
  Adq G (Id A a b) U
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (RefEl _) () a evA fm
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu Bot evA fm = tt
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (FunEl _) evA ()
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (PiCode _ _) evA ()
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (IdCode _ _ _) evA ()
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (RefEl _) evA ()
adequacy-ty-Id-full dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH (IdCode t l r) hu UCode evA fm =
  adequacy-ty-Id-core dA da db IH-A IH-a IH-b sigma rho crho vs fits wtsub wfH t l r hu evA fm

------------------------------------------------------------------------
-- ty-Id : two-substitution value (same term Id A a b, subs sigma / sigma').
------------------------------------------------------------------------

adequacyV-ty-Id-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> AdqConv G A U -> AdqConv G a A -> AdqConv G b A ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (t l r : FinEl) ->
  EvalRel (Id A a b) rho (IdCode t l r) -> EvalRel U rho UCode -> FinMem (IdCode t l r) UCode ->
  EqVal2 H (substExpr sigma (Id A a b)) (substExpr sigma' (Id A a b)) (substExpr sigma U) (IdCode t l r) UCode
adequacyV-ty-Id-core {A = A} {a = a} {b = b} dA da db IH-cA IH-ca IH-cb
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH t l r hu evU fm =
  mkSigma redU (mkSigma valTyIdAB (mkSigma valTyIdA'B' eqValTyId))
  where
    sA   = substExpr sigma A  ; sA'  = substExpr sigma' A
    sa   = substExpr sigma a  ; sa'  = substExpr sigma' a
    sb   = substExpr sigma b  ; sb'  = substExpr sigma' b
    tU   = finMem-idU-dom t l r fm
    fmL  = finMem-idU-lhs t l r fm
    fmR  = finMem-idU-rhs t l r fm
    evAt = fst (snd hu)
    eva  = fst (snd (snd hu))
    evb  = snd (snd (snd hu))
    evUU = mkSigma tt (LeCode-refl UCode tt)
    redU = mkRed3 headred-refl (conv-refl (ty-U wfH))

    htA  = subst-HasType wtsub  wfH dA  ; htA'  = subst-HasType wtsub' wfH dA
    htL  = subst-HasType wtsub  wfH da  ; htL'  = subst-HasType wtsub' wfH da
    htR  = subst-HasType wtsub  wfH db  ; htR'  = subst-HasType wtsub' wfH db

    eqD1  = IH-cA sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH t evAt UCode evUU tU
    valA  = Val2-U-to-ValTy2 t tU (Val2-from-EqVal2-first  t UCode eqD1)
    valA' = Val2-U-to-ValTy2 t tU (Val2-from-EqVal2-second t UCode eqD1)
    eqA   = EqVal2-U-to-EqValTy2 t tU eqD1

    eqD-a = IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH l eva t evAt fmL
    eqD-b = IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH r evb t evAt fmR
    vllAB = Val2-from-EqVal2-first  l t eqD-a
    vlrAB = Val2-from-EqVal2-first  r t eqD-b
    vllA'B' = Val2-type-transport l t eqA (Val2-from-EqVal2-second l t eqD-a)
    vlrA'B' = Val2-type-transport r t eqA (Val2-from-EqVal2-second r t eqD-b)

    convA = subst-ConvTm-cross dA wtsub wtsub' wcs wfH
    convL = subst-ConvTm-cross da wtsub wtsub' wcs wfH
    convR = subst-ConvTm-cross db wtsub wtsub' wcs wfH

    valTyIdAB = mk-ValTyId (record
      { domA = sA ; lhs = sa ; rhs = sb
      ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htR))
      ; htA = htA ; htL = htL ; htR = htR ; valA = valA ; valL = fmL ; valR = fmR
      ; valLlog = vllAB ; valRlog = vlrAB })
    valTyIdA'B' = mk-ValTyId (record
      { domA = sA' ; lhs = sa' ; rhs = sb'
      ; red = mkRed3 headred-refl (conv-refl (ty-Id htA' htL' htR'))
      ; htA = htA' ; htL = htL' ; htR = htR' ; valA = valA' ; valL = fmL ; valR = fmR
      ; valLlog = vllA'B' ; valRlog = vlrA'B' })
    eqValTyId = mk-EqValTyId valTyIdAB valTyIdA'B' (record
      { domA = sA ; lhs = sa ; rhs = sb ; domA' = sA' ; lhs' = sa' ; rhs' = sb'
      ; redM = mkRed3 headred-refl (conv-refl (ty-Id htA htL htR))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Id htA' htL' htR'))
      ; convA = convA ; convL = convL ; convR = convR ; eqA = eqA ; eqL = eqD-a ; eqR = eqD-b })

adequacyV-ty-Id-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> AdqConv G A U -> AdqConv G a A -> AdqConv G b A ->
  AdqConv G (Id A a b) U
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl _) () a evA fm
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu Bot evA fm = tt
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu (FunEl _) evA ()
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu (PiCode _ _) evA ()
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu (IdCode _ _ _) evA ()
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu (RefEl _) evA ()
adequacyV-ty-Id-full dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode t l r) hu UCode evA fm =
  adequacyV-ty-Id-core dA da db IH-cA IH-ca IH-cb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH t l r hu evA fm

------------------------------------------------------------------------
-- conv-Id : single sub, two terms Id A a b / Id A' a' b'.
------------------------------------------------------------------------

adequacyEqSub2-Id-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' a a' b b' : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A ->
  ConvTm G A A' U -> ConvTm G a a' A -> ConvTm G b b' A ->
  Adq G A U -> AdqE1 G A A' U -> AdqE1 G a a' A -> AdqE1 G b b' A ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (t l r : FinEl) ->
  EvalRel (Id A a b) rho (IdCode t l r) -> EvalRel U rho UCode -> FinMem (IdCode t l r) UCode ->
  EqVal2 H (substExpr sigma (Id A a b)) (substExpr sigma (Id A' a' b')) (substExpr sigma U) (IdCode t l r) UCode
adequacyEqSub2-Id-core {A = A} {A' = A'} {a = a} {a' = a'} {b = b} {b' = b'}
    dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH t l r hu evU fm =
  mkSigma redU (mkSigma valTyIdAB (mkSigma valTyIdA'B' eqValTyId))
  where
    sA   = substExpr sigma A  ; sA'  = substExpr sigma A'
    sa   = substExpr sigma a  ; sa'  = substExpr sigma a'
    sb   = substExpr sigma b  ; sb'  = substExpr sigma b'
    tU   = finMem-idU-dom t l r fm
    fmL  = finMem-idU-lhs t l r fm
    fmR  = finMem-idU-rhs t l r fm
    evAt = fst (snd hu)
    evUU = mkSigma tt (LeCode-refl UCode tt)
    redU = mkRed3 headred-refl (conv-refl (ty-U wfH))

    htA   = subst-HasType wtsub wfH dA
    htL   = subst-HasType wtsub wfH da
    htR   = subst-HasType wtsub wfH db
    convA = subst-ConvTm wtsub wfH cA
    convL = subst-ConvTm wtsub wfH ca
    convR = subst-ConvTm wtsub wfH cb
    htA'  = subst-HasType wtsub wfH (snd (typing-ConvTm cA))
    htL'  = ty-conv (subst-HasType wtsub wfH (snd (typing-ConvTm ca))) convA htA'
    htR'  = ty-conv (subst-HasType wtsub wfH (snd (typing-ConvTm cb))) convA htA'

    valA  = Val2-U-to-ValTy2 t tU (IH-A sigma rho crho vs fits wtsub wfH t evAt UCode evUU tU)
    eqD1  = IH-eA sigma rho crho vs fits wtsub wfH t evAt UCode evUU tU
    valA' = Val2-U-to-ValTy2 t tU (Val2-from-EqVal2-second t UCode eqD1)
    eqA   = EqVal2-U-to-EqValTy2 t tU eqD1
    eva   = fst (snd (snd hu))
    evb   = snd (snd (snd hu))
    eqD-a = IH-eL sigma rho crho vs fits wtsub wfH l eva t evAt fmL
    eqD-b = IH-eR sigma rho crho vs fits wtsub wfH r evb t evAt fmR
    vllAB = Val2-from-EqVal2-first l t eqD-a
    vlrAB = Val2-from-EqVal2-first r t eqD-b
    vllA'B' = Val2-type-transport l t eqA (Val2-from-EqVal2-second l t eqD-a)
    vlrA'B' = Val2-type-transport r t eqA (Val2-from-EqVal2-second r t eqD-b)

    valTyIdAB = mk-ValTyId (record
      { domA = sA ; lhs = sa ; rhs = sb
      ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htR))
      ; htA = htA ; htL = htL ; htR = htR ; valA = valA ; valL = fmL ; valR = fmR
      ; valLlog = vllAB ; valRlog = vlrAB })
    valTyIdA'B' = mk-ValTyId (record
      { domA = sA' ; lhs = sa' ; rhs = sb'
      ; red = mkRed3 headred-refl (conv-refl (ty-Id htA' htL' htR'))
      ; htA = htA' ; htL = htL' ; htR = htR' ; valA = valA' ; valL = fmL ; valR = fmR
      ; valLlog = vllA'B' ; valRlog = vlrA'B' })
    eqValTyId = mk-EqValTyId valTyIdAB valTyIdA'B' (record
      { domA = sA ; lhs = sa ; rhs = sb ; domA' = sA' ; lhs' = sa' ; rhs' = sb'
      ; redM = mkRed3 headred-refl (conv-refl (ty-Id htA htL htR))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Id htA' htL' htR'))
      ; convA = convA ; convL = convL ; convR = convR ; eqA = eqA ; eqL = eqD-a ; eqR = eqD-b })

adequacyEqSub2-Id-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' a a' b b' : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A ->
  ConvTm G A A' U -> ConvTm G a a' A -> ConvTm G b b' A ->
  Adq G A U -> AdqE1 G A A' U -> AdqE1 G a a' A -> AdqE1 G b b' A ->
  AdqE1 G (Id A a b) (Id A' a' b') U
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (RefEl _) () a evA fm
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu Bot evA fm = tt
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (FunEl _) evA ()
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (PiCode _ _) evA ()
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (IdCode _ _ _) evA ()
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu (RefEl _) evA ()
adequacyEqSub2-Id-full dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH (IdCode t l r) hu UCode evA fm =
  adequacyEqSub2-Id-core dA da db cA ca cb IH-A IH-eA IH-eL IH-eR sigma rho crho vs fits wtsub wfH t l r hu evA fm
