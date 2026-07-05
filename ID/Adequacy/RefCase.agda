{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.RefCase.agda
--
-- The adequacy combinators for the Ref proof CONSTRUCTOR:
--
--   ty-Ref   : adequacy-ty-Ref-full    : Adq G (Ref a) (Id A a a)
--   ty-Ref   : adequacyV-ty-Ref-full   : AdqConv G (Ref a) (Id A a a)
--   conv-Ref : adequacyEqSub2-Ref-full : AdqE1 G (Ref a) (Ref a') (Id A a a)
--
-- The proof VALUE records RValId / REqValId are proof-IRRELEVANT (only
-- domA0/lhs0/rhs0/red), so the two-substitution and conversion cases collapse
-- to the same record as the single case.  The type-part (ValTy2 of Id A a a)
-- is built by reusing `adequacy-ty-Id-core` on the type former.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.RefCase where

import ID.Domain.Basic as S
open S using (Nat ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl)
open import ID.Syntax.Raw using (Expr ; U ; Id ; Ref ; Sub ; substExpr)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; FinMem ; FinMem-a-in-U ;
  FinMem-coh-u ; coh-from-aU ; finMem-idU-dom)
open import ID.Domain.Membership using (finMem-ref-wit)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; CoherentEnv)
open import ID.Syntax.Typing using (Ctx ; HasType ; ConvTm ; WfCtx ; ty-Id ; ty-Ref ;
  conv-refl ; conv-sym ; conv-conv ; conv-Id)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ;
  subst-ConvTm ; subst-ConvTm-cross ; typing-ConvTm)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2)
open import ID.Adequacy.IdCase using (adequacy-ty-Id-core)
open import ID.Adequacy.VE using (AdqE1)
open import ID.Syntax.Reduction using (headred-refl)

------------------------------------------------------------------------
-- Shared: build ValTy2 of the Id type (Id A a a) at code (IdCode t l r),
-- reusing the Id-type former's single-substitution adequacy.
------------------------------------------------------------------------

refIdTyVal : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a : Expr g} ->
  HasType G A U -> HasType G a A -> Adq G A U -> Adq G a A ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (w t l r : FinEl) ->
  EvalRel (Id A a a) rho (IdCode t l r) -> FinMem (RefEl w) (IdCode t l r) ->
  ValTy2 H (substExpr sigma (Id A a a)) (IdCode t l r)
refIdTyVal {A = A} {a = a} dA da IH-A IH-a sigma rho crho vs fits wtsub wfH w t l r evA fm =
  Val2-U-to-ValTy2 (IdCode t l r) fmIdU
    (adequacy-ty-Id-core dA da da IH-A IH-a IH-a sigma rho crho vs fits wtsub wfH t l r evA evUU fmIdU)
  where
    evUU  = mkSigma tt (LeCode-refl UCode tt)
    fmIdU = FinMem-a-in-U (RefEl w) (IdCode t l r) fm

------------------------------------------------------------------------
-- ty-Ref : single-substitution value.
------------------------------------------------------------------------

adequacy-ty-Ref-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a : Expr g} ->
  HasType G A U -> HasType G a A -> Adq G A U -> Adq G a A ->
  Adq G (Ref a) (Id A a a)
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (IdCode _ _ _) () a evA fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu Bot evA fm = tt
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu UCode () fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu (FunEl _) () fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu (PiCode _ _) () fm
adequacy-ty-Ref-full dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu (RefEl _) () fm
adequacy-ty-Ref-full {A = A} {a = a} dA da IH-A IH-a sigma rho crho vs fits wtsub wfH (RefEl w) hu (IdCode t l r) evA fm =
  mk-ValId (refIdTyVal dA da IH-A IH-a sigma rho crho vs fits wtsub wfH w t l r evA fm)
    (record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
            ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
            ; wit0 = substExpr sigma a ; redTm = mkRed3 headred-refl (conv-refl (ty-Ref htA htL)) ; refConvL = conv-refl htL ; refConvR = conv-refl htL ; refMem = fm
            ; endEqL = endEqd ; endEqR = endEqd })
  where
    htA = subst-HasType wtsub wfH dA
    htL = subst-HasType wtsub wfH da
    val_a = IH-a sigma rho crho vs fits wtsub wfH w hu t (fst (snd evA)) (finMem-ref-wit w t l r fm)
    endEqd = Val2-to-EqVal2 w t val_a

------------------------------------------------------------------------
-- ty-Ref : two-substitution value (same term Ref a).  RValId proof-irrelevant,
-- so both endpoints and the equality use the identical record.
------------------------------------------------------------------------

adequacyV-ty-Ref-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a : Expr g} ->
  HasType G A U -> HasType G a A -> Adq G A U -> Adq G a A -> AdqConv G a A ->
  AdqConv G (Ref a) (Id A a a)
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (IdCode _ _ _) () a evA fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu Bot evA fm = tt
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu UCode () fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu (FunEl _) () fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu (PiCode _ _) () fm
adequacyV-ty-Ref-full dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu (RefEl _) () fm
adequacyV-ty-Ref-full {A = A} {a = a} dA da IH-A IH-a IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (RefEl w) hu (IdCode t l r) evA fm =
  mk-EqValId (refIdTyVal dA da IH-A IH-a sigma rho crho vs fits wtsub wfH w t l r evA fm) rM rN rEq
  where
    htA  = subst-HasType wtsub  wfH dA ; htL  = subst-HasType wtsub  wfH da
    htA' = subst-HasType wtsub' wfH dA ; htL' = subst-HasType wtsub' wfH da
    convA = subst-ConvTm-cross dA wtsub wtsub' wcs wfH
    convL = subst-ConvTm-cross da wtsub wtsub' wcs wfH
    htIdσ = ty-Id htA htL htL
    -- σ'-side Ref: retype its natural Id type (Id s'A s'a s'a) to the σ type.
    cIdFwd = conv-Id htA htL htL convA convL convL
    redTmN = mkRed3 headred-refl (conv-conv (conv-refl (ty-Ref htA' htL')) (conv-sym cIdFwd) htIdσ)
    redTmM = mkRed3 headred-refl (conv-refl (ty-Ref htA htL))
    fmwt = finMem-ref-wit w t l r fm
    cohW = FinMem-coh-u w t fmwt
    cohT = coh-from-aU t (finMem-idU-dom t l r (FinMem-a-in-U (RefEl w) (IdCode t l r) fm))
    crossA = IH-ca sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH w hu t (fst (snd evA)) fmwt
    endReflM = Val2-to-EqVal2 w t (Val2-from-EqVal2-first w t crossA)   -- sa ~ sa
    endSymN  = EqVal2-sym w t cohW cohT crossA                          -- sa' ~ sa
    rM  = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0 = substExpr sigma a ; redTm = redTmM ; refConvL = conv-refl htL ; refConvR = conv-refl htL ; refMem = fm
                 ; endEqL = endReflM ; endEqR = endReflM }
    rN  = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0 = substExpr sigma' a ; redTm = redTmN ; refConvL = conv-sym convL ; refConvR = conv-sym convL ; refMem = fm
                 ; endEqL = endSymN ; endEqR = endSymN }
    rEq = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0M = substExpr sigma a ; wit0N = substExpr sigma' a
                 ; redTmM = redTmM ; redTmN = redTmN ; refMem = fm
                 ; endEqLM = endReflM ; endEqRM = endReflM ; endEqLN = endSymN ; endEqRN = endSymN }

------------------------------------------------------------------------
-- conv-Ref : single sub, Ref a / Ref a'.  The a'-side proof term Ref a' is
-- retyped from its natural Id type to the stated Id A a a.
------------------------------------------------------------------------

adequacyEqSub2-Ref-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a a' : Expr g} ->
  HasType G A U -> HasType G a A -> ConvTm G a a' A -> Adq G A U -> Adq G a A -> AdqE1 G a a' A ->
  AdqE1 G (Ref a) (Ref a') (Id A a a)
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (IdCode _ _ _) () a evA fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu Bot evA fm = tt
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu UCode () fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu (FunEl _) () fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu (PiCode _ _) () fm
adequacyEqSub2-Ref-full dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu (RefEl _) () fm
adequacyEqSub2-Ref-full {A = A} {a = a} {a' = a'} dA da ca IH-A IH-a IH-ea sigma rho crho vs fits wtsub wfH (RefEl w) hu (IdCode t l r) evA fm =
  mk-EqValId (refIdTyVal dA da IH-A IH-a sigma rho crho vs fits wtsub wfH w t l r evA fm) rM rN rEq
  where
    htA  = subst-HasType wtsub wfH dA ; htL = subst-HasType wtsub wfH da
    htL'' = subst-HasType wtsub wfH (snd (typing-ConvTm ca))   -- HasType sa' sA
    convL = subst-ConvTm wtsub wfH ca                          -- ConvTm sa sa' sA
    htIdσ = ty-Id htA htL htL
    cIdFwd = conv-Id htA htL htL (conv-refl htA) convL convL
    redTmN = mkRed3 headred-refl (conv-conv (conv-refl (ty-Ref htA htL'')) (conv-sym cIdFwd) htIdσ)
    redTmM = mkRed3 headred-refl (conv-refl (ty-Ref htA htL))
    fmwt = finMem-ref-wit w t l r fm
    cohW = FinMem-coh-u w t fmwt
    cohT = coh-from-aU t (finMem-idU-dom t l r (FinMem-a-in-U (RefEl w) (IdCode t l r) fm))
    crossA = IH-ea sigma rho crho vs fits wtsub wfH w hu t (fst (snd evA)) fmwt   -- sa ~ sa' : sA
    endReflM = Val2-to-EqVal2 w t (Val2-from-EqVal2-first w t crossA)             -- sa ~ sa
    endSymN  = EqVal2-sym w t cohW cohT crossA                                    -- sa' ~ sa
    rM  = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0 = substExpr sigma a ; redTm = redTmM ; refConvL = conv-refl htL ; refConvR = conv-refl htL ; refMem = fm
                 ; endEqL = endReflM ; endEqR = endReflM }
    rN  = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0 = substExpr sigma a' ; redTm = redTmN ; refConvL = conv-sym convL ; refConvR = conv-sym convL ; refMem = fm
                 ; endEqL = endSymN ; endEqR = endSymN }
    rEq = record { domA0 = substExpr sigma A ; lhs0 = substExpr sigma a ; rhs0 = substExpr sigma a
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htA htL htL))
                 ; wit0M = substExpr sigma a ; wit0N = substExpr sigma a'
                 ; redTmM = redTmM ; redTmN = redTmN ; refMem = fm
                 ; endEqLM = endReflM ; endEqRM = endReflM ; endEqLN = endSymN ; endEqRN = endSymN }
