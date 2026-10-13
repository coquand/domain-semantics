{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Sound.agda
--
-- Theorem 16 for the concrete beta-delta term model.  The ONLY
-- remaining hypothesis is the fixed point of Gamma (Lemma 14, where
-- Mahlo strength is needed).
--
-- Consequence (T2a): if  |- t = t' : C  (closed), then the erasures of
-- t and t' (with the delta-steps fhat |-> f A F, ghat |-> g A F c
-- performed, i.e. den) reduce to values with the same eta-normal form;
-- in particular every closed well-typed term has a beta-delta normal
-- form.
------------------------------------------------------------------------

module MAHLO.Concrete.Sound where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax using (Num ; zero ; Fin ; Expr)
open import MAHLO.Typing using (empty ; HasType ; ConvTm ; conv-refl)
open import MAHLO.Fixpoint using (Fixpoint)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.Rel
open import MAHLO.Concrete.Den
open import MAHLO.Concrete.Instance

emptyEnv' : TEnv zero
emptyEnv' ()

module _ (Fx : Fixpoint concreteTM) where

  open import MAHLO.Soundness concreteTM concreteModel Fx

  -- Theorem 16, closed form, in the concrete model
  sound-closed : {t u A : Expr zero} -> ConvTm empty t u A ->
                 SR (den t emptyEnv) (den u emptyEnv)
  sound-closed c = soundness-closed c

  -- (T2a): every closed well-typed term normalises
  normalise : {t A : Expr zero} -> HasType empty t A ->
              Sg Tm (\ v -> den t emptyEnv' ⇓ v)
  normalise {t} h =
    let s = sound-closed (conv-refl h) in
    SR.va s , transport (\ z -> z ⇓ SR.va s) (den-ext (\ ()) t) (SR.da s)

------------------------------------------------------------------------
-- (T2a) from the impredicative fixed-point principle of fix.pdf
------------------------------------------------------------------------

open import MAHLO.FixHyp concreteTM using (FixThm ; LargeSups ; PFix ; fixpoint ; fixpoint-of-pfix)

-- every closed well-typed term normalises, assuming the merged principle
normalise-pfix : (P0 : PFix) {t A : Expr zero} -> HasType empty t A ->
                 Sg Tm (\ v -> den t emptyEnv' ⇓ v)
normalise-pfix P0 h = normalise (fixpoint-of-pfix P0) h

-- ... or Coquand's theorem plus large sups of candidates
normalise-fix : FixThm -> LargeSups -> {t A : Expr zero} -> HasType empty t A ->
                Sg Tm (\ v -> den t emptyEnv' ⇓ v)
normalise-fix T L h = normalise (fixpoint T L) h
