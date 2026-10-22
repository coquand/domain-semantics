{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MINPROP.NoConfusion
--
-- Sanity checks that definitional proof irrelevance does not identify
-- distinct type formers: U, Prop and Pi types are pairwise non-convertible
-- at U, in any context.  Proved from the model (conversion soundness):
-- the approximants UCode / PropCode / PiCode separate them.
--
-- No postulates.
------------------------------------------------------------------------

module MINPROP.NoConfusion where

open import MINPROP.Domain.Basic using ( Nat ; suc ; Empty ; tt ; mkSigma ; fst ; snd ;
  FinEl ; Bot ; UCode ; PropCode ; PiCode ; nil )
open import MINPROP.Domain.Kernel using ( LeCode-refl )
open import MINPROP.Syntax.Raw using ( Expr ; U ; Prop ; Pi )
open import MINPROP.Syntax.Typing using ( Ctx ; ConvTm )
open import MINPROP.Model.Eval using ( EvalRel )
open import MINPROP.Model.Soundness using ( convSound' )
open import MINPROP.PiInjectivity using ( botEnv ; botEnv-fits ; evalRel-Pi-trivial )

U-not-Prop : {n : Nat} {G : Ctx n} -> ConvTm G U Prop U -> Empty
U-not-Prop {n} {G} d =
  let mkSigma _ (mkSigma _ (mkSigma fwd _)) = convSound' d (botEnv n) (botEnv-fits G)
  in snd (fwd UCode (mkSigma tt (LeCode-refl UCode tt)))

Prop-not-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
  ConvTm G Prop (Pi A B) U -> Empty
Prop-not-Pi {n} {G} {A} {B} d =
  let mkSigma _ (mkSigma _ (mkSigma _ bwd)) = convSound' d (botEnv n) (botEnv-fits G)
  in snd (bwd (PiCode Bot nil) (evalRel-Pi-trivial A B (botEnv n)))

U-not-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
  ConvTm G U (Pi A B) U -> Empty
U-not-Pi {n} {G} {A} {B} d =
  let mkSigma _ (mkSigma _ (mkSigma _ bwd)) = convSound' d (botEnv n) (botEnv-fits G)
  in snd (bwd (PiCode Bot nil) (evalRel-Pi-trivial A B (botEnv n)))
