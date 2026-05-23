{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ConvPiVariant.agda  (MIN/ — Pi + U fragment)
--
-- Route 1: mutual admissibility of the two formulations of the Pi
-- congruence rule, differing ONLY in the context of the dB' premise:
--
--   standard  conv-Pi      : dB' : (extend G A ) |- B' : U
--   variant   conv-Pi-var  : dB' : (extend G A') |- B' : U
--
-- We show each rule is a derived (admissible) rule of the system that
-- has the other.  The bridge is context conversion (ctx-conv-HasType),
-- and the missing typing presupposition of A' comes from typing-ConvTm
-- d1.  Both lemmas already live in MIN.SubstitutionLemma.
--
-- This is the purely syntactical witness that the two typing systems
-- derive exactly the same judgments.
--
-- No postulates, no holes.
------------------------------------------------------------------------

module MIN.ConvPiVariant where

open import MIN.Basic using (Nat ; suc ; fst ; snd)
open import MIN.RawSyntax using (Expr ; U ; Pi)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; ConvTm ;
  conv-Pi ; conv-sym)
open import MIN.SubstitutionLemma using (typing-ConvTm ; ctx-conv-HasType)

------------------------------------------------------------------------
-- Direction (a): the VARIANT rule is admissible in the STANDARD system.
--
-- Given the variant-shaped premises (dB' typed in extend G A'), we build
-- the conclusion using the real conv-Pi: convert dB' from extend G A'
-- back to extend G A along (conv-sym d1), supplying the A'/A typing
-- presuppositions of d1.
------------------------------------------------------------------------

conv-Pi-variant :
  {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HasType G A U ->
  HasType (extend G A) B U ->
  HasType (extend G A') B' U ->          -- variant: dB' lives in  Γ.A'
  ConvTm G A A' U ->
  ConvTm (extend G A) B B' U ->
  ConvTm G (Pi A B) (Pi A' B') U
conv-Pi-variant dA dB dB' d1 d2 =
  conv-Pi dA dB
    (ctx-conv-HasType (snd (typing-ConvTm d1)) (fst (typing-ConvTm d1))
                      (conv-sym d1) dB')
    d1 d2

------------------------------------------------------------------------
-- Direction (b): the STANDARD rule is admissible in the VARIANT system.
--
-- We abstract over the variant rule as a hypothesis (VariantPiRule) --
-- i.e. we assume a system whose Pi congruence has dB' typed in extend
-- G A' -- and derive the standard-shaped conclusion from standard
-- premises (dB' typed in extend G A), converting dB' the other way.
------------------------------------------------------------------------

VariantPiRule : Set
VariantPiRule =
  {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HasType G A U ->
  HasType (extend G A) B U ->
  HasType (extend G A') B' U ->
  ConvTm G A A' U ->
  ConvTm (extend G A) B B' U ->
  ConvTm G (Pi A B) (Pi A' B') U

conv-Pi-from-variant :
  VariantPiRule ->
  {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HasType G A U ->
  HasType (extend G A) B U ->
  HasType (extend G A) B' U ->           -- standard: dB' lives in  Γ.A
  ConvTm G A A' U ->
  ConvTm (extend G A) B B' U ->
  ConvTm G (Pi A B) (Pi A' B') U
conv-Pi-from-variant variantRule dA dB dB' d1 d2 =
  variantRule dA dB
    (ctx-conv-HasType (fst (typing-ConvTm d1)) (snd (typing-ConvTm d1))
                      d1 dB')
    d1 d2
