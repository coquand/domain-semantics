{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SubjectReduction.agda  (MIN/ — Pi + U fragment)
--
-- Subject reduction for single-step head reduction:
--   HasType G M A  ->  HeadRed1 M N  ->  HasType G N A
--
-- Uses Pi injectivity for the beta case (to invert Lam typing through
-- conversion).  This is the Pi+U port of the Pi+Sigma+U
-- SubjectReduction5; with no Prop there is no cumulativity rule
-- (ty-Prop-U), so a Lam can only arise from ty-Lam / ty-conv and the
-- proof is correspondingly simpler.
--
-- 0 postulates.
------------------------------------------------------------------------

module MIN.SubjectReduction where

open import MIN.Basic using ( Nat ; suc ; mkSigma ; fst ; snd ; Pair )
open import MIN.RawSyntax using ( Expr ; U ; Pi ; Lam ; App ; subst1 )
open import MIN.TypingRules using
  ( Ctx ; extend ; HasType ; ConvTm
  ; ty-conv ; ty-Pi ; ty-Lam ; ty-App
  ; conv-refl ; conv-trans )
open import MIN.Reduction using ( HeadRed1 ; headred-beta ; headred-app )
open import MIN.SubstitutionLemma using
  ( typing-WfCtx ; subst-HasType ; subst1-WtSub
  ; ctx-conv-HasType ; ctx-conv-ConvTm )
open import MIN.PiInjectivity using ( piInjectivity )

------------------------------------------------------------------------
-- Lam body extraction through conversion.
--
-- Given HasType G (Lam A M) T and ConvTm G T (Pi A0 B0) U, produce
-- HasType (extend G A0) M B0.
--   * ty-Lam: T = Pi A B; invert the conversion with piInjectivity and
--     convert the context/codomain from A to A0.
--   * ty-conv: chain the conversions and recurse.
------------------------------------------------------------------------

ty-Lam-body : {n : Nat} {G : Ctx n}
  {A : Expr n} {M : Expr (suc n)} {T A0 : Expr n} {B0 : Expr (suc n)} ->
  HasType G (Lam A M) T ->
  ConvTm G T (Pi A0 B0) U ->
  HasType G A0 U -> HasType (extend G A0) B0 U ->
  HasType (extend G A0) M B0
ty-Lam-body (ty-Lam dA dB dM) conv dA0 dB0 =
  let mkSigma cvA cvB = piInjectivity conv
  in ty-conv (ctx-conv-HasType dA dA0 cvA dM)
             (ctx-conv-ConvTm dA dA0 cvA cvB) dB0
ty-Lam-body (ty-conv d dConv' _) conv dA0 dB0 =
  ty-Lam-body d (conv-trans dConv' conv) dA0 dB0

------------------------------------------------------------------------
-- Subject reduction for single-step head reduction.
------------------------------------------------------------------------

subject-red1 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> HasType G N A

-- ty-conv: peel off the conversion, recurse, re-wrap.
subject-red1 (ty-conv d dConv dT) hr =
  ty-conv (subject-red1 d hr) dConv dT

-- ty-App + headred-app: the function reduces; rebuild the App.
subject-red1 (ty-App dA dB df da) (headred-app hr) =
  ty-App dA dB (subject-red1 df hr) da

-- ty-App + headred-beta: invert the Lam typing at the domain/codomain
-- via ty-Lam-body, then substitute.
--   df : HasType G (Lam A' M') (Pi A0 B0), da0 : HasType G a A0
--   goal: HasType G (subst1 M' a) (subst1 B0 a)
subject-red1 (ty-App dA0 dB0 df da0) headred-beta =
  let dBody = ty-Lam-body df (conv-refl (ty-Pi dA0 dB0)) dA0 dB0
  in subst-HasType (subst1-WtSub dA0 da0) (typing-WfCtx dA0) dBody
