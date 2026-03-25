{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SubjectReduction.agda
--
-- Subject reduction for single-step head reduction:
--   HasType G M A  →  HeadRed1 M N  →  HasType G N A
--
-- Uses Pi injectivity for the beta case (to invert Lam typing
-- through conversion).
--
-- 0 postulates.
------------------------------------------------------------------------

module SubjectReduction where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq)
open import RawSyntax using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; subst1)
open import TypingRules using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ;
  ty-Lam ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi)
open import Reduction using (HeadRed ; HeadRed1 ; headred-beta ; headred-app ;
  headred-refl ; headred-step)
open import PaperSemantics using (absurdEl)
open import SubstitutionLemma using (typing-ConvTm ; typing-WfCtx ;
  typing-type ; subst-HasType ; subst-ConvTm ;
  subst1-WtSub ; ctx-conv-HasType ; ctx-conv-ConvTm)
open import PiInjectivity using (piInjectivity ; piConv)

------------------------------------------------------------------------
-- HeadRed from U or Prop to a Pi is impossible (both are normal forms
-- distinct from Pi)
------------------------------------------------------------------------

HeadRed-not-U-Pi : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
  HeadRed U (Pi B F) -> Empty
HeadRed-not-U-Pi (headred-step () _)

HeadRed-not-Prop-Pi : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
  HeadRed Prop (Pi B F) -> Empty
HeadRed-not-Prop-Pi (headred-step () _)

------------------------------------------------------------------------
-- Lam body extraction through conversion
--
-- Given HasType G (Lam A M) T and ConvTm G T (Pi A0 B0) U,
-- produce HasType (extend G A0) M B0.
--
-- Key cases:
--   ty-Lam: T = Pi A B, use piInjectivity on the conversion
--   ty-conv: accumulate conversion, recurse
--   ty-Prop-U: T = U, conv U → Pi is impossible (via piConv)
------------------------------------------------------------------------

ty-Lam-body : {n : Nat} {G : Ctx n}
  {A : Expr n} {M : Expr (suc n)} {T A0 : Expr n} {B0 : Expr (suc n)} ->
  HasType G (Lam A M) T ->
  ConvTm G T (Pi A0 B0) U ->
  HasType G A0 U -> HasType (extend G A0) B0 U ->
  HasType (extend G A0) M B0

-- ty-Lam: T = Pi A B. piInjectivity + context/type conversion.
ty-Lam-body (ty-Lam dA dB dM) conv dA0 dB0 =
  let mkSigma cvA cvB = piInjectivity conv
  in ty-conv (ctx-conv-HasType dA dA0 cvA dM)
             (ctx-conv-ConvTm dA dA0 cvA cvB) dB0

-- ty-conv: chain conversions, recurse on inner derivation
ty-Lam-body (ty-conv d dConv' _) conv dA0 dB0 =
  ty-Lam-body d (conv-trans dConv' conv) dA0 dB0

-- ty-Prop-U: T = U. ConvTm G U (Pi A0 B0) U is impossible
-- because piConv gives HeadRed U (Pi _ _) which can't exist.
ty-Lam-body (ty-Prop-U d) conv dA0 dB0 =
  let mkSigma _ (mkSigma _ (mkSigma hr _)) = piConv conv
  in absurdEl (HeadRed-not-U-Pi hr)

------------------------------------------------------------------------
-- Subject reduction for single-step head reduction
------------------------------------------------------------------------

subject-red1 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> HasType G N A

-- ty-conv: peel off, recurse, re-wrap
subject-red1 (ty-conv d dConv dT) hr =
  ty-conv (subject-red1 d hr) dConv dT

-- ty-Prop-U: peel off, recurse, re-wrap
subject-red1 (ty-Prop-U d) hr =
  ty-Prop-U (subject-red1 d hr)

-- ty-App + headred-app: function reduces, rebuild App
subject-red1 (ty-App dA dB df da) (headred-app hr) =
  ty-App dA dB (subject-red1 df hr) da

-- ty-App + headred-beta: the key case
-- df : HasType G (Lam A' M') (Pi A0 B0), da : HasType G a A0
-- Need: HasType G (subst1 M' a) (subst1 B0 a)
subject-red1 (ty-App dA0 dB0 df da0) headred-beta =
  let -- Extract body at the target type via ty-Lam-body
      dBody = ty-Lam-body df (conv-refl (ty-Pi dA0 dB0)) dA0 dB0
      -- Substitute: HasType G (subst1 M' a) (subst1 B0 a)
  in subst-HasType (subst1-WtSub dA0 da0) (typing-WfCtx dA0) dBody
