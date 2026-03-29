{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SubjectReduction5.agda
--
-- Subject reduction for single-step head reduction in the
-- Pi + Sigma + U system:
--   HasType G M A  ->  HeadRed1 M N  ->  HasType G N A
--
-- Also proves: HeadRed1 embeds into ConvTm (subject-conv1),
-- needed for the Snd-under-reduction case.
--
-- 0 postulates.
------------------------------------------------------------------------

module SubjectReduction5 where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; subst1)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ;
  ty-Lam ; ty-App ;
  ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-Sigma ;
  conv-beta-fst ; conv-beta-snd ;
  conv-App-fun ; conv-Fst ; conv-Snd ;
  conv-Prop-U)
open import ReductionSigma using (HeadRed ; HeadRed1 ;
  headred-beta ; headred-app ;
  headred-beta-fst ; headred-beta-snd ;
  headred-fst ; headred-snd ;
  headred-refl ; headred-step)
open import PaperSemanticsSigma using (absurdEl)
open import SubstitutionLemmaSigma using (typing-ConvTm ; typing-WfCtx ;
  typing-type ; subst-HasType ; subst-ConvTm ;
  subst1-WtSub ; ctx-conv-HasType ; ctx-conv-ConvTm ;
  subst1-cong-ConvTm)
open import Injectivity5 using (piInjectivity ; piConv ;
  sigmaInjectivity ; sigmaConv)

------------------------------------------------------------------------
-- HeadRed impossibilities
------------------------------------------------------------------------

HeadRed-not-U-Pi : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
  HeadRed U (Pi B F) -> Empty
HeadRed-not-U-Pi (headred-step () _)

HeadRed-not-U-Sigma : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
  HeadRed U (SigmaE B F) -> Empty
HeadRed-not-U-Sigma (headred-step () _)

------------------------------------------------------------------------
-- Lam body extraction through conversion
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

ty-Lam-body (ty-Prop-U d) conv dA0 dB0 =
  let mkSigma _ (mkSigma _ (mkSigma hr _)) = piConv conv
  in absurdEl (HeadRed-not-U-Pi hr)

------------------------------------------------------------------------
-- Lam conversion extraction: given HasType G (Lam A M) T,
-- extract ConvTm G T (Pi A B) U and HasType G A U etc.
-- Accumulates conversions through ty-conv.
------------------------------------------------------------------------

ty-Lam-conv : {n : Nat} {G : Ctx n}
  {A : Expr n} {M : Expr (suc n)} {T : Expr n} ->
  HasType G (Lam A M) T ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (HasType G A U) \ dA ->
  Sigma (HasType (extend G A) B U) \ dB ->
  Sigma (HasType (extend G A) M B) \ _ ->
  ConvTm G T (Pi A B) U

ty-Lam-conv (ty-Lam dA dB dM) =
  mkSigma _ (mkSigma dA (mkSigma dB (mkSigma dM (conv-refl (ty-Pi dA dB)))))

ty-Lam-conv (ty-conv d cv dT) =
  let mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM cvInner))) = ty-Lam-conv d
  in mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM (conv-trans (conv-sym cv) cvInner))))

ty-Lam-conv (ty-Prop-U d) =
  let mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM cvInner))) = ty-Lam-conv d
      -- cvInner : ConvTm G Prop (Pi A B) U — HeadRed Prop (Pi ..) impossible
      mkSigma _ (mkSigma _ (mkSigma hr _)) = piConv cvInner
  in absurdEl (HeadRed-not-Prop-Pi hr)
  where
    HeadRed-not-Prop-Pi : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
      HeadRed Prop (Pi B F) -> Empty
    HeadRed-not-Prop-Pi (headred-step () _)

------------------------------------------------------------------------
-- MkPair component extraction through conversion
------------------------------------------------------------------------

ty-MkPair-components : {n : Nat} {G : Ctx n}
  {M' N' : Expr n} {T A0 : Expr n} {B0 : Expr (suc n)} ->
  HasType G (MkPair M' N') T ->
  ConvTm G T (SigmaE A0 B0) U ->
  HasType G A0 U -> HasType (extend G A0) B0 U ->
  Pair (HasType G M' A0) (HasType G N' (subst1 B0 M'))

ty-MkPair-components (ty-MkPair dA dB dM dN) conv dA0 dB0 =
  let mkSigma cvA cvB = sigmaInjectivity conv
      dM' = ty-conv dM cvA dA0
      dBctx = ctx-conv-HasType dA dA0 cvA dB
      cvBctx = ctx-conv-ConvTm dA dA0 cvA cvB
      wfG = typing-WfCtx dA0
      da' = ty-conv dM cvA dA0
      wtsub1 = subst1-WtSub dA0 da'
      cvSubst = subst-ConvTm wtsub1 wfG cvBctx
      dB0sub = subst-HasType wtsub1 wfG dB0
      dN' = ty-conv dN cvSubst dB0sub
  in mkSigma dM' dN'

ty-MkPair-components (ty-conv d dConv' _) conv dA0 dB0 =
  ty-MkPair-components d (conv-trans dConv' conv) dA0 dB0

ty-MkPair-components (ty-Prop-U d) conv dA0 dB0 =
  let mkSigma _ (mkSigma _ (mkSigma hr _)) = sigmaConv conv
  in absurdEl (HeadRed-not-U-Sigma hr)

------------------------------------------------------------------------
-- MkPair conversion extraction (analogous to ty-Lam-conv)
------------------------------------------------------------------------

ty-MkPair-conv : {n : Nat} {G : Ctx n}
  {M' N' : Expr n} {T : Expr n} ->
  HasType G (MkPair M' N') T ->
  Sigma (Expr n) \ A -> Sigma (Expr (suc n)) \ B ->
  Sigma (HasType G A U) \ dA ->
  Sigma (HasType (extend G A) B U) \ dB ->
  Sigma (HasType G M' A) \ _ ->
  Sigma (HasType G N' (subst1 B M')) \ _ ->
  ConvTm G T (SigmaE A B) U

ty-MkPair-conv (ty-MkPair dA dB dM dN) =
  mkSigma _ (mkSigma _ (mkSigma dA (mkSigma dB (mkSigma dM (mkSigma dN (conv-refl (ty-Sigma dA dB)))))))

ty-MkPair-conv (ty-conv d cv dT) =
  let mkSigma A (mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM (mkSigma dN cvInner))))) = ty-MkPair-conv d
  in mkSigma A (mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM (mkSigma dN (conv-trans (conv-sym cv) cvInner))))))

ty-MkPair-conv (ty-Prop-U d) =
  let mkSigma A (mkSigma B (mkSigma dA (mkSigma dB (mkSigma dM (mkSigma dN cvInner))))) = ty-MkPair-conv d
      mkSigma _ (mkSigma _ (mkSigma hr _)) = sigmaConv cvInner
  in absurdEl (HeadRed-not-Prop-Sigma hr)
  where
    HeadRed-not-Prop-Sigma : {n : Nat} {B : Expr n} {F : Expr (suc n)} ->
      HeadRed Prop (SigmaE B F) -> Empty
    HeadRed-not-Prop-Sigma (headred-step () _)

------------------------------------------------------------------------
-- Subject reduction and subject conversion (mutual)
------------------------------------------------------------------------

subject-red1 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> HasType G N A

subject-conv1 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> ConvTm G M N A

-- ===================== subject-red1 =====================

subject-red1 (ty-conv d dConv dT) hr =
  ty-conv (subject-red1 d hr) dConv dT

subject-red1 (ty-Prop-U d) hr =
  ty-Prop-U (subject-red1 d hr)

-- App + headred-app
subject-red1 (ty-App dA dB df da) (headred-app hr) =
  ty-App dA dB (subject-red1 df hr) da

-- App + headred-beta
subject-red1 (ty-App dA0 dB0 df da0) headred-beta =
  let dBody = ty-Lam-body df (conv-refl (ty-Pi dA0 dB0)) dA0 dB0
  in subst-HasType (subst1-WtSub dA0 da0) (typing-WfCtx dA0) dBody

-- Fst + headred-fst
subject-red1 (ty-Fst dA dB dM) (headred-fst hr) =
  ty-Fst dA dB (subject-red1 dM hr)

-- Fst + headred-beta-fst
subject-red1 (ty-Fst dA dB dMkP) headred-beta-fst =
  fst (ty-MkPair-components dMkP (conv-refl (ty-Sigma dA dB)) dA dB)

-- Snd + headred-snd (type changes: need subject-conv1)
subject-red1 (ty-Snd dA dB dM) (headred-snd hr) =
  let dM' = subject-red1 dM hr
      cvM = subject-conv1 dM hr
      cvFst = conv-Fst dA dB cvM
      htFstM = ty-Fst dA dB dM
      htFstM' = ty-Fst dA dB dM'
      cvType = subst1-cong-ConvTm dA dB htFstM htFstM' cvFst
      htSndM' = ty-Snd dA dB dM'
      dBFstM = subst-HasType (subst1-WtSub dA htFstM) (typing-WfCtx dA) dB
  in ty-conv htSndM' (conv-sym cvType) dBFstM

-- Snd + headred-beta-snd
subject-red1 (ty-Snd dA dB dMkP) headred-beta-snd =
  let mkSigma dM dN = ty-MkPair-components dMkP (conv-refl (ty-Sigma dA dB)) dA dB
      htMkP = ty-MkPair dA dB dM dN
      cvFst = conv-beta-fst dA dB dM dN
      cvType = subst1-cong-ConvTm dA dB (ty-Fst dA dB htMkP) dM cvFst
      dBFstMkP = subst-HasType (subst1-WtSub dA (ty-Fst dA dB htMkP)) (typing-WfCtx dA) dB
  in ty-conv dN (conv-sym cvType) dBFstMkP

-- ===================== subject-conv1 =====================

subject-conv1 (ty-conv d dConv dT) hr =
  conv-conv (subject-conv1 d hr) dConv dT

subject-conv1 (ty-Prop-U d) hr =
  conv-Prop-U (subject-conv1 d hr)

-- App + headred-app
subject-conv1 (ty-App dA dB df da) (headred-app hr) =
  conv-App-fun dA dB (subject-conv1 df hr) da

-- App + headred-beta: extract Lam components, apply conv-beta
subject-conv1 (ty-App dA0 dB0 df da0) headred-beta =
  let mkSigma B' (mkSigma dA' (mkSigma dB' (mkSigma dM' cvT))) = ty-Lam-conv df
      -- cvT : ConvTm G (Pi A0 B0) (Pi A' B') U
      mkSigma cvA cvB = piInjectivity cvT
      -- cvA : ConvTm G A0 A' U, cvB : ConvTm (extend G A0) B0 B' U
      da' = ty-conv da0 cvA dA'
      -- conv-beta dA' dB' dM' da' : ConvTm G (App (Lam A' M') a) (subst1 M' a) (subst1 B' a)
      cvBeta = conv-beta dA' dB' dM' da'
      -- Convert type from subst1 B' a to subst1 B0 a
      -- conv-sym cvB : ConvTm (extend G A0) B' B0 U
      -- subst at a: ConvTm G (subst1 B' a) (subst1 B0 a) U
      wfG = typing-WfCtx dA0
      cvBsub = subst-ConvTm (subst1-WtSub dA0 da0) wfG (conv-sym cvB)
      dBa = subst-HasType (subst1-WtSub dA0 da0) wfG dB0
  in conv-conv cvBeta cvBsub dBa

-- Fst + headred-fst
subject-conv1 (ty-Fst dA dB dM) (headred-fst hr) =
  conv-Fst dA dB (subject-conv1 dM hr)

-- Fst + headred-beta-fst
subject-conv1 (ty-Fst dA dB dMkP) headred-beta-fst =
  let mkSigma dM dN = ty-MkPair-components dMkP (conv-refl (ty-Sigma dA dB)) dA dB
  in conv-beta-fst dA dB dM dN

-- Snd + headred-snd
subject-conv1 (ty-Snd dA dB dM) (headred-snd hr) =
  conv-Snd dA dB (subject-conv1 dM hr)

-- Snd + headred-beta-snd
-- conv-beta-snd gives ConvTm at (subst1 B M), but we need it at (subst1 B (Fst (MkPair M N)))
subject-conv1 (ty-Snd dA dB dMkP) headred-beta-snd =
  let mkSigma dM dN = ty-MkPair-components dMkP (conv-refl (ty-Sigma dA dB)) dA dB
      htMkP = ty-MkPair dA dB dM dN
      cvFst = conv-beta-fst dA dB dM dN  -- ConvTm G (Fst (MkPair M N)) M A
      cvType = subst1-cong-ConvTm dA dB (ty-Fst dA dB htMkP) dM cvFst
      -- cvType : ConvTm G (subst1 B (Fst (MkPair M N))) (subst1 B M) U
      cvBeta = conv-beta-snd dA dB dM dN  -- ConvTm G (Snd (MkPair M N)) N (subst1 B M)
      dBFstMkP = subst-HasType (subst1-WtSub dA (ty-Fst dA dB htMkP)) (typing-WfCtx dA) dB
  in conv-conv cvBeta (conv-sym cvType) dBFstMkP
