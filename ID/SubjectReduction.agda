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

module ID.SubjectReduction where

open import ID.Domain.Basic using ( Nat ; suc ; mkSigma ; fst ; snd ; Pair )
open import ID.Syntax.Raw using ( Expr ; U ; Pi ; Lam ; App ; J ; Ref ; Id
  ; subst1 ; motiveTy ; baseTy )
open import ID.Syntax.Typing using
  ( Ctx ; extend ; HasType ; ConvTm
  ; ty-conv ; ty-Pi ; ty-Lam ; ty-App ; ty-J ; ty-Id ; ty-Ref
  ; conv-refl ; conv-trans ; conv-sym ; conv-conv ; conv-beta ; conv-App-fun
  ; conv-J ; conv-J-beta )
open import ID.Syntax.Reduction using
  ( HeadRed1 ; headred-beta ; headred-app ; headred-J ; headred-J-scrut )
open import ID.Syntax.Substitution using
  ( typing-WfCtx ; subst-HasType ; subst-ConvTm ; subst1-WtSub ; typing-ConvTm
  ; ty-baseBody ; ty-motiveApp3 ; conv-motiveApp3
  ; ctx-conv-HasType ; ctx-conv-ConvTm )
open import ID.PiInjectivity using ( piInjectivity )
open import ID.Adequacy.JApp using ( conv-App3-endpoints )
open import ID.RefEndpoints using ( ty-Ref-endpoints )

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
-- based-J beta conversion (shared by red1-conv and subject-red1).
--
-- With the proof forced to a literal Ref (p = Ref a0), the J-redex
-- converts to its contractum at the goal type App³ C a b (Ref a0):
--   conv-J-beta gives it at App³ C a0 a0 (Ref a0);
--   ty-Ref-endpoints (a0≅a, a0≅b) + conv-App3-endpoints retype the two
--   endpoints back to a,b.
------------------------------------------------------------------------

jbetaConv : {n : Nat} {G : Ctx n} {A a b C d a0 : Expr n} ->
  HasType G A U -> HasType G a A -> HasType G b A ->
  HasType G C (motiveTy A) -> HasType G d (baseTy A C) ->
  HasType G (Ref a0) (Id A a b) ->
  ConvTm G (J C d (Ref a0)) (App d a0) (App (App (App C a) b) (Ref a0))
jbetaConv dA da db dC dd dp =
  let mkSigma ca0a ca0b = ty-Ref-endpoints dp (conv-refl (ty-Id dA da db)) dA
      da0 = fst (typing-ConvTm ca0a)
      convApp3 = conv-App3-endpoints dA dC da0 da da0 db (ty-Ref dA da0) ca0a ca0b
  in conv-conv (conv-J-beta dA da0 dC dd) convApp3 (ty-motiveApp3 dA dC da db dp)

------------------------------------------------------------------------
-- beta-conv : the conversion witnessing one beta step at the App level,
-- inverting the Lam typing through any conversion (mirrors ty-Lam-body,
-- ported from NAT.SubjectReduction).
------------------------------------------------------------------------

beta-conv : {n : Nat} {G : Ctx n}
  {A' a : Expr n} {M' : Expr (suc n)} {T : Expr n} {A0 : Expr n} {B0 : Expr (suc n)} ->
  HasType G (Lam A' M') T -> ConvTm G T (Pi A0 B0) U ->
  HasType G A0 U -> HasType (extend G A0) B0 U -> HasType G a A0 ->
  ConvTm G (App (Lam A' M') a) (subst1 M' a) (subst1 B0 a)
beta-conv {a = a} (ty-Lam dA' dB' dMb) conv dA0 dB0 da0 =
  let mkSigma cvA cvB = piInjectivity conv
      da'   = ty-conv da0 (conv-sym cvA) dA'
      betaP = conv-beta dA' dB' dMb da'
      cvBa  = subst-ConvTm (subst1-WtSub dA' da') (typing-WfCtx dA') cvB
      dB0a  = subst-HasType (subst1-WtSub dA0 da0) (typing-WfCtx dA0) dB0
  in conv-conv betaP cvBa dB0a
beta-conv (ty-conv d dConv' _) conv dA0 dB0 da0 =
  beta-conv d (conv-trans dConv' conv) dA0 dB0 da0

------------------------------------------------------------------------
-- headred1-conv : a single head-reduction step is a conversion at the
-- term's type.  Used by subject-red1's J-scrut case to retype the reduced
-- proof (result type App³ C a b p transported along p ~ p').
------------------------------------------------------------------------

headred1-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> ConvTm G M N A
headred1-conv (ty-conv d dConv dT) hr =
  conv-conv (headred1-conv d hr) dConv dT
headred1-conv (ty-App dA dB df da) (headred-app hr) =
  conv-App-fun dA dB (headred1-conv df hr) da
headred1-conv (ty-App dA0 dB0 df da0) headred-beta =
  beta-conv df (conv-refl (ty-Pi dA0 dB0)) dA0 dB0 da0
headred1-conv (ty-J dA da db dC dd dp) headred-J =
  jbetaConv dA da db dC dd dp
headred1-conv (ty-J dA da db dC dd dp) (headred-J-scrut hr) =
  conv-J dA da db dC dd dp (conv-refl dC) (conv-refl dd) (headred1-conv dp hr)

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

-- ty-J + headred-J (beta, p = Ref a0): the contractum App d a0 typed at
-- the goal type App³ C a b (Ref a0) is the RHS presupposition of jbetaConv.
subject-red1 (ty-J dA da db dC dd dp) headred-J =
  snd (typing-ConvTm (jbetaConv dA da db dC dd dp))

-- ty-J + headred-J-scrut (proof p -> p'): retype J C d p' back from
-- App³ C a b p' to App³ C a b p via conv-motiveApp3 (proof p' ≅ p).
subject-red1 (ty-J dA da db dC dd dp) (headred-J-scrut hr) =
  let dp'  = subject-red1 dp hr
      cP'P = conv-sym (headred1-conv dp hr)
      cvTy = conv-motiveApp3 dA dC dC (conv-refl dC) da db dp' cP'P
  in ty-conv (ty-J dA da db dC dd dp') cvTy (ty-motiveApp3 dA dC da db dp)
