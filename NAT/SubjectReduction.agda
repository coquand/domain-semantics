{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SubjectReduction.agda  (NAT/ — Pi + U fragment)
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

module NAT.SubjectReduction where

open import NAT.Domain.Basic using ( Nat ; suc ; mkSigma ; fst ; snd ; Pair ; Eq-transport )
open import NAT.Syntax.Raw using ( Expr ; U ; Pi ; Lam ; App ; NatT ; Zero ; Suc ; Case ; Y ;
  wkExpr ; subst1 ; subSucC ; subSucC-subst1 )
open import NAT.Syntax.Typing using
  ( Ctx ; extend ; HasType ; ConvTm
  ; ty-conv ; ty-Pi ; ty-Lam ; ty-App ; ty-NatT ; ty-Suc ; ty-Case ; ty-Case-dep ; ty-Y
  ; conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-beta ; conv-Y ; conv-App-fun
  ; conv-Case ; conv-Case-dep ; conv-case-zero ; conv-case-suc
  ; conv-case-zero-dep ; conv-case-suc-dep )
open import NAT.Syntax.Reduction using ( HeadRed1 ; headred-beta ; headred-app ; headred-Y
  ; headred-case-zero ; headred-case-suc ; headred-case )
open import NAT.Syntax.Substitution using
  ( typing-WfCtx ; subst-HasType ; subst-ConvTm ; subst1-WtSub ; subst1-wk ; wk-HasType
  ; subst1-cong-ConvTm ; ty-subst1-motive ; codSubSucC
  ; ctx-conv-HasType ; ctx-conv-ConvTm )
open import NAT.PiInjectivity using ( piInjectivity )

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
-- Suc scrutinee inversion (through conversion): Suc m : T => m : NatT.
------------------------------------------------------------------------

ty-Suc-arg : {n : Nat} {G : Ctx n} {m : Expr n} {T : Expr n} ->
  HasType G (Suc m) T -> HasType G m NatT
ty-Suc-arg (ty-Suc dm)     = dm
ty-Suc-arg (ty-conv d _ _) = ty-Suc-arg d

------------------------------------------------------------------------
-- beta-conv : the conversion witnessing one beta step at the App level,
-- inverting the Lam typing through any conversion (mirrors ty-Lam-body).
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
-- term's type.  (Reduction is contained in conversion.)  Used by the
-- dependent caseNat scrutinee-reduction clause, whose result type
-- subst1 C M must be transported along M ~ M'.  Structural; the beta case
-- delegates to beta-conv.
------------------------------------------------------------------------

headred1-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  HasType G M A -> HeadRed1 M N -> ConvTm G M N A
headred1-conv (ty-conv d dConv dT) hr =
  conv-conv (headred1-conv d hr) dConv dT
headred1-conv (ty-App dA dB df da) (headred-app hr) =
  conv-App-fun dA dB (headred1-conv df hr) da
headred1-conv (ty-App dA0 dB0 df da0) headred-beta =
  beta-conv df (conv-refl (ty-Pi dA0 dB0)) dA0 dB0 da0
headred1-conv (ty-Y {A = A} {g = g} aU dg) headred-Y =
  conv-Y aU dg
headred1-conv (ty-Case dC dM da db) headred-case-zero =
  conv-case-zero dC da db
headred1-conv (ty-Case dC dM da db) headred-case-suc =
  conv-case-suc dC (ty-Suc-arg dM) da db
headred1-conv (ty-Case dC dM da db) (headred-case hr) =
  conv-Case dC (headred1-conv dM hr) (conv-refl da) (conv-refl db)
headred1-conv (ty-Case-dep dC dM da db) headred-case-zero =
  conv-case-zero-dep dC da db
headred1-conv (ty-Case-dep dC dM da db) headred-case-suc =
  conv-case-suc-dep dC (ty-Suc-arg dM) da db
headred1-conv (ty-Case-dep dC dM da db) (headred-case hr) =
  conv-Case-dep dC (headred1-conv dM hr) (conv-refl da) (conv-refl db)

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

-- ty-Case + headred-case-zero: Case Zero a b -> a, typed by the zero branch.
subject-red1 (ty-Case dC dM da db) headred-case-zero = da

-- ty-Case + headred-case-suc: Case (Suc m) a b -> App b m; invert the scrutinee
-- typing to m : Nat, then App b m : subst1 (wkExpr C) m = C.
subject-red1 (ty-Case {C = C} dC dM da db) (headred-case-suc {m = m}) =
  let dm = ty-Suc-arg dM
  in Eq-transport (\ T -> HasType _ (App _ m) T) (subst1-wk C m)
       (ty-App (ty-NatT (typing-WfCtx dC)) (wk-HasType (ty-NatT (typing-WfCtx dC)) dC) db dm)

-- ty-Case + headred-case: the scrutinee reduces.
subject-red1 (ty-Case dC dM da db) (headred-case hr) =
  ty-Case dC (subject-red1 dM hr) da db

-- ty-Y + headred-Y: Y g -> App g (Y g) : subst1 (wkExpr A) (Y g) = A.
subject-red1 (ty-Y {A = A} {g = g} aU dg) headred-Y =
  Eq-transport (\ T -> HasType _ (App g (Y g)) T) (subst1-wk A (Y g))
    (ty-App aU (wk-HasType aU aU) dg (ty-Y aU dg))

-- ty-Case-dep + headred-case-zero: Case Zero a b -> a : subst1 C Zero.
subject-red1 (ty-Case-dep dC dM da db) headred-case-zero = da

-- ty-Case-dep + headred-case-suc: Case (Suc m) a b -> App b m;
--   App b m : subst1 (subSucC C) m = subst1 C (Suc m).
subject-red1 (ty-Case-dep {C = C} dC dM da db) (headred-case-suc {m = m}) =
  Eq-transport (\ T -> HasType _ (App _ m) T) (subSucC-subst1 C m)
    (ty-App (ty-NatT (typing-WfCtx dM)) (codSubSucC dC) db (ty-Suc-arg dM))

-- ty-Case-dep + headred-case: the scrutinee reduces M -> M'; the dependent
-- result type subst1 C M is transported along the scrutinee conversion M ~ M'.
subject-red1 (ty-Case-dep {C = C} dC dM da db) (headred-case hr) =
  let dM'   = subject-red1 dM hr
      cvM'M = subst1-cong-ConvTm (ty-NatT (typing-WfCtx dM)) dC dM' dM
                (conv-sym (headred1-conv dM hr))
  in ty-conv (ty-Case-dep dC dM' da db) cvM'M (ty-subst1-motive dC dM)
