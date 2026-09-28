{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.StripUniq
--
-- Lemma 4.17/4.18 for U : U: the annotations of T_R are redundant.
--
--   If Γ ⊢ u0 : T0 and Γ ⊢ u1 : T1 in T_R with strip u0 = strip u1,
--   then Γ ⊢ T0 = T1 and Γ ⊢ u0 = u1 : T0.
--
-- With a single universe there is no cumulativity, so types are unique
-- up to conversion and the paper's induction on the term goes through
-- as it stands (compare ERT.Gap417 / ERT.StripUniqNF for the
-- cumulative hierarchy).  The only non-syntactic ingredient is
-- Π-injectivity (ERTUU.PiInjectivityR, from adequacy of the domain
-- model).  No normalisation: T_P with U : U does not normalise.
------------------------------------------------------------------------

module ERTUU.StripUniq where

open import ERTUU.Basic
open import ERTUU.RussellSyntax
open import ERTUU.RussellTyping
open import ERTUU.RussellMeta
open import ERTUU.RussellMetaCong using (subst1-cong-Ty)
open import ERTUU.PiInjectivityR using (PiInj-R)
open import ERTUU.Model.Strip using (strip)
import ERTUU.Model.Core as C

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  C-App-inj : {n : Nat} {c c' a a' : C.Expr n} -> Eq (C.App c a) (C.App c' a') -> Pair (Eq c c') (Eq a a')
  C-App-inj refl = mkSigma refl refl

  C-Lam-inj : {n : Nat} {A A' : C.Expr n} {b b' : C.Expr (suc n)} -> Eq (C.Lam A b) (C.Lam A' b') -> Pair (Eq A A') (Eq b b')
  C-Lam-inj refl = mkSigma refl refl

  C-Pi-inj : {n : Nat} {A A' : C.Expr n} {B B' : C.Expr (suc n)} -> Eq (C.Pi A B) (C.Pi A' B') -> Pair (Eq A A') (Eq B B')
  C-Pi-inj refl = mkSigma refl refl

------------------------------------------------------------------------
-- Inversion (no cumulativity: the type is determined up to conversion)
------------------------------------------------------------------------

inv-Var : {n : Nat} {G : Ctx n} {i : Fin n} {T : Expr n} ->
  HasType G (Var i) T -> Pair (WfCtx G) (ConvTy G (lookup G i) T)
inv-Var (ty-var {i = i} wf) = mkSigma wf (conv-Ty-refl (wfCtx-lookup wf i))
inv-Var (ty-conv d c)       = let r = inv-Var d in mkSigma (fst r) (conv-Ty-trans (snd r) c)

inv-U : {n : Nat} {G : Ctx n} {T : Expr n} -> HasType G U T -> Pair (WfCtx G) (ConvTy G U T)
inv-U (ty-U wf)     = mkSigma wf (conv-Ty-refl (isType-U wf))
inv-U (ty-conv d c) = let r = inv-U d in mkSigma (fst r) (conv-Ty-trans (snd r) c)

record InvPi {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvPi
  field
    dA  : HasType G A U
    dB  : HasType (extend G A) B U
    cnv : ConvTy G U T

inv-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {T : Expr n} ->
  HasType G (Pi A B) T -> InvPi G A B T
inv-Pi (ty-Pi dA dB) = mkInvPi dA dB (conv-Ty-refl (isType-U (typing-WfCtx dA)))
inv-Pi (ty-conv d c) = let r = inv-Pi d in mkInvPi (InvPi.dA r) (InvPi.dB r) (conv-Ty-trans (InvPi.cnv r) c)

record InvLam {n : Nat} (G : Ctx n) (A : Expr n) (B b : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvLam
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    db  : HasType (extend G A) b B
    cnv : ConvTy G (Pi A B) T

inv-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {T : Expr n} ->
  HasType G (Lam A B b) T -> InvLam G A B b T
inv-Lam (ty-Lam dA dB db) = mkInvLam dA dB db (conv-Ty-refl (isType-Pi dA dB))
inv-Lam (ty-conv d c) = let r = inv-Lam d in
  mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r) (conv-Ty-trans (InvLam.cnv r) c)

record InvApp {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (c a T : Expr n) : Set where
  constructor mkInvApp
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    dc  : HasType G c (Pi A B)
    da  : HasType G a A
    cnv : ConvTy G (subst1 B a) T

inv-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a T : Expr n} ->
  HasType G (App A B c a) T -> InvApp G A B c a T
inv-App (ty-App dA dB dc da) =
  mkInvApp dA dB dc da (conv-Ty-refl (subst-IsType (subst1-WtSub dA da) (isType-WfCtx dA) dB))
inv-App (ty-conv d c) = let r = inv-App d in
  mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r) (conv-Ty-trans (InvApp.cnv r) c)

------------------------------------------------------------------------
-- The lemma, by structural induction on the term
------------------------------------------------------------------------

mutual

  uniq : {n : Nat} {G : Ctx n} (u0 u1 : Expr n) {T0 T1 : Expr n} ->
    Eq (strip u0) (strip u1) -> HasType G u0 T0 -> HasType G u1 T1 ->
    Pair (ConvTy G T0 T1) (ConvTm G u0 u1 T0)
  -- variables
  uniq (Var i) (Var .i) refl d0 d1 =
    let r0 = inv-Var d0 ; r1 = inv-Var d1
    in mkSigma (conv-Ty-trans (conv-Ty-sym (snd r0)) (snd r1)) (conv-refl d0)
  uniq (Var _) U ()
  uniq (Var _) (Pi _ _) ()
  uniq (Var _) (Lam _ _ _) ()
  uniq (Var _) (App _ _ _ _) ()
  -- the universe
  uniq U U refl d0 d1 =
    mkSigma (conv-Ty-trans (conv-Ty-sym (snd (inv-U d0))) (snd (inv-U d1))) (conv-refl d0)
  uniq U (Var _) ()
  uniq U (Pi _ _) ()
  uniq U (Lam _ _ _) ()
  uniq U (App _ _ _ _) ()
  -- products
  uniq (Pi A0 B0) (Pi A1 B1) e d0 d1 =
    let inj  = C-Pi-inj e
        p0   = inv-Pi d0 ; p1 = inv-Pi d1
        dA0  = InvPi.dA p0 ; dA1 = InvPi.dA p1
        eA   = snd (uniq A0 A1 (fst inj) dA0 dA1)
        cA   = conv-Ty-from-U eA
        dB1' = ctx-conv-HasType (is-Ty-from-U dA1) (is-Ty-from-U dA0) (conv-Ty-sym cA) (InvPi.dB p1)
        eB   = snd (uniq B0 B1 (snd inj) (InvPi.dB p0) dB1')
        cT   = conv-Ty-trans (conv-Ty-sym (InvPi.cnv p0)) (InvPi.cnv p1)
    in mkSigma cT (conv-conv (conv-cong-Pi dA0 (InvPi.dB p0) eA eB) (InvPi.cnv p0))
  uniq (Pi _ _) (Var _) ()
  uniq (Pi _ _) U ()
  uniq (Pi _ _) (Lam _ _ _) ()
  uniq (Pi _ _) (App _ _ _ _) ()
  -- abstractions
  uniq (Lam A0 B0 b0) (Lam A1 B1 b1) e d0 d1 =
    let inj  = C-Lam-inj e
        l0   = inv-Lam d0 ; l1 = inv-Lam d1
        dA0  = InvLam.dA l0 ; dB0 = InvLam.dB l0 ; db0 = InvLam.db l0
        dA1  = InvLam.dA l1
        cA   = tyEq A0 A1 (fst inj) dA0 dA1
        db1' = ctx-conv-HasType dA1 dA0 (conv-Ty-sym cA) (InvLam.db l1)
        rb   = uniq b0 b1 (snd inj) db0 db1'                    -- B0 = B1, b0 = b1 : B0
        cB   = fst rb
        step1 = conv-cong-Lam-body dA0 dB0 db0 (snd rb)
        step2 = conv-cong-Lam-Ty dA0 dB0 cA cB (ty-conv db1' (conv-Ty-sym cB))
        cPi  = conv-Ty-Pi dA0 dB0 cA cB
        cT   = conv-Ty-trans (conv-Ty-sym (InvLam.cnv l0)) (conv-Ty-trans cPi (InvLam.cnv l1))
    in mkSigma cT (conv-conv (conv-trans step1 step2) (InvLam.cnv l0))
  uniq (Lam _ _ _) (Var _) ()
  uniq (Lam _ _ _) U ()
  uniq (Lam _ _ _) (Pi _ _) ()
  uniq (Lam _ _ _) (App _ _ _ _) ()
  -- applications: the annotations are forced by the type of the function
  uniq (App C0 D0 c0 a0) (App C1 D1 c1 a1) e d0 d1 =
    let inj   = C-App-inj e
        i0    = inv-App d0 ; i1 = inv-App d1
        dC0   = InvApp.dA i0 ; dD0 = InvApp.dB i0
        rc    = uniq c0 c1 (fst inj) (InvApp.dc i0) (InvApp.dc i1)
        pinj  = PiInj-R (fst rc)
        cC    = fst pinj ; cD = snd pinj
        cf    = snd rc                                           -- c0 = c1 : Π(C0,D0)
        da1'  = ty-conv (InvApp.da i1) (conv-Ty-sym cC)
        ca    = snd (uniq a0 a1 (snd inj) (InvApp.da i0) da1')   -- a0 = a1 : C0
        df1'  = presup-r-ConvTm cf
        cDa   = subst1-cong-Ty ca dC0 dD0
        step1 = conv-cong-App-fun dC0 dD0 cf (InvApp.da i0)
        step2 = conv-cong-App-arg dC0 dD0 df1' ca cDa
        step3 = conv-conv (conv-cong-App-Ty dC0 dD0 cC cD df1' da1') (conv-Ty-sym cDa)
        cDD   = conv-Ty-trans cDa (subst-ConvTy (subst1-WtSub dC0 da1') (isType-WfCtx dC0) cD)
        cT    = conv-Ty-trans (conv-Ty-sym (InvApp.cnv i0)) (conv-Ty-trans cDD (InvApp.cnv i1))
    in mkSigma cT (conv-conv (conv-trans step1 (conv-trans step2 step3)) (InvApp.cnv i0))
  uniq (App _ _ _ _) (Var _) ()
  uniq (App _ _ _ _) U ()
  uniq (App _ _ _ _) (Pi _ _) ()
  uniq (App _ _ _ _) (Lam _ _ _) ()

  tyEq : {n : Nat} {G : Ctx n} (A0 A1 : Expr n) ->
    Eq (strip A0) (strip A1) -> IsType G A0 -> IsType G A1 -> ConvTy G A0 A1
  tyEq A0 A1 e (is-Ty-from-U d0) (is-Ty-from-U d1) = conv-Ty-from-U (snd (uniq A0 A1 e d0 d1))

------------------------------------------------------------------------
-- Lemma 4.18 (same interface as ERT.StripUniqNF)
------------------------------------------------------------------------

type-uniq-NF : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
  IsType G A0 -> IsType G A1 -> Eq (strip A0) (strip A1) -> ConvTy G A0 A1
type-uniq-NF {A0 = A0} {A1 = A1} d0 d1 e = tyEq A0 A1 e d0 d1

-- no hypothesis on the types is needed: they are unique up to conversion
term-uniq : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) ->
  Pair (ConvTy G A0 A1) (ConvTm G u0 u1 A0)
term-uniq {u0 = u0} {u1 = u1} d0 d1 e = uniq u0 u1 e d0 d1

term-uniq-conv-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> ConvTy G A0 A1 ->
  ConvTm G u0 u1 A0
term-uniq-conv-NF d0 d1 e _ = snd (term-uniq d0 d1 e)

term-uniq-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> Eq (strip A0) (strip A1) ->
  Pair (ConvTy G A0 A1) (ConvTm G u0 u1 A0)
term-uniq-NF d0 d1 eu _ = term-uniq d0 d1 eu
