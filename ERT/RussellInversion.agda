{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.RussellInversion
--
-- Inversion of T_R typing in the presence of cumulativity.  A typing
-- derivation ends with its "principal" rule followed by conversions and
-- cumulativity steps; the latter are summarised by the relation
--
--   SubTy G P T :=  Γ ⊢ P = T
--               or Γ ⊢ P = U_k and Γ ⊢ T = U_m with k ≤ m.
--
-- Uses injectivity of universes and Π/U no-confusion, both from the
-- soundness of the domain model.
------------------------------------------------------------------------

module ERT.RussellInversion where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.Model.Strip using (strip ; stripCtx)
open import ERT.Model.RussellSound using (sound-CTy)
open import ERT.Model.EvalSubstitution using (botEnv)
open import ERT.PiInjectivityR using (botEnv-fits ; evalRel-Pi-bot)
import ERT.Dom.Basic as D

------------------------------------------------------------------------
-- Injectivity of universes, Π/U no-confusion (soundness of the model)
------------------------------------------------------------------------

U-inj-R : {n : Nat} {G : Ctx n} {m k : Nat} -> ConvTy G (U m) (U k) -> Eq m k
U-inj-R {G = G} {m = m} {k = k} d =
  let fwd = fst (snd (snd (sound-CTy d botEnv (botEnv-fits G))))
  in D.EqL-Eq m k (snd (fwd (D.UCode m) (mkSigma tt (D.EqL-refl m))))

Pi-U-noconf : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {m : Nat} ->
  ConvTy G (Pi A B) (U m) -> Empty
Pi-U-noconf {G = G} {A = A} {B = B} d =
  let fwd = fst (snd (snd (sound-CTy d botEnv (botEnv-fits G))))
  in snd (fwd (D.PiCode D.Bot D.nil) (evalRel-Pi-bot (strip A) (strip B) botEnv))

------------------------------------------------------------------------
-- The relation SubTy
------------------------------------------------------------------------

data SubTy {n : Nat} (G : Ctx n) (P T : Expr n) : Set where
  sub-conv : ConvTy G P T -> SubTy G P T
  sub-cum  : (k m : Nat) -> Le k m -> ConvTy G P (U k) -> ConvTy G T (U m) -> SubTy G P T

Sub-refl : {n : Nat} {G : Ctx n} {P : Expr n} -> IsType G P -> SubTy G P P
Sub-refl dP = sub-conv (conv-Ty-refl dP)

Sub-conv-right : {n : Nat} {G : Ctx n} {P T T' : Expr n} -> SubTy G P T -> ConvTy G T T' -> SubTy G P T'
Sub-conv-right (sub-conv c)          c' = sub-conv (conv-Ty-trans c c')
Sub-conv-right (sub-cum k m le cP cT) c' = sub-cum k m le cP (conv-Ty-trans (conv-Ty-sym c') cT)

Sub-conv-left : {n : Nat} {G : Ctx n} {P P' T : Expr n} -> ConvTy G P' P -> SubTy G P T -> SubTy G P' T
Sub-conv-left c' (sub-conv c)          = sub-conv (conv-Ty-trans c' c)
Sub-conv-left c' (sub-cum k m le cP cT) = sub-cum k m le (conv-Ty-trans c' cP) cT

private
  Le-cong : {k m l : Nat} -> Eq m l -> Le k m -> Le k l
  Le-cong refl h = h

-- one cumulativity step on the right
Sub-cum : {n : Nat} {G : Ctx n} {P : Expr n} {l : Nat} -> SubTy G P (U l) -> SubTy G P (U (suc l))
Sub-cum {l = l} (sub-conv c) =
  sub-cum l (suc l) (Le-suc l l (Le-refl l)) c
    (conv-Ty-refl (isType-U (isType-WfCtx (presup-r-ConvTy c))))
Sub-cum {l = l} (sub-cum k m le cP cT) =
  sub-cum k (suc l) (Le-suc k l (Le-cong {k = k} (Eq-sym (U-inj-R cT)) le)) cP
    (conv-Ty-refl (isType-U (isType-WfCtx (presup-r-ConvTy cT))))

-- a product is only below itself
Sub-Pi : {n : Nat} {G : Ctx n} {P A : Expr n} {B : Expr (suc n)} -> SubTy G P (Pi A B) -> ConvTy G P (Pi A B)
Sub-Pi (sub-conv c)           = c
Sub-Pi (sub-cum k m le cP cT) = absurd (Pi-U-noconf cT)

-- moving a typing / a conversion up along Sub
lift-HasType : {n : Nat} {G : Ctx n} {M P T : Expr n} -> HasType G M P -> SubTy G P T -> HasType G M T
lift-HasType d (sub-conv c)           = ty-conv d c
lift-HasType d (sub-cum k m le cP cT) = ty-conv (cum-le k m le (ty-conv d cP)) (conv-Ty-sym cT)

lift-ConvTm : {n : Nat} {G : Ctx n} {M N P T : Expr n} -> ConvTm G M N P -> SubTy G P T -> ConvTm G M N T
lift-ConvTm d (sub-conv c)           = conv-conv d c
lift-ConvTm d (sub-cum k m le cP cT) = conv-conv (cum-le-Tm k m le (conv-conv d cP)) (conv-Ty-sym cT)

------------------------------------------------------------------------
-- Inversion lemmas
------------------------------------------------------------------------

inv-Var : {n : Nat} {G : Ctx n} {i : Fin n} {T : Expr n} ->
  HasType G (Var i) T -> Pair (WfCtx G) (SubTy G (lookup G i) T)
inv-Var (ty-var {i = i} wf) = mkSigma wf (Sub-refl (wfCtx-lookup wf i))
inv-Var (ty-conv d c)       = let r = inv-Var d in mkSigma (fst r) (Sub-conv-right (snd r) c)
inv-Var (ty-cum d)          = let r = inv-Var d in mkSigma (fst r) (Sub-cum (snd r))

inv-U : {n : Nat} {G : Ctx n} {l : Nat} {T : Expr n} ->
  HasType G (U l) T -> Pair (WfCtx G) (SubTy G (U (suc l)) T)
inv-U (ty-U wf)     = mkSigma wf (Sub-refl (isType-U wf))
inv-U (ty-conv d c) = let r = inv-U d in mkSigma (fst r) (Sub-conv-right (snd r) c)
inv-U (ty-cum d)    = let r = inv-U d in mkSigma (fst r) (Sub-cum (snd r))

record InvPi {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvPi
  field
    lvl : Nat
    dA  : HasType G A (U lvl)
    dB  : HasType (extend G A) B (U lvl)
    sub : SubTy G (U lvl) T

inv-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {T : Expr n} ->
  HasType G (Pi A B) T -> InvPi G A B T
inv-Pi (ty-Pi {l = l} dA dB) = mkInvPi l dA dB (Sub-refl (isType-U (typing-WfCtx dA)))
inv-Pi (ty-conv d c) = let r = inv-Pi d in
  mkInvPi (InvPi.lvl r) (InvPi.dA r) (InvPi.dB r) (Sub-conv-right (InvPi.sub r) c)
inv-Pi (ty-cum d) = let r = inv-Pi d in
  mkInvPi (InvPi.lvl r) (InvPi.dA r) (InvPi.dB r) (Sub-cum (InvPi.sub r))

record InvLam {n : Nat} (G : Ctx n) (A : Expr n) (B b : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvLam
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    db  : HasType (extend G A) b B
    sub : SubTy G (Pi A B) T

inv-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {T : Expr n} ->
  HasType G (Lam A B b) T -> InvLam G A B b T
inv-Lam (ty-Lam dA dB db) = mkInvLam dA dB db (Sub-refl (isType-Pi dA dB))
inv-Lam (ty-conv d c) = let r = inv-Lam d in
  mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r) (Sub-conv-right (InvLam.sub r) c)
inv-Lam (ty-cum d) = let r = inv-Lam d in
  mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r) (Sub-cum (InvLam.sub r))

record InvApp {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (c a T : Expr n) : Set where
  constructor mkInvApp
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    dc  : HasType G c (Pi A B)
    da  : HasType G a A
    sub : SubTy G (subst1 B a) T

inv-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a T : Expr n} ->
  HasType G (App A B c a) T -> InvApp G A B c a T
inv-App (ty-App dA dB dc da) =
  mkInvApp dA dB dc da (Sub-refl (subst-IsType (subst1-WtSub dA da) (isType-WfCtx dA) dB))
inv-App (ty-conv d c) = let r = inv-App d in
  mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r) (Sub-conv-right (InvApp.sub r) c)
inv-App (ty-cum d) = let r = inv-App d in
  mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r) (Sub-cum (InvApp.sub r))
