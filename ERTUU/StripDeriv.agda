{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.StripDeriv  —  paper Theorem 4.15
--
--   If Γ ⊢ J in T_R, then strip(Γ) ⊢ strip(J) in T_P.
--
-- By structural induction on the T_R derivation: every T_R rule strips
-- to a T_P rule (the presupposition premises of T_R are dropped), except
-- conv-cong-App-Ty, whose two sides have the same stripping and which
-- therefore strips to reflexivity.
------------------------------------------------------------------------

module ERTUU.StripDeriv where

open import ERTUU.Basic using (Nat ; suc ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport ; fzero)
import ERTUU.RussellSyntax as R
import ERTUU.RussellTyping as RT
import ERTUU.Model.Core as C
import ERTUU.PTyping as P
open import ERTUU.Model.Strip

private
  -- move a T_P judgement along equalities of its components
  tyM : {n : Nat} {G : C.Ctx n} {M A A' : C.Expr n} -> Eq A A' -> P.HasType G M A -> P.HasType G M A'
  tyM refl d = d

  cvM : {n : Nat} {G : C.Ctx n} {M M' N N' A A' : C.Expr n} ->
    Eq M M' -> Eq N N' -> Eq A A' -> P.ConvTm G M N A -> P.ConvTm G M' N' A'
  cvM refl refl refl d = d

mutual

  strip-WfCtx : {n : Nat} {G : RT.Ctx n} -> RT.WfCtx G -> P.WfCtx (stripCtx G)
  strip-WfCtx RT.wf-empty       = P.wf-empty
  strip-WfCtx (RT.wf-extend dA) = P.wf-extend (strip-IsType dA)

  strip-IsType : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} ->
    RT.IsType G A -> P.IsType (stripCtx G) (strip A)
  strip-IsType (RT.is-Ty-from-U d) = P.is-Ty-from-U (strip-HasType d)

  strip-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n} ->
    RT.HasType G M A -> P.HasType (stripCtx G) (strip M) (strip A)
  strip-HasType {G = G} (RT.ty-var {i = i} wf) =
    tyM (Eq-sym (strip-lookup G i)) (P.ty-var (strip-WfCtx wf))
  strip-HasType (RT.ty-conv d c)           = P.ty-conv (strip-HasType d) (strip-ConvTy c)
  strip-HasType (RT.ty-U wf)               = P.ty-U (strip-WfCtx wf)
  strip-HasType (RT.ty-Pi dA dB)           = P.ty-Pi (strip-HasType dA) (strip-HasType dB)
  strip-HasType (RT.ty-Lam dA dB db)       = P.ty-Lam (strip-IsType dA) (strip-IsType dB) (strip-HasType db)
  strip-HasType (RT.ty-App {B = B} {a = a} dA dB dc da) =
    tyM (Eq-sym (strip-subst1 B a)) (P.ty-App (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-HasType da))

  strip-ConvTy : {n : Nat} {G : RT.Ctx n} {A B : R.Expr n} ->
    RT.ConvTy G A B -> P.ConvTy (stripCtx G) (strip A) (strip B)
  strip-ConvTy (RT.conv-Ty-refl dA)      = P.conv-Ty-refl (strip-IsType dA)
  strip-ConvTy (RT.conv-Ty-sym d)        = P.conv-Ty-sym (strip-ConvTy d)
  strip-ConvTy (RT.conv-Ty-trans d1 d2)  = P.conv-Ty-trans (strip-ConvTy d1) (strip-ConvTy d2)
  strip-ConvTy (RT.conv-Ty-Pi dA dB cA cB) = P.conv-Ty-Pi (strip-IsType dA) (strip-IsType dB) (strip-ConvTy cA) (strip-ConvTy cB)
  strip-ConvTy (RT.conv-Ty-from-U d)     = P.conv-Ty-from-U (strip-ConvTm d)

  strip-ConvTm : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n} ->
    RT.ConvTm G M N A -> P.ConvTm (stripCtx G) (strip M) (strip N) (strip A)
  strip-ConvTm (RT.conv-refl d)       = P.conv-refl (strip-HasType d)
  strip-ConvTm (RT.conv-sym d)        = P.conv-sym (strip-ConvTm d)
  strip-ConvTm (RT.conv-trans d1 d2)  = P.conv-trans (strip-ConvTm d1) (strip-ConvTm d2)
  strip-ConvTm (RT.conv-conv d c)     = P.conv-conv (strip-ConvTm d) (strip-ConvTy c)
  strip-ConvTm (RT.conv-cong-Pi dA dB cA cB) =
    P.conv-cong-Pi (strip-HasType dA) (strip-HasType dB) (strip-ConvTm cA) (strip-ConvTm cB)
  strip-ConvTm (RT.conv-cong-Lam-body dA dB db0 db) =
    P.conv-cong-Lam-body (strip-IsType dA) (strip-IsType dB) (strip-HasType db0) (strip-ConvTm db)
  strip-ConvTm (RT.conv-cong-Lam-Ty dA dB cA _ db) =
    P.conv-cong-Lam-dom (strip-IsType dA) (strip-IsType dB) (strip-ConvTy cA) (strip-HasType db)
  strip-ConvTm (RT.conv-cong-App-fun {B = B} {a = a} dA dB dc da) =
    cvM refl refl (Eq-sym (strip-subst1 B a))
      (P.conv-cong-App-fun (strip-IsType dA) (strip-IsType dB) (strip-ConvTm dc) (strip-HasType da))
  strip-ConvTm (RT.conv-cong-App-arg {B = B} {a = a} dA dB dc da _) =
    cvM refl refl (Eq-sym (strip-subst1 B a))
      (P.conv-cong-App-arg (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-ConvTm da))
  strip-ConvTm (RT.conv-cong-App-Ty {B = B} {a = a} dA dB _ _ dc da) =
    P.conv-refl (tyM (Eq-sym (strip-subst1 B a))
      (P.ty-App (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-HasType da)))
  strip-ConvTm (RT.conv-beta {B = B} {b = b} {a = a} dA dB db da) =
    cvM refl (Eq-sym (strip-subst1 b a)) (Eq-sym (strip-subst1 B a))
      (P.conv-beta (strip-IsType dA) (strip-IsType dB) (strip-HasType db) (strip-HasType da))
  strip-ConvTm (RT.conv-eta {A = A} {c = c} dA dB dc) =
    cvM refl (Eq-cong (\ X -> C.Lam (strip A) (C.App X (C.Var fzero))) (Eq-sym (strip-wk c))) refl
      (P.conv-eta (strip-IsType dA) (strip-IsType dB) (strip-HasType dc))
