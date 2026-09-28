{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.RussellTyping
--
-- Typing and βη-conversion for the Russell-style theory T_R.
--
-- Five mutually defined judgements:
--
--   WfCtx   G            "Γ ctx"
--   IsType  G A          "Γ ⊢ A type"
--   HasType G M A        "Γ ⊢ M : A"
--   ConvTy  G A B        "Γ ⊢ A = B"
--   ConvTm  G M N A      "Γ ⊢ M = N : A"
--
-- One universe, U : U (type in type).
--
-- λ and app keep their (A,B) annotations.
------------------------------------------------------------------------

module ERTUU.RussellTyping where

open import ERTUU.Basic
open import ERTUU.RussellSyntax

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data Ctx : Nat -> Set where
  empty  : Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

------------------------------------------------------------------------
-- Judgement forms (mutual)
------------------------------------------------------------------------

data WfCtx   : {n : Nat} -> Ctx n -> Set
data IsType  : {n : Nat} -> Ctx n -> Expr n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTy  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

------------------------------------------------------------------------
-- WfCtx
------------------------------------------------------------------------

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- IsType  ("Γ ⊢ A type")
--
--   Γ ⊢ A : U
--   ────────────
--   Γ ⊢ A type
------------------------------------------------------------------------

data IsType where
  is-Ty-from-U : {n : Nat} {G : Ctx n} {A : Expr n}
    -> HasType G A U
    -> IsType G A

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

data HasType where

  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  -- type conversion uses ConvTy, not ConvTm
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTy G A B
    -> HasType G M B

  -- U : U
  ty-U : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G U U

  -- Γ ⊢ A : U   Γ.A ⊢ B : U
  -- ───────────────────────────────
  -- Γ ⊢ Π(A,B) : U
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G (Pi A B) U

  -- Γ ⊢ A type   Γ.A ⊢ B type   Γ.A ⊢ b : B
  -- ──────────────────────────────────────────────
  -- Γ ⊢ λ(A,B,b) : Π(A,B)
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G (Lam A B b) (Pi A B)

  -- Γ ⊢ A type   Γ.A ⊢ B type   Γ ⊢ c : Π(A,B)   Γ ⊢ a : A
  -- ────────────────────────────────────────────────────────────
  -- Γ ⊢ app(A,B,c,a) : B[a]
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
           {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> HasType G (App A B c a) (subst1 B a)

------------------------------------------------------------------------
-- ConvTy  ("Γ ⊢ A = B")
--
-- Inherits all structure from ConvTm at U, plus its own equivalence
-- rules so we can manipulate type-equality without naming a level.
------------------------------------------------------------------------

data ConvTy where
  conv-Ty-refl : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> ConvTy G A A

  conv-Ty-sym : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B
    -> ConvTy G B A

  conv-Ty-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
    -> ConvTy G A B
    -> ConvTy G B C
    -> ConvTy G A C

  -- congruence for Π at the type level.  The binder congruences (here,
  -- conv-cong-Pi, conv-cong-Lam-body, conv-cong-Lam-Ty) carry the
  -- typings of the LEFT-hand components as extra premises.  These are
  -- presuppositions (admissible: see the mk-* rules of RussellMeta,
  -- which have the paper's premises only); having them as subderivations
  -- keeps the metatheory and the adequacy proof structurally recursive.
  conv-Ty-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> ConvTy G (Pi A B) (Pi A' B')

  -- A = B : U  ⇒  A = B
  conv-Ty-from-U : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTm G A B U
    -> ConvTy G A B

------------------------------------------------------------------------
-- ConvTm  (judgemental βη conversion)
------------------------------------------------------------------------

data ConvTm where

  -- equivalence
  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A
    -> ConvTm G M M A

  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N M A

  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N P A
    -> ConvTm G M P A

  -- propagate type equality on the type of the conversion
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTy G A B
    -> ConvTm G M N B

  -- congruence rules
  conv-cong-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G (Pi A B) (Pi A' B') U

  -- Lam / App congruences split (matches Tarski).
  conv-cong-Lam-body : {n : Nat} {G : Ctx n}
    {A : Expr n} {B b b' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> ConvTm (extend G A) b b' B
    -> ConvTm G (Lam A B b) (Lam A B b') (Pi A B)

  conv-cong-Lam-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType (extend G A) b B
    -> ConvTm G (Lam A B b) (Lam A' B' b) (Pi A B)

  conv-cong-App-fun : {n : Nat} {G : Ctx n}
    {A : Expr n} {B : Expr (suc n)} {c c' a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm G c c' (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A B c' a) (subst1 B a)

  conv-cong-App-arg : {n : Nat} {G : Ctx n}
    {A : Expr n} {B : Expr (suc n)} {c a a' : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G a a' A
    -> ConvTy G (subst1 B a) (subst1 B a')
    -> ConvTm G (App A B c a) (App A B c a') (subst1 B a)

  conv-cong-App-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)} {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)

  -- β
  -- app(A,B, λ(A,B,b), a) = b[a] : B[a]
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
              {a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G a A
    -> ConvTm G (App A B (Lam A B b) a) (subst1 b a) (subst1 B a)

  -- η
  -- c = λ(A,B, app(A↑, B↑, c↑, v_0)) : Π(A,B)
  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
             {c : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G c
       (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B)
                     (wkExpr c) (Var fzero)))
       (Pi A B)
