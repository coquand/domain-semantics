{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.TarskiTyping
--
-- Typing and βη-conversion for the Tarski-style theory with ONE universe
-- containing its own code (U : U, the type-in-type version of T_T).
--
--   * U is a type only; its code is the term UCode : U.
--   * El a is the type decoded from a code a : U.
--   * PiCode a b : U codes Π (El a) (El b).
--
-- The judgemental equations:
--   El UCode          =  U
--   El (PiCode a b)   =  Π (El a) (El b)
--
-- The binder congruences carry the left presupposition of the domain
-- as a premise (admissible; keeps renaming/substitution structural).
------------------------------------------------------------------------

module ERTUU.TarskiTyping where

open import ERTUU.Basic
open import ERTUU.TarskiSyntax

data Ctx : Nat -> Set where
  empty  : Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

data WfCtx   : {n : Nat} -> Ctx n -> Set
data IsType  : {n : Nat} -> Ctx n -> Expr n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTy  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> WfCtx (extend G A)

data IsType where
  is-Ty-U : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> IsType G U
  is-Ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (Pi A B)
  is-Ty-El : {n : Nat} {G : Ctx n} {a : Expr n}
    -> HasType G a U
    -> IsType G (El a)

data HasType where
  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTy G A B
    -> HasType G M B
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G (Lam A B b) (Pi A B)
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> HasType G (App A B c a) (subst1 B a)
  ty-PiCode : {n : Nat} {G : Ctx n} {a : Expr n} {b : Expr (suc n)}
    -> HasType G a U
    -> HasType (extend G (El a)) b U
    -> HasType G (PiCode a b) U
  ty-UCode : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G UCode U

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
  conv-Ty-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> ConvTy G (Pi A B) (Pi A' B')
  conv-Ty-El : {n : Nat} {G : Ctx n} {a a' : Expr n}
    -> ConvTm G a a' U
    -> ConvTy G (El a) (El a')
  conv-Ty-El-UCode : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> ConvTy G (El UCode) U
  conv-Ty-El-PiCode : {n : Nat} {G : Ctx n}
    {a : Expr n} {b : Expr (suc n)}
    -> HasType G a U
    -> HasType (extend G (El a)) b U
    -> ConvTy G (El (PiCode a b)) (Pi (El a) (El b))

data ConvTm where
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
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTy G A B
    -> ConvTm G M N B
  conv-cong-Lam-body : {n : Nat} {G : Ctx n}
    {A : Expr n} {B b b' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm (extend G A) b b' B
    -> ConvTm G (Lam A B b) (Lam A B b') (Pi A B)
  conv-cong-Lam-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' b : Expr (suc n)}
    -> IsType G A
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
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)
  conv-cong-PiCode : {n : Nat} {G : Ctx n}
    {a a' : Expr n} {b b' : Expr (suc n)}
    -> HasType G a U
    -> ConvTm G a a' U
    -> ConvTm (extend G (El a)) b b' U
    -> ConvTm G (PiCode a b) (PiCode a' b') U
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G a A
    -> ConvTm G (App A B (Lam A B b) a) (subst1 b a) (subst1 B a)
  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G c
       (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B)
                     (wkExpr c) (Var fzero)))
       (Pi A B)
