{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.PTyping
--
-- The unannotated Russell theory T_P (paper, appendix A.4): the closest
-- presentation of T_R as a pure type system with a cumulative
-- hierarchy.  Its syntax is the core syntax of the model
-- (ERTUU.Model.Core):
--
--   A, B, a, b ::= v_i | Π A B | U_n | λ A b | c a
--
-- i.e. λ keeps its domain, application keeps nothing, and
-- ERTUU.Model.Strip.strip : T_R -> T_P forgets the annotations.
--
-- The rules are those of T_R (ERTUU.RussellTyping) with the
-- annotations removed.  As in T_R, the binder rules carry the typings of
-- the domain / codomain as (admissible, presupposition) premises; they
-- make the section of strip (ERTUU.SectionR, Thm 4.19) structural.
------------------------------------------------------------------------

module ERTUU.PTyping where

open import ERTUU.Basic using (Nat ; zero ; suc ; Fin ; fzero ; fsuc ; liftRen ; wkRen)
open import ERTUU.Model.Core

data WfCtx   : {n : Nat} -> Ctx n -> Set
data IsType  : {n : Nat} -> Ctx n -> Expr n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTy  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx (extend G A)

data IsType where
  is-Ty-from-U : {n : Nat} {G : Ctx n} {A : Expr n} ->
    HasType G A (U 0) -> IsType G A

data HasType where
  ty-var : {n : Nat} {G : Ctx n} {i : Fin n} ->
    WfCtx G -> HasType G (Var i) (lookup G i)
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n} ->
    HasType G M A -> ConvTy G A B -> HasType G M B
  ty-U : {n : Nat} {G : Ctx n} ->
    WfCtx G -> HasType G (U 0) (U 0)
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
    HasType G A (U 0) -> HasType (extend G A) B (U 0) -> HasType G (Pi A B) (U 0)
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B ->
    HasType (extend G A) b B -> HasType G (Lam A b) (Pi A B)
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a : Expr n} ->
    IsType G A -> IsType (extend G A) B ->
    HasType G c (Pi A B) -> HasType G a A -> HasType G (App c a) (subst1 B a)

data ConvTy where
  conv-Ty-refl : {n : Nat} {G : Ctx n} {A : Expr n} ->
    IsType G A -> ConvTy G A A
  conv-Ty-sym : {n : Nat} {G : Ctx n} {A B : Expr n} ->
    ConvTy G A B -> ConvTy G B A
  conv-Ty-trans : {n : Nat} {G : Ctx n} {A B C : Expr n} ->
    ConvTy G A B -> ConvTy G B C -> ConvTy G A C
  conv-Ty-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' -> ConvTy G (Pi A B) (Pi A' B')
  conv-Ty-from-U : {n : Nat} {G : Ctx n} {A B : Expr n} ->
    ConvTm G A B (U 0) -> ConvTy G A B

data ConvTm where
  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n} ->
    HasType G M A -> ConvTm G M M A
  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A -> ConvTm G N M A
  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n} ->
    ConvTm G M N A -> ConvTm G N P A -> ConvTm G M P A
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n} ->
    ConvTm G M N A -> ConvTy G A B -> ConvTm G M N B
  conv-cong-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
    HasType G A (U 0) -> HasType (extend G A) B (U 0) -> ConvTm G A A' (U 0) -> ConvTm (extend G A) B B' (U 0) ->
    ConvTm G (Pi A B) (Pi A' B') (U 0)
  conv-cong-Lam-body : {n : Nat} {G : Ctx n} {A : Expr n} {B b b' : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
    ConvTm (extend G A) b b' B -> ConvTm G (Lam A b) (Lam A b') (Pi A B)
  conv-cong-Lam-dom : {n : Nat} {G : Ctx n} {A A' : Expr n} {B b : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> HasType (extend G A) b B -> ConvTm G (Lam A b) (Lam A' b) (Pi A B)
  conv-cong-App-fun : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c c' a : Expr n} ->
    IsType G A -> IsType (extend G A) B -> ConvTm G c c' (Pi A B) -> HasType G a A -> ConvTm G (App c a) (App c' a) (subst1 B a)
  conv-cong-App-arg : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a a' : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> ConvTm G a a' A -> ConvTm G (App c a) (App c a') (subst1 B a)
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {a : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B -> HasType G a A ->
    ConvTm G (App (Lam A b) a) (subst1 b a) (subst1 B a)
  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) ->
    ConvTm G c (Lam A (App (wkExpr c) (Var fzero))) (Pi A B)
