{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- RawSyntax.agda
--
-- Raw syntax with de Bruijn indices, renamings, and unary substitution.
-- No semantics, no typing rules.
------------------------------------------------------------------------

module RawSyntax where

open import Basic using (Nat ; zero ; suc)

------------------------------------------------------------------------
-- Fin — de Bruijn variables
------------------------------------------------------------------------

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Expr — raw expressions
------------------------------------------------------------------------

data Expr : Nat -> Set where
  Var : {n : Nat} -> Fin n -> Expr n
  U   : {n : Nat} -> Expr n
  Pi  : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  Lam : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  App : {n : Nat} -> Expr n -> Expr n -> Expr n

------------------------------------------------------------------------
-- Ren — renamings
------------------------------------------------------------------------

Ren : Nat -> Nat -> Set
Ren n m = Fin n -> Fin m

liftRen : {n m : Nat} -> Ren n m -> Ren (suc n) (suc m)
liftRen r fzero    = fzero
liftRen r (fsuc i) = fsuc (r i)

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)   = Var (r i)
renExpr r U         = U
renExpr r (Pi A B)  = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A M) = Lam (renExpr r A) (renExpr (liftRen r) M)
renExpr r (App f a) = App (renExpr r f) (renExpr r a)

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

wkRen : {n : Nat} -> Ren n (suc n)
wkRen i = fsuc i

wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

------------------------------------------------------------------------
-- General (parallel) substitution
------------------------------------------------------------------------

Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub sigma fzero    = Var fzero
liftSub sigma (fsuc i) = wkExpr (sigma i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr sigma (Var i)   = sigma i
substExpr sigma U         = U
substExpr sigma (Pi A B)  = Pi (substExpr sigma A) (substExpr (liftSub sigma) B)
substExpr sigma (Lam A M) = Lam (substExpr sigma A) (substExpr (liftSub sigma) M)
substExpr sigma (App f a) = App (substExpr sigma f) (substExpr sigma a)

------------------------------------------------------------------------
-- Unary substitution (defined via general substitution)
------------------------------------------------------------------------

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub s fzero    = s
subst1Sub s (fsuc i) = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 M s = substExpr (subst1Sub s) M
