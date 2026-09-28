{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.PReduction
--
-- β-reduction (at any position) on the unannotated syntax T_P, β-normal
-- forms, and the weak normalisation hypothesis used in §4.3:
--
--   WN-P : every term typable in T_P β-reduces to a β-normal form.
------------------------------------------------------------------------

module ERT.PReduction where

open import ERT.Basic using (Nat ; suc ; Fin ; Sigma ; Pair ; mkSigma)
open import ERT.Model.Core
import ERT.PTyping as P

data Step : {n : Nat} -> Expr n -> Expr n -> Set where
  st-beta : {n : Nat} {A : Expr n} {b : Expr (suc n)} {a : Expr n} ->
    Step (App (Lam A b) a) (subst1 b a)
  st-app-l : {n : Nat} {c c' a : Expr n} -> Step c c' -> Step (App c a) (App c' a)
  st-app-r : {n : Nat} {c a a' : Expr n} -> Step a a' -> Step (App c a) (App c a')
  st-lam-d : {n : Nat} {A A' : Expr n} {b : Expr (suc n)} -> Step A A' -> Step (Lam A b) (Lam A' b)
  st-lam-b : {n : Nat} {A : Expr n} {b b' : Expr (suc n)} -> Step b b' -> Step (Lam A b) (Lam A b')
  st-pi-d  : {n : Nat} {A A' : Expr n} {B : Expr (suc n)} -> Step A A' -> Step (Pi A B) (Pi A' B)
  st-pi-c  : {n : Nat} {A : Expr n} {B B' : Expr (suc n)} -> Step B B' -> Step (Pi A B) (Pi A B')

data Star {n : Nat} : Expr n -> Expr n -> Set where
  st-refl : {M : Expr n} -> Star M M
  st-step : {M N K : Expr n} -> Step M N -> Star N K -> Star M K

-- β-normal and neutral terms
data Ne : {n : Nat} -> Expr n -> Set
data Nf : {n : Nat} -> Expr n -> Set

data Ne where
  ne-var : {n : Nat} {i : Fin n} -> Ne (Var i)
  ne-app : {n : Nat} {c a : Expr n} -> Ne c -> Nf a -> Ne (App c a)

data Nf where
  nf-ne  : {n : Nat} {M : Expr n} -> Ne M -> Nf M
  nf-lam : {n : Nat} {A : Expr n} {b : Expr (suc n)} -> Nf A -> Nf b -> Nf (Lam A b)
  nf-pi  : {n : Nat} {A : Expr n} {B : Expr (suc n)} -> Nf A -> Nf B -> Nf (Pi A B)
  nf-U   : {n l : Nat} -> Nf {n} (U l)

-- The hypothesis: weak β-normalisation of the typable terms of T_P.
WN-P : Set
WN-P = {n : Nat} {G : Ctx n} {M A : Expr n} -> P.HasType G M A ->
  Sigma (Expr n) (\ N -> Pair (Star M N) (Nf N))
