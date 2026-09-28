{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Basic.agda  (MIN/ — Pi + U fragment only)
--
-- Basic types, finite elements, and rank for the domain model.
-- No Sigma, no Prop.
-- No postulates.
------------------------------------------------------------------------

module ERTUU.Dom.Basic where

------------------------------------------------------------------------
-- Basic types: shared with the rest of ERT (same Nat, Eq, Sigma),
-- so that universe levels in the model and in the syntax coincide.
------------------------------------------------------------------------

open import ERTUU.Basic public
  using ( Top ; tt ; Empty ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; Sigma ; mkSigma ; fst ; snd ; Pair )

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

------------------------------------------------------------------------
-- All: predicate holding for every element of a list
------------------------------------------------------------------------

All : {A : Set} -> (A -> Set) -> List A -> Set
All P nil         = Top
All P (cons x xs) = Pair (P x) (All P xs)

------------------------------------------------------------------------
-- Finite elements and finite functions
-- (Pi + U fragment only.)
------------------------------------------------------------------------

mutual
  data FinEl : Set where
    Bot      : FinEl
    UCode    : Nat -> FinEl         -- the universe U_l (level l)
    FunEl    : FinFun -> FinEl
    PiCode   : FinEl -> FinFun -> FinEl

  FinFun : Set
  FinFun = List (Pair FinEl FinEl)

------------------------------------------------------------------------
-- Rank (cf. paper Section 2)
------------------------------------------------------------------------

mutual
  rk : FinEl -> Nat
  rk Bot            = 0
  rk (UCode _)      = 0
  rk (FunEl g)      = rkFun g
  rk (PiCode a f)   = suc (max (rk a) (rkFun f))

  rkFun : FinFun -> Nat
  rkFun nil         = 0
  rkFun (cons p xs) = suc (max (rk (fst p)) (max (rk (snd p)) (rkFun xs)))

------------------------------------------------------------------------
-- Misc helpers
------------------------------------------------------------------------

min : Nat -> Nat -> Nat
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

isPos : Nat -> Set
isPos zero    = Empty
isPos (suc n) = Top

min-isPos : (m n : Nat) -> isPos (min m n) -> Pair (isPos m) (isPos n)
min-isPos zero    n       ()
min-isPos (suc m) zero    ()
min-isPos (suc m) (suc n) _ = mkSigma tt tt

pair-eq : {A : Set} {B : Set} {a1 a2 : A} {b1 b2 : B} ->
  Eq a1 a2 -> Eq b1 b2 -> Eq (mkSigma {B = \ _ -> B} a1 b1) (mkSigma a2 b2)
pair-eq refl refl = refl

cons-eq : {p q : Pair FinEl FinEl} {ps qs : FinFun} ->
  Eq p q -> Eq ps qs -> Eq (cons p ps) (cons q qs)
cons-eq refl refl = refl

-- The universe used as the TYPE of codes in membership statements.
-- Membership ignores the level of a universe (typing in the model is
-- U:U-like); only the order compares levels.
U0 : FinEl
U0 = UCode 0

------------------------------------------------------------------------
-- Level equality, as a proposition (EqL) and as a 0/1 test (eqL).
-- The order on FinEl compares the levels of universes with these.
------------------------------------------------------------------------

EqL : Nat -> Nat -> Set
EqL zero    zero    = Top
EqL zero    (suc m) = Empty
EqL (suc k) zero    = Empty
EqL (suc k) (suc m) = EqL k m

eqL : Nat -> Nat -> Nat
eqL zero    zero    = suc zero
eqL zero    (suc m) = zero
eqL (suc k) zero    = zero
eqL (suc k) (suc m) = eqL k m

EqL-refl : (k : Nat) -> EqL k k
EqL-refl zero    = tt
EqL-refl (suc k) = EqL-refl k

EqL-sym : (k m : Nat) -> EqL k m -> EqL m k
EqL-sym zero    zero    e = tt
EqL-sym zero    (suc m) ()
EqL-sym (suc k) zero    ()
EqL-sym (suc k) (suc m) e = EqL-sym k m e

EqL-trans : (k m p : Nat) -> EqL k m -> EqL m p -> EqL k p
EqL-trans zero    zero    p       e1 e2 = e2
EqL-trans zero    (suc m) p       ()
EqL-trans (suc k) zero    p       ()
EqL-trans (suc k) (suc m) zero    e1 ()
EqL-trans (suc k) (suc m) (suc p) e1 e2 = EqL-trans k m p e1 e2

EqL-Eq : (k m : Nat) -> EqL k m -> Eq k m
EqL-Eq zero    zero    e = refl
EqL-Eq zero    (suc m) ()
EqL-Eq (suc k) zero    ()
EqL-Eq (suc k) (suc m) e = Eq-cong suc (EqL-Eq k m e)

eqL-refl : (k : Nat) -> Eq (eqL k k) (suc zero)
eqL-refl zero    = refl
eqL-refl (suc k) = eqL-refl k

-- eqL k m is 1 exactly when EqL k m holds (isPos (eqL k m) <-> EqL k m).
eqL-EqL : (k m : Nat) -> isPos (eqL k m) -> EqL k m
eqL-EqL zero    zero    p = tt
eqL-EqL zero    (suc m) ()
eqL-EqL (suc k) zero    ()
eqL-EqL (suc k) (suc m) p = eqL-EqL k m p

EqL-eqL : (k m : Nat) -> EqL k m -> isPos (eqL k m)
EqL-eqL zero    zero    e = tt
EqL-eqL zero    (suc m) ()
EqL-eqL (suc k) zero    ()
EqL-eqL (suc k) (suc m) e = EqL-eqL k m e
