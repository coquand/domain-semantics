{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BasicSigma.agda
--
-- Basic types, finite elements with Sigma/Pair codes, and rank.
-- Parallel version of Basic.agda extended with SigmaCode and PairCode.
-- No postulates.
------------------------------------------------------------------------

module BasicSigma where

------------------------------------------------------------------------
-- Basic types
------------------------------------------------------------------------

data Top : Set where
  tt : Top

data Empty : Set where

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

-- Nat is shared with Basic.agda to avoid a "Duplicate binding for
-- built-in thing NATURAL" error whenever a consumer ends up importing
-- both modules in the same import graph. We re-export Basic.Nat (and
-- its constructors) here so BasicSigma.Nat keeps numeric-literal sugar
-- without redeclaring the BUILTIN.
open import Basic public using (Nat ; zero ; suc)

max : Nat -> Nat -> Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

Le : Nat -> Nat -> Set
Le zero    n       = Top
Le (suc m) zero    = Empty
Le (suc m) (suc n) = Le m n

Le-refl : (n : Nat) -> Le n n
Le-refl zero    = tt
Le-refl (suc n) = Le-refl n

Le-suc : (m n : Nat) -> Le m n -> Le m (suc n)
Le-suc zero    n       h = tt
Le-suc (suc m) zero    ()
Le-suc (suc m) (suc n) h = Le-suc m n h

Le-trans : (l m n : Nat) -> Le l m -> Le m n -> Le l n
Le-trans zero    m       n       h1 h2 = tt
Le-trans (suc l) zero    n       ()
Le-trans (suc l) (suc m) zero    h1 ()
Le-trans (suc l) (suc m) (suc n) h1 h2 = Le-trans l m n h1 h2

Le-max-l : (m n : Nat) -> Le m (max m n)
Le-max-l zero    n       = tt
Le-max-l (suc m) zero    = Le-refl m
Le-max-l (suc m) (suc n) = Le-max-l m n

Le-max-r : (m n : Nat) -> Le n (max m n)
Le-max-r zero    n       = Le-refl n
Le-max-r (suc m) zero    = tt
Le-max-r (suc m) (suc n) = Le-max-r m n

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

Eq-transport : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
Eq-transport P refl px = px

Eq-sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
Eq-sym refl = refl

Eq-cong : {A : Set} {B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
Eq-cong f refl = refl

------------------------------------------------------------------------
-- Sigma types and pairs
------------------------------------------------------------------------

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst

open Sigma public

Pair : Set -> Set -> Set
Pair A B = Sigma A (\ _ -> B)

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
--
-- Extended with SigmaCode and PairCode.
------------------------------------------------------------------------

mutual
  data FinEl : Set where
    Bot       : FinEl
    UCode     : FinEl
    PropCode  : FinEl
    FunEl     : FinFun -> FinEl
    PiCode    : FinEl -> FinFun -> FinEl
    SigmaCode : FinEl -> FinFun -> FinEl
    PairCode  : FinEl -> FinEl -> FinEl

  FinFun : Set
  FinFun = List (Pair FinEl FinEl)

------------------------------------------------------------------------
-- Rank (cf. paper Section 2)
------------------------------------------------------------------------

mutual
  rk : FinEl -> Nat
  rk Bot            = 0
  rk UCode          = 0
  rk PropCode       = 0
  rk (FunEl g)      = rkFun g
  rk (PiCode a f)   = suc (max (rk a) (rkFun f))
  rk (SigmaCode a f) = suc (max (rk a) (rkFun f))
  rk (PairCode u v) = suc (max (rk u) (rk v))

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

------------------------------------------------------------------------
-- Code projections (for uniform Sigma validity)
------------------------------------------------------------------------

codeFst : FinEl -> FinEl
codeFst (PairCode u v) = u
codeFst Bot = Bot
codeFst UCode = Bot
codeFst PropCode = Bot
codeFst (FunEl g) = Bot
codeFst (PiCode a f) = Bot
codeFst (SigmaCode a f) = Bot

codeSnd : FinEl -> FinEl
codeSnd (PairCode u v) = v
codeSnd Bot = Bot
codeSnd UCode = Bot
codeSnd PropCode = Bot
codeSnd (FunEl g) = Bot
codeSnd (PiCode a f) = Bot
codeSnd (SigmaCode a f) = Bot
