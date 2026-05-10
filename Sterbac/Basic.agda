{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.Basic
--
-- Minimal prelude for the Sterbac equivalence formalisation.
-- All purely syntactic; no postulates, no domain theory, no type-in-type.
------------------------------------------------------------------------

module Sterbac.Basic where

------------------------------------------------------------------------
-- Top, Empty
------------------------------------------------------------------------

data Top : Set where
  tt : Top

data Empty : Set where

absurd : {A : Set} -> Empty -> A
absurd ()

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

infixl 20 _+_
_+_ : Nat -> Nat -> Nat
zero  + n = n
suc m + n = suc (m + n)

------------------------------------------------------------------------
-- Finite sets (de Bruijn variables)
------------------------------------------------------------------------

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Renamings (shared by all syntaxes)
------------------------------------------------------------------------

Ren : Nat -> Nat -> Set
Ren n m = Fin n -> Fin m

liftRen : {n m : Nat} -> Ren n m -> Ren (suc n) (suc m)
liftRen r fzero    = fzero
liftRen r (fsuc i) = fsuc (r i)

wkRen : {n : Nat} -> Ren n (suc n)
wkRen i = fsuc i

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

Eq-sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
Eq-sym refl = refl

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans refl q = q

Eq-cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
Eq-cong f refl = refl

Eq-cong2 : {A B C : Set} (f : A -> B -> C)
  {x x' : A} {y y' : B} -> Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
Eq-cong2 f refl refl = refl

Eq-cong3 : {A B C D : Set} (f : A -> B -> C -> D)
  {x x' : A} {y y' : B} {z z' : C}
  -> Eq x x' -> Eq y y' -> Eq z z' -> Eq (f x y z) (f x' y' z')
Eq-cong3 f refl refl refl = refl

Eq-cong4 : {A B C D E : Set} (f : A -> B -> C -> D -> E)
  {x x' : A} {y y' : B} {z z' : C} {w w' : D}
  -> Eq x x' -> Eq y y' -> Eq z z' -> Eq w w' -> Eq (f x y z w) (f x' y' z' w')
Eq-cong4 f refl refl refl refl = refl

Eq-transport : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
Eq-transport P refl px = px

------------------------------------------------------------------------
-- Sigma / pair
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
-- Sums
------------------------------------------------------------------------

data Either (A B : Set) : Set where
  inl : A -> Either A B
  inr : B -> Either A B

------------------------------------------------------------------------
-- Order on naturals
------------------------------------------------------------------------

Le : Nat -> Nat -> Set
Le zero    n       = Top
Le (suc m) zero    = Empty
Le (suc m) (suc n) = Le m n

Le-refl : (n : Nat) -> Le n n
Le-refl zero    = tt
Le-refl (suc n) = Le-refl n

Le-suc : (m n : Nat) -> Le m n -> Le m (suc n)
Le-suc zero    n       _ = tt
Le-suc (suc m) zero    ()
Le-suc (suc m) (suc n) h = Le-suc m n h

Le-trans : (l m n : Nat) -> Le l m -> Le m n -> Le l n
Le-trans zero    m       n       _ _  = tt
Le-trans (suc l) zero    n       () _
Le-trans (suc l) (suc m) zero    _ ()
Le-trans (suc l) (suc m) (suc n) p q  = Le-trans l m n p q

Lt : Nat -> Nat -> Set
Lt m n = Le (suc m) n

max : Nat -> Nat -> Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

Le-max-l : (m n : Nat) -> Le m (max m n)
Le-max-l zero    n       = tt
Le-max-l (suc m) zero    = Le-refl m
Le-max-l (suc m) (suc n) = Le-max-l m n

Le-max-r : (m n : Nat) -> Le n (max m n)
Le-max-r zero    n       = Le-refl n
Le-max-r (suc m) zero    = tt
Le-max-r (suc m) (suc n) = Le-max-r m n
