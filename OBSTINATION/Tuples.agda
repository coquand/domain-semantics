{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Tuples
--
-- n-tuples of domain elements, Section 1: A in D^n, the coordinate
-- A(i) = get i A, the (n-1)-tuple A[i] = dropAt i A, and the pointwise
-- order A <= B.  Tuples are plain Lists (no length index); the arity n,
-- when needed, is `length A`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Tuples where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain

------------------------------------------------------------------------
-- Tuples
------------------------------------------------------------------------

Tup : Set
Tup = List D

FTup : Set
FTup = List FEl

-- coordinate A(i)  (default bot for out-of-range, never used in range)
get : Nat -> Tup -> D
get i A = nth botD i A

-- the (n-1)-tuple A[i]
dropAt : Nat -> Tup -> Tup
dropAt i A = del i A

------------------------------------------------------------------------
-- Pointwise order  A <= B  (Empty on a length mismatch)
------------------------------------------------------------------------

LeTup : Tup -> Tup -> Set
LeTup nil         nil         = Top
LeTup nil         (cons _ _)  = Empty
LeTup (cons _ _)  nil         = Empty
LeTup (cons x xs) (cons y ys) = Pair (LeD x y) (LeTup xs ys)

LeTup-refl : (A : Tup) -> LeTup A A
LeTup-refl nil         = tt
LeTup-refl (cons x xs) = mkSigma (LeD-refl x) (LeTup-refl xs)

LeTup-trans : {A B C : Tup} -> LeTup A B -> LeTup B C -> LeTup A C
LeTup-trans {nil}      {nil}      {nil}      p q = tt
LeTup-trans {nil}      {nil}      {cons _ _} p ()
LeTup-trans {nil}      {cons _ _} {C}        () q
LeTup-trans {cons _ _} {nil}      {C}        () q
LeTup-trans {cons _ _} {cons _ _} {nil}      p ()
LeTup-trans {cons x xs} {cons y ys} {cons z zs} p q =
  mkSigma (LeD-trans {x} {y} {z} (fst p) (fst q))
          (LeTup-trans {xs} {ys} {zs} (snd p) (snd q))

-- pointwise order respects coordinate projection
LeTup-get : (i : Nat) {A B : Tup} -> LeTup A B -> LeD (get i A) (get i B)
LeTup-get i       {nil}       {nil}       p = LeD-refl botD
LeTup-get i       {nil}       {cons _ _}  ()
LeTup-get i       {cons _ _}  {nil}       ()
LeTup-get zero    {cons x xs} {cons y ys} p = fst p
LeTup-get (suc i) {cons x xs} {cons y ys} p = LeTup-get i {xs} {ys} (snd p)

------------------------------------------------------------------------
-- Finiteness of tuples
------------------------------------------------------------------------

FiniteTup : Tup -> Set
FiniteTup nil         = Top
FiniteTup (cons x xs) = Pair (Finite x) (FiniteTup xs)

-- a tuple of finite elements embeds to a finite tuple of D
embedTup : FTup -> Tup
embedTup nil         = nil
embedTup (cons x xs) = cons (embed x) (embedTup xs)

FiniteTup-embed : (A : FTup) -> FiniteTup (embedTup A)
FiniteTup-embed nil         = tt
FiniteTup-embed (cons x xs) = mkSigma (Finite-embed x) (FiniteTup-embed xs)

------------------------------------------------------------------------
-- Pointwise order on finite tuples
------------------------------------------------------------------------

LeFTup : FTup -> FTup -> Set
LeFTup A B = LeTup (embedTup A) (embedTup B)

LeFTup-refl : (A : FTup) -> LeFTup A A
LeFTup-refl A = LeTup-refl (embedTup A)
