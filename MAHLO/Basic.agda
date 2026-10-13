{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Basic.agda
--
-- Minimal prelude for the MAHLO development (phase P1 of
-- mahlo-plan.tex): empty type, identity type, Sigma, sum.
------------------------------------------------------------------------

module MAHLO.Basic where

data Empty : Set where

Empty-elim : {A : Set} -> Empty -> A
Empty-elim ()

data Eq {A : Set} (a : A) : A -> Set where
  refl : Eq a a

Eq-sym : {A : Set} {a b : A} -> Eq a b -> Eq b a
Eq-sym refl = refl

Eq-trans : {A : Set} {a b c : A} -> Eq a b -> Eq b c -> Eq a c
Eq-trans refl e = e

Eq-cong : {A B : Set} (h : A -> B) {a b : A} -> Eq a b -> Eq (h a) (h b)
Eq-cong h refl = refl

transport : {A : Set} (P : A -> Set) {a b : A} -> Eq a b -> P a -> P b
transport P refl p = p

transport2 : {A B : Set} (P : A -> B -> Set) {a a' : A} {b b' : B} ->
             Eq a a' -> Eq b b' -> P a b -> P a' b'
transport2 P refl refl p = p

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Sigma public

infixr 4 _,_
infixr 2 _*_

_*_ : Set -> Set -> Set
A * B = Sigma A (\ _ -> B)

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B
