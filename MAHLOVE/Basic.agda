{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOVE/Basic.agda
--
-- The identity type and its basic operations (the part of MAHLO/Basic
-- used here), so that MAHLOVE builds on its own.
------------------------------------------------------------------------

module MAHLOVE.Basic where

data Eq {A : Set} (a : A) : A -> Set where
  refl : Eq a a

Eq-sym : {A : Set} {a b : A} -> Eq a b -> Eq b a
Eq-sym refl = refl

Eq-trans : {A : Set} {a b c : A} -> Eq a b -> Eq b c -> Eq a c
Eq-trans refl e = e

Eq-cong : {A B : Set} (h : A -> B) {a b : A} -> Eq a b -> Eq (h a) (h b)
Eq-cong h refl = refl
