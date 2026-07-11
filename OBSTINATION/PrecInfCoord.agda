{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfCoord
--
-- Coordinate bookkeeping lemmas for the infinite-recursion dispatch:
-- monotonicity of deletion, commutation of deletion with the embedding,
-- and the length facts relating a UO approximant's tail to the point.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfCoord where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF)

------------------------------------------------------------------------
-- Deletion is monotone on tuples
------------------------------------------------------------------------

LeTup-del : (i : Nat) {A B : Tup} -> LeTup A B -> LeTup (del i A) (del i B)
LeTup-del i       {nil}       {nil}       le = tt
LeTup-del i       {nil}       {cons _ _}  ()
LeTup-del i       {cons _ _}  {nil}       ()
LeTup-del zero    {cons x xs} {cons y ys} le = snd le
LeTup-del (suc i) {cons x xs} {cons y ys} le = mkSigma (fst le) (LeTup-del i {xs} {ys} (snd le))

-- deletion commutes with the embedding
del-embedTup : (i : Nat) (A : FTup) -> Eq (embedTup (del i A)) (del i (embedTup A))
del-embedTup i       nil         = refl
del-embedTup zero    (cons x xs) = refl
del-embedTup (suc i) (cons x xs) = Eq-cong (cons (embed x)) (del-embedTup i xs)

LeFTup-del : (i : Nat) {A B : FTup} -> LeFTup A B -> LeFTup (del i A) (del i B)
LeFTup-del i {A} {B} le =
  Eq-transport (\ W -> LeTup W (embedTup (del i B))) (Eq-sym (del-embedTup i A))
    (Eq-transport (\ W -> LeTup (del i (embedTup A)) W) (Eq-sym (del-embedTup i B))
      (LeTup-del i {embedTup A} {embedTup B} le))

------------------------------------------------------------------------
-- Length facts
------------------------------------------------------------------------

length-embedTup : (A : FTup) -> Eq (length (embedTup A)) (length A)
length-embedTup nil         = refl
length-embedTup (cons x xs) = Eq-cong suc (length-embedTup xs)

-- a pointwise order forces equal length
LeTup-length : {A B : Tup} -> LeTup A B -> Eq (length A) (length B)
LeTup-length {nil}      {nil}      le = refl
LeTup-length {nil}      {cons _ _} ()
LeTup-length {cons _ _} {nil}      ()
LeTup-length {cons x xs} {cons y ys} le = Eq-cong suc (LeTup-length {xs} {ys} (snd le))

LeFTup-length : {A B : FTup} -> LeFTup A B -> Eq (length A) (length B)
LeFTup-length {A} {B} le =
  Eq-trans (Eq-sym (length-embedTup A))
    (Eq-trans (LeTup-length {embedTup A} {embedTup B} le) (length-embedTup B))
