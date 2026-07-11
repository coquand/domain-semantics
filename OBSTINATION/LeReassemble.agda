{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.LeReassemble
--
-- Reassemble the pointwise order from a single coordinate plus the rest:
-- if P and X have equal length, P(i) <= X(i), and P[i] <= X[i]
-- (pointwise on the deleted tuples), then P <= X.
--
-- The composition Case-3 assembly uses this to reconcile the EXACT
-- value it pins at coordinate i' (from the inner function's Case 3)
-- with the >= bound `pullback` provides on the remaining coordinates.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.LeReassemble where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF)

LeFTup-from-del : (i : Nat) (P X : FTup) ->
  Eq (length P) (length X) ->
  LeF (getF i P) (getF i X) ->
  LeFTup (del i P) (del i X) ->
  LeFTup P X
LeFTup-from-del i       nil         nil         leq co de = tt
LeFTup-from-del i       nil         (cons _ _)  ()  co de
LeFTup-from-del i       (cons _ _)  nil         ()  co de
LeFTup-from-del zero    (cons p ps) (cons x xs) leq co de = mkSigma co de
LeFTup-from-del (suc i) (cons p ps) (cons x xs) leq co de =
  mkSigma (fst de) (LeFTup-from-del i ps xs (suc-inj leq) co (snd de))
