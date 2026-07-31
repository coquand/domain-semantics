{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PropertyVecTest
--
-- End-to-end check that the joint interface of `PropertyVec` is usable
-- with the existing Proposition 1.
--
-- Given a LIST of PR terms  p_1,...,p_r,  all well-formed at one arity n
-- (the shape a mutually defined block will have), form the tuple-valued
--
--   evalTup n ps X  =  < guard n (evalF p_1) X , ... , guard n (evalF p_r) X >
--
-- and derive JOINT ultimate obstination: at every point A there is ONE
-- finite approximant A0 <= A carrying a verdict for every component.
--
-- This exercises `UOMall-build` on real interpretations, and is the
-- interface the mutual step function <h_1,...,h_r> will be plugged into.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PropertyVecTest where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR using (PR ; zerf ; evalF)
open import OBSTINATION.Property using (UO ; UOall ; getF)
open import OBSTINATION.PropertyAt using (UOat)
open import OBSTINATION.PropertyVec
open import OBSTINATION.Arity using (UOn ; guard ; guard-uoall)
open import OBSTINATION.CompPull using (UO-pointwise)
open import OBSTINATION.Prop1 using (Wf ; AllWf ; prop1)

------------------------------------------------------------------------
-- The tuple-valued interpretation of a block of terms
------------------------------------------------------------------------

evalTup : Nat -> List PR -> FTup -> FTup
evalTup n nil         X = nil
evalTup n (cons p ps) X = cons (guard n (evalF p) X) (evalTup n ps X)

nthPR : Nat -> List PR -> PR
nthPR = nth zerf

-- component i of the block is the guarded interpretation of the i-th term
evalTup-comp : (n : Nat) (ps : List PR) (i : Nat) -> LeN (suc i) (length ps) ->
  (X : FTup) -> Eq (getF i (evalTup n ps X)) (guard n (evalF (nthPR i ps)) X)
evalTup-comp n nil         i       ()
evalTup-comp n (cons p ps) zero    lt X = refl
evalTup-comp n (cons p ps) (suc i) lt X = evalTup-comp n ps i lt X

------------------------------------------------------------------------
-- Proposition 1 gives UOn at the term's own arity; the guard totalises it
------------------------------------------------------------------------

block-uoall : (n : Nat) (ps : List PR) -> AllWf ps n ->
  (i : Nat) -> LeN (suc i) (length ps) -> UOall (guard n (evalF (nthPR i ps)))
block-uoall n nil         aw i       ()
block-uoall n (cons p ps) aw zero    lt =
  guard-uoall n (evalF p)
    (\ A e -> prop1 p A (Eq-transport (Wf p) (Eq-sym e) (fst aw)))
block-uoall n (cons p ps) aw (suc i) lt = block-uoall n ps (snd aw) i lt

------------------------------------------------------------------------
-- Joint obstination of the whole block, at ONE shared approximant
------------------------------------------------------------------------

block-UOM : (n : Nat) (ps : List PR) -> AllWf ps n ->
  UOMall (evalTup n ps) (length ps)
block-UOM n ps aw =
  UOMall-build (evalTup n ps) (length ps)
    (\ i lt A ->
       UO-pointwise (\ X -> Eq-sym (evalTup-comp n ps i lt X))
         (block-uoall n ps aw i lt A))

-- unpacked form: the shared approximant, and the verdict for each component
block-approx : (n : Nat) (ps : List PR) -> AllWf ps n -> Tup -> FTup
block-approx n ps aw A = fst (block-UOM n ps aw A)

block-verdict : (n : Nat) (ps : List PR) (aw : AllWf ps n) (A : Tup)
  (i : Nat) -> LeN (suc i) (length ps) ->
  UOat (compOf (evalTup n ps) i) A (block-approx n ps aw A)
block-verdict n ps aw A = snd (snd (block-UOM n ps aw A))
