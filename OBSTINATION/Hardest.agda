{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Hardest
--
-- Examples that drive the *hardest* branch of the proof: the
-- FINITE-INCOMPLETE first-argument case of primitive recursion,
-- `prop1-prec-bot-all` (files `PrecBot*`, with base constancy
-- `PrecBaseConst`).  Note that `Computable.fhat-diag` only ever evaluates
-- at the infinite point `S^ω(⊥)`, which routes through the *infinite*-
-- argument machinery (`PrecInf*`); to reach the finite-incomplete cone one
-- must evaluate `fhat` at a point whose first coordinate is `Sʲ(⊥)` with
-- `j ≥ 1` -- an incomplete finite element that is neither `0`/complete nor
-- infinite.  That is what this file does.
--
-- Recall the shape of the recursion at `f(Sʲ(⊥), Y)`: the recursion peels
-- the `j` known successors of the first argument and then hits `⊥`, so the
-- complete base `f(0,Y)=g(Y)` is NEVER reached.  The value therefore comes
-- entirely from how the step `h` acts on the (finite, incomplete) recursion
-- result and on `Y`.  The proof dispatches on `h`'s obstination case at the
-- pinned point; the three examples below select the three genuinely
-- different branches.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Hardest where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Prop1 using (Wf ; prop1)
open import OBSTINATION.Computable using (fhat)
open import OBSTINATION.PredMin using (addPR ; wf-add)

------------------------------------------------------------------------
-- A step term that reads the Y-coordinate:
--   f(0, y) = 0,   f(S x, y) = S(y).    (arity 2)
------------------------------------------------------------------------

stepY : PR
stepY = prec zerf (comp succ (cons (proj (suc (suc zero))) nil))

wf-stepY : Wf stepY (suc (suc zero))
wf-stepY =
  mkSigma (suc zero)
    (mkSigma refl (mkSigma tt (mkSigma tt (mkSigma tt tt))))

------------------------------------------------------------------------
-- Evaluation points with a FINITE-INCOMPLETE first coordinate  S^2(⊥).
------------------------------------------------------------------------

-- (S^2 ⊥ , S^ω ⊥):  the step sends the recursion to the INFINITE
-- Y-coordinate.  Branch: finite-incomplete cone, Case 3 at a Y-coordinate
-- (PrecBotCase23 / PrecBotHval → witness W4).  Value climbs to infinity.
hardest-Ycoord-inf : Eq (fhat stepY (cons (bot (suc (suc zero))) (cons inf nil)) wf-stepY) inf
hardest-Ycoord-inf = refl

-- (S^2 ⊥ , 3):  the step reads a COMPLETE Y-coordinate.  Branch:
-- finite-incomplete cone, Case 1 (PrecBotCase1).  Value = S(3) = 4.
hardest-Ycoord-cpl :
  Eq (fhat stepY (cons (bot (suc (suc zero))) (cons (cpl (suc (suc (suc zero)))) nil)) wf-stepY)
     (cpl (suc (suc (suc (suc zero)))))
hardest-Ycoord-cpl = refl

-- add at (S^2 ⊥ , 3):  the step is  succ(recursion result).  The recursion
-- result is itself finite-incomplete, so h is Case 2 at coordinate 1 (the
-- recursion-result coordinate).  Branch: finite-incomplete cone, coord-1
-- Case 2 -- the BASE-CONSTANCY argument (PrecBotCoord1 / PrecBaseConst,
-- the note's direct Berry-stability computation).  Value = S^2(⊥).
hardest-coord1-baseconst :
  Eq (fhat addPR (cons (bot (suc (suc zero))) (cons (cpl (suc (suc (suc zero)))) nil)) wf-add)
     (bot (suc (suc zero)))
hardest-coord1-baseconst = refl

------------------------------------------------------------------------
-- The single hardest branch -- coordinate-1 Case 3 (a strictly-growing
-- recursion result governing the step at an incomplete first argument) --
-- is NOT reachable by any value: at a finite-incomplete first argument the
-- recursion result is always finite, so that configuration is contradictory
-- and the proof discharges it to the empty type (PrecBotCoord1C, via
-- StabExclude, Berry-stability exclusion).  It is exercised by the type
-- checker as an impossibility, not by a computed example.
------------------------------------------------------------------------
