{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RankCounterexamplesSigma.agda
--
-- Closed-form Agda witnesses that the `rk` / `rkFun` measure defined
-- in BasicSigma is a SIZE measure (counts cons cells) and NOT the
-- iterative-stage RANK measure used in the paper.
--
-- IMPORTANT: these counterexamples do NOT impugn termination of the
-- Sigma-stack mutual blocks (FinMem, EvalFun, Val/EqVal, ...).  Those
-- blocks terminate under the proper iterative-stage RANK -- the
-- intended measure where finite elements are built in stages and a
-- function f's value f(v) lives at a strictly lower stage than f
-- itself.  See ValiditySigma / PaperSemanticsSigma comments near each
-- {-# TERMINATING #-} pragma for the relevant lex measure.
--
-- The file exists because, during the termination audit, the syntactic
-- measure `rk` was conflated with the iterative-stage RANK, and these
-- witnesses were used to (incorrectly) conclude that no rank-based
-- measure works.  They actually only refute the obvious bounds on the
-- size measure `rk`.
--
-- 0 postulates.
------------------------------------------------------------------------

module RankCounterexamplesSigma where

open import BasicSigma
open import PaperSemanticsSigma using (append ; Sup ; EvalFun)

------------------------------------------------------------------------
-- The size measure `rk` in BasicSigma is defined with a `suc` per cons:
--   rkFun (cons p xs) = suc (max (rk (fst p)) (max (rk (snd p)) (rkFun xs)))
-- So rkFun behaves like LENGTH + max-of-component-ranks.  It is not
-- the iterative-stage RANK.
--
-- The intended iterative-stage RANK (informally, used in the paper
-- and in the termination arguments) has NO `suc` per cons:
--   RANKFun (cons (u,v) ps) = max (RANK u) (max (RANK v) (RANKFun ps))
-- and RANK(FunEl g) = 1 + RANKFun g, etc.  Under that RANK, all the
-- bounds below DO hold; what fails is the syntactic `rk`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A: a length-3 coherent FunFun of (Bot, UCode) entries.
-- Coherent because each entry's value UCode is NotBot and the keys
-- Bot are pairwise compatible.
------------------------------------------------------------------------

A : FinFun
A = cons (mkSigma Bot UCode)
   (cons (mkSigma Bot UCode)
   (cons (mkSigma Bot UCode) nil))

-- rkFun A = 3.  Each cons adds 1 to rkFun.  (RANKFun A = 0, since the
-- entries' components Bot and UCode are at iterative stage 0.)
rkA : Eq (rkFun A) 3
rkA = refl

------------------------------------------------------------------------
-- Failure mode 1 (for `rk`, NOT for RANK):
--   rkFun (append f g) <= max (rkFun f) (rkFun g)   is FALSE.
-- Take f = g = A.  rkFun (append A A) = 6 > 3 = max (rkFun A) (rkFun A).
--
-- Under proper RANK: RANKFun (append A A) = max (RANKFun A) (RANKFun A)
-- = 0.  The bound holds.
------------------------------------------------------------------------

rkAppendAA : Eq (rkFun (append A A)) 6
rkAppendAA = refl

rkMaxAA : Eq (max (rkFun A) (rkFun A)) 3
rkMaxAA = refl

------------------------------------------------------------------------
-- Failure mode 2 (for `rk`, NOT for RANK):
--   rk (Sup x y) <= max (rk x) (rk y)   is FALSE.
-- Take x = y = FunEl A.  rk (Sup ...) = 6 > 3 = max (rk x) (rk y).
--
-- Under proper RANK: RANK (Sup (FunEl A) (FunEl A))
--   = RANK (FunEl (append A A)) = 1 + RANKFun (append A A) = 1
--   = max (RANK (FunEl A)) (RANK (FunEl A)).
-- The bound holds (with equality).
------------------------------------------------------------------------

rkSupFunEl : Eq (rk (Sup (FunEl A) (FunEl A))) 6
rkSupFunEl = refl

rkMaxFunEl : Eq (max (rk (FunEl A)) (rk (FunEl A))) 3
rkMaxFunEl = refl

------------------------------------------------------------------------
-- Failure mode 3 (for `rk`, NOT for RANK):
--   rk (EvalFun f u) <= rkFun f   is FALSE.
-- Take f to be a length-3 coherent FunFun whose value at each entry
-- is FunEl A.  rkFun f = 6 but rk (EvalFun f UCode) = 9.
--
-- Under proper RANK: RANKFun f = 1 (the max over entries' values
-- FunEl A, all of RANK 1).  EvalFun f UCode = FunEl (append A A A)
-- has RANK 1 + RANKFun (append A A A) = 1 + 0 = 1.  So
-- RANK (EvalFun f UCode) = 1 <= RANKFun f = 1 holds.
-- And the strictly-less form RANK (EvalFun f u) < RANK (FunEl f) = 2
-- also holds.
------------------------------------------------------------------------

f : FinFun
f = cons (mkSigma UCode (FunEl A))
   (cons (mkSigma UCode (FunEl A))
   (cons (mkSigma UCode (FunEl A)) nil))

rkFunF : Eq (rkFun f) 6
rkFunF = refl

rkEvalFunF : Eq (rk (EvalFun f UCode)) 9
rkEvalFunF = refl

------------------------------------------------------------------------
-- Moral
--
-- `rk` is the SIZE of a FinEl as a syntax tree (cons cells count).
-- RANK in the iterative-stage sense is the construction DEPTH.  The
-- termination measures in the Sigma stack use RANK -- with the key
-- property that a function applied to anything yields something at
-- strictly lower RANK.
--
-- A future cleanup pass could add an actual `RANK : FinEl -> Nat` /
-- `RANKFun : FinFun -> Nat` to BasicSigma (defined without `suc` per
-- cons), prove the three closed-form bounds above as Agda lemmas, and
-- then optionally rewrite each {-# TERMINATING #-} block to use Acc
-- recursion on RANK.  That would discharge the pragmas mechanically.
------------------------------------------------------------------------
