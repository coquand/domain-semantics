{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RankCounterexamplesSigma.agda
--
-- Closed-form counterexamples showing that the "obvious" rank bounds
-- on Sup / append / EvalFun / Selection are FALSE -- even on coherent
-- finite-function data.
--
-- The {-# TERMINATING #-} block in ValiditySigma cannot be justified
-- by an `rk`-based lex measure: the natural candidates all fail.
-- This file documents the smallest concrete witnesses we have found.
-- Every check below typechecks under `--without-K --exact-split`, with
-- the only postulate being normalisation by Agda itself.
--
-- 0 postulates.
------------------------------------------------------------------------

module RankCounterexamplesSigma where

open import BasicSigma
open import PaperSemanticsSigma using (append ; Sup ; EvalFun)

------------------------------------------------------------------------
-- A: a length-3 coherent FunFun of (Bot, UCode) entries.
-- (Coherent because each entry's value UCode is NotBot, and the keys
-- Bot are pairwise compatible.)
------------------------------------------------------------------------

A : FinFun
A = cons (mkSigma Bot UCode)
   (cons (mkSigma Bot UCode)
   (cons (mkSigma Bot UCode) nil))

-- rkFun A = 3.  Each cons adds 1 to rkFun.
rkA : Eq (rkFun A) 3
rkA = refl

------------------------------------------------------------------------
-- Counterexample 1:
--   rkFun (append f g) <= max (rkFun f) (rkFun g)   is FALSE.
--
-- Take f = g = A.  append A A has length 6, so rkFun jumps to 6,
-- while max (rkFun A) (rkFun A) = 3.
------------------------------------------------------------------------

rkAppendAA : Eq (rkFun (append A A)) 6
rkAppendAA = refl

rkMaxAA : Eq (max (rkFun A) (rkFun A)) 3
rkMaxAA = refl

-- Conclusion: 6 > 3.

------------------------------------------------------------------------
-- Counterexample 2:
--   rk (Sup x y) <= max (rk x) (rk y)   is FALSE.
--
-- Take x = y = FunEl A.  Sup (FunEl A) (FunEl A) = FunEl (append A A),
-- so rk = rkFun (append A A) = 6, while max (rk (FunEl A)) (rk (FunEl A))
-- = 3.
------------------------------------------------------------------------

rkSupFunEl : Eq (rk (Sup (FunEl A) (FunEl A))) 6
rkSupFunEl = refl

rkMaxFunEl : Eq (max (rk (FunEl A)) (rk (FunEl A))) 3
rkMaxFunEl = refl

-- Conclusion: 6 > 3.

------------------------------------------------------------------------
-- Counterexample 3:
--   rk (EvalFun f u) <= rkFun f   is FALSE.
--
-- Take f to be a length-3 coherent FunFun whose value at each entry
-- is FunEl A:
--
--   f = cons (UCode, FunEl A) (cons (UCode, FunEl A) (cons (UCode, FunEl A) nil))
--
-- f is coherent: each entry's value is NotBot, and CompFun A A holds
-- (Comp Bot Bot, Comp UCode UCode both hold), so the entries are
-- pairwise compatible.
--
-- EvalFun f UCode steps through all three entries (leFinEl UCode UCode = 1)
-- and Sup's their values: FunEl A -|- FunEl A -|- FunEl A = FunEl
-- (append A (append A A)), which has length 9 and so rkFun 9.
--
-- rkFun f = 6, but rk (EvalFun f UCode) = 9.
------------------------------------------------------------------------

f : FinFun
f = cons (mkSigma UCode (FunEl A))
   (cons (mkSigma UCode (FunEl A))
   (cons (mkSigma UCode (FunEl A)) nil))

rkFunF : Eq (rkFun f) 6
rkFunF = refl

rkEvalFunF : Eq (rk (EvalFun f UCode)) 9
rkEvalFunF = refl

-- Conclusion: 9 > 6.

------------------------------------------------------------------------
-- Counterexample 4 (sketch):
--   Selection g u v -> rk u <= rkFun g   is FALSE.
--
-- The same idea: take g with two entries whose KEYS are FunEl A each
-- (rkFun A = 3), and use sel-take twice to get u = Sup (FunEl A)
-- (FunEl A) = FunEl (append A A), so rk u = 6, while rkFun g = 5 (the
-- length-2 outer wrapper around the keys).  We omit the closed form
-- here because constructing the Comp / Coherent witnesses for keys at
-- FunEl A would inflate this file; the structural reason is the same
-- as counterexamples 1-3 above: Sup-of-FunEl appends and so grows
-- rkFun by a length term that rkFun g does not budget for.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Why this matters for ValiditySigma's {-# TERMINATING #-} block:
--
-- The monotonicity block (downVal/upVal/restrict... at lines ~774-2236
-- of ValiditySigma) makes recursive calls of shape
--     downValTy G ... v0 v1   with v0 = EvalFun f0 u, v1 = EvalFun f1 u
-- (in transportPiEdgeVal-sel, etc.).  Any rk-based lex termination
-- measure would need rk v1 < rk (PiCode b1 f1), which decomposes to
-- rk (EvalFun f1 u) < rkFun f1.  Counterexample 3 above shows this
-- bound CAN fail on coherent data.
--
-- Consequently the pragma is NOT discharged by a clean lex measure on
-- `rk`.  Whether the block terminates by some other (e.g. multiset or
-- ordinal) measure is an open question in this codebase.
------------------------------------------------------------------------
