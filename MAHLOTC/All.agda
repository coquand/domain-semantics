{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/All.agda
--
-- (T3), second half: decidable type checking for the bidirectional
-- fragment, relative to TCHyp (decTyEq, decPi, decSig, decU + InjHyp).
--
--   Base     Dec, lists, DecEq on Expr (generated), TCHyp
--   Frag     Inf / Chk / ChkTy: the bidirectional fragment
--   Lemmas   inversion of IsType for type formers, shapes
--   Res      inference results (finite type lists, saturated U <= V)
--   Rules    one rule per term former, with completeness
--   Check    infer / check / isType; decHasType, decIsType, decWfCtx
--
-- NEGATIVE FACT (not machine-checked; it needs V /= U(f,g), which is
-- deliberately not among the hypotheses):  with unannotated pairs,
-- typing is not closed under beta-EXPANSION.  In a context where
-- U(f,g) : V,
--   App (Lam V (Pair x0 y)) Nat   is NOT of type  SigmaB (Ucode f g) C2,
-- because the pair's first component is the variable x0 : V, so every
-- Sigma-type of the body has domain ~ V, and its instance is V /= U(f,g);
-- while the contractum  Pair Nat y'  IS of that type (Nat : U(f,g)).
-- So typing a beta-redex with a check-only body is a higher-order
-- matching problem modulo conversion; its decidability is OPEN, and such
-- redexes are outside the fragment.
------------------------------------------------------------------------

module MAHLOTC.All where

import MAHLOTC.Base
import MAHLOTC.Frag
import MAHLOTC.Lemmas
import MAHLOTC.Res
import MAHLOTC.Rules
import MAHLOTC.Check
import MAHLOTC.Instance
