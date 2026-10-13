{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/All.agda
--
-- Phases P1 and P2 of mahlo-plan.tex.
--
-- P1: the extended predicative construction of the Mahlo universe over
-- an abstract term model (Pi, Sigma, Nat, the codes U(f,g)).
--
--   Candidate   candidates, Fun                      (Definition 3)
--   Pre         families, pre(f,g,X), Indep, Op      (Definitions 4, 5)
--   Congruence  Lemma 9 (congruence), Lemma 10 (safety)
--   Gamma       the operator, Lemma 11 (Gamma preserves candidates)
--   EndExt      Lemma 8 (transfer), Lemma 12 (extended predicativity),
--               Lemma 13 (monotonicity)
--   Fixpoint    the fixed point as a HYPOTHESIS (Lemma 14),
--               Lemma 15 (the Mahlo property)
--
-- P2: soundness of the PER model (Theorem 16), for the frozen syntax
-- MAHLO/Syntax.agda and typing MAHLO/Typing.agda.
--
--   Model       the term model with a denotation (Abel--Coquand 5.1)
--   Type        large types over V*, end-extension, PER, safety
--   Validity    validity of judgements, generic rules, semantic Pi/Sigma
--   ValPi       Pi, Sigma, lambda, application, pairs, beta, eta
--   ValNat      V, Nat, 0, S, rec
--   ValU        universe rules: subsumption, (R'), U(f,g) : V, fhat,
--               ghat, delta (the key observation: invU)
--   Soundness   Theorem 16, by induction on derivations
--   EqInstance  sanity: an Eq-based term model is an instance
--               (D is a setoid: elements compared by ~~, not Eq)
------------------------------------------------------------------------

module MAHLO.All where

import MAHLO.Basic
import MAHLO.TermModel
import MAHLO.Candidate
import MAHLO.Pre
import MAHLO.Congruence
import MAHLO.Gamma
import MAHLO.EndExt
import MAHLO.Fixpoint
import MAHLO.Syntax
import MAHLO.Typing
import MAHLO.Model
import MAHLO.Type
import MAHLO.Validity
import MAHLO.ValPi
import MAHLO.ValNat
import MAHLO.ValU
import MAHLO.Soundness
import MAHLO.EqInstance
import MAHLO.Concrete.All
import MAHLO.FixpointSpike
import MAHLO.FixCounter
import MAHLO.FixHyp
