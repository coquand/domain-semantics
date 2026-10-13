{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/All.agda
--
-- (T3) for conversion, relative to the fixed point of Gamma.
--
--   Concrete/Std  (a) weak-head standardisation (Takahashi)
--   Sim           (b) syntactic weak-head reduction simulated by den
--   Shape, Whnf       syntactic weak-head normal forms and their values
--   WhnfNoDelta       weak-head normalisation for beta, pi, iota alone
--   EtaDec            decomposition of eta-equality along shapes
--   Measure, CompLem  measure and case lemmas
--   Complete      (c) typed completeness of the algorithm
--   T3            (e) Dec of conversion and of type equality, the
--                     weak-head normal forms of types (decPi, decSig,
--                     decU), and U-injectivity
--   T3PFix            the same, relative to the principle PFix
------------------------------------------------------------------------

module MAHLOALG.All where

import MAHLO.Concrete.Std
import MAHLOALG.Sim
import MAHLOALG.Shape
import MAHLOALG.Whnf
import MAHLOALG.WhnfNoDelta
import MAHLOALG.EtaDec
import MAHLOALG.Measure
import MAHLOALG.CompLem
import MAHLOALG.Complete
import MAHLOALG.T3
import MAHLOALG.T3PFix
