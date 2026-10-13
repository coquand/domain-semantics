{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/EquivalenceFinal.agda
--
-- Russell (R') <=> Tarski (reflection) for the Mahlo universe,
-- HYPOTHESIS-FREE: MAHLORT/Equivalence instantiated at the Tarski
-- Pi/Sigma-injectivity proved by the Tarski adequacy (MAHLORT/TFinal).
------------------------------------------------------------------------

module MAHLORT.EquivalenceFinal where

open import MAHLORT.TFinal using (tInj)
open import MAHLORT.Equivalence tInj public
