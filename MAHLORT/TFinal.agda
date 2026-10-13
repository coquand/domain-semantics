{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/TFinal.agda
--
-- The hypotheses of uniqueness / section / equivalence (MAHLORT/Hyp,
-- record TInj) are discharged, with no assumption:
--   Pi-inj, Sig-inj  for Tarski type equality, by the Tarski logical
--                    relation and its fundamental lemma (MAHLORT/Valid,
--                    MAHLORT/Adq), at the identity substitution and the
--                    bottom environment; the model is the finite-element
--                    model of MAHLOINJ, through erasure (MAHLORT/Model).
-- No-confusion of the Tarski type formers is MAHLORT/TNoConf.
------------------------------------------------------------------------

module MAHLORT.TFinal where

open import MAHLORT.Hyp using (TInj)
import MAHLORT.Adq.Inj as I

tInj : TInj
tInj = record { Pi-inj = I.Pi-inj ; Sig-inj = I.Sig-inj }

open I public using (Pi-inj ; Sig-inj)
open import MAHLORT.TNoConf public
