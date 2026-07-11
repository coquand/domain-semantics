{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecAll
--
-- The primitive-recursion case of Proposition 1, ASSEMBLED over ALL
-- first arguments  a : D:
--
--   a = S^n(bot)   incomplete finite  -> prop1-prec-bot-all  (PrecBotStep)
--   a = S^n(0)     complete finite     -> prop1-prec-cpl      (PrecFinCpl)
--   a = S^omega(bot) infinite          -> prop1-prec-inf      (PrecInfDispatch)
--
-- Hence  prec g h  satisfies ultimate obstination at every point
-- cons a Y, given the base g and step h do so everywhere.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecAll where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.PrecFun using (RecData ; PF)
open import OBSTINATION.PrecFinCpl using (prop1-prec-cpl)
open import OBSTINATION.PrecInfDispatch using (prop1-prec-inf)
open import OBSTINATION.PrecBotStep using (prop1-prec-bot-all)

-- The recursion case of Proposition 1, over an abstract base/step bundle,
-- assembled over all first arguments  a : D  (incomplete finite / complete
-- finite / infinite).  Instantiated (in `Prop1`) with the arity-guarded
-- interpretations of the sub-terms.
module _ (rd : RecData) where
  open RecData rd

  prop1-prec-generic : (a : D) (Y : Tup) -> UO (PF G H) (cons a Y)
  prop1-prec-generic (bot n) Y = prop1-prec-bot-all rd n Y
  prop1-prec-generic (cpl n) Y = prop1-prec-cpl     rd n Y
  prop1-prec-generic inf     Y = prop1-prec-inf     rd Y
