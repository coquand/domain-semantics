{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBot
--
-- Primitive recursion, the base sub-case where the recursion argument
-- is bot:  f(bot, Y) = bot.  The function is then eventually constant
-- incomplete (value S^0(bot)) pinned at coordinate 0, i.e. Case 2.
--
-- (This is the  x = bot  branch of the eventual  prop1-prec  dispatch.)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBot where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike)
open import OBSTINATION.PrecFun using (RecData ; PF)

prop1-prec-bot : (rd : RecData) (Y : Tup) ->
  UO (PF (RecData.G rd) (RecData.H rd)) (cons (bot zero) Y)
prop1-prec-bot rd Y =
  uo2 (mkSigma A0 (mkSigma below
    (mkSigma zero (mkSigma zero (mkSigma tt (mkSigma tt (mkSigma refl univ)))))))
  where
    open RecData rd
    A0 : FTup
    A0 = cons (fbot zero) (botLike Y)
    below : Below A0 (cons (bot zero) Y)
    below = mkSigma (LeD-refl (bot zero)) (Below-botLike Y)
    univ : (X : FTup) -> Eq (length X) (length A0) ->
           Eq (getF zero X) (getF zero A0) ->
           LeFTup (del zero A0) (del zero X) ->
           Eq (PF G H X) (fbot zero)
    univ nil ()
    univ (cons x xs) lenX coordX delX =
      Eq-transport (\ w -> Eq (PF G H (cons w xs)) (fbot zero))
        (Eq-sym coordX) refl
