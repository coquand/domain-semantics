{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MIN.AdequacyHeadRed.agda
--
-- Aggregator for the adequacy stack: re-exports AdequacyHelpers (the
-- public validity API + records + converters) and the stratified
-- head-expansion family (MIN.ValidityHeadRed).
--
-- The only thing defined here is the code-fixed Val2->Val2 beta-expansion
-- used by the adequacy fundamental lemma.
--
-- 0 postulates.
------------------------------------------------------------------------

module MIN.AdequacyHeadRed where
open import MIN.AdequacyHelpers public
open import MIN.ValidityHeadRed public
  using (Val2-headred-contract ; EqVal2-headred-contract ; EqVal2-headred-expand)

open import MIN.Basic using (Nat ; FinEl)
open import MIN.RawSyntax using (Expr)
open import MIN.TypingRules using (Ctx ; HasType ; ConvTm)
open import MIN.Reduction using (HeadRed)

------------------------------------------------------------------------
-- Val2-beta-expand (Val2 -> Val2): HeadRed M' M means M' reduces to M.
-- Code-fixed, so it is just the canonical-level BetaPack wrapper composed
-- with the second projection.
------------------------------------------------------------------------

Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
  (u a : FinEl) -> HeadRed M' M -> ConvTm G M' M T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-beta-expand u a hr cv val =
  Val2-from-EqVal2-second u a (Val2-beta-expand-pub u a hr cv val)
