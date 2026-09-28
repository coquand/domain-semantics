{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.HeadRed.agda
--
-- Aggregator for the adequacy stack: re-exports AdequacyHelpers (the
-- public validity API + records + converters) and the stratified
-- head-expansion family (BCDE4.Valid.HeadRed).
--
-- The only thing defined here is the code-fixed Val2->Val2 beta-expansion
-- used by the adequacy fundamental lemma.
--
-- 0 postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.HeadRed (D : LDecAll) where

open import BCDE4.Valid.Core public using (U-tr)
open import BCDE4.Valid.AnnLemmas D public
open import BCDE4.Valid.Public D public
open import BCDE4.Adeq.Helpers D public
open import BCDE4.Valid.HeadRed D public
  using (Val2-headred-contract ; EqVal2-headred-contract ; EqVal2-headred-expand ;
         ValTy2-headred-expand ; EqValTy2-headred-expand)

open import BCDE4.Dom.Basic using (Nat ; FinEl)
open import BCDE4.RussellSyntax using (Expr)
open import BCDE4.RussellTyping
open import BCDE4.RussellReduction

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
