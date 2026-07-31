{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterShape
--
-- Shapes of the finite iterates of a mutual block.
--
-- The one-step law of `IterCycleComp` speaks of HEIGHTS, which only makes
-- sense while a component is incomplete (of the form S^j(bot)).  This file
-- settles that side condition:
--
--   * the iterates increase with the recursion argument (`iter-le`);
--   * hence a component that has become COMPLETE stays complete, at the
--     very same value (`cpl-persists`) -- because complete elements are
--     maximal.  Such a component has already stabilised and falls in the
--     ConstFrom branch, so the height analysis never has to touch it;
--   * dually, a component incomplete at some stage was incomplete at every
--     earlier stage (`bot-earlier`).
--
-- So at each component the recursion splits cleanly: an initial stretch of
-- incomplete values, where heights are defined and the one-step law
-- applies, followed (possibly) by a constant complete tail.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterShape where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF)
open import OBSTINATION.PropertyAt using (getF-le)
open import OBSTINATION.IterFun

module _ (idt : IterData) (Y : FTup) where
  open IterData idt

  iter : Nat -> FTup
  iter m = iterVec G H ar (fbot m) Y

  ------------------------------------------------------------------------
  -- The iterates increase with the recursion argument
  ------------------------------------------------------------------------

  iter-le : (a b : Nat) -> LeN a b -> LeFTup (iter a) (iter b)
  iter-le a b le =
    iterVec-mono G H ar lenG lenH monoG monoH
      {fbot a} {fbot b} {Y} {Y} le (LeFTup-refl Y)

  ------------------------------------------------------------------------
  -- A complete component is stuck at its value
  ------------------------------------------------------------------------

  above-cpl : (j : Nat) (x : FEl) -> LeD (cpl j) (embed x) -> Eq x (fcpl j)
  above-cpl j (fbot k) ()
  above-cpl j (fcpl k) e = Eq-cong fcpl (Eq-sym e)

  cpl-persists : (i j a b : Nat) ->
    Eq (getF i (iter a)) (fcpl j) -> LeN a b ->
    Eq (getF i (iter b)) (fcpl j)
  cpl-persists i j a b ea le =
    above-cpl j (getF i (iter b))
      (Eq-transport (\ z -> LeD (embed z) (embed (getF i (iter b)))) ea
        (getF-le i (iter-le a b le)))

  ------------------------------------------------------------------------
  -- Dually: incomplete now means incomplete before
  ------------------------------------------------------------------------

  IsBot : FEl -> Set
  IsBot (fbot _) = Top
  IsBot (fcpl _) = Empty

  bot-earlier : (i a b : Nat) -> LeN a b ->
    IsBot (getF i (iter b)) -> IsBot (getF i (iter a))
  bot-earlier i a b le ib = go (getF i (iter a)) refl
    where
      go : (x : FEl) -> Eq (getF i (iter a)) x -> IsBot (getF i (iter a))
      go (fbot k) e = Eq-transport IsBot (Eq-sym e) tt
      go (fcpl k) e =
        Empty-elim
          (Eq-transport IsBot (cpl-persists i k a b e le) ib)
