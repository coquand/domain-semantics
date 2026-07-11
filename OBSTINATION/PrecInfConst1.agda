{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfConst1
--
-- The coordinate-1 CONSTANT builder for primitive recursion at the
-- infinite first argument.  Used by the first principal case (finite
-- limit S^{l0}(bot)) when h controls the recursion-result coordinate but
-- its value has SATURATED at S^{l0}(bot) (h Case 2 at coordinate 1, pinned
-- to S^{l0}(bot)).  Then f is Case 3 at its OWN coordinate 0 with the
-- CONSTANT witness phi = const l0:  f(S^n b, X) = S^{l0} b  for n >= n0,
-- X >= Y0.
--
-- Unlike PrecInfSub4 (which needs h's germ at coordinate 1 = S^k b for
-- MANY k), this builder needs h's germ ONLY at coordinate 1 = S^{l0} b
-- (the saturated value) -- exactly what a Case-2-at-coordinate-1 pin
-- provides.  Base constancy in the tail comes from `base-const` (minimal
-- germ), and the up-recurrence propagates the constant.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfConst1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)
open import OBSTINATION.PhiComp using (le-to-addN)
open import OBSTINATION.PrecBaseConst using (base-const)
open import OBSTINATION.PrecFun using (RecData ; PF)

module _ (rd : RecData) (n0 l0 : Nat) (Y0 : FTup)
  (Neq : Eq (PF (RecData.G rd) (RecData.H rd) (cons (fbot n0) Y0)) (fbot l0))
  (germL : (n : Nat) (X : FTup) -> LeN n0 n -> LeFTup Y0 X ->
             Eq (RecData.H rd (cons (fbot n) (cons (fbot l0) X))) (fbot l0))
  where
  open RecData rd

  germN0 : (X : FTup) -> LeFTup Y0 X ->
    Eq (H (cons (fbot n0) (cons (fbot l0) X))) (fbot l0)
  germN0 X leX = germL n0 X (LeN-refl n0) leX

  bc : (n : Nat) (X : FTup) -> LeN n n0 -> LeFTup Y0 X ->
       Eq (PF G H (cons (fbot n) X)) (PF G H (cons (fbot n) Y0))
  bc = base-const rd n0 l0 l0 Y0 Neq germN0

  -- f(S^n b, X) = S^{l0} b  for n >= n0, X >= Y0  (induction on the offset)
  fconst-off : (d : Nat) (X : FTup) -> LeFTup Y0 X ->
    Eq (PF G H (cons (fbot (addN n0 d)) X)) (fbot l0)
  fconst-off zero    X leX = Eq-trans (bc n0 X (LeN-refl n0) leX) Neq
  fconst-off (suc d) X leX =
    Eq-trans (Eq-cong (\ z -> H (cons (fbot m) (cons z X))) ih)
             (germL m X (LeN-addN-l n0 d) leX)
    where
      m = addN n0 d
      ih : Eq (PF G H (cons (fbot m) X)) (fbot l0)
      ih = fconst-off d X leX

  fconst-up : (n : Nat) -> LeN n0 n -> (X : FTup) -> LeFTup Y0 X ->
    Eq (PF G H (cons (fbot n) X)) (fbot l0)
  fconst-up n n0n X leX =
    Eq-transport (\ z -> Eq (PF G H (cons (fbot z) X)) (fbot l0))
      (snd r) (fconst-off (fst r) X leX)
    where r = le-to-addN n0 n n0n

  prec-inf-const-coord1 : (Y : Tup) -> Below Y0 Y ->
    UO (PF G H) (cons inf Y)
  prec-inf-const-coord1 Y belY0 =
    uo3 (mkSigma (cons (fbot n0) Y0) (mkSigma (mkSigma tt belY0)
      (mkSigma zero (mkSigma refl (mkSigma n0 (mkSigma refl
        (mkSigma (\ _ -> l0) (mkSigma (inl (\ _ _ -> refl)) univ))))))))
    where
      univ : (W : FTup) (p : Nat) ->
             Eq (length W) (length (cons (fbot n0) Y0)) -> LeN n0 p ->
             Eq (getF zero W) (fbot p) ->
             LeFTup (del zero (cons (fbot n0) Y0)) (del zero W) ->
             Eq (PF G H W) (fbot l0)
      univ nil p ()
      univ (cons a X') p lenW n0p coordW delW =
        Eq-transport (\ z -> Eq (PF G H (cons z X')) (fbot l0))
          (Eq-sym coordW) (fconst-up p n0p X' delW)
