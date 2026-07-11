{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecFinCpl
--
-- Primitive recursion at a COMPLETE finite first argument:  f(S^n(0), Y)
-- satisfies ultimate obstination, for every n and Y.  This is the finite
-- recurrence of Proposition 1 in the complete case (min1.pdf p.2, "le cas
-- ou x est fini est une recurrence directe sur x").
--
-- The step  f(S^{j+1}(0), Y) = h(S^j(0), f(S^j(0), Y), Y)  is handled by
-- the GENERIC composition (CompDispatch.prop1-compose):
--
--   * the base value  S^j(0)  is folded into  hCst zs = h(S^j(0), zs);
--   * the recursive restriction  fj zs = f(S^j(0), zs)  is a UOFun, its
--     obstination coming from the induction hypothesis via `unshift-cpl`;
--   * the pass-through argument tuple is the tuple of guarded projections
--     `gprojsFrom 0 (length Y)`, which reconstructs the tail.
--
-- Composition gives obstination of  zs |-> f(S^{j+1}(0), zs)  at Y, and
-- `lift-cpl` re-attaches the complete leading coordinate S^{j+1}(0).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecFinCpl where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.PrecUnshift using (unshift-cpl)
open import OBSTINATION.PrecCpl0 using (prec-lift-cpl0)
open import OBSTINATION.LiftCpl using (lift-cpl)
open import OBSTINATION.GProj using (gprojsFrom ; mapU-gprojs ; UO-pointwise-len)
open import OBSTINATION.CompPull using (UOFun ; Mono ; mapU ; compFn)
open import OBSTINATION.CompDispatch using (prop1-compose)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono ; precFun)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- The successor step, given the induction hypothesis at S^j(0)
  ------------------------------------------------------------------------

  prec-fin-cpl : (j : Nat) (Y : Tup) ->
    ((Z : Tup) -> UO (PF G H) (cons (cpl j) Z)) ->
    UO (PF G H) (cons (cpl (suc j)) Y)
  prec-fin-cpl j Y ih =
    lift-cpl (PF G H) (suc j) Y stepUO
    where
      -- the recursive restriction  fj zs = f(S^j(0), zs)
      fj : FTup -> FEl
      fj zs = PF G H (cons (fcpl j) zs)
      fjUO : UOall fj
      fjUO Z = unshift-cpl (PF G H) j Z (ih Z)
      fjMono : Mono fj
      fjMono {X} {Y'} le =
        PF-mono G H monoG monoH {cons (fcpl j) X} {cons (fcpl j) Y'}
          (mkSigma (LeF-refl (fcpl j)) le)
      fjU : UOFun
      fjU = mkSigma fj (mkSigma fjUO fjMono)
      -- h with its leading coordinate fixed to the complete S^j(0)
      hCst : FTup -> FEl
      hCst zs = H (cons (fcpl j) zs)
      hCstUO : UOall hCst
      hCstUO Z = unshift-cpl H j Z (uoh (cons (cpl j) Z))
      -- inner tuple: the recursive restriction, then the identity tail
      fs : List UOFun
      fs = cons fjU (gprojsFrom zero (length Y))
      composed : UO (compFn hCst fs) Y
      composed = prop1-compose hCst hCstUO fs Y
      -- on tuples of the ambient length, the composition is the step function
      agree : (X : FTup) -> Eq (length X) (length Y) ->
              Eq (compFn hCst fs X) (PF G H (cons (fcpl (suc j)) X))
      agree X lenX =
        Eq-cong (\ t -> H (cons (fcpl j) (cons (fj X) t)))
          (Eq-transport (\ n -> Eq (mapU (gprojsFrom zero n) X) X) lenX (mapU-gprojs X))
      stepUO : UO (\ zs -> PF G H (cons (fcpl (suc j)) zs)) Y
      stepUO = UO-pointwise-len agree composed

  ------------------------------------------------------------------------
  -- The complete finite-argument theorem, by recurrence on n
  ------------------------------------------------------------------------

  prop1-prec-cpl : (n : Nat) (Y : Tup) -> UO (PF G H) (cons (cpl n) Y)
  prop1-prec-cpl zero    Y = prec-lift-cpl0 rd Y (uog Y)
  prop1-prec-cpl (suc j) Y =
    prec-fin-cpl j Y (\ Z -> prop1-prec-cpl j Z)
