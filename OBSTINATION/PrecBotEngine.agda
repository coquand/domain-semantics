{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotEngine
--
-- Foundations for the INCOMPLETE finite first argument of primitive
-- recursion:  f(S^n(bot), Y),  the "recurrence directe sur x" that
-- min1.pdf (page 2) dismisses as easy but leaves to the reader.
--
-- The recursion peels ONE successor off the incomplete first coordinate:
--
--   f(cons(fbot(suc c)) X')  =  h(cons(fbot c)(cons(Fc X') X'))
--
-- where  Fc X' = f(cons(fbot c) X')  is the recursion result one step
-- down.  This module provides:
--
--   * `recstep-eq` : the single-unfolding identity for a first
--     coordinate  x >= S^{c+1}(bot)  (so x is S^{q+1}(bot) or S^{q+1}(0)
--     with q >= c) -- NO deep peeling is needed because h's germ at a
--     coordinate other than 0/1 ignores the exact height of x.
--
--   * `unshift-bot` : from  UO f (cons(bot c) Y)  (the induction
--     hypothesis) classify the tail function  Fc  at Y as EITHER a
--     genuine  UO Fc Y  (induction cases 1 / 2-at-a-Y-coord / 3-at-a-
--     Y-coord)  OR  constant-incomplete  (the induction hypothesis is
--     Case 2 pinned at coordinate 0, which loses its controlling
--     coordinate once coordinate 0 is removed).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotEngine where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (LeFTup-length ; embed-inj)
open import OBSTINATION.CompCase3Helpers using (bot-not-inf)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

------------------------------------------------------------------------
-- Predecessor of a first coordinate >= S^{c+1}(bot), and the single
-- recursion-unfolding identity.
------------------------------------------------------------------------

pred-of : FEl -> FEl
pred-of (fbot (suc q)) = fbot q
pred-of (fcpl (suc q)) = fcpl q
pred-of (fbot zero)    = fbot zero
pred-of (fcpl zero)    = fbot zero

-- for x >= S^{c+1}(bot),  pred-of x >= S^c(bot)
pred-ge : (c : Nat) (x : FEl) -> LeF (fbot (suc c)) x -> LeF (fbot c) (pred-of x)
pred-ge c (fbot (suc q)) le = le
pred-ge c (fcpl (suc q)) le = le
pred-ge c (fbot zero)    ()
pred-ge c (fcpl zero)    ()

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- The recursion result one step down, as a function of the tail.
  ------------------------------------------------------------------------

  FcFun : (c : Nat) -> FTup -> FEl
  FcFun c X' = precFun G H (fbot c) X'

  -- one unfolding of the recursion at an incomplete-or-complete successor
  recstep-eq : (c : Nat) (x : FEl) (tail : FTup) -> LeF (fbot (suc c)) x ->
    Eq (precFun G H x tail)
       (H (cons (pred-of x) (cons (precFun G H (pred-of x) tail) tail)))
  recstep-eq c (fbot (suc q)) tail le = refl
  recstep-eq c (fcpl (suc q)) tail le = refl
  recstep-eq c (fbot zero)    tail ()
  recstep-eq c (fcpl zero)    tail ()

  ------------------------------------------------------------------------
  -- Classifying the tail function Fc from the induction hypothesis.
  ------------------------------------------------------------------------

  -- The "bad" outcome: Fc is eventually constant incomplete, with no
  -- controlling coordinate among Y's (it came from the hypothesis being
  -- Case 2 pinned at coordinate 0).  Recorded as: a value m', a region
  -- A0' <= Y, and Fc X' = S^{m'}(bot) for all X' >= A0'.
  FcConst : (c : Nat) (Y : Tup) -> Set
  FcConst c Y =
    Sigma Nat (\ m' -> Sigma FTup (\ A0' ->
      Pair (Below A0' Y)
        ((X' : FTup) -> LeFTup A0' X' -> Eq (FcFun c X') (fbot m'))))

  unshift-bot : (c : Nat) (Y : Tup) ->
    UO (PF G H) (cons (bot c) Y) ->
    Or (UO (FcFun c) Y) (FcConst c Y)
  -- Case 1: eventually complete -- genuine UO of the tail (Case 1).
  unshift-bot c Y (uo1 (mkSigma nil (mkSigma below _))) = Empty-elim below
  unshift-bot c Y (uo1 (mkSigma (cons f0 F0') (mkSigma below (mkSigma m univ)))) =
    inl (uo1 (mkSigma F0' (mkSigma (snd below) (mkSigma m univ'))))
    where
      univ' : (X' : FTup) -> LeFTup F0' X' -> Eq (FcFun c X') (fcpl m)
      univ' X' leX' = univ (cons (fbot c) X') (mkSigma (fst below) leX')
  -- Case 2 at coordinate 0: constant incomplete -- the "bad" case.
  unshift-bot c Y (uo2 (mkSigma nil (mkSigma below _))) = Empty-elim below
  unshift-bot c Y (uo2 (mkSigma (cons f0 F0') (mkSigma below
    (mkSigma m (mkSigma zero (mkSigma _ (mkSigma _ (mkSigma eqinv univ)))))))) =
    inr (mkSigma m (mkSigma F0' (mkSigma (snd below) univ')))
    where
      -- the pin value getF 0 A0 = f0 embeds to bot c, hence f0 = fbot c
      f0eq : Eq f0 (fbot c)
      f0eq = embed-inj {f0} {fbot c} eqinv
      univ' : (X' : FTup) -> LeFTup F0' X' -> Eq (FcFun c X') (fbot m)
      univ' X' leX' =
        univ (cons (fbot c) X')
          (Eq-cong suc (Eq-sym (LeFTup-length {F0'} {X'} leX')))
          (Eq-sym f0eq)
          leX'
  -- Case 2 at coordinate (suc i'): genuine UO of the tail (Case 2 at i').
  unshift-bot c Y (uo2 (mkSigma (cons f0 F0') (mkSigma below
    (mkSigma m (mkSigma (suc i') (mkSigma irange (mkSigma incompl (mkSigma eqinv univ)))))))) =
    inl (uo2 (mkSigma F0' (mkSigma (snd below)
      (mkSigma m (mkSigma i' (mkSigma irange (mkSigma incompl (mkSigma eqinv univ'))))))))
    where
      univ' : (X' : FTup) -> Eq (length X') (length F0') ->
              Eq (getF i' X') (getF i' F0') -> LeFTup (del i' F0') (del i' X') ->
              Eq (FcFun c X') (fbot m)
      univ' X' lenX' coordX' delX' =
        univ (cons (fbot c) X') (Eq-cong suc lenX') coordX' (mkSigma (fst below) delX')
  -- Case 3 at coordinate 0: impossible (get 0 = bot c is not inf).
  unshift-bot c Y (uo3 (mkSigma (cons f0 F0') (mkSigma below
    (mkSigma zero (mkSigma eqinf _))))) = Empty-elim (bot-not-inf eqinf)
  unshift-bot c Y (uo3 (mkSigma nil (mkSigma below _))) = Empty-elim below
  -- Case 3 at coordinate (suc i'): genuine UO of the tail (Case 3 at i').
  unshift-bot c Y (uo3 (mkSigma (cons f0 F0') (mkSigma below
    (mkSigma (suc i') (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ))))))))) =
    inl (uo3 (mkSigma F0' (mkSigma (snd below)
      (mkSigma i' (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ')))))))))
    where
      univ' : (X' : FTup) (p : Nat) -> Eq (length X') (length F0') -> LeN k p ->
              Eq (getF i' X') (fbot p) -> LeFTup (del i' F0') (del i' X') ->
              Eq (FcFun c X') (fbot (phi p))
      univ' X' p lenX' pk coordX' delX' =
        univ (cons (fbot c) X') p (Eq-cong suc lenX') pk coordX' (mkSigma (fst below) delX')
