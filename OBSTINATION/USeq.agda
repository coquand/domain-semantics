{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.USeq
--
-- The Kleene fixpoint sequence for primitive recursion at the INFINITE
-- first argument (min1.pdf p.2-3).  For f = prec g h at the point
-- (S^omega(bot), Y), the value f(S^omega(bot), Y) is the least fixpoint of
--   Phi(z) = h-hat (S^omega(bot), z, Y),
-- approximated from below by
--   u 0 = bot,   u (k+1) = h-hat (S^omega(bot), u k, Y).
--
-- Here  h-hat = ext (evalF h) uoh  is the Scott-continuous extension of h
-- (available because h satisfies ultimate obstination).  This file builds
-- the sequence and its order-theoretic backbone:
--   * uSeq-mono : the sequence is increasing;
--   * uSeq-le   : hence monotone in the index;
--   * uSeq-stab : once two consecutive terms agree it is constant onward.
-- These are exactly the "(u_k) is increasing, and u_k = u_{k+1} entails
-- u_k = u_n for n >= k" of the note.  The monotonicity rests on ext-mono.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.USeq where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Extension using (ext)
open import OBSTINATION.ExtMono using (ext-mono)
open import OBSTINATION.PhiProps using (addN)
open import OBSTINATION.PhiComp using (le-to-addN)
open import OBSTINATION.PrecFun using (RecData)

module _ (rd : RecData) (Y : Tup) where
  open RecData rd

  ------------------------------------------------------------------------
  -- The sequence and the step operator
  ------------------------------------------------------------------------

  -- Phi z = h-hat (S^omega(bot), z, Y)
  step : D -> D
  step z = ext H uoh (cons inf (cons z Y))

  uSeq : Nat -> D
  uSeq zero    = bot zero
  uSeq (suc k) = step (uSeq k)

  ------------------------------------------------------------------------
  -- step is monotone (from ext-mono), and the sequence increases
  ------------------------------------------------------------------------

  step-mono : {a b : D} -> LeD a b -> LeD (step a) (step b)
  step-mono {a} {b} le =
    ext-mono H monoH uoh
      {cons inf (cons a Y)} {cons inf (cons b Y)}
      (mkSigma (LeD-refl inf) (mkSigma le (LeTup-refl Y)))

  uSeq-mono : (k : Nat) -> LeD (uSeq k) (uSeq (suc k))
  uSeq-mono zero    = LeD-botD (uSeq (suc zero))
  uSeq-mono (suc k) = step-mono (uSeq-mono k)

  -- monotone in the index
  uSeq-le-from : (k d : Nat) -> LeD (uSeq k) (uSeq (addN k d))
  uSeq-le-from k zero    = LeD-refl (uSeq k)
  uSeq-le-from k (suc d) = LeD-trans {uSeq k} {uSeq (addN k d)} {uSeq (suc (addN k d))}
                             (uSeq-le-from k d) (uSeq-mono (addN k d))

  uSeq-le : (k n : Nat) -> LeN k n -> LeD (uSeq k) (uSeq n)
  uSeq-le k n kn =
    Eq-transport (\ z -> LeD (uSeq k) (uSeq z)) (snd r) (uSeq-le-from k (fst r))
    where r = le-to-addN k n kn

  ------------------------------------------------------------------------
  -- Stabilisation propagates forward
  ------------------------------------------------------------------------

  module _ (k : Nat) (e : Eq (uSeq k) (uSeq (suc k))) where

    stab-step : (m : Nat) -> Eq (uSeq k) (uSeq m) -> Eq (uSeq k) (uSeq (suc m))
    stab-step m em = Eq-sym (Eq-trans (Eq-cong step (Eq-sym em)) (Eq-sym e))

    stab-add : (d : Nat) -> Eq (uSeq k) (uSeq (addN k d))
    stab-add zero    = refl
    stab-add (suc d) = stab-step (addN k d) (stab-add d)

    uSeq-stab : (n : Nat) -> LeN k n -> Eq (uSeq k) (uSeq n)
    uSeq-stab n kn =
      Eq-transport (\ z -> Eq (uSeq k) (uSeq z)) (snd r) (stab-add (fst r))
      where r = le-to-addN k n kn
