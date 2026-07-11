{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.USeqDich
--
-- The decidable stabilisation engine driving the two principal cases of
-- the infinite-argument recursion (min1.pdf p.3).  For the monotone
-- Kleene sequence u_k, at every stage n exactly one of:
--
--   * the sequence has already stabilised (u_k = u_{k+1} for some k) --
--     hence, by uSeq-stab, it is constant from k on and its limit is the
--     finite value u_k;  or
--   * S^n(bot) <= u_n  (the sequence "keeps up with the diagonal").
--
-- The subtlety is completion: if u_{n} = S^{n}(bot) but u_{n+1} = S^{n}(0)
-- (jumps to complete without gaining height), then S^{n+1}(bot) <= u_{n+1}
-- fails -- but a complete value is maximal, so the sequence stabilises at
-- the NEXT step.  `dich-step` handles this by also inspecting u_{n+2}.
--
-- `uSeq-finite-trigger` packages the contrapositive: a single failure
-- `not (S^{k0}(bot) <= u_{k0})` yields a genuine stabilisation point --
-- the entry to the first principal case (finite limit).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.USeqDich where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property using (UOall)
open import OBSTINATION.PrecFun using (RecData)
open import OBSTINATION.USeq using (uSeq ; uSeq-mono)

------------------------------------------------------------------------
-- Elementary domain facts
------------------------------------------------------------------------

-- a complete element is maximal
cpl-max : {k : Nat} {x : D} -> LeD (cpl k) x -> Eq x (cpl k)
cpl-max {k} {bot m} ()
cpl-max {k} {cpl m} e = Eq-cong cpl (Eq-sym e)
cpl-max {k} {inf}   ()

-- the infinite element is maximal
inf-max : {x : D} -> LeD inf x -> Eq x inf
inf-max {bot m} ()
inf-max {cpl m} ()
inf-max {inf}   e = refl

-- from  j <= k  and  j /= k  to the strict  suc j <= k
le-neq-lt : (j k : Nat) -> LeN j k -> Not (Eq j k) -> LeN (suc j) k
le-neq-lt zero    zero    le ne = Empty-elim (ne refl)
le-neq-lt zero    (suc k) le ne = tt
le-neq-lt (suc j) zero    () ne
le-neq-lt (suc j) (suc k) le ne = le-neq-lt j k le (\ e -> ne (Eq-cong suc e))

------------------------------------------------------------------------
-- One step of the dichotomy, as a pure order fact on three D values
--   a = u_n,  b = u_{n+1},  c = u_{n+2}  with  bot n <= a <= b <= c.
------------------------------------------------------------------------

dich-step : (n : Nat) (a b c : D) ->
  LeD (bot n) a -> LeD a b -> LeD b c ->
  Or (Eq a b) (Or (Eq b c) (LeD (bot (suc n)) b))
dich-step n (bot j) (bot k) c bn ab bc with EqNat-dec j k
... | yes e = inl (Eq-cong bot e)
... | no ne = inr (inr (LeN-trans {suc n} {suc j} {k} bn (le-neq-lt j k ab ne)))
dich-step n (bot j) (cpl k) c bn ab bc = inr (inl (Eq-sym (cpl-max bc)))
dich-step n (bot j) inf     c bn ab bc = inr (inr tt)
dich-step n (cpl j) b       c bn ab bc = inl (Eq-sym (cpl-max ab))
dich-step n inf     b       c bn ab bc = inl (Eq-sym (inf-max ab))

------------------------------------------------------------------------
-- The dichotomy and the finite trigger
------------------------------------------------------------------------

module _ (rd : RecData) (Y : Tup) where
  open RecData rd

  Stabilises : Set
  Stabilises = Sigma Nat (\ k -> Eq (uSeq rd Y k) (uSeq rd Y (suc k)))

  uSeq-dichotomy : (n : Nat) -> Or Stabilises (LeD (bot n) (uSeq rd Y n))
  uSeq-dichotomy zero    = inr tt
  uSeq-dichotomy (suc n) with uSeq-dichotomy n
  ... | inl s   = inl s
  ... | inr bn  with dich-step n (uSeq rd Y n) (uSeq rd Y (suc n))
                       (uSeq rd Y (suc (suc n)))
                       bn (uSeq-mono rd Y n) (uSeq-mono rd Y (suc n))
  ...   | inl e       = inl (mkSigma n e)
  ...   | inr (inl e) = inl (mkSigma (suc n) e)
  ...   | inr (inr l) = inr l

  uSeq-finite-trigger : (k0 : Nat) ->
    Not (LeD (bot k0) (uSeq rd Y k0)) -> Stabilises
  uSeq-finite-trigger k0 nle with uSeq-dichotomy k0
  ... | inl s = s
  ... | inr l = Empty-elim (nle l)
