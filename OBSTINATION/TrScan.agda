{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrScan
--
-- PLUMBING FOR THE CLIMB.
--
--   * `orMap` -- a demand shifted through a whole chain of freezes.
--     `blockOn` un-shifts one freeze at a time (`shiftOr c`); a proof that
--     recurses into continuations has to carry the composite of those
--     shifts, and `orMap-shiftOr` is how the composite grows.
--
--   * `OrEq-dec` -- "is the composite waiting on `j` right now?" is
--     DECIDABLE.  That is what makes the climb's searches bounded rather
--     than unbounded: every question it asks is about one stage.
--
--   * `scan` -- the bounded search itself: over `t < s`, either the
--     predicate holds throughout, or a first counterexample is produced.
--
--   * `del-tup` -- deleting a coordinate of a tuple built by `tup` is
--     again such a tuple, at the re-indexed function.  This is what keeps
--     the family a `tup` across a descent.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrScan where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (le-nlt-eq)
open import OBSTINATION.TraceDef using (tup ; su ; shiftOr)

------------------------------------------------------------------------
-- A DEMAND, SHIFTED THROUGH A CHAIN OF FREEZES
------------------------------------------------------------------------

orMap : (Nat -> Nat) -> Or Top Nat -> Or Top Nat
orMap f (inl tt) = inl tt
orMap f (inr j)  = inr (f j)

orMap-shiftOr : (f : Nat -> Nat) (c : Nat) (r : Or Top Nat)
              -> Eq (orMap f (shiftOr c r)) (orMap (\ j -> f (su c j)) r)
orMap-shiftOr f c (inl tt) = refl
orMap-shiftOr f c (inr j)  = refl

orMap-id : (r : Or Top Nat) -> Eq (orMap (\ x -> x) r) r
orMap-id (inl tt) = refl
orMap-id (inr j)  = refl

------------------------------------------------------------------------
-- EVERY QUESTION THE CLIMB ASKS IS DECIDABLE
------------------------------------------------------------------------

inr-inj : (i j : Nat) -> Eq {Or Top Nat} (inr i) (inr j) -> Eq i j
inr-inj i j refl = refl

OrEq-dec : (r : Or Top Nat) (j : Nat) -> Dec (Eq r (inr j))
OrEq-dec (inl tt) j = no (\ ())
OrEq-dec (inr i)  j = route (EqNat-dec i j)
  where
    route : Dec (Eq i j) -> Dec (Eq {Or Top Nat} (inr i) (inr j))
    route (yes e) = yes (Eq-cong inr e)
    route (no ne) = no (\ e -> ne (inr-inj i j e))

------------------------------------------------------------------------
-- THE BOUNDED SEARCH
------------------------------------------------------------------------

scan : (P : Nat -> Set) -> ((t : Nat) -> Dec (P t)) -> (s : Nat)
     -> Or ((t : Nat) -> LeN (suc t) s -> P t)
           (Sigma Nat (\ t -> Pair (LeN (suc t) s) (Not (P t))))
scan P dec zero    = inl (\ t ())
scan P dec (suc s) = route (scan P dec s)
  where
    Res : Nat -> Set
    Res n =
      Or ((t : Nat) -> LeN (suc t) n -> P t)
         (Sigma Nat (\ t -> Pair (LeN (suc t) n) (Not (P t))))

    route : Res s -> Res (suc s)
    route (inr (mkSigma t (mkSigma lt np))) =
      inr (mkSigma t
            (mkSigma (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s)) np))
    route (inl h) = route2 (dec s)
      where
        route2 : Dec (P s) -> Res (suc s)
        route2 (no np) = inr (mkSigma s (mkSigma (LeN-refl s) np))
        route2 (yes ps) = inl ext
          where
            ext : (t : Nat) -> LeN (suc t) (suc s) -> P t
            ext t lt = pick (LeN-dec (suc t) s)
              where
                pick : Dec (LeN (suc t) s) -> P t
                pick (yes l)  = h t l
                pick (no  nl) =
                  Eq-transport P (Eq-sym (le-nlt-eq t s lt nl)) ps

------------------------------------------------------------------------
-- DELETING A COORDINATE OF A `tup`
------------------------------------------------------------------------

del-tup : (q c : Nat) -> LeN (suc c) (suc q) -> (f : Nat -> FEl)
        -> Eq (del c (tup (suc q) f)) (tup q (\ j -> f (su c j)))
del-tup q       zero    lc f = refl
del-tup zero    (suc c) ()  f
del-tup (suc q) (suc c) lc f =
  Eq-cong (cons (f zero)) (del-tup q c lc (\ j -> f (suc j)))

------------------------------------------------------------------------
-- RANGE PROOFS ARE UNIQUE
--
-- `LeN` is `Top`/`Empty`-valued, so two proofs of the same bound are
-- propositionally equal.  The descent phase of the recursion needs this:
-- `blockOn` descends into `cont c lc v`, and across the walk the `lc` it
-- passes is `ivr (NG k)` for a REPLAY DEPTH THAT KEEPS GROWING, so the
-- continuations are the same trace only up to the proof argument.
------------------------------------------------------------------------

LeN-uniq : (m n : Nat) (x y : LeN m n) -> Eq x y
LeN-uniq zero    n       tt tt = refl
LeN-uniq (suc m) zero    () y
LeN-uniq (suc m) (suc n) x  y  = LeN-uniq m n x y
