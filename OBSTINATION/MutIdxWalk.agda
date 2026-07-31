{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MutIdxWalk
--
-- THE WALK INDUCED BY IMG_0239's SEQUENTIALITY-INDEX RECIPE, AND EXACTLY
-- WHERE r = 1 AND r >= 2 PART COMPANY.
--
-- The manuscript (IMG_0239, section 2) defines the sequentiality index of
-- `f_i` at `(u, v~)` by induction on `u`:
--
--   u = bot    -- the index is the recursion argument;
--   u = S(u0)  -- take the index `s` of `g_i` at `(w_1,...,w_r, v~)`,
--                 where `w_j = f_j(u0, v~)`; if `s < r` (a RECURSIVE CALL)
--                 the answer is the index of `f_s` at `(u0, v~)`; if
--                 `s = r+j` (a PARAMETER) the answer is `1+j`.
--
-- So the index at level `m+1` is computed by a WALK that descends one
-- level per step and moves between the r components, stopping as soon as
-- some `g_i` reads a parameter rather than a recursive call.  `pickM` is
-- that dispatch.
--
-- Assume, as the induction on the definition gives, that each `g_i`'s own
-- index is EVENTUALLY CONSTANT along the (increasing) sequence of levels:
-- `c i m = C i` for `m >= L`.  Then above `L` the walk is the ITERATION OF
-- THE SELF-MAP `C` on {0,...,r-1}, and this module reads off what that
-- gives:
--
--   exit-const  -- if `C i >= r` (component i reads a parameter), `q i` is
--                  CONSTANT from L+1 on;
--   descend     -- otherwise `q i (m+t) = q (C^t i) m` for `m >= L`;
--   periodic-at -- on the cycle of `C` through i (which exists, `d <= r`,
--                  by `IterCycle.orbit-cycle`) the index is PERIODIC with
--                  period `d`:  `q j (m+d) = q j m` for `m >= L`.
--
-- **r = 1 IS THEREFORE TRIVIAL** (`one-const`): the only cycle has `d = 1`,
-- and period 1 IS constancy -- no bounded search, no Proposition, no
-- uniqueness of the index.  This is why Colson's original lemma is easy on
-- this route.
--
-- **r >= 2 GIVES PERIOD `d <= r`, NOT CONSTANCY.**  That is exactly the gap
-- the manuscript's Lemma (IMG_0241) has to close, and it is also exactly
-- David's `C_mut`: multi-step iteration with period `p <= k` for a system
-- of `k` mutually recursive functions (remark (4) after Corollary 15 of
-- rdavid.pdf).  The two routes agree on where the difficulty is.
--
-- What remains for constancy is that the values `q j0, ..., q j_{d-1}` at
-- the base level `L` around the cycle COINCIDE -- i.e. that the walk, once
-- below `L`, still descends all the way to `bot` (answer: the recursion
-- argument).  That is the content of IMG_0241's Lemma, and this module
-- makes it the only thing left to prove.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MutIdxWalk where

open import OBSTINATION.Prelude
open import OBSTINATION.Classes using (add ; add-ge ; le-to-add)
open import OBSTINATION.IntBeh using (predIter)
open import OBSTINATION.IterCycleComp using (pIter)
open import OBSTINATION.IterCycle using (Cycle ; orbit-cycle ; orbit-range)

------------------------------------------------------------------------
-- Eventually constant / eventually periodic
------------------------------------------------------------------------

EvConstN : (Nat -> Nat) -> Set
EvConstN u = Sigma Nat (\ N -> (n : Nat) -> LeN N n -> Eq (u n) (u N))

------------------------------------------------------------------------
-- IMG_0239's dispatch
--
-- `pickM r s rec`: the index `s` of the step function; below `r` it names
-- a recursive call and the walk continues at `rec s`; at or above `r` it
-- names the `(s-r)`-th parameter, whose position among `f_i`'s own
-- arguments (recursion argument first) is `1 + (s-r)`.
------------------------------------------------------------------------

pickAux : (r s : Nat) (rec : Nat -> Nat) -> Dec (LeN (suc s) r) -> Nat
pickAux r s rec (yes _) = rec s
pickAux r s rec (no  _) = suc (predIter r s)

pickM : Nat -> Nat -> (Nat -> Nat) -> Nat
pickM r s rec = pickAux r s rec (LeN-dec (suc s) r)

pickM-in : (r s : Nat) (rec : Nat -> Nat) -> LeN (suc s) r
         -> Eq (pickM r s rec) (rec s)
pickM-in r s rec lt with LeN-dec (suc s) r
... | yes _ = refl
... | no  q = Empty-elim (q lt)

pickM-out : (r s : Nat) (rec : Nat -> Nat) -> Not (LeN (suc s) r)
          -> Eq (pickM r s rec) (suc (predIter r s))
pickM-out r s rec nt with LeN-dec (suc s) r
... | yes p = Empty-elim (nt p)
... | no  _ = refl

------------------------------------------------------------------------
-- THE WALK
--
--   c i m  -- the index of the step function g_i at level m
--   q i m  -- the index of f_i at recursion argument S^m(bot)
------------------------------------------------------------------------

module Walk (r : Nat)
            (c : Nat -> Nat -> Nat)
            (q : Nat -> Nat -> Nat)
            (qS : (i m : Nat) -> Eq (q i (suc m)) (pickM r (c i m) (\ s -> q s m)))
            (L : Nat) (C : Nat -> Nat)
            (stab : (i m : Nat) -> LeN L m -> Eq (c i m) (C i))
            where

  ----------------------------------------------------------------------
  -- the walk EXITS at i: the index is constant from L+1 on
  ----------------------------------------------------------------------

  exit : (i : Nat) -> Not (LeN (suc (C i)) r) -> (m : Nat) -> LeN L m
       -> Eq (q i (suc m)) (suc (predIter r (C i)))
  exit i out m lm =
    Eq-trans (qS i m)
      (Eq-trans (Eq-cong (\ z -> pickM r z (\ s -> q s m)) (stab i m lm))
        (pickM-out r (C i) (\ s -> q s m) out))

  exit-const : (i : Nat) -> Not (LeN (suc (C i)) r) -> EvConstN (q i)
  exit-const i out = mkSigma (suc L) ev
    where
      ev : (n : Nat) -> LeN (suc L) n -> Eq (q i n) (q i (suc L))
      ev zero    ()
      ev (suc m) lm =
        Eq-trans (exit i out m lm) (Eq-sym (exit i out L (LeN-refl L)))

  ----------------------------------------------------------------------
  -- the walk STEPS at i
  ----------------------------------------------------------------------

  step : (i : Nat) -> LeN (suc (C i)) r -> (m : Nat) -> LeN L m
       -> Eq (q i (suc m)) (q (C i) m)
  step i ins m lm =
    Eq-trans (qS i m)
      (Eq-trans (Eq-cong (\ z -> pickM r z (\ s -> q s m)) (stab i m lm))
        (pickM-in r (C i) (\ s -> q s m) ins))

  ----------------------------------------------------------------------
  -- descending t levels follows C for t steps
  ----------------------------------------------------------------------

  InRange : Nat -> Nat -> Set
  InRange t i = (j : Nat) -> LeN (suc j) t -> LeN (suc (C (pIter C j i))) r

  descend : (t i m : Nat) -> LeN L m -> InRange t i
          -> Eq (q i (add m t)) (q (pIter C t i) m)
  descend zero    i m lm ir = refl
  descend (suc t) i m lm ir =
    Eq-trans
      (step i (ir zero tt) (add m t)
        (LeN-trans {L} {m} {add m t} lm (add-ge m t)))
      (descend t (C i) m lm (\ j lj -> ir (suc j) lj))

  ----------------------------------------------------------------------
  -- PERIODICITY, on the cycle of C through i
  ----------------------------------------------------------------------

  module Cyc (Crange : (j : Nat) -> LeN (suc j) r -> LeN (suc (C j)) r) where

    inrange : (t i : Nat) -> LeN (suc i) r -> InRange t i
    inrange t i li j lj = Crange (pIter C j i) (orbit-range r C Crange i li j)

    -- the cycle point, its period, and the periodicity of the index there
    periodic-at : (i : Nat) -> LeN (suc i) r ->
      Sigma Nat (\ j ->
        Pair (LeN (suc j) r)
        (Sigma Nat (\ d ->
          Pair (LeN (suc zero) d)
          (Pair (LeN d r)
          (Pair (Eq (pIter C d j) j)
                ((m : Nat) -> LeN L m -> Eq (q j (add m d)) (q j m)))))))
    periodic-at i li =
      mkSigma j (mkSigma lj
        (mkSigma d (mkSigma d1 (mkSigma dr (mkSigma cyc per)))))
      where
        cy : Cycle r C i
        cy = orbit-cycle r C Crange i li

        a : Nat
        a = fst cy

        d : Nat
        d = fst (snd cy)

        d1 : LeN (suc zero) d
        d1 = fst (snd (snd cy))

        dr : LeN d r
        dr = fst (snd (snd (snd cy)))

        j : Nat
        j = pIter C a i

        lj : LeN (suc j) r
        lj = orbit-range r C Crange i li a

        cyc : Eq (pIter C d j) j
        cyc = snd (snd (snd (snd cy)))

        per : (m : Nat) -> LeN L m -> Eq (q j (add m d)) (q j m)
        per m lm =
          Eq-trans (descend d j m lm (inrange d j lj))
            (Eq-cong (\ z -> q z m) cyc)

------------------------------------------------------------------------
-- r = 1: PERIOD 1, HENCE CONSTANT
--
-- With a single recursive call the walk can only stay on component 0, so
-- the cycle has `1 <= d <= 1`, and periodicity with period 1 IS eventual
-- constancy.  No bounded search, no appeal to the Proposition, and no
-- uniqueness of the index -- which is why Colson's original lemma is the
-- easy case of the manuscript's argument.
------------------------------------------------------------------------

LeN-zero' : (k : Nat) -> LeN k zero -> Eq k zero
LeN-zero' zero    le = refl
LeN-zero' (suc k) ()

module One (c : Nat -> Nat -> Nat)
           (q : Nat -> Nat -> Nat)
           (qS : (i m : Nat) -> Eq (q i (suc m))
                                   (pickM (suc zero) (c i m) (\ s -> q s m)))
           (L : Nat) (C : Nat -> Nat)
           (stab : (i m : Nat) -> LeN L m -> Eq (c i m) (C i))
           where

  open Walk (suc zero) c q qS L C stab

  one-const : EvConstN (q zero)
  one-const = route (LeN-dec (suc (C zero)) (suc zero))
    where
      route : Dec (LeN (suc (C zero)) (suc zero)) -> EvConstN (q zero)
      -- the walk exits: the index is a parameter, constant from L+1 on
      route (no out) = exit-const zero out
      -- the walk continues: with r = 1 it can only stay at component 0,
      -- so `q 0 (m+1) = q 0 m` and the index is constant from L on
      route (yes ins) = mkSigma L go'
        where
          c0 : Eq (C zero) zero
          c0 = LeN-zero' (C zero) ins

          stepq : (m : Nat) -> LeN L m -> Eq (q zero (suc m)) (q zero m)
          stepq m lm =
            Eq-trans (step zero ins m lm) (Eq-cong (\ z -> q z m) c0)

          go : (t : Nat) -> Eq (q zero (add L t)) (q zero L)
          go zero    = refl
          go (suc t) = Eq-trans (stepq (add L t) (add-ge L t)) (go t)

          go' : (n : Nat) -> LeN L n -> Eq (q zero n) (q zero L)
          go' n ln =
            Eq-transport (\ z -> Eq (q zero z) (q zero L))
              (snd (le-to-add L n ln)) (go (fst (le-to-add L n ln)))
