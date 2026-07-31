{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterCycle
--
-- THE READ-GRAPH ALWAYS HAS A CYCLE, OF LENGTH d WITH 1 <= d <= r.
--
-- `IterOneStep.block-DStep` takes `Eq (pIter p d i) i` -- "i lies on a
-- cycle of length d" -- as a HYPOTHESIS, and the note records "d <= r"
-- as an argument (Colson Prop. 3.4 makes the read-graph functional, so
-- each component has one cycle, of length at most r) rather than a proof.
-- This file proves it.
--
-- The read-graph is a self-map of the r components: `IterOneStep.p-range`
-- shows `p` maps {0..r-1} into itself, because a case-3 verdict at the top
-- point can only consult a recursion slot (`topQ-inf-range`).  So the orbit
--
--   i,  p i,  p^2 i,  ...
--
-- stays in a set of r elements and must repeat within r+1 steps.  That is
-- pigeonhole, proved here from scratch (`pigeon`) since the development
-- uses no library: r+1 points, r values, so two indices a < b <= r agree,
-- and then  j = p^a i  satisfies  p^d j = j  with  d = b - a  in [1, r].
--
-- MAIN RESULTS
--
--   orbit-cycle      -- pure graph theory: any self-map of {0..r-1} has,
--                       from every start, a cycle on its orbit, 1<=d<=r
--   read-graph-cycle -- instantiated at the read-graph of a block
--   cycle-DStep-at   -- the payoff: EVERY component i leads to a node j on
--                       its orbit whose height sequence obeys the d-step
--                       recurrence, with no cycle hypothesis left
--
-- NB the cycle is on the ORBIT of i, not at i itself: a component may sit
-- on a tail leading into a cycle, and then its own heights obey no d-step
-- law.  That is the correct statement, and it is what `IterCompose` needs
-- -- the dichotomy is applied at the cycle.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterCycle where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF ; Below)
open import OBSTINATION.PropertyAt using (Case3at)
open import OBSTINATION.PropertyVec using (compOf)
open import OBSTINATION.PhiProps using (addN)
open import OBSTINATION.PhiComp using (le-to-addN)
open import OBSTINATION.IterFun using (IterData)
open import OBSTINATION.IterCompose using (DStep)
open import OBSTINATION.IterCycleComp using (pIter ; Comp)
open import OBSTINATION.IterGraph using (repT)
open import OBSTINATION.IterOneStep

-- the pigeonhole and its bounded search now live in their own Prelude-only
-- module (the trace-side block modules need them without the rest of this
-- development); re-exported here, so every earlier user is unaffected
open import OBSTINATION.Pigeon public

------------------------------------------------------------------------
-- Arithmetic odds and ends
------------------------------------------------------------------------

LeN-addN-r : (a d : Nat) -> LeN d (addN a d)
LeN-addN-r a zero    = tt
LeN-addN-r a (suc d) = LeN-addN-r a d

------------------------------------------------------------------------
-- Iterating the read-graph successor
------------------------------------------------------------------------

module _ (p : Nat -> Nat) where

  pIter-suc : (d i : Nat) -> Eq (pIter p (suc d) i) (p (pIter p d i))
  pIter-suc zero    i = refl
  pIter-suc (suc d) i = pIter-suc d (p i)

  pIter-add : (a d i : Nat) ->
    Eq (pIter p (addN a d) i) (pIter p d (pIter p a i))
  pIter-add a zero    i = refl
  pIter-add a (suc d) i =
    Eq-trans (pIter-suc (addN a d) i)
      (Eq-trans (Eq-cong p (pIter-add a d i))
                (Eq-sym (pIter-suc d (pIter p a i))))

------------------------------------------------------------------------
-- ANY self-map of {0..r-1} has a cycle on every orbit, of length 1..r
------------------------------------------------------------------------

Cycle : Nat -> (Nat -> Nat) -> Nat -> Set
Cycle r p i =
  Sigma Nat (\ a -> Sigma Nat (\ d ->
    Pair (LeN (suc zero) d) (Pair (LeN d r)
      (Eq (pIter p d (pIter p a i)) (pIter p a i)))))

module _ (r : Nat) (p : Nat -> Nat)
         (pr : (j : Nat) -> LeN (suc j) r -> LeN (suc (p j)) r) where

  orbit-range : (i : Nat) -> LeN (suc i) r ->
    (n : Nat) -> LeN (suc (pIter p n i)) r
  orbit-range i li zero    = li
  orbit-range i li (suc n) = orbit-range (p i) (pr i li) n

  orbit-cycle : (i : Nat) -> LeN (suc i) r -> Cycle r p i
  orbit-cycle i li =
    build (pigeon r (\ n -> pIter p n i) (\ j lj -> orbit-range i li j))
    where
      build : Repeat r (\ n -> pIter p n i) -> Cycle r p i
      build (mkSigma a (mkSigma b (mkSigma ab (mkSigma br e)))) =
        mkSigma a (mkSigma d (mkSigma d1 (mkSigma dr cyc)))
        where
          aleb : LeN a b
          aleb = LeN-trans {a} {suc a} {b} (LeN-suc a) ab

          rr = le-to-addN a b aleb
          d : Nat
          d = fst rr
          eqd : Eq (addN a d) b
          eqd = snd rr

          -- d >= 1: otherwise a = b, contradicting a < b
          d1 : LeN (suc zero) d
          d1 = nonzero d eqd
            where
              nonzero : (d' : Nat) -> Eq (addN a d') b -> LeN (suc zero) d'
              nonzero zero    eq0 =
                Empty-elim (LeN-suc-not a
                  (Eq-transport (\ z -> LeN (suc a) z) (Eq-sym eq0) ab))
              nonzero (suc _) _   = tt

          dr : LeN d r
          dr = LeN-trans {d} {b} {r}
                 (Eq-transport (\ z -> LeN d z) eqd (LeN-addN-r a d)) br

          cyc : Eq (pIter p d (pIter p a i)) (pIter p a i)
          cyc =
            Eq-sym
              (Eq-trans
                (Eq-transport (\ z -> Eq (pIter p a i) (pIter p z i)) (Eq-sym eqd) e)
                (pIter-add p a d i))

------------------------------------------------------------------------
-- Instantiated at the read-graph of a block
------------------------------------------------------------------------

module _ (idt : IterData) (Y : FTup) where
  open IterData idt

  ----------------------------------------------------------------------
  -- Generic in the analysis point (`IterOneStep.At`), re-exported at the
  -- top point: nothing here uses the point except as the source of the
  -- verdicts.
  ----------------------------------------------------------------------

  module Cyc (V : Tup) (lenV : Eq (length V) ar) where

    private module A = At idt Y V lenV

    -- Ax: one approximant per component (the constant family <Q0,...,Q0> is
    -- the joint analysis; `IterEach` uses each component's own)
    module _ (Ax : Nat -> FTup)
             (belAx : (i : Nat) -> LeN (suc i) ar -> Below (Ax i) A.P)
             (all3 : (i : Nat) -> LeN (suc i) ar ->
                     Case3at (compOf H i) A.P (Ax i)) where

      pB : Nat -> Nat
      pB = A.p Ax belAx all3

      -- every component's orbit meets a cycle of length between 1 and ar
      read-graph-cycle : (i : Nat) -> LeN (suc i) ar -> Cycle ar pB i
      read-graph-cycle = orbit-cycle ar pB (A.p-range Ax belAx all3)

      --------------------------------------------------------------------
      -- THE PAYOFF: no cycle hypothesis left
      --
      -- Given the stage N, every component i leads to a node j on its orbit
      -- whose height sequence obeys the d-step recurrence, for a period d
      -- computed from the read-graph.
      --------------------------------------------------------------------

      module _ (allbot : (j m : Nat) -> LeN (suc j) ar ->
                         Incompl (getF j (it idt Y m)))
               (N : Nat)
               (rN : (i : Nat) -> LeN (suc i) ar -> ReachAt idt Y (Ax i) N) where

        cycle-DStep-at : (i : Nat) -> LeN (suc i) ar ->
          Sigma Nat (\ j -> Sigma Nat (\ d ->
            Pair (LeN (suc zero) d) (Pair (LeN d ar)
              (DStep N d (psi idt Y j) (Comp pB (A.phi Ax belAx all3) j d)))))
        cycle-DStep-at i li = assemble (read-graph-cycle i li)
          where
            assemble : Cycle ar pB i ->
              Sigma Nat (\ j -> Sigma Nat (\ d ->
                Pair (LeN (suc zero) d) (Pair (LeN d ar)
                  (DStep N d (psi idt Y j) (Comp pB (A.phi Ax belAx all3) j d)))))
            assemble (mkSigma a (mkSigma d (mkSigma d1 (mkSigma dr cyc)))) =
              mkSigma (pIter pB a i) (mkSigma d (mkSigma d1 (mkSigma dr
                (A.block-DStep Ax belAx all3 allbot N rN d (pIter pB a i) cyc))))

  open Cyc (repT ar inf) (length-repT ar inf) public
