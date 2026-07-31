{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterCycleComp
--
-- COMPOSING THE CASE-3 DESCRIPTIONS AROUND THE CYCLE.
--
-- `IterCompose` states and uses the d-step recurrence `DStep k d psi Phi`.
-- This file DERIVES it, from the one-step law that the verdicts of the
-- step functions supply.
--
-- Write  psi i m  for the height of component i at the m-th iterate, and
-- p for the read-graph successor (component i consults slot p i, which is
-- single-valued by Colson Prop. 3.4 -- at most one argument stops a
-- computation).  The verdict of h_i gives its response phi i, hence the
--
--   ONE-STEP LAW    psi i (m+1) = phi i (psi (p i) m)        (m >= k)
--
-- Iterating it d times walks the read-graph d steps (`around`):
--
--   psi i (m+d) = Comp i d (psi (p^d i) m)
--
-- where `Comp i d = phi i o phi (p i) o ... o phi (p^{d-1} i)`.  When i
-- lies on a cycle of length d, p^d i = i and this IS `DStep`
-- (`cycle-DStep`) -- the composite `Comp i d` is the operator Phi that
-- `IterCompose` and `IterDich` then dispatch on.
--
-- CHECK.  Instantiating at the `IterPhiFail` block -- p swaps 0 and 1,
-- phi_0 = identity (a projection), phi_1 = successor -- the machinery
-- computes  Comp 0 2 = suc  and re-derives `DStep 0 2 half suc`, which
-- `IterCompose.half-DStep` had to assert by hand.
--
-- WHAT IS STILL ASSUMED.  The one-step law is taken as a hypothesis here.
-- Discharging it from `uoh` is the remaining bookkeeping: it means
-- checking that the case-3 side conditions (length, threshold k, the
-- del-domination of the approximant) hold at the actual iterate tuples.
-- Note that this is entirely in the FINITE world -- `iterVec` works on
-- FTup -- so no Scott extension is involved.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterCycleComp where

open import OBSTINATION.Prelude
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)
open import OBSTINATION.IterCompose using (DStep)
open import OBSTINATION.IterPhiFail using (half ; two)

------------------------------------------------------------------------
-- Walking the read-graph, and the composite response along the walk
------------------------------------------------------------------------

module _ (p : Nat -> Nat) where

  -- p^d applied to i
  pIter : Nat -> Nat -> Nat
  pIter zero    i = i
  pIter (suc d) i = pIter d (p i)

module _ (p : Nat -> Nat) (phi : Nat -> Nat -> Nat) where

  -- phi i o phi (p i) o ... o phi (p^{d-1} i)
  Comp : Nat -> Nat -> Nat -> Nat
  Comp i zero    x = x
  Comp i (suc d) x = phi i (Comp (p i) d x)

------------------------------------------------------------------------
-- From the one-step law to the d-step law
------------------------------------------------------------------------

module _ (k : Nat) (p : Nat -> Nat) (phi : Nat -> Nat -> Nat)
         (psi : Nat -> Nat -> Nat)
         (one-step : (i m : Nat) -> LeN k m ->
                     Eq (psi i (suc m)) (phi i (psi (p i) m)))
         where

  -- d steps along the graph
  around : (d i m : Nat) -> LeN k m ->
    Eq (psi i (addN m d)) (Comp p phi i d (psi (pIter p d i) m))
  around zero    i m km = refl
  around (suc d) i m km =
    Eq-trans
      (one-step i (addN m d)
        (LeN-trans {k} {m} {addN m d} km (LeN-addN-l m d)))
      (Eq-cong (phi i) (around d (p i) m km))

  -- on a cycle of length d the walk returns, and the d-step law is DStep
  cycle-DStep : (d i : Nat) -> Eq (pIter p d i) i ->
    DStep k d (psi i) (Comp p phi i d)
  cycle-DStep d i cyc m km =
    Eq-trans (around d i m km)
             (Eq-cong (\ j -> Comp p phi i d (psi j m)) cyc)

------------------------------------------------------------------------
-- CHECK: the IterPhiFail block, re-derived
--
--   f_1(S x) = f_2(x)      -- component 0 consults slot 1, response = id
--   f_2(S x) = S(f_1(x))   -- component 1 consults slot 0, response = suc
------------------------------------------------------------------------

pB : Nat -> Nat
pB zero            = suc zero
pB (suc zero)      = zero
pB (suc (suc j))   = zero

phiB : Nat -> Nat -> Nat
phiB zero          x = x
phiB (suc zero)    x = suc x
phiB (suc (suc j)) x = zero

psiB : Nat -> Nat -> Nat
psiB zero          m = half m
psiB (suc zero)    m = half (suc m)
psiB (suc (suc j)) m = zero

-- the one-step law holds on the nose for this block
one-stepB : (i m : Nat) -> LeN zero m ->
  Eq (psiB i (suc m)) (phiB i (psiB (pB i) m))
one-stepB zero          m km = refl
one-stepB (suc zero)    m km = refl
one-stepB (suc (suc j)) m km = refl

-- component 0 lies on a 2-cycle
cycleB : Eq (pIter pB two zero) zero
cycleB = refl

-- and one turn of that cycle is the successor
CompB-is-suc : (x : Nat) -> Eq (Comp pB phiB zero two x) (suc x)
CompB-is-suc x = refl

-- so DStep for phi_1 = floor(m/2) comes out of the machinery
blockB-DStep : DStep zero two half (Comp pB phiB zero two)
blockB-DStep = cycle-DStep zero pB phiB psiB one-stepB two zero cycleB

-- component 1 likewise lies on a 2-cycle, with the same composite
cycleB1 : Eq (pIter pB two (suc zero)) (suc zero)
cycleB1 = refl

blockB-DStep1 : DStep zero two (psiB (suc zero)) (Comp pB phiB (suc zero) two)
blockB-DStep1 = cycle-DStep zero pB phiB psiB one-stepB two (suc zero) cycleB1
