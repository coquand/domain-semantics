{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterCompose
--
-- COMPOSITION AROUND THE CYCLE, in the form the two counterexamples force.
--
-- Going once around a cycle of length d in the read-graph composes the
-- per-edge responses into a single  Phi : Nat -> Nat, and the case-3
-- witness of the component obeys the d-step recurrence
--
--   DStep k d phi Phi  =  (m >= k) -> phi (m + d) = Phi (phi m)
--
-- `IterCycleFail` shows the DECISION cannot be read off the individual
-- edges (pred and succ are each strictly increasing, yet their composite
-- is the identity and the block stabilises).  It has to be read off Phi:
--
--   * Phi(x) > x on the orbit  ->  StrictIncBy k d phi   (`Phi-grows-IncBy`)
--   * Phi(phi k) = phi k       ->  phi constant along the d-progression
--                                                        (`Phi-fixed-const`)
--
-- and since each per-edge response is monotone, so is Phi, and the chain
-- is non-decreasing (`uVec-mono`), so Phi(x) >= x on the orbit and the two
-- cases above are exhaustive and decidable pointwise (`orbit-dichotomy`).
--
-- THE POINT.  This reduces mutual iteration to ONE monotone operator Phi
-- on Nat -- exactly the situation the unary development already handles.
-- The read-graph's job shrinks to finding the cycle and its length d
-- (which is what `PhiPeriod.StrictIncBy` needs as its period); the
-- divergence decision is then the existing unary `PrecInfDispatch` test
-- applied to Phi, not a graph-liveness test.
--
-- Both counterexample blocks are re-derived here from the abstract lemma,
-- as a check that it does the work: `half-IncBy2-via-compose` (Phi = suc)
-- and `cycle-const-via-compose` (Phi = identity).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterCompose where

open import OBSTINATION.Prelude
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)
open import OBSTINATION.PhiPeriod using (StrictIncBy ; stepN ; stepN-ge ; two)
open import OBSTINATION.IterPhiFail using (half)

------------------------------------------------------------------------
-- The d-step recurrence produced by one turn of the cycle
------------------------------------------------------------------------

DStep : Nat -> Nat -> (Nat -> Nat) -> (Nat -> Nat) -> Set
DStep k d phi Phi = (m : Nat) -> LeN k m -> Eq (phi (addN m d)) (Phi (phi m))

------------------------------------------------------------------------
-- If one turn of the cycle strictly increases the height, the component
-- satisfies the refined invariant with period d
------------------------------------------------------------------------

Phi-grows-IncBy : (k d : Nat) (phi Phi : Nat -> Nat) ->
  DStep k d phi Phi ->
  ((x : Nat) -> LeN (suc x) (Phi x)) ->
  StrictIncBy k d phi
Phi-grows-IncBy k d phi Phi rec gr m km =
  Eq-transport (\ z -> LeN (suc (phi m)) z) (Eq-sym (rec m km)) (gr (phi m))

-- the growth hypothesis is only ever needed on the values phi takes,
-- so here is the version restricted to the orbit
Phi-grows-IncBy-orbit : (k d : Nat) (phi Phi : Nat -> Nat) ->
  DStep k d phi Phi ->
  ((m : Nat) -> LeN k m -> LeN (suc (phi m)) (Phi (phi m))) ->
  StrictIncBy k d phi
Phi-grows-IncBy-orbit k d phi Phi rec gr m km =
  Eq-transport (\ z -> LeN (suc (phi m)) z) (Eq-sym (rec m km)) (gr m km)

------------------------------------------------------------------------
-- If one turn returns where it started, the component is constant along
-- the d-progression  k, k+d, k+2d, ...
------------------------------------------------------------------------

Phi-fixed-const : (k d : Nat) (phi Phi : Nat -> Nat) ->
  DStep k d phi Phi ->
  Eq (Phi (phi k)) (phi k) ->
  (n : Nat) -> Eq (phi (stepN k d n)) (phi k)
Phi-fixed-const k d phi Phi rec fx zero    = refl
Phi-fixed-const k d phi Phi rec fx (suc n) =
  Eq-trans (rec (stepN k d n) (stepN-ge k d n))
    (Eq-trans (Eq-cong Phi (Phi-fixed-const k d phi Phi rec fx n)) fx)

------------------------------------------------------------------------
-- The two cases are exhaustive on a non-decreasing orbit
--
-- The Kleene chain never loses height (`IterSeq.uVec-mono`), so
-- Phi (phi m) >= phi m; comparing with equality splits it into the two
-- branches above.  This is where the unary dispatch has to be applied to
-- Phi -- knowing Phi(x) > x at ONE point is not enough for StrictIncBy,
-- exactly as in the unary case.
------------------------------------------------------------------------

orbit-dichotomy : (x y : Nat) -> LeN x y -> Or (Eq y x) (LeN (suc x) y)
orbit-dichotomy zero    zero    le = inl refl
orbit-dichotomy zero    (suc y) le = inr tt
orbit-dichotomy (suc x) zero    ()
orbit-dichotomy (suc x) (suc y) le = shift (orbit-dichotomy x y le)
  where
    shift : Or (Eq y x) (LeN (suc x) y) -> Or (Eq (suc y) (suc x)) (LeN (suc x) y)
    shift (inl e)  = inl (Eq-cong suc e)
    shift (inr lt) = inr lt

------------------------------------------------------------------------
-- Check: the abstract lemma re-derives both counterexamples
------------------------------------------------------------------------

-- IterPhiFail's block: cycle proj/succ, one turn adds one.
--   half (m+2) = suc (half m),  so Phi = suc.
half-DStep : DStep zero two half suc
half-DStep m km = refl

half-IncBy2-via-compose : StrictIncBy zero two half
half-IncBy2-via-compose =
  Phi-grows-IncBy zero two half suc half-DStep (\ x -> LeN-refl x)

-- IterCycleFail's block: cycle pred/succ, one turn is the identity.
--   the component is constantly 0, so Phi = id has phi k as a fixed point.
zeroPhi : Nat -> Nat
zeroPhi m = zero

idPhi : Nat -> Nat
idPhi x = x

cycle-DStep : DStep zero two zeroPhi idPhi
cycle-DStep m km = refl

cycle-const-via-compose : (n : Nat) ->
  Eq (zeroPhi (stepN zero two n)) (zeroPhi zero)
cycle-const-via-compose =
  Phi-fixed-const zero two zeroPhi idPhi cycle-DStep refl
