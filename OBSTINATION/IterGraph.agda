{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterGraph
--
-- The READ-GRAPH of a mutual iteration block: which recursion slot each
-- step function h_i consults at the top of the Kleene chain.  This is the
-- constructive avatar of Colson's sequentiality index, and it is what
-- must replace `PrecInfDispatch` in the mutual case.
--
-- The top point is  topQ r Y = <inf,...,inf, Y>  (r infinite recursion
-- slots followed by the parameters).  Applying the JOINT obstination of H
-- there (`PropertyVec.UOMall`) gives one approximant and r verdicts;
-- `classify` reads each verdict off into:
--
--   indep     -- h_i does not consult any recursion slot
--   depC p    -- h_i consults slot p, with phi CONSTANT from its threshold
--   depI p    -- h_i consults slot p, with phi STRICTLY INCREASING
--
-- WHAT THIS FILE ESTABLISHES.  The classification itself, and two facts
-- about it: `case2-not-recursion` (case 2 can never consult a recursion
-- slot, so every edge into the block carries a phi) and
-- `case3-const-finite` / `case3-inc-infinite` (the phi-class is the
-- finite/infinite dichotomy of the response).
--
-- WARNING -- THE `depI` READING IS NOT SOUND.  An earlier reading of this
-- file took a cycle of `depI` edges to force divergence.  That is FALSE:
-- see `IterCycleFail`.  "phi strictly increasing" says the response grows
-- WITH the consulted value, not that it EXCEEDS it -- predecessor has
-- phi(m) = m-1, strictly increasing while losing height -- and a pred/succ
-- two-cycle has both edges `depI` yet stabilises at once, because one turn
-- of the cycle composes to the IDENTITY.
--
-- What decides divergence is the d-fold COMPOSITE Phi around the cycle,
-- not the classes of its edges: see `IterCompose`.  So the role of this
-- file is only to locate the cycle and its length d (the period that
-- `PhiPeriod.StrictIncBy` needs); the decision is the unary
-- `PrecInfDispatch` test applied to Phi.
--
-- `Diverges2` below is therefore a statement about LIVE PATHS ONLY, and
-- everything proved about it in `IterGraph2` is purely combinatorial and
-- remains valid; it is its interpretation as "this component diverges"
-- that the counterexample withdraws.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterGraph where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.PropertyAt
open import OBSTINATION.IterSeq using (appT)

------------------------------------------------------------------------
-- The top of the chain: all recursion slots infinite
------------------------------------------------------------------------

repT : Nat -> D -> Tup
repT zero    d = nil
repT (suc r) d = cons d (repT r d)

topQ : Nat -> Tup -> Tup
topQ r Y = appT (repT r inf) Y

-- every recursion slot of topQ is infinite
topQ-get : (r : Nat) (Y : Tup) (p : Nat) -> LeN (suc p) r ->
  Eq (get p (topQ r Y)) inf
topQ-get zero    Y p       ()
topQ-get (suc r) Y zero    lt = refl
topQ-get (suc r) Y (suc p) lt = topQ-get r Y p lt

------------------------------------------------------------------------
-- Projections out of a case-3 verdict
------------------------------------------------------------------------

-- f, A, A0 are EXPLICIT throughout: Case2at / Case3at / Case3 are
-- definitions, so their parameters occur only under Sigma/Pi bodies and
-- are not recoverable by unification from an argument's type.

module _ (f : FTup -> FEl) (A : Tup) (A0 : FTup) where

  c3-slot : Case3at f A A0 -> Nat
  c3-slot c = fst c

  c3-thr : Case3at f A A0 -> Nat
  c3-thr c = fst (snd (snd c))

  c3-phi : Case3at f A A0 -> (Nat -> Nat)
  c3-phi c = fst (snd (snd (snd (snd c))))

  c3-ok : (c : Case3at f A A0) -> PhiOK (c3-thr c) (c3-phi c)
  c3-ok c = fst (snd (snd (snd (snd (snd c)))))

  c3-inf : (c : Case3at f A A0) -> Eq (get (c3-slot c) A) inf
  c3-inf c = fst (snd c)

------------------------------------------------------------------------
-- Case 2 can never consult a recursion slot
--
-- Case 2 requires its pinned coordinate to be INCOMPLETE FINITE, and every
-- recursion slot of topQ is inf, for which `IncompleteFinite` is Empty.
-- So all edges into the recursion block come from case 3 -- which is what
-- makes the read-graph carry a phi (hence a phi-class) on every edge.
------------------------------------------------------------------------

c2-slot : (f : FTup -> FEl) (A : Tup) (A0 : FTup) -> Case2at f A A0 -> Nat
c2-slot f A A0 c = fst (snd c)

c2-incomplete : (f : FTup -> FEl) (A : Tup) (A0 : FTup) (c : Case2at f A A0) ->
  IncompleteFinite (get (c2-slot f A A0 c) A)
c2-incomplete f A A0 c = fst (snd (snd (snd c)))

case2-not-recursion : (r : Nat) (Y : Tup) (f : FTup -> FEl) (A0 : FTup)
  (c : Case2at f (topQ r Y) A0) ->
  LeN (suc (c2-slot f (topQ r Y) A0 c)) r -> Empty
case2-not-recursion r Y f A0 c lt =
  Eq-transport IncompleteFinite
    (topQ-get r Y (c2-slot f (topQ r Y) A0 c) lt)
    (c2-incomplete f (topQ r Y) A0 c)

------------------------------------------------------------------------
-- The classification
------------------------------------------------------------------------

data Dep (r : Nat) : Set where
  indep : Dep r                                   -- consults no recursion slot
  depC  : (p : Nat) -> LeN (suc p) r -> Dep r     -- slot p, phi constant
  depI  : (p : Nat) -> LeN (suc p) r -> Dep r     -- slot p, phi strictly increasing

-- UOat IS a data type, so its indices are recoverable here; they are
-- bound by name only to be passed on to the (explicit) projections.
classify : (r : Nat) {f : FTup -> FEl} {A : Tup} {Q0 : FTup} ->
  UOat f A Q0 -> Dep r
classify r (uo1at _) = indep
classify r (uo2at _) = indep
classify r {f} {A} {Q0} (uo3at c) =
  decide (LeN-dec (suc (c3-slot f A Q0 c)) r) (c3-ok f A Q0 c)
  where
    decide : Dec (LeN (suc (c3-slot f A Q0 c)) r) ->
             PhiOK (c3-thr f A Q0 c) (c3-phi f A Q0 c) -> Dep r
    decide (yes lt) (inl _) = depC (c3-slot f A Q0 c) lt
    decide (yes lt) (inr _) = depI (c3-slot f A Q0 c) lt
    decide (no _)   _       = indep

------------------------------------------------------------------------
-- A constant phi bounds the response: this is why a depC edge is dead
--
-- The extension value at an infinite coordinate is S^{phi(k)}(bot), a
-- FINITE element, when phi is constant from k on -- however far the
-- consulted slot climbs.  (In the strictly increasing case it is inf,
-- which is exactly when the edge is live.)
------------------------------------------------------------------------

IsConst : (f : FTup -> FEl) (A : Tup) -> Case3 f A -> Set
IsConst f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma (inl _) _)))))))) = Top
IsConst f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma (inr _) _)))))))) = Empty

case3-const-finite : (f : FTup -> FEl) (A : Tup) (c : Case3 f A) ->
  IsConst f A c -> Finite (uoValue (uo3 c))
case3-const-finite f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma _ (mkSigma (inl _) _)))))))) ic = tt
case3-const-finite f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma _ (mkSigma (inr _) _)))))))) ()

-- dually: a strictly increasing phi is exactly the infinite response
IsInc : (f : FTup -> FEl) (A : Tup) -> Case3 f A -> Set
IsInc f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma (inl _) _)))))))) = Empty
IsInc f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma (inr _) _)))))))) = Top

case3-inc-infinite : (f : FTup -> FEl) (A : Tup) (c : Case3 f A) ->
  IsInc f A c -> Eq (uoValue (uo3 c)) inf
case3-inc-infinite f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma _ (mkSigma (inl _) _)))))))) ()
case3-inc-infinite f A (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _
  (mkSigma _ (mkSigma _ (mkSigma (inr _) _)))))))) ii = refl

------------------------------------------------------------------------
-- Live edges, and the divergence criterion for r = 2
------------------------------------------------------------------------

data Live : Set where
  dead : Live
  live : Nat -> Live

liveOf : {r : Nat} -> Dep r -> Live
liveOf indep      = dead
liveOf (depC _ _) = dead
liveOf (depI p _) = live p

isLive : Live -> Set
isLive dead     = Empty
isLive (live _) = Top

isLive-dec : (l : Live) -> Dec (isLive l)
isLive-dec dead     = no (\ ())
isLive-dec (live _) = yes tt

-- with only two nodes, every slot is 0 or 1 ...
two : Nat
two = suc (suc zero)

below2 : (p : Nat) -> LeN (suc p) two -> Or (Eq p zero) (Eq p (suc zero))
below2 zero          lt = inl refl
below2 (suc zero)    lt = inr refl
below2 (suc (suc p)) ()

-- ... so a live path of length two has already entered a cycle, and the
-- criterion needs to look no further than two steps.
-- one step along the live edge out of a node whose edge is `l`
follow2 : (Nat -> Dep two) -> Live -> Set
follow2 ds dead     = Empty
follow2 ds (live p) = isLive (liveOf (ds p))

follow2-dec : (ds : Nat -> Dep two) (l : Live) -> Dec (follow2 ds l)
follow2-dec ds dead     = no (\ ())
follow2-dec ds (live p) = isLive-dec (liveOf (ds p))

Diverges2 : (Nat -> Dep two) -> Nat -> Set
Diverges2 ds i = follow2 ds (liveOf (ds i))

Diverges2-dec : (ds : Nat -> Dep two) (i : Nat) -> Dec (Diverges2 ds i)
Diverges2-dec ds i = follow2-dec ds (liveOf (ds i))
