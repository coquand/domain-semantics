{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MPGrow
--
-- THE GROWTH CLAUSE (G) OF THE REFINED MAIN PROPERTY.
--
-- A function with a trace is a pair (iv, kv).  The refined Main Property
-- of such a function is
--
--     MP iv kv = (I) EvConstN iv                -- the index settles
--              & (G) GV kv                      -- the height is classified
--
-- with
--
--     GV k = EvBndN k                   -- eventually constant, sup ATTAINED
--          + GrowN  k                   -- grows by >= 1 every p steps past M
--
-- and `p >= 1`, `M` EXISTENTIALLY QUANTIFIED DATA, with NO bound on `p`
-- (the period multiplies under composition and under a cross-cycle, so any
-- bound -- e.g. David's `p <= r` -- would not survive; see
-- NEXT_SESSION_MP_CMUT.md sec 5).
--
-- This is the `(lag, increment, threshold)` form: `Classes.Cmut`'s
-- `cmut-mstep`, `MutUOWeak.Case3w`, `MutInv`'s invariant.  The point of
-- carrying the period is that the disjunction becomes a COMPUTATION and not
-- a decision: "does k ever pass K?" is answered by
--
--     grow-unb : GrowN k -> (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (k s))
--
-- with the explicit witness  s = (K+1)*p + M  -- whereas from the bare
-- verdict "bounded or unbounded" (the old `MainComp.HV`) it is Sigma-0-1 and
-- has to be ASSUMED.  `gv-pass` is that answer as a decision procedure, and
-- it is what replaces `MainComp.hdec`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MPGrow where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r ; nle-lt)
open import OBSTINATION.MPPass using (HPass ; plus-ge-l ; plus-assoc)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

-- j copies of q  (recursion on j, so that mulp (suc j) q = plus q (mulp j q))
mulp : Nat -> Nat -> Nat
mulp zero    q = zero
mulp (suc j) q = plus q (mulp j q)

mulp-pos : (p q : Nat) -> LeN (suc zero) p -> LeN (suc zero) q ->
  LeN (suc zero) (mulp p q)
mulp-pos zero    q ()  lq
mulp-pos (suc j) q lp  lq =
  LeN-trans {suc zero} {q} {plus q (mulp j q)} lq (plus-ge-l q (mulp j q))

------------------------------------------------------------------------
-- THE TWO HALVES OF (G)
------------------------------------------------------------------------

-- eventually constant with the supremum ATTAINED at a given point
EvBndN : (Nat -> Nat) -> Set
EvBndN k = Sigma Nat (\ M -> (s : Nat) -> LeN (k s) (k M))

-- grows by at least one every p steps past the threshold M
GrowN : (Nat -> Nat) -> Set
GrowN k =
  Sigma Nat (\ p -> Sigma Nat (\ M ->
    Pair (LeN (suc zero) p)
         ((n : Nat) -> LeN M n -> LeN (suc (k n)) (k (plus p n)))))

-- the verdict (G)
GV : (Nat -> Nat) -> Set
GV k = Or (EvBndN k) (GrowN k)

-- the (G)-flavoured Main Property.  NOT the invariant any more -- (G) is not
-- closed under mutual recursion (`BlkGrowFail`); see `MPPass.MP`.
MPG : (Nat -> Nat) -> (Nat -> Nat) -> Set
MPG iv kv = Pair (EvConstN iv) (GV kv)

------------------------------------------------------------------------
-- ITERATING A PERIODIC INCREMENT
--
-- One increment every p steps, iterated j times, is j increments every
-- j*p steps -- with the period MULTIPLIED, which is the whole point.
------------------------------------------------------------------------

step-iter : (u : Nat -> Nat) (p M : Nat) ->
  ((n : Nat) -> LeN M n -> LeN (suc (u n)) (u (plus p n))) ->
  (j n : Nat) -> LeN M n -> LeN (plus j (u n)) (u (plus (mulp j p) n))
step-iter u p M st zero    n ln = LeN-refl (u n)
step-iter u p M st (suc j) n ln =
  Eq-transport (\ z -> LeN (suc (plus j (u n))) (u z))
    (Eq-sym (plus-assoc p (mulp j p) n))
    (LeN-trans {suc (plus j (u n))} {suc (u n')} {u (plus p n')}
      (step-iter u p M st j n ln)
      (st n' (LeN-trans {M} {n} {n'} ln (plus-ge-r (mulp j p) n))))
  where
    n' : Nat
    n' = plus (mulp j p) n

------------------------------------------------------------------------
-- (G) DECIDES "DOES THE HEIGHT PASS K?" -- BY COMPUTATION
------------------------------------------------------------------------

grow-unb : (k : Nat -> Nat) -> GrowN k -> (K : Nat) ->
  Sigma Nat (\ s -> LeN (suc K) (k s))
grow-unb k (mkSigma p (mkSigma M (mkSigma p1 st))) K =
  mkSigma (plus (mulp (suc K) p) M)
    (LeN-trans {suc K} {plus (suc K) (k M)} {k (plus (mulp (suc K) p) M)}
      (plus-ge-l (suc K) (k M))
      (step-iter k p M st (suc K) M (LeN-refl M)))

gv-pass : (k : Nat -> Nat) -> GV k -> HPass k
gv-pass k (inl (mkSigma M bnd)) K = pick (LeN-dec (k M) K)
  where
    pick : Dec (LeN (k M) K) ->
      Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K)
    pick (yes l)  = inr (\ s -> LeN-trans {k s} {k M} {K} (bnd s) l)
    pick (no  nl) = inl (mkSigma M (nle-lt (k M) K nl))
gv-pass k (inr gr) K = inl (grow-unb k gr K)

------------------------------------------------------------------------
-- (G) TRANSPORTS ALONG A POINTWISE EQUALITY
------------------------------------------------------------------------

gv-cong : (k k' : Nat -> Nat) -> ((n : Nat) -> Eq (k n) (k' n)) -> GV k -> GV k'
gv-cong k k' e (inl (mkSigma M bnd)) = inl (mkSigma M bnd')
  where
    bnd' : (s : Nat) -> LeN (k' s) (k' M)
    bnd' s =
      Eq-transport (\ z -> LeN z (k' M)) (e s)
        (Eq-transport (\ z -> LeN (k s) z) (e M) (bnd s))
gv-cong k k' e (inr (mkSigma p (mkSigma M (mkSigma p1 st)))) =
  inr (mkSigma p (mkSigma M (mkSigma p1 st')))
  where
    st' : (n : Nat) -> LeN M n -> LeN (suc (k' n)) (k' (plus p n))
    st' n ln =
      Eq-transport (\ z -> LeN (suc z) (k' (plus p n))) (e n)
        (Eq-transport (\ z -> LeN (suc (k n)) z) (e (plus p n)) (st n ln))

------------------------------------------------------------------------
-- A BOUNDED MONOTONE HEIGHT IS EVENTUALLY EXACTLY CONSTANT
------------------------------------------------------------------------

evbnd-const : (k : Nat -> Nat) ->
  ((n n' : Nat) -> LeN n n' -> LeN (k n) (k n')) ->
  (M : Nat) -> ((s : Nat) -> LeN (k s) (k M)) ->
  (s : Nat) -> LeN M s -> Eq (k s) (k M)
evbnd-const k mono M bnd s ls = LeN-antisym {k s} {k M} (bnd s) (mono M s ls)
