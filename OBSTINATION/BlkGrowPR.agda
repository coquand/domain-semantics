{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkGrowPR
--
-- `BlkGrowFail`'s BLOCK IS NOT REALISED BY ANY PR STEP TERMS.
--
-- `BlkGrowFail` exhibits a block at r = 2 whose two step terms satisfy
-- (I) and (G) and for which (G) of the block is LPO.  It is therefore
-- the natural candidate for "a mutual recursion
--
--     f_i (S x , y) = g_i (f_1 (x,y) , f_2 (x,y) , y)
--
-- whose value at (S^w(bot), S^w(bot)) is not computable".  IT IS NOT ONE.
--
-- Its step height is `kv 0 n = b n + n` for an arbitrary binary `b`, and
-- what makes the orbit LPO-hard is exactly that `b` may DROP from 1 to 0.
-- But Proposition 1 (`Prop1.prop1`, Case 3) gives every PR term a
-- `Property.PhiOK` witness -- constant, or STRICTLY increasing, past a
-- threshold the proof produces -- and `b n + n` has one only when `b` is
-- monotone past that threshold, which already decides LPO:
--
--     phiok-lpo : (k : Nat) -> PhiOK k kv0 -> LPOb
--
-- `ConstFrom` is impossible outright (`kv0 n >= n`), so `PhiOK` forces
-- `StrictIncFrom`, i.e. `b m <= b (m+1)` past `k`; a binary sequence that
-- never drops after `k` is decided by ONE test at `k` plus a bounded
-- search below it.
--
-- SO THE ABSTRACT-TRACE REFUTATION DOES NOT TRANSFER.  `BlkGrowFail`
-- refutes closure of the invariant (I)+(G) over ARBITRARY traces
-- `(iv, kv)`; it does not exhibit a real primitive recursive block whose
-- value at the all-infinite point is uncomputable, because its `kv` is
-- not the `kv` of any PR term.  Any counterexample must be built from
-- step terms that DO satisfy `PhiOK` -- and the case analysis then looks
-- decidable in every configuration (see the note at the end of this
-- file).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkGrowPR where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-mono ; le-nlt-eq ; LeN-suc-not)
open import OBSTINATION.MP1 using (le-add)
open import OBSTINATION.CapDet using (nle-lt)
open import OBSTINATION.Property using
  (PhiOK ; ConstFrom ; StrictIncFrom)
open import OBSTINATION.BlkGrowFail using (LPOb ; kv0 ; b-le1)

one : Nat
one = suc zero

module _ (b : Nat -> Nat)
         (bb : (n : Nat) -> Or (Eq (b n) zero) (Eq (b n) one))
         where

  KV : Nat -> Nat
  KV = kv0 b bb

  ------------------------------------------------------------------
  -- `kv0` IS NEVER EVENTUALLY CONSTANT: it is at least the identity
  ------------------------------------------------------------------

  const-imp : (k : Nat) -> ConstFrom k KV -> Empty
  const-imp k cf = LeN-suc-not k bad
    where
      e : Eq (KV (suc (suc k))) (KV k)
      e = cf (suc (suc k))
            (LeN-trans {k} {suc k} {suc (suc k)} (LeN-suc k) (LeN-suc (suc k)))

      lo : LeN (suc (suc k)) (KV (suc (suc k)))
      lo = plus-ge-r (b (suc (suc k))) (suc (suc k))

      hi : LeN (KV k) (suc k)
      hi = plus-mono (b k) one k k (b-le1 b bb k) (LeN-refl k)

      bad : LeN (suc k) k
      bad =
        LeN-trans {suc (suc k)} {KV k} {suc k}
          (Eq-transport (\ z -> LeN (suc (suc k)) z) e lo) hi

  ------------------------------------------------------------------
  -- SO `PhiOK` FORCES `b` NOT TO DROP PAST THE THRESHOLD
  ------------------------------------------------------------------

  no-drop : (k m : Nat) -> StrictIncFrom k KV -> LeN k m
          -> Eq (b m) one -> Eq (b (suc m)) one
  no-drop k m si lm e1 = route (bb (suc m))
    where
      route : Or (Eq (b (suc m)) zero) (Eq (b (suc m)) one) -> Eq (b (suc m)) one
      route (inr e) = e
      route (inl e0) = Empty-elim (LeN-suc-not m bad)
        where
          -- `kv0 m = m+1` and `kv0 (m+1) = m+1`, so the step is not strict
          step : LeN (suc (KV m)) (KV (suc m))
          step = si m lm

          e1' : Eq (KV m) (suc m)
          e1' = Eq-cong (\ z -> plus z m) e1

          e0' : Eq (KV (suc m)) (suc m)
          e0' = Eq-cong (\ z -> plus z (suc m)) e0

          bad : LeN (suc m) m
          bad =
            Eq-transport (\ z -> LeN (suc z) (suc m)) e1'
              (Eq-transport (\ z -> LeN (suc (KV m)) z) e0' step)

  -- ... hence it is 1 for ever above the threshold
  all-one : (k : Nat) -> StrictIncFrom k KV -> Eq (b k) one
          -> (t : Nat) -> Eq (b (plus t k)) one
  all-one k si e1 zero    = e1
  all-one k si e1 (suc t) =
    no-drop k (plus t k) si (plus-ge-r t k) (all-one k si e1 t)

  ------------------------------------------------------------------
  -- A BOUNDED SEARCH BELOW THE THRESHOLD
  ------------------------------------------------------------------

  find-lt : (k : Nat)
          -> Or (Sigma Nat (\ n -> Eq (b n) zero))
                ((n : Nat) -> LeN (suc n) k -> Eq (b n) one)
  find-lt zero    = inr (\ n ())
  find-lt (suc k) = step (find-lt k)
    where
      Res : Set
      Res =
        Or (Sigma Nat (\ n -> Eq (b n) zero))
           ((n : Nat) -> LeN (suc n) (suc k) -> Eq (b n) one)

      step : Or (Sigma Nat (\ n -> Eq (b n) zero))
                ((n : Nat) -> LeN (suc n) k -> Eq (b n) one)
           -> Res
      step (inl w)  = inl w
      step (inr hh) = route (bb k)
        where
          route : Or (Eq (b k) zero) (Eq (b k) one) -> Res
          route (inl e0) = inl (mkSigma k e0)
          route (inr e1) = inr ext
            where
              ext : (n : Nat) -> LeN (suc n) (suc k) -> Eq (b n) one
              ext n ln = pick (LeN-dec (suc n) k)
                where
                  pick : Dec (LeN (suc n) k) -> Eq (b n) one
                  pick (yes l)  = hh n l
                  pick (no  nl) =
                    Eq-transport (\ z -> Eq (b z) one)
                      (Eq-sym (le-nlt-eq n k ln nl)) e1

  ------------------------------------------------------------------
  -- THE POINT: `PhiOK` FOR THIS STEP HEIGHT ALREADY DECIDES LPO
  ------------------------------------------------------------------

  phiok-lpo : (k : Nat) -> PhiOK k KV -> LPOb b bb
  phiok-lpo k (inl cf) = Empty-elim (const-imp k cf)
  phiok-lpo k (inr si) = route (bb k)
    where
      route : Or (Eq (b k) zero) (Eq (b k) one) -> LPOb b bb
      route (inl e0) = inl (mkSigma k e0)
      route (inr e1) = below (find-lt k)
        where
          above : (n : Nat) -> LeN k n -> Eq (b n) one
          above n ln = rt (le-add k n ln)
            where
              rt : Sigma Nat (\ t -> Eq n (plus t k)) -> Eq (b n) one
              rt (mkSigma t e) =
                Eq-transport (\ z -> Eq (b z) one) (Eq-sym e)
                  (all-one k si e1 t)

          below : Or (Sigma Nat (\ n -> Eq (b n) zero))
                     ((n : Nat) -> LeN (suc n) k -> Eq (b n) one)
                -> LPOb b bb
          below (inl w)  = inl w
          below (inr hh) = inr ext
            where
              ext : (n : Nat) -> Eq (b n) one
              ext n = pick (LeN-dec (suc n) k)
                where
                  pick : Dec (LeN (suc n) k) -> Eq (b n) one
                  pick (yes l)  = hh n l
                  pick (no  nl) = above n (nle-lt (suc n) k nl)

------------------------------------------------------------------------
-- WHERE A REAL COUNTEREXAMPLE WOULD HAVE TO COME FROM
--
-- With `PhiOK` available for each step term AT A COMPUTABLE THRESHOLD --
-- which is what `Prop1.prop1` delivers -- the configurations of
--
--     f_i (S x , y) = g_i (f_1 (x,y) , f_2 (x,y) , y)
--
-- at the all-infinite point look decidable one by one.  Apply
-- Proposition 1 to `g_i` at `(S^w bot, S^w bot, S^w bot)`.  Case 2 is
-- impossible there (`PRInf.valOK`: it pins a coordinate that is
-- incomplete AND finite).  So each `g_i` is
--
--   * Case 1 -- complete above a finite approximant, so `f_i` is a
--     numeral once the iterates pass it;
--   * Case 3 -- pinned at ONE coordinate `c_i`, with `phi_i` constant or
--     strictly increasing past a computable `k_i`.  Then:
--       - `c_i` = the PARAMETER: `f_i` is eventually constant;
--       - `c_i` = ITSELF: a one-coordinate iteration `h(m+1) = phi_i(h m)`
--         with `phi_i` PhiOK, and ONE test at the first orbit point above
--         `k_i` decides bounded/unbounded, because `phi_i(x) >= x` on the
--         orbit and strict increase propagates `phi_i(x) > x` upward;
--       - `c_i` = the OTHER component: compose around the cycle, and
--         `PhiOK` IS closed under composition (const o anything = const,
--         strictly increasing o strictly increasing = strictly
--         increasing), so the same test applies to `phi_1 o phi_2`.
--
-- THE GAP is Case 3's side condition `X[c] >= A_0[c]`: it needs the
-- coordinates OTHER than the pinned one to have passed the approximant,
-- and if the other component stalls below it the clause never applies.
-- That is where a counterexample would have to live, and it is also
-- exactly what `MainBlk2.comp-verdict` ("frozen from D on, or replay past
-- its threshold at D") was built to handle.
------------------------------------------------------------------------
