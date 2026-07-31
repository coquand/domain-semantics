{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CapDet
--
-- CAPPED DETERMINATION OF THE STEP INDEX -- section 3.2 (a) of
-- `NEXT_SESSION_MP_HPASS.md`, and UNIFORMLY IN THE DEPTH.
--
--   cIdx j m = iv j (nOf a (iv j) (ivr j) (av m))
--
-- depends on the available heights `av m` ONLY THROUGH THEIR CAPS AT
-- `N j`, where `N j` is the (computable) `EvConstN (iv j)` threshold.
--
-- The reason is elementary and is the whole content: the replay's levels
-- satisfy `lv c n <= n` (`ReplayLv.lv-le`), so the advance test at step
-- `n < N` compares a number `< N` with `av c` -- and `v < x` iff
-- `v < min x N` when `v < N`.  Hence the first `N` steps of the walk are
-- identical at `av` and `av'`, so either both stick at the SAME step
-- below `N`, or both reach `N`; and `iv` cannot tell the latter two
-- apart, being constant from `N` on.
--
-- Nothing here mentions the depth, the block, or the parameters.  The
-- consequence drawn in `BlkFun` is that the parameter coordinate is
-- capped at `N j` in every replay -- uniformly in the depth -- unless
-- `iv j`'s eventual value IS the parameter, in which case the component
-- exits to it and the demand is settled anyway.
--
--   adv-cap  -- one step of the replay is cap-determined below N
--   reach    -- so is "the replay gets as far as k", for k <= N
--   nOf-cap  -- both reach N, or the stuck steps coincide
--   iv-cap   -- and then the step index agrees
--   cIdx-cap -- the two facts combined
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CapDet where

open import OBSTINATION.Prelude
open import OBSTINATION.ReplayLv using
  (lv ; lv-le ; Adv ; Adv-dec ; find ; find-yes ; find-no ; nOf ; stuck ; sumTo)
open import OBSTINATION.BlkReplay using (le-ne-lt ; LeN-suc-not)

------------------------------------------------------------------------
-- Cap arithmetic
------------------------------------------------------------------------

-- below the cap, "< x" and "< min x N" agree
lt-cap : (v x N : Nat) -> LeN (suc v) N -> LeN (suc v) x -> LeN (suc v) (minN x N)
lt-cap v       zero    N       lN ()
lt-cap v       (suc x) zero    () lx
lt-cap zero    (suc x) (suc N) lN lx = tt
lt-cap (suc v) (suc x) (suc N) lN lx = lt-cap v x N lN lx

cap-lt : (v x N : Nat) -> LeN (suc v) (minN x N) -> LeN (suc v) x
cap-lt v x N l = LeN-trans {suc v} {minN x N} {x} l (minN-le-l x N)

nle-lt : (m n : Nat) -> Not (LeN m n) -> LeN (suc n) m
nle-lt zero    n       nl = Empty-elim (nl tt)
nle-lt (suc m) zero    nl = tt
nle-lt (suc m) (suc n) nl = nle-lt m n nl

le-cases : (n x : Nat) -> LeN n x -> Or (Eq x n) (LeN (suc n) x)
le-cases n x le = route (EqNat-dec x n)
  where
    route : Dec (Eq x n) -> Or (Eq x n) (LeN (suc n) x)
    route (yes e)  = inl e
    route (no  ne) = inr (le-ne-lt n x le ne)

------------------------------------------------------------------------
-- The replay of one step term
------------------------------------------------------------------------

module _ (a : Nat) (iv : Nat -> Nat)
         (ivr : (n : Nat) -> LeN (suc (iv n)) a) where

  ----------------------------------------------------------------------
  -- Every step strictly below the stuck step does advance
  ----------------------------------------------------------------------

  find-pre : (av : Nat -> Nat) (n F s : Nat) -> LeN n s
           -> LeN (suc s) (find a iv ivr av n F) -> Adv a iv ivr av s
  find-pre av n zero s ln lt =
    Empty-elim (LeN-suc-not s (LeN-trans {suc s} {n} {s} lt ln))
  find-pre av n (suc F) s ln lt = route (Adv-dec a iv ivr av n)
    where
      route : Dec (Adv a iv ivr av n) -> Adv a iv ivr av s
      route (no nd) =
        Empty-elim (LeN-suc-not s (LeN-trans {suc s} {n} {s} lt' ln))
        where
          lt' : LeN (suc s) n
          lt' = Eq-transport (\ z -> LeN (suc s) z)
                  (find-no a iv ivr av n F nd) lt
      route (yes ad) = inner (EqNat-dec s n)
        where
          lt' : LeN (suc s) (find a iv ivr av (suc n) F)
          lt' = Eq-transport (\ z -> LeN (suc s) z)
                  (find-yes a iv ivr av n F ad) lt

          inner : Dec (Eq s n) -> Adv a iv ivr av s
          inner (yes e)  =
            Eq-transport (\ z -> Adv a iv ivr av z) (Eq-sym e) ad
          inner (no  ne) =
            find-pre av (suc n) F s (le-ne-lt n s ln ne) lt'

  nOf-pre : (av : Nat -> Nat) (s : Nat)
          -> LeN (suc s) (nOf a iv ivr av) -> Adv a iv ivr av s
  nOf-pre av s lt = find-pre av zero (suc (sumTo a av)) s tt lt

  ----------------------------------------------------------------------
  -- FACT 1: the replay, capped at N, is determined by the heights
  -- capped at N
  ----------------------------------------------------------------------

  Cap : Nat -> (Nat -> Nat) -> (Nat -> Nat) -> Set
  Cap N av av' = (c : Nat) -> Eq (minN (av c) N) (minN (av' c) N)

  adv-cap : (N : Nat) (av av' : Nat -> Nat) -> Cap N av av'
          -> (n : Nat) -> LeN (suc n) N
          -> Adv a iv ivr av n -> Adv a iv ivr av' n
  adv-cap N av av' cap n ln ad = cap-lt v (av' (iv n)) N capped'
    where
      v : Nat
      v = lv a iv ivr (iv n) n

      lvN : LeN (suc v) N
      lvN = LeN-trans {suc v} {suc n} {N} (lv-le a iv ivr (iv n) n) ln

      capped : LeN (suc v) (minN (av (iv n)) N)
      capped = lt-cap v (av (iv n)) N lvN ad

      capped' : LeN (suc v) (minN (av' (iv n)) N)
      capped' = Eq-transport (\ z -> LeN (suc v) z) (cap (iv n)) capped

  reach : (N : Nat) (av av' : Nat -> Nat) -> Cap N av av'
        -> (k : Nat) -> LeN k N
        -> LeN k (nOf a iv ivr av) -> LeN k (nOf a iv ivr av')
  reach N av av' cap zero    lk lr = tt
  reach N av av' cap (suc k) lk lr = route (le-cases k (nOf a iv ivr av') ih)
    where
      ih : LeN k (nOf a iv ivr av')
      ih = reach N av av' cap k
             (LeN-trans {k} {suc k} {N} (LeN-suc k) lk)
             (LeN-trans {k} {suc k} {nOf a iv ivr av} (LeN-suc k) lr)

      ad' : Adv a iv ivr av' k
      ad' = adv-cap N av av' cap k lk (nOf-pre av k lr)

      route : Or (Eq (nOf a iv ivr av') k) (LeN (suc k) (nOf a iv ivr av'))
            -> LeN (suc k) (nOf a iv ivr av')
      route (inl e)  =
        Empty-elim
          (stuck a iv ivr av'
            (Eq-transport (\ z -> Adv a iv ivr av' z) (Eq-sym e) ad'))
      route (inr le) = le

  nOf-cap : (N : Nat) (av av' : Nat -> Nat) -> Cap N av av'
          -> Or (Pair (LeN N (nOf a iv ivr av)) (LeN N (nOf a iv ivr av')))
                (Eq (nOf a iv ivr av) (nOf a iv ivr av'))
  nOf-cap N av av' cap = route (LeN-dec N (nOf a iv ivr av))
    where
      cap' : Cap N av' av
      cap' c = Eq-sym (cap c)

      route : Dec (LeN N (nOf a iv ivr av))
            -> Or (Pair (LeN N (nOf a iv ivr av)) (LeN N (nOf a iv ivr av')))
                  (Eq (nOf a iv ivr av) (nOf a iv ivr av'))
      route (yes le) =
        inl (mkSigma le (reach N av av' cap N (LeN-refl N) le))
      route (no  nl) = inr (small (le-cases n0 (nOf a iv ivr av') ge))
        where
          n0 : Nat
          n0 = nOf a iv ivr av

          ltN : LeN (suc n0) N
          ltN = nle-lt N n0 nl

          leN : LeN n0 N
          leN = LeN-trans {n0} {suc n0} {N} (LeN-suc n0) ltN

          ge : LeN n0 (nOf a iv ivr av')
          ge = reach N av av' cap n0 leN (LeN-refl n0)

          -- the stuck step of `av` is stuck for `av'` as well
          nadv' : Not (Adv a iv ivr av' n0)
          nadv' ad' =
            stuck a iv ivr av (adv-cap N av' av cap' n0 ltN ad')

          small : Or (Eq (nOf a iv ivr av') n0) (LeN (suc n0) (nOf a iv ivr av'))
                -> Eq n0 (nOf a iv ivr av')
          small (inl e)  = Eq-sym e
          small (inr le) = Empty-elim (nadv' (nOf-pre av' n0 le))

  ----------------------------------------------------------------------
  -- FACT 2: an eventually constant `iv` cannot tell apart two arguments
  -- with the same cap at its own threshold
  ----------------------------------------------------------------------

  iv-cap : (N : Nat) -> ((n : Nat) -> LeN N n -> Eq (iv n) (iv N))
         -> (n n' : Nat) -> Or (Pair (LeN N n) (LeN N n')) (Eq n n')
         -> Eq (iv n) (iv n')
  iv-cap N ev n n' (inl (mkSigma l l')) = Eq-trans (ev n l) (Eq-sym (ev n' l'))
  iv-cap N ev n n' (inr e)              = Eq-cong iv e

  ----------------------------------------------------------------------
  -- THE STEP INDEX IS CAP-DETERMINED AT `N`
  ----------------------------------------------------------------------

  cIdx-cap : (N : Nat) -> ((n : Nat) -> LeN N n -> Eq (iv n) (iv N))
           -> (av av' : Nat -> Nat) -> Cap N av av'
           -> Eq (iv (nOf a iv ivr av)) (iv (nOf a iv ivr av'))
  cIdx-cap N ev av av' cap =
    iv-cap N ev (nOf a iv ivr av) (nOf a iv ivr av') (nOf-cap N av av' cap)
