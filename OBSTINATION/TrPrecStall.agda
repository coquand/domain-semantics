{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecStall
--
-- **THE STALL DICHOTOMY: A STALL OF THE STEP TERM'S REPLAY IS PERMANENT.**
--
-- For  f(bot,Y) = bot ,  f(S^(j+1) bot,Y) = g(S^j bot, f(S^j bot,Y), Y),
-- let `NJ j` be `g`'s replay depth at recursion depth `j`.  `NJ` is
-- monotone; the question that governs everything is whether it EVER
-- stalls, and this file settles the shape of a stall:
--
--     stall-not-zero : NJ (j+1) = NJ j  ->  ivh (NJ j) /= 0
--
-- -- the replay can never stall on the RECURSION ARGUMENT.  Reason: at
-- depth `j` the walk got to step `NJ j`, so its levels are below what was
-- available there (`ReplayLv.find-below`), in particular
--
--     lv 0 (NJ j)  <=  AV j 0  =  j ,
--
-- while being still stuck at that same step one depth later would need
--
--     lv 0 (NJ j)  >=  AV (j+1) 0  =  j+1 .
--
-- The recursion argument is the one coordinate that grows by one per
-- depth ALL BY ITSELF, so it can never be what a stall waits on.
--
-- WHAT IT BUYS.  A stall must therefore be on the recursive value
-- (coordinate 1) or on a parameter, and both are permanent:
--
--   * a parameter never changes, so the replay stays stuck for ever;
--   * a stall pins the recursive value -- `V (j+2) = ovh (NJ (j+1))
--     = ovh (NJ j) = V (j+1)` (`TrPrecChain.step`) -- so coordinate 1
--     does not grow either, and the replay stays stuck for ever.
--
-- So the chain is EITHER frozen from the first stall on, OR `NJ` is
-- strictly increasing at every depth.  That dichotomy is what a
-- Proposition-1-free proof of MP1's VALUE clause for `precTr` needs; the
-- `EvTot` half of it is already used in `TrPrecDecMP`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecStall where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl)
open import OBSTINATION.BlkReplay using (nle-lt)
open import OBSTINATION.ReplayLv using
  (sumTo ; lv ; Adv ; nOf ; stuck ; Below ; find-below ; nOf-le ; nOf-mono)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrPrecChain using (Bt ; module CH)

------------------------------------------------------------------------
-- THE REPLAY'S LEVELS ARE BELOW WHAT WAS AVAILABLE
--
-- `ReplayLv` proves this inside `stuck`; here it is on its own, since the
-- stall dichotomy is exactly its contrapositive at coordinate 0.
------------------------------------------------------------------------

nOf-below : (a : Nat) (iv : Nat -> Nat)
            (ivr : (n : Nat) -> LeN (suc (iv n)) a)
            (av : Nat -> Nat)
          -> Below a iv ivr av (nOf a iv ivr av)
nOf-below a iv ivr av =
  find-below a iv ivr av zero (suc (sumTo a av)) (\ c -> tt)

------------------------------------------------------------------------
-- THE STALL DICHOTOMY
------------------------------------------------------------------------

module ST (p : Nat)
          (ivh : Nat -> Nat)
          (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
          (ovh : Nat -> FEl)
          (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                 -> Tr (suc p))
          (L : Nat -> Nat)
          where

  open CH p ivh ivhr ovh conth L

  -- being stuck at step `n` means the level reached there is already all
  -- that is available
  blocked : (j : Nat) -> LeN (AV j (ivh (NJ j))) (lv a ivh ivhr (ivh (NJ j)) (NJ j))
  blocked j =
    nle-lt (suc (lv a ivh ivhr (ivh (NJ j)) (NJ j))) (AV j (ivh (NJ j)))
      (stuck a ivh ivhr (AV j))

  -- ... and the levels reached are below what was available
  below : (j : Nat) (c : Nat) -> LeN (lv a ivh ivhr c (NJ j)) (AV j c)
  below j = nOf-below a ivh ivhr (AV j)

  -- THE LEMMA: the recursion argument grows on its own, so a stall can
  -- never be waiting on it
  stall-not-zero : (j : Nat) -> Eq (NJ (suc j)) (NJ j)
                 -> Not (Eq (ivh (NJ j)) zero)
  stall-not-zero j eq e0 = LeN-suc-not j bad
    where
      LeN-suc-not : (x : Nat) -> Not (LeN (suc x) x)
      LeN-suc-not zero    ()
      LeN-suc-not (suc x) l = LeN-suc-not x l

      -- still stuck one depth later, at the same step
      stuck' : LeN (AV (suc j) (ivh (NJ (suc j))))
                   (lv a ivh ivhr (ivh (NJ (suc j))) (NJ (suc j)))
      stuck' = blocked (suc j)

      -- read at the step `NJ j`, and at coordinate 0
      at0 : LeN (AV (suc j) zero) (lv a ivh ivhr zero (NJ j))
      at0 =
        Eq-transport (\ z -> LeN (AV (suc j) z) (lv a ivh ivhr z (NJ j))) e0
          (Eq-transport
            (\ n -> LeN (AV (suc j) (ivh n)) (lv a ivh ivhr (ivh n) n)) eq stuck')

      -- but at depth `j` the walk got past it with only `j` available
      bad : LeN (suc j) j
      bad =
        LeN-trans {suc j} {lv a ivh ivhr zero (NJ j)} {j}
          (Eq-transport (\ z -> LeN z (lv a ivh ivhr zero (NJ j)))
            (AV-zero (suc j)) at0)
          (Eq-transport (\ z -> LeN (lv a ivh ivhr zero (NJ j)) z)
            (AV-zero j) (below j zero))

  ------------------------------------------------------------------
  -- ... AND A STALL IS PERMANENT
  --
  -- The stalled coordinate is not the recursion argument, so it is the
  -- recursive value or a parameter -- and neither moves any more: a
  -- parameter never does, and the recursive value is pinned by the stall
  -- itself (`TrPrecChain.step` twice).  So the replay is stuck at the
  -- same step one depth later, and by induction for ever.
  ------------------------------------------------------------------

  le-not-suc : (x y : Nat) -> LeN x y -> Not (LeN (suc y) x)
  le-not-suc x y le l = nope y (LeN-trans {suc y} {x} {y} l le)
    where
      nope : (z : Nat) -> Not (LeN (suc z) z)
      nope zero    ()
      nope (suc z) l' = nope z l'

  stall-perm : (j : Nat) -> Bt (V j) -> Bt (V (suc j))
             -> Eq (NJ (suc j)) (NJ j)
             -> Eq (NJ (suc (suc j))) (NJ (suc j))
  stall-perm j bj bsj eq =
    LeN-antisym {NJ (suc (suc j))} {NJ (suc j)}
      (nOf-le a ivh ivhr (AV (suc (suc j))) (NJ (suc j)) still)
      (nOf-mono a ivh ivhr (AV (suc j)) (AV (suc (suc j))) grow)
    where
      n : Nat
      n = NJ (suc j)

      d : Nat
      d = ivh n

      nz : Not (Eq d zero)
      nz = Eq-transport (\ m -> Not (Eq (ivh m) zero)) (Eq-sym eq)
             (stall-not-zero j eq)

      -- the stall pins the recursive value
      same-V : Eq (V (suc (suc j))) (V (suc j))
      same-V =
        Eq-trans (step (suc j) bsj)
          (Eq-trans (Eq-cong ovh eq) (Eq-sym (step j bj)))

      -- so nothing but the recursion argument moves
      agree : (c : Nat) -> Not (Eq c zero) -> Eq (AV (suc j) c) (AV (suc (suc j)) c)
      agree c nc = route (LeN-dec (suc c) a)
        where
          route : Dec (LeN (suc c) a) -> Eq (AV (suc j) c) (AV (suc (suc j)) c)
          route (no ni) =
            Eq-trans (AV-out c ni (suc j)) (Eq-sym (AV-out c ni (suc (suc j))))
          route (yes li) = shape c li nc
            where
              shape : (e : Nat) -> LeN (suc e) a -> Not (Eq e zero)
                    -> Eq (AV (suc j) e) (AV (suc (suc j)) e)
              shape zero          le' ne = Empty-elim (ne refl)
              shape (suc zero)    le' ne =
                Eq-trans (AV-one (suc j))
                  (Eq-trans (Eq-cong hgt (Eq-sym same-V)) (Eq-sym (AV-one (suc (suc j)))))
              shape (suc (suc k)) le' ne = AV-par k (suc j) (suc (suc j)) le'

      grow : (c : Nat) -> LeN (AV (suc j) c) (AV (suc (suc j)) c)
      grow c = route (EqNat-dec c zero)
        where
          route : Dec (Eq c zero) -> LeN (AV (suc j) c) (AV (suc (suc j)) c)
          route (yes e) =
            Eq-transport (\ z -> LeN (AV (suc j) z) (AV (suc (suc j)) z)) (Eq-sym e)
              (Eq-transport (\ z -> LeN z (AV (suc (suc j)) zero))
                (Eq-sym (AV-zero (suc j)))
                (Eq-transport (\ z -> LeN (suc j) z) (Eq-sym (AV-zero (suc (suc j))))
                  (LeN-suc (suc j))))
          route (no ne) =
            Eq-transport (\ z -> LeN (AV (suc j) c) z) (agree c ne)
              (LeN-refl (AV (suc j) c))

      -- still stuck at the same step
      still : Not (Adv a ivh ivhr (AV (suc (suc j))) (NJ (suc j)))
      still =
        le-not-suc (AV (suc (suc j)) d) (lv a ivh ivhr d n)
          (Eq-transport (\ z -> LeN z (lv a ivh ivhr d n)) (agree d nz)
            (blocked (suc j)))
