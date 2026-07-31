{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.WalkAffine
--
-- PAST ITS THRESHOLD, A REPLAY DEPTH IS AN AFFINE FUNCTION OF ONE HEIGHT.
--
-- Let a walk (iv, of arity a) have an eventually constant index: `iv n = I`
-- for every `n >= N`.  Then from `N` on the walk raises ONLY coordinate I, so
-- the levels of the other coordinates are frozen at their values at N, and
--
--     l_I (n) = (n - N) + l_I (N)          (`lv-run`)
--
-- Meanwhile the replay against available heights `av` is stuck exactly at the
-- level it needs at the coordinate it is stuck on (`stuck-level`: `<=` is
-- `levels-below`, `>=` is `stuck`).  Putting the two together, as soon as the
-- replay gets past N it is stuck on I and
--
--     nOf av = D + av I,      D + l_I (N) = N          (`affine`)
--
-- with D a CONSTANT of the walk alone -- the levels it has to spend elsewhere
-- before it settles.  So `kv (nOf av) = kv (D + av I)`: past its threshold a
-- step term's output height is a fixed monotone function of the height
-- available at ONE coordinate.
--
-- This is what turns a block component into a deterministic one-coordinate
-- iteration (`MPPass.IterF`), and it is the trace-level form of the
-- "(lag, increment, threshold)" computation of `MutInv` / `MutCross`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.WalkAffine where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r ; nle-lt)
open import OBSTINATION.MPPass using
  (plus-ge-l ; plus-assoc ; plus-comm ; le-plus)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; lv ; lv-le ; Adv ; nOf ; stuck ; nOf-below-adv ; levels-below)

-- D + (k + x) = k + (D + x)
plus-swap : (D k x : Nat) -> Eq (plus D (plus k x)) (plus k (plus D x))
plus-swap D k x =
  Eq-trans (Eq-sym (plus-assoc D k x))
    (Eq-trans (Eq-cong (\ z -> plus z x) (plus-comm D k)) (plus-assoc k D x))

module _ (a : Nat) (iv : Nat -> Nat)
         (ivr : (n : Nat) -> LeN (suc (iv n)) a)
         where

  ----------------------------------------------------------------------
  -- THE REPLAY IS STUCK EXACTLY AT THE LEVEL IT NEEDS
  ----------------------------------------------------------------------

  stuck-level : (av : Nat -> Nat) ->
    Eq (lv a iv ivr (iv (nOf a iv ivr av)) (nOf a iv ivr av))
       (av (iv (nOf a iv ivr av)))
  stuck-level av = LeN-antisym {lv a iv ivr c n} {av c} le ge
    where
      n : Nat
      n = nOf a iv ivr av

      c : Nat
      c = iv n

      le : LeN (lv a iv ivr c n) (av c)
      le = levels-below a iv ivr av n (nOf-below-adv a iv ivr av) c

      ge : LeN (av c) (lv a iv ivr c n)
      ge = nle-lt (suc (lv a iv ivr c n)) (av c) (stuck a iv ivr av)

  ----------------------------------------------------------------------
  -- PAST THE THRESHOLD ONLY ONE COORDINATE MOVES
  ----------------------------------------------------------------------

  module _ (N I : Nat) (stab : (n : Nat) -> LeN N n -> Eq (iv n) I) where

    lv-run : (k : Nat) ->
      Eq (lv a iv ivr I (plus k N)) (plus k (lv a iv ivr I N))
    lv-run zero    = refl
    lv-run (suc k) =
      Eq-trans
        (bump-eq (iv (plus k N)) (\ d -> lv a iv ivr d (plus k N)) I
          (Eq-sym (stab (plus k N) (plus-ge-r k N))))
        (Eq-cong suc (lv-run k))

    -- the constant offset: the levels the walk spends elsewhere
    Dof : Nat
    Dof = fst (le-plus (lv a iv ivr I N) N (lv-le a iv ivr I N))

    Dof-eq : Eq (plus Dof (lv a iv ivr I N)) N
    Dof-eq = snd (le-plus (lv a iv ivr I N) N (lv-le a iv ivr I N))

    ------------------------------------------------------------------
    -- THE AFFINE LAW
    ------------------------------------------------------------------

    affine : (av : Nat -> Nat) -> LeN N (nOf a iv ivr av) ->
      Eq (nOf a iv ivr av) (plus Dof (av I))
    affine av past = route (le-plus N (nOf a iv ivr av) past)
      where
        n : Nat
        n = nOf a iv ivr av

        -- past N the stuck coordinate is I
        atI : Eq (lv a iv ivr I n) (av I)
        atI =
          Eq-transport (\ z -> Eq (lv a iv ivr z n) (av z)) (stab n past)
            (stuck-level av)

        route : Sigma Nat (\ k -> Eq (plus k N) n) -> Eq n (plus Dof (av I))
        route (mkSigma k eq) =
          Eq-trans (Eq-sym eq)
            (Eq-trans (Eq-cong (\ z -> plus k z) (Eq-sym Dof-eq))
              (Eq-trans (Eq-sym (plus-swap Dof k (lv a iv ivr I N)))
                (Eq-cong (plus Dof) levI)))
          where
            -- av I = k + l_I(N)
            levI : Eq (plus k (lv a iv ivr I N)) (av I)
            levI =
              Eq-trans (Eq-sym (lv-run k))
                (Eq-trans (Eq-cong (\ z -> lv a iv ivr I z) eq) atI)
