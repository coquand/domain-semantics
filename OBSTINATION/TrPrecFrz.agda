{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecFrz
--
-- IMG_0270's LOOPING CRITERION, PROVED.
--
--     f (bot , z) = bot ,   f (S x , z) = h (x , f (x,z) , z)
--
-- Writing `h`'s sequence as `(n_p , x_p , y_p , z_p)` -- output height,
-- depth in `u`, depth in `v` (the recursive value), depths in `z` --
-- the criterion for `f` to loop in its first argument is
--
--     exists p .  y (p+1) = y p + 1   and   n_p <= y_p
--
-- Read on the walk, `y (p+1) = y p + 1` says `h` is stuck on the
-- RECURSIVE VALUE at step `p`, and then `stuck-level` says `y_p` is
-- exactly the height available there, i.e. `hgt (Vd L j)`, while `n_p` is
-- `hgt (Vd L (suc j))`.  So the criterion is simply
--
--     h is blocked on the recursive value, and the value did not grow.
--
-- `frz-step` shows that this state REPRODUCES ITSELF: the tuples at
-- depths `j` and `j+1` differ only at the recursion coordinate -- which
-- `h` is not waiting on -- so `TrSat.sem-sat` and `TrSat.blockOn-sat`
-- give the same value and the same block one depth up.  Hence, by
-- `frz`, `Vd` is constant from `j` on (min1.pdf Case 2) and `Qd` is too,
-- since a block on the recursive value makes `qsel` DESCEND
-- (`qsel prev (inr 1) = prev`).
--
-- That is exactly "la suite associee a f aura ultimement la forme
-- (n_p , x , z) , (n_p , x+1 , z) , ...".
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecFrz where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrPrec using (module R ; qsel)

------------------------------------------------------------------------
-- comparing two tuples built by `tup`
------------------------------------------------------------------------

tup-le : (a : Nat) (f g : Nat -> FEl)
       -> ((c : Nat) -> LeN (suc c) a -> LeF (f c) (g c))
       -> LeX (tup a f) (tup a g)
tup-le a f g h c = route (LeN-dec (suc c) a)
  where
    route : Dec (LeN (suc c) a)
          -> LeF (nth (fbot zero) c (tup a f)) (nth (fbot zero) c (tup a g))
    route (yes lc) =
      Eq-transport (\ z -> LeF z (nth (fbot zero) c (tup a g)))
        (Eq-sym (tup-nth a f c lc))
        (Eq-transport (\ z -> LeF (f c) z) (Eq-sym (tup-nth a g c lc)) (h c lc))
    route (no nc) =
      Eq-transport (\ z -> LeF z (nth (fbot zero) c (tup a g)))
        (Eq-sym (tup-out a f c nc))
        (Eq-transport (\ z -> LeF (fbot zero) z)
          (Eq-sym (tup-out a g c nc)) (LeF-refl (fbot zero)))

------------------------------------------------------------------------
-- THE FREEZE
------------------------------------------------------------------------

module F (p : Nat) (Th : Tr (suc (suc p))) (mth : MonoTr (suc (suc p)) Th)
         where

  open R p Th

  ah : Nat
  ah = suc (suc p)

  -- one depth up: the tuples differ only at the recursion coordinate
  step-le : (L : Nat -> Nat) (j : Nat) -> Eq (Vd L (suc j)) (Vd L j)
          -> LeX (avT L j) (avT L (suc j))
  step-le L j eV = tup-le ah (avf L j) (avf L (suc j)) go
    where
      go : (c : Nat) -> LeN (suc c) ah -> LeF (avf L j c) (avf L (suc j) c)
      go zero             lc = LeN-suc j
      go (suc zero)       lc =
        Eq-transport (\ z -> LeF (Vd L j) z) (Eq-sym eV) (LeF-refl (Vd L j))
      go (suc (suc c))    lc = LeF-refl (fbot (L (suc c)))

  step-agr : (L : Nat -> Nat) (j : Nat) -> Eq (Vd L (suc j)) (Vd L j)
           -> Agr (inr (suc zero)) (avT L j) (avT L (suc j))
  step-agr L j eV =
    Eq-trans (tup-nth ah (avf L j) (suc zero) tt)
      (Eq-trans (Eq-sym eV)
        (Eq-sym (tup-nth ah (avf L (suc j)) (suc zero) tt)))

  -- THE STATE REPRODUCES ITSELF
  frz-step : (L : Nat -> Nat) (j : Nat)
           -> Eq (blockOn ah Th (avT L j)) (inr (suc zero))
           -> Eq (Vd L (suc j)) (Vd L j)
           -> Pair (Eq (blockOn ah Th (avT L (suc j))) (inr (suc zero)))
                   (Eq (Vd L (suc (suc j))) (Vd L (suc j)))
  frz-step L j eB eV = mkSigma blk val
    where
      agr : Agr (blockOn ah Th (avT L j)) (avT L j) (avT L (suc j))
      agr =
        Eq-transport (\ r -> Agr r (avT L j) (avT L (suc j))) (Eq-sym eB)
          (step-agr L j eV)

      blk : Eq (blockOn ah Th (avT L (suc j))) (inr (suc zero))
      blk =
        Eq-trans
          (Eq-sym (blockOn-sat ah Th mth (avT L j) (avT L (suc j))
                     (step-le L j eV) agr))
          eB

      val : Eq (Vd L (suc (suc j))) (Vd L (suc j))
      val =
        Eq-sym (sem-sat ah Th mth (avT L j) (avT L (suc j))
                  (step-le L j eV) agr)

  -- ... FOR EVER
  frz : (L : Nat -> Nat) (j : Nat)
      -> Eq (blockOn ah Th (avT L j)) (inr (suc zero))
      -> Eq (Vd L (suc j)) (Vd L j)
      -> (t : Nat)
      -> Pair (Eq (blockOn ah Th (avT L (plus t j))) (inr (suc zero)))
              (Eq (Vd L (suc (plus t j))) (Vd L (plus t j)))
  frz L j eB eV zero    = mkSigma eB eV
  frz L j eB eV (suc t) = frz-step L (plus t j) (fst ih) (snd ih)
    where
      ih : Pair (Eq (blockOn ah Th (avT L (plus t j))) (inr (suc zero)))
                (Eq (Vd L (suc (plus t j))) (Vd L (plus t j)))
      ih = frz L j eB eV t

  ------------------------------------------------------------------
  -- CONSEQUENCE 1: the value is constant from `j` on -- min1.pdf Case 2
  ------------------------------------------------------------------

  Vd-frozen : (L : Nat -> Nat) (j : Nat)
            -> Eq (blockOn ah Th (avT L j)) (inr (suc zero))
            -> Eq (Vd L (suc j)) (Vd L j)
            -> (t : Nat) -> Eq (Vd L (plus t j)) (Vd L j)
  Vd-frozen L j eB eV zero    = refl
  Vd-frozen L j eB eV (suc t) =
    Eq-trans (snd (frz L j eB eV t)) (Vd-frozen L j eB eV t)

  ------------------------------------------------------------------
  -- CONSEQUENCE 2: so is the demand -- `h` blocked on the recursive
  -- value makes `qsel` DESCEND, so `Qd` stops moving
  ------------------------------------------------------------------

  Qd-frozen : (L : Nat -> Nat) (j : Nat)
            -> Eq (blockOn ah Th (avT L j)) (inr (suc zero))
            -> Eq (Vd L (suc j)) (Vd L j)
            -> (t : Nat) -> Eq (Qd L (plus t j)) (Qd L j)
  Qd-frozen L j eB eV zero    = refl
  Qd-frozen L j eB eV (suc t) =
    Eq-trans (Eq-cong (\ r -> qsel (Qd L (plus t j)) r) (fst (frz L j eB eV t)))
      (Qd-frozen L j eB eV t)

  ------------------------------------------------------------------
  -- ... i.e. `f`'s sequence is ultimately  (n , x , z) , (n , x+1 , z) ,
  -- ... : a constant value and an unchanging demand
  ------------------------------------------------------------------

  ultimate : (L : Nat -> Nat) (j : Nat)
           -> Eq (blockOn ah Th (avT L j)) (inr (suc zero))
           -> Eq (Vd L (suc j)) (Vd L j)
           -> (m : Nat) -> LeN j m
           -> Pair (Eq (Vd L m) (Vd L j)) (Eq (Qd L m) (Qd L j))
  ultimate L j eB eV m lm with le-add j m lm
    where
      le-add : (k n : Nat) -> LeN k n -> Sigma Nat (\ t -> Eq n (plus t k))
      le-add zero    n       _  = mkSigma n (Eq-sym (plus-zero n))
        where
          plus-zero : (n : Nat) -> Eq (plus n zero) n
          plus-zero zero    = refl
          plus-zero (suc n) = Eq-cong suc (plus-zero n)
      le-add (suc k) zero    ()
      le-add (suc k) (suc n) le with le-add k n le
      ... | mkSigma t e =
        mkSigma t (Eq-trans (Eq-cong suc e) (Eq-sym (plus-suc t k)))
        where
          plus-suc : (a b : Nat) -> Eq (plus a (suc b)) (suc (plus a b))
          plus-suc zero    b = refl
          plus-suc (suc a) b = Eq-cong suc (plus-suc a b)
  ... | mkSigma t e =
    mkSigma
      (Eq-transport (\ z -> Eq (Vd L z) (Vd L j)) (Eq-sym e)
        (Vd-frozen L j eB eV t))
      (Eq-transport (\ z -> Eq (Qd L z) (Qd L j)) (Eq-sym e)
        (Qd-frozen L j eB eV t))
