{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrWalk
--
-- Plumbing for the correctness proofs:
--
--   * `den-sem` / `den-cont` -- the two components of `Den`, extracted
--     uniformly over `stop` and `node` (a `stop` has no continuations of
--     its own, but freezing a coordinate of a constant is that constant);
--
--   * `lv-L` -- a walk's level function IS the state `L k c` of the
--     recursion `L 0 = 0~`, `L (k+1) = bump (iv k) (L k)`.  Both are the
--     same recursion, so this is one induction, but it is what lets
--     `ReplayLv`'s `levels-below` and `stuck-level` be read on the state
--     a construction actually carries.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrWalk where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (bump ; bump-eq ; bump-ne ; lv ; nOf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrDen

------------------------------------------------------------------------
-- the two components of `Den`
------------------------------------------------------------------------

den-sem : (a : Nat) (T : Tr a) (f : FTup -> FEl) -> Den a T f
        -> (X : FTup) -> Eq (length X) a -> Eq (sem a T X) (f X)
den-sem a       (stop v)              f d X lx = d X lx
den-sem (suc a) (node iv ivr ov cont) f d X lx = fst d X lx

den-cont : (a : Nat) (T : Tr (suc a)) (f : FTup -> FEl) -> Den (suc a) T f
         -> (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
         -> Den a (contOf T c lc v) (\ Y -> f (ins c (fcpl v) Y))
den-cont a (stop w) f d c lc v = go
  where
    go : (Y : FTup) -> Eq (length Y) a -> Eq w (f (ins c (fcpl v) Y))
    go Y ly =
      d (ins c (fcpl v) Y)
        (Eq-trans
          (ins-len c (fcpl v) Y
            (Eq-transport (\ z -> LeN c z) (Eq-sym ly) lc))
          (Eq-cong suc ly))
den-cont a (node iv ivr ov cont) f d c lc v = snd d c lc v

------------------------------------------------------------------------
-- a walk's levels are the state it carries
------------------------------------------------------------------------

bump-cong : (i : Nat) (f g : Nat -> Nat) -> ((d : Nat) -> Eq (f d) (g d))
          -> (c : Nat) -> Eq (bump i f c) (bump i g c)
bump-cong i f g e c = route (EqNat-dec c i)
  where
    route : Dec (Eq c i) -> Eq (bump i f c) (bump i g c)
    route (yes q) =
      Eq-trans (bump-eq i f c q)
        (Eq-trans (Eq-cong suc (e c)) (Eq-sym (bump-eq i g c q)))
    route (no  nq) =
      Eq-trans (bump-ne i f c nq) (Eq-trans (e c) (Eq-sym (bump-ne i g c nq)))

lv-L : (a : Nat) (iv : Nat -> Nat)
       (ivr : (n : Nat) -> LeN (suc (iv n)) a)
       (L : Nat -> Nat -> Nat)
     -> ((c : Nat) -> Eq (L zero c) zero)
     -> ((k c : Nat) -> Eq (L (suc k) c) (bump (iv k) (L k) c))
     -> (k c : Nat) -> Eq (lv a iv ivr c k) (L k c)
lv-L a iv ivr L b0 bs zero    c = Eq-sym (b0 c)
lv-L a iv ivr L b0 bs (suc k) c =
  Eq-trans
    (bump-cong (iv k) (\ d -> lv a iv ivr d k) (L k) (lv-L a iv ivr L b0 bs k) c)
    (Eq-sym (bs k c))
