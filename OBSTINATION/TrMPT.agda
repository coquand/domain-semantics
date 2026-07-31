{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrMPT
--
-- **THE COMMON WEAKENING OF MP1 AND MP2.**
--
--     MPT a (stop v)              = Top
--     MPT (suc a) (node iv ivr ov cont) =
--       (I) EvConstN iv                          -- the demand settles
--       (S) OvSettles ov + OvUnbT ov             -- the value settles, or
--                                                   its height is UNBOUNDED
--       (H) every continuation again MPT
--
-- WHY.  `TrSelStab`, `CmutFed`, `CompCmut`, `TrFeedR` -- everything whose
-- CONCLUSION is not itself a `PhiOK` -- take `MP1T` as a hypothesis but
-- use only four things of it: the index threshold, the split
-- "settles or grows", the decision "ever complete or never", and the same
-- invariant at every continuation.  MP2 (`TrMP2`) supplies all four as
-- well (`TrMP2.verdict2-split`), with `OvGrows`'s rate -- one level per
-- step -- weakened to plain unboundedness.  `MPT` is exactly that common
-- part, so those files can be stated once and used from both sides:
--
--     mp1-mpT : MonoTr a T -> MP1T a T -> MPT a T
--     mp2-mpT : MonoTr a T -> MP2T a T -> MPT a T   (`TrMP2T`)
--
-- WHAT IS LOST IS THE RATE, AND NOTHING ELSE.  `UnbN` is constructive and
-- hands over an explicit witness, so every bounded search stays effective;
-- an argument of the form "after k stages the level has grown by k" simply
-- becomes "call `UnbN` at the level actually needed and use the `s` it
-- returns".
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrMPT where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.MP1 using (StrictIncFrom ; sinc-pass)
open import OBSTINATION.BlkReplay using (plus)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; leF-hgt ; MonoTr)
open import OBSTINATION.TrMono using (ovOf-mono)
open import OBSTINATION.TrMP1 using
  (EvTot ; Never ; Verdict ; MP1T ; IvAll)
open import OBSTINATION.TrCompSel using
  (OvSettles ; OvGrows ; verdict-split)

------------------------------------------------------------------------
-- SMALL FACTS
------------------------------------------------------------------------

-- an incomplete element IS its own bottom
notCpl-bt : (x : FEl) -> Not (IsCpl x) -> Eq x (fbot (hgt x))
notCpl-bt (fbot k) nc = refl
notCpl-bt (fcpl k) nc = Empty-elim (nc tt)

bt-notCpl : (x : FEl) -> Eq x (fbot (hgt x)) -> Not (IsCpl x)
bt-notCpl (fbot k) e ()
bt-notCpl (fcpl k) ()

IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
IsCpl-dec (fbot k) = no (\ z -> z)
IsCpl-dec (fcpl k) = yes tt

------------------------------------------------------------------------
-- THE CLAUSE
------------------------------------------------------------------------

-- unbounded, with a witness (identical to `BlkVerdict2.Unb`)
UnbN : (Nat -> Nat) -> Set
UnbN h = (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (h s))

-- never complete, and the height unbounded (identical to `TrMP2.OvUnb`)
OvUnbT : (Nat -> FEl) -> Set
OvUnbT ov = Pair (Never ov) (UnbN (\ n -> hgt (ov n)))

MPT : (a : Nat) -> Tr a -> Set
MPT a       (stop v)              = Top
MPT (suc a) (node iv ivr ov cont) =
  Pair (EvConstN iv)
    (Pair (Or (OvSettles ov) (OvUnbT ov))
      ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat) -> MPT a (cont c lc v)))

------------------------------------------------------------------------
-- THE PROJECTIONS, READ UNIFORMLY -- `stop` INCLUDED
------------------------------------------------------------------------

mpT-idx : (a : Nat) (T : Tr a) -> MPT a T -> EvConstN (ivOf T)
mpT-idx a       (stop v)              m = mkSigma zero (\ n ln -> refl)
mpT-idx (suc a) (node iv ivr ov cont) m = fst m

mpT-cont : (a : Nat) (T : Tr (suc a)) -> MPT (suc a) T
         -> (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
         -> MPT a (contOf T c lc v)
mpT-cont a (stop w)              m c lc v = tt
mpT-cont a (node iv ivr ov cont) m c lc v = snd (snd m) c lc v

mpT-split : (a : Nat) (T : Tr a) -> MPT a T
          -> Or (OvSettles (ovOf T)) (OvUnbT (ovOf T))
mpT-split a       (stop v)              m = inl (mkSigma zero (\ k lk -> refl))
mpT-split (suc a) (node iv ivr ov cont) m = fst (snd m)

mpT-ivAll : (a : Nat) (T : Tr a) -> MPT a T -> IvAll a T
mpT-ivAll a       (stop v)              m = tt
mpT-ivAll (suc a) (node iv ivr ov cont) m =
  mkSigma (fst m)
    (\ c lc v -> mpT-ivAll a (cont c lc v) (snd (snd m) c lc v))

------------------------------------------------------------------------
-- ... AND THE DECISION "EVER COMPLETE, OR NEVER"
--
-- `OvUnbT` carries `Never` outright.  If instead the value SETTLES at
-- `n1`, one test at `n1` decides it: a complete value is maximal, so a
-- complete value anywhere below `n1` would make `ov n1` complete too.
------------------------------------------------------------------------

settles-TN : (ov : Nat -> FEl)
           -> ((m n : Nat) -> LeN m n -> LeF (ov m) (ov n))
           -> OvSettles ov -> Or (EvTot ov) (Never ov)
settles-TN ov mono (mkSigma n1 con) = route (IsCpl-dec (ov n1))
  where
    route : Dec (IsCpl (ov n1)) -> Or (EvTot ov) (Never ov)
    route (yes ic) = inl (mkSigma n1 ic)
    route (no  nc) = inr (\ n -> notCpl-bt (ov n) (nn n))
      where
        nn : (n : Nat) -> Not (IsCpl (ov n))
        nn n ic = pick (LeN-total n1 n)
          where
            pick : Or (LeN n1 n) (LeN n n1) -> Empty
            pick (inl l) =
              nc (Eq-transport (\ z -> IsCpl z) (con n l) ic)
            pick (inr l) =
              nc (Eq-transport (\ z -> IsCpl z) (cpl-max (ov n) (ov n1) (mono n n1 l) ic) ic)

mpT-TN : (a : Nat) (T : Tr a) -> MonoTr a T -> MPT a T
       -> Or (EvTot (ovOf T)) (Never (ovOf T))
mpT-TN a T mt m = route (mpT-split a T m)
  where
    route : Or (OvSettles (ovOf T)) (OvUnbT (ovOf T))
          -> Or (EvTot (ovOf T)) (Never (ovOf T))
    route (inl st)               = settles-TN (ovOf T) (ovOf-mono a T mt) st
    route (inr (mkSigma nev un)) = inr nev

-- the same, in the shape the older files ask for
mpT-tot-or-never : (a : Nat) (T : Tr a) -> MonoTr a T -> MPT a T
                 -> Or (Sigma Nat (\ n0 -> IsCpl (ovOf T n0)))
                       ((m : Nat) -> Not (IsCpl (ovOf T m)))
mpT-tot-or-never a T mt m = route (mpT-TN a T mt m)
  where
    route : Or (EvTot (ovOf T)) (Never (ovOf T))
          -> Or (Sigma Nat (\ n0 -> IsCpl (ovOf T n0)))
                ((m : Nat) -> Not (IsCpl (ovOf T m)))
    route (inl et)  = inl et
    route (inr nev) = inr (\ m -> bt-notCpl (ovOf T m) (nev m))

------------------------------------------------------------------------
-- MP1 IMPLIES IT: `OvGrows` IS `OvUnbT` WITH A RATE
------------------------------------------------------------------------

grows-unb : (ov : Nat -> FEl) -> OvGrows ov -> OvUnbT ov
grows-unb ov (mkSigma nev (mkSigma n1 si)) =
  mkSigma nev
    (\ K -> mkSigma (plus (suc K) n1)
              (sinc-pass (\ n -> hgt (ov n)) n1 si K))

mp1-mpT : (a : Nat) (T : Tr a) -> MonoTr a T -> MP1T a T -> MPT a T
mp1-mpT a       (stop v)              mt m1 = tt
mp1-mpT (suc a) (node iv ivr ov cont) mt m1 =
  mkSigma (fst m1)
    (mkSigma (route (verdict-split ov (fst mt) (fst (snd m1))))
      (\ c lc v ->
         mp1-mpT a (cont c lc v) (snd mt c lc v) (snd (snd m1) c lc v)))
  where
    route : Or (OvSettles ov) (OvGrows ov) -> Or (OvSettles ov) (OvUnbT ov)
    route (inl st) = inl st
    route (inr gr) = inr (grows-unb ov gr)
