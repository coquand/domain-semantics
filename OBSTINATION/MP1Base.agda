{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MP1Base
--
-- THE BASE CASES OF THE TRACE: `zerf`, `proj i`, `succ`.
--
-- With `MP1Comp` (composition) and `MP1Prec` (primitive recursion) these
-- complete the structural definition of a trace `(iv , kv)` for every PR
-- term, and the proof that MP1 holds of it -- everything except the
-- BRIDGE `evalF p X = fbot (kv (nOf a iv ivr (levels X)))`, which is the
-- next step.
--
-- All three base terms have a CONSTANT sequentiality index, so their
-- replay is completely explicit (`Const.nOf-const`):
--
--     iv = \ _ -> i   ==>   nOf a iv ivr av = av i
--
-- because the walk raises only coordinate `i` (`lv i n = n`) and so
-- sticks exactly when it has consumed `av i` of it.  The three traces are
-- then read off the three defining equations of `PR.evalF`:
--
--   proj i   arity a   iv = \ _ -> i   kv n = n
--                      evalF (proj i) X = X_i        -- height `av i`
--   succ     arity 1   iv = \ _ -> 0   kv n = suc n
--                      evalF succ (x) = sucF x       -- height `av 0 + 1`
--   zerf     arity a   iv = \ _ -> 0   kv n = zero
--                      evalF zerf X = fcpl zero      -- COMPLETE, so the
--                      bridge equation never fires and `kv` is a
--                      convention; `zero` is the one that makes it
--                      `ConstFrom zero`.
--
-- `proj` and `succ` are `StrictIncFrom zero`, `zerf` is `ConstFrom zero`
-- -- the two halves of `PhiOK` are both already used at the leaves.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MP1Base where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using (LeN-suc-not)
open import OBSTINATION.MPPass using (Mono)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; lv ; Adv ; nOf ; nOf-ge ; nOf-le)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1

------------------------------------------------------------------------
-- THE INVARIANT AT THE LEAVES
------------------------------------------------------------------------

evconst-const : (i : Nat) -> EvConstN (\ _ -> i)
evconst-const i = mkSigma zero (\ n _ -> refl)

mono-const : (v : Nat) -> Mono (\ _ -> v)
mono-const v m m' le = LeN-refl v

mono-id : Mono (\ n -> n)
mono-id m m' le = le

mono-suc : Mono (\ n -> suc n)
mono-suc m m' le = le

phiok-const : (v : Nat) -> PhiOK (\ _ -> v)
phiok-const v = mkSigma zero (inl (\ _ _ -> refl))

phiok-id : PhiOK (\ n -> n)
phiok-id = mkSigma zero (inr (\ m _ -> LeN-refl (suc m)))

phiok-suc : PhiOK (\ n -> suc n)
phiok-suc = mkSigma zero (inr (\ m _ -> LeN-refl (suc (suc m))))

------------------------------------------------------------------------
-- A CONSTANT INDEX MAKES THE REPLAY EXPLICIT
--
-- The walk raises only coordinate `i`, so `l_i (n) = n` and every other
-- level is 0.  The advance test at step `n` is therefore `n < av i`, and
-- the replay sticks exactly at `av i`.
------------------------------------------------------------------------

module Const (a i : Nat) (ivr : (n : Nat) -> LeN (suc i) a) where

  iv : Nat -> Nat
  iv _ = i

  lv-const : (n : Nat) -> Eq (lv a iv ivr i n) n
  lv-const zero    = refl
  lv-const (suc n) =
    Eq-trans (bump-eq i (\ d -> lv a iv ivr d n) i refl)
      (Eq-cong suc (lv-const n))

  nOf-const : (av : Nat -> Nat) -> Eq (nOf a iv ivr av) (av i)
  nOf-const av = LeN-antisym {nOf a iv ivr av} {av i} le ge
    where
      ge : LeN (av i) (nOf a iv ivr av)
      ge = nOf-ge a iv ivr av (av i) hh
        where
          hh : (n : Nat) -> LeN (suc n) (av i) -> Adv a iv ivr av n
          hh n ln =
            Eq-transport (\ z -> LeN (suc z) (av i)) (Eq-sym (lv-const n)) ln

      le : LeN (nOf a iv ivr av) (av i)
      le = nOf-le a iv ivr av (av i) nb
        where
          nb : Not (Adv a iv ivr av (av i))
          nb ad =
            LeN-suc-not (av i)
              (Eq-transport (\ z -> LeN (suc z) (av i)) (lv-const (av i)) ad)

------------------------------------------------------------------------
-- proj i:  the height of the i-th argument
------------------------------------------------------------------------

module Proj (a i : Nat) (ivr : (n : Nat) -> LeN (suc i) a) where

  open Const a i ivr public

  kv : Nat -> Nat
  kv n = n

  kv-mono : Mono kv
  kv-mono = mono-id

  -- the trace really does compute the projection
  height : (av : Nat -> Nat) -> Eq (kv (nOf a iv ivr av)) (av i)
  height = nOf-const

  mp1 : MP1 iv kv
  mp1 = mkSigma (evconst-const i) phiok-id

------------------------------------------------------------------------
-- succ:  one more level than its single argument
------------------------------------------------------------------------

module Succ where

  a : Nat
  a = suc zero

  ivr : (n : Nat) -> LeN (suc zero) a
  ivr n = tt

  open Const a zero ivr public

  kv : Nat -> Nat
  kv n = suc n

  kv-mono : Mono kv
  kv-mono = mono-suc

  height : (av : Nat -> Nat) -> Eq (kv (nOf a iv ivr av)) (suc (av zero))
  height av = Eq-cong suc (nOf-const av)

  mp1 : MP1 iv kv
  mp1 = mkSigma (evconst-const zero) phiok-suc

------------------------------------------------------------------------
-- zerf:  the value is COMPLETE, so the trace's height is a convention
------------------------------------------------------------------------

module Zerf (a : Nat) (ivr : (n : Nat) -> LeN (suc zero) a) where

  open Const a zero ivr public

  kv : Nat -> Nat
  kv n = zero

  kv-mono : Mono kv
  kv-mono = mono-const zero

  mp1 : MP1 iv kv
  mp1 = mkSigma (evconst-const zero) (phiok-const zero)
