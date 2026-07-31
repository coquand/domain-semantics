{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MPGrowFail2
--
-- THE (lag, increment, threshold) CLASS IS ALREADY REFUTED AT r = 2.
--
-- `MPGrow.GV` IS the (lag, increment, threshold) form -- its own header
-- says so: `Classes.Cmut`'s `cmut-mstep`, `MutUOWeak.Case3w`, `MutInv`'s
-- invariant.  Explicitly,
--
--     GV k = EvBndN k                      -- eventually constant
--          + GrowN  k                      -- exists p >= 1 and M with
--                                          --   k (p + n) >= k n + 1  (n >= M)
--
-- so the proposal "replace PhiOK's constant-or-STRICTLY-increasing by a
-- lag p, so that floor(m/2) is admitted (lag 2)" is exactly `GrowN`, and
-- the refined Main Property it suggests is exactly `MPGrow.MPG`.
--
-- `BlkGrowFail` refutes its closure under mutual recursion AT r = 2, and
-- the reason it applies is precisely that its counterexample lives in the
-- lag class rather than in `PhiOK`: the step height is
--
--     kv 0 n = b n + n          (b an arbitrary binary sequence)
--
-- which is NOT strictly increasing (b can drop from 1 to 0) but DOES grow
-- by at least one every TWO steps -- `BlkGrowFail.kv0-grow : GrowN kv0`,
-- lag 2, threshold 0.  So widening `PhiOK` to the lag class is exactly
-- what lets the counterexample in.
--
-- This file makes that explicit: from the closure statement one derives
-- LPO.  The statement is fixed at arity 2 and r = 2, which only makes it
-- WEAKER and so the refutation stronger.
--
-- What survives is `MPPass.HPass` -- the level-by-level verdict "does the
-- height ever pass K?" -- which holds for a block unconditionally, being
-- a deterministic monotone iteration (`MPPass.IterF.it-pass`).  See
-- `OBSTINATION/prinf.tex` s6 for why that is the right statement and not
-- a retreat.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MPGrowFail2 where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MPGrow using (GV)
open import OBSTINATION.BlkTraceR using (hv ; q)
open import OBSTINATION.BlkGrowFail using
  (LPOb ; blk-grow-lpo ; ivE ; ivrE ; kvE ; kvE-mono ; YE ; gvE)

one : Nat
one = suc zero

two : Nat
two = suc one

------------------------------------------------------------------------
-- THE CLOSURE STATEMENT, AT r = 2
--
-- "(I) and (G) for the two step terms give (I) and (G) for each block
-- component."
------------------------------------------------------------------------

MPG2 : Set
MPG2 =
  (iv : Nat -> Nat -> Nat)
  (ivr : (j n : Nat) -> LeN (suc (iv j n)) two)
  (kv : Nat -> Nat -> Nat)
  (kvm : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
  (Y : Nat -> Nat)
  -> ((j : Nat) -> EvConstN (iv j))
  -> ((j : Nat) -> GV (kv j))
  -> (j : Nat) -> LeN (suc j) two
  -> Pair (EvConstN (q two two iv ivr kv kvm Y j))
          (GV (\ m -> hv two two iv ivr kv kvm Y m j))

------------------------------------------------------------------------
-- ... AND IT IS LPO
------------------------------------------------------------------------

mpg-not-closed :
    (b : Nat -> Nat)
    (bb : (n : Nat) -> Or (Eq (b n) zero) (Eq (b n) one))
  -> MPG2 -> LPOb b bb
mpg-not-closed b bb cl =
  blk-grow-lpo b bb
    (snd (cl (ivE b bb) (ivrE b bb) (kvE b bb) (kvE-mono b bb) (YE b bb)
             ivEC (gvE b bb) zero tt))
  where
    ivEC : (j : Nat) -> EvConstN (ivE b bb j)
    ivEC zero    = mkSigma zero (\ n ln -> refl)
    ivEC (suc j) = mkSigma zero (\ n ln -> refl)
