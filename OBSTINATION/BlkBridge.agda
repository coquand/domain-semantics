{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkBridge
--
-- THE FIRST STEP OF THE REMAINING FRONT, AND IT IS FREE.
--
-- `BlkVerdict2.BLK` needs, for each step term,
--
--     Sigma Nat (\ k -> Property.PhiOK k (kv j)),
--
-- and `TrMP1.Verdict`'s second branch IS exactly that, at
-- `kv j = hgt o ov_j`.  The two `PhiOK`s -- `MP1.PhiOK` (which `TrMP1`
-- uses) and `Property.PhiOK` (which `BlkVerdict2` uses) -- unfold to the
-- same thing, so nothing has to be transported:
--
--     verdict-phiok : Verdict ov
--                   -> EvTot ov + Sigma k. PhiOK k (hgt o ov)
--
-- Since `TrTermIv.traceOf-MP1` gives `MP1T` for the trace of EVERY PR
-- term, the hypothesis of `BlkVerdict2.BLK` is available for real step
-- terms -- EXCEPT in the `EvTot` branch, where the step term's value goes
-- COMPLETE.  That branch is the whole remaining difficulty, and it is not
-- a gap in the argument but in the MODEL: `BlkTraceR`'s block trace is
-- HEIGHT-ONLY (`hv : Nat -> Nat -> Nat`), and a height cannot tell
-- `fbot k` from `fcpl k` -- which is exactly what `MP1BridgeFail`
-- refuted.  See `NEXT_SESSION_BLKVERDICT.md`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkBridge where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl)
open import OBSTINATION.TraceDef using (hgt)
open import OBSTINATION.TrMP1 using (Verdict ; EvTot)
open import OBSTINATION.Property using (PhiOK)

verdict-phiok : (ov : Nat -> FEl) -> Verdict ov
              -> Or (EvTot ov)
                    (Sigma Nat (\ k -> PhiOK k (\ n -> hgt (ov n))))
verdict-phiok ov (inl et)               = inl et
verdict-phiok ov (inr (mkSigma nev pk)) = inr pk
