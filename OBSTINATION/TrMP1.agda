{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrMP1
--
-- MP1 FOR THE `ov`-VALUED TRACE: THE STATEMENT, AND THE BASE CASES.
--
-- min1.pdf's three cases are a THEOREM about the recorded value `ov`, not
-- data in the trace (`TraceDef`).  Written out:
--
--     Case 1   `ov` is eventually TOTAL                    (`EvTot`)
--     Case 2   `ov` is incomplete and eventually CONSTANT  \  `PhiOK` of
--     Case 3   `ov` is incomplete and STRICTLY INCREASING  /  the height
--
-- Cases 2 and 3 are exactly `MP1.PhiOK` applied to `\ n -> hgt (ov n)`,
-- which is why `PhiOK` is used verbatim: everything proved about it in
-- `MP1` (`phiok-comp`, `phiok-orbit`, `phiok-verdict`) is about that same
-- predicate.  Case 1 has to be separate: `hgt` cannot tell `fbot k` from
-- `fcpl k`, and that is precisely what refuted the old height-only trace
-- (`MP1BridgeFail`).
--
--     MP1T (node iv ivr ov cont) =
--         EvConstN iv , Verdict ov , (every continuation)
--
-- The continuation component is not decoration: `sem` reaches
-- `cont c lc v` only when the walk happens to stick on `c` at level `v`,
-- so -- exactly as for `TrDen.Den` -- the invariant has to be carried
-- structurally.
--
-- WHAT IS PROVED HERE: the three base cases, `zerf` / `proj i` / `succ`.
-- All three have a constant walk index, `proj` and `succ` are Case 3 from
-- step 0, and `zerf` is a `stop`.
--
-- WHAT IS OPEN: closure under `compTr` and `precTr`.  See
-- `NEXT_SESSION_TRACE.md` section 5 -- the old `MP1Comp.Comp.mp1` and
-- `MP1Prec` are the model, but they are theorems about the OLD walk, and
-- the new composite state is the composite's OWN LEVELS, so the "bounded
-- climb" has to be redone against `dep k i = nOfOf (Ths i) (L k)`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrMP1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl)

------------------------------------------------------------------------
-- THE INVARIANT
------------------------------------------------------------------------

-- Case 1: the computation eventually answers.  A total value is MAXIMAL,
-- so one such step is all it takes -- `ov` is constant from there by
-- `TrSat.cpl-max` and `MonoTr`.
EvTot : (Nat -> FEl) -> Set
EvTot ov = Sigma Nat (\ n -> IsCpl (ov n))

-- Cases 2 and 3.  The value is INCOMPLETE -- which is not a decoration:
-- a monotone `ov` that ever goes complete stays complete (`cpl-max`), so
-- "incomplete at arbitrarily large depths" is "incomplete everywhere",
-- and this branch is what lets a caller know a coordinate will NEVER
-- become a numeral.  Without it the two branches would not be a
-- trichotomy, only a covering.
Never : (Nat -> FEl) -> Set
Never ov = (n : Nat) -> Eq (ov n) (fbot (hgt (ov n)))

Verdict : (Nat -> FEl) -> Set
Verdict ov = Or (EvTot ov) (Pair (Never ov) (PhiOK (\ n -> hgt (ov n))))

MP1T : (a : Nat) -> Tr a -> Set
MP1T a       (stop v)              = Top
MP1T (suc a) (node iv ivr ov cont) =
  Pair (EvConstN iv)
    (Pair (Verdict ov)
      ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat) -> MP1T a (cont c lc v)))

-- THE INDEX HALF ALONE -- the trace's own walk and every continuation's.
-- `TrVerdict` shows the value half is Proposition 1 given this, so `IvAll`
-- is all that is left of MP1.
IvAll : (a : Nat) -> Tr a -> Set
IvAll a       (stop v)              = Top
IvAll (suc a) (node iv ivr ov cont) =
  Pair (EvConstN iv)
    ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat) -> IvAll a (cont c lc v))

-- ... and the value half alone, at one node
OvOK : (a : Nat) -> Tr a -> Set
OvOK a       (stop v)              = Top
OvOK (suc a) (node iv ivr ov cont) = Verdict ov

-- the decision half of a verdict: does the value ever become a numeral?
-- (`PhiOK` is irrelevant to it, and MP2 supplies the same thing)
verdict-TN : (ov : Nat -> FEl) -> Verdict ov -> Or (EvTot ov) (Never ov)
verdict-TN ov (inl et)               = inl et
verdict-TN ov (inr (mkSigma nev pk)) = inr nev

mp1T-ivAll : (a : Nat) (T : Tr a) -> MP1T a T -> IvAll a T
mp1T-ivAll a       (stop v)              m = tt
mp1T-ivAll (suc a) (node iv ivr ov cont) m =
  mkSigma (fst m)
    (\ c lc v -> mp1T-ivAll a (cont c lc v) (snd (snd m) c lc v))

------------------------------------------------------------------------
-- the two shapes the leaves use
------------------------------------------------------------------------

evconst-const : (i : Nat) -> EvConstN (\ _ -> i)
evconst-const i = mkSigma zero (\ n _ -> refl)

-- `S^n(bot)` and `S^(n+1)(bot)`: strictly increasing from step 0
phiok-id : PhiOK (\ n -> n)
phiok-id = mkSigma zero (inr (\ m lm -> LeN-refl (suc m)))

phiok-suc : PhiOK (\ n -> suc n)
phiok-suc = mkSigma zero (inr (\ m lm -> LeN-refl (suc (suc m))))

------------------------------------------------------------------------
-- zerf: a `stop`, so there is nothing to say
------------------------------------------------------------------------

zerfTr-mp1 : (a : Nat) -> MP1T a (zerfTr a)
zerfTr-mp1 a = tt

------------------------------------------------------------------------
-- proj i: constant index, value `S^n(bot)` -- Case 3.  Freezing the
-- projected coordinate stops; freezing any other gives a projection again.
------------------------------------------------------------------------

projTr-mp1 : (a i : Nat) (li : LeN (suc i) a) -> MP1T a (projTr a i li)
projTr-mp1 zero    i       ()
projTr-mp1 (suc a) i li =
  mkSigma (evconst-const i)
    (mkSigma (inr (mkSigma (\ n -> refl) phiok-id)) cn)
  where
    cn : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
       -> MP1T a (projCont a i li c lc v)
    cn c lc v = go (EqNat-dec i c) refl
      where
        go : (D : Dec (Eq i c)) -> Eq (EqNat-dec i c) D
           -> MP1T a (projCont a i li c lc v)
        go (yes ei) eD =
          Eq-transport (\ T -> MP1T a T)
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD)) tt
        go (no  ne) eD =
          Eq-transport (\ T -> MP1T a T)
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD))
            (projTr-mp1 a (sd c i) (sd-range a c i lc li ne))

------------------------------------------------------------------------
-- succ: constant index 0, value `S^(n+1)(bot)` -- Case 3
------------------------------------------------------------------------

succTr-mp1 : MP1T (suc zero) succTr
succTr-mp1 =
  mkSigma (evconst-const zero)
    (mkSigma (inr (mkSigma (\ n -> refl) phiok-suc)) (\ c lc v -> tt))
