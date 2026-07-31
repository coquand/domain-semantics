{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompSel
--
-- WHEN DOES THE COMPOSITE'S SELECTION FREEZE?
--
-- `TrCompIv` reduced the composite's index clause to `SelStab`: the
-- demand `sel k = blockOn p Tg (vals k)` is eventually constant.  This
-- file settles the freezing half of that, outright.
--
--   * `sel-inl-stable` -- once `Tg` waits for NOTHING it never waits
--     again.  `TrSat.blockOn-sat` needs agreement only at the coordinate
--     `Tg` is waiting on, and `inl tt` waits on none, so the hypothesis
--     is vacuous.
--
--   * `sel-frozen` -- if `Tg` waits on `j` and the value at `j` never
--     moves again, `sel` never moves again.  Same lemma, at `inr j`.
--
--   * `verdict-split` -- MP1's `Verdict` is exactly the dichotomy the
--     caller wants: either `ov` is eventually CONSTANT (with a
--     computable threshold: Case 1 collapses by `cpl-max`, Case 2 by
--     `Never` plus a constant height), or its height is STRICTLY
--     INCREASING from a computable threshold (Case 3).
--
--   * `settles-frozen` -- putting the two together: if the SELECTED
--     argument's value settles, then `sel` freezes, as soon as the drive
--     (`TrCompIv.CI.Sel.dep-drive`) has pushed that argument's replay
--     past the threshold.
--
-- So `SelStab` reduces further, to the single remaining case:
--
--     the selected argument's value keeps GROWING (`OvGrows`).
--
-- There `sel` may legitimately stay put for ever -- `proj 0` never stops
-- waiting on coordinate 0 -- so stability cannot come from unblocking.
-- It has to come from `Tg`'s own bounded progress: `Tg`'s replay depth
-- passes its `EvConstN` threshold, or a coordinate goes complete and `Tg`
-- descends into a continuation (at most `p` times).  That is the bounded
-- climb of `MP1Comp`, and it is what is still OPEN.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompSel where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrComp
open import OBSTINATION.TrPrecFrz using (tup-le)
open import OBSTINATION.TrMono using (ovOf-mono ; nOfOf-mono)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict ; MP1T)
open import OBSTINATION.TrCompIv using (module CI)

------------------------------------------------------------------------
-- THE DICHOTOMY BEHIND `Verdict`
------------------------------------------------------------------------

-- the value sequence stops moving, from a computable threshold
OvSettles : (Nat -> FEl) -> Set
OvSettles ov =
  Sigma Nat (\ n1 -> (m : Nat) -> LeN n1 m -> Eq (ov m) (ov n1))

-- ... or it is NEVER complete and its height strictly increases, from a
-- computable threshold.  `Never` has to be carried: the caller needs to
-- know the coordinate will not go total behind its back.
OvGrows : (Nat -> FEl) -> Set
OvGrows ov =
  Pair (Never ov) (Sigma Nat (\ n1 -> StrictIncFrom n1 (\ n -> hgt (ov n))))

verdict-split : (ov : Nat -> FEl)
              -> ((m n : Nat) -> LeN m n -> LeF (ov m) (ov n))
              -> Verdict ov -> Or (OvSettles ov) (OvGrows ov)
-- Case 1: a total value is maximal, so everything above it is that value
verdict-split ov mono (inl (mkSigma n0 ic)) =
  inl (mkSigma n0
        (\ m lm -> Eq-sym (cpl-max (ov n0) (ov m) (mono n0 m lm) ic)))
-- Case 2: incomplete with a constant height IS constant
verdict-split ov mono (inr (mkSigma nev (mkSigma k1 (inl cf)))) =
  inl (mkSigma k1
        (\ m lm ->
           Eq-trans (nev m)
             (Eq-trans (Eq-cong fbot (cf m lm)) (Eq-sym (nev k1)))))
-- Case 3
verdict-split ov mono (inr (mkSigma nev (mkSigma k1 (inr si)))) =
  inr (mkSigma nev (mkSigma k1 si))

-- DOES THE VALUE EVER GO TOTAL?  `Verdict` decides it: Case 1 says yes
-- with a witness, Cases 2 and 3 say never.  A caller needs this to know
-- whether a coordinate will ever make `blockOn` descend.
ovTot-or-never : (a : Nat) (T : Tr a) -> MP1T a T
               -> Or (Sigma Nat (\ n0 -> IsCpl (ovOf T n0)))
                     ((m : Nat) -> Not (IsCpl (ovOf T m)))
ovTot-or-never a (stop v) m1 = route (IsCplD v)
  where
    IsCplD : (x : FEl) -> Dec (IsCpl x)
    IsCplD (fbot j) = no (\ z -> z)
    IsCplD (fcpl j) = yes tt

    route : Dec (IsCpl v)
          -> Or (Sigma Nat (\ n0 -> IsCpl (ovOf (stop {a} v) n0)))
                ((m : Nat) -> Not (IsCpl (ovOf (stop {a} v) m)))
    route (yes ic) = inl (mkSigma zero ic)
    route (no  nc) = inr (\ m -> nc)
ovTot-or-never (suc a) (node iv ivr ov cont) m1 = route (fst (snd m1))
  where
    route : Verdict ov
          -> Or (Sigma Nat (\ n0 -> IsCpl (ov n0)))
                ((m : Nat) -> Not (IsCpl (ov m)))
    route (inl et) = inl et
    route (inr (mkSigma nev _)) =
      inr (\ m ic -> Eq-transport (\ z -> IsCpl z) (nev m) ic)

-- a `stop` argument settles at once
stop-settles : (a : Nat) (T : Tr a) -> MonoTr a T -> MP1T a T
             -> ((m n : Nat) -> LeN m n -> LeF (ovOf T m) (ovOf T n))
             -> Or (OvSettles (ovOf T)) (OvGrows (ovOf T))
stop-settles a       (stop v)              mt m1 mono =
  inl (mkSigma zero (\ m lm -> refl))
stop-settles (suc a) (node iv ivr ov cont) mt m1 mono =
  verdict-split ov mono (fst (snd m1))

------------------------------------------------------------------------
-- THE COMPOSITE
------------------------------------------------------------------------

module CS (p : Nat) (Tg : Tr p) (mtg : MonoTr p Tg)
          (a : Nat) (Ths : Nat -> Tr (suc a))
          (mTh : (i : Nat) -> MonoTr (suc a) (Ths i)) where

  module WW = W p Tg a Ths
  open CI p Tg a Ths using (L-mono ; dep-mono)

  --------------------------------------------------------------------
  -- what `Tg` sees, coordinate by coordinate
  --------------------------------------------------------------------

  valAt : Nat -> Nat -> FEl
  valAt k i = nth (fbot zero) i (WW.vals k)

  valAt-eq : (k i : Nat) -> LeN (suc i) p
           -> Eq (valAt k i) (ovOf (Ths i) (WW.dep k i))
  valAt-eq k i li = tup-nth p (\ d -> ovOf (Ths d) (WW.dep k d)) i li

  vals-mono : (k k' : Nat) -> LeN k k' -> LeX (WW.vals k) (WW.vals k')
  vals-mono k k' le =
    tup-le p (\ i -> ovOf (Ths i) (WW.dep k i))
             (\ i -> ovOf (Ths i) (WW.dep k' i))
      (\ i li ->
         ovOf-mono (suc a) (Ths i) (mTh i) (WW.dep k i) (WW.dep k' i)
           (dep-mono k k' le i))

  --------------------------------------------------------------------
  -- WAITING FOR NOTHING IS FOR EVER
  --------------------------------------------------------------------

  sel-inl-stable : (K : Nat) -> Eq (WW.sel K) (inl tt)
                 -> (k : Nat) -> LeN K k -> Eq (WW.sel k) (inl tt)
  sel-inl-stable K eK k lk =
    Eq-trans
      (Eq-sym
        (blockOn-sat p Tg mtg (WW.vals K) (WW.vals k) (vals-mono K k lk)
          (Eq-transport (\ r -> Agr r (WW.vals K) (WW.vals k))
            (Eq-sym eK) tt)))
      eK

  --------------------------------------------------------------------
  -- AND SO IS WAITING ON A COORDINATE THAT NEVER MOVES
  --------------------------------------------------------------------

  sel-frozen : (K j : Nat) -> Eq (WW.sel K) (inr j)
             -> ((k : Nat) -> LeN K k -> Eq (valAt K j) (valAt k j))
             -> (k : Nat) -> LeN K k -> Eq (WW.sel k) (WW.sel K)
  sel-frozen K j eK agree k lk =
    Eq-sym
      (blockOn-sat p Tg mtg (WW.vals K) (WW.vals k) (vals-mono K k lk)
        (Eq-transport (\ r -> Agr r (WW.vals K) (WW.vals k))
          (Eq-sym eK) (agree k lk)))

  --------------------------------------------------------------------
  -- A SETTLED ARGUMENT FREEZES THE SELECTION
  --
  -- No drive is needed here: the replay depth `dep` is monotone, so once
  -- it is past the argument's own threshold it stays past it.
  --------------------------------------------------------------------

  settles-frozen : (K j : Nat) -> LeN (suc j) p -> Eq (WW.sel K) (inr j)
                 -> (n1 : Nat)
                 -> ((m : Nat) -> LeN n1 m
                     -> Eq (ovOf (Ths j) m) (ovOf (Ths j) n1))
                 -> LeN n1 (WW.dep K j)
                 -> (k : Nat) -> LeN K k -> Eq (WW.sel k) (WW.sel K)
  settles-frozen K j lj eK n1 con deep = sel-frozen K j eK agree
    where
      agree : (k : Nat) -> LeN K k -> Eq (valAt K j) (valAt k j)
      agree k lk =
        Eq-trans (valAt-eq K j lj)
          (Eq-trans (con (WW.dep K j) deep)
            (Eq-trans (Eq-sym (con (WW.dep k j)
                        (LeN-trans {n1} {WW.dep K j} {WW.dep k j}
                          deep (dep-mono K k lk j))))
              (Eq-sym (valAt-eq k j lj))))
