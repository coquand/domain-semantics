{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrMono
--
-- `MonoTr` FOR THE CONSTRUCTED TRACES.
--
-- `MonoTr T` -- the recorded value `ov` grows with the replay depth -- is
-- what `TrSat.sem-sat` and `TrSat.blockOn-sat` need for their "already
-- total" branch.  Every correctness proof asks for it, so every
-- construction has to supply it.
--
-- For a COMPOSITE it is not a structural fact about the walk: `ovf k` is
-- `g` applied to the arguments replayed at the levels obtained after `k`
-- steps, so its monotonicity is the monotonicity of `g` composed with
--
--   * `L` is monotone in `k` (a `bump` never lowers a level),
--   * hence each argument's replay depth `dep k i` is (`nOf-mono`),
--   * hence its recorded value is (`MonoTr (Ths i)`).
--
-- and `g`'s own monotonicity is read off `Den p Tg g` -- there is no need
-- for `MonoTr Tg`, and indeed `MonoTr` of the OUTER trace never appears.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrMono where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (le-nlt-eq)
open import OBSTINATION.ReplayLv using (bump ; bump-eq ; bump-ne ; nOf ; nOf-mono)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (LeX ; MonoF ; MonoTr)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrWalk using (den-sem)
open import OBSTINATION.TrComp using (compTr ; module W)
open import OBSTINATION.TrCompDen using (monoTr-cont)
open import OBSTINATION.TrPrecFrz using (tup-le)

------------------------------------------------------------------------
-- the two accessors, at either shape of trace
------------------------------------------------------------------------

ovOf-mono : (a : Nat) (T : Tr a) -> MonoTr a T -> (m n : Nat) -> LeN m n
          -> LeF (ovOf T m) (ovOf T n)
ovOf-mono a       (stop v)              mt m n le = LeF-refl v
ovOf-mono (suc a) (node iv ivr ov cont) mt m n le = fst mt m n le

nOfOf-mono : (a : Nat) (T : Tr a) (av av' : Nat -> Nat)
           -> ((c : Nat) -> LeN (av c) (av' c))
           -> LeN (nOfOf a T av) (nOfOf a T av')
nOfOf-mono a       (stop v)              av av' le = tt
nOfOf-mono (suc a) (node iv ivr ov cont) av av' le =
  nOf-mono (suc a) iv ivr av av' le

------------------------------------------------------------------------
-- the base cases
------------------------------------------------------------------------

zerfTr-mono : (a : Nat) -> MonoTr a (zerfTr a)
zerfTr-mono a = tt

succTr-mono : MonoTr (suc zero) succTr
succTr-mono = mkSigma (\ m n le -> le) (\ c lc v -> tt)

projTr-mono : (a i : Nat) (li : LeN (suc i) a) -> MonoTr a (projTr a i li)
projTr-mono zero    i       ()
projTr-mono (suc a) i li = mkSigma (\ m n le -> le) cn
  where
    cn : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
       -> MonoTr a (projCont a i li c lc v)
    cn c lc v = go (EqNat-dec i c) refl
      where
        go : (D : Dec (Eq i c)) -> Eq (EqNat-dec i c) D
           -> MonoTr a (projCont a i li c lc v)
        go (yes ei) eD =
          Eq-transport (\ T -> MonoTr a T)
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD)) tt
        go (no ne) eD =
          Eq-transport (\ T -> MonoTr a T)
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD))
            (projTr-mono a (sd c i) (sd-range a c i lc li ne))

------------------------------------------------------------------------
-- A WALK'S LEVELS NEVER GO DOWN
--
-- Stated for any state satisfying the `bump` recurrence, since `TrComp`
-- and `TrPrec` each carry their own copy of it (`W.L`, `P.Lv`).
------------------------------------------------------------------------

lev-step : (iv : Nat -> Nat) (L : Nat -> Nat -> Nat)
         -> ((k c : Nat) -> Eq (L (suc k) c) (bump (iv k) (L k) c))
         -> (k c : Nat) -> LeN (L k c) (L (suc k) c)
lev-step iv L bs k c = route (EqNat-dec c (iv k))
  where
    route : Dec (Eq c (iv k)) -> LeN (L k c) (L (suc k) c)
    route (yes e) =
      Eq-transport (\ z -> LeN (L k c) z)
        (Eq-sym (Eq-trans (bs k c) (bump-eq (iv k) (L k) c e)))
        (LeN-suc (L k c))
    route (no ne) =
      Eq-transport (\ z -> LeN (L k c) z)
        (Eq-sym (Eq-trans (bs k c) (bump-ne (iv k) (L k) c ne)))
        (LeN-refl (L k c))

lev-mono : (iv : Nat -> Nat) (L : Nat -> Nat -> Nat)
         -> ((k c : Nat) -> Eq (L (suc k) c) (bump (iv k) (L k) c))
         -> (m n : Nat) -> LeN m n -> (c : Nat) -> LeN (L m c) (L n c)
lev-mono iv L bs m zero    le c =
  Eq-transport (\ z -> LeN (L z c) (L zero c))
    (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (L zero c))
lev-mono iv L bs m (suc n) le c with LeN-dec m n
... | yes l  =
      LeN-trans {L m c} {L n c} {L (suc n) c}
        (lev-mono iv L bs m n l c) (lev-step iv L bs n c)
... | no  nl =
      Eq-transport (\ z -> LeN (L z c) (L (suc n) c))
        (Eq-sym (le-nlt-eq m (suc n) le nl)) (LeN-refl (L (suc n) c))

------------------------------------------------------------------------
-- THE COMPOSITE
------------------------------------------------------------------------

compTr-mono : (p : Nat) (Tg : Tr p) (g : FTup -> FEl)
            -> Den p Tg g -> MonoF p g
            -> (a : Nat) (Ths : Nat -> Tr a) -> ((i : Nat) -> MonoTr a (Ths i))
            -> MonoTr a (compTr p Tg a Ths)
compTr-mono p Tg g dg mg zero    Ths mTh = tt
compTr-mono p Tg g dg mg (suc a) Ths mTh = mkSigma ovm cns
  where
    module WW = W p Tg a Ths

    L-mono : (m n : Nat) -> LeN m n -> (c : Nat) -> LeN (WW.L m c) (WW.L n c)
    L-mono m n le c = lev-mono WW.ivf WW.L (\ _ _ -> refl) m n le c

    ------------------------------------------------------------------
    -- ... so neither do the replay depths, nor the values `g` sees
    ------------------------------------------------------------------

    vals-le : (m n : Nat) -> LeN m n -> LeX (WW.vals m) (WW.vals n)
    vals-le m n le =
      tup-le p (\ i -> ovOf (Ths i) (WW.dep m i))
               (\ i -> ovOf (Ths i) (WW.dep n i))
        (\ i li ->
           ovOf-mono (suc a) (Ths i) (mTh i) (WW.dep m i) (WW.dep n i)
             (nOfOf-mono (suc a) (Ths i) (WW.L m) (WW.L n) (L-mono m n le)))

    dsem : (k : Nat) -> Eq (WW.ovf k) (g (WW.vals k))
    dsem k =
      den-sem p Tg g dg (WW.vals k)
        (tup-len p (\ i -> ovOf (Ths i) (WW.dep k i)))

    vlen : (k : Nat) -> Eq (length (WW.vals k)) p
    vlen k = tup-len p (\ i -> ovOf (Ths i) (WW.dep k i))

    ovm : (m n : Nat) -> LeN m n -> LeF (WW.ovf m) (WW.ovf n)
    ovm m n le =
      Eq-transport (\ z -> LeF z (WW.ovf n)) (Eq-sym (dsem m))
        (Eq-transport (\ z -> LeF (g (WW.vals m)) z) (Eq-sym (dsem n))
          (mg (WW.vals m) (WW.vals n) (vlen m) (vlen n) (vals-le m n le)))

    cns : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
        -> MonoTr a (compTr p Tg a (\ i -> contOf (Ths i) c lc v))
    cns c lc v =
      compTr-mono p Tg g dg mg a (\ i -> contOf (Ths i) c lc v)
        (\ i -> monoTr-cont a (Ths i) (mTh i) c lc v)
