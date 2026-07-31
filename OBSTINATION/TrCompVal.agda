{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompVal
--
-- THE VALUE SIDE OF `TrCompNG`: what `sem` does at each of the three
-- cases `blockOn` distinguishes.
--
--   sem-inl     -- the outer value is already total: that IS the value.
--   sem-fbot    -- it is not, and the demanded coordinate is incomplete:
--                  the value is `ovg (NG k)`, a function of the replay
--                  depth ALONE.
--   sem-descend -- it is not, and the demanded coordinate is a numeral:
--                  `sem` descends into the continuation, on the tuple with
--                  that coordinate deleted.
--
-- These are the exact analogues of `TrCompNG`'s `blk-inl` / `blk-fbot` /
-- `blk-descend`, and together with `NG-freeze` -- a descent freezes the
-- replay for ever, so the continuation descended into is FIXED -- they
-- are what turns MP1's value clause for a composite into a structural
-- recursion on the outer trace.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompVal where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (nOf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; LeX ; LeX-hts ; MonoTr)
open import OBSTINATION.TrCompNG using (module NGf)
open import OBSTINATION.TrScan using (LeN-uniq)

------------------------------------------------------------------------
-- THE THREE CASES OF `sem` AT A NODE
------------------------------------------------------------------------

module SEMf (q : Nat) (ivg : Nat -> Nat)
            (ivgr : (n : Nat) -> LeN (suc (ivg n)) (suc q))
            (ovg : Nat -> FEl)
            (contg : (c : Nat) -> LeN (suc c) (suc q) -> (v : Nat) -> Tr q)
            (V : Nat -> FTup)
            (Vmono : (k k' : Nat) -> LeN k k' -> LeX (V k) (V k'))
            (mt : MonoTr (suc q) (node ivg ivgr ovg contg))
            where

  open NGf q ivg ivgr ovg contg V Vmono mt public

  SV : Nat -> FEl
  SV k = sem (suc q) Tg (V k)

  -- the continuation `sem` descends into at stage `k`
  CT : Nat -> Tr q
  CT k = contg (cg k) (ivgr (NG k)) (hts (V k) (cg k))

  ----------------------------------------------------------------------
  -- 1. THE OUTER VALUE IS ALREADY TOTAL
  ----------------------------------------------------------------------

  sem-inl : (k : Nat) -> IsCpl (ovg (NG k)) -> Eq (SV k) (ovg (NG k))
  sem-inl k ic = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y -> Eq (SV k) (ovg (NG k))
      go (fbot w) e = Empty-elim (Eq-transport (\ z -> IsCpl z) e ic)
      go (fcpl w) e =
        Eq-trans
          (Eq-cong (\ z -> hlt z (brf (ovg (NG k)) (sem q (CT k) (del (cg k) (V k)))
                                    (at k))) e)
          (Eq-sym e)

  ----------------------------------------------------------------------
  -- 2. IT IS NOT, AND THE DEMANDED COORDINATE IS INCOMPLETE
  ----------------------------------------------------------------------

  sem-fbot : (k : Nat) -> Not (IsCpl (ovg (NG k))) -> Not (IsCpl (at k))
           -> Eq (SV k) (ovg (NG k))
  sem-fbot k nc na = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y -> Eq (SV k) (ovg (NG k))
      go (fcpl w) e = Empty-elim (nc (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt))
      go (fbot w) e = br (at k) refl
        where
          br : (y : FEl) -> Eq (at k) y -> Eq (SV k) (ovg (NG k))
          br (fcpl j) ey =
            Empty-elim (na (Eq-transport (\ z -> IsCpl z) (Eq-sym ey) tt))
          br (fbot j) ey =
            Eq-trans
              (Eq-cong (\ z -> hlt z (brf (ovg (NG k))
                                       (sem q (CT k) (del (cg k) (V k))) (at k))) e)
              (Eq-cong (\ z -> brf (ovg (NG k))
                                 (sem q (CT k) (del (cg k) (V k))) z) ey)

  ----------------------------------------------------------------------
  -- 3. IT IS NOT, AND THE DEMANDED COORDINATE IS A NUMERAL
  ----------------------------------------------------------------------

  sem-descend : (k : Nat) -> Not (IsCpl (ovg (NG k))) -> IsCpl (at k)
              -> Eq (SV k) (sem q (CT k) (del (cg k) (V k)))
  sem-descend k nc ia = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y
         -> Eq (SV k) (sem q (CT k) (del (cg k) (V k)))
      go (fcpl w) e = Empty-elim (nc (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt))
      go (fbot w) e = br (at k) refl
        where
          br : (y : FEl) -> Eq (at k) y
             -> Eq (SV k) (sem q (CT k) (del (cg k) (V k)))
          br (fbot j) ey = Empty-elim (Eq-transport (\ z -> IsCpl z) ey ia)
          br (fcpl j) ey =
            Eq-trans
              (Eq-cong (\ z -> hlt z (brf (ovg (NG k))
                                       (sem q (CT k) (del (cg k) (V k))) (at k))) e)
              (Eq-cong (\ z -> brf (ovg (NG k))
                                 (sem q (CT k) (del (cg k) (V k))) z) ey)

  ----------------------------------------------------------------------
  -- ... AND THE CONTINUATION IS THE SAME ONE FOR EVER
  --
  -- `NG-freeze` pins the replay depth, hence `cg`, hence the frozen
  -- level: after a descent the outer trace is out of the picture and the
  -- computation is a FIXED smaller trace on the remaining coordinates.
  ----------------------------------------------------------------------

  CT-freeze : (K : Nat) -> IsCpl (at K) -> (k : Nat) -> LeN K k -> Eq (CT k) (CT K)
  CT-freeze K ic k lk =
    Eq-trans
      (Eq-cong (\ n -> contg (ivg n) (ivgr n) (hts (V k) (ivg n)))
        (NG-freeze K ic k lk))
      (Eq-cong (\ z -> contg (cg K) (ivgr (NG K)) z) (Eq-sym agr))
    where
      agr : Eq (hts (V K) (cg K)) (hts (V k) (cg K))
      agr =
        Eq-cong hgt
          (cpl-max (nth (fbot zero) (cg K) (V K)) (nth (fbot zero) (cg K) (V k))
            (Vmono K k lk (cg K)) ic)
