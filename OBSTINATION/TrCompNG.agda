{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompNG
--
-- THE OUTER TRACE'S RUN ALONG A GROWING FAMILY, AND WHY ITS PROGRESS IS
-- BOUNDED.
--
-- `TrCompSel` left `SelStab` with one case: the selected argument's value
-- keeps growing.  Then the selection can only change when the OUTER trace
-- `Tg` itself moves, and this file proves that `Tg` can move only
-- finitely often, by settling the top-level case analysis of `blockOn`
-- along a monotone family `V`:
--
--     NG k = nOf (suc q) ivg ivgr (hts (V k))     -- Tg's replay depth
--     cg k = ivg (NG k)                           -- the stuck coordinate
--
--   * `blk-inl`     -- `ovg (NG k)` total: waiting for nothing.
--   * `blk-fbot`    -- otherwise, if `V k (cg k)` is incomplete the
--                      demand is `inr (cg k)` -- a function of `NG k`
--                      ALONE, so it cannot change while `NG` does not.
--   * `blk-descend` -- and if `V k (cg k)` is a numeral, `blockOn`
--                      descends into a continuation.
--   * `NG-freeze`   -- THE KEY: a descent FREEZES `NG` FOR EVER.  The
--                      replay is stuck on `cg k`, whose value is total,
--                      hence maximal, hence never moves again -- so
--                      `nOf-stick` pins the replay depth.  Therefore
--                      `cg` is frozen too, the continuation `Tg` descends
--                      into is FIXED, and the argument recurses on a
--                      strictly smaller trace.
--
-- So `Tg`'s progress is bounded twice over: the replay depth `NG` climbs
-- at most to the threshold of `EvConstN ivg` (past it, `cg` is constant
-- and so is the demand), and a descent can happen at most `q+1` times
-- since it drops the arity and freezes everything above it.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompNG where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.CapDet using (nle-lt)
open import OBSTINATION.CapDet using (le-cases)
open import OBSTINATION.ReplayLv using
  (lv ; lv-le ; Adv ; Adv-mono ; nOf ; nOf-mono ; nOf-ge ; nOf-below-adv)
open import OBSTINATION.WalkAffine using (stuck-level)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat

IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
IsCpl-dec (fbot j) = no (\ z -> z)
IsCpl-dec (fcpl j) = yes tt

module NGf (q : Nat) (ivg : Nat -> Nat)
           (ivgr : (n : Nat) -> LeN (suc (ivg n)) (suc q))
           (ovg : Nat -> FEl)
           (contg : (c : Nat) -> LeN (suc c) (suc q) -> (v : Nat) -> Tr q)
           (V : Nat -> FTup)
           (Vmono : (k k' : Nat) -> LeN k k' -> LeX (V k) (V k'))
           (mt : MonoTr (suc q) (node ivg ivgr ovg contg))
           where

  Tg : Tr (suc q)
  Tg = node ivg ivgr ovg contg

  NG : Nat -> Nat
  NG k = nOf (suc q) ivg ivgr (hts (V k))

  NG-mono : (k k' : Nat) -> LeN k k' -> LeN (NG k) (NG k')
  NG-mono k k' le =
    nOf-mono (suc q) ivg ivgr (hts (V k)) (hts (V k'))
      (LeX-hts (V k) (V k') (Vmono k k' le))

  cg : Nat -> Nat
  cg k = ivg (NG k)

  at : Nat -> FEl
  at k = nth (fbot zero) (cg k) (V k)

  BLK : Nat -> Or Top Nat
  BLK k =
    shiftOr (cg k)
      (blockOn q (contg (cg k) (ivgr (NG k)) (hts (V k) (cg k)))
        (del (cg k) (V k)))

  --------------------------------------------------------------------
  -- THE REPLAY IS AT LEAST AS DEEP AS THE LEVEL IT NEEDS
  --
  -- `stuck-level` says the level `Tg` needs at `cg k` IS `hts (V k) (cg k)`,
  -- and a walk spends at most one step per level (`lv-le`).  So a
  -- coordinate whose height grows without bound drags `NG` up with it --
  -- which is what turns "the selected argument keeps growing" into
  -- "`Tg` keeps advancing".
  --------------------------------------------------------------------

  NG-ge-hts : (k : Nat) -> LeN (hts (V k) (cg k)) (NG k)
  NG-ge-hts k =
    Eq-transport (\ z -> LeN z (NG k))
      (stuck-level (suc q) ivg ivgr (hts (V k)))
      (lv-le (suc q) ivg ivgr (cg k) (NG k))

  --------------------------------------------------------------------
  -- RAISING THE DEMANDED COORDINATE ADVANCES THE REPLAY
  --
  -- `stuck-level` says the replay is stuck at exactly the height the
  -- demanded coordinate has; so if that height grows, the step it was
  -- stuck on can be taken, and the replay depth STRICTLY increases.
  -- (`TrCompIv.nOf-step` is the special case where the growth is a
  -- single `bump`.)
  --------------------------------------------------------------------

  NG-grow : (j j' : Nat) -> LeN j j'
          -> LeN (suc (hts (V j) (cg j))) (hts (V j') (cg j))
          -> LeN (suc (NG j)) (NG j')
  NG-grow j j' lj gr = nOf-ge (suc q) ivg ivgr (hts (V j')) (suc (NG j)) adv
    where
      le : (c : Nat) -> LeN (hts (V j) c) (hts (V j') c)
      le c = LeX-hts (V j) (V j') (Vmono j j' lj) c

      atN : Adv (suc q) ivg ivgr (hts (V j')) (NG j)
      atN =
        Eq-transport (\ z -> LeN (suc z) (hts (V j') (cg j)))
          (Eq-sym (stuck-level (suc q) ivg ivgr (hts (V j)))) gr

      adv : (m : Nat) -> LeN (suc m) (suc (NG j))
          -> Adv (suc q) ivg ivgr (hts (V j')) m
      adv m lm = route (le-cases m (NG j) lm)
        where
          route : Or (Eq (NG j) m) (LeN (suc m) (NG j))
                -> Adv (suc q) ivg ivgr (hts (V j')) m
          route (inl e)  =
            Eq-transport (\ z -> Adv (suc q) ivg ivgr (hts (V j')) z) e atN
          route (inr lt) =
            Adv-mono (suc q) ivg ivgr (hts (V j)) (hts (V j')) le m
              (nOf-below-adv (suc q) ivg ivgr (hts (V j)) m lt)

  --------------------------------------------------------------------
  -- A DEMANDED COORDINATE IS EITHER THE EVENTUAL ONE, OR SHALLOW
  --
  -- This is min1.pdf's finiteness of the approximant `A_0`, read on the
  -- trace.  `NG-ge-hts` says the demanded coordinate's height is below
  -- the replay depth; so if that height has already reached the walk's
  -- own threshold `Nh`, the replay is past `Nh` and the demand IS the
  -- eventual index `ivg Nh` -- fixed for ever.  Otherwise the height is
  -- strictly below `Nh`.
  --
  -- Hence a coordinate that is ALWAYS incomplete and only ever grows when
  -- demanded -- which is exactly what a parameter of a primitive
  -- recursion is -- can be demanded at most `Nh` times before the demand
  -- has settled.  That is the measure the recursion clause was missing.
  --------------------------------------------------------------------

  cg-or-small : (Nh : Nat) -> ((n : Nat) -> LeN Nh n -> Eq (ivg n) (ivg Nh))
              -> (k : Nat)
              -> Or (Eq (cg k) (ivg Nh)) (LeN (suc (hts (V k) (cg k))) Nh)
  cg-or-small Nh stab k = route (LeN-dec Nh (NG k))
    where
      route : Dec (LeN Nh (NG k))
            -> Or (Eq (cg k) (ivg Nh)) (LeN (suc (hts (V k) (cg k))) Nh)
      route (yes l)  = inl (stab (NG k) l)
      route (no  nl) =
        inr
          (LeN-trans {suc (hts (V k) (cg k))} {suc (NG k)} {Nh}
            (NG-ge-hts k) (nle-lt Nh (NG k) nl))

  --------------------------------------------------------------------
  -- THE TOP-LEVEL CASE ANALYSIS
  --------------------------------------------------------------------

  blk-inl : (k : Nat) -> IsCpl (ovg (NG k))
          -> Eq (blockOn (suc q) Tg (V k)) (inl tt)
  blk-inl k ic = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y
         -> Eq (blockOn (suc q) Tg (V k)) (inl tt)
      go (fbot w) e = Empty-elim (Eq-transport (\ z -> IsCpl z) e ic)
      go (fcpl w) e =
        Eq-cong (\ z -> hb z (bb (cg k) (BLK k) (at k))) e

  blk-fbot : (k : Nat) -> Not (IsCpl (ovg (NG k))) -> Not (IsCpl (at k))
           -> Eq (blockOn (suc q) Tg (V k)) (inr (cg k))
  blk-fbot k nc na = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y
         -> Eq (blockOn (suc q) Tg (V k)) (inr (cg k))
      go (fcpl w) e = Empty-elim (nc (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt))
      go (fbot w) e = br (at k) refl
        where
          br : (y : FEl) -> Eq (at k) y
             -> Eq (blockOn (suc q) Tg (V k)) (inr (cg k))
          br (fcpl j) ey =
            Empty-elim (na (Eq-transport (\ z -> IsCpl z) (Eq-sym ey) tt))
          br (fbot j) ey =
            Eq-trans (Eq-cong (\ z -> hb z (bb (cg k) (BLK k) (at k))) e)
              (Eq-cong (\ z -> bb (cg k) (BLK k) z) ey)

  blk-descend : (k : Nat) -> Not (IsCpl (ovg (NG k))) -> IsCpl (at k)
              -> Eq (blockOn (suc q) Tg (V k)) (BLK k)
  blk-descend k nc ia = go (ovg (NG k)) refl
    where
      go : (y : FEl) -> Eq (ovg (NG k)) y
         -> Eq (blockOn (suc q) Tg (V k)) (BLK k)
      go (fcpl w) e = Empty-elim (nc (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt))
      go (fbot w) e = br (at k) refl
        where
          br : (y : FEl) -> Eq (at k) y
             -> Eq (blockOn (suc q) Tg (V k)) (BLK k)
          br (fbot j) ey =
            Empty-elim (Eq-transport (\ z -> IsCpl z) ey ia)
          br (fcpl j) ey =
            Eq-trans (Eq-cong (\ z -> hb z (bb (cg k) (BLK k) (at k))) e)
              (Eq-cong (\ z -> bb (cg k) (BLK k) z) ey)

  --------------------------------------------------------------------
  -- A DESCENT FREEZES THE REPLAY FOR EVER
  --------------------------------------------------------------------

  NG-freeze : (K : Nat) -> IsCpl (at K)
            -> (k : Nat) -> LeN K k -> Eq (NG k) (NG K)
  NG-freeze K ic k lk =
    Eq-sym
      (nOf-stick (suc q) ivg ivgr (hts (V K)) (hts (V k))
        (LeX-hts (V K) (V k) (Vmono K k lk)) agr)
    where
      -- the stuck coordinate is total, hence MAXIMAL, hence unchanged
      same : Eq (nth (fbot zero) (cg K) (V K)) (nth (fbot zero) (cg K) (V k))
      same =
        cpl-max (nth (fbot zero) (cg K) (V K)) (nth (fbot zero) (cg K) (V k))
          (Vmono K k lk (cg K)) ic

      agr : Eq (hts (V K) (cg K)) (hts (V k) (cg K))
      agr = Eq-cong hgt same

  cg-freeze : (K : Nat) -> IsCpl (at K)
            -> (k : Nat) -> LeN K k -> Eq (cg k) (cg K)
  cg-freeze K ic k lk = Eq-cong ivg (NG-freeze K ic k lk)

  -- ... so the continuation it descends into is FIXED
  hts-freeze : (K : Nat) -> IsCpl (at K)
             -> (k : Nat) -> LeN K k
             -> Eq (hts (V k) (cg k)) (hts (V K) (cg K))
  hts-freeze K ic k lk =
    Eq-trans (Eq-cong (\ z -> hts (V k) z) (cg-freeze K ic k lk))
      (Eq-sym
        (Eq-cong hgt
          (cpl-max (nth (fbot zero) (cg K) (V K)) (nth (fbot zero) (cg K) (V k))
            (Vmono K k lk (cg K)) ic)))

  --------------------------------------------------------------------
  -- PAST THE THRESHOLD, WITH NOTHING GOING COMPLETE, THE DEMAND IS THE
  -- EVENTUAL INDEX -- FOR EVER
  --------------------------------------------------------------------

  -- past the threshold the demanded coordinate IS the eventual index,
  -- at every later stage
  cg-past : (Nh : Nat) -> ((n : Nat) -> LeN Nh n -> Eq (ivg n) (ivg Nh))
          -> (J : Nat) -> LeN Nh (NG J)
          -> (k : Nat) -> LeN J k -> Eq (cg k) (ivg Nh)
  cg-past Nh stab J past k lk =
    stab (NG k) (LeN-trans {Nh} {NG J} {NG k} past (NG-mono J k lk))

  tail-const : (Nh : Nat) -> ((n : Nat) -> LeN Nh n -> Eq (ivg n) (ivg Nh))
             -> (J : Nat) -> LeN Nh (NG J)
             -> ((k : Nat) -> LeN J k -> Not (IsCpl (ovg (NG k))))
             -> ((k : Nat) -> LeN J k -> Not (IsCpl (at k)))
             -> (k : Nat) -> LeN J k
             -> Eq (blockOn (suc q) Tg (V k)) (blockOn (suc q) Tg (V J))
  tail-const Nh stab J past nc na k lk =
    Eq-trans (blk-fbot k (nc k lk) (na k lk))
      (Eq-trans (Eq-cong inr (Eq-trans (atNh k lk) (Eq-sym (atNh J (LeN-refl J)))))
        (Eq-sym (blk-fbot J (nc J (LeN-refl J)) (na J (LeN-refl J)))))
    where
      atNh : (k' : Nat) -> LeN J k' -> Eq (cg k') (ivg Nh)
      atNh k' lk' =
        stab (NG k')
          (LeN-trans {Nh} {NG J} {NG k'} past (NG-mono J k' lk'))

  --------------------------------------------------------------------
  -- ONE DECISION SETTLES A FAMILY IN WHICH ONLY ONE COORDINATE MOVES
  --
  -- If nothing ever goes complete, one coordinate `dom` has height at
  -- least the stage number, and every OTHER coordinate is constant, then
  -- ONE test at stage `Nh` decides everything: if the demand is `dom`,
  -- the replay is past `Nh` (`NG-ge-hts`) and `tail-const` applies; if it
  -- is any other coordinate, that coordinate never moves and
  -- `blockOn-sat` freezes the demand.
  --------------------------------------------------------------------

  scan-const : (Nh : Nat) -> ((n : Nat) -> LeN Nh n -> Eq (ivg n) (ivg Nh))
             -> Or (Sigma Nat (\ n0 -> IsCpl (ovg n0)))
                   ((m : Nat) -> Not (IsCpl (ovg m)))
             -> ((k c : Nat) -> Not (IsCpl (nth (fbot zero) c (V k))))
             -> (dom : Nat) -> ((k : Nat) -> LeN k (hts (V k) dom))
             -> ((c : Nat) -> Not (Eq c dom) -> (k k' : Nat) -> LeN k k'
                 -> Eq (nth (fbot zero) c (V k)) (nth (fbot zero) c (V k')))
             -> Sigma Nat (\ J -> (k : Nat) -> LeN J k
                  -> Eq (blockOn (suc q) Tg (V k)) (blockOn (suc q) Tg (V J)))
  scan-const Nh stab tot ncp dom grow fix = route tot
    where
      Res : Set
      Res =
        Sigma Nat (\ J -> (k : Nat) -> LeN J k
          -> Eq (blockOn (suc q) Tg (V k)) (blockOn (suc q) Tg (V J)))

      -- nothing is waited on: stable, with a vacuous agreement
      frzInl : (J : Nat) -> IsCpl (ovg (NG J)) -> Res
      frzInl J ic =
        mkSigma J
          (\ k lk ->
             Eq-sym
               (blockOn-sat (suc q) Tg mt (V J) (V k) (Vmono J k lk)
                 (Eq-transport (\ r -> Agr r (V J) (V k))
                   (Eq-sym (blk-inl J ic)) tt)))

      -- the demanded coordinate never moves: stable
      frzFix : (J : Nat) -> Not (IsCpl (ovg (NG J))) -> Not (Eq (cg J) dom) -> Res
      frzFix J nc ne =
        mkSigma J
          (\ k lk ->
             Eq-sym
               (blockOn-sat (suc q) Tg mt (V J) (V k) (Vmono J k lk)
                 (Eq-transport (\ r -> Agr r (V J) (V k))
                   (Eq-sym (blk-fbot J nc (ncp J (cg J))))
                   (fix (cg J) ne J k lk))))

      -- the growing coordinate drags the replay past `Nh`
      atDom : (J : Nat) -> Eq (cg J) dom -> LeN J (NG J)
      atDom J e =
        LeN-trans {J} {hts (V J) (cg J)} {NG J}
          (Eq-transport (\ z -> LeN J (hts (V J) z)) (Eq-sym e) (grow J))
          (NG-ge-hts J)

      route : Or (Sigma Nat (\ n0 -> IsCpl (ovg n0)))
                 ((m : Nat) -> Not (IsCpl (ovg m)))
            -> Res
      ------------------------------------------------------------
      -- the outer value never goes total
      ------------------------------------------------------------
      route (inr nev) = pick (EqNat-dec (cg Nh) dom)
        where
          pick : Dec (Eq (cg Nh) dom) -> Res
          pick (yes e) =
            mkSigma Nh
              (tail-const Nh stab Nh (atDom Nh e)
                (\ k lk -> nev (NG k)) (\ k lk -> ncp k (cg k)))
          pick (no ne) = frzFix Nh (nev (NG Nh)) ne
      ------------------------------------------------------------
      -- it does: then at `max Nh n0` it already has, or the demand
      -- was never the growing coordinate in the first place
      ------------------------------------------------------------
      route (inl (mkSigma n0 ic0)) = pick0 (IsCpl-dec (ovg (NG Q)))
        where
          Q : Nat
          Q = maxN Nh n0

          pick0 : Dec (IsCpl (ovg (NG Q))) -> Res
          pick0 (yes ic) = frzInl Q ic
          pick0 (no  nc) = pick1 (EqNat-dec (cg Q) dom)
            where
              pick1 : Dec (Eq (cg Q) dom) -> Res
              pick1 (no ne) = frzFix Q nc ne
              pick1 (yes e) = Empty-elim (nc icQ)
                where
                  bigQ : LeN n0 (NG Q)
                  bigQ =
                    LeN-trans {n0} {Q} {NG Q} (maxN-le-r Nh n0) (atDom Q e)

                  icQ : IsCpl (ovg (NG Q))
                  icQ =
                    Eq-transport (\ z -> IsCpl z)
                      (cpl-max (ovg n0) (ovg (NG Q)) (fst mt n0 (NG Q) bigQ) ic0)
                      ic0

  --------------------------------------------------------------------
  -- AND THE DEMAND CANNOT MOVE WHILE THE REPLAY DOES NOT
  --------------------------------------------------------------------

  blk-stuck : (K k : Nat) -> Eq (NG k) (NG K)
            -> Not (IsCpl (ovg (NG K))) -> Not (IsCpl (at K)) -> Not (IsCpl (at k))
            -> Eq (blockOn (suc q) Tg (V k)) (blockOn (suc q) Tg (V K))
  blk-stuck K k eN nc naK nak =
    Eq-trans
      (blk-fbot k
        (\ ic -> nc (Eq-transport (\ z -> IsCpl (ovg z)) eN ic)) nak)
      (Eq-trans (Eq-cong (\ z -> inr (ivg z)) eN)
        (Eq-sym (blk-fbot K nc naK)))
