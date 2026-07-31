{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecIv
--
-- THE RECURSION'S INDEX: THE DEPTH DIRECTION.
--
-- `precTr`'s index is
--
--     ivP k = R.Qd (P.Lv k) (P.Lv k zero)
--
-- and `Qd` is not a `blockOn` but a FOLD of `qsel` down the recursion
-- chain: `Qd L (j+1) = qsel (Qd L j) (blockOn Th (avT L j))`.  It
-- descends through the consecutive depths at which `h` is blocked on the
-- RECURSIVE VALUE (`qsel prev (inr 1) = prev`) and stops at the first
-- that is not.
--
-- The one thing that makes the walk two-dimensional is worth stating
-- plainly, since the definitions hide it: `avT L j` does NOT mention
-- `L 0`.  The chain depends on `L` only through the PARAMETER levels.
-- So `ivP k = 0` grows the depth and leaves the chain alone, while
-- `ivP k = 1+i` grows parameter `i` and recomputes the chain.
--
-- THIS FILE settles the DEPTH direction.
--
--   `QD.Qd-evconst` -- `blockOn Th (avT L .)` eventually constant ==>
--     `Qd L .` eventually constant, one step later, because `qsel _ R` is
--     idempotent in `R` (`qsel-idem`): whatever `h`'s settled demand is,
--     folding it again changes nothing.  And `avT L .` IS a monotone
--     family in `j` -- coordinate 0 grows by exactly one per step, the
--     parameters are fixed -- so its hypothesis is what `TrSelStab`'s
--     climb proves, once that is generalised from the composite's own
--     family to an arbitrary monotone one.
--
--   `PZ.stretch` -- and then a BOUNDED CHECK decides a stretch of the
--     walk: if `Qd (Lv K) .` is constant from `J+1` on, then `ivP` being
--     `0` for the first `J+2` steps forces it to be `0` FOR EVER.  So a
--     `0`-stretch either settles the index outright or ends within `J+2`
--     steps, at a stage demanding a PARAMETER.  (`PZ.Vd-cong` /
--     `PZ.Qd-cong` are what make this work: the chain does not see `L 0`,
--     so a `0`-stretch leaves it alone and merely appends fold steps.)
--
-- THE PARAMETER DIRECTION IS NOT AN INSTANCE OF THE COMPOSITE ARGUMENT,
-- and it is worth recording why before anyone tries:
--
--   * a composite argument may SETTLE, and `TrCompSel.settles-frozen`
--     freezes the selection when it does.  A PARAMETER never settles: it
--     is `fbot (L (1+i))`, and the walk grows exactly the coordinate it
--     demands.  So the freezing half of the composite proof has no
--     analogue here, and stability cannot come from that direction;
--   * growing the demanded parameter perturbs the WHOLE chain, not just
--     the depth the descent stopped at: any lower depth blocked on the
--     same parameter moves too, and every value above it is recomputed.
--     So there is no `Qd`-analogue of `blockOn-sat` to lean on.  The
--     simplest instance is `h (x,r,z) = z`, i.e. `Th = proj 2`: EVERY
--     depth is blocked on the same parameter, so one bump recomputes the
--     whole chain.  (That instance still settles -- `ivP` is `0` then `1`
--     for ever -- which is why the difficulty is finding a MEASURE, not a
--     counterexample.)
--
-- Note that `p = 0` is trivial: `R.Qd-range` forces `Qd L m = 0`, so
-- `ivP` is constantly `0`.  The whole difficulty is the parameters.
--
-- What replaces them has to be `TrPrecFrz.F.ultimate` -- IMG_0270's
-- criterion: `h` blocked on the recursive value with the value NOT grown
-- freezes `Vd` and `Qd` for ever.  That is the only freezing mechanism
-- the recursion has, and min1.pdf singles it out for exactly that reason.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecIv where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-suc-r ; plus-mono ; Eq-cong2 ; le-ne-lt ; le-nlt-eq ;
   LeN-suc-not)
open import OBSTINATION.MP1 using (le-add ; plus-ge-l)
open import OBSTINATION.CapDet using (nle-lt)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; bump-ne ; sumTo ; sumTo-mono ; sumTo-bump ; nOf ; nOf-mono)
open import OBSTINATION.TraceDef
open import OBSTINATION.Domain using (LeF ; LeF-refl)
open import OBSTINATION.TrSat using
  (IsCpl ; LeX ; LeX-hts ; MonoTr ; Agr ; blockOn-sat)
open import OBSTINATION.TrPrecFrz using (tup-le)
open import OBSTINATION.TrCompNG using (module NGf ; IsCpl-dec)
open import OBSTINATION.TrPrecFrz using (module F)
open import OBSTINATION.TrSat using (cpl-max)
open import OBSTINATION.TrCompSel using (ovTot-or-never)
open import OBSTINATION.TrMP1 using (MP1T)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TrScan using (del-tup ; inr-inj)
open import OBSTINATION.TrCompDen using (tup-cong)
open import OBSTINATION.TrMono using (lev-mono)
open import OBSTINATION.TrPrec using (module R ; module P ; qsel)

------------------------------------------------------------------------
-- FOLDING A SETTLED DEMAND CHANGES NOTHING
------------------------------------------------------------------------

-- and when the demand is anything BUT the recursive value, the fold does
-- not look at the accumulator at all
qsel-indep : (x y : Nat) (Rm : Or Top Nat) -> Not (Eq Rm (inr (suc zero)))
           -> Eq (qsel x Rm) (qsel y Rm)
qsel-indep x y (inl tt)            nr = refl
qsel-indep x y (inr zero)          nr = refl
qsel-indep x y (inr (suc zero))    nr = Empty-elim (nr refl)
qsel-indep x y (inr (suc (suc i))) nr = refl

qsel-idem : (x : Nat) (Rm : Or Top Nat) -> Eq (qsel (qsel x Rm) Rm) (qsel x Rm)
qsel-idem x (inl tt)            = refl
qsel-idem x (inr zero)          = refl
qsel-idem x (inr (suc zero))    = refl
qsel-idem x (inr (suc (suc i))) = refl

------------------------------------------------------------------------
-- THE DEPTH DIRECTION
------------------------------------------------------------------------

module QD (p : Nat) (Th : Tr (suc (suc p))) (L : Nat -> Nat) where

  Dm : Nat -> Or Top Nat
  Dm j = blockOn (suc (suc p)) Th (R.avT p Th L j)

  Qd-stab : (J : Nat) -> ((j : Nat) -> LeN J j -> Eq (Dm j) (Dm J))
          -> (t : Nat)
          -> Eq (R.Qd p Th L (plus t (suc J))) (R.Qd p Th L (suc J))
  Qd-stab J con zero    = refl
  Qd-stab J con (suc t) =
    Eq-trans
      (Eq-cong2 qsel (Qd-stab J con t) (con (plus t (suc J)) lJ))
      (qsel-idem (R.Qd p Th L J) (Dm J))
    where
      lJ : LeN J (plus t (suc J))
      lJ =
        LeN-trans {J} {suc J} {plus t (suc J)} (LeN-suc J)
          (plus-ge-r t (suc J))

  Qd-evconst : (J : Nat) -> ((j : Nat) -> LeN J j -> Eq (Dm j) (Dm J))
             -> (j : Nat) -> LeN (suc J) j
             -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J))
  Qd-evconst J con j lj = route (le-add (suc J) j lj)
    where
      route : Sigma Nat (\ t -> Eq j (plus t (suc J)))
            -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J))
      route (mkSigma t e) =
        Eq-transport
          (\ z -> Eq (R.Qd p Th L z) (R.Qd p Th L (suc J)))
          (Eq-sym e) (Qd-stab J con t)

------------------------------------------------------------------------
-- THE CHAIN DOES NOT SEE THE DEPTH COORDINATE
--
-- `avT L j` mentions `L` only at `1+i`.  So a stretch of the walk in
-- which `ivP` is `0` -- which raises coordinate `0` and nothing else --
-- leaves the whole chain alone and merely appends fold steps.
------------------------------------------------------------------------

module PZ (p : Nat) (Th : Tr (suc (suc p))) where

  open P p Th

  mutual
    Vd-cong : (L L' : Nat -> Nat) -> ((i : Nat) -> Eq (L (suc i)) (L' (suc i)))
            -> (j : Nat) -> Eq (Vd L j) (Vd L' j)
    Vd-cong L L' e zero    = refl
    Vd-cong L L' e (suc j) =
      Eq-cong (\ X -> sem (suc (suc p)) Th X) (avT-cong L L' e j)

    avT-cong : (L L' : Nat -> Nat) -> ((i : Nat) -> Eq (L (suc i)) (L' (suc i)))
             -> (j : Nat) -> Eq (avT L j) (avT L' j)
    avT-cong L L' e j = tup-cong (suc (suc p)) (avf L j) (avf L' j) pt
      where
        pt : (c : Nat) -> Eq (avf L j c) (avf L' j c)
        pt zero          = refl
        pt (suc zero)    = Vd-cong L L' e j
        pt (suc (suc i)) = Eq-cong fbot (e i)

  Qd-cong : (L L' : Nat -> Nat) -> ((i : Nat) -> Eq (L (suc i)) (L' (suc i)))
          -> (j : Nat) -> Eq (Qd L j) (Qd L' j)
  Qd-cong L L' e zero    = refl
  Qd-cong L L' e (suc j) =
    Eq-cong2 qsel (Qd-cong L L' e j)
      (Eq-cong (\ X -> blockOn (suc (suc p)) Th X) (avT-cong L L' e j))

  ------------------------------------------------------------------
  -- ONLY THE RECURSIVE VALUE CAN EVER BE A NUMERAL
  --
  -- In `avT L j` coordinate 0 is `fbot j` and coordinate `2+i` is
  -- `fbot (L (1+i))`.  Only coordinate 1, the recursive value, can be
  -- complete.  So `blockOn Th (avT L j)` DESCENDS AT MOST ONCE, at
  -- coordinate 1, and what it descends into is all-incomplete, hence
  -- cannot descend again -- the recursion's `blockOn` has none of the
  -- composite's descent tower.
  ------------------------------------------------------------------

  avT-shape : (L : Nat -> Nat) (j c : Nat) -> Not (Eq c (suc zero))
            -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (avT L j)) (fbot m))
  avT-shape L j c ne = route (LeN-dec (suc c) (suc (suc p)))
    where
      route : Dec (LeN (suc c) (suc (suc p)))
            -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (avT L j)) (fbot m))
      route (no nc) =
        mkSigma zero (tup-out (suc (suc p)) (avf L j) c nc)
      route (yes lc) = pick c ne (tup-nth (suc (suc p)) (avf L j) c lc)
        where
          pick : (d : Nat) -> Not (Eq d (suc zero))
               -> Eq (nth (fbot zero) c (avT L j)) (avf L j d)
               -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (avT L j)) (fbot m))
          pick zero          nd e = mkSigma j e
          pick (suc zero)    nd e = Empty-elim (nd refl)
          pick (suc (suc i)) nd e = mkSigma (L (suc i)) e

  avT-incpl : (L : Nat -> Nat) (j c : Nat) -> Not (Eq c (suc zero))
            -> Not (IsCpl (nth (fbot zero) c (avT L j)))
  avT-incpl L j c ne = route (avT-shape L j c ne)
    where
      route : Sigma Nat (\ m -> Eq (nth (fbot zero) c (avT L j)) (fbot m))
            -> Not (IsCpl (nth (fbot zero) c (avT L j)))
      route (mkSigma m e) ic = Eq-transport (\ z -> IsCpl z) e ic

  ------------------------------------------------------------------
  -- THE CHAIN IS A MONOTONE FAMILY IN THE DEPTH, AND TWO OF THE FOUR
  -- DEMANDS FREEZE IT OUTRIGHT
  --
  -- Along the depth only coordinates 0 and 1 move -- the PARAMETERS are
  -- constant in `j`.  So if `h` waits on a parameter, `blockOn-sat`
  -- freezes the demand FOR EVER with no further argument; and waiting on
  -- nothing is stable for the same reason.  Of the four cases only
  -- "waits on `x`" and "waits on the recursive value" can move, and the
  -- second is IMG_0270's criterion (`TrPrecFrz`).
  ------------------------------------------------------------------

  Dmj : (Nat -> Nat) -> Nat -> Or Top Nat
  Dmj L j = blockOn (suc (suc p)) Th (avT L j)

  avT-mono : (L : Nat -> Nat)
           -> ((j j' : Nat) -> LeN j j' -> LeF (Vd L j) (Vd L j'))
           -> (j j' : Nat) -> LeN j j' -> LeX (avT L j) (avT L j')
  avT-mono L vm j j' lj = tup-le (suc (suc p)) (avf L j) (avf L j') go
    where
      go : (c : Nat) -> LeN (suc c) (suc (suc p))
         -> LeF (avf L j c) (avf L j' c)
      go zero          lc = lj
      go (suc zero)    lc = vm j j' lj
      go (suc (suc i)) lc = LeF-refl (fbot (L (suc i)))

  -- waiting on a PARAMETER is for ever
  Dm-par-frozen : (L : Nat -> Nat)
                -> ((j j' : Nat) -> LeN j j' -> LeF (Vd L j) (Vd L j'))
                -> MonoTr (suc (suc p)) Th
                -> (J i : Nat) -> Eq (Dmj L J) (inr (suc (suc i)))
                -> (j : Nat) -> LeN J j -> Eq (Dmj L j) (Dmj L J)
  Dm-par-frozen L vm mth J i eJ j lj =
    Eq-sym
      (blockOn-sat (suc (suc p)) Th mth (avT L J) (avT L j)
        (avT-mono L vm J j lj)
        (Eq-transport (\ r -> Agr r (avT L J) (avT L j)) (Eq-sym eJ) agr))
    where
      agr : Eq (nth (fbot zero) (suc (suc i)) (avT L J))
               (nth (fbot zero) (suc (suc i)) (avT L j))
      agr = route (LeN-dec (suc (suc (suc i))) (suc (suc p)))
        where
          route : Dec (LeN (suc (suc (suc i))) (suc (suc p)))
                -> Eq (nth (fbot zero) (suc (suc i)) (avT L J))
                      (nth (fbot zero) (suc (suc i)) (avT L j))
          route (yes lc) =
            Eq-trans (tup-nth (suc (suc p)) (avf L J) (suc (suc i)) lc)
              (Eq-sym (tup-nth (suc (suc p)) (avf L j) (suc (suc i)) lc))
          route (no nc) =
            Eq-trans (tup-out (suc (suc p)) (avf L J) (suc (suc i)) nc)
              (Eq-sym (tup-out (suc (suc p)) (avf L j) (suc (suc i)) nc))

  -- and so is waiting on NOTHING
  Dm-inl-frozen : (L : Nat -> Nat)
                -> ((j j' : Nat) -> LeN j j' -> LeF (Vd L j) (Vd L j'))
                -> MonoTr (suc (suc p)) Th
                -> (J : Nat) -> Eq (Dmj L J) (inl tt)
                -> (j : Nat) -> LeN J j -> Eq (Dmj L j) (Dmj L J)
  Dm-inl-frozen L vm mth J eJ j lj =
    Eq-sym
      (blockOn-sat (suc (suc p)) Th mth (avT L J) (avT L j)
        (avT-mono L vm J j lj)
        (Eq-transport (\ r -> Agr r (avT L J) (avT L j)) (Eq-sym eJ) tt))

  ------------------------------------------------------------------
  -- A PARAMETER DEMAND OF `f` IS A PARAMETER DEMAND OF `h`
  --
  -- `Qd` is a fold, so a non-zero value can only have been produced by
  -- the one clause that produces non-zero: `qsel _ (inr (2+i)) = 1+i`.
  -- Hence if `f` demands parameter `i` at depth `D`, then `h` demands
  -- coordinate `2+i` at SOME depth below `D` -- which is what lets
  -- `TrCompNG.cg-or-small` bound that parameter's level.
  ------------------------------------------------------------------

  Qd-source : (L : Nat -> Nat) (D i : Nat) -> Eq (Qd L D) (suc i)
            -> Sigma Nat (\ j -> Pair (LeN (suc j) D)
                 (Eq (Dmj L j) (inr (suc (suc i)))))
  Qd-source L zero    i e = Empty-elim (znotsuc e)
    where
      znotsuc : Not (Eq zero (suc i))
      znotsuc ()
  Qd-source L (suc D) i e = route (Dmj L D) refl
    where
      Res : Set
      Res = Sigma Nat (\ j -> Pair (LeN (suc j) (suc D))
              (Eq (Dmj L j) (inr (suc (suc i)))))

      route : (r : Or Top Nat) -> Eq (Dmj L D) r -> Res
      route (inl tt) er = Empty-elim (znotsuc (Eq-trans (Eq-sym at) e))
        where
          at : Eq (Qd L (suc D)) zero
          at = Eq-cong (qsel (Qd L D)) er

          znotsuc : Not (Eq zero (suc i))
          znotsuc ()
      route (inr zero) er = Empty-elim (znotsuc (Eq-trans (Eq-sym at) e))
        where
          at : Eq (Qd L (suc D)) zero
          at = Eq-cong (qsel (Qd L D)) er

          znotsuc : Not (Eq zero (suc i))
          znotsuc ()
      route (inr (suc zero)) er = up (Qd-source L D i down)
        where
          down : Eq (Qd L D) (suc i)
          down = Eq-trans (Eq-sym (Eq-cong (qsel (Qd L D)) er)) e

          up : Sigma Nat (\ j -> Pair (LeN (suc j) D)
                 (Eq (Dmj L j) (inr (suc (suc i))))) -> Res
          up (mkSigma j (mkSigma lj eq)) =
            mkSigma j
              (mkSigma (LeN-trans {suc j} {D} {suc D} lj (LeN-suc D)) eq)
      route (inr (suc (suc i'))) er =
        mkSigma D
          (mkSigma (LeN-refl D)
            (Eq-trans er (Eq-cong (\ z -> inr (suc (suc z))) same)))
        where
          same : Eq i' i
          same = suc-inj (Eq-trans (Eq-sym (Eq-cong (qsel (Qd L D)) er)) e)

  ------------------------------------------------------------------
  -- ONCE THE DEPTH DEMAND HAS SETTLED ON ANYTHING BUT THE RECURSIVE
  -- VALUE, THE INDEX IS DETERMINED BY `Th` ALONE
  --
  -- `qsel _ (inr (2+i)) = 1+i` and `qsel _ (inl tt) = qsel _ (inr 0) = 0`
  -- do not look at the accumulator, so the PARAMETER LEVELS DROP OUT: the
  -- constant is read off `Th`'s settled demand and nothing else.  Only
  -- `qsel _ (inr 1) = prev` -- `h` waiting on the recursive value --
  -- keeps a dependence on the chain below, and that is IMG_0270's case.
  ------------------------------------------------------------------

  Qd-indep-par : (L : Nat -> Nat) (J i : Nat)
               -> ((j : Nat) -> LeN J j -> Eq (Dmj L j) (Dmj L J))
               -> Eq (Dmj L J) (inr (suc (suc i)))
               -> (D : Nat) -> LeN (suc J) D -> Eq (Qd L D) (suc i)
  Qd-indep-par L J i con e D lD =
    Eq-trans (QD.Qd-evconst p Th L J con D lD) (Eq-cong (qsel (Qd L J)) e)

  Qd-indep-zero : (L : Nat -> Nat) (J : Nat)
                -> ((j : Nat) -> LeN J j -> Eq (Dmj L j) (Dmj L J))
                -> Or (Eq (Dmj L J) (inl tt)) (Eq (Dmj L J) (inr zero))
                -> (D : Nat) -> LeN (suc J) D -> Eq (Qd L D) zero
  Qd-indep-zero L J con (inl e) D lD =
    Eq-trans (QD.Qd-evconst p Th L J con D lD) (Eq-cong (qsel (Qd L J)) e)
  Qd-indep-zero L J con (inr e) D lD =
    Eq-trans (QD.Qd-evconst p Th L J con D lD) (Eq-cong (qsel (Qd L J)) e)

  -- the dual: a ZERO demand comes from `h` waiting on `x` or on nothing
  -- at some depth -- unless EVERY depth descends
  Qd-zero-source : (L : Nat -> Nat) (D : Nat) -> Eq (Qd L D) zero
                 -> Or ((j : Nat) -> LeN (suc j) D
                        -> Eq (Dmj L j) (inr (suc zero)))
                       (Sigma Nat (\ j -> Pair (LeN (suc j) D)
                          (Or (Eq (Dmj L j) (inl tt)) (Eq (Dmj L j) (inr zero)))))
  Qd-zero-source L zero    e = inl (\ j ())
  Qd-zero-source L (suc D) e = route (Dmj L D) refl
    where
      Res : Set
      Res =
        Or ((j : Nat) -> LeN (suc j) (suc D) -> Eq (Dmj L j) (inr (suc zero)))
           (Sigma Nat (\ j -> Pair (LeN (suc j) (suc D))
              (Or (Eq (Dmj L j) (inl tt)) (Eq (Dmj L j) (inr zero)))))

      route : (r : Or Top Nat) -> Eq (Dmj L D) r -> Res
      route (inl tt) er =
        inr (mkSigma D (mkSigma (LeN-refl D) (inl er)))
      route (inr zero) er =
        inr (mkSigma D (mkSigma (LeN-refl D) (inr er)))
      route (inr (suc (suc i))) er = Empty-elim (znotsuc bad)
        where
          bad : Eq zero (suc i)
          bad = Eq-trans (Eq-sym e) (Eq-cong (qsel (Qd L D)) er)

          znotsuc : Not (Eq zero (suc i))
          znotsuc ()
      route (inr (suc zero)) er = up (Qd-zero-source L D down)
        where
          down : Eq (Qd L D) zero
          down = Eq-trans (Eq-sym (Eq-cong (qsel (Qd L D)) er)) e

          up : Or ((j : Nat) -> LeN (suc j) D -> Eq (Dmj L j) (inr (suc zero)))
                  (Sigma Nat (\ j -> Pair (LeN (suc j) D)
                     (Or (Eq (Dmj L j) (inl tt)) (Eq (Dmj L j) (inr zero)))))
             -> Res
          up (inr (mkSigma j (mkSigma lj w))) =
            inr (mkSigma j
                  (mkSigma (LeN-trans {suc j} {D} {suc D} lj (LeN-suc D)) w))
          up (inl all) = inl ext
            where
              ext : (j : Nat) -> LeN (suc j) (suc D)
                  -> Eq (Dmj L j) (inr (suc zero))
              ext j lj = pick (LeN-dec (suc j) D)
                where
                  pick : Dec (LeN (suc j) D) -> Eq (Dmj L j) (inr (suc zero))
                  pick (yes l)  = all j l
                  pick (no  nl) =
                    Eq-transport (\ z -> Eq (Dmj L z) (inr (suc zero)))
                      (Eq-sym (le-nlt-eq j D lj nl)) er

  su1-not-one : (j : Nat) -> Not (Eq (su (suc zero) j) (suc zero))
  su1-not-one zero    ()
  su1-not-one (suc j) ()

  shiftOr1-ne : (r : Or Top Nat)
              -> Not (Eq (shiftOr (suc zero) r) (inr (suc zero)))
  shiftOr1-ne (inl tt) ()
  shiftOr1-ne (inr j)  e =
    su1-not-one j (inr-inj (su (suc zero) j) (suc zero) e)

  ------------------------------------------------------------------
  -- A STRETCH OF `ivP = 0`
  ------------------------------------------------------------------

  Zero-upto : Nat -> Nat -> Set
  Zero-upto K t = (t' : Nat) -> LeN (suc t') t -> Eq (ivP (plus t' K)) zero

  Zero-down : (K t t' : Nat) -> LeN t' t -> Zero-upto K t -> Zero-upto K t'
  Zero-down K t t' le h t'' l =
    h t'' (LeN-trans {suc t''} {t'} {t} l le)

  -- only the depth moves
  Lv-fix : (K t : Nat) -> Zero-upto K t -> (i : Nat)
         -> Eq (Lv (plus t K) (suc i)) (Lv K (suc i))
  Lv-fix K zero    h i = refl
  Lv-fix K (suc t) h i =
    Eq-trans
      (bump-ne (ivP (plus t K)) (Lv (plus t K)) (suc i) ne)
      (Lv-fix K t (Zero-down K (suc t) t (LeN-suc t) h) i)
    where
      ne : Not (Eq (suc i) (ivP (plus t K)))
      ne e = zne (Eq-trans e (h t (LeN-refl t)))
        where
          zne : Not (Eq (suc i) zero)
          zne ()

  -- ... and it moves by exactly one per step
  Lv-depth : (K t : Nat) -> Zero-upto K t
           -> Eq (Lv (plus t K) zero) (plus t (Lv K zero))
  Lv-depth K zero    h = refl
  Lv-depth K (suc t) h =
    Eq-trans
      (bump-eq (ivP (plus t K)) (Lv (plus t K)) zero
        (Eq-sym (h t (LeN-refl t))))
      (Eq-cong suc (Lv-depth K t (Zero-down K (suc t) t (LeN-suc t) h)))

  -- so along the stretch the index is the OLD chain, one fold deeper
  ivP-along : (K t : Nat) -> Zero-upto K t
            -> Eq (ivP (plus t K)) (Qd (Lv K) (plus t (Lv K zero)))
  ivP-along K t h =
    Eq-trans
      (Qd-cong (Lv (plus t K)) (Lv K) (Lv-fix K t h) (Lv (plus t K) zero))
      (Eq-cong (\ z -> Qd (Lv K) z) (Lv-depth K t h))

  ------------------------------------------------------------------
  -- A BOUNDED CHECK DECIDES A `0`-STRETCH
  --
  -- If `Qd (Lv K) .` is constant from `J+1` on -- which the depth
  -- direction supplies -- then `ivP` being `0` for the first `J+2` steps
  -- of the stretch forces it to be `0` FOR EVER.  So either the stretch
  -- ends within `J+2` steps, at a stage where a PARAMETER is demanded, or
  -- the index has already settled.
  ------------------------------------------------------------------

  stretch : (K J : Nat)
          -> ((j : Nat) -> LeN (suc J) j -> Eq (Qd (Lv K) j) (Qd (Lv K) (suc J)))
          -> Zero-upto K (suc (suc J))
          -> (t : Nat) -> Eq (ivP (plus t K)) zero
  stretch K J con hyp t = all (suc t) t (LeN-refl t)
    where
      -- the constant value IS `0`, read off the last checked step
      baseEq : Eq (Qd (Lv K) (suc J)) zero
      baseEq =
        Eq-trans
          (Eq-sym
            (Eq-trans
              (ivP-along K (suc J)
                (Zero-down K (suc (suc J)) (suc J) (LeN-suc (suc J)) hyp))
              (con (plus (suc J) (Lv K zero)) (plus-ge-l (suc J) (Lv K zero)))))
          (hyp (suc J) (LeN-refl (suc J)))

      all : (n : Nat) -> Zero-upto K n
      all zero    = \ t' ()
      all (suc n) = ext
        where
          ext : (t' : Nat) -> LeN (suc t') (suc n) -> Eq (ivP (plus t' K)) zero
          ext t' lt = pick (LeN-dec (suc t') (suc (suc J)))
            where
              pick : Dec (LeN (suc t') (suc (suc J))) -> Eq (ivP (plus t' K)) zero
              pick (yes l)  = hyp t' l
              pick (no  nl) =
                Eq-trans (ivP-along K t' (Zero-down K n t' lt (all n)))
                  (Eq-trans (con (plus t' (Lv K zero)) big) baseEq)
                where
                  big : LeN (suc J) (plus t' (Lv K zero))
                  big =
                    LeN-trans {suc J} {t'} {plus t' (Lv K zero)}
                      (LeN-trans {suc J} {suc (suc J)} {t'}
                        (LeN-suc (suc J)) (nle-lt t' (suc J) nl))
                      (plus-ge-l t' (Lv K zero))

------------------------------------------------------------------------
-- AFTER THE DESCENT: EVERY COORDINATE BUT THE DEPTH IS FIXED
--
-- Once the recursive value is a numeral, `blockOn Th` descends at
-- coordinate 1 -- and by `PZ.avT-incpl` it cannot descend again.  What it
-- descends into is
--
--     ( S^j(bot) , S^(L 1)(bot) , ... , S^(L p)(bot) )
--
-- in which ONLY the depth moves.  `TrCompNG.NGf.scan-const` settles such
-- a family outright: at most two decisions, no climb.
------------------------------------------------------------------------

pvf : (Nat -> Nat) -> Nat -> Nat -> FEl
pvf L j zero    = fbot j
pvf L j (suc i) = fbot (L (suc i))

parV : Nat -> (Nat -> Nat) -> Nat -> FTup
parV p L j = tup (suc p) (pvf L j)

parV-shape : (p : Nat) (L : Nat -> Nat) (j c : Nat)
           -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (parV p L j)) (fbot m))
parV-shape p L j c = route (LeN-dec (suc c) (suc p))
  where
    route : Dec (LeN (suc c) (suc p))
          -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (parV p L j)) (fbot m))
    route (no nc) = mkSigma zero (tup-out (suc p) (pvf L j) c nc)
    route (yes lc) = pick c (tup-nth (suc p) (pvf L j) c lc)
      where
        pick : (d : Nat) -> Eq (nth (fbot zero) c (parV p L j)) (pvf L j d)
             -> Sigma Nat (\ m -> Eq (nth (fbot zero) c (parV p L j)) (fbot m))
        pick zero    e = mkSigma j e
        pick (suc i) e = mkSigma (L (suc i)) e

parV-incpl : (p : Nat) (L : Nat -> Nat) (j c : Nat)
           -> Not (IsCpl (nth (fbot zero) c (parV p L j)))
parV-incpl p L j c = route (parV-shape p L j c)
  where
    route : Sigma Nat (\ m -> Eq (nth (fbot zero) c (parV p L j)) (fbot m))
          -> Not (IsCpl (nth (fbot zero) c (parV p L j)))
    route (mkSigma m e) ic = Eq-transport (\ z -> IsCpl z) e ic

parV-mono : (p : Nat) (L : Nat -> Nat) (j j' : Nat) -> LeN j j'
          -> LeX (parV p L j) (parV p L j')
parV-mono p L j j' lj = tup-le (suc p) (pvf L j) (pvf L j') go
  where
    go : (c : Nat) -> LeN (suc c) (suc p) -> LeF (pvf L j c) (pvf L j' c)
    go zero    lc = lj
    go (suc i) lc = LeF-refl (fbot (L (suc i)))

parV-fix : (p : Nat) (L : Nat -> Nat) (c : Nat) -> Not (Eq c zero)
         -> (j j' : Nat) -> LeN j j'
         -> Eq (nth (fbot zero) c (parV p L j)) (nth (fbot zero) c (parV p L j'))
parV-fix p L c ne j j' lj = route (LeN-dec (suc c) (suc p))
  where
    route : Dec (LeN (suc c) (suc p))
          -> Eq (nth (fbot zero) c (parV p L j)) (nth (fbot zero) c (parV p L j'))
    route (no nc) =
      Eq-trans (tup-out (suc p) (pvf L j) c nc)
        (Eq-sym (tup-out (suc p) (pvf L j') c nc))
    route (yes lc) =
      Eq-trans (tup-nth (suc p) (pvf L j) c lc)
        (Eq-trans (pick c ne) (Eq-sym (tup-nth (suc p) (pvf L j') c lc)))
      where
        pick : (d : Nat) -> Not (Eq d zero) -> Eq (pvf L j d) (pvf L j' d)
        pick zero    nd = Empty-elim (nd refl)
        pick (suc i) nd = refl

parV-grow : (p : Nat) (L : Nat -> Nat) (j : Nat)
          -> LeN j (hts (parV p L j) zero)
parV-grow p L j =
  Eq-transport (\ z -> LeN j (hgt z))
    (Eq-sym (tup-nth (suc p) (pvf L j) zero tt)) (LeN-refl j)

------------------------------------------------------------------------
-- THE POST-DESCENT DEMAND SETTLES
------------------------------------------------------------------------

post-stab : (p : Nat) (L : Nat -> Nat) (T : Tr (suc p))
          -> MonoTr (suc p) T -> MP1T (suc p) T
          -> Sigma Nat (\ J -> (j : Nat) -> LeN J j
               -> Eq (blockOn (suc p) T (parV p L j))
                     (blockOn (suc p) T (parV p L J)))
post-stab p L (stop w)              mt m1 = mkSigma zero (\ j lj -> refl)
post-stab p L (node iv ivr ov cont) mt m1 =
  NGf.scan-const p iv ivr ov cont (parV p L) (parV-mono p L) mt
    (fst (fst m1)) (snd (fst m1))
    (ovTot-or-never (suc p) (node iv ivr ov cont) m1)
    (\ k c -> parV-incpl p L k c)
    zero (parV-grow p L)
    (\ c ne k k' lk -> parV-fix p L c ne k k' lk)

------------------------------------------------------------------------
-- THE ACCOUNTING FOR THE PRE-DESCENT SCAN
--
-- While `h` waits on the RECURSIVE VALUE and IMG_0270's criterion has not
-- fired, the value strictly grows -- and while it is incomplete, growing
-- means its HEIGHT grows.  So `Nh` such steps push the height past `Nh`,
-- and `NG-ge-hts` then puts `Th`'s replay past its own threshold, where
-- `cg-or-small` says the demand has settled.  That is the bound that
-- makes the scan finite.
------------------------------------------------------------------------

leF-ne-hgt : (x y : FEl) -> LeF x y -> Not (IsCpl y) -> Not (Eq x y)
           -> LeN (suc (hgt x)) (hgt y)
leF-ne-hgt (fbot a) (fbot b) le nc ne =
  le-ne-lt a b le (\ e -> ne (Eq-cong fbot (Eq-sym e)))
leF-ne-hgt (fbot a) (fcpl b) le nc ne = Empty-elim (nc tt)
leF-ne-hgt (fcpl a) (fbot b) () nc ne
leF-ne-hgt (fcpl a) (fcpl b) le nc ne = Empty-elim (nc tt)

-- a sequence that strictly increases over a stretch grows at least as
-- fast as the stretch
run-up : (u : Nat -> Nat) (A s : Nat)
       -> ((t : Nat) -> LeN (suc t) s -> LeN (suc (u (plus t A))) (u (plus (suc t) A)))
       -> (t : Nat) -> LeN t s -> LeN (plus t (u A)) (u (plus t A))
run-up u A s inc zero    lt = plus-ge-r zero (u A)
run-up u A s inc (suc t) lt =
  LeN-trans {suc (plus t (u A))} {suc (u (plus t A))} {u (plus (suc t) A)}
    (run-up u A s inc t (LeN-trans {t} {suc t} {s} (LeN-suc t) lt))
    (inc t lt)

------------------------------------------------------------------------
-- IN THE DESCENT REGIME THE FOLD STOPS FOLDING
--
-- `qsel _ (inr 1) = prev` is the ONLY clause that keeps a dependence on
-- the chain below, and it fires only when `h` is BLOCKED on the recursive
-- value -- which needs that value to be INCOMPLETE.  Once it is a
-- numeral, `blockOn` freezes it and descends instead; a descent can only
-- be at coordinate 1 (nothing else is ever a numeral), and `su 1 j` is
-- never `1`.  So no depth whose recursive value is a numeral returns
-- `inr 1`, and there `Qd L D` is read off the TOP demand alone.
------------------------------------------------------------------------

Dm-not-one : (p : Nat)
             (ivh : Nat -> Nat)
             (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
             (ovh : Nat -> FEl)
             (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                    -> Tr (suc p))
           -> (mth : MonoTr (suc (suc p)) (node ivh ivhr ovh conth))
           -> (L : Nat -> Nat)
           -> (vm : (j j' : Nat) -> LeN j j'
                  -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                         (R.Vd p (node ivh ivhr ovh conth) L j'))
           -> (j : Nat) -> IsCpl (R.Vd p (node ivh ivhr ovh conth) L j)
           -> Not (Eq (PZ.Dmj p (node ivh ivhr ovh conth) L j) (inr (suc zero)))
Dm-not-one p ivh ivhr ovh conth mth L vm j ic e =
  route (IsCpl-dec (ovh (N.NG j)))
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth

    module N =
      NGf (suc p) ivh ivhr ovh conth (R.avT p Th L) (PZ.avT-mono p Th L vm) mth

    atV : Eq (nth (fbot zero) (suc zero) (R.avT p Th L j)) (R.Vd p Th L j)
    atV = tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt

    route : Dec (IsCpl (ovh (N.NG j))) -> Empty
    -- waiting for nothing: `inl tt`, not `inr 1`
    route (yes ico) = inlNe (Eq-trans (Eq-sym (N.blk-inl j ico)) e)
      where
        inlNe : Not (Eq {Or Top Nat} (inl tt) (inr (suc zero)))
        inlNe ()
    route (no nco) = route2 (IsCpl-dec (N.at j))
      where
        route2 : Dec (IsCpl (N.at j)) -> Empty
        -- a numeral at the demanded coordinate: it DESCENDS, and a
        -- descent can only be at coordinate 1, where `su 1 _` is never 1
        route2 (yes ia) =
          PZ.shiftOr1-ne p Th
            (blockOn (suc p)
              (conth (N.cg j) (ivhr (N.NG j))
                (hts (R.avT p Th L j) (N.cg j)))
              (del (N.cg j) (R.avT p Th L j)))
            (Eq-trans
              (Eq-cong
                (\ z -> shiftOr z
                          (blockOn (suc p)
                            (conth (N.cg j) (ivhr (N.NG j))
                              (hts (R.avT p Th L j) (N.cg j)))
                            (del (N.cg j) (R.avT p Th L j))))
                (Eq-sym ecg))
              (Eq-trans (Eq-sym (N.blk-descend j nco ia)) e))
          where
            ecg : Eq (N.cg j) (suc zero)
            ecg = route3 (EqNat-dec (N.cg j) (suc zero))
              where
                route3 : Dec (Eq (N.cg j) (suc zero)) -> Eq (N.cg j) (suc zero)
                route3 (yes q) = q
                route3 (no  nq) =
                  Empty-elim (PZ.avT-incpl p Th L j (N.cg j) nq ia)
        -- otherwise the demand is `inr (cg j)`, and `inr 1` would mean
        -- the recursive value is INCOMPLETE
        route2 (no na) = na (Eq-transport (\ z -> IsCpl z) (Eq-sym atCg) ic)
          where
            ecg : Eq (N.cg j) (suc zero)
            ecg =
              inr-inj (N.cg j) (suc zero)
                (Eq-trans (Eq-sym (N.blk-fbot j nco na)) e)

            atCg : Eq (N.at j) (R.Vd p Th L j)
            atCg =
              Eq-trans
                (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) ecg) atV

------------------------------------------------------------------------
-- THE PRE-DESCENT SCAN
--
-- With the recursive value never a numeral there is NO descent at all
-- (`PZ.avT-incpl` for the other coordinates), so `blockOn Th (avT L j)`
-- is `inr (cg j)` at every stage, and there are exactly three ways out:
--
--   * `h` waits on NOTHING            ==> `PZ.Dm-inl-frozen`
--   * `h` waits on a PARAMETER        ==> `PZ.Dm-par-frozen`
--   * `h` waits on the RECURSIVE VALUE and it did not grow
--                                     ==> `TrPrecFrz.F.frz` (IMG_0270)
--
-- and otherwise the demanded coordinate's height GREW -- the depth in the
-- `x` case, the recursive value's height in the other (`leF-ne-hgt`) --
-- so `NG-grow` makes the replay depth strictly increase.  It can do that
-- at most `Nh` times before `cg-or-small`'s threshold is passed, and then
-- `tail-const` finishes.  The scan is therefore bounded by `Nh` -- the
-- two moving coordinates may interleave, but EVERY continuing step costs
-- one unit of replay depth, so no separate accounting is needed.
------------------------------------------------------------------------

fbot-inj : (a b : Nat) -> Eq (fbot a) (fbot b) -> Eq a b
fbot-inj a b refl = refl

fcpl-inj : (a b : Nat) -> Eq (fcpl a) (fcpl b) -> Eq a b
fcpl-inj a b refl = refl

EqFEl-dec : (x y : FEl) -> Dec (Eq x y)
EqFEl-dec (fbot a) (fcpl b) = no (\ ())
EqFEl-dec (fcpl a) (fbot b) = no (\ ())
EqFEl-dec (fbot a) (fbot b) = route (EqNat-dec a b)
  where
    route : Dec (Eq a b) -> Dec (Eq (fbot a) (fbot b))
    route (yes e) = yes (Eq-cong fbot e)
    route (no ne) = no (\ e -> ne (fbot-inj a b e))
EqFEl-dec (fcpl a) (fcpl b) = route (EqNat-dec a b)
  where
    route : Dec (Eq a b) -> Dec (Eq (fcpl a) (fcpl b))
    route (yes e) = yes (Eq-cong fcpl e)
    route (no ne) = no (\ e -> ne (fcpl-inj a b e))

pre-stab : (p : Nat) (Th : Tr (suc (suc p)))
         -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
         -> (L : Nat -> Nat)
         -> ((j j' : Nat) -> LeN j j' -> LeF (R.Vd p Th L j) (R.Vd p Th L j'))
         -> ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
         -> Sigma Nat (\ J -> (j : Nat) -> LeN J j
              -> Eq (blockOn (suc (suc p)) Th (R.avT p Th L j))
                    (blockOn (suc (suc p)) Th (R.avT p Th L J)))
pre-stab p (stop w) mth m1th L vm nevV = mkSigma zero (\ j lj -> refl)
pre-stab p (node ivh ivhr ovh conth) mth m1th L vm nevV = result
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth

    module N =
      NGf (suc p) ivh ivhr ovh conth (R.avT p Th L) (PZ.avT-mono p Th L vm) mth

    Res : Set
    Res =
      Sigma Nat (\ J -> (j : Nat) -> LeN J j
        -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L J))

    Nh : Nat
    Nh = fst (fst m1th)

    stabh : (n : Nat) -> LeN Nh n -> Eq (ivh n) (ivh Nh)
    stabh = snd (fst m1th)

    ------------------------------------------------------------------
    -- nothing is ever a numeral, so nothing ever descends
    ------------------------------------------------------------------

    ncp : (j c : Nat) -> Not (IsCpl (nth (fbot zero) c (R.avT p Th L j)))
    ncp j c = route (EqNat-dec c (suc zero))
      where
        route : Dec (Eq c (suc zero))
              -> Not (IsCpl (nth (fbot zero) c (R.avT p Th L j)))
        route (no ne) = PZ.avT-incpl p Th L j c ne
        route (yes e) = \ ic -> nevV j (Eq-transport (\ z -> IsCpl z) atV ic)
          where
            atV : Eq (nth (fbot zero) c (R.avT p Th L j)) (R.Vd p Th L j)
            atV =
              Eq-trans
                (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) e)
                (tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt)

    ------------------------------------------------------------------
    -- the two moving coordinates
    ------------------------------------------------------------------

    htsAt0 : (j : Nat) -> Eq (hts (R.avT p Th L j) zero) j
    htsAt0 j = Eq-cong hgt (tup-nth (suc (suc p)) (R.avf p Th L j) zero tt)

    htsAt1 : (j : Nat)
           -> Eq (hts (R.avT p Th L j) (suc zero)) (hgt (R.Vd p Th L j))
    htsAt1 j = Eq-cong hgt (tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt)

    ------------------------------------------------------------------
    -- the three ways out
    ------------------------------------------------------------------

    frzInl : (J : Nat) -> IsCpl (ovh (N.NG J)) -> Res
    frzInl J ic =
      mkSigma J (PZ.Dm-inl-frozen p Th L vm mth J (N.blk-inl J ic))

    frzPar : (J i : Nat) -> Eq (PZ.Dmj p Th L J) (inr (suc (suc i))) -> Res
    frzPar J i eJ = mkSigma J (PZ.Dm-par-frozen p Th L vm mth J i eJ)

    frzRec : (J : Nat) -> Eq (PZ.Dmj p Th L J) (inr (suc zero))
           -> Eq (R.Vd p Th L (suc J)) (R.Vd p Th L J) -> Res
    frzRec J eB eV = mkSigma J con
      where
        con : (j : Nat) -> LeN J j -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L J)
        con j lj = route (le-add J j lj)
          where
            route : Sigma Nat (\ t -> Eq j (plus t J))
                  -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L J)
            route (mkSigma t e) =
              Eq-transport
                (\ z -> Eq (PZ.Dmj p Th L z) (PZ.Dmj p Th L J)) (Eq-sym e)
                (Eq-trans (fst (F.frz p Th mth L J eB eV t)) (Eq-sym eB))

    ------------------------------------------------------------------
    -- THE SCAN: every continuing step costs one unit of replay depth
    ------------------------------------------------------------------

    scan : (Q : Nat)
         -> ((j : Nat) -> LeN Q (N.NG j) -> Not (IsCpl (ovh (N.NG j))) -> Res)
         -> (F j : Nat) -> LeN Q (plus F (N.NG j)) -> Res
    scan Q fin F j le = top (IsCpl-dec (ovh (N.NG j)))
      where
        top : Dec (IsCpl (ovh (N.NG j))) -> Res
        top (yes ic) = frzInl j ic
        top (no  nc) = fuel F le
          where
            eD : Eq (PZ.Dmj p Th L j) (inr (N.cg j))
            eD = N.blk-fbot j nc (ncp j (N.cg j))

            -- one more unit of replay depth buys one more step
            step : LeN (suc (hts (R.avT p Th L j) (N.cg j))
                        ) (hts (R.avT p Th L (suc j)) (N.cg j))
                 -> (F' : Nat) -> LeN Q (suc (plus F' (N.NG j))) -> Res
            step gr F' le' =
              scan Q fin F' (suc j)
                (LeN-trans {Q} {plus F' (suc (N.NG j))} {plus F' (N.NG (suc j))}
                  (Eq-transport (\ z -> LeN Q z)
                    (Eq-sym (plus-suc-r F' (N.NG j))) le')
                  (plus-mono F' F' (suc (N.NG j)) (N.NG (suc j)) (LeN-refl F')
                    (N.NG-grow j (suc j) (LeN-suc j) gr)))

            fuel : (F' : Nat) -> LeN Q (plus F' (N.NG j)) -> Res
            fuel zero     le' = fin j le' nc
            fuel (suc F') le' = route (N.cg j) refl
              where
                route : (c : Nat) -> Eq (N.cg j) c -> Res
                --------------------------------------------------
                -- waits on a PARAMETER: frozen
                --------------------------------------------------
                route (suc (suc i)) ec =
                  frzPar j i (Eq-trans eD (Eq-cong inr ec))
                --------------------------------------------------
                -- waits on `x`: the depth grew
                --------------------------------------------------
                route zero ec =
                  step
                    (Eq-transport
                      (\ z -> LeN (suc (hts (R.avT p Th L j) z))
                                 (hts (R.avT p Th L (suc j)) z))
                      (Eq-sym ec)
                      (Eq-transport
                        (\ z -> LeN (suc z) (hts (R.avT p Th L (suc j)) zero))
                        (Eq-sym (htsAt0 j))
                        (Eq-transport (\ z -> LeN (suc j) z)
                          (Eq-sym (htsAt0 (suc j))) (LeN-refl (suc j)))))
                    F' le'
                --------------------------------------------------
                -- waits on the RECURSIVE VALUE
                --------------------------------------------------
                route (suc zero) ec =
                  rec (EqFEl-dec (R.Vd p Th L (suc j)) (R.Vd p Th L j))
                  where
                    rec : Dec (Eq (R.Vd p Th L (suc j)) (R.Vd p Th L j)) -> Res
                    -- IMG_0270's criterion: frozen
                    rec (yes ev) = frzRec j (Eq-trans eD (Eq-cong inr ec)) ev
                    -- it grew, so its HEIGHT grew
                    rec (no nv) =
                      step
                        (Eq-transport
                          (\ z -> LeN (suc (hts (R.avT p Th L j) z))
                                     (hts (R.avT p Th L (suc j)) z))
                          (Eq-sym ec)
                          (Eq-transport
                            (\ z -> LeN (suc z)
                                       (hts (R.avT p Th L (suc j)) (suc zero)))
                            (Eq-sym (htsAt1 j))
                            (Eq-transport (\ z -> LeN (suc (hgt (R.Vd p Th L j))) z)
                              (Eq-sym (htsAt1 (suc j)))
                              (leF-ne-hgt (R.Vd p Th L j) (R.Vd p Th L (suc j))
                                (vm j (suc j) (LeN-suc j)) (nevV (suc j))
                                (\ e -> nv (Eq-sym e))))))
                        F' le'

    ------------------------------------------------------------------
    -- and the two ways the outer value can behave
    ------------------------------------------------------------------

    result : Res
    result = top (ovTot-or-never (suc (suc p)) Th m1th)
      where
        top : Or (Sigma Nat (\ n0 -> IsCpl (ovOf Th n0)))
                 ((m : Nat) -> Not (IsCpl (ovOf Th m)))
            -> Res
        top (inr nevo) =
          scan Nh finNever Nh zero (plus-ge-l Nh (N.NG zero))
          where
            finNever : (j : Nat) -> LeN Nh (N.NG j)
                     -> Not (IsCpl (ovh (N.NG j))) -> Res
            finNever j past nc =
              mkSigma j
                (N.tail-const Nh stabh j past
                  (\ k lk -> nevo (N.NG k)) (\ k lk -> ncp k (N.cg k)))
        top (inl (mkSigma n0 ic0)) =
          scan Q finTot Q zero (plus-ge-l Q (N.NG zero))
          where
            Q : Nat
            Q = maxN Nh n0

            finTot : (j : Nat) -> LeN Q (N.NG j)
                   -> Not (IsCpl (ovh (N.NG j))) -> Res
            finTot j past nc = Empty-elim (nc icj)
              where
                bigj : LeN n0 (N.NG j)
                bigj = LeN-trans {n0} {Q} {N.NG j} (maxN-le-r Nh n0) past

                icj : IsCpl (ovh (N.NG j))
                icj =
                  Eq-transport (\ z -> IsCpl z)
                    (cpl-max (ovh n0) (ovh (N.NG j)) (fst mth n0 (N.NG j) bigj)
                      ic0)
                    ic0

------------------------------------------------------------------------
-- THE DESCENT CASE
--
-- If the recursive value IS a numeral from `j0` on, it is maximal, so it
-- never moves again -- and then every coordinate but the depth is fixed.
-- The scan is the same three-way test as before, except that "waits on
-- the recursive value" now DESCENDS, into a continuation that
-- `NG-freeze` pins for ever and a family that is exactly `parV`, which
-- `post-stab` settles.
------------------------------------------------------------------------

delEq : (p : Nat) (Th : Tr (suc (suc p))) (L : Nat -> Nat) (j : Nat)
      -> Eq (del (suc zero) (R.avT p Th L j)) (parV p L j)
delEq p Th L j =
  Eq-trans (del-tup (suc p) (suc zero) tt (R.avf p Th L j))
    (tup-cong (suc p) (\ c -> R.avf p Th L j (su (suc zero) c)) (pvf L j) pt)
  where
    pt : (c : Nat) -> Eq (R.avf p Th L j (su (suc zero) c)) (pvf L j c)
    pt zero    = refl
    pt (suc i) = refl

post-desc : (p : Nat) (Th : Tr (suc (suc p)))
          -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
          -> (L : Nat -> Nat)
          -> ((j j' : Nat) -> LeN j j' -> LeF (R.Vd p Th L j) (R.Vd p Th L j'))
          -> (j0 : Nat) -> IsCpl (R.Vd p Th L j0)
          -> Sigma Nat (\ J -> (j : Nat) -> LeN J j
               -> Eq (blockOn (suc (suc p)) Th (R.avT p Th L j))
                     (blockOn (suc (suc p)) Th (R.avT p Th L J)))
post-desc p (stop w) mth m1th L vm j0 ic0 = mkSigma zero (\ j lj -> refl)
post-desc p (node ivh ivhr ovh conth) mth m1th L vm j0 ic0 = result
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth

    module N =
      NGf (suc p) ivh ivhr ovh conth (R.avT p Th L) (PZ.avT-mono p Th L vm) mth

    Res : Set
    Res =
      Sigma Nat (\ J -> (j : Nat) -> LeN J j
        -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L J))

    Nh : Nat
    Nh = fst (fst m1th)

    stabh : (n : Nat) -> LeN Nh n -> Eq (ivh n) (ivh Nh)
    stabh = snd (fst m1th)

    -- the recursive value is maximal, hence never moves again
    VdC : (j : Nat) -> LeN j0 j -> Eq (R.Vd p Th L j0) (R.Vd p Th L j)
    VdC j lj = cpl-max (R.Vd p Th L j0) (R.Vd p Th L j) (vm j0 j lj) ic0

    atV : (j : Nat)
        -> Eq (nth (fbot zero) (suc zero) (R.avT p Th L j)) (R.Vd p Th L j)
    atV j = tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt

    icAt : (j : Nat) -> LeN j0 j -> Eq (N.cg j) (suc zero) -> IsCpl (N.at j)
    icAt j lj ec =
      Eq-transport (\ z -> IsCpl z)
        (Eq-sym
          (Eq-trans (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) ec)
            (Eq-trans (atV j) (Eq-sym (VdC j lj)))))
        ic0

    htsAt0 : (j : Nat) -> Eq (hts (R.avT p Th L j) zero) j
    htsAt0 j = Eq-cong hgt (tup-nth (suc (suc p)) (R.avf p Th L j) zero tt)

    frzInl : (J : Nat) -> IsCpl (ovh (N.NG J)) -> Res
    frzInl J ic =
      mkSigma J (PZ.Dm-inl-frozen p Th L vm mth J (N.blk-inl J ic))

    frzPar : (J i : Nat) -> Eq (PZ.Dmj p Th L J) (inr (suc (suc i))) -> Res
    frzPar J i eJ = mkSigma J (PZ.Dm-par-frozen p Th L vm mth J i eJ)

    ------------------------------------------------------------------
    -- THE DESCENT: the continuation and the family are both fixed
    ------------------------------------------------------------------

    descend : (J : Nat) -> LeN j0 J -> Not (IsCpl (ovh (N.NG J)))
            -> Eq (N.cg J) (suc zero) -> Res
    descend J lJ nc ec = lift (post-stab p L T' mt' m1')
      where
        iaJ : IsCpl (N.at J)
        iaJ = icAt J lJ ec

        T' : Tr (suc p)
        T' = conth (N.cg J) (ivhr (N.NG J)) (hts (R.avT p Th L J) (N.cg J))

        mt' : MonoTr (suc p) T'
        mt' = snd mth (N.cg J) (ivhr (N.NG J)) (hts (R.avT p Th L J) (N.cg J))

        m1' : MP1T (suc p) T'
        m1' = snd (snd m1th) (N.cg J) (ivhr (N.NG J))
                (hts (R.avT p Th L J) (N.cg J))

        -- from `J` on the demand IS the descended one
        blkEq : (j : Nat) -> LeN J j
              -> Eq (PZ.Dmj p Th L j)
                    (shiftOr (N.cg J) (blockOn (suc p) T' (parV p L j)))
        blkEq j lj =
          Eq-trans (N.blk-descend j (ncAt j lj) (iaAt j lj))
            (Eq-trans
              (Eq-cong
                (\ n -> shiftOr (ivh n)
                          (blockOn (suc p)
                            (conth (ivh n) (ivhr n)
                              (hts (R.avT p Th L j) (ivh n)))
                            (del (ivh n) (R.avT p Th L j))))
                (N.NG-freeze J iaJ j lj))
              (Eq-trans
                (Eq-cong
                  (\ w -> shiftOr (N.cg J)
                            (blockOn (suc p) (conth (N.cg J) (ivhr (N.NG J)) w)
                              (del (N.cg J) (R.avT p Th L j))))
                  (htsSame j lj))
                (Eq-cong
                  (\ Y -> shiftOr (N.cg J) (blockOn (suc p) T' Y))
                  (Eq-transport
                    (\ z -> Eq (del z (R.avT p Th L j)) (parV p L j))
                    (Eq-sym ec) (delEq p Th L j)))))
          where
            ncAt : (k : Nat) -> LeN J k -> Not (IsCpl (ovh (N.NG k)))
            ncAt k lk ic =
              nc (Eq-transport (\ z -> IsCpl (ovh z)) (N.NG-freeze J iaJ k lk) ic)

            htsSame : (k : Nat) -> LeN J k
                    -> Eq (hts (R.avT p Th L k) (N.cg J))
                          (hts (R.avT p Th L J) (N.cg J))
            htsSame k lk =
              Eq-cong hgt
                (Eq-sym
                  (cpl-max (nth (fbot zero) (N.cg J) (R.avT p Th L J))
                    (nth (fbot zero) (N.cg J) (R.avT p Th L k))
                    (PZ.avT-mono p Th L vm J k lk (N.cg J)) iaJ))

            iaAt : (k : Nat) -> LeN J k -> IsCpl (N.at k)
            iaAt k lk =
              icAt k (LeN-trans {j0} {J} {k} lJ lk)
                (Eq-trans (N.cg-freeze J iaJ k lk) ec)

        lift : Sigma Nat (\ J' -> (j : Nat) -> LeN J' j
                 -> Eq (blockOn (suc p) T' (parV p L j))
                       (blockOn (suc p) T' (parV p L J')))
             -> Res
        lift (mkSigma J' con) = mkSigma M go
          where
            M : Nat
            M = maxN J J'

            go : (j : Nat) -> LeN M j
               -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L M)
            go j lj =
              Eq-trans (blkEq j lJj)
                (Eq-trans
                  (Eq-cong (shiftOr (N.cg J))
                    (Eq-trans (con j lJ'j) (Eq-sym (con M lJ'M))))
                  (Eq-sym (blkEq M lJM)))
              where
                lJM : LeN J M
                lJM = maxN-le-l J J'

                lJ'M : LeN J' M
                lJ'M = maxN-le-r J J'

                lJj : LeN J j
                lJj = LeN-trans {J} {M} {j} lJM lj

                lJ'j : LeN J' j
                lJ'j = LeN-trans {J'} {M} {j} lJ'M lj

    ------------------------------------------------------------------
    -- THE SCAN
    ------------------------------------------------------------------

    scan : (Q : Nat)
         -> ((j : Nat) -> LeN j0 j -> LeN Q (N.NG j)
             -> Not (IsCpl (ovh (N.NG j))) -> Eq (N.cg j) zero -> Res)
         -> (F j : Nat) -> LeN j0 j -> LeN Q (plus F (N.NG j)) -> Res
    scan Q fin F j lj le = top (IsCpl-dec (ovh (N.NG j)))
      where
        top : Dec (IsCpl (ovh (N.NG j))) -> Res
        top (yes ic) = frzInl j ic
        top (no  nc) = route (N.cg j) refl
          where
            route : (c : Nat) -> Eq (N.cg j) c -> Res
            route (suc (suc i)) ec =
              frzPar j i
                (Eq-trans (N.blk-fbot j nc (naZ ec)) (Eq-cong inr ec))
              where
                naZ : Eq (N.cg j) (suc (suc i)) -> Not (IsCpl (N.at j))
                naZ e =
                  Eq-transport
                    (\ z -> Not (IsCpl (nth (fbot zero) z (R.avT p Th L j))))
                    (Eq-sym e)
                    (PZ.avT-incpl p Th L j (suc (suc i)) (\ ()))
            route (suc zero) ec = descend j lj nc ec
            route zero       ec = fuel F le
              where
                fuel : (F' : Nat) -> LeN Q (plus F' (N.NG j)) -> Res
                fuel zero     le' = fin j lj le' nc ec
                fuel (suc F') le' =
                  scan Q fin F' (suc j)
                    (LeN-trans {j0} {j} {suc j} lj (LeN-suc j))
                    (LeN-trans {Q} {plus F' (suc (N.NG j))}
                      {plus F' (N.NG (suc j))}
                      (Eq-transport (\ z -> LeN Q z)
                        (Eq-sym (plus-suc-r F' (N.NG j))) le')
                      (plus-mono F' F' (suc (N.NG j)) (N.NG (suc j))
                        (LeN-refl F')
                        (N.NG-grow j (suc j) (LeN-suc j) gr)))
                  where
                    gr : LeN (suc (hts (R.avT p Th L j) (N.cg j)))
                             (hts (R.avT p Th L (suc j)) (N.cg j))
                    gr =
                      Eq-transport
                        (\ z -> LeN (suc (hts (R.avT p Th L j) z))
                                   (hts (R.avT p Th L (suc j)) z))
                        (Eq-sym ec)
                        (Eq-transport
                          (\ z -> LeN (suc z) (hts (R.avT p Th L (suc j)) zero))
                          (Eq-sym (htsAt0 j))
                          (Eq-transport (\ z -> LeN (suc j) z)
                            (Eq-sym (htsAt0 (suc j))) (LeN-refl (suc j))))

    result : Res
    result = top (ovTot-or-never (suc (suc p)) Th m1th)
      where
        top : Or (Sigma Nat (\ n0 -> IsCpl (ovOf Th n0)))
                 ((m : Nat) -> Not (IsCpl (ovOf Th m)))
            -> Res
        top (inr nevo) =
          scan Nh finNever Nh j0 (LeN-refl j0) (plus-ge-l Nh (N.NG j0))
          where
            finNever : (j : Nat) -> LeN j0 j -> LeN Nh (N.NG j)
                     -> Not (IsCpl (ovh (N.NG j))) -> Eq (N.cg j) zero -> Res
            finNever j lj past nc ec =
              mkSigma j
                (N.tail-const Nh stabh j past
                  (\ k lk -> nevo (N.NG k)) na)
              where
                na : (k : Nat) -> LeN j k -> Not (IsCpl (N.at k))
                na k lk =
                  Eq-transport
                    (\ z -> Not (IsCpl (nth (fbot zero) z (R.avT p Th L k))))
                    (Eq-sym cgk)
                    (PZ.avT-incpl p Th L k zero (\ ()))
                  where
                    cgk : Eq (N.cg k) zero
                    cgk =
                      Eq-trans
                        (Eq-trans
                          (stabh (N.NG k)
                            (LeN-trans {Nh} {N.NG j} {N.NG k} past
                              (N.NG-mono j k lk)))
                          (Eq-sym (stabh (N.NG j) past)))
                        ec
        top (inl (mkSigma n0 ic0')) =
          scan Q finTot Q j0 (LeN-refl j0) (plus-ge-l Q (N.NG j0))
          where
            Q : Nat
            Q = maxN Nh n0

            finTot : (j : Nat) -> LeN j0 j -> LeN Q (N.NG j)
                   -> Not (IsCpl (ovh (N.NG j))) -> Eq (N.cg j) zero -> Res
            finTot j lj past nc ec = Empty-elim (nc icj)
              where
                bigj : LeN n0 (N.NG j)
                bigj = LeN-trans {n0} {Q} {N.NG j} (maxN-le-r Nh n0) past

                icj : IsCpl (ovh (N.NG j))
                icj =
                  Eq-transport (\ z -> IsCpl z)
                    (cpl-max (ovh n0) (ovh (N.NG j)) (fst mth n0 (N.NG j) bigj)
                      ic0')
                    ic0'

------------------------------------------------------------------------
-- THE DEPTH DIRECTION, ASSEMBLED
--
-- The two branches are chosen by ONE question -- does the recursive value
-- ever become a numeral? -- and that question is answered by Proposition
-- 1 applied to the chain: `TrPrecDen.Vd-den` says
-- `Vd L j = precFun g h (avP p L j)`, and `avP p L .` is exactly the
-- family `Property.UO` speaks about at the point whose coordinate 0 is
-- `S^w(bot)` and whose parameters are at `L`.  Case 1 gives the numeral,
-- Cases 2 and 3 give "never".
------------------------------------------------------------------------

Dm-stab : (p : Nat) (Th : Tr (suc (suc p)))
        -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
        -> (L : Nat -> Nat)
        -> ((j j' : Nat) -> LeN j j' -> LeF (R.Vd p Th L j) (R.Vd p Th L j'))
        -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
              ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
        -> Sigma Nat (\ J -> (j : Nat) -> LeN J j
             -> Eq (blockOn (suc (suc p)) Th (R.avT p Th L j))
                   (blockOn (suc (suc p)) Th (R.avT p Th L J)))
Dm-stab p Th mth m1th L vm (inl (mkSigma j0 ic0)) =
  post-desc p Th mth m1th L vm j0 ic0
Dm-stab p Th mth m1th L vm (inr nev) =
  pre-stab p Th mth m1th L vm nev

-- ... and then the fold settles one step later
Qd-stab-full : (p : Nat) (Th : Tr (suc (suc p)))
             -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
             -> (L : Nat -> Nat)
             -> ((j j' : Nat) -> LeN j j'
                 -> LeF (R.Vd p Th L j) (R.Vd p Th L j'))
             -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
                   ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
             -> Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
                  -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J)))
Qd-stab-full p Th mth m1th L vm dec = route (Dm-stab p Th mth m1th L vm dec)
  where
    route : Sigma Nat (\ J -> (j : Nat) -> LeN J j
              -> Eq (blockOn (suc (suc p)) Th (R.avT p Th L j))
                    (blockOn (suc (suc p)) Th (R.avT p Th L J)))
          -> Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
               -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J)))
    route (mkSigma J con) = mkSigma J (QD.Qd-evconst p Th L J con)

------------------------------------------------------------------------
-- A PARAMETER DEMAND PAST THE THRESHOLD IS TERMINAL
--
-- This is what makes the fuel over parameter bumps close.  Suppose at
-- depth `J` the step term's replay is already past its own threshold
-- `Nh` and its eventual demand `ivh Nh` is a PARAMETER `2+i`.  Then
-- `cg-past` gives that demand at EVERY depth above `J`; a parameter is
-- never a numeral, so nothing descends there; hence `Qd L D = 1+i` for
-- every `D > J`, by `Qd-indep-par`.
--
-- And the hypothesis survives a bump: raising a parameter only raises
-- the tuple, so `NG` only grows, so `LeN Nh (NG J)` still holds at the
-- next stage.  A bump whose parameter is ALREADY at level `Nh` therefore
-- fixes the index for ever -- while a bump below `Nh` costs one unit of a
-- budget of `p * Nh`.  That is the dichotomy `cg-or-small` provides.
------------------------------------------------------------------------

Qd-par-const : (p : Nat)
               (ivh : Nat -> Nat)
               (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
               (ovh : Nat -> FEl)
               (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                      -> Tr (suc p))
             -> (mth : MonoTr (suc (suc p)) (node ivh ivhr ovh conth))
             -> (L : Nat -> Nat)
             -> (vm : (j j' : Nat) -> LeN j j'
                    -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                           (R.Vd p (node ivh ivhr ovh conth) L j'))
             -> (Nh : Nat) -> ((n : Nat) -> LeN Nh n -> Eq (ivh n) (ivh Nh))
             -> ((m : Nat) -> Not (IsCpl (ovh m)))
             -> (J i : Nat)
             -> LeN Nh (NGf.NG (suc p) ivh ivhr ovh conth
                          (R.avT p (node ivh ivhr ovh conth) L)
                          (PZ.avT-mono p (node ivh ivhr ovh conth) L vm) mth J)
             -> Eq (ivh Nh) (suc (suc i))
             -> (D : Nat) -> LeN (suc J) D
             -> Eq (R.Qd p (node ivh ivhr ovh conth) L D) (suc i)
Qd-par-const p ivh ivhr ovh conth mth L vm Nh stabh nevo J i past ei D lD =
  PZ.Qd-indep-par p Th L J i con eJ D lD
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth

    module N =
      NGf (suc p) ivh ivhr ovh conth (R.avT p Th L) (PZ.avT-mono p Th L vm) mth

    dem : (j : Nat) -> LeN J j -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i)))
    dem j lj =
      Eq-trans (N.blk-fbot j (nevo (N.NG j)) na) (Eq-cong inr cgj)
      where
        cgj : Eq (N.cg j) (suc (suc i))
        cgj = Eq-trans (N.cg-past Nh stabh J past j lj) ei

        na : Not (IsCpl (N.at j))
        na =
          Eq-transport
            (\ z -> Not (IsCpl (nth (fbot zero) z (R.avT p Th L j))))
            (Eq-sym cgj)
            (PZ.avT-incpl p Th L j (suc (suc i)) (\ ()))

    eJ : Eq (PZ.Dmj p Th L J) (inr (suc (suc i)))
    eJ = dem J (LeN-refl J)

    con : (j : Nat) -> LeN J j -> Eq (PZ.Dmj p Th L j) (PZ.Dmj p Th L J)
    con j lj = Eq-trans (dem j lj) (Eq-sym eJ)

-- the chain is monotone in the PARAMETER LEVELS too, given that the
-- recursive value is (`TrPrecDec.Vd-mono-L` supplies that)
PZ-avT-mono-L : (p : Nat) (Th : Tr (suc (suc p))) (L L' : Nat -> Nat)
              -> ((j : Nat) -> LeF (R.Vd p Th L j) (R.Vd p Th L' j))
              -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
              -> (j : Nat) -> LeX (R.avT p Th L j) (R.avT p Th L' j)
PZ-avT-mono-L p Th L L' vmL lp j =
  tup-le (suc (suc p)) (R.avf p Th L j) (R.avf p Th L' j) go
  where
    go : (c : Nat) -> LeN (suc c) (suc (suc p))
       -> LeF (R.avf p Th L j c) (R.avf p Th L' j c)
    go zero          lc = LeN-refl j
    go (suc zero)    lc = vmL j
    go (suc (suc i)) lc = lp i

------------------------------------------------------------------------
-- THE BUDGET FOR PARAMETER BUMPS
--
-- `cg-or-small` splits a parameter bump in two: either the parameter's
-- level is already `Nh` -- and then `Qd-par-const` fixes the index for
-- ever -- or it is below `Nh`, and the bump raises it.  Count the second
-- kind with
--
--     Mof Nh k = sum over the parameters of (min (level) Nh)
--
-- which is bounded by `p * Nh` and STRICTLY INCREASES on every cheap
-- bump.  So there are at most `p * Nh` of them, and `M-max` says that at
-- the bound every bump must be the terminal kind.
------------------------------------------------------------------------

sumTo-cong : (n : Nat) (f g : Nat -> Nat) -> ((i : Nat) -> Eq (f i) (g i))
           -> Eq (sumTo n f) (sumTo n g)
sumTo-cong zero    f g e = refl
sumTo-cong (suc n) f g e = Eq-cong2 plus (e n) (sumTo-cong n f g e)

module BUD (p : Nat) (Th : Tr (suc (suc p))) (Nh : Nat) where

  open P p Th

  Mof : Nat -> Nat
  Mof k = sumTo p (\ i -> minN (Lv k (suc i)) Nh)

  Cap : Nat
  Cap = sumTo p (\ _ -> Nh)

  M-bound : (k : Nat) -> LeN (Mof k) Cap
  M-bound k =
    sumTo-mono p (\ i -> minN (Lv k (suc i)) Nh) (\ _ -> Nh)
      (\ i -> minN-le-r (Lv k (suc i)) Nh)

  -- a CHEAP bump raises the budget by exactly one
  M-step : (k i0 : Nat) -> LeN (suc i0) p -> Eq (ivP k) (suc i0)
         -> LeN (suc (Lv k (suc i0))) Nh
         -> Eq (Mof (suc k)) (suc (Mof k))
  M-step k i0 li0 ev cheap =
    Eq-trans
      (sumTo-cong p (\ i -> minN (Lv (suc k) (suc i)) Nh)
        (bump i0 (\ i -> minN (Lv k (suc i)) Nh)) pt)
      (sumTo-bump p i0 li0 (\ i -> minN (Lv k (suc i)) Nh))
    where
      pt : (i : Nat) -> Eq (minN (Lv (suc k) (suc i)) Nh)
                           (bump i0 (\ d -> minN (Lv k (suc d)) Nh) i)
      pt i = route (EqNat-dec i i0)
        where
          route : Dec (Eq i i0)
                -> Eq (minN (Lv (suc k) (suc i)) Nh)
                      (bump i0 (\ d -> minN (Lv k (suc d)) Nh) i)
          route (yes e) =
            Eq-trans
              (Eq-cong (\ z -> minN (Lv (suc k) (suc z)) Nh) e)
              (Eq-trans atI0
                (Eq-sym
                  (Eq-trans
                    (Eq-cong (bump i0 (\ d -> minN (Lv k (suc d)) Nh)) e)
                    (bump-eq i0 (\ d -> minN (Lv k (suc d)) Nh) i0 refl))))
            where
              lvE : Eq (Lv (suc k) (suc i0)) (suc (Lv k (suc i0)))
              lvE =
                Eq-trans
                  (bump-eq (ivP k) (Lv k) (suc i0) (Eq-sym ev))
                  refl

              atI0 : Eq (minN (Lv (suc k) (suc i0)) Nh)
                        (suc (minN (Lv k (suc i0)) Nh))
              atI0 =
                Eq-trans (Eq-cong (\ z -> minN z Nh) lvE)
                  (Eq-trans (minN-l {suc (Lv k (suc i0))} {Nh} cheap)
                    (Eq-cong suc
                      (Eq-sym
                        (minN-l {Lv k (suc i0)} {Nh}
                          (LeN-trans {Lv k (suc i0)} {suc (Lv k (suc i0))} {Nh}
                            (LeN-suc (Lv k (suc i0))) cheap)))))
          route (no ne) =
            Eq-trans
              (Eq-cong (\ z -> minN z Nh)
                (bump-ne (ivP k) (Lv k) (suc i)
                  (\ e -> ne (suc-inj (Eq-trans e ev)))))
              (Eq-sym (bump-ne i0 (\ d -> minN (Lv k (suc d)) Nh) i ne))

  -- at the bound, every bump must be the TERMINAL kind
  M-max : (k i0 : Nat) -> LeN (suc i0) p -> Eq (ivP k) (suc i0)
        -> LeN Cap (Mof k) -> Not (LeN (suc (Lv k (suc i0))) Nh)
  M-max k i0 li0 ev full cheap =
    LeN-suc-not Cap
      (LeN-trans {suc Cap} {suc (Mof k)} {Cap} full
        (Eq-transport (\ z -> LeN z Cap) (M-step k i0 li0 ev cheap)
          (M-bound (suc k))))

------------------------------------------------------------------------
-- THE ASSEMBLY (main phase: the recursive value is never a numeral,
-- so nothing ever descends)
--
-- A fuel-recursion on the budget `BUD.Cap = p * Nh`.  At each stage the
-- index is decided:
--
--   * `0`      -- run `PZ.stretch`: if the index is `0` for the first
--                 `J+2` steps (`J` from the depth direction) it is `0`
--                 FOR EVER; otherwise jump to the first stage that is
--                 not, which is a bump;
--   * `1+i`    -- `Qd-source` names a depth `j*` where the step term
--                 demands the parameter, and `cg-or-small`'s dichotomy
--                 applies: past `Nh` the bump is TERMINAL
--                 (`Qd-par-const`, whose hypothesis survives every later
--                 bump because `NG` is monotone in `L`), below `Nh` it is
--                 CHEAP and costs one unit of the budget (`M-step`).
--
-- `M-max` says the cheap case cannot occur once the budget is spent, so
-- the recursion terminates.
------------------------------------------------------------------------

module LOOP (p : Nat)
            (ivh : Nat -> Nat)
            (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
            (ovh : Nat -> FEl)
            (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                   -> Tr (suc p))
            (mth : MonoTr (suc (suc p)) (node ivh ivhr ovh conth))
            (m1th : MP1T (suc (suc p)) (node ivh ivhr ovh conth))
            (vmj : (L : Nat -> Nat) (j j' : Nat) -> LeN j j'
                 -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                        (R.Vd p (node ivh ivhr ovh conth) L j'))
            (vmL : (L L' : Nat -> Nat)
                 -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
                 -> (j : Nat) -> LeX (R.avT p (node ivh ivhr ovh conth) L j)
                                     (R.avT p (node ivh ivhr ovh conth) L' j))
            (nevo : (m : Nat) -> Not (IsCpl (ovh m)))
            (nevV : (L : Nat -> Nat) (j : Nat)
                  -> Not (IsCpl (R.Vd p (node ivh ivhr ovh conth) L j)))
            where

  Th : Tr (suc (suc p))
  Th = node ivh ivhr ovh conth

  open P p Th

  Nh : Nat
  Nh = fst (fst m1th)

  stabh : (n : Nat) -> LeN Nh n -> Eq (ivh n) (ivh Nh)
  stabh = snd (fst m1th)

  module B = BUD p Th Nh

  ------------------------------------------------------------------
  -- the replay depth, and its two monotonicities
  ------------------------------------------------------------------

  NGat : (Nat -> Nat) -> Nat -> Nat
  NGat L j = nOf (suc (suc p)) ivh ivhr (hts (R.avT p Th L j))

  NG-monoL : (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j : Nat) -> LeN (NGat L j) (NGat L' j)
  NG-monoL L L' lp j =
    nOf-mono (suc (suc p)) ivh ivhr
      (hts (R.avT p Th L j)) (hts (R.avT p Th L' j))
      (LeX-hts (R.avT p Th L j) (R.avT p Th L' j) (vmL L L' lp j))

  Lv-monoP : (k k' : Nat) -> LeN k k' -> (i : Nat)
           -> LeN (Lv k (suc i)) (Lv k' (suc i))
  Lv-monoP k k' le i = lev-mono ivP Lv (\ _ _ -> refl) k k' le (suc i)

  Lv-mono0 : (k k' : Nat) -> LeN k k' -> LeN (Lv k zero) (Lv k' zero)
  Lv-mono0 k k' le = lev-mono ivP Lv (\ _ _ -> refl) k k' le zero

  ------------------------------------------------------------------
  -- nothing at a demanded coordinate is ever a numeral
  ------------------------------------------------------------------

  ncAll : (L : Nat -> Nat) (j c : Nat)
        -> Not (IsCpl (nth (fbot zero) c (R.avT p Th L j)))
  ncAll L j c = route (EqNat-dec c (suc zero))
    where
      route : Dec (Eq c (suc zero))
            -> Not (IsCpl (nth (fbot zero) c (R.avT p Th L j)))
      route (no ne) = PZ.avT-incpl p Th L j c ne
      route (yes e) = \ ic -> nevV L j (Eq-transport (\ z -> IsCpl z) atV ic)
        where
          atV : Eq (nth (fbot zero) c (R.avT p Th L j)) (R.Vd p Th L j)
          atV =
            Eq-trans (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) e)
              (tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt)

  ------------------------------------------------------------------
  -- the depth direction, at each parameter setting
  ------------------------------------------------------------------

  JJ : (L : Nat -> Nat)
     -> Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
          -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J)))
  JJ L = Qd-stab-full p Th mth m1th L (vmj L) (inr (nevV L))

  ------------------------------------------------------------------
  -- the two outcomes
  ------------------------------------------------------------------

  Res : Set
  Res = Sigma Nat (\ N -> (n : Nat) -> LeN N n -> Eq (ivP n) (ivP N))

  -- a bump whose parameter is already at level `Nh`
  terminal : (k i0 j : Nat) -> Eq (ivP k) (suc i0)
           -> LeN (suc j) (Lv k zero) -> LeN Nh (NGat (Lv k) j)
           -> Eq (ivh Nh) (suc (suc i0)) -> Res
  terminal k i0 j ev lj past ei = mkSigma k con
    where
      con : (n : Nat) -> LeN k n -> Eq (ivP n) (ivP k)
      con n ln =
        Eq-trans
          (Qd-par-const p ivh ivhr ovh conth mth (Lv n) (vmj (Lv n))
            Nh stabh nevo j i0
            (LeN-trans {Nh} {NGat (Lv k) j} {NGat (Lv n) j} past
              (NG-monoL (Lv k) (Lv n) (Lv-monoP k n ln) j))
            ei (Lv n zero)
            (LeN-trans {suc j} {Lv k zero} {Lv n zero} lj (Lv-mono0 k n ln)))
          (Eq-sym ev)

  ------------------------------------------------------------------
  -- the budget only ever grows
  ------------------------------------------------------------------

  minN-mono : (a b c : Nat) -> LeN a b -> LeN (minN a c) (minN b c)
  minN-mono zero    b       c       le = tt
  minN-mono (suc a) zero    c       ()
  minN-mono (suc a) (suc b) zero    le = tt
  minN-mono (suc a) (suc b) (suc c) le = minN-mono a b c le

  Mof-mono : (k k' : Nat) -> LeN k k' -> LeN (B.Mof k) (B.Mof k')
  Mof-mono k k' le =
    sumTo-mono p (\ i -> minN (Lv k (suc i)) Nh) (\ i -> minN (Lv k' (suc i)) Nh)
      (\ i -> minN-mono (Lv k (suc i)) (Lv k' (suc i)) Nh (Lv-monoP k k' le i))

  ------------------------------------------------------------------
  -- THE LOOP
  ------------------------------------------------------------------

  loop : (F k : Nat) -> LeN B.Cap (plus F (B.Mof k)) -> Res
  loop F k inv = route (ivP k) refl
    where
      ------------------------------------------------------------
      -- a bump at stage `k'`, demanding parameter `i0`
      ------------------------------------------------------------
      bumpAt : (k' i0 : Nat) -> LeN k k' -> Eq (ivP k') (suc i0) -> Res
      bumpAt k' i0 lkk' ev = src (PZ.Qd-source p Th (Lv k') (Lv k' zero) i0 ev)
        where
          src : Sigma Nat (\ j -> Pair (LeN (suc j) (Lv k' zero))
                  (Eq (PZ.Dmj p Th (Lv k') j) (inr (suc (suc i0)))))
              -> Res
          src (mkSigma j (mkSigma lj eD)) = pick (LeN-dec Nh (NGat (Lv k') j))
            where
              -- the demand at `j` IS the top-level one: nothing descends
              ecg : Eq (ivh (NGat (Lv k') j)) (suc (suc i0))
              ecg =
                inr-inj (ivh (NGat (Lv k') j)) (suc (suc i0))
                  (Eq-trans
                    (Eq-sym
                      (NGf.blk-fbot (suc p) ivh ivhr ovh conth
                        (R.avT p Th (Lv k')) (PZ.avT-mono p Th (Lv k') (vmj (Lv k')))
                        mth j (nevo (NGat (Lv k') j))
                        (ncAll (Lv k') j (ivh (NGat (Lv k') j)))))
                    eD)

              pick : Dec (LeN Nh (NGat (Lv k') j)) -> Res
              --------------------------------------------------
              -- past the threshold: TERMINAL
              --------------------------------------------------
              pick (yes past) =
                terminal k' i0 j ev lj past
                  (Eq-trans (Eq-sym (stabh (NGat (Lv k') j) past)) ecg)
              --------------------------------------------------
              -- below it: CHEAP, one unit of the budget
              --------------------------------------------------
              pick (no nl) = spend F inv'
                where
                  cheap : LeN (suc (Lv k' (suc i0))) Nh
                  cheap =
                    LeN-trans {suc (Lv k' (suc i0))} {suc (NGat (Lv k') j)} {Nh}
                      (Eq-transport (\ z -> LeN z (NGat (Lv k') j)) htsE
                        (NGf.NG-ge-hts (suc p) ivh ivhr ovh conth
                          (R.avT p Th (Lv k'))
                          (PZ.avT-mono p Th (Lv k') (vmj (Lv k'))) mth j))
                      (nle-lt Nh (NGat (Lv k') j) nl)
                    where
                      htsE : Eq (hts (R.avT p Th (Lv k') j)
                                   (ivh (NGat (Lv k') j)))
                                (Lv k' (suc i0))
                      htsE =
                        Eq-cong hgt
                          (Eq-trans
                            (Eq-cong
                              (\ z -> nth (fbot zero) z (R.avT p Th (Lv k') j))
                              ecg)
                            (tup-nth (suc (suc p)) (R.avf p Th (Lv k') j)
                              (suc (suc i0)) li0'))
                        where
                          li0' : LeN (suc (suc (suc i0))) (suc (suc p))
                          li0' =
                            Eq-transport (\ z -> LeN (suc z) (suc (suc p))) ecg
                              (ivhr (NGat (Lv k') j))

                  li0 : LeN (suc i0) p
                  li0 =
                    Eq-transport (\ z -> LeN (suc z) (suc (suc p))) ecg
                      (ivhr (NGat (Lv k') j))

                  inv' : LeN B.Cap (plus F (B.Mof k'))
                  inv' =
                    LeN-trans {B.Cap} {plus F (B.Mof k)} {plus F (B.Mof k')} inv
                      (plus-mono F F (B.Mof k) (B.Mof k') (LeN-refl F)
                        (Mof-mono k k' lkk'))

                  spend : (F' : Nat) -> LeN B.Cap (plus F' (B.Mof k')) -> Res
                  spend zero     le' =
                    Empty-elim (B.M-max k' i0 li0 ev le' cheap)
                  spend (suc F') le' =
                    loop F' (suc k')
                      (Eq-transport (\ z -> LeN B.Cap z) (Eq-sym stepE) le')
                    where
                      stepE : Eq (plus F' (B.Mof (suc k')))
                                 (suc (plus F' (B.Mof k')))
                      stepE =
                        Eq-trans
                          (Eq-cong (plus F') (B.M-step k' i0 li0 ev cheap))
                          (plus-suc-r F' (B.Mof k'))

      ------------------------------------------------------------
      -- the index is `0` here: either for ever, or a bump is near
      ------------------------------------------------------------
      zeroCase : Eq (ivP k) zero -> Res
      zeroCase ev = jj (JJ (Lv k))
        where
          jj : Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
                 -> Eq (R.Qd p Th (Lv k) j) (R.Qd p Th (Lv k) (suc J)))
             -> Res
          jj (mkSigma J con) = sc (scanZ (suc (suc J)))
            where
              P0 : Nat -> Set
              P0 t = Eq (ivP (plus t k)) zero

              P0dec : (t : Nat) -> Dec (P0 t)
              P0dec t = EqNat-dec (ivP (plus t k)) zero

              scanZ : (s : Nat)
                    -> Or ((t : Nat) -> LeN (suc t) s -> P0 t)
                          (Sigma Nat (\ t -> Pair (LeN (suc t) s) (Not (P0 t))))
              scanZ zero    = inl (\ t ())
              scanZ (suc s) = step (scanZ s)
                where
                  step : Or ((t : Nat) -> LeN (suc t) s -> P0 t)
                            (Sigma Nat (\ t -> Pair (LeN (suc t) s) (Not (P0 t))))
                       -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                             (Sigma Nat (\ t ->
                                Pair (LeN (suc t) (suc s)) (Not (P0 t))))
                  step (inr (mkSigma t (mkSigma lt np))) =
                    inr (mkSigma t
                          (mkSigma (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s))
                            np))
                  step (inl hh) = step2 (P0dec s)
                    where
                      step2 : Dec (P0 s)
                            -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                                  (Sigma Nat (\ t ->
                                     Pair (LeN (suc t) (suc s)) (Not (P0 t))))
                      step2 (no np) =
                        inr (mkSigma s (mkSigma (LeN-refl s) np))
                      step2 (yes ps) = inl ext
                        where
                          ext : (t : Nat) -> LeN (suc t) (suc s) -> P0 t
                          ext t lt = pk (LeN-dec (suc t) s)
                            where
                              pk : Dec (LeN (suc t) s) -> P0 t
                              pk (yes l)  = hh t l
                              pk (no  nl) =
                                Eq-transport P0
                                  (Eq-sym (le-nlt-eq t s lt nl)) ps

              sc : Or ((t : Nat) -> LeN (suc t) (suc (suc J)) -> P0 t)
                      (Sigma Nat (\ t ->
                         Pair (LeN (suc t) (suc (suc J))) (Not (P0 t))))
                 -> Res
              -- `0` for the whole window, hence for ever
              sc (inl hh) = mkSigma k con0
                where
                  allz : (t : Nat) -> Eq (ivP (plus t k)) zero
                  allz = PZ.stretch p Th k J con hh

                  con0 : (n : Nat) -> LeN k n -> Eq (ivP n) (ivP k)
                  con0 n ln = rt (le-add k n ln)
                    where
                      rt : Sigma Nat (\ t -> Eq n (plus t k))
                         -> Eq (ivP n) (ivP k)
                      rt (mkSigma t e) =
                        Eq-trans
                          (Eq-transport (\ z -> Eq (ivP z) zero) (Eq-sym e)
                            (allz t))
                          (Eq-sym ev)
              -- a bump within the window
              sc (inr (mkSigma t (mkSigma lt np))) =
                nz (ivP (plus t k)) refl
                where
                  nz : (v : Nat) -> Eq (ivP (plus t k)) v -> Res
                  nz zero     e = Empty-elim (np e)
                  nz (suc i0) e = bumpAt (plus t k) i0 (plus-ge-r t k) e

      route : (v : Nat) -> Eq (ivP k) v -> Res
      route zero     ev = zeroCase ev
      route (suc i0) ev = bumpAt k i0 (LeN-refl k) ev

  ivP-evconst : Res
  ivP-evconst = loop B.Cap zero (plus-ge-l B.Cap (B.Mof zero))

  -- ... which IS the index clause of MP1 for the recursion trace
  ivP-EvConstN : EvConstN (P.ivP p Th)
  ivP-EvConstN = ivP-evconst

------------------------------------------------------------------------
-- SO IN THE DESCENT REGIME THE INDEX IS THE TOP DEMAND, FULL STOP
--
-- `Dm-not-one` plus `qsel-indep`: at a depth whose recursive value is a
-- numeral the fold ignores everything below it, so `Qd L (D+1)` is a
-- function of `blockOn Th (avT L D)` ALONE.  Together with `post-stab` --
-- which settles that demand, the post-descent family having only the
-- depth moving -- this is what makes the descent phase of the parameter
-- direction no harder than the main one.
------------------------------------------------------------------------

Qd-top-only : (p : Nat)
              (ivh : Nat -> Nat)
              (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
              (ovh : Nat -> FEl)
              (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                     -> Tr (suc p))
            -> (mth : MonoTr (suc (suc p)) (node ivh ivhr ovh conth))
            -> (L : Nat -> Nat)
            -> (vm : (j j' : Nat) -> LeN j j'
                   -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                          (R.Vd p (node ivh ivhr ovh conth) L j'))
            -> (D : Nat) -> IsCpl (R.Vd p (node ivh ivhr ovh conth) L D)
            -> Eq (R.Qd p (node ivh ivhr ovh conth) L (suc D))
                  (qsel zero (PZ.Dmj p (node ivh ivhr ovh conth) L D))
Qd-top-only p ivh ivhr ovh conth mth L vm D ic =
  qsel-indep (R.Qd p (node ivh ivhr ovh conth) L D) zero
    (PZ.Dmj p (node ivh ivhr ovh conth) L D)
    (Dm-not-one p ivh ivhr ovh conth mth L vm D ic)
