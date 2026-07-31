{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecDec
--
-- DOES THE RECURSIVE VALUE EVER BECOME A NUMERAL?
--
-- That is the one question `TrPrecIv.Dm-stab` takes as a hypothesis, and
-- Proposition 1 answers it.  `TrPrecDen.Vd-den` says
--
--     Vd L j = precFun g h (avP p L j)
--
-- and `avP p L .` -- coordinate 0 at `S^j(bot)`, the parameters frozen at
-- `L` -- is EXACTLY the family `Property.UO` speaks about at the point
-- whose coordinate 0 is `S^w(bot)`:
--
--   * UO Case 1 -- `f` is `S^m(0)` above a finite `A0` -- gives the
--     numeral, at the computable stage where `avP` passes `A0`;
--   * UO Case 2 -- pinned at a coordinate with an incomplete FINITE
--     value, hence not coordinate 0 -- gives `f X = S^m(bot)`, so the
--     value is incomplete at arbitrarily large `j`, hence (monotone plus
--     `cpl-max`) incomplete everywhere;
--   * UO Case 3 -- at the infinite coordinate, which must be 0 -- gives
--     `f X = S^(phi m)(bot)`, incomplete likewise.
--
-- This is `TrVerdict.verdict-of`'s move at a different family, and a
-- simpler one: there is no walk here, coordinate 0 just grows by one per
-- step.  The plumbing (`dtup`, `ptD`, the `Below` analysis) is reused
-- from `TrVerdict`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecDec where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using
  (UO ; uo1 ; uo2 ; uo3 ; getF ; IncompleteFinite)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r)
open import OBSTINATION.MP1 using (plus-ge-l)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrDen
open import OBSTINATION.TrPrecFun using (precFun ; precFun-mono ; LeX-cons)
open import OBSTINATION.TrPrecFrz using (tup-le)
open import OBSTINATION.TrPrecIv using (Qd-stab-full ; PZ-avT-mono-L)
open import OBSTINATION.TrPrecDen using (avP ; avP-len ; parTup ; Vd-den)
open import OBSTINATION.TrPrec using (module R)
open import OBSTINATION.TrMP1 using (MP1T)
open import OBSTINATION.TrMPT using (MPT ; mp1-mpT)
open import OBSTINATION.TrVerdict using
  (dtup ; dtup-len ; dtup-nth ; dtup-out ; get-embedTup ; embedTup-len ;
   LeTup-len ; bot-not-inf ; embed-bot ; below-bot ; below-bot-le ; below-inf ;
   notCpl-shape ; fbot-notCpl ; orD ; ptD ; ptD-I ; ptD-ne)

------------------------------------------------------------------------
-- THE CHAIN AS A FAMILY
------------------------------------------------------------------------

module DC (p : Nat) (g h : FTup -> FEl)
         (mg : MonoF p g) (mh : MonoF (suc (suc p)) h)
         (L : Nat -> Nat)
         where

  FF : FTup -> FEl
  FF = precFun g h

  XT : Nat -> FTup
  XT j = avP p L j

  XTlen : (j : Nat) -> Eq (length (XT j)) (suc p)
  XTlen j = avP-len p L j

  -- coordinate 0 grows by exactly one per step
  XT-0 : (j : Nat) -> Eq (getF zero (XT j)) (fbot j)
  XT-0 j = refl

  -- and every other coordinate does not move at all
  XT-suc : (j i : Nat)
         -> Eq (getF (suc i) (XT j)) (nth (fbot zero) i (parTup p L))
  XT-suc j i = refl

  XT-par : (j i : Nat) -> LeN (suc i) p
         -> Eq (getF (suc i) (XT j)) (fbot (L (suc i)))
  XT-par j i li = tup-nth p (\ d -> fbot (L (suc d))) i li

  XT-mono : (j j' : Nat) -> LeN j j' -> LeX (XT j) (XT j')
  XT-mono j j' lj =
    LeX-cons (fbot j) (fbot j') (parTup p L) (parTup p L) lj
      (\ c -> LeF-refl (nth (fbot zero) c (parTup p L)))

  FFmono : (j j' : Nat) -> LeN j j' -> LeF (FF (XT j)) (FF (XT j'))
  FFmono j j' lj =
    precFun-mono p g h mg mh (XT j) (XT j') (XTlen j) (XTlen j') (XT-mono j j' lj)

  ------------------------------------------------------------------
  -- THE POINT: coordinate 0 infinite, the parameters at `L`
  ------------------------------------------------------------------

  A : Tup
  A = dtup (suc p) (ptD zero L)

  Alen : Eq (length A) (suc p)
  Alen = dtup-len (suc p) (ptD zero L)

  getA-0 : Eq (get zero A) inf
  getA-0 = Eq-trans (dtup-nth (suc p) (ptD zero L) zero tt) (ptD-I zero L)

  getA-ne : (c : Nat) -> LeN (suc c) (suc p) -> Not (Eq c zero)
          -> Eq (get c A) (bot (L c))
  getA-ne c lc nc =
    Eq-trans (dtup-nth (suc p) (ptD zero L) c lc) (ptD-ne zero L c nc)

  getA-inf : (c : Nat) -> Eq (get c A) inf -> Eq c zero
  getA-inf c e = route (LeN-dec (suc c) (suc p))
    where
      route : Dec (LeN (suc c) (suc p)) -> Eq c zero
      route (no nc) =
        Empty-elim
          (bot-not-inf zero
            (Eq-trans (Eq-sym (dtup-out (suc p) (ptD zero L) c nc)) e))
      route (yes lc) = route2 (EqNat-dec c zero)
        where
          route2 : Dec (Eq c zero) -> Eq c zero
          route2 (yes ec) = ec
          route2 (no  nc) =
            Empty-elim
              (bot-not-inf (L c) (Eq-trans (Eq-sym (getA-ne c lc nc)) e))

  ------------------------------------------------------------------
  -- a finite approximant below it
  ------------------------------------------------------------------

  module Approx (A0 : FTup) (bel : LeTup (embedTup A0) A) where

    A0len : Eq (length A0) (suc p)
    A0len =
      Eq-trans (Eq-sym (embedTup-len A0))
        (Eq-trans (LeTup-len (embedTup A0) A bel) Alen)

    A0at : (c : Nat) -> LeD (embed (getF c A0)) (get c A)
    A0at c =
      Eq-transport (\ z -> LeD z (get c A)) (get-embedTup c A0)
        (LeTup-get c {embedTup A0} {A} bel)

    k0 : Nat
    k0 = hgt (getF zero A0)

    A0-0 : Eq (getF zero A0) (fbot k0)
    A0-0 =
      below-inf (getF zero A0)
        (Eq-transport (\ z -> LeD (embed (getF zero A0)) z) getA-0 (A0at zero))

    A0-ne : (c : Nat) -> LeN (suc c) (suc p) -> Not (Eq c zero)
          -> Eq (getF c A0) (fbot (hgt (getF c A0)))
    A0-ne c lc nc =
      below-bot (getF c A0) (L c)
        (Eq-transport (\ z -> LeD (embed (getF c A0)) z)
          (getA-ne c lc nc) (A0at c))

    A0-le : (c : Nat) -> LeN (suc c) (suc p) -> Not (Eq c zero)
          -> LeN (hgt (getF c A0)) (L c)
    A0-le c lc nc =
      below-bot-le (getF c A0) (L c)
        (Eq-transport (\ z -> LeD (embed (getF c A0)) z)
          (getA-ne c lc nc) (A0at c))

    leX : (j : Nat) -> LeN k0 j -> LeX A0 (XT j)
    leX j lt c = route (LeN-dec (suc c) (suc p))
      where
        route : Dec (LeN (suc c) (suc p)) -> LeF (getF c A0) (getF c (XT j))
        route (no nc) =
          Eq-transport (\ z -> LeF z (getF c (XT j)))
            (Eq-sym
              (nth-out (fbot zero) c A0
                (\ l -> nc (Eq-transport (\ z -> LeN (suc c) z) A0len l))))
            (Eq-transport (\ z -> LeF (fbot zero) z)
              (Eq-sym (outXT c nc)) tt)
          where
            outXT : (d : Nat) -> Not (LeN (suc d) (suc p))
                  -> Eq (getF d (XT j)) (fbot zero)
            outXT zero    nd = Empty-elim (nd tt)
            outXT (suc i) nd =
              tup-out p (\ e -> fbot (L (suc e))) i nd
        route (yes lc) = route2 (EqNat-dec c zero)
          where
            route2 : Dec (Eq c zero) -> LeF (getF c A0) (getF c (XT j))
            route2 (yes ec) =
              Eq-transport (\ z -> LeF (getF z A0) (getF z (XT j))) (Eq-sym ec)
                (Eq-transport (\ z -> LeF z (getF zero (XT j))) (Eq-sym A0-0) lt)
            route2 (no nc) =
              Eq-transport (\ z -> LeF z (getF c (XT j)))
                (Eq-sym (A0-ne c lc nc))
                (Eq-transport (\ z -> LeF (fbot (hgt (getF c A0))) z)
                  (Eq-sym (parAt c lc nc)) (A0-le c lc nc))
              where
                parAt : (d : Nat) -> LeN (suc d) (suc p) -> Not (Eq d zero)
                      -> Eq (getF d (XT j)) (fbot (L d))
                parAt zero    ld nd = Empty-elim (nd refl)
                parAt (suc i) ld nd = XT-par j i ld

    lenXA : (j : Nat) -> Eq (length (XT j)) (length A0)
    lenXA j = Eq-trans (XTlen j) (Eq-sym A0len)

    leFT : (j : Nat) -> LeN k0 j -> LeFTup A0 (XT j)
    leFT j lt = LeX-LeFTup A0 (XT j) (Eq-sym (lenXA j)) (leX j lt)

    leFT-del : (i : Nat) -> LeN (suc i) (suc p) -> (j : Nat) -> LeN k0 j
             -> LeFTup (del i A0) (del i (XT j))
    leFT-del i li j lt =
      LeX-LeFTup (del i A0) (del i (XT j)) dlen (LeX-del i A0 (XT j) (leX j lt))
      where
        dlen : Eq (length (del i A0)) (length (del i (XT j)))
        dlen =
          suc-inj
            (Eq-trans
              (del-len i A0
                (Eq-transport (\ z -> LeN (suc i) z) (Eq-sym A0len) li))
              (Eq-trans A0len
                (Eq-trans (Eq-sym (XTlen j))
                  (Eq-sym
                    (del-len i (XT j)
                      (Eq-transport (\ z -> LeN (suc i) z)
                        (Eq-sym (XTlen j)) li))))))

  ------------------------------------------------------------------
  -- incompleteness at arbitrarily large `j` IS incompleteness
  ------------------------------------------------------------------

  notCpl-down : (j j' : Nat) -> LeN j j' -> Not (IsCpl (FF (XT j')))
              -> Not (IsCpl (FF (XT j)))
  notCpl-down j j' le nc ic =
    nc (Eq-transport (\ z -> IsCpl z)
         (cpl-max (FF (XT j)) (FF (XT j')) (FFmono j j' le) ic) ic)

  never-of : (t0 : Nat) -> ((t : Nat) -> LeN t0 t -> Not (IsCpl (FF (XT t))))
           -> (j : Nat) -> Not (IsCpl (FF (XT j)))
  never-of t0 h j =
    notCpl-down j (plus t0 j) (plus-ge-r t0 j) (h (plus t0 j) (plus-ge-l t0 j))

  ------------------------------------------------------------------
  -- THE DECISION
  ------------------------------------------------------------------

  decide : UO FF A
         -> Or (Sigma Nat (\ j0 -> IsCpl (FF (XT j0))))
               ((j : Nat) -> Not (IsCpl (FF (XT j))))
  ------------------------------------------------------------------
  -- Case 1: a numeral above a finite approximant
  ------------------------------------------------------------------
  decide (uo1 (mkSigma A0 (mkSigma bel (mkSigma m hyp)))) =
    inl (mkSigma AP.k0 isc)
    where
      module AP = Approx A0 bel

      isc : IsCpl (FF (XT AP.k0))
      isc =
        Eq-transport (\ z -> IsCpl z)
          (Eq-sym (hyp (XT AP.k0) (AP.leFT AP.k0 (LeN-refl AP.k0)))) tt
  ------------------------------------------------------------------
  -- Case 2: pinned at a FINITE incomplete coordinate, so not 0
  ------------------------------------------------------------------
  decide (uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma li
           (mkSigma incf (mkSigma eqA hyp)))))))) =
    inr (never-of AP.k0 (\ t lt -> fbot-notCpl (FF (XT t)) m (hit t lt)))
    where
      module AP = Approx A0 bel

      li' : LeN (suc i) (suc p)
      li' = Eq-transport (\ z -> LeN (suc i) z) AP.A0len li

      ni : Not (Eq i zero)
      ni ei =
        Eq-transport (\ z -> IncompleteFinite z)
          (Eq-trans (Eq-cong (\ z -> get z A) ei) getA-0) incf

      A0i : Eq (getF i A0) (fbot (L i))
      A0i = embed-bot (getF i A0) (L i) (Eq-trans eqA (getA-ne i li' ni))

      same : (t : Nat) -> Eq (getF i (XT t)) (getF i A0)
      same t = Eq-trans (parAt i li' ni) (Eq-sym A0i)
        where
          parAt : (d : Nat) -> LeN (suc d) (suc p) -> Not (Eq d zero)
                -> Eq (getF d (XT t)) (fbot (L d))
          parAt zero    ld nd = Empty-elim (nd refl)
          parAt (suc c) ld nd = XT-par t c ld

      hit : (t : Nat) -> LeN AP.k0 t -> Eq (FF (XT t)) (fbot m)
      hit t lt = hyp (XT t) (AP.lenXA t) (same t) (AP.leFT-del i li' t lt)
  ------------------------------------------------------------------
  -- Case 3: at the infinite coordinate, which must be 0
  ------------------------------------------------------------------
  decide (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf (mkSigma k
           (mkSigma eA0 (mkSigma phi (mkSigma pk hyp))))))))) =
    inr
      (never-of AP.k0
        (\ t lt -> fbot-notCpl (FF (XT t)) (phi t) (hit t lt)))
    where
      module AP = Approx A0 bel

      ei : Eq i zero
      ei = getA-inf i einf

      li' : LeN (suc i) (suc p)
      li' = Eq-transport (\ z -> LeN (suc z) (suc p)) (Eq-sym ei) tt

      kk : Eq k AP.k0
      kk =
        Eq-cong hgt
          (Eq-trans (Eq-sym eA0)
            (Eq-trans (Eq-cong (\ z -> getF z A0) ei) AP.A0-0))

      atI : (t : Nat) -> Eq (getF i (XT t)) (fbot t)
      atI t =
        Eq-transport (\ z -> Eq (getF z (XT t)) (fbot t)) (Eq-sym ei) (XT-0 t)

      ge-k : (t : Nat) -> LeN AP.k0 t -> LeN k t
      ge-k t lt = Eq-transport (\ z -> LeN z t) (Eq-sym kk) lt

      hit : (t : Nat) -> LeN AP.k0 t -> Eq (FF (XT t)) (fbot (phi t))
      hit t lt =
        hyp (XT t) t (AP.lenXA t) (ge-k t lt) (atI t) (AP.leFT-del i li' t lt)

------------------------------------------------------------------------
-- ... AND THE ANSWER, FOR THE RECURSION'S OWN CHAIN
------------------------------------------------------------------------

Vd-tot-or-never : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
                -> Den (suc (suc p)) Th h
                -> MonoF p g -> MonoF (suc (suc p)) h
                -> ((A : Tup) -> Eq (length A) (suc p) -> UO (precFun g h) A)
                -> (L : Nat -> Nat)
                -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
                      ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
Vd-tot-or-never p Th g h dh mg mh uo L =
  route (DC.decide p g h mg mh L (uo (DC.A p g h mg mh L) (DC.Alen p g h mg mh L)))
  where
    route : Or (Sigma Nat (\ j0 -> IsCpl (precFun g h (avP p L j0))))
               ((j : Nat) -> Not (IsCpl (precFun g h (avP p L j))))
          -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
                ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
    route (inl (mkSigma j0 ic)) =
      inl (mkSigma j0
            (Eq-transport (\ z -> IsCpl z)
              (Eq-sym (Vd-den p Th g h dh L j0)) ic))
    route (inr nev) =
      inr (\ j ic ->
             nev j
               (Eq-transport (\ z -> IsCpl z) (Vd-den p Th g h dh L j) ic))

------------------------------------------------------------------------
-- THE DEPTH DIRECTION, UNCONDITIONALLY
--
-- `TrPrecIv.Qd-stab-full` took the decision as a hypothesis; `decide`
-- supplies it.  So for the trace of an actual PR term -- where `Den`,
-- `MonoF` and Proposition 1 are all available -- the fold `Qd L .` is
-- eventually constant, with no hypothesis left.
------------------------------------------------------------------------

Vd-mono : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
        -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
        -> (L : Nat -> Nat) (j j' : Nat) -> LeN j j'
        -> LeF (R.Vd p Th L j) (R.Vd p Th L j')
Vd-mono p Th g h dh mg mh L j j' lj =
  Eq-transport (\ z -> LeF z (R.Vd p Th L j'))
    (Eq-sym (Vd-den p Th g h dh L j))
    (Eq-transport (\ z -> LeF (precFun g h (avP p L j)) z)
      (Eq-sym (Vd-den p Th g h dh L j'))
      (precFun-mono p g h mg mh (avP p L j) (avP p L j')
        (avP-len p L j) (avP-len p L j')
        (DC.XT-mono p g h mg mh L j j' lj)))

Qd-stab-of : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
           -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
           -> Den (suc (suc p)) Th h
           -> MonoF p g -> MonoF (suc (suc p)) h
           -> ((A : Tup) -> Eq (length A) (suc p) -> UO (precFun g h) A)
           -> (L : Nat -> Nat)
           -> Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
                -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J)))
Qd-stab-of p Th g h mth m1th dh mg mh uo L =
  Qd-stab-full p Th mth (mp1-mpT (suc (suc p)) Th mth m1th) L
    (Vd-mono p Th g h dh mg mh L)
    (Vd-tot-or-never p Th g h dh mg mh uo L)

------------------------------------------------------------------------
-- MONOTONICITY IN THE PARAMETER LEVELS
--
-- The terminal case of the parameter fuel (`TrPrecIv.Qd-par-const`)
-- needs its hypothesis -- the step term's replay is past `Nh` at some
-- depth -- to SURVIVE A BUMP.  It does, because raising a parameter only
-- raises the whole chain: the recursive value is monotone in `L` (by
-- `Vd-den` and `precFun-mono`), hence so is `avT`, hence so is the replay
-- depth (`nOf-mono`).
------------------------------------------------------------------------

avP-mono-L : (p : Nat) (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j : Nat) -> LeX (avP p L j) (avP p L' j)
avP-mono-L p L L' lp j =
  LeX-cons (fbot j) (fbot j) (parTup p L) (parTup p L') (LeN-refl j)
    (tup-le p (\ i -> fbot (L (suc i))) (\ i -> fbot (L' (suc i)))
      (\ i li -> lp i))

Vd-mono-L : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
          -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
          -> (L L' : Nat -> Nat)
          -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
          -> (j : Nat) -> LeF (R.Vd p Th L j) (R.Vd p Th L' j)
Vd-mono-L p Th g h dh mg mh L L' lp j =
  Eq-transport (\ z -> LeF z (R.Vd p Th L' j))
    (Eq-sym (Vd-den p Th g h dh L j))
    (Eq-transport (\ z -> LeF (precFun g h (avP p L j)) z)
      (Eq-sym (Vd-den p Th g h dh L' j))
      (precFun-mono p g h mg mh (avP p L j) (avP p L' j)
        (avP-len p L j) (avP-len p L' j) (avP-mono-L p L L' lp j)))

avT-mono-L : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
           -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
           -> (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j : Nat) -> LeX (R.avT p Th L j) (R.avT p Th L' j)
avT-mono-L p Th g h dh mg mh L L' lp j =
  PZ-avT-mono-L p Th L L' (Vd-mono-L p Th g h dh mg mh L L' lp) lp j

------------------------------------------------------------------------
-- THE PHASE CHANGE HAPPENS AT MOST ONCE
--
-- A complete value is MAXIMAL, so as soon as the recursive value is a
-- numeral anywhere it is the SAME numeral at every greater depth AND at
-- every greater parameter setting.  Hence the continuation
-- `conth 1 _ w` that `blockOn` descends into -- and with it its own
-- threshold `Nh'` -- is fixed once and for all, and the walk passes from
-- the no-descent regime to the descent regime at most once.
------------------------------------------------------------------------

Vd-cpl-fixed : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
             -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
             -> (L L' : Nat -> Nat)
             -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
             -> (j j' : Nat) -> LeN j j'
             -> IsCpl (R.Vd p Th L j)
             -> Eq (R.Vd p Th L j) (R.Vd p Th L' j')
Vd-cpl-fixed p Th g h dh mg mh L L' lp j j' lj ic =
  cpl-max (R.Vd p Th L j) (R.Vd p Th L' j') le ic
  where
    le : LeF (R.Vd p Th L j) (R.Vd p Th L' j')
    le =
      LeF-trans {R.Vd p Th L j} {R.Vd p Th L j'} {R.Vd p Th L' j'}
        (Vd-mono p Th g h dh mg mh L j j' lj)
        (Vd-mono-L p Th g h dh mg mh L L' lp j')

-- ... so the descent point is fixed too
Vd-cpl-up : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
          -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
          -> (L L' : Nat -> Nat)
          -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
          -> (j j' : Nat) -> LeN j j'
          -> IsCpl (R.Vd p Th L j) -> IsCpl (R.Vd p Th L' j')
Vd-cpl-up p Th g h dh mg mh L L' lp j j' lj ic =
  Eq-transport (\ z -> IsCpl z)
    (Vd-cpl-fixed p Th g h dh mg mh L L' lp j j' lj ic) ic
