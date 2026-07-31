{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecPar
--
-- THE RECURSION'S INDEX: THE PARAMETER DIRECTION, BOTH REGIMES.
--
-- `TrPrecIv.LOOP` settled the parameter direction under the hypothesis
-- that the recursive value is NEVER a numeral -- the regime in which
-- `blockOn Th (avT L j)` never descends.  This file drops that
-- hypothesis.
--
-- THE ONE NEW CASE.  At the depth `j` that `PZ.Qd-source` names, `h`
-- demands `f`'s parameter `i0`.  Either
--
--   (A) the coordinate `h` is stuck on is INCOMPLETE -- then the demand
--       is the top-level one, `ivh (NG L j) = 2+i0`, and the analysis is
--       `TrPrecIv.LOOP`'s: past `Th`'s own threshold the demand is fixed
--       for ever (`cg-past`), below it the parameter's level is small
--       and the bump costs one unit of `BUD.Mof`;
--
--   (B) or it is COMPLETE -- and then by `PZ.avT-incpl` the only
--       coordinate that can be complete is 1, the recursive value.  So
--       `blockOn` DESCENDS, into
--
--           T' = conth 1 _ w      at      parV p L j
--
--       and the demand `2+i0` of `f` is the demand `1+i0` of `T'`
--       (`shiftOr 1`).  The same dichotomy then applies ONE LEVEL DOWN,
--       at `T'`'s own threshold.
--
-- WHY (B) IS NOT A REGRESS.  Three facts, all already available:
--
--   * `parV` has NO complete coordinate (`parV-incpl`), so `T'` cannot
--     descend again -- the case analysis is two levels deep, full stop;
--
--   * a descent FREEZES the top level for ever, in BOTH directions:
--     the replay is stuck on coordinate 1, whose value is complete hence
--     maximal, so `nOf-freeze` pins `NG` at every greater depth AND at
--     every greater parameter setting.  Hence `cg`, the continuation
--     `T'`, and `ovh (NG)` are all fixed;
--
--   * `T'` itself is fixed once and for all: a complete recursive value
--     is maximal, so two stages at which it is complete give the SAME
--     numeral (`w-fixed`, by `cpl-max` at the pointwise max).  So the
--     walk passes from regime (A) to regime (B) AT MOST ONCE, and the
--     budget for (B) -- `T'`'s threshold -- is a single number.
--
-- Hence the loop runs with bound `Q0` until it first meets a descent,
-- and from there with bound `maxN Q0 Q1`.  This is min1.pdf's
-- "propriete remarquable" of the associated sequence, read on the trace:
-- growing a parameter does not RECOMPUTE the chain, it moves along the
-- same sequence -- `blockOn-sat`/`nOf-freeze` -- so a demand that has
-- passed its threshold never moves again.
--
-- `ov` GOING TOTAL is handled uniformly at both levels by `node-split`:
-- the threshold is raised past the stage at which `ov` is complete, and
-- there the demand is `inl tt`, which CONTRADICTS the parameter demand
-- we started from.  So `LOOP`'s `nevo` hypothesis is gone too.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecPar where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using
  (FEl ; fbot ; fcpl ; LeF ; LeF-refl ; LeF-trans)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-suc-r ; plus-mono ; le-nlt-eq ; LeN-suc-not)
open import OBSTINATION.MP1 using (le-add ; plus-ge-l)
open import OBSTINATION.CapDet using (nle-lt)
open import OBSTINATION.ReplayLv using
  (nOf ; nOf-mono ; nOf-freeze ; sumTo-mono)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; LeX ; LeX-hts ; MonoTr ; cpl-max)
open import OBSTINATION.TrCompNG using (module NGf ; IsCpl-dec)
open import OBSTINATION.TrCompSel using (ovTot-or-never)
open import OBSTINATION.TrMP1 using (MP1T)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TrScan using (inr-inj ; LeN-uniq)
open import OBSTINATION.TrMono using (lev-mono)
open import OBSTINATION.TrPrecFrz using (tup-le)
open import OBSTINATION.TrPrec using (module R ; module P ; qsel)
open import OBSTINATION.TrPrecIv using
  (module PZ ; module BUD ; parV ; pvf ; parV-incpl ; parV-mono ;
   delEq ; Qd-stab-full ; PZ-avT-mono-L ; qsel-indep ; Dm-not-one ;
   parV-fix ; parV-grow ; post-stab ; sumTo-cong)

------------------------------------------------------------------------
-- THE OUTPUT SEQUENCE OF A TRACE IS MONOTONE IN THE REPLAY DEPTH
------------------------------------------------------------------------

ovMono : (a : Nat) (T : Tr a) -> MonoTr a T
       -> (m n : Nat) -> LeN m n -> LeF (ovOf T m) (ovOf T n)
ovMono a       (stop v)              mt m n le = LeF-refl v
ovMono (suc a) (node iv ivr ov cont) mt m n le = fst mt m n le

------------------------------------------------------------------------
-- ONE THRESHOLD THAT SETTLES BOTH HALVES OF A NODE
--
-- Past `Q` the index is the eventual one; and `ov` is EITHER never
-- complete, or complete throughout.  In the second case the demand past
-- `Q` is `inl tt`, so any hypothesis of the form "the demand past `Q` is
-- a coordinate" is contradictory -- which is how the `nevo` hypothesis
-- of `TrPrecIv.LOOP` disappears.
------------------------------------------------------------------------

node-split : (a : Nat) (iv : Nat -> Nat)
             (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a))
             (ov : Nat -> FEl)
             (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
           -> MonoTr (suc a) (node iv ivr ov cont)
           -> MP1T (suc a) (node iv ivr ov cont)
           -> Sigma Nat (\ Q ->
                Pair ((n : Nat) -> LeN Q n -> Eq (iv n) (iv Q))
                     (Or ((n : Nat) -> Not (IsCpl (ov n)))
                         ((n : Nat) -> LeN Q n -> IsCpl (ov n))))
node-split a iv ivr ov cont mt m1 =
  route (ovTot-or-never (suc a) (node iv ivr ov cont) m1)
  where
    Nh : Nat
    Nh = fst (fst m1)

    stab : (n : Nat) -> LeN Nh n -> Eq (iv n) (iv Nh)
    stab = snd (fst m1)

    Res : Set
    Res =
      Sigma Nat (\ Q ->
        Pair ((n : Nat) -> LeN Q n -> Eq (iv n) (iv Q))
             (Or ((n : Nat) -> Not (IsCpl (ov n)))
                 ((n : Nat) -> LeN Q n -> IsCpl (ov n))))

    route : Or (Sigma Nat (\ n0 -> IsCpl (ov n0)))
               ((m : Nat) -> Not (IsCpl (ov m)))
          -> Res
    route (inr nev) = mkSigma Nh (mkSigma stab (inl nev))
    route (inl (mkSigma n0 ic)) = mkSigma Q (mkSigma stabQ (inr tot))
      where
        Q : Nat
        Q = maxN Nh n0

        leNhQ : LeN Nh Q
        leNhQ = maxN-le-l Nh n0

        len0Q : LeN n0 Q
        len0Q = maxN-le-r Nh n0

        stabQ : (n : Nat) -> LeN Q n -> Eq (iv n) (iv Q)
        stabQ n le =
          Eq-trans (stab n (LeN-trans {Nh} {Q} {n} leNhQ le))
            (Eq-sym (stab Q leNhQ))

        tot : (n : Nat) -> LeN Q n -> IsCpl (ov n)
        tot n le =
          Eq-transport (\ z -> IsCpl z)
            (cpl-max (ov n0) (ov n)
              (fst mt n0 n (LeN-trans {n0} {Q} {n} len0Q le)) ic)
            ic

------------------------------------------------------------------------
-- `shiftOr 1` IS INJECTIVE WHERE IT MATTERS
--
-- A demand `2+i0` of `f` that came through a descent at coordinate 1 is
-- the demand `1+i0` of the descended trace.  (`su 1 0 = 0`, so a `2+i0`
-- can never come from coordinate 0 of the sub-trace: that is `f`'s own
-- recursion argument, not a parameter.)
------------------------------------------------------------------------

shiftOr-inv : (r : Or Top Nat) (i0 : Nat)
            -> Eq (shiftOr (suc zero) r) (inr (suc (suc i0)))
            -> Eq r (inr (suc i0))
shiftOr-inv (inl tt)      i0 ()
shiftOr-inv (inr zero)    i0 ()
shiftOr-inv (inr (suc c)) i0 e =
  Eq-cong (\ z -> inr (suc z))
    (suc-inj (suc-inj (inr-inj (suc (suc c)) (suc (suc i0)) e)))

shiftOr1-back : (i0 : Nat)
              -> Eq (shiftOr (suc zero) (inr (suc i0))) (inr (suc (suc i0)))
shiftOr1-back i0 = refl

------------------------------------------------------------------------
-- THE PARAMETER FAMILY IS MONOTONE IN THE PARAMETER LEVELS TOO
------------------------------------------------------------------------

parV-monoL : (p : Nat) (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j : Nat) -> LeX (parV p L j) (parV p L' j)
parV-monoL p L L' lp j = tup-le (suc p) (pvf L j) (pvf L' j) go
  where
    go : (c : Nat) -> LeN (suc c) (suc p) -> LeF (pvf L j c) (pvf L' j c)
    go zero    lc = LeN-refl j
    go (suc i) lc = lp i

parV-mono2 : (p : Nat) (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j j' : Nat) -> LeN j j'
           -> LeX (parV p L j) (parV p L' j')
parV-mono2 p L L' lp j j' lj c =
  LeF-trans
    {nth (fbot zero) c (parV p L j)}
    {nth (fbot zero) c (parV p L j')}
    {nth (fbot zero) c (parV p L' j')}
    (parV-mono p L j j' lj c) (parV-monoL p L L' lp j' c)

------------------------------------------------------------------------
-- THE PARAMETER DIRECTION
------------------------------------------------------------------------

module PAR (p : Nat)
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
           (vdL : (L L' : Nat -> Nat)
                -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
                -> (j : Nat) -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                                    (R.Vd p (node ivh ivhr ovh conth) L' j))
           (dec : (L : Nat -> Nat)
                -> Or (Sigma Nat (\ j0 ->
                        IsCpl (R.Vd p (node ivh ivhr ovh conth) L j0)))
                      ((j : Nat) ->
                        Not (IsCpl (R.Vd p (node ivh ivhr ovh conth) L j))))
           where

  Th : Tr (suc (suc p))
  Th = node ivh ivhr ovh conth

  open P p Th

  ------------------------------------------------------------------
  -- the chain, and its two monotonicities
  ------------------------------------------------------------------

  vmL : (L L' : Nat -> Nat) -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
      -> (j : Nat) -> LeX (R.avT p Th L j) (R.avT p Th L' j)
  vmL L L' lp = PZ-avT-mono-L p Th L L' (vdL L L' lp) lp

  module NN (L : Nat -> Nat) =
    NGf (suc p) ivh ivhr ovh conth (R.avT p Th L)
        (PZ.avT-mono p Th L (vmj L)) mth

  NGat : (Nat -> Nat) -> Nat -> Nat
  NGat L j = NN.NG L j

  NG-monoL : (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j : Nat) -> LeN (NGat L j) (NGat L' j)
  NG-monoL L L' lp j =
    nOf-mono (suc (suc p)) ivh ivhr
      (hts (R.avT p Th L j)) (hts (R.avT p Th L' j))
      (LeX-hts (R.avT p Th L j) (R.avT p Th L' j) (vmL L L' lp j))

  NG-mono2 : (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j j' : Nat) -> LeN j j' -> LeN (NGat L j) (NGat L' j')
  NG-mono2 L L' lp j j' lj =
    LeN-trans {NGat L j} {NGat L j'} {NGat L' j'}
      (NN.NG-mono L j j' lj) (NG-monoL L L' lp j')

  ------------------------------------------------------------------
  -- the top-level threshold
  ------------------------------------------------------------------

  Q0d : Sigma Nat (\ Q ->
          Pair ((n : Nat) -> LeN Q n -> Eq (ivh n) (ivh Q))
               (Or ((n : Nat) -> Not (IsCpl (ovh n)))
                   ((n : Nat) -> LeN Q n -> IsCpl (ovh n))))
  Q0d = node-split (suc p) ivh ivhr ovh conth mth m1th

  Q0 : Nat
  Q0 = fst Q0d

  q0stab : (n : Nat) -> LeN Q0 n -> Eq (ivh n) (ivh Q0)
  q0stab = fst (snd Q0d)

  q0ov : Or ((n : Nat) -> Not (IsCpl (ovh n)))
            ((n : Nat) -> LeN Q0 n -> IsCpl (ovh n))
  q0ov = snd (snd Q0d)

  ------------------------------------------------------------------
  -- a demand that is a COORDINATE forces `ovh` to be incomplete there
  ------------------------------------------------------------------

  nc-of : (L : Nat -> Nat) (j c : Nat)
        -> Eq (PZ.Dmj p Th L j) (inr c) -> Not (IsCpl (ovh (NGat L j)))
  nc-of L j c e ic = bad (Eq-trans (Eq-sym (NN.blk-inl L j ic)) e)
    where
      bad : Not (Eq {Or Top Nat} (inl tt) (inr c))
      bad ()

  ------------------------------------------------------------------
  -- ONLY THE RECURSIVE VALUE CAN BE COMPLETE
  ------------------------------------------------------------------

  cg-one : (L : Nat -> Nat) (j : Nat) -> IsCpl (NN.at L j)
         -> Eq (NN.cg L j) (suc zero)
  cg-one L j ic = route (EqNat-dec (NN.cg L j) (suc zero))
    where
      route : Dec (Eq (NN.cg L j) (suc zero)) -> Eq (NN.cg L j) (suc zero)
      route (yes e) = e
      route (no ne) = Empty-elim (PZ.avT-incpl p Th L j (NN.cg L j) ne ic)

  atE : (L : Nat -> Nat) (j : Nat) -> Eq (NN.cg L j) (suc zero)
      -> Eq (NN.at L j) (R.Vd p Th L j)
  atE L j ec =
    Eq-trans
      (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) ec)
      (tup-nth (suc (suc p)) (R.avf p Th L j) (suc zero) tt)

  at-Vd : (L : Nat -> Nat) (j : Nat) -> IsCpl (NN.at L j)
        -> IsCpl (R.Vd p Th L j)
  at-Vd L j ic = Eq-transport (\ z -> IsCpl z) (atE L j (cg-one L j ic)) ic

  Vd-at : (L : Nat -> Nat) (j : Nat) -> Eq (NN.cg L j) (suc zero)
        -> IsCpl (R.Vd p Th L j) -> IsCpl (NN.at L j)
  Vd-at L j ec ic = Eq-transport (\ z -> IsCpl z) (Eq-sym (atE L j ec)) ic

  ------------------------------------------------------------------
  -- THE DESCENDED TRACE
  ------------------------------------------------------------------

  lc1 : LeN (suc (suc zero)) (suc (suc p))
  lc1 = tt

  Tw : Nat -> Tr (suc p)
  Tw w = conth (suc zero) lc1 w

  conth-cong : (c c' : Nat) -> Eq c c'
             -> (lc : LeN (suc c) (suc (suc p)))
             -> (lc' : LeN (suc c') (suc (suc p)))
             -> (v v' : Nat) -> Eq v v'
             -> Eq (conth c lc v) (conth c' lc' v')
  conth-cong c c' refl lc lc' v v' refl =
    Eq-cong (\ z -> conth c z v) (LeN-uniq (suc c) (suc (suc p)) lc lc')

  htsE1 : (L : Nat -> Nat) (j : Nat) -> Eq (NN.cg L j) (suc zero)
        -> Eq (hts (R.avT p Th L j) (NN.cg L j)) (hgt (R.Vd p Th L j))
  htsE1 L j ec = Eq-cong hgt (atE L j ec)

  T'eq : (L : Nat -> Nat) (j : Nat) (ic : IsCpl (NN.at L j))
       -> Eq (conth (NN.cg L j) (ivhr (NGat L j))
                (hts (R.avT p Th L j) (NN.cg L j)))
             (Tw (hgt (R.Vd p Th L j)))
  T'eq L j ic =
    conth-cong (NN.cg L j) (suc zero) (cg-one L j ic)
      (ivhr (NGat L j)) lc1
      (hts (R.avT p Th L j) (NN.cg L j)) (hgt (R.Vd p Th L j))
      (htsE1 L j (cg-one L j ic))

  descEq : (L : Nat -> Nat) (j : Nat) (ic : IsCpl (NN.at L j))
         -> Not (IsCpl (ovh (NGat L j)))
         -> Eq (PZ.Dmj p Th L j)
               (shiftOr (suc zero)
                 (blockOn (suc p) (Tw (hgt (R.Vd p Th L j))) (parV p L j)))
  descEq L j ic nc =
    Eq-trans (NN.blk-descend L j nc ic) (Eq-trans st1 (Eq-trans st2 st3))
    where
      st1 : Eq (NN.BLK L j)
               (shiftOr (suc zero)
                 (blockOn (suc p)
                   (conth (NN.cg L j) (ivhr (NGat L j))
                     (hts (R.avT p Th L j) (NN.cg L j)))
                   (del (suc zero) (R.avT p Th L j))))
      st1 =
        Eq-cong
          (\ z -> shiftOr z
                    (blockOn (suc p)
                      (conth (NN.cg L j) (ivhr (NGat L j))
                        (hts (R.avT p Th L j) (NN.cg L j)))
                      (del z (R.avT p Th L j))))
          (cg-one L j ic)

      st2 : Eq (shiftOr (suc zero)
                 (blockOn (suc p)
                   (conth (NN.cg L j) (ivhr (NGat L j))
                     (hts (R.avT p Th L j) (NN.cg L j)))
                   (del (suc zero) (R.avT p Th L j))))
               (shiftOr (suc zero)
                 (blockOn (suc p) (Tw (hgt (R.Vd p Th L j)))
                   (del (suc zero) (R.avT p Th L j))))
      st2 =
        Eq-cong
          (\ T -> shiftOr (suc zero)
                    (blockOn (suc p) T (del (suc zero) (R.avT p Th L j))))
          (T'eq L j ic)

      st3 : Eq (shiftOr (suc zero)
                 (blockOn (suc p) (Tw (hgt (R.Vd p Th L j)))
                   (del (suc zero) (R.avT p Th L j))))
               (shiftOr (suc zero)
                 (blockOn (suc p) (Tw (hgt (R.Vd p Th L j))) (parV p L j)))
      st3 =
        Eq-cong
          (\ Y -> shiftOr (suc zero)
                    (blockOn (suc p) (Tw (hgt (R.Vd p Th L j))) Y))
          (delEq p Th L j)

  ------------------------------------------------------------------
  -- A COMPLETE RECURSIVE VALUE IS THE SAME NUMERAL EVERYWHERE ABOVE
  ------------------------------------------------------------------

  Vd-le2 : (L L' : Nat -> Nat)
         -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
         -> (j j' : Nat) -> LeN j j'
         -> LeF (R.Vd p Th L j) (R.Vd p Th L' j')
  Vd-le2 L L' lp j j' lj =
    LeF-trans {R.Vd p Th L j} {R.Vd p Th L j'} {R.Vd p Th L' j'}
      (vmj L j j' lj) (vdL L L' lp j')

  Vd-up : (L L' : Nat -> Nat)
        -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
        -> (j j' : Nat) -> LeN j j'
        -> IsCpl (R.Vd p Th L j) -> Eq (R.Vd p Th L j) (R.Vd p Th L' j')
  Vd-up L L' lp j j' lj ic =
    cpl-max (R.Vd p Th L j) (R.Vd p Th L' j') (Vd-le2 L L' lp j j' lj) ic

  -- ... and hence the SAME numeral at two INCOMPARABLE stages, as long
  -- as the parameter levels are comparable: compare both with the
  -- pointwise maximum of the depths.
  w-fixed : (L L' : Nat -> Nat)
          -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
          -> (j0 j : Nat)
          -> IsCpl (R.Vd p Th L j0) -> IsCpl (R.Vd p Th L' j)
          -> Eq (R.Vd p Th L' j) (R.Vd p Th L j0)
  w-fixed L L' lp j0 j ic0 ic = Eq-trans e2 (Eq-sym e1)
    where
      M : Nat
      M = maxN j0 j

      e1 : Eq (R.Vd p Th L j0) (R.Vd p Th L' M)
      e1 = Vd-up L L' lp j0 M (maxN-le-l j0 j) ic0

      e2 : Eq (R.Vd p Th L' j) (R.Vd p Th L' M)
      e2 =
        cpl-max (R.Vd p Th L' j) (R.Vd p Th L' M)
          (vmj L' j M (maxN-le-r j0 j)) ic

  ------------------------------------------------------------------
  -- WHAT A BUMP MUST DELIVER
  --
  -- "the demand `2+i0` is there at every later stage and every greater
  -- depth" -- which `PZ.Qd-indep-par` turns into "the index is `1+i0`
  -- for ever".
  ------------------------------------------------------------------

  Persist : (Nat -> Nat) -> Nat -> Nat -> Set
  Persist L j i0 =
    (L' : Nat -> Nat) -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
    -> (j' : Nat) -> LeN j j'
    -> Eq (PZ.Dmj p Th L' j') (inr (suc (suc i0)))

  avT-mono2 : (L L' : Nat -> Nat)
            -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
            -> (j j' : Nat) -> LeN j j'
            -> LeX (R.avT p Th L j) (R.avT p Th L' j')
  avT-mono2 L L' lp j j' lj c =
    LeF-trans
      {nth (fbot zero) c (R.avT p Th L j)}
      {nth (fbot zero) c (R.avT p Th L j')}
      {nth (fbot zero) c (R.avT p Th L' j')}
      (PZ.avT-mono p Th L (vmj L) j j' lj c) (vmL L L' lp j' c)

  stabAt : (B : Nat) -> LeN Q0 B
         -> (n : Nat) -> LeN B n -> Eq (ivh n) (ivh B)
  stabAt B le n ln =
    Eq-trans (q0stab n (LeN-trans {Q0} {B} {n} le ln)) (Eq-sym (q0stab B le))

  ------------------------------------------------------------------
  -- REGIME (A): NOTHING DESCENDS AT THE SOURCE DEPTH
  ------------------------------------------------------------------

  cgA : (L : Nat -> Nat) (j i0 : Nat)
      -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
      -> Not (IsCpl (NN.at L j))
      -> Eq (NN.cg L j) (suc (suc i0))
  cgA L j i0 eD na =
    inr-inj (NN.cg L j) (suc (suc i0))
      (Eq-trans (Eq-sym (NN.blk-fbot L j (nc-of L j (suc (suc i0)) eD) na)) eD)

  termA : (B : Nat) -> LeN Q0 B
        -> (L : Nat -> Nat) (j i0 : Nat)
        -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
        -> Not (IsCpl (NN.at L j))
        -> LeN B (NGat L j)
        -> Persist L j i0
  termA B leB L j i0 eD na past L' lp j' lj =
    Eq-trans (NN.blk-fbot L' j' nc' na') (Eq-cong inr cgE')
    where
      nc : Not (IsCpl (ovh (NGat L j)))
      nc = nc-of L j (suc (suc i0)) eD

      cgE : Eq (NN.cg L j) (suc (suc i0))
      cgE = cgA L j i0 eD na

      eiB : Eq (ivh B) (suc (suc i0))
      eiB = Eq-trans (Eq-sym (stabAt B leB (NGat L j) past)) cgE

      pastAt : LeN B (NGat L' j')
      pastAt =
        LeN-trans {B} {NGat L j} {NGat L' j'} past
          (NG-mono2 L L' lp j j' lj)

      cgE' : Eq (NN.cg L' j') (suc (suc i0))
      cgE' = Eq-trans (stabAt B leB (NGat L' j') pastAt) eiB

      na' : Not (IsCpl (NN.at L' j'))
      na' =
        Eq-transport
          (\ z -> Not (IsCpl (nth (fbot zero) z (R.avT p Th L' j'))))
          (Eq-sym cgE')
          (PZ.avT-incpl p Th L' j' (suc (suc i0)) (\ ()))

      nc' : Not (IsCpl (ovh (NGat L' j')))
      nc' = route q0ov
        where
          route : Or ((n : Nat) -> Not (IsCpl (ovh n)))
                     ((n : Nat) -> LeN Q0 n -> IsCpl (ovh n))
                -> Not (IsCpl (ovh (NGat L' j')))
          route (inl nev) = nev (NGat L' j')
          route (inr tot) =
            Empty-elim
              (nc (tot (NGat L j) (LeN-trans {Q0} {B} {NGat L j} leB past)))

  cheapA : (B : Nat)
         -> (L : Nat -> Nat) (j i0 : Nat)
         -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
         -> Not (IsCpl (NN.at L j))
         -> Not (LeN B (NGat L j))
         -> LeN (suc (L (suc i0))) B
  cheapA B L j i0 eD na nl =
    LeN-trans {suc (L (suc i0))} {suc (NGat L j)} {B} lt1
      (nle-lt B (NGat L j) nl)
    where
      cgE : Eq (NN.cg L j) (suc (suc i0))
      cgE = cgA L j i0 eD na

      li : LeN (suc (suc (suc i0))) (suc (suc p))
      li =
        Eq-transport (\ z -> LeN (suc z) (suc (suc p))) cgE (ivhr (NGat L j))

      htsE : Eq (hts (R.avT p Th L j) (NN.cg L j)) (L (suc i0))
      htsE =
        Eq-cong hgt
          (Eq-trans
            (Eq-cong (\ z -> nth (fbot zero) z (R.avT p Th L j)) cgE)
            (tup-nth (suc (suc p)) (R.avf p Th L j) (suc (suc i0)) li))

      lt1 : LeN (suc (L (suc i0))) (suc (NGat L j))
      lt1 =
        Eq-transport (\ z -> LeN z (NGat L j)) htsE (NN.NG-ge-hts L j)

  ------------------------------------------------------------------
  -- A DESCENT FREEZES THE TOP LEVEL IN BOTH DIRECTIONS
  ------------------------------------------------------------------

  NG-frz : (L L' : Nat -> Nat)
         -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
         -> (j j' : Nat) -> LeN j j' -> IsCpl (NN.at L j)
         -> Eq (NGat L' j') (NGat L j)
  NG-frz L L' lp j j' lj ic =
    nOf-freeze (suc (suc p)) ivh ivhr
      (hts (R.avT p Th L j)) (hts (R.avT p Th L' j')) le agree
    where
      le : (c : Nat) -> LeN (hts (R.avT p Th L j) c)
                           (hts (R.avT p Th L' j') c)
      le = LeX-hts (R.avT p Th L j) (R.avT p Th L' j')
             (avT-mono2 L L' lp j j' lj)

      agree : Eq (hts (R.avT p Th L' j') (NN.cg L j))
                 (hts (R.avT p Th L j) (NN.cg L j))
      agree =
        Eq-cong hgt
          (Eq-sym
            (cpl-max (nth (fbot zero) (NN.cg L j) (R.avT p Th L j))
                     (nth (fbot zero) (NN.cg L j) (R.avT p Th L' j'))
                     (avT-mono2 L L' lp j j' lj (NN.cg L j)) ic))

  ------------------------------------------------------------------
  -- REGIME (B): THE DESCENDED TRACE'S OWN DICHOTOMY
  --
  -- The descent goes into `Tw w`, which is FIXED (`w-fixed`), so its
  -- threshold `Q1` is a single number.  The family it runs along --
  -- `parV p L j` -- has no complete coordinate at all, so there is no
  -- third level: exactly the same two-way split closes it.
  ------------------------------------------------------------------

  module SUB (w : Nat)
             (iv1 : Nat -> Nat)
             (ivr1 : (n : Nat) -> LeN (suc (iv1 n)) (suc p))
             (ov1 : Nat -> FEl)
             (cont1 : (c : Nat) -> LeN (suc c) (suc p) -> (v : Nat) -> Tr p)
             (eTw : Eq (Tw w) (node iv1 ivr1 ov1 cont1))
             (mt1 : MonoTr (suc p) (node iv1 ivr1 ov1 cont1))
             (m11 : MP1T (suc p) (node iv1 ivr1 ov1 cont1))
             where

    T1 : Tr (suc p)
    T1 = node iv1 ivr1 ov1 cont1

    module MM (L : Nat -> Nat) =
      NGf p iv1 ivr1 ov1 cont1 (parV p L) (parV-mono p L) mt1

    NG1 : (Nat -> Nat) -> Nat -> Nat
    NG1 L j = MM.NG L j

    NG1-mono2 : (L L' : Nat -> Nat)
              -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
              -> (j j' : Nat) -> LeN j j' -> LeN (NG1 L j) (NG1 L' j')
    NG1-mono2 L L' lp j j' lj =
      nOf-mono (suc p) iv1 ivr1
        (hts (parV p L j)) (hts (parV p L' j'))
        (LeX-hts (parV p L j) (parV p L' j')
          (parV-mono2 p L L' lp j j' lj))

    Q1d : Sigma Nat (\ Q ->
            Pair ((n : Nat) -> LeN Q n -> Eq (iv1 n) (iv1 Q))
                 (Or ((n : Nat) -> Not (IsCpl (ov1 n)))
                     ((n : Nat) -> LeN Q n -> IsCpl (ov1 n))))
    Q1d = node-split p iv1 ivr1 ov1 cont1 mt1 m11

    Q1 : Nat
    Q1 = fst Q1d

    q1stab : (n : Nat) -> LeN Q1 n -> Eq (iv1 n) (iv1 Q1)
    q1stab = fst (snd Q1d)

    q1ov : Or ((n : Nat) -> Not (IsCpl (ov1 n)))
              ((n : Nat) -> LeN Q1 n -> IsCpl (ov1 n))
    q1ov = snd (snd Q1d)

    stab1At : (B : Nat) -> LeN Q1 B
            -> (n : Nat) -> LeN B n -> Eq (iv1 n) (iv1 B)
    stab1At B le n ln =
      Eq-trans (q1stab n (LeN-trans {Q1} {B} {n} le ln)) (Eq-sym (q1stab B le))

    ----------------------------------------------------------------
    -- the demand, read one level down
    ----------------------------------------------------------------

    dEq : (L : Nat -> Nat) (j : Nat) -> IsCpl (NN.at L j)
        -> Not (IsCpl (ovh (NGat L j)))
        -> Eq (hgt (R.Vd p Th L j)) w
        -> Eq (PZ.Dmj p Th L j)
              (shiftOr (suc zero) (blockOn (suc p) T1 (parV p L j)))
    dEq L j ic nc ew =
      Eq-trans (descEq L j ic nc)
        (Eq-cong
          (\ T -> shiftOr (suc zero) (blockOn (suc p) T (parV p L j)))
          (Eq-trans (Eq-cong Tw ew) eTw))

    blkD : (L : Nat -> Nat) (j i0 : Nat)
         -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
         -> (ic : IsCpl (NN.at L j))
         -> Eq (hgt (R.Vd p Th L j)) w
         -> Eq (blockOn (suc p) T1 (parV p L j)) (inr (suc i0))
    blkD L j i0 eD ic ew =
      shiftOr-inv (blockOn (suc p) T1 (parV p L j)) i0
        (Eq-trans
          (Eq-sym (dEq L j ic (nc-of L j (suc (suc i0)) eD) ew)) eD)

    nc1-of : (L : Nat -> Nat) (j i0 : Nat)
           -> Eq (blockOn (suc p) T1 (parV p L j)) (inr (suc i0))
           -> Not (IsCpl (ov1 (NG1 L j)))
    nc1-of L j i0 e icv = bad (Eq-trans (Eq-sym (MM.blk-inl L j icv)) e)
      where
        bad : Not (Eq {Or Top Nat} (inl tt) (inr (suc i0)))
        bad ()

    cg1E-of : (L : Nat -> Nat) (j i0 : Nat)
            -> Eq (blockOn (suc p) T1 (parV p L j)) (inr (suc i0))
            -> Eq (MM.cg L j) (suc i0)
    cg1E-of L j i0 e =
      inr-inj (MM.cg L j) (suc i0)
        (Eq-trans
          (Eq-sym
            (MM.blk-fbot L j (nc1-of L j i0 e) (parV-incpl p L j (MM.cg L j))))
          e)

    ----------------------------------------------------------------
    -- the whole top level is frozen above a descent, so the descended
    -- demand IS the recursion's demand at every later stage
    ----------------------------------------------------------------

    liftUp : (L L' : Nat -> Nat)
           -> ((i : Nat) -> LeN (L (suc i)) (L' (suc i)))
           -> (j j' : Nat) -> LeN j j'
           -> (ic : IsCpl (NN.at L j))
           -> Not (IsCpl (ovh (NGat L j)))
           -> Eq (hgt (R.Vd p Th L j)) w
           -> Eq (PZ.Dmj p Th L' j')
                 (shiftOr (suc zero) (blockOn (suc p) T1 (parV p L' j')))
    liftUp L L' lp j j' lj ic nc ew = dEq L' j' ic' nc' ew'
      where
        frz : Eq (NGat L' j') (NGat L j)
        frz = NG-frz L L' lp j j' lj ic

        cgSame : Eq (NN.cg L' j') (NN.cg L j)
        cgSame = Eq-cong ivh frz

        vdE : Eq (R.Vd p Th L j) (R.Vd p Th L' j')
        vdE = Vd-up L L' lp j j' lj (at-Vd L j ic)

        ic' : IsCpl (NN.at L' j')
        ic' =
          Vd-at L' j' (Eq-trans cgSame (cg-one L j ic))
            (Eq-transport (\ z -> IsCpl z) vdE (at-Vd L j ic))

        nc' : Not (IsCpl (ovh (NGat L' j')))
        nc' = Eq-transport (\ z -> Not (IsCpl (ovh z))) (Eq-sym frz) nc

        ew' : Eq (hgt (R.Vd p Th L' j')) w
        ew' = Eq-trans (Eq-cong hgt (Eq-sym vdE)) ew

    termB : (B : Nat) -> LeN Q1 B
          -> (L : Nat -> Nat) (j i0 : Nat)
          -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
          -> (ic : IsCpl (NN.at L j))
          -> Eq (hgt (R.Vd p Th L j)) w
          -> LeN B (NG1 L j)
          -> Persist L j i0
    termB B leB L j i0 eD ic ew past L' lp j' lj =
      Eq-trans (liftUp L L' lp j j' lj ic nc ew)
        (Eq-cong (shiftOr (suc zero))
          (Eq-trans (MM.blk-fbot L' j' nc1' (parV-incpl p L' j' (MM.cg L' j')))
            (Eq-cong inr cg1E')))
      where
        nc : Not (IsCpl (ovh (NGat L j)))
        nc = nc-of L j (suc (suc i0)) eD

        bE : Eq (blockOn (suc p) T1 (parV p L j)) (inr (suc i0))
        bE = blkD L j i0 eD ic ew

        nc1 : Not (IsCpl (ov1 (NG1 L j)))
        nc1 = nc1-of L j i0 bE

        cg1E : Eq (MM.cg L j) (suc i0)
        cg1E = cg1E-of L j i0 bE

        ei1 : Eq (iv1 B) (suc i0)
        ei1 = Eq-trans (Eq-sym (stab1At B leB (NG1 L j) past)) cg1E

        past' : LeN B (NG1 L' j')
        past' =
          LeN-trans {B} {NG1 L j} {NG1 L' j'} past
            (NG1-mono2 L L' lp j j' lj)

        cg1E' : Eq (MM.cg L' j') (suc i0)
        cg1E' = Eq-trans (stab1At B leB (NG1 L' j') past') ei1

        nc1' : Not (IsCpl (ov1 (NG1 L' j')))
        nc1' = route q1ov
          where
            route : Or ((n : Nat) -> Not (IsCpl (ov1 n)))
                       ((n : Nat) -> LeN Q1 n -> IsCpl (ov1 n))
                  -> Not (IsCpl (ov1 (NG1 L' j')))
            route (inl nev) = nev (NG1 L' j')
            route (inr tot) =
              Empty-elim
                (nc1 (tot (NG1 L j) (LeN-trans {Q1} {B} {NG1 L j} leB past)))

    cheapB : (B : Nat)
           -> (L : Nat -> Nat) (j i0 : Nat)
           -> Eq (PZ.Dmj p Th L j) (inr (suc (suc i0)))
           -> (ic : IsCpl (NN.at L j))
           -> Eq (hgt (R.Vd p Th L j)) w
           -> Not (LeN B (NG1 L j))
           -> LeN (suc (L (suc i0))) B
    cheapB B L j i0 eD ic ew nl =
      LeN-trans {suc (L (suc i0))} {suc (NG1 L j)} {B} lt1
        (nle-lt B (NG1 L j) nl)
      where
        bE : Eq (blockOn (suc p) T1 (parV p L j)) (inr (suc i0))
        bE = blkD L j i0 eD ic ew

        cg1E : Eq (MM.cg L j) (suc i0)
        cg1E = cg1E-of L j i0 bE

        li1 : LeN (suc (suc i0)) (suc p)
        li1 = Eq-transport (\ z -> LeN (suc z) (suc p)) cg1E (ivr1 (NG1 L j))

        htsE : Eq (hts (parV p L j) (MM.cg L j)) (L (suc i0))
        htsE =
          Eq-cong hgt
            (Eq-trans
              (Eq-cong (\ z -> nth (fbot zero) z (parV p L j)) cg1E)
              (tup-nth (suc p) (pvf L j) (suc i0) li1))

        lt1 : LeN (suc (L (suc i0))) (suc (NG1 L j))
        lt1 = Eq-transport (\ z -> LeN z (NG1 L j)) htsE (MM.NG-ge-hts L j)

  ------------------------------------------------------------------
  -- THE WALK'S PLUMBING
  ------------------------------------------------------------------

  Res : Set
  Res = Sigma Nat (\ N -> (n : Nat) -> LeN N n -> Eq (ivP n) (ivP N))

  Lv-monoP : (k k' : Nat) -> LeN k k' -> (i : Nat)
           -> LeN (Lv k (suc i)) (Lv k' (suc i))
  Lv-monoP k k' le i = lev-mono ivP Lv (\ _ _ -> refl) k k' le (suc i)

  Lv-mono0 : (k k' : Nat) -> LeN k k' -> LeN (Lv k zero) (Lv k' zero)
  Lv-mono0 k k' le = lev-mono ivP Lv (\ _ _ -> refl) k k' le zero

  minN-mono : (a b c : Nat) -> LeN a b -> LeN (minN a c) (minN b c)
  minN-mono zero    b       c       le = tt
  minN-mono (suc a) zero    c       ()
  minN-mono (suc a) (suc b) zero    le = tt
  minN-mono (suc a) (suc b) (suc c) le = minN-mono a b c le

  -- the depth direction, at each parameter setting, UNCONDITIONALLY
  JJ : (L : Nat -> Nat)
     -> Sigma Nat (\ J -> (j : Nat) -> LeN (suc J) j
          -> Eq (R.Qd p Th L j) (R.Qd p Th L (suc J)))
  JJ L = Qd-stab-full p Th mth m1th L (vmj L) (dec L)

  ------------------------------------------------------------------
  -- A PERSISTING DEMAND FIXES THE INDEX
  ------------------------------------------------------------------

  terminalP : (k' i0 j : Nat) -> Eq (ivP k') (suc i0)
            -> LeN (suc j) (Lv k' zero) -> Persist (Lv k') j i0 -> Res
  terminalP k' i0 j ev lj pers = mkSigma k' con
    where
      con : (n : Nat) -> LeN k' n -> Eq (ivP n) (ivP k')
      con n ln =
        Eq-trans (PZ.Qd-indep-par p Th (Lv n) j i0 conN eJ (Lv n zero) lD)
          (Eq-sym ev)
        where
          lp : (i : Nat) -> LeN (Lv k' (suc i)) (Lv n (suc i))
          lp i = Lv-monoP k' n ln i

          eJ : Eq (PZ.Dmj p Th (Lv n) j) (inr (suc (suc i0)))
          eJ = pers (Lv n) lp j (LeN-refl j)

          conN : (j' : Nat) -> LeN j j'
               -> Eq (PZ.Dmj p Th (Lv n) j') (PZ.Dmj p Th (Lv n) j)
          conN j' lj' = Eq-trans (pers (Lv n) lp j' lj') (Eq-sym eJ)

          lD : LeN (suc j) (Lv n zero)
          lD = LeN-trans {suc j} {Lv k' zero} {Lv n zero} lj (Lv-mono0 k' n ln)

  ------------------------------------------------------------------
  -- THE LOOP, PARAMETRIC IN THE BOUND AND IN THE BUMP ANALYSIS
  ------------------------------------------------------------------

  module RUN (B : Nat) (k0 : Nat)
             (bsplit : (k' i0 : Nat) -> LeN k0 k' -> Eq (ivP k') (suc i0)
                     -> (j : Nat) -> LeN (suc j) (Lv k' zero)
                     -> Eq (PZ.Dmj p Th (Lv k') j) (inr (suc (suc i0)))
                     -> Or (Persist (Lv k') j i0)
                           (Or (LeN (suc (Lv k' (suc i0))) B) Res))
             where

    module BB = BUD p Th B

    Mof-mono : (k k' : Nat) -> LeN k k' -> LeN (BB.Mof k) (BB.Mof k')
    Mof-mono k k' le =
      sumTo-mono p (\ i -> minN (Lv k (suc i)) B)
        (\ i -> minN (Lv k' (suc i)) B)
        (\ i -> minN-mono (Lv k (suc i)) (Lv k' (suc i)) B (Lv-monoP k k' le i))

    loop : (F k : Nat) -> LeN k0 k -> LeN BB.Cap (plus F (BB.Mof k)) -> Res
    loop F k lk0 inv = route (ivP k) refl
      where
        ------------------------------------------------------------
        -- a bump at stage `k'`, demanding parameter `i0`
        ------------------------------------------------------------
        bumpAt : (k' i0 : Nat) -> LeN k k' -> Eq (ivP k') (suc i0) -> Res
        bumpAt k' i0 lkk' ev =
          src (PZ.Qd-source p Th (Lv k') (Lv k' zero) i0 ev)
          where
            lk0' : LeN k0 k'
            lk0' = LeN-trans {k0} {k} {k'} lk0 lkk'

            src : Sigma Nat (\ j -> Pair (LeN (suc j) (Lv k' zero))
                    (Eq (PZ.Dmj p Th (Lv k') j) (inr (suc (suc i0)))))
                -> Res
            src (mkSigma j (mkSigma lj eD)) =
              pick (bsplit k' i0 lk0' ev j lj eD)
              where
                pick : Or (Persist (Lv k') j i0)
                          (Or (LeN (suc (Lv k' (suc i0))) B) Res)
                     -> Res
                pick (inl pers)     = terminalP k' i0 j ev lj pers
                pick (inr (inr r))  = r
                pick (inr (inl ch)) = spend F inv'
                  where
                    li0 : LeN (suc i0) p
                    li0 =
                      Eq-transport (\ z -> LeN (suc z) (suc p)) ev (ivPr k')

                    inv' : LeN BB.Cap (plus F (BB.Mof k'))
                    inv' =
                      LeN-trans {BB.Cap} {plus F (BB.Mof k)}
                        {plus F (BB.Mof k')} inv
                        (plus-mono F F (BB.Mof k) (BB.Mof k') (LeN-refl F)
                          (Mof-mono k k' lkk'))

                    spend : (F' : Nat) -> LeN BB.Cap (plus F' (BB.Mof k'))
                          -> Res
                    spend zero     le' =
                      Empty-elim (BB.M-max k' i0 li0 ev le' ch)
                    spend (suc F') le' =
                      loop F' (suc k')
                        (LeN-trans {k0} {k'} {suc k'} lk0' (LeN-suc k'))
                        (Eq-transport (\ z -> LeN BB.Cap z)
                          (Eq-sym stepE) le')
                      where
                        stepE : Eq (plus F' (BB.Mof (suc k')))
                                   (suc (plus F' (BB.Mof k')))
                        stepE =
                          Eq-trans
                            (Eq-cong (plus F') (BB.M-step k' i0 li0 ev ch))
                            (plus-suc-r F' (BB.Mof k'))

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
                            (Sigma Nat (\ t ->
                               Pair (LeN (suc t) s) (Not (P0 t))))
                scanZ zero    = inl (\ t ())
                scanZ (suc s) = step (scanZ s)
                  where
                    step : Or ((t : Nat) -> LeN (suc t) s -> P0 t)
                              (Sigma Nat (\ t ->
                                 Pair (LeN (suc t) s) (Not (P0 t))))
                         -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                               (Sigma Nat (\ t ->
                                  Pair (LeN (suc t) (suc s)) (Not (P0 t))))
                    step (inr (mkSigma t (mkSigma lt np))) =
                      inr (mkSigma t
                            (mkSigma
                              (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s))
                              np))
                    step (inl hh) = step2 (P0dec s)
                      where
                        step2 : Dec (P0 s)
                              -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                                    (Sigma Nat (\ t ->
                                       Pair (LeN (suc t) (suc s))
                                            (Not (P0 t))))
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
                            (Eq-transport (\ z -> Eq (ivP z) zero)
                              (Eq-sym e) (allz t))
                            (Eq-sym ev)
                sc (inr (mkSigma t (mkSigma lt np))) =
                  nz (ivP (plus t k)) refl
                  where
                    nz : (v : Nat) -> Eq (ivP (plus t k)) v -> Res
                    nz zero     e = Empty-elim (np e)
                    nz (suc i0) e = bumpAt (plus t k) i0 (plus-ge-r t k) e

        route : (v : Nat) -> Eq (ivP k) v -> Res
        route zero     ev = zeroCase ev
        route (suc i0) ev = bumpAt k i0 (LeN-refl k) ev

    run : Res
    run = loop BB.Cap k0 (LeN-refl k0) (plus-ge-l BB.Cap (BB.Mof k0))

  ------------------------------------------------------------------
  -- THE DESCENT REGIME: RESTART THE LOOP WITH THE SUB-TRACE'S BOUND
  --
  -- Reached at most once: `w-fixed` says the recursive value is the
  -- SAME numeral at every stage from here on, so the trace descended
  -- into -- and with it the bound `Q1` -- never changes again.
  ------------------------------------------------------------------

  goB : (kstar jstar i0 : Nat)
      -> Eq (PZ.Dmj p Th (Lv kstar) jstar) (inr (suc (suc i0)))
      -> IsCpl (NN.at (Lv kstar) jstar)
      -> Res
  goB kstar jstar i0 eD ic = match (Tw w) refl
    where
      w : Nat
      w = hgt (R.Vd p Th (Lv kstar) jstar)

      icStar : IsCpl (R.Vd p Th (Lv kstar) jstar)
      icStar = at-Vd (Lv kstar) jstar ic

      nc : Not (IsCpl (ovh (NGat (Lv kstar) jstar)))
      nc = nc-of (Lv kstar) jstar (suc (suc i0)) eD

      match : (T : Tr (suc p)) -> Eq (Tw w) T -> Res
      -- a `stop` waits for nothing, contradicting the parameter demand
      match (stop v) e = Empty-elim (bad (Eq-trans (Eq-sym eD) dd))
        where
          dd : Eq (PZ.Dmj p Th (Lv kstar) jstar) (inl tt)
          dd =
            Eq-trans (descEq (Lv kstar) jstar ic nc)
              (Eq-cong
                (\ T -> shiftOr (suc zero)
                          (blockOn (suc p) T (parV p (Lv kstar) jstar)))
                e)

          bad : Not (Eq {Or Top Nat} (inr (suc (suc i0))) (inl tt))
          bad ()
      match (node iv1 ivr1 ov1 cont1) e = RUN.run B1 kstar bsplitB
        where
          mt1 : MonoTr (suc p) (node iv1 ivr1 ov1 cont1)
          mt1 =
            Eq-transport (\ T -> MonoTr (suc p) T) e
              (snd mth (suc zero) lc1 w)

          m11 : MP1T (suc p) (node iv1 ivr1 ov1 cont1)
          m11 =
            Eq-transport (\ T -> MP1T (suc p) T) e
              (snd (snd m1th) (suc zero) lc1 w)

          module S = SUB w iv1 ivr1 ov1 cont1 e mt1 m11

          B1 : Nat
          B1 = maxN Q0 S.Q1

          leQ0B1 : LeN Q0 B1
          leQ0B1 = maxN-le-l Q0 S.Q1

          leQ1B1 : LeN S.Q1 B1
          leQ1B1 = maxN-le-r Q0 S.Q1

          bsplitB : (k' i1 : Nat) -> LeN kstar k' -> Eq (ivP k') (suc i1)
                  -> (j : Nat) -> LeN (suc j) (Lv k' zero)
                  -> Eq (PZ.Dmj p Th (Lv k') j) (inr (suc (suc i1)))
                  -> Or (Persist (Lv k') j i1)
                        (Or (LeN (suc (Lv k' (suc i1))) B1) Res)
          bsplitB k' i1 lk ev j lj eD1 = top (IsCpl-dec (NN.at (Lv k') j))
            where
              Out : Set
              Out =
                Or (Persist (Lv k') j i1)
                   (Or (LeN (suc (Lv k' (suc i1))) B1) Res)

              top : Dec (IsCpl (NN.at (Lv k') j)) -> Out
              -- (A) nothing descends here
              top (no na) = pickA (LeN-dec B1 (NGat (Lv k') j))
                where
                  pickA : Dec (LeN B1 (NGat (Lv k') j)) -> Out
                  pickA (yes past) =
                    inl (termA B1 leQ0B1 (Lv k') j i1 eD1 na past)
                  pickA (no nl) =
                    inr (inl (cheapA B1 (Lv k') j i1 eD1 na nl))
              -- (B) the demand comes through the descent
              top (yes ic') = pickB (LeN-dec B1 (S.NG1 (Lv k') j))
                where
                  ew : Eq (hgt (R.Vd p Th (Lv k') j)) w
                  ew =
                    Eq-cong hgt
                      (w-fixed (Lv kstar) (Lv k') (Lv-monoP kstar k' lk)
                        jstar j icStar (at-Vd (Lv k') j ic'))

                  pickB : Dec (LeN B1 (S.NG1 (Lv k') j)) -> Out
                  pickB (yes past) =
                    inl (S.termB B1 leQ1B1 (Lv k') j i1 eD1 ic' ew past)
                  pickB (no nl) =
                    inr (inl (S.cheapB B1 (Lv k') j i1 eD1 ic' ew nl))

  ------------------------------------------------------------------
  -- THE MAIN REGIME, AND THE ANSWER
  ------------------------------------------------------------------

  bsplitA : (k' i0 : Nat) -> LeN zero k' -> Eq (ivP k') (suc i0)
          -> (j : Nat) -> LeN (suc j) (Lv k' zero)
          -> Eq (PZ.Dmj p Th (Lv k') j) (inr (suc (suc i0)))
          -> Or (Persist (Lv k') j i0)
                (Or (LeN (suc (Lv k' (suc i0))) Q0) Res)
  bsplitA k' i0 lk ev j lj eD = top (IsCpl-dec (NN.at (Lv k') j))
    where
      Out : Set
      Out =
        Or (Persist (Lv k') j i0)
           (Or (LeN (suc (Lv k' (suc i0))) Q0) Res)

      top : Dec (IsCpl (NN.at (Lv k') j)) -> Out
      top (no na) = pick (LeN-dec Q0 (NGat (Lv k') j))
        where
          pick : Dec (LeN Q0 (NGat (Lv k') j)) -> Out
          pick (yes past) =
            inl (termA Q0 (LeN-refl Q0) (Lv k') j i0 eD na past)
          pick (no nl) =
            inr (inl (cheapA Q0 (Lv k') j i0 eD na nl))
      top (yes ic) = inr (inr (goB k' j i0 eD ic))

  ivP-evconst : Res
  ivP-evconst = RUN.run Q0 zero bsplitA

  -- ... which IS the index clause of MP1 for the recursion trace,
  -- with NO hypothesis on the recursive value.
  ivP-EvConstN : EvConstN (P.ivP p Th)
  ivP-EvConstN = ivP-evconst
