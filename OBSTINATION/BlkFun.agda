{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkFun
--
-- THE BLOCK COMPONENT AS A FUNCTION WITH A TRACE OF ITS OWN.
--
-- `BlkTraceR` describes a block by DEPTH: `q j m` is the coordinate f_j
-- demands when its recursion argument is at level m, and `hv m j` the height
-- it then offers, the parameters being pinned at heights `Y`.  But a function
-- with a trace is indexed by ITS OWN WALK STEP, and f_j's arguments are the
-- recursion argument x AND the parameters -- so its walk raises whichever of
-- them it demands, and the depth is just the level reached at x.  That trace
-- is DEFINED here from the block's, exactly as `MainComp` defines the
-- composite's from the parts':
--
--     A n c    -- the level of f_j's argument c after n walk steps
--     Ypar n c -- the level reached at the parameter that is the step terms'
--                 coordinate c, i.e. A n (1 + (c - r))
--     Ivb n    -- f_j's demand: q, at depth `A n 0`, with the parameters at
--                 the heights they have REACHED
--     Kvb n    -- f_j's height there
--
-- f_j's coordinate 0 is x, and its coordinate 1 + (c - r) is the step terms'
-- parameter c -- which is exactly the numbering `q` already produces
-- (`BlkTraceR.pickQ`), so `Ivb` is in range for the arity 1 + (a - r)
-- (`Ivb-range`).
--
-- WHAT IS PROVED HERE.  For a block with NO parameters (a = r), the walk
-- raises only x, so the depth IS the walk step, and the Main Property of the
-- components as functions with a trace follows from `MainBlk2.MPblock` and
-- `BlkPass2.hpass-blk` (`mp-fun`): MP of the step terms gives MP of f_0, f_1.
--
-- WITH parameters this reindexing is NOT settled -- see the comment at
-- `mp-fun` and NEXT_SESSION_MP_HPASS.md: the parameters' levels grow along
-- f_j's own walk, so `Ivb` is the block's index at a MOVING `Y`, whereas
-- everything proved so far is at a fixed one.
--
-- The Y-congruence and Y-monotonicity of the block trace (`hv-Y`, `q-Y`,
-- `hv-Y-le`) are what connects the two, and they hold in general.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkFun where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MPPass using (Mono ; HPass ; MP ; hpass-cong)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; bump-ne ; nOf ; nOf-cong ; nOf-mono)
open import OBSTINATION.BlkTraceR using
  (subN ; hv ; av ; nn ; cIdx ; q ; pickQ-in ; pickQ-out ;
   av-rec ; av-out ; av-mono ; hv-mono1)
open import OBSTINATION.MainBlk2 using (one ; two ; hgt ; MPblock)
open import OBSTINATION.BlkPass2 using (hpass-blk)

------------------------------------------------------------------------
-- THE BLOCK TRACE DEPENDS ON THE PARAMETERS ONLY THROUGH THEIR HEIGHTS
------------------------------------------------------------------------

module _ (r a : Nat)
         (iv : Nat -> Nat -> Nat)
         (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
         (kv : Nat -> Nat -> Nat)
         (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         where

  private
    HV : (Nat -> Nat) -> Nat -> Nat -> Nat
    HV Y = hv r a iv ivr kv kv-mono Y

    AV : (Nat -> Nat) -> Nat -> Nat -> Nat
    AV Y = av r a iv ivr kv kv-mono Y

    NN : (Nat -> Nat) -> Nat -> Nat -> Nat
    NN Y = nn r a iv ivr kv kv-mono Y

    CI : (Nat -> Nat) -> Nat -> Nat -> Nat
    CI Y = cIdx r a iv ivr kv kv-mono Y

    Q : (Nat -> Nat) -> Nat -> Nat -> Nat
    Q Y = q r a iv ivr kv kv-mono Y

  -- POINTWISE EQUAL PARAMETER HEIGHTS GIVE THE SAME TRACE
  module _ (Y Y' : Nat -> Nat)
           (agree : (c : Nat) -> Not (LeN (suc c) r) -> Eq (Y c) (Y' c))
           where

    mutual
      hv-Y : (m j : Nat) -> Eq (HV Y m j) (HV Y' m j)
      hv-Y zero    j = refl
      hv-Y (suc m) j = Eq-cong (kv j) (nn-Y m j)

      nn-Y : (m j : Nat) -> Eq (NN Y j m) (NN Y' j m)
      nn-Y m j =
        nOf-cong a (iv j) (ivr j) (AV Y m) (AV Y' m) same
        where
          same : (c : Nat) -> Eq (AV Y m c) (AV Y' m c)
          same c = route (LeN-dec (suc c) r)
            where
              route : Dec (LeN (suc c) r) -> Eq (AV Y m c) (AV Y' m c)
              route (yes lc) =
                Eq-trans (av-rec r a iv ivr kv kv-mono Y c lc m)
                  (Eq-trans (hv-Y m c)
                    (Eq-sym (av-rec r a iv ivr kv kv-mono Y' c lc m)))
              route (no nc) =
                Eq-trans (av-out r a iv ivr kv kv-mono Y c nc m)
                  (Eq-trans (agree c nc)
                    (Eq-sym (av-out r a iv ivr kv kv-mono Y' c nc m)))

    ci-Y : (m j : Nat) -> Eq (CI Y j m) (CI Y' j m)
    ci-Y m j = Eq-cong (iv j) (nn-Y m j)

    q-Y : (m j : Nat) -> Eq (Q Y j m) (Q Y' j m)
    q-Y zero    j = refl
    q-Y (suc m) j = route (LeN-dec (suc (CI Y j m)) r)
      where
        route : Dec (LeN (suc (CI Y j m)) r) -> Eq (Q Y j (suc m)) (Q Y' j (suc m))
        route (yes lc) =
          Eq-trans (pickQ-in r a iv ivr kv kv-mono Y (CI Y j m) (\ s -> Q Y s m) lc)
            (Eq-trans (q-Y m (CI Y j m))
              (Eq-trans (Eq-cong (\ z -> Q Y' z m) (ci-Y m j))
                (Eq-sym
                  (pickQ-in r a iv ivr kv kv-mono Y' (CI Y' j m) (\ s -> Q Y' s m)
                    (Eq-transport (\ z -> LeN (suc z) r) (ci-Y m j) lc)))))
        route (no nc) =
          Eq-trans (pickQ-out r a iv ivr kv kv-mono Y (CI Y j m) (\ s -> Q Y s m) nc)
            (Eq-trans (Eq-cong (\ z -> suc (subN r z)) (ci-Y m j))
              (Eq-sym
                (pickQ-out r a iv ivr kv kv-mono Y' (CI Y' j m) (\ s -> Q Y' s m)
                  (\ lc -> nc (Eq-transport (\ z -> LeN (suc z) r)
                                 (Eq-sym (ci-Y m j)) lc)))))

  -- HIGHER PARAMETERS GIVE A HIGHER TRACE
  module _ (Y Y' : Nat -> Nat)
           (grows : (c : Nat) -> Not (LeN (suc c) r) -> LeN (Y c) (Y' c))
           where

    mutual
      hv-Y-le : (m j : Nat) -> LeN (HV Y m j) (HV Y' m j)
      hv-Y-le zero    j = tt
      hv-Y-le (suc m) j = kv-mono j (NN Y j m) (NN Y' j m) (nn-Y-le m j)

      nn-Y-le : (m j : Nat) -> LeN (NN Y j m) (NN Y' j m)
      nn-Y-le m j = nOf-mono a (iv j) (ivr j) (AV Y m) (AV Y' m) same
        where
          same : (c : Nat) -> LeN (AV Y m c) (AV Y' m c)
          same c = route (LeN-dec (suc c) r)
            where
              route : Dec (LeN (suc c) r) -> LeN (AV Y m c) (AV Y' m c)
              route (yes lc) =
                Eq-transport (\ z -> LeN z (AV Y' m c))
                  (Eq-sym (av-rec r a iv ivr kv kv-mono Y c lc m))
                  (Eq-transport (\ z -> LeN (HV Y m c) z)
                    (Eq-sym (av-rec r a iv ivr kv kv-mono Y' c lc m))
                    (hv-Y-le m c))
              route (no nc) =
                Eq-transport (\ z -> LeN z (AV Y' m c))
                  (Eq-sym (av-out r a iv ivr kv kv-mono Y c nc m))
                  (Eq-transport (\ z -> LeN (Y c) z)
                    (Eq-sym (av-out r a iv ivr kv kv-mono Y' c nc m))
                    (grows c nc))

  -- monotone in the depth, for a component in range
  hv-le : (Y : Nat -> Nat) (j : Nat) -> LeN (suc j) r -> Mono (\ m -> HV Y m j)
  hv-le Y j lj m m' le =
    Eq-transport (\ z -> LeN z (HV Y m' j))
      (av-rec r a iv ivr kv kv-mono Y j lj m)
      (Eq-transport (\ z -> LeN (AV Y m j) z)
        (av-rec r a iv ivr kv kv-mono Y j lj m')
        (av-mono r a iv ivr kv kv-mono Y m m' le j))

------------------------------------------------------------------------
-- s - n IS STRICTLY SMALLER THAN a - n, FOR n <= s < a
------------------------------------------------------------------------

subN-lt : (n s a : Nat) -> LeN (suc s) a -> Not (LeN (suc s) n) ->
  LeN (suc (subN n s)) (subN n a)
subN-lt zero    s       a       ls nt = ls
subN-lt (suc n) zero    a       ls nt = Empty-elim (nt tt)
subN-lt (suc n) (suc s) zero    () nt
subN-lt (suc n) (suc s) (suc a) ls nt = subN-lt n s a ls nt

------------------------------------------------------------------------
-- THE COMPONENT'S OWN TRACE
--
-- Arity `b = 1 + (a - r)`: the recursion argument, then the parameters.  The
-- walk raises whatever f_j demands, and the recursion DEPTH is the level it
-- has reached at coordinate 0 -- so the demand and the height are the block's,
-- read at that depth and at the parameter levels REACHED SO FAR.
------------------------------------------------------------------------

module Trace (a : Nat)
             (iv : Nat -> Nat -> Nat)
             (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
             (kv : Nat -> Nat -> Nat)
             (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
             (j : Nat) (lj : LeN (suc j) two)
             where

  b : Nat
  b = suc (subN two a)

  mutual
    A : Nat -> Nat -> Nat
    A zero    c = zero
    A (suc n) c = bump (Ivb n) (A n) c

    -- the level reached at the parameter that is the step terms' coordinate c
    Ypar : Nat -> Nat -> Nat
    Ypar n c = A n (suc (subN two c))

    Ivb : Nat -> Nat
    Ivb n = q two a iv ivr kv kv-mono (Ypar n) j (A n zero)

    Kvb : Nat -> Nat
    Kvb n = hv two a iv ivr kv kv-mono (Ypar n) (A n zero) j

  ----------------------------------------------------------------------
  -- IT IS A FUNCTION WITH A TRACE: the demand is in range ...
  ----------------------------------------------------------------------

  q-range : (Y : Nat -> Nat) (i m : Nat) ->
    LeN (suc (q two a iv ivr kv kv-mono Y i m)) b
  q-range Y i zero    = tt
  q-range Y i (suc m) = route (LeN-dec (suc (cIdx two a iv ivr kv kv-mono Y i m)) two)
    where
      c : Nat
      c = cIdx two a iv ivr kv kv-mono Y i m

      route : Dec (LeN (suc c) two) ->
        LeN (suc (q two a iv ivr kv kv-mono Y i (suc m))) b
      route (yes lc) =
        Eq-transport (\ z -> LeN (suc z) b)
          (Eq-sym (pickQ-in two a iv ivr kv kv-mono Y c
                    (\ s -> q two a iv ivr kv kv-mono Y s m) lc))
          (q-range Y c m)
      route (no nc) =
        Eq-transport (\ z -> LeN (suc z) b)
          (Eq-sym (pickQ-out two a iv ivr kv kv-mono Y c
                    (\ s -> q two a iv ivr kv kv-mono Y s m) nc))
          (subN-lt two c a (ivr i (nn two a iv ivr kv kv-mono Y i m)) nc)

  Ivb-range : (n : Nat) -> LeN (suc (Ivb n)) b
  Ivb-range n = q-range (Ypar n) j (A n zero)

  ----------------------------------------------------------------------
  -- ... and the height is monotone
  ----------------------------------------------------------------------

  A-mono1 : (n c : Nat) -> LeN (A n c) (A (suc n) c)
  A-mono1 n c = route (EqNat-dec c (Ivb n))
    where
      route : Dec (Eq c (Ivb n)) -> LeN (A n c) (A (suc n) c)
      route (yes e) =
        Eq-transport (\ z -> LeN (A n c) z)
          (Eq-sym (bump-eq (Ivb n) (A n) c e)) (LeN-suc (A n c))
      route (no ne) =
        Eq-transport (\ z -> LeN (A n c) z)
          (Eq-sym (bump-ne (Ivb n) (A n) c ne)) (LeN-refl (A n c))

  A-mono : (n n' : Nat) -> LeN n n' -> (c : Nat) -> LeN (A n c) (A n' c)
  A-mono n zero     le c =
    Eq-transport (\ z -> LeN (A z c) (A zero c))
      (Eq-sym (LeN-antisym {n} {zero} le tt)) (LeN-refl (A zero c))
  A-mono n (suc n') le c = route (LeN-dec n n')
    where
      eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
      eq' zero    y       l nl = Empty-elim (nl tt)
      eq' (suc x) zero    l nl = Eq-cong suc (LeN-antisym {x} {zero} l tt)
      eq' (suc x) (suc y) l nl = Eq-cong suc (eq' x y l nl)

      route : Dec (LeN n n') -> LeN (A n c) (A (suc n') c)
      route (yes l)  =
        LeN-trans {A n c} {A n' c} {A (suc n') c} (A-mono n n' l c) (A-mono1 n' c)
      route (no  nl) =
        Eq-transport (\ z -> LeN (A z c) (A (suc n') c))
          (Eq-sym (eq' n n' le nl)) (LeN-refl (A (suc n') c))

  Kvb-mono : Mono Kvb
  Kvb-mono n n' le =
    LeN-trans {Kvb n}
              {hv two a iv ivr kv kv-mono (Ypar n') (A n zero) j}
              {Kvb n'}
      (hv-Y-le two a iv ivr kv kv-mono (Ypar n) (Ypar n')
        (\ c _ -> A-mono n n' le (suc (subN two c))) (A n zero) j)
      (hv-le two a iv ivr kv kv-mono (Ypar n') j lj
        (A n zero) (A n' zero) (A-mono n n' le zero))

------------------------------------------------------------------------
-- A BLOCK WITHOUT PARAMETERS: MP OF THE STEP TERMS GIVES MP OF f_0, f_1
--
-- With `a = r = 2` the step terms read only the two recursive values, so no
-- descent can ever answer a parameter: every demand of f_j is the recursion
-- argument (`q-nopar`), f_j is unary, its walk raises only coordinate 0, and
-- so the DEPTH IS THE WALK STEP (`A-diag`).  Then the block's Main Property
-- transfers verbatim: (I) is `MainBlk2.MPblock` and (H) is
-- `BlkPass2.hpass-blk`, read at the depth = step.
--
-- This is the reindexing that turns the depth-indexed block statement into the
-- Main Property of f_j AS A FUNCTION WITH A TRACE.  For a block WITH
-- parameters it is open: there `Ivb n` is the block's index at the parameter
-- levels the walk has REACHED, which grow with n, whereas `MPblock` /
-- `hpass-blk` are proved at a FIXED `Y`.  `hv-Y`, `q-Y` and `hv-Y-le` above
-- are the tools that relate the two.
------------------------------------------------------------------------

module NoPar (iv : Nat -> Nat -> Nat)
             (ivr : (j n : Nat) -> LeN (suc (iv j n)) two)
             (kv : Nat -> Nat -> Nat)
             (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
             (N I : Nat -> Nat)
             (iv-stab : (j n : Nat) -> LeN (N j) n -> Eq (iv j n) (I j))
             (hverd : (j : Nat) -> HPass (kv j))
             (j : Nat) (lj : LeN (suc j) two)
             where

  open Trace two iv ivr kv kv-mono j lj

  -- the parameters, of which there are none
  Z : Nat -> Nat
  Z c = zero

  ----------------------------------------------------------------------
  -- EVERY DEMAND IS THE RECURSION ARGUMENT
  ----------------------------------------------------------------------

  q-nopar : (Y : Nat -> Nat) (i m : Nat) ->
    Eq (q two two iv ivr kv kv-mono Y i m) zero
  q-nopar Y i zero    = refl
  q-nopar Y i (suc m) =
    Eq-trans
      (pickQ-in two two iv ivr kv kv-mono Y c
        (\ s -> q two two iv ivr kv kv-mono Y s m) lc)
      (q-nopar Y c m)
    where
      c : Nat
      c = cIdx two two iv ivr kv kv-mono Y i m

      -- a step term of arity 2 can only read a recursive value
      lc : LeN (suc c) two
      lc = ivr i (nn two two iv ivr kv kv-mono Y i m)

  Ivb-zero : (n : Nat) -> Eq (Ivb n) zero
  Ivb-zero n = q-nopar (Ypar n) j (A n zero)

  ----------------------------------------------------------------------
  -- SO THE WALK RAISES ONLY COORDINATE 0, AND THE DEPTH IS THE STEP
  ----------------------------------------------------------------------

  A-diag : (n : Nat) -> Eq (A n zero) n
  A-diag zero    = refl
  A-diag (suc n) =
    Eq-trans (bump-eq (Ivb n) (A n) zero (Eq-sym (Ivb-zero n)))
             (Eq-cong suc (A-diag n))

  A-off : (n i : Nat) -> Eq (A n (suc i)) zero
  A-off zero    i = refl
  A-off (suc n) i =
    Eq-trans (bump-ne (Ivb n) (A n) (suc i) ne) (A-off n i)
    where
      ne : Not (Eq (suc i) (Ivb n))
      ne e = zne (Eq-trans e (Ivb-zero n))
        where
          zne : Not (Eq (suc i) zero)
          zne ()

  Ypar-Z : (n c : Nat) -> Eq (Ypar n c) (Z c)
  Ypar-Z n c = A-off n (subN two c)

  ----------------------------------------------------------------------
  -- THE MAIN PROPERTY OF f_j
  ----------------------------------------------------------------------

  HGT : Nat -> Nat -> Nat
  HGT = hgt two iv ivr kv kv-mono Z N I iv-stab

  Kvb-eq : (n : Nat) -> Eq (Kvb n) (HGT n j)
  Kvb-eq n =
    Eq-trans (hv-Y two two iv ivr kv kv-mono (Ypar n) Z (\ c _ -> Ypar-Z n c)
                (A n zero) j)
             (Eq-cong (\ z -> HGT z j) (A-diag n))

  mp-fun : MP Ivb Kvb
  mp-fun = mkSigma ivb-ev kvb-pass
    where
      ivb-ev : EvConstN Ivb
      ivb-ev =
        mkSigma zero (\ n _ -> Eq-trans (Ivb-zero n) (Eq-sym (Ivb-zero zero)))

      kvb-pass : HPass Kvb
      kvb-pass =
        hpass-cong (\ m -> HGT m j) Kvb (\ n -> Eq-sym (Kvb-eq n))
          (hpass-blk two iv ivr kv kv-mono Z N I iv-stab hverd j lj)
