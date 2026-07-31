{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompIv
--
-- THE COMPOSITE'S INDEX CLAUSE REDUCES TO THE STABILITY OF `sel`.
--
-- What is left of MP1 after `TrMP1Red` is `IvAll` -- the sequentiality
-- index, at every node.  For a composite the index is
--
--     ivf k = ivOf (Ths (selC k)) (dep k (selC k))
--
-- so it is the SELECTED argument's own demand, at that argument's replay
-- depth.  This file shows that ONE fact suffices:
--
--     `selC` is eventually constant  ==>  `ivf` is eventually constant.
--
-- The reason is the drive.  While `selC k = j`, the composite's next
-- demand is exactly the level argument `j`'s replay is stuck on, and
-- raising it advances that replay by at least one step (`nOf-step`, from
-- `stuck-level` and `bump-eq`).  So
--
--     dep (s + K) j  >=  s + dep K j                        (`dep-drive`)
--
-- -- argument `j` is driven linearly -- and `EvConstN (ivOf (Ths j))`
-- then pins `ivf` down.  (If `Ths j` is a `stop` there is no drive and
-- none is needed: `ivOf (stop w)` is constantly `0`.)
--
-- Note what is NOT needed: nothing about `Tg` beyond the stability of
-- `sel`, and no verdict on the values.  The whole remaining difficulty of
-- MP1 is therefore concentrated in
--
--     SelStab : `blockOn p Tg (vals k)` is eventually constant
--
-- which is the bounded climb of `MP1Comp` transported to the corrected
-- walk (see `NEXT_SESSION_TRACE.md` section 5).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompIv where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r)
open import OBSTINATION.MP1 using (plus-ge-l)
open import OBSTINATION.CapDet using (le-cases)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; bump-ne ; lv ; Adv ; Adv-mono ; nOf ; nOf-ge ;
   nOf-below-adv)
open import OBSTINATION.WalkAffine using (stuck-level)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrComp
open import OBSTINATION.TrMono using (lev-mono ; nOfOf-mono)
open import OBSTINATION.TrMP1 using (IvAll)

------------------------------------------------------------------------
-- RAISING THE LEVEL A REPLAY IS STUCK ON ADVANCES IT
------------------------------------------------------------------------

nOf-step : (a : Nat) (iv : Nat -> Nat)
           (ivr : (n : Nat) -> LeN (suc (iv n)) a) (L : Nat -> Nat)
         -> LeN (suc (nOf a iv ivr L))
                (nOf a iv ivr (bump (iv (nOf a iv ivr L)) L))
nOf-step a iv ivr L = nOf-ge a iv ivr L' (suc n) adv
  where
    n : Nat
    n = nOf a iv ivr L

    L' : Nat -> Nat
    L' = bump (iv n) L

    le : (c : Nat) -> LeN (L c) (L' c)
    le c = route (EqNat-dec c (iv n))
      where
        route : Dec (Eq c (iv n)) -> LeN (L c) (L' c)
        route (yes e) =
          Eq-transport (\ z -> LeN (L c) z)
            (Eq-sym (bump-eq (iv n) L c e)) (LeN-suc (L c))
        route (no ne) =
          Eq-transport (\ z -> LeN (L c) z)
            (Eq-sym (bump-ne (iv n) L c ne)) (LeN-refl (L c))

    atN : Adv a iv ivr L' n
    atN =
      Eq-transport (\ z -> LeN (suc z) (L' (iv n)))
        (Eq-sym (stuck-level a iv ivr L))
        (Eq-transport (\ z -> LeN (suc (L (iv n))) z)
          (Eq-sym (bump-eq (iv n) L (iv n) refl))
          (LeN-refl (suc (L (iv n)))))

    adv : (m : Nat) -> LeN (suc m) (suc n) -> Adv a iv ivr L' m
    adv m lm = route (le-cases m n lm)
      where
        route : Or (Eq n m) (LeN (suc m) n) -> Adv a iv ivr L' m
        route (inl e)  = Eq-transport (\ z -> Adv a iv ivr L' z) e atN
        route (inr lt) =
          Adv-mono a iv ivr L L' le m (nOf-below-adv a iv ivr L m lt)

------------------------------------------------------------------------
-- `IvAll` at a continuation, and the index of an arbitrary trace
------------------------------------------------------------------------

ivAll-cont : (a : Nat) (T : Tr (suc a)) -> IvAll (suc a) T
           -> (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
           -> IvAll a (contOf T c lc v)
ivAll-cont a (stop w)              ia c lc v = tt
ivAll-cont a (node iv ivr ov cont) ia c lc v = snd ia c lc v

------------------------------------------------------------------------
-- THE COMPOSITE WALK
------------------------------------------------------------------------

module CI (p : Nat) (Tg : Tr p) (a : Nat) (Ths : Nat -> Tr (suc a)) where

  module WW = W p Tg a Ths

  L-mono : (m n : Nat) -> LeN m n -> (c : Nat) -> LeN (WW.L m c) (WW.L n c)
  L-mono = lev-mono WW.ivf WW.L (\ _ _ -> refl)

  dep-mono : (m n : Nat) -> LeN m n -> (i : Nat)
           -> LeN (WW.dep m i) (WW.dep n i)
  dep-mono m n le i =
    nOfOf-mono (suc a) (Ths i) (WW.L m) (WW.L n) (L-mono m n le)

  --------------------------------------------------------------------
  -- THE DRIVE: while `j` is selected, argument `j` advances every step
  --------------------------------------------------------------------

  module Sel (j : Nat)
             (ivj : Nat -> Nat)
             (ivrj : (n : Nat) -> LeN (suc (ivj n)) (suc a))
             (ovj : Nat -> FEl)
             (contj : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
             (ej : Eq (Ths j) (node ivj ivrj ovj contj))
             where

    depEq : (k : Nat) -> Eq (WW.dep k j) (nOf (suc a) ivj ivrj (WW.L k))
    depEq k = Eq-cong (\ T -> nOfOf (suc a) T (WW.L k)) ej

    ivfEq : (k : Nat) -> Eq (WW.selC k) j
          -> Eq (WW.ivf k) (ivj (nOf (suc a) ivj ivrj (WW.L k)))
    ivfEq k ek =
      Eq-trans (Eq-cong (\ z -> ivOf (Ths z) (WW.dep k z)) ek)
        (Eq-cong (\ T -> ivOf T (nOfOf (suc a) T (WW.L k))) ej)

    dep-step : (k : Nat) -> Eq (WW.selC k) j
             -> LeN (suc (WW.dep k j)) (WW.dep (suc k) j)
    dep-step k ek =
      Eq-transport (\ z -> LeN (suc z) (WW.dep (suc k) j))
        (Eq-sym (depEq k))
        (Eq-transport (\ z -> LeN (suc (nOf (suc a) ivj ivrj (WW.L k))) z)
          (Eq-sym (Eq-trans (depEq (suc k)) bumped))
          (nOf-step (suc a) ivj ivrj (WW.L k)))
      where
        bumped : Eq (nOf (suc a) ivj ivrj (WW.L (suc k)))
                    (nOf (suc a) ivj ivrj
                      (bump (ivj (nOf (suc a) ivj ivrj (WW.L k))) (WW.L k)))
        bumped =
          Eq-cong (\ z -> nOf (suc a) ivj ivrj (bump z (WW.L k))) (ivfEq k ek)

    -- the BOUNDED form: only the stretch actually walked is needed, which
    -- is what a climb can check (`Eq (sel k) (inr j)` is decidable).
    dep-drive-b : (K s : Nat)
                -> ((t : Nat) -> LeN (suc t) s -> Eq (WW.selC (plus t K)) j)
                -> LeN (plus s (WW.dep K j)) (WW.dep (plus s K) j)
    dep-drive-b K zero    frz = LeN-refl (WW.dep K j)
    dep-drive-b K (suc s) frz =
      LeN-trans {suc (plus s (WW.dep K j))}
        {suc (WW.dep (plus s K) j)} {WW.dep (suc (plus s K)) j}
        (dep-drive-b K s
          (\ t lt -> frz t (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s))))
        (dep-step (plus s K) (frz s (LeN-refl s)))

    dep-drive : (K : Nat) -> ((k : Nat) -> LeN K k -> Eq (WW.selC k) j)
              -> (s : Nat) -> LeN (plus s (WW.dep K j)) (WW.dep (plus s K) j)
    dep-drive K frz s =
      dep-drive-b K s (\ t lt -> frz (plus t K) (plus-ge-r t K))

  --------------------------------------------------------------------
  -- the drive, uniformly over the shape of the argument
  --
  -- A `stop` argument has no drive and needs none: its recorded value is
  -- constant, so it cannot be what a climb is waiting to grow.
  --------------------------------------------------------------------

  dep-drive-any : (j K s : Nat)
                -> ((t : Nat) -> LeN (suc t) s -> Eq (WW.selC (plus t K)) j)
                -> Or ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
                      (LeN (plus s (WW.dep K j)) (WW.dep (plus s K) j))
  dep-drive-any j K s frz = route (Ths j) refl
    where
      Res : Set
      Res = Or ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
               (LeN (plus s (WW.dep K j)) (WW.dep (plus s K) j))

      route : (T : Tr (suc a)) -> Eq (Ths j) T -> Res
      route (stop w) e =
        inl (\ m ->
          Eq-trans (Eq-cong (\ T -> ovOf T m) e)
            (Eq-sym (Eq-cong (\ T -> ovOf T zero) e)))
      route (node ivj ivrj ovj contj) e =
        inr (Sel.dep-drive-b j ivj ivrj ovj contj e K s frz)

  --------------------------------------------------------------------
  -- ... SO A STABLE SELECTION SETTLES THE COMPOSITE'S INDEX
  --------------------------------------------------------------------

  sel-const-ivf : (K j : Nat)
                -> ((k : Nat) -> LeN K k -> Eq (WW.selC k) j)
                -> IvAll (suc a) (Ths j) -> EvConstN WW.ivf
  sel-const-ivf K j frz ia = go (Ths j) refl
    where
      ------------------------------------------------------------
      -- a constant argument: no drive, and none needed
      ------------------------------------------------------------
      go : (T : Tr (suc a)) -> Eq (Ths j) T -> EvConstN WW.ivf
      go (stop w) e = mkSigma K con
        where
          val : (k : Nat) -> LeN K k -> Eq (WW.ivf k) zero
          val k lk =
            Eq-trans (Eq-cong (\ z -> ivOf (Ths z) (WW.dep k z)) (frz k lk))
              (Eq-cong (\ T -> ivOf T (nOfOf (suc a) T (WW.L k))) e)

          con : (n : Nat) -> LeN K n -> Eq (WW.ivf n) (WW.ivf K)
          con n ln = Eq-trans (val n ln) (Eq-sym (val K (LeN-refl K)))
      ------------------------------------------------------------
      -- a genuine walk: driven linearly, so its own threshold fires
      ------------------------------------------------------------
      go (node ivj ivrj ovj contj) e = mkSigma M con
        where
          module SS = Sel j ivj ivrj ovj contj e

          ia' : Pair (EvConstN ivj)
                     ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
                      -> IvAll a (contj c lc v))
          ia' = Eq-transport (\ T -> IvAll (suc a) T) e ia

          Nj : Nat
          Nj = fst (fst ia')

          stabj : (n : Nat) -> LeN Nj n -> Eq (ivj n) (ivj Nj)
          stabj = snd (fst ia')

          M : Nat
          M = plus Nj K

          lKM : LeN K M
          lKM = plus-ge-r Nj K

          -- argument `j` is past its own threshold from `M` on
          deep : (n : Nat) -> LeN M n -> LeN Nj (WW.dep n j)
          deep n ln =
            LeN-trans {Nj} {WW.dep M j} {WW.dep n j}
              (LeN-trans {Nj} {plus Nj (WW.dep K j)} {WW.dep M j}
                (plus-ge-l Nj (WW.dep K j)) (SS.dep-drive K frz Nj))
              (dep-mono M n ln j)

          val : (n : Nat) -> LeN M n -> Eq (WW.ivf n) (ivj Nj)
          val n ln =
            Eq-trans (SS.ivfEq n (frz n (LeN-trans {K} {M} {n} lKM ln)))
              (stabj (nOf (suc a) ivj ivrj (WW.L n))
                (Eq-transport (\ z -> LeN Nj z) (SS.depEq n) (deep n ln)))

          con : (n : Nat) -> LeN M n -> Eq (WW.ivf n) (WW.ivf M)
          con n ln = Eq-trans (val n ln) (Eq-sym (val M (LeN-refl M)))

------------------------------------------------------------------------
-- WHAT REMAINS OF THE COMPOSITE'S INDEX CLAUSE
--
-- `SelStab` -- the demand `blockOn p Tg (vals k)` is eventually constant,
-- for the composite AND for every tower of continuations underneath it.
------------------------------------------------------------------------

SelStab : (p : Nat) -> Tr p -> (a : Nat) -> (Nat -> Tr a) -> Set
SelStab p Tg zero    Ths = Top
SelStab p Tg (suc a) Ths =
  Pair (Sigma Nat (\ K -> Sigma Nat (\ j ->
          (k : Nat) -> LeN K k -> Eq (W.selC p Tg a Ths k) j)))
       ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
        -> SelStab p Tg a (\ i -> contOf (Ths i) c lc v))

compTr-ivAll : (p : Nat) (Tg : Tr p) (a : Nat) (Ths : Nat -> Tr a)
             -> ((i : Nat) -> IvAll a (Ths i))
             -> SelStab p Tg a Ths
             -> IvAll a (compTr p Tg a Ths)
compTr-ivAll p Tg zero    Ths ia ss = tt
compTr-ivAll p Tg (suc a) Ths ia ss =
  mkSigma
    (CI.sel-const-ivf p Tg a Ths
      (fst (fst ss)) (fst (snd (fst ss))) (snd (snd (fst ss)))
      (ia (fst (snd (fst ss)))))
    (\ c lc v ->
       compTr-ivAll p Tg a (\ i -> contOf (Ths i) c lc v)
         (\ i -> ivAll-cont a (Ths i) (ia i) c lc v)
         (snd ss c lc v))
