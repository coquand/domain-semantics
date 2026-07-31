{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkVerdict2
--
-- **PhiOK FOR THE STEP TERMS GIVES THE BOUNDED-OR-UNBOUNDED VERDICT FOR
-- THE BLOCK, AT r = 2.**
--
--     vd2-blk : ((j : Nat) -> Sigma Nat (\ k -> PhiOK k (kv j)))
--             -> (j : Nat) -> LeN (suc j) two
--             -> Vd2 (\ m -> HGT m j)
--
-- with
--
--     Unb h = (K : Nat) -> Sigma Nat (\ s -> h s > K)
--     Vd2 h = EvBndN h  +  Unb h
--
-- `Vd2` is exactly what naming the value at the all-infinite point
-- requires: `EvBndN` gives `S^(h M)(bot)`, `Unb` gives `S^w(bot)`.  It is
-- weaker than `MPGrow.GV` -- no rate is claimed -- and that is what makes
-- it survive the subsequence steps below, where `GV`'s period would have
-- to be rescaled.
--
-- THIS IS THE IMPLICATION THAT THREADS BETWEEN THE TWO REFUTATIONS:
--
--   `BlkGrowFail`  --  (G) for the step traces does NOT give (G) for the
--                      block.  Its step heights have (G) but NOT `PhiOK`
--                      (`BlkGrowPR.phiok-lpo`), so it does not apply here.
--   `MutUOFail`    --  `PhiOK` for the step terms does NOT give `PhiOK`
--                      for the block: the block height can be floor(m/2).
--                      That is unbounded, so `Vd2` still holds -- and the
--                      conclusion here is `Vd2`, not `PhiOK`.
--
-- `PhiOK` is exactly the extra strength Proposition 1 gives for REAL
-- primitive recursive step terms and `GV` does not.
--
-- THE ASSEMBLY is `BlkPass2`'s, one case at a time, with `Vd2` in place of
-- `HPass`.  `BlkPass2.shape` already sorts each component into
--
--   Stab  -- the height is eventually constant (a frozen component, or one
--            whose ultimate demand is a parameter);
--   Self  -- `HGT (m+1) j = phi j (HGT m j)` past a threshold;
--   Cross -- `HGT (m+1) j = phi j (HGT m (oth j))` past a threshold;
--
-- and then
--
--   Stab           ==>  `vd2-evconst`;
--   Self           ==>  `PhiIter.iter-gv` on the one-coordinate iteration,
--                       whose map `phi j` is `PhiOK` by `phiok-shift`;
--   Cross onto a settled component ==> `vd2-comp` (the verdict of the other
--                       component composed with a `PhiOK` map) + `vd2-tail`;
--   CROSS-CYCLE     ==> compose around the cycle, `PhiIter.phiok-comp`
--                       keeps the composite `PhiOK`, and `iter-gv` again.
--
-- `BlkPass2`'s own hypothesis `HPass (kv j)` is implied by `PhiOK` plus
-- monotonicity (`phiok-gv` then `MPGrow.gv-pass`), so its `shape` and its
-- affine law are reused verbatim.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkVerdict2 where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-mono ; plus-suc-r ; nle-lt)
open import OBSTINATION.MPPass using (Mono ; HPass ; plus-ge-l ; double ; double-ge)
open import OBSTINATION.MPGrow using (EvBndN ; GrowN ; GV ; grow-unb ; gv-pass)
open import OBSTINATION.Property using (PhiOK ; ConstFrom ; StrictIncFrom)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.PhiComp using (sinc-mono-le)
open import OBSTINATION.PhiIter using (iter-gv ; phiok-comp)
open import OBSTINATION.BlkTraceR using (q)
open import OBSTINATION.MainBlk2 using
  (one ; two ; oth ; oth-range ; hgt ; hgt-mono)
open import OBSTINATION.BlkPass2 using
  (oth-oth ; Stab ; Self ; Cross ; shape ; phi ; phi-mono ; D)

------------------------------------------------------------------------
-- THE VERDICT THAT NAMES THE VALUE
------------------------------------------------------------------------

Unb : (Nat -> Nat) -> Set
Unb h = (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (h s))

Vd2 : (Nat -> Nat) -> Set
Vd2 h = Or (EvBndN h) (Unb h)

gv-vd2 : (h : Nat -> Nat) -> GV h -> Vd2 h
gv-vd2 h (inl bd) = inl bd
gv-vd2 h (inr gr) = inr (grow-unb h gr)

vd2-cong : (u v : Nat -> Nat) -> ((k : Nat) -> Eq (u k) (v k)) -> Vd2 u -> Vd2 v
vd2-cong u v e (inl (mkSigma M bd)) = inl (mkSigma M bd')
  where
    bd' : (s : Nat) -> LeN (v s) (v M)
    bd' s =
      Eq-transport (\ z -> LeN z (v M)) (e s)
        (Eq-transport (\ z -> LeN (u s) z) (e M) (bd s))
vd2-cong u v e (inr un) = inr un'
  where
    un' : (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (v s))
    un' K = rt (un K)
      where
        rt : Sigma Nat (\ s -> LeN (suc K) (u s))
           -> Sigma Nat (\ s -> LeN (suc K) (v s))
        rt (mkSigma s big) =
          mkSigma s (Eq-transport (\ z -> LeN (suc K) z) (e s) big)

------------------------------------------------------------------------
-- EVENTUALLY CONSTANT
------------------------------------------------------------------------

vd2-evconst : (h : Nat -> Nat) -> Mono h -> (T : Nat)
            -> ((n : Nat) -> LeN T n -> Eq (h n) (h T)) -> Vd2 h
vd2-evconst h mh T ev = inl (mkSigma T go)
  where
    go : (s : Nat) -> LeN (h s) (h T)
    go s = route (LeN-dec s T)
      where
        route : Dec (LeN s T) -> LeN (h s) (h T)
        route (yes l)  = mh s T l
        route (no  nl) =
          Eq-transport (\ z -> LeN z (h T)) (Eq-sym (ev s ls)) (LeN-refl (h T))
          where
            ls : LeN T s
            ls = LeN-trans {T} {suc T} {s} (LeN-suc T) (nle-lt s T nl)

------------------------------------------------------------------------
-- A SUBSEQUENCE
--
-- This is where `Vd2` is easier than `GV`: `Unb` transports along any
-- subsequence with no rescaling, whereas `GrowN`'s period would have to
-- be multiplied by the subsequence's step.
------------------------------------------------------------------------

vd2-sub : (h : Nat -> Nat) -> Mono h -> (g : Nat -> Nat)
        -> ((k : Nat) -> LeN k (g k))
        -> Vd2 (\ k -> h (g k)) -> Vd2 h
vd2-sub h mh g gge (inl (mkSigma M bd)) = inl (mkSigma (g M) go)
  where
    go : (s : Nat) -> LeN (h s) (h (g M))
    go s = LeN-trans {h s} {h (g s)} {h (g M)} (mh s (g s) (gge s)) (bd s)
vd2-sub h mh g gge (inr un) = inr go
  where
    go : (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (h s))
    go K = rt (un K)
      where
        rt : Sigma Nat (\ k -> LeN (suc K) (h (g k)))
           -> Sigma Nat (\ s -> LeN (suc K) (h s))
        rt (mkSigma k big) = mkSigma (g k) big

------------------------------------------------------------------------
-- A TAIL
------------------------------------------------------------------------

vd2-tail : (h F : Nat -> Nat) -> Mono h -> Mono F -> (T : Nat)
         -> ((m : Nat) -> LeN T m -> Eq (h (suc m)) (F m))
         -> Vd2 F -> Vd2 h
vd2-tail h F mh mF T eq (inl (mkSigma M bd)) = inl (mkSigma (suc M') go)
  where
    M' : Nat
    M' = maxN M T

    -- the bound is attained above `T` as well
    same : Eq (h (suc M')) (F M')
    same = eq M' (maxN-le-r M T)

    go : (s : Nat) -> LeN (h s) (h (suc M'))
    go s =
      Eq-transport (\ z -> LeN (h s) z) (Eq-sym same)
        (LeN-trans {h s} {h (suc s')} {F M'}
          (mh s (suc s')
            (LeN-trans {s} {s'} {suc s'} (maxN-le-l s T) (LeN-suc s')))
          (Eq-transport (\ z -> LeN z (F M')) (Eq-sym (eq s' (maxN-le-r s T)))
            (LeN-trans {F s'} {F M} {F M'} (bd s') (mF M M' (maxN-le-l M T)))))
      where
        s' : Nat
        s' = maxN s T
vd2-tail h F mh mF T eq (inr un) = inr go
  where
    go : (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (h s))
    go K = rt (un K)
      where
        rt : Sigma Nat (\ s -> LeN (suc K) (F s))
           -> Sigma Nat (\ s -> LeN (suc K) (h s))
        rt (mkSigma s big) = mkSigma (suc s') pass
          where
            s' : Nat
            s' = maxN s T

            pass : LeN (suc K) (h (suc s'))
            pass =
              Eq-transport (\ z -> LeN (suc K) z) (Eq-sym (eq s' (maxN-le-r s T)))
                (LeN-trans {suc K} {F s} {F s'} big (mF s s' (maxN-le-l s T)))

------------------------------------------------------------------------
-- `PhiOK` PLUMBING
------------------------------------------------------------------------

-- a monotone `PhiOK` map has the verdict outright
phiok-gv : (f : Nat -> Nat) -> Mono f -> (k : Nat) -> PhiOK k f -> GV f
phiok-gv f mf k (inl cf) = inl (mkSigma k go)
  where
    go : (s : Nat) -> LeN (f s) (f k)
    go s = route (LeN-dec s k)
      where
        route : Dec (LeN s k) -> LeN (f s) (f k)
        route (yes l)  = mf s k l
        route (no  nl) =
          Eq-transport (\ z -> LeN z (f k)) (Eq-sym (cf s ls)) (LeN-refl (f k))
          where
            ls : LeN k s
            ls = LeN-trans {k} {suc k} {s} (LeN-suc k) (nle-lt s k nl)
phiok-gv f mf k (inr si) = inr (mkSigma (suc zero) (mkSigma k (mkSigma tt si)))

-- precomposing with a shift keeps `PhiOK`
phiok-shift : (f : Nat -> Nat) (Dd k : Nat) -> PhiOK k f
            -> PhiOK k (\ x -> f (plus Dd x))
phiok-shift f Dd k (inl cf) = inl go
  where
    go : (m : Nat) -> LeN k m -> Eq (f (plus Dd m)) (f (plus Dd k))
    go m lm =
      Eq-trans (cf (plus Dd m) (LeN-trans {k} {m} {plus Dd m} lm (plus-ge-r Dd m)))
        (Eq-sym (cf (plus Dd k) (plus-ge-r Dd k)))
phiok-shift f Dd k (inr si) = inr go
  where
    go : (m : Nat) -> LeN k m
       -> LeN (suc (f (plus Dd m))) (f (plus Dd (suc m)))
    go m lm =
      Eq-transport (\ z -> LeN (suc (f (plus Dd m))) (f z))
        (Eq-sym (plus-suc-r Dd m))
        (si (plus Dd m) (LeN-trans {k} {m} {plus Dd m} lm (plus-ge-r Dd m)))

------------------------------------------------------------------------
-- COMPOSING A VERDICT WITH A `PhiOK` MAP
--
-- The other component's verdict, fed through this one's step map.  A
-- BOUNDED argument gives a bounded value by monotonicity; an UNBOUNDED
-- one is where `PhiOK` is spent: constant past `k` gives a constant
-- value, strictly increasing past `k` gives an unbounded one.
------------------------------------------------------------------------

vd2-comp : (f w : Nat -> Nat) -> Mono f -> Mono w -> (k : Nat) -> PhiOK k f
         -> Vd2 w -> Vd2 (\ m -> f (w m))
vd2-comp f w mf mw k pk (inl (mkSigma M bd)) = inl (mkSigma M go)
  where
    go : (s : Nat) -> LeN (f (w s)) (f (w M))
    go s = mf (w s) (w M) (bd s)
vd2-comp f w mf mw k pk (inr un) = route pk
  where
    -- the argument passes `k` at a computable stage
    big : Sigma Nat (\ s0 -> LeN k (w s0))
    big = rt (un k)
      where
        rt : Sigma Nat (\ s -> LeN (suc k) (w s)) -> Sigma Nat (\ s0 -> LeN k (w s0))
        rt (mkSigma s0 b) =
          mkSigma s0 (LeN-trans {k} {suc k} {w s0} (LeN-suc k) b)

    route : PhiOK k f -> Vd2 (\ m -> f (w m))
    ------------------------------------------------------------
    -- constant past `k`: the value settles
    ------------------------------------------------------------
    route (inl cf) = go big
      where
        go : Sigma Nat (\ s0 -> LeN k (w s0)) -> Vd2 (\ m -> f (w m))
        go (mkSigma s0 lk) = inl (mkSigma s0 bnd)
          where
            atk : (s : Nat) -> LeN k (w s) -> Eq (f (w s)) (f k)
            atk s l = cf (w s) l

            bnd : (s : Nat) -> LeN (f (w s)) (f (w s0))
            bnd s = pick (LeN-dec (w s) (w s0))
              where
                pick : Dec (LeN (w s) (w s0)) -> LeN (f (w s)) (f (w s0))
                pick (yes l) = mf (w s) (w s0) l
                pick (no nl) =
                  Eq-transport (\ z -> LeN z (f (w s0))) (Eq-sym same)
                    (LeN-refl (f (w s0)))
                  where
                    lks : LeN k (w s)
                    lks =
                      LeN-trans {k} {w s0} {w s} lk
                        (LeN-trans {w s0} {suc (w s0)} {w s}
                          (LeN-suc (w s0)) (nle-lt (w s) (w s0) nl))

                    same : Eq (f (w s)) (f (w s0))
                    same = Eq-trans (atk s lks) (Eq-sym (atk s0 lk))
    ------------------------------------------------------------
    -- strictly increasing past `k`: the value is unbounded too
    ------------------------------------------------------------
    route (inr si) = inr go
      where
        go : (K : Nat) -> Sigma Nat (\ s -> LeN (suc K) (f (w s)))
        go K = esc (phi-escape k f si (suc K))
          where
            esc : Sigma Nat (\ m -> Pair (LeN k m) (LeN (suc K) (f m)))
                -> Sigma Nat (\ s -> LeN (suc K) (f (w s)))
            esc (mkSigma m (mkSigma lkm bigm)) = rt (un m)
              where
                rt : Sigma Nat (\ s -> LeN (suc m) (w s))
                   -> Sigma Nat (\ s -> LeN (suc K) (f (w s)))
                rt (mkSigma s bs) =
                  mkSigma s
                    (LeN-trans {suc K} {f m} {f (w s)} bigm
                      (sinc-mono-le k f si m (w s) lkm
                        (LeN-trans {m} {suc m} {w s} (LeN-suc m) bs)))

------------------------------------------------------------------------
-- THE ASSEMBLY
------------------------------------------------------------------------

module BLK (a : Nat)
           (iv : Nat -> Nat -> Nat)
           (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
           (kv : Nat -> Nat -> Nat)
           (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
           (Y : Nat -> Nat)
           (N I : Nat -> Nat)
           (iv-stab : (j n : Nat) -> LeN (N j) n -> Eq (iv j n) (I j))
           (pverd : (j : Nat) -> Sigma Nat (\ k -> PhiOK k (kv j)))
           where

  ------------------------------------------------------------------
  -- `PhiOK` implies `BlkPass2`'s own hypothesis, so its case analysis
  -- is reused verbatim
  ------------------------------------------------------------------

  kvm : (j : Nat) -> Mono (kv j)
  kvm j = kv-mono j

  hverd : (j : Nat) -> HPass (kv j)
  hverd j = rt (pverd j)
    where
      rt : Sigma Nat (\ k -> PhiOK k (kv j)) -> HPass (kv j)
      rt (mkSigma k pk) = gv-pass (kv j) (phiok-gv (kv j) (kvm j) k pk)

  HGT : Nat -> Nat -> Nat
  HGT = hgt a iv ivr kv kv-mono Y N I iv-stab

  HGTm : (j : Nat) -> LeN (suc j) two -> Mono (\ m -> HGT m j)
  HGTm j lj = hgt-mono a iv ivr kv kv-mono Y N I iv-stab j lj

  PH : Nat -> Nat -> Nat
  PH = phi a iv ivr kv kv-mono Y N I iv-stab hverd

  PHm : (j : Nat) -> Mono (PH j)
  PHm = phi-mono a iv ivr kv kv-mono Y N I iv-stab hverd

  DD : Nat -> Nat
  DD = D a iv ivr kv kv-mono Y N I iv-stab hverd

  ST : Nat -> Set
  ST = Stab a iv ivr kv kv-mono Y N I iv-stab hverd

  SE : Nat -> Set
  SE = Self a iv ivr kv kv-mono Y N I iv-stab hverd

  CR : Nat -> Set
  CR = Cross a iv ivr kv kv-mono Y N I iv-stab hverd

  SH : (j : Nat) -> LeN (suc j) two -> Or (ST j) (Or (SE j) (CR j))
  SH = shape a iv ivr kv kv-mono Y N I iv-stab hverd

  -- the step map of a component past its threshold is `PhiOK`
  phok : (j : Nat) -> Sigma Nat (\ k -> PhiOK k (PH j))
  phok j = rt (pverd j)
    where
      rt : Sigma Nat (\ k -> PhiOK k (kv j))
         -> Sigma Nat (\ k -> PhiOK k (PH j))
      rt (mkSigma k pk) = mkSigma k (phiok-shift (kv j) (DD j) k pk)

  ------------------------------------------------------------------
  -- STAB: an eventually constant height
  ------------------------------------------------------------------

  vd2-stab : (j : Nat) -> LeN (suc j) two -> ST j -> Vd2 (\ m -> HGT m j)
  vd2-stab j lj (mkSigma T same) =
    vd2-evconst (\ m -> HGT m j) (HGTm j lj) (suc T) ev
    where
      ev : (n : Nat) -> LeN (suc T) n -> Eq (HGT n j) (HGT (suc T) j)
      ev zero    ()
      ev (suc m) ln = same m ln

  ------------------------------------------------------------------
  -- SELF: the one-coordinate iteration -- where `BlkGrowFail` bites,
  -- and where `PhiOK` pays
  ------------------------------------------------------------------

  vd2-self : (j : Nat) -> LeN (suc j) two -> SE j -> Vd2 (\ m -> HGT m j)
  vd2-self j lj (mkSigma T sf) =
    vd2-sub (\ m -> HGT m j) (HGTm j lj) g gge
      (gv-vd2 u (go (phok j)))
    where
      g : Nat -> Nat
      g k = plus k T

      gge : (k : Nat) -> LeN k (g k)
      gge k = plus-ge-l k T

      u : Nat -> Nat
      u k = HGT (plus k T) j

      rec : (m : Nat) -> Eq (u (suc m)) (PH j (u m))
      rec m = sf (plus m T) (plus-ge-r m T)

      umono : (m : Nat) -> LeN (u m) (u (suc m))
      umono m =
        HGTm j lj (plus m T) (suc (plus m T)) (LeN-suc (plus m T))

      go : Sigma Nat (\ k -> PhiOK k (PH j)) -> GV u
      go (mkSigma k pk) = iter-gv (PH j) u rec umono k pk

  ------------------------------------------------------------------
  -- CROSS onto a component whose verdict is already known
  ------------------------------------------------------------------

  vd2-cross-from : (j : Nat) -> LeN (suc j) two -> CR j
                 -> Vd2 (\ m -> HGT m (oth j)) -> Vd2 (\ m -> HGT m j)
  vd2-cross-from j lj (mkSigma T cr) vw =
    vd2-tail (\ m -> HGT m j) F (HGTm j lj) mF T cr (go (phok j))
    where
      F : Nat -> Nat
      F m = PH j (HGT m (oth j))

      mF : Mono F
      mF m m' le =
        PHm j (HGT m (oth j)) (HGT m' (oth j))
          (HGTm (oth j) (oth-range j) m m' le)

      go : Sigma Nat (\ k -> PhiOK k (PH j)) -> Vd2 F
      go (mkSigma k pk) =
        vd2-comp (PH j) (\ m -> HGT m (oth j)) (PHm j)
          (HGTm (oth j) (oth-range j)) k pk vw

  ------------------------------------------------------------------
  -- THE CROSS-CYCLE: compose around it, `PhiOK` survives
  ------------------------------------------------------------------

  vd2-cycle : (j : Nat) -> LeN (suc j) two -> CR j -> CR (oth j)
            -> Vd2 (\ m -> HGT m j)
  vd2-cycle j lj (mkSigma T cr) (mkSigma T' cr') =
    vd2-sub (\ m -> HGT m j) (HGTm j lj) g gge (gv-vd2 u (go (comp (phok j) (phok (oth j)))))
    where
      T2 : Nat
      T2 = maxN T T'

      lT : LeN T T2
      lT = maxN-le-l T T'

      lT' : LeN T' T2
      lT' = maxN-le-r T T'

      g : Nat -> Nat
      g k = plus (double k) T2

      gge : (k : Nat) -> LeN k (g k)
      gge k =
        LeN-trans {k} {double k} {plus (double k) T2}
          (double-ge k) (plus-ge-l (double k) T2)

      u : Nat -> Nat
      u k = HGT (g k) j

      psi : Nat -> Nat
      psi x = PH j (PH (oth j) x)

      rec : (k : Nat) -> Eq (u (suc k)) (psi (u k))
      rec k =
        Eq-trans (cr (suc m) (LeN-trans {T} {m} {suc m} lm (LeN-suc m)))
          (Eq-cong (PH j)
            (Eq-trans (cr' m lm')
              (Eq-cong (PH (oth j))
                (Eq-cong (\ z -> HGT m z) (oth-oth j lj)))))
        where
          m : Nat
          m = plus (double k) T2

          lm : LeN T m
          lm = LeN-trans {T} {T2} {m} lT (plus-ge-r (double k) T2)

          lm' : LeN T' m
          lm' = LeN-trans {T'} {T2} {m} lT' (plus-ge-r (double k) T2)

      umono : (k : Nat) -> LeN (u k) (u (suc k))
      umono k =
        HGTm j lj (g k) (g (suc k))
          (Eq-transport (\ z -> LeN (g k) (plus z T2))
            (Eq-sym (dbl k)) (plus-mono (double k) (suc (suc (double k))) T2 T2
              (LeN-trans {double k} {suc (double k)} {suc (suc (double k))}
                (LeN-suc (double k)) (LeN-suc (suc (double k))))
              (LeN-refl T2)))
        where
          dbl : (n : Nat) -> Eq (double (suc n)) (suc (suc (double n)))
          dbl n = refl

      comp : Sigma Nat (\ k -> PhiOK k (PH j))
           -> Sigma Nat (\ k -> PhiOK k (PH (oth j)))
           -> Sigma Nat (\ k -> PhiOK k psi)
      comp (mkSigma k1 p1) (mkSigma k2 p2) =
        phiok-comp (PH j) (PH (oth j)) k1 k2 p1 p2

      go : Sigma Nat (\ k -> PhiOK k psi) -> GV u
      go (mkSigma k pk) = iter-gv psi u rec umono k pk

  ------------------------------------------------------------------
  -- THE VERDICT FOR BOTH COMPONENTS
  ------------------------------------------------------------------

  vd2-blk : (j : Nat) -> LeN (suc j) two -> Vd2 (\ m -> HGT m j)
  vd2-blk j lj = route (SH j lj)
    where
      lc : LeN (suc (oth j)) two
      lc = oth-range j

      other : Or (ST (oth j)) (Or (SE (oth j)) (CR (oth j)))
            -> Or (Vd2 (\ m -> HGT m (oth j))) (CR (oth j))
      other (inl st)        = inl (vd2-stab (oth j) lc st)
      other (inr (inl sf))  = inl (vd2-self (oth j) lc sf)
      other (inr (inr crs)) = inr crs

      route : Or (ST j) (Or (SE j) (CR j)) -> Vd2 (\ m -> HGT m j)
      route (inl st)       = vd2-stab j lj st
      route (inr (inl sf)) = vd2-self j lj sf
      route (inr (inr cr)) = cross (other (SH (oth j) lc))
        where
          cross : Or (Vd2 (\ m -> HGT m (oth j))) (CR (oth j))
                -> Vd2 (\ m -> HGT m j)
          cross (inl vw)  = vd2-cross-from j lj cr vw
          cross (inr crs) = vd2-cycle j lj cr crs
