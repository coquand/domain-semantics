{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PhiIter
--
-- THE REFINEMENT OF MP1 THAT THREADS BETWEEN THE TWO REFUTATIONS.
--
-- For a block  f_i (S x , y) = g_i (f_1 (x,y) , f_2 (x,y) , y)  the value
-- at the all-infinite point is the least fixed point of one monotone map
-- on D^2, and what has to be decided is whether the Kleene iteration
-- reaches it.  `BlkPass2` settles the LEVEL-BY-LEVEL question (`HPass`)
-- unconditionally; the GLOBAL bounded-or-unbounded verdict (`MPGrow.GV`)
-- is what computability as an element of `D` needs, and there are two
-- known refutations:
--
--   `BlkGrowFail`  --  (G) for the step traces does NOT give (G) for the
--                      block: it implies LPO.
--   `MutUOFail`    --  `PhiOK` for the step terms does NOT give `PhiOK`
--                      for the block: the height can be floor(m/2).
--
-- BUT THOSE REFUTE TWO DIFFERENT IMPLICATIONS, AND THE ONE IN BETWEEN IS
-- NOT REFUTED BY EITHER:
--
--     PhiOK for the step terms   ==>   GV for the block.
--
-- `MutUOFail` does not touch it (floor(m/2) is unbounded, so the BLOCK
-- still has GV), and `BlkGrowFail` does not touch it either, because its
-- step heights have GV but NOT PhiOK -- that is `BlkGrowPR.phiok-lpo`.
-- `PhiOK` is exactly the extra strength Proposition 1 gives for real
-- primitive recursive step terms and `GV` does not.
--
-- THIS FILE PROVES THE CONFIGURATION WHERE `BlkGrowFail` BITES.  Its
-- counterexample is the SELF-POINTING one: a component whose step term
-- ultimately reads its own value one depth down, so the height is a
-- deterministic monotone one-coordinate iteration
--
--     h (m+1) = phi (h m).
--
-- With only `GV phi` that is LPO.  With `PhiOK k phi` -- constant or
-- STRICTLY increasing past a threshold the proof PRODUCES -- it is
-- decided by `k+2` steps and one comparison:
--
--     iter-gv : PhiOK k phi -> GV h.
--
-- The two branches, and where the strength is spent:
--
--   * scan `k+1` steps.  Either the iteration REPEATED -- and a repeat is
--     a fixed point, by determinism (`freeze`), so `h` is bounded with the
--     sup attained -- or `h (k+1) >= k+1 > k`, so the orbit has entered
--     the region where `phi` is classified.
--   * `ConstFrom`: `phi` is `phi k` there, so `h` is constant from `k+2`
--     on.  BOUNDED.
--   * `StrictIncFrom`: put `x = h (k+1) >= k`.  Monotonicity of `h` gives
--     `phi x >= x`, so ONE comparison decides `phi x = x` -- a fixed
--     point, BOUNDED -- or `phi x > x`, and then strict increase
--     PROPAGATES: `phi (z+1) >= phi z + 1 > z+1` for every `z >= x`.  So
--     the orbit gains at least one per step for ever.  GROWING, with
--     period 1 and an explicit threshold.
--
-- Note what fails for `GV`: its growth clause gives `phi (p+n) >= phi n +1`
-- only along a fixed period, and says nothing about `phi x` versus `x`,
-- which is the comparison the orbit needs.  That is precisely the gap
-- `b n + n` exploits.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PhiIter where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; le-ne-lt ; nle-lt ; LeN-suc-not)
open import OBSTINATION.MP1 using (le-add)
open import OBSTINATION.MPGrow using (EvBndN ; GrowN ; GV)
open import OBSTINATION.Property using (PhiOK ; ConstFrom ; StrictIncFrom)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.PhiComp using (sinc-mono-le ; sinc-mono-lt)

module _ (phi : Nat -> Nat) (h : Nat -> Nat)
         (step : (m : Nat) -> Eq (h (suc m)) (phi (h m)))
         (mono1 : (m : Nat) -> LeN (h m) (h (suc m)))
         where

  ------------------------------------------------------------------
  -- the orbit is monotone
  ------------------------------------------------------------------

  h-mono : (m n : Nat) -> LeN m n -> LeN (h m) (h n)
  h-mono m zero     le =
    Eq-transport (\ z -> LeN (h z) (h zero))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (h zero))
  h-mono m (suc n) le = route (LeN-dec m n)
    where
      eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
      eq' zero    y       l nl = Empty-elim (nl tt)
      eq' (suc x) zero    l nl = Eq-cong suc (LeN-antisym {x} {zero} l tt)
      eq' (suc x) (suc y) l nl = Eq-cong suc (eq' x y l nl)

      route : Dec (LeN m n) -> LeN (h m) (h (suc n))
      route (yes l)  =
        LeN-trans {h m} {h n} {h (suc n)} (h-mono m n l) (mono1 n)
      route (no  nl) =
        Eq-transport (\ z -> LeN (h z) (h (suc n)))
          (Eq-sym (eq' m n le nl)) (LeN-refl (h (suc n)))

  ------------------------------------------------------------------
  -- A REPEAT IS A FIXED POINT
  --
  -- The step is a FUNCTION of the state, so `h (m+1) = h m` freezes the
  -- orbit for ever.  This is the only thing determinism is used for, and
  -- it is what makes "bounded" a Sigma-0-1 fact one can WITNESS.
  ------------------------------------------------------------------

  freeze : (m : Nat) -> Eq (h (suc m)) (h m)
         -> (t : Nat) -> Eq (h (plus t m)) (h m)
  freeze m e zero    = refl
  freeze m e (suc t) =
    Eq-trans (step (plus t m))
      (Eq-trans (Eq-cong phi (freeze m e t))
        (Eq-trans (Eq-sym (step m)) e))

  freeze-bnd : (m : Nat) -> Eq (h (suc m)) (h m) -> EvBndN h
  freeze-bnd m e = mkSigma m go
    where
      go : (s : Nat) -> LeN (h s) (h m)
      go s = route (LeN-dec s m)
        where
          route : Dec (LeN s m) -> LeN (h s) (h m)
          route (yes l)  = h-mono s m l
          route (no  nl) = rt (le-add m s (nle-lt' s m nl))
            where
              nle-lt' : (x y : Nat) -> Not (LeN x y) -> LeN y x
              nle-lt' x y nl' =
                LeN-trans {y} {suc y} {x} (LeN-suc y) (nle-lt x y nl')

              rt : Sigma Nat (\ t -> Eq s (plus t m)) -> LeN (h s) (h m)
              rt (mkSigma t es) =
                Eq-transport (\ z -> LeN (h z) (h m)) (Eq-sym es)
                  (Eq-transport (\ z -> LeN z (h m)) (Eq-sym (freeze m e t))
                    (LeN-refl (h m)))

  ------------------------------------------------------------------
  -- A BOUNDED SCAN: EITHER THE ORBIT REPEATED, OR IT HAS CLIMBED
  ------------------------------------------------------------------

  scan : (s : Nat)
       -> Or (Sigma Nat (\ m -> Eq (h (suc m)) (h m))) (LeN s (h s))
  scan zero    = inr tt
  scan (suc s) = route (scan s)
    where
      Res : Set
      Res = Or (Sigma Nat (\ m -> Eq (h (suc m)) (h m))) (LeN (suc s) (h (suc s)))

      route : Or (Sigma Nat (\ m -> Eq (h (suc m)) (h m))) (LeN s (h s)) -> Res
      route (inl w)  = inl w
      route (inr ls) = pick (EqNat-dec (h (suc s)) (h s))
        where
          pick : Dec (Eq (h (suc s)) (h s)) -> Res
          pick (yes e) = inl (mkSigma s e)
          pick (no ne) =
            inr
              (LeN-trans {suc s} {suc (h s)} {h (suc s)} ls
                (le-ne-lt (h s) (h (suc s)) (mono1 s) ne))

  ------------------------------------------------------------------
  -- STRICT INCREASE PROPAGATES UPWARD FROM ONE POINT
  ------------------------------------------------------------------

  sinc-above : (k : Nat) -> StrictIncFrom k phi
             -> (x : Nat) -> LeN k x -> LeN (suc x) (phi x)
             -> (t : Nat) -> LeN (suc (plus t x)) (phi (plus t x))
  sinc-above k si x lk gt zero    = gt
  sinc-above k si x lk gt (suc t) =
    LeN-trans {suc (suc (plus t x))} {suc (phi (plus t x))} {phi (suc (plus t x))}
      (sinc-above k si x lk gt t)
      (si (plus t x) (LeN-trans {k} {x} {plus t x} lk (plus-ge-r t x)))

  ------------------------------------------------------------------
  -- THE VERDICT
  ------------------------------------------------------------------

  iter-gv : (k : Nat) -> PhiOK k phi -> GV h
  iter-gv k pk = route (scan (suc k))
    where
      route : Or (Sigma Nat (\ m -> Eq (h (suc m)) (h m))) (LeN (suc k) (h (suc k)))
            -> GV h
      route (inl (mkSigma m e)) = inl (freeze-bnd m e)
      route (inr big) = split pk
        where
          x : Nat
          x = h (suc k)

          lkx : LeN k x
          lkx = LeN-trans {k} {suc k} {x} (LeN-suc k) big

          -- the next point is `phi x`, and the orbit is monotone
          nxt : Eq (h (suc (suc k))) (phi x)
          nxt = step (suc k)

          gex : LeN x (phi x)
          gex = Eq-transport (\ z -> LeN x z) nxt (mono1 (suc k))

          ----------------------------------------------------------
          -- CONSTANT past `k`: the orbit is `phi k` from `k+2` on
          ----------------------------------------------------------
          cst : ConstFrom k phi -> GV h
          cst cf = inl (mkSigma (suc (suc k)) go)
            where
              -- every later point is `phi k`
              hi : (n : Nat) -> LeN (suc k) n -> Eq (h (suc n)) (phi k)
              hi n ln =
                Eq-trans (step n)
                  (cf (h n) (LeN-trans {k} {x} {h n} lkx (h-mono (suc k) n ln)))

              go : (s : Nat) -> LeN (h s) (h (suc (suc k)))
              go s = pick (LeN-dec s (suc (suc k)))
                where
                  pick : Dec (LeN s (suc (suc k))) -> LeN (h s) (h (suc (suc k)))
                  pick (yes l)  = h-mono s (suc (suc k)) l
                  pick (no  nl) =
                    Eq-transport (\ z -> LeN z (h (suc (suc k))))
                      (Eq-sym same) (LeN-refl (h (suc (suc k))))
                    where
                      ls : LeN (suc (suc k)) s
                      ls =
                        LeN-trans {suc (suc k)} {suc (suc (suc k))} {s}
                          (LeN-suc (suc (suc k)))
                          (nle-lt s (suc (suc k)) nl)

                      -- `s` is a successor, since it is above `k+2`
                      shape : (u : Nat) -> LeN (suc (suc k)) u
                            -> Sigma Nat (\ v -> Pair (Eq u (suc v)) (LeN (suc k) v))
                      shape zero    ()
                      shape (suc v) l = mkSigma v (mkSigma refl l)

                      same : Eq (h s) (h (suc (suc k)))
                      same = rt (shape s ls)
                        where
                          rt : Sigma Nat (\ v -> Pair (Eq s (suc v)) (LeN (suc k) v))
                             -> Eq (h s) (h (suc (suc k)))
                          rt (mkSigma v (mkSigma es lv)) =
                            Eq-trans
                              (Eq-trans (Eq-cong h es) (hi v lv))
                              (Eq-sym (hi (suc k) (LeN-refl (suc k))))

          ----------------------------------------------------------
          -- STRICTLY INCREASING past `k`: ONE comparison decides
          ----------------------------------------------------------
          sic : StrictIncFrom k phi -> GV h
          sic si = pick (EqNat-dec (phi x) x)
            where
              pick : Dec (Eq (phi x) x) -> GV h
              -- a fixed point: BOUNDED
              pick (yes e) =
                inl (freeze-bnd (suc k)
                       (Eq-trans nxt e))
              -- `phi x > x`, and that propagates: GROWING, period 1
              pick (no ne) = inr (mkSigma (suc zero) (mkSigma (suc k) (mkSigma tt gw)))
                where
                  gt : LeN (suc x) (phi x)
                  gt = le-ne-lt x (phi x) gex (\ e -> ne e)

                  gw : (n : Nat) -> LeN (suc k) n -> LeN (suc (h n)) (h (suc n))
                  gw n ln = rt (le-add x (h n) (h-mono (suc k) n ln))
                    where
                      rt : Sigma Nat (\ t -> Eq (h n) (plus t x))
                         -> LeN (suc (h n)) (h (suc n))
                      rt (mkSigma t et) =
                        Eq-transport (\ z -> LeN (suc (h n)) z) (Eq-sym (step n))
                          (Eq-transport (\ z -> LeN (suc z) (phi (h n)))
                            (Eq-sym et)
                            (Eq-transport (\ z -> LeN (suc (plus t x)) (phi z))
                              (Eq-sym et)
                              (sinc-above k si x lkx gt t)))

          split : PhiOK k phi -> GV h
          split (inl cf) = cst cf
          split (inr si) = sic si

------------------------------------------------------------------------
-- `PhiOK` IS CLOSED UNDER COMPOSITION
--
-- which is what the CROSS-CYCLE configuration needs.  `BlkPass2` collapses
-- "component 0 ultimately reads component 1, component 1 reads component
-- 0" to a one-coordinate iteration of PERIOD 2 whose map is the composite
-- `phi_0 o phi_1`; `iter-gv` then applies to it, provided the composite is
-- still `PhiOK`.  It is:
--
--   * inner CONSTANT past k2  ==>  the composite is constant past k2,
--     whatever the outer one does;
--   * inner STRICTLY INCREASING  ==>  it is unbounded (`phi-escape`), so
--     past a COMPUTABLE stage `m0` its values are above the outer
--     threshold `k1`, and there the outer classification takes over --
--     constant gives constant, strictly increasing gives strictly
--     increasing (`sinc-mono-lt`).
--
-- Note `GV` is NOT closed under composition in this way: its growth
-- clause carries a period, and nothing relates `phi x` to `x`.
------------------------------------------------------------------------

phiok-comp : (p1 p2 : Nat -> Nat) (k1 k2 : Nat)
           -> PhiOK k1 p1 -> PhiOK k2 p2
           -> Sigma Nat (\ k -> PhiOK k (\ m -> p1 (p2 m)))
phiok-comp p1 p2 k1 k2 ok1 (inl cf2) =
  mkSigma k2 (inl (\ m lm -> Eq-cong p1 (cf2 m lm)))
phiok-comp p1 p2 k1 k2 ok1 (inr si2) = esc (phi-escape k2 p2 si2 k1)
  where
    Res : Set
    Res = Sigma Nat (\ k -> PhiOK k (\ m -> p1 (p2 m)))

    esc : Sigma Nat (\ m -> Pair (LeN k2 m) (LeN k1 (p2 m))) -> Res
    esc (mkSigma m0 (mkSigma lk2 lk1)) = route ok1
      where
        -- past `m0` the inner values are all above the outer threshold
        above : (m : Nat) -> LeN m0 m -> LeN k1 (p2 m)
        above m lm =
          LeN-trans {k1} {p2 m0} {p2 m} lk1
            (sinc-mono-le k2 p2 si2 m0 m lk2 lm)

        route : PhiOK k1 p1 -> Res
        route (inl cf1) = mkSigma m0 (inl go)
          where
            go : (m : Nat) -> LeN m0 m -> Eq (p1 (p2 m)) (p1 (p2 m0))
            go m lm =
              Eq-trans (cf1 (p2 m) (above m lm))
                (Eq-sym (cf1 (p2 m0) (above m0 (LeN-refl m0))))
        route (inr si1) = mkSigma m0 (inr go)
          where
            go : (m : Nat) -> LeN m0 m
               -> LeN (suc (p1 (p2 m))) (p1 (p2 (suc m)))
            go m lm =
              sinc-mono-lt k1 p1 si1 (p2 m) (p2 (suc m)) (above m lm)
                (si2 m (LeN-trans {k2} {m0} {m} lk2 lm))
