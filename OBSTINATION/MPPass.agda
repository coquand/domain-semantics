{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MPPass
--
-- THE HEIGHT CLAUSE (H) OF THE MAIN PROPERTY, AND ITS TOOLKIT.
--
-- A function with a trace is a pair (iv, kv): at step n of its demand walk
-- it asks for coordinate `iv n` and its output has height `kv n`.  THE MAIN
-- PROPERTY is
--
--     MP iv kv = (I) EvConstN iv          -- the sequentiality index settles
--              & (H) HPass  kv            -- the height verdict, LEVEL BY LEVEL
--
--     HPass k = (K : Nat) -> Or (Sigma s. k s > K) ((s : Nat) -> k s <= K)
--
-- (H) answers each level on demand: "here is a step whose height exceeds K",
-- or "no step does".  It is NOT the global verdict "bounded or unbounded"
-- (the old `MainComp.HV`, and the bounded side of `MPGrow.GV`), which asks in
-- addition whether the first answer comes back for EVERY K -- one quantifier
-- more, and the one that cannot be had: `BlkGrowFail` exhibits a block, with
-- (I) and (G) for its step terms, whose height satisfies (H) outright and for
-- which the global verdict is LPO.
--
-- What makes (H) the right clause is that it is exactly what the composition
-- proof consumes (`MainComp.hdec`) and that it holds unconditionally for a
-- deterministic monotone iteration (`IterF.it-pass`), which is the shape a
-- block component's height takes past its threshold.
--
-- The toolkit here is what the two closure proofs need:
--
--     hpass-const, hpass-ge      -- the basic functions
--     hpass-evconst              -- anything eventually constant
--     hpass-cong, hpass-sub      -- transport, and along a subsequence
--     find-least                 -- the LEAST level witness (needs monotony)
--     IterF                      -- a deterministic monotone iteration
--     hpass-comp2                -- k (D + w m), from (H) of k and of w
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MPPass where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-mono ; plus-suc-r ; nle-lt ; LeN-suc-not)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus-ge-l : (x y : Nat) -> LeN x (plus x y)
plus-ge-l zero    y = tt
plus-ge-l (suc x) y = plus-ge-l x y

plus-assoc : (x y z : Nat) -> Eq (plus (plus x y) z) (plus x (plus y z))
plus-assoc zero    y z = refl
plus-assoc (suc x) y z = Eq-cong suc (plus-assoc x y z)

plus-zero-r : (x : Nat) -> Eq (plus x zero) x
plus-zero-r zero    = refl
plus-zero-r (suc x) = Eq-cong suc (plus-zero-r x)

plus-comm : (x y : Nat) -> Eq (plus x y) (plus y x)
plus-comm zero    y = Eq-sym (plus-zero-r y)
plus-comm (suc x) y =
  Eq-trans (Eq-cong suc (plus-comm x y)) (Eq-sym (plus-suc-r y x))

le-nle-eq : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
le-nle-eq zero    y       l nl = Empty-elim (nl tt)
le-nle-eq (suc x) zero    l nl = Eq-cong suc (LeN-antisym {x} {zero} l tt)
le-nle-eq (suc x) (suc y) l nl = Eq-cong suc (le-nle-eq x y l nl)

-- m <= n gives the difference explicitly
le-plus : (m n : Nat) -> LeN m n -> Sigma Nat (\ k -> Eq (plus k m) n)
le-plus m zero    le =
  mkSigma zero (LeN-antisym {m} {zero} le tt)
le-plus m (suc n) le = route (LeN-dec m n)
  where
    route : Dec (LeN m n) -> Sigma Nat (\ k -> Eq (plus k m) (suc n))
    route (yes l)  = grow (le-plus m n l)
      where
        grow : Sigma Nat (\ k -> Eq (plus k m) n) ->
               Sigma Nat (\ k -> Eq (plus k m) (suc n))
        grow (mkSigma k e) = mkSigma (suc k) (Eq-cong suc e)
    route (no  nl) =
      mkSigma zero (le-nle-eq m n le nl)

double : Nat -> Nat
double zero    = zero
double (suc m) = suc (suc (double m))

double-ge : (m : Nat) -> LeN m (double m)
double-ge zero    = tt
double-ge (suc m) = LeN-trans {m} {double m} {suc (double m)}
                      (double-ge m) (LeN-suc (double m))

------------------------------------------------------------------------
-- MONOTONE HEIGHTS, AND THE CLAUSE ITSELF
------------------------------------------------------------------------

Mono : (Nat -> Nat) -> Set
Mono k = (n n' : Nat) -> LeN n n' -> LeN (k n) (k n')

HPass : (Nat -> Nat) -> Set
HPass k =
  (K : Nat) ->
  Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K)

-- THE MAIN PROPERTY of a function with a trace
MP : (Nat -> Nat) -> (Nat -> Nat) -> Set
MP iv kv = Pair (EvConstN iv) (HPass kv)

------------------------------------------------------------------------
-- TRANSPORT
------------------------------------------------------------------------

hpass-cong : (k k' : Nat -> Nat) -> ((n : Nat) -> Eq (k n) (k' n)) ->
  HPass k -> HPass k'
hpass-cong k k' e h K = route (h K)
  where
    route :
      Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K) ->
      Or (Sigma Nat (\ s -> LeN (suc K) (k' s))) ((s : Nat) -> LeN (k' s) K)
    route (inl (mkSigma s big)) =
      inl (mkSigma s (Eq-transport (\ z -> LeN (suc K) z) (e s) big))
    route (inr bnd) =
      inr (\ s -> Eq-transport (\ z -> LeN z K) (e s) (bnd s))

-- (H) along a subsequence that outruns the index gives (H)
hpass-sub : (k : Nat -> Nat) -> Mono k -> (g : Nat -> Nat) ->
  ((m : Nat) -> LeN m (g m)) -> HPass (\ m -> k (g m)) -> HPass k
hpass-sub k mk g gge h K = route (h K)
  where
    route :
      Or (Sigma Nat (\ s -> LeN (suc K) (k (g s))))
         ((s : Nat) -> LeN (k (g s)) K) ->
      Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K)
    route (inl (mkSigma s big)) = inl (mkSigma (g s) big)
    route (inr bnd) =
      inr (\ m -> LeN-trans {k m} {k (g m)} {K} (mk m (g m) (gge m)) (bnd m))

------------------------------------------------------------------------
-- THE EASY CASES OF (H)
------------------------------------------------------------------------

hpass-const : (c : Nat) -> HPass (\ _ -> c)
hpass-const c K = route (LeN-dec c K)
  where
    route : Dec (LeN c K) ->
      Or (Sigma Nat (\ s -> LeN (suc K) c)) ((s : Nat) -> LeN c K)
    route (yes l)  = inr (\ s -> l)
    route (no  nl) = inl (mkSigma zero (nle-lt c K nl))

-- a height at least as big as the step number passes every level at once
hpass-ge : (k : Nat -> Nat) -> ((n : Nat) -> LeN n (k n)) -> HPass k
hpass-ge k le K = inl (mkSigma (suc K) (le (suc K)))

hpass-evconst : (k : Nat -> Nat) -> Mono k -> (T : Nat) ->
  ((n : Nat) -> LeN T n -> Eq (k n) (k T)) -> HPass k
hpass-evconst k mk T ev K = route (LeN-dec (k T) K)
  where
    route : Dec (LeN (k T) K) ->
      Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K)
    route (no  nl) = inl (mkSigma T (nle-lt (k T) K nl))
    route (yes l)  = inr bnd
      where
        bnd : (s : Nat) -> LeN (k s) K
        bnd s = pick (LeN-dec T s)
          where
            pick : Dec (LeN T s) -> LeN (k s) K
            pick (yes ls) =
              Eq-transport (\ z -> LeN z K) (Eq-sym (ev s ls)) l
            pick (no  nls) =
              LeN-trans {k s} {k T} {K}
                (mk s T (LeN-trans {s} {suc s} {T} (LeN-suc s) (nle-lt T s nls))) l

------------------------------------------------------------------------
-- THE LEAST LEVEL WITNESS
--
-- `HPass k` at K hands over SOME step whose height passes K; for the
-- composition of two heights one needs the FIRST one, so that everything
-- strictly below it is known to stay at or below K.  Bounded minimisation,
-- using monotony to bound the whole prefix at once.
------------------------------------------------------------------------

find-least : (k : Nat -> Nat) -> Mono k -> (K s : Nat) -> LeN (suc K) (k s) ->
  Sigma Nat (\ n0 -> Pair (LeN (suc K) (k n0))
                          ((n : Nat) -> LeN (suc n) n0 -> LeN (k n) K))
find-least k mk K zero    big = mkSigma zero (mkSigma big (\ n ()))
find-least k mk K (suc s) big = route (LeN-dec (suc K) (k s))
  where
    route : Dec (LeN (suc K) (k s)) ->
      Sigma Nat (\ n0 -> Pair (LeN (suc K) (k n0))
                              ((n : Nat) -> LeN (suc n) n0 -> LeN (k n) K))
    route (yes p)  = find-least k mk K s p
    route (no  np) = mkSigma (suc s) (mkSigma big rest)
      where
        les : LeN (k s) K
        les = nle-lt (suc K) (k s) np

        rest : (n : Nat) -> LeN (suc n) (suc s) -> LeN (k n) K
        rest n ln = LeN-trans {k n} {k s} {K} (mk n s ln) les

------------------------------------------------------------------------
-- A DETERMINISTIC MONOTONE ITERATION ALWAYS HAS (H)
--
-- `it m` is the m-th iterate of a monotone `phi` from `x0`.  Nothing else is
-- assumed, and yet:
--
--   * a repeat is a FIXED point, so the iteration freezes for ever
--     (`it-freeze`);
--   * hence if it has not passed K after K+1 steps it never will, since
--     until it freezes it goes up by at least one each step (`it-scan`).
--
-- This is the base case of the recursion clause: past its threshold, a block
-- component's height is exactly such an iteration (period 1 if it reads
-- itself, period 2 around a cross-cycle).  Note the CONTRAST with the global
-- verdict, which for the very same iteration is LPO (`BlkGrowFail`).
------------------------------------------------------------------------

module IterF (phi : Nat -> Nat) (phi-mono : Mono phi)
             (x0 : Nat) (x0-le : LeN x0 (phi x0)) where

  it : Nat -> Nat
  it zero    = x0
  it (suc m) = phi (it m)

  it-mono1 : (m : Nat) -> LeN (it m) (it (suc m))
  it-mono1 zero    = x0-le
  it-mono1 (suc m) = phi-mono (it m) (it (suc m)) (it-mono1 m)

  it-mono : Mono it
  it-mono m zero     le =
    Eq-transport (\ z -> LeN (it z) (it zero))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (it zero))
  it-mono m (suc m') le = route (LeN-dec m m')
    where
      route : Dec (LeN m m') -> LeN (it m) (it (suc m'))
      route (yes l)  =
        LeN-trans {it m} {it m'} {it (suc m')} (it-mono m m' l) (it-mono1 m')
      route (no  nl) =
        Eq-transport (\ z -> LeN (it z) (it (suc m')))
          (Eq-sym (le-nle-eq m m' le nl)) (LeN-refl (it (suc m')))

  -- determinism: a repeated value is a fixed point
  it-freeze : (m : Nat) -> Eq (it (suc m)) (it m) ->
    (n : Nat) -> LeN m n -> Eq (it n) (it m)
  it-freeze m e zero    ln =
    Eq-transport (\ z -> Eq (it zero) (it z))
      (Eq-sym (LeN-antisym {m} {zero} ln tt)) refl
  it-freeze m e (suc n) ln = route (LeN-dec m n)
    where
      route : Dec (LeN m n) -> Eq (it (suc n)) (it m)
      route (yes l)  = Eq-trans (Eq-cong phi (it-freeze m e n l)) e
      route (no  nl) =
        Eq-transport (\ z -> Eq (it (suc n)) (it z))
          (Eq-sym (le-nle-eq m n ln nl)) refl

  -- either a repeat is found below T, or the iteration has climbed T times
  it-scan : (T : Nat) ->
    Or (Sigma Nat (\ m -> Eq (it (suc m)) (it m))) (LeN T (it T))
  it-scan zero    = inr tt
  it-scan (suc T) = route (it-scan T)
    where
      route : Or (Sigma Nat (\ m -> Eq (it (suc m)) (it m))) (LeN T (it T)) ->
        Or (Sigma Nat (\ m -> Eq (it (suc m)) (it m))) (LeN (suc T) (it (suc T)))
      route (inl w)  = inl w
      route (inr le) = pick (EqNat-dec (it (suc T)) (it T))
        where
          lt : Not (Eq (it (suc T)) (it T)) -> LeN (suc (it T)) (it (suc T))
          lt ne = go (it T) (it (suc T)) (it-mono1 T) ne
            where
              go : (x y : Nat) -> LeN x y -> Not (Eq y x) -> LeN (suc x) y
              go zero    zero    l ne' = Empty-elim (ne' refl)
              go zero    (suc y) l ne' = tt
              go (suc x) zero    () ne'
              go (suc x) (suc y) l ne' = go x y l (\ q -> ne' (Eq-cong suc q))

          pick : Dec (Eq (it (suc T)) (it T)) ->
            Or (Sigma Nat (\ m -> Eq (it (suc m)) (it m)))
               (LeN (suc T) (it (suc T)))
          pick (yes e)  = inl (mkSigma T e)
          pick (no  ne) =
            inr (LeN-trans {suc T} {suc (it T)} {it (suc T)} le (lt ne))

  it-pass : HPass it
  it-pass K = route (it-scan (suc K))
    where
      route :
        Or (Sigma Nat (\ m -> Eq (it (suc m)) (it m)))
           (LeN (suc K) (it (suc K))) ->
        Or (Sigma Nat (\ s -> LeN (suc K) (it s))) ((s : Nat) -> LeN (it s) K)
      route (inr le) = inl (mkSigma (suc K) le)
      route (inl (mkSigma m e)) = pick (LeN-dec (it m) K)
        where
          bnd : (s : Nat) -> LeN (it s) (it m)
          bnd s = decide (LeN-dec m s)
            where
              decide : Dec (LeN m s) -> LeN (it s) (it m)
              decide (yes l)  =
                Eq-transport (\ z -> LeN z (it m)) (Eq-sym (it-freeze m e s l))
                  (LeN-refl (it m))
              decide (no  nl) =
                it-mono s m (LeN-trans {s} {suc s} {m} (LeN-suc s) (nle-lt m s nl))

          pick : Dec (LeN (it m) K) ->
            Or (Sigma Nat (\ s -> LeN (suc K) (it s))) ((s : Nat) -> LeN (it s) K)
          pick (yes l)  = inr (\ s -> LeN-trans {it s} {it m} {K} (bnd s) l)
          pick (no  nl) = inl (mkSigma m (nle-lt (it m) K nl))

------------------------------------------------------------------------
-- (H) COMPOSES: a height read at an offset of another height
--
-- `\ m -> k (D + w m)` is the shape of a block component that reads ANOTHER
-- coordinate: past its threshold its replay depth is `D` plus the height
-- available there (`WalkAffine`).  The level K is answered by asking k for
-- the FIRST level n0 it passes K at, and then asking w whether it ever
-- reaches n0 - D.
------------------------------------------------------------------------

hpass-comp2 : (k w : Nat -> Nat) -> Mono k -> Mono w ->
  HPass k -> HPass w -> (D : Nat) -> HPass (\ m -> k (plus D (w m)))
hpass-comp2 k w mk mw hk hw D K = route (hk K)
  where
    Goal : Set
    Goal = Or (Sigma Nat (\ m -> LeN (suc K) (k (plus D (w m)))))
              ((m : Nat) -> LeN (k (plus D (w m))) K)

    route :
      Or (Sigma Nat (\ s -> LeN (suc K) (k s))) ((s : Nat) -> LeN (k s) K) ->
      Goal
    route (inr bnd) = inr (\ m -> bnd (plus D (w m)))
    route (inl (mkSigma s big)) = least (find-least k mk K s big)
      where
        least :
          Sigma Nat (\ n0 -> Pair (LeN (suc K) (k n0))
                                  ((n : Nat) -> LeN (suc n) n0 -> LeN (k n) K)) ->
          Goal
        least (mkSigma n0 (mkSigma big0 less)) = split (LeN-dec n0 D)
          where
            -- the offset alone already reaches the level
            split : Dec (LeN n0 D) -> Goal
            split (yes ln) =
              inl (mkSigma zero
                (LeN-trans {suc K} {k n0} {k (plus D (w zero))} big0
                  (mk n0 (plus D (w zero))
                    (LeN-trans {n0} {D} {plus D (w zero)} ln
                      (plus-ge-l D (w zero))))))
            -- otherwise ask w whether it reaches the difference
            split (no nl) = diff (le-plus D n0 leDn0)
              where
                ltDn0 : LeN (suc D) n0
                ltDn0 = nle-lt n0 D nl

                leDn0 : LeN D n0
                leDn0 = LeN-trans {D} {suc D} {n0} (LeN-suc D) ltDn0

                diff : Sigma Nat (\ e -> Eq (plus e D) n0) -> Goal
                diff (mkSigma zero eq) =
                  Empty-elim (LeN-suc-not D
                    (Eq-transport (\ z -> LeN (suc D) z) (Eq-sym eq) ltDn0))
                diff (mkSigma (suc e) eq) = pick (hw e)
                  where
                    -- n0 = 1 + e + D
                    pick :
                      Or (Sigma Nat (\ m -> LeN (suc e) (w m)))
                         ((m : Nat) -> LeN (w m) e) ->
                      Goal
                    pick (inl (mkSigma m bigw)) =
                      inl (mkSigma m
                        (LeN-trans {suc K} {k n0} {k (plus D (w m))} big0
                          (mk n0 (plus D (w m)) reach)))
                      where
                        reach : LeN n0 (plus D (w m))
                        reach =
                          Eq-transport (\ z -> LeN z (plus D (w m))) eq
                            (Eq-transport (\ z -> LeN z (plus D (w m)))
                              (plus-comm D (suc e))
                              (plus-mono D D (suc e) (w m) (LeN-refl D) bigw))
                    pick (inr bndw) = inr small
                      where
                        small : (m : Nat) -> LeN (k (plus D (w m))) K
                        small m = less (plus D (w m)) lt
                          where
                            lt : LeN (suc (plus D (w m))) n0
                            lt =
                              Eq-transport (\ z -> LeN (suc (plus D (w m))) z) eq
                                (Eq-transport
                                  (\ z -> LeN (suc (plus D (w m))) (suc z))
                                  (plus-comm D e)
                                  (plus-mono D D (w m) e (LeN-refl D) (bndw m)))
