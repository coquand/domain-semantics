{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MP1
--
-- THE NON-MUTUAL INVARIANT: (1) the sequentiality index is eventually
-- constant, and (2') Colson's `PhiOK` -- the height is CONSTANT from a
-- computable threshold, or STRICTLY INCREASING from one.
--
--     MP1 iv kv = Pair (EvConstN iv) (PhiOK kv)
--
-- WHY `PhiOK` AND NOT "bounded or unbounded".  The plain verdict is NOT
-- closed under recursion, and `BlkGrowFail`'s instance already shows it
-- WITHOUT any mutual recursion: there component 1 is inert (`kv 1 = 0`)
-- and `iv 0 n = 0` makes the dynamics the one-coordinate orbit
-- `x (m+1) = kv0 (x m) = x m + b (x m)`, i.e. exactly `f (S x) = g (f x)`.
-- Its step term satisfies (1) and "bounded or unbounded" outright
-- (`kv0 n >= n`), yet the orbit's verdict is LPO.
--
-- `PhiOK` repairs it, and `phiok-orbit` is where one sees why: for a
-- STRICTLY INCREASING step, ONE comparison decides the orbit --
-- `f x = x` freezes for ever, `f x > x` propagates for ever.  That single
-- comparison is the whole content of the recursion clause, and it is
-- exactly what `MutUOFail` destroys for mutual blocks (`floor (m/2)` is
-- neither constant nor strictly increasing), after which `BlkGrowFail`
-- shows nothing decides.
--
-- Proved here, all with computable thresholds:
--
--   phiok-hpass   -- MP1 implies MP: nothing is lost
--   phiok-verdict -- and the global bounded/unbounded verdict IS decided
--   phiok-comp    -- CLOSURE UNDER COMPOSITION, the `k (D + w m)` shape
--   phiok-orbit   -- CLOSURE UNDER RECURSION, the orbit of the step
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MP1 where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-suc-r ; le-ne-lt ; LeN-suc-not)
open import OBSTINATION.MPPass using (plus-zero-r)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MPPass using (Mono ; HPass ; plus-assoc)
open import OBSTINATION.CapDet using (nle-lt ; le-cases)

------------------------------------------------------------------------
-- THE INVARIANT
------------------------------------------------------------------------

ConstFrom : Nat -> (Nat -> Nat) -> Set
ConstFrom k u = (m : Nat) -> LeN k m -> Eq (u m) (u k)

StrictIncFrom : Nat -> (Nat -> Nat) -> Set
StrictIncFrom k u = (m : Nat) -> LeN k m -> LeN (suc (u m)) (u (suc m))

PhiOK : (Nat -> Nat) -> Set
PhiOK u = Sigma Nat (\ k -> Or (ConstFrom k u) (StrictIncFrom k u))

MP1 : (Nat -> Nat) -> (Nat -> Nat) -> Set
MP1 iv kv = Pair (EvConstN iv) (PhiOK kv)

------------------------------------------------------------------------
-- arithmetic
------------------------------------------------------------------------

plus-ge-l : (a b : Nat) -> LeN a (plus a b)
plus-ge-l zero    b = tt
plus-ge-l (suc a) b = plus-ge-l a b

plus-smono : (D x y : Nat) -> LeN (suc x) y -> LeN (suc (plus D x)) (plus D y)
plus-smono zero    x y l = l
plus-smono (suc D) x y l = plus-smono D x y l

le-add : (k n : Nat) -> LeN k n -> Sigma Nat (\ t -> Eq n (plus t k))
le-add zero    n       _  = mkSigma n (Eq-sym (plus-zero-r n))
le-add (suc k) zero    ()
le-add (suc k) (suc n) le with le-add k n le
... | mkSigma t e =
  mkSigma t (Eq-trans (Eq-cong suc e) (Eq-sym (plus-suc-r t k)))

------------------------------------------------------------------------
-- basic consequences of the two clauses
------------------------------------------------------------------------

const-bound : (u : Nat -> Nat) -> Mono u -> (k : Nat) -> ConstFrom k u
            -> (m : Nat) -> LeN (u m) (u k)
const-bound u mu k cf m = route (LeN-dec k m)
  where
    route : Dec (LeN k m) -> LeN (u m) (u k)
    route (yes le) = Eq-transport (\ z -> LeN z (u k)) (Eq-sym (cf m le))
                       (LeN-refl (u k))
    route (no  nl) = mu m k (LeN-trans {m} {suc m} {k} (LeN-suc m) (nle-lt k m nl))

-- strict increase across a gap, not just at a successor
sinc-gap : (u : Nat -> Nat) -> Mono u -> (k : Nat) -> StrictIncFrom k u
         -> (z z' : Nat) -> LeN k z -> LeN (suc z) z'
         -> LeN (suc (u z)) (u z')
sinc-gap u mu k si z zero     lk ()
sinc-gap u mu k si z (suc z') lk le = route (le-cases z z' le)
  where
    route : Or (Eq z' z) (LeN (suc z) z') -> LeN (suc (u z)) (u (suc z'))
    route (inl e)  =
      Eq-transport (\ w -> LeN (suc (u z)) (u (suc w))) (Eq-sym e) (si z lk)
    route (inr lt) =
      LeN-trans {suc (u z)} {u z'} {u (suc z')}
        (sinc-gap u mu k si z z' lk lt) (mu z' (suc z') (LeN-suc z'))

-- a strictly increasing tail grows at least linearly
sinc-grow : (u : Nat -> Nat) -> (k : Nat) -> StrictIncFrom k u
          -> (t : Nat) -> LeN (plus t (u k)) (u (plus t k))
sinc-grow u k si zero    = LeN-refl (u k)
sinc-grow u k si (suc t) =
  LeN-trans {suc (plus t (u k))} {suc (u (plus t k))} {u (suc (plus t k))}
    (sinc-grow u k si t) (si (plus t k) (plus-ge-r t k))

sinc-pass : (u : Nat -> Nat) -> (k : Nat) -> StrictIncFrom k u
          -> (K : Nat) -> LeN (suc K) (u (plus (suc K) k))
sinc-pass u k si K =
  LeN-trans {suc K} {plus (suc K) (u k)} {u (plus (suc K) k)}
    (plus-ge-l (suc K) (u k)) (sinc-grow u k si (suc K))

------------------------------------------------------------------------
-- MP1 IMPLIES MP -- nothing is lost by strengthening
------------------------------------------------------------------------

phiok-hpass : (u : Nat -> Nat) -> Mono u -> PhiOK u -> HPass u
phiok-hpass u mu (mkSigma k (inl cf)) K = route (LeN-dec (suc K) (u k))
  where
    route : Dec (LeN (suc K) (u k))
          -> Or (Sigma Nat (\ s -> LeN (suc K) (u s))) ((s : Nat) -> LeN (u s) K)
    route (yes p) = inl (mkSigma k p)
    route (no  n) =
      inr (\ s -> LeN-trans {u s} {u k} {K}
                    (const-bound u mu k cf s) (nle-lt (suc K) (u k) n))
phiok-hpass u mu (mkSigma k (inr si)) K =
  inl (mkSigma (plus (suc K) k) (sinc-pass u k si K))

------------------------------------------------------------------------
-- ... AND THE GLOBAL VERDICT IS DECIDED
------------------------------------------------------------------------

Bounded : (Nat -> Nat) -> Set
Bounded u = Sigma Nat (\ B -> (m : Nat) -> LeN (u m) B)

Unbounded : (Nat -> Nat) -> Set
Unbounded u = (K : Nat) -> Sigma Nat (\ m -> LeN (suc K) (u m))

phiok-verdict : (u : Nat -> Nat) -> Mono u -> PhiOK u
              -> Or (Bounded u) (Unbounded u)
phiok-verdict u mu (mkSigma k (inl cf)) =
  inl (mkSigma (u k) (const-bound u mu k cf))
phiok-verdict u mu (mkSigma k (inr si)) =
  inr (\ K -> mkSigma (plus (suc K) k) (sinc-pass u k si K))

------------------------------------------------------------------------
-- CLOSURE UNDER COMPOSITION
--
-- The shape `MainComp` consumes: the outer height read at a shifted
-- inner height.
------------------------------------------------------------------------

phiok-comp : (k w : Nat -> Nat) -> Mono k -> Mono w
           -> PhiOK k -> PhiOK w -> (D : Nat)
           -> PhiOK (\ m -> k (plus D (w m)))
phiok-comp k w mk mw pk (mkSigma w0 (inl cfw)) D =
  mkSigma w0 (inl (\ m lm -> Eq-cong (\ z -> k (plus D z)) (cfw m lm)))
phiok-comp k w mk mw (mkSigma k0 (inl cfk)) (mkSigma w0 (inr siw)) D =
  mkSigma T (inl (\ m lm -> Eq-trans (cfk (plus D (w m)) (big m lm))
                              (Eq-sym (cfk (plus D (w T)) (big T (LeN-refl T))))))
  where
    T : Nat
    T = plus (suc k0) w0

    wT : LeN k0 (w T)
    wT = LeN-trans {k0} {suc k0} {w T} (LeN-suc k0) (sinc-pass w w0 siw k0)

    big : (m : Nat) -> LeN T m -> LeN k0 (plus D (w m))
    big m lm =
      LeN-trans {k0} {w m} {plus D (w m)}
        (LeN-trans {k0} {w T} {w m} wT (mw T m lm)) (plus-ge-r D (w m))
phiok-comp k w mk mw (mkSigma k0 (inr sik)) (mkSigma w0 (inr siw)) D =
  mkSigma T (inr step)
  where
    T : Nat
    T = plus (suc k0) w0

    wT : LeN k0 (w T)
    wT = LeN-trans {k0} {suc k0} {w T} (LeN-suc k0) (sinc-pass w w0 siw k0)

    big : (m : Nat) -> LeN T m -> LeN k0 (plus D (w m))
    big m lm =
      LeN-trans {k0} {w m} {plus D (w m)}
        (LeN-trans {k0} {w T} {w m} wT (mw T m lm)) (plus-ge-r D (w m))

    step : (m : Nat) -> LeN T m
         -> LeN (suc (k (plus D (w m)))) (k (plus D (w (suc m))))
    step m lm =
      sinc-gap k mk k0 sik (plus D (w m)) (plus D (w (suc m))) (big m lm)
        (plus-smono D (w m) (w (suc m))
          (siw m (LeN-trans {w0} {T} {m} (plus-ge-r (suc k0) w0) lm)))

------------------------------------------------------------------------
-- STABILITY OF `PhiOK`: shifting the argument, and changing the
-- sequence below a threshold
------------------------------------------------------------------------

phiok-shift : (u : Nat -> Nat) -> PhiOK u -> (D : Nat)
            -> PhiOK (\ z -> u (plus D z))
phiok-shift u (mkSigma k (inl cf)) D =
  mkSigma k (inl (\ m lm -> Eq-trans (cf (plus D m) (le-D m lm))
                              (Eq-sym (cf (plus D k) (le-D k (LeN-refl k))))))
  where
    le-D : (m : Nat) -> LeN k m -> LeN k (plus D m)
    le-D m lm = LeN-trans {k} {m} {plus D m} lm (plus-ge-r D m)
phiok-shift u (mkSigma k (inr si)) D = mkSigma k (inr step)
  where
    step : (m : Nat) -> LeN k m
         -> LeN (suc (u (plus D m))) (u (plus D (suc m)))
    step m lm =
      Eq-transport (\ z -> LeN (suc (u (plus D m))) (u z))
        (Eq-sym (plus-suc-r D m))
        (si (plus D m) (LeN-trans {k} {m} {plus D m} lm (plus-ge-r D m)))

-- shifting on the RIGHT: `plus (suc z) D` reduces, so this is even easier
phiok-shift-r : (u : Nat -> Nat) -> PhiOK u -> (D : Nat)
              -> PhiOK (\ z -> u (plus z D))
phiok-shift-r u (mkSigma k (inl cf)) D =
  mkSigma k (inl (\ m lm -> Eq-trans (cf (plus m D) (le-D m lm))
                              (Eq-sym (cf (plus k D) (le-D k (LeN-refl k))))))
  where
    le-D : (m : Nat) -> LeN k m -> LeN k (plus m D)
    le-D m lm = LeN-trans {k} {m} {plus m D} lm (plus-ge-l m D)
phiok-shift-r u (mkSigma k (inr si)) D = mkSigma k (inr step)
  where
    step : (m : Nat) -> LeN k m
         -> LeN (suc (u (plus m D))) (u (plus (suc m) D))
    step m lm = si (plus m D) (LeN-trans {k} {m} {plus m D} lm (plus-ge-l m D))

phiok-cong-from : (u u' : Nat -> Nat) (T : Nat)
                -> ((m : Nat) -> LeN T m -> Eq (u m) (u' m))
                -> PhiOK u -> PhiOK u'
phiok-cong-from u u' T ag (mkSigma k (inl cf)) = mkSigma M (inl con)
  where
    M : Nat
    M = maxN k T

    lkM : LeN k M
    lkM = maxN-le-l k T

    ltM : LeN T M
    ltM = maxN-le-r k T

    con : ConstFrom M u'
    con m lm =
      Eq-trans (Eq-sym (ag m (LeN-trans {T} {M} {m} ltM lm)))
        (Eq-trans (cf m (LeN-trans {k} {M} {m} lkM lm))
          (Eq-trans (Eq-sym (cf M lkM)) (ag M ltM)))
phiok-cong-from u u' T ag (mkSigma k (inr si)) = mkSigma M (inr inc)
  where
    M : Nat
    M = maxN k T

    inc : StrictIncFrom M u'
    inc m lm =
      Eq-transport (\ z -> LeN (suc z) (u' (suc m)))
        (ag m lT)
        (Eq-transport (\ z -> LeN (suc (u m)) z)
          (ag (suc m) (LeN-trans {T} {m} {suc m} lT (LeN-suc m)))
          (si m (LeN-trans {k} {M} {m} (maxN-le-l k T) lm)))
      where
        lT : LeN T m
        lT = LeN-trans {T} {M} {m} (maxN-le-r k T) lm

-- reading a sequence one step later
phiok-from-succ : (p u : Nat -> Nat) (T : Nat)
                -> ((m : Nat) -> LeN T m -> Eq (p (suc m)) (u m))
                -> PhiOK u -> PhiOK p
phiok-from-succ p u T ag (mkSigma k (inl cf)) = mkSigma (suc M) (inl con)
  where
    M : Nat
    M = maxN T k

    at : (m : Nat) -> LeN M m -> Eq (p (suc m)) (u k)
    at m lm =
      Eq-trans (ag m (LeN-trans {T} {M} {m} (maxN-le-l T k) lm))
        (cf m (LeN-trans {k} {M} {m} (maxN-le-r T k) lm))

    con : ConstFrom (suc M) p
    con zero    ()
    con (suc m) lm = Eq-trans (at m lm) (Eq-sym (at M (LeN-refl M)))
phiok-from-succ p u T ag (mkSigma k (inr si)) = mkSigma (suc M) (inr inc)
  where
    M : Nat
    M = maxN T k

    inc : StrictIncFrom (suc M) p
    inc zero    ()
    inc (suc m) lm =
      Eq-transport (\ z -> LeN (suc z) (p (suc (suc m))))
        (Eq-sym (ag m lT))
        (Eq-transport (\ z -> LeN (suc (u m)) z)
          (Eq-sym (ag (suc m) (LeN-trans {T} {m} {suc m} lT (LeN-suc m))))
          (si m (LeN-trans {k} {M} {m} (maxN-le-r T k) lm)))
      where
        lT : LeN T m
        lT = LeN-trans {T} {M} {m} (maxN-le-l T k) lm

-- reading a sequence from an offset
phiok-reindex : (p o : Nat -> Nat) (M : Nat)
              -> ((t : Nat) -> Eq (p (plus t M)) (o t))
              -> PhiOK o -> PhiOK p
phiok-reindex p o M ag (mkSigma k (inl cf)) = mkSigma (plus k M) (inl con)
  where
    con : ConstFrom (plus k M) p
    con m lm with le-add (plus k M) m lm
    ... | mkSigma j e =
      Eq-transport (\ z -> Eq (p z) (p (plus k M))) (Eq-sym e)
        (Eq-transport (\ z -> Eq (p z) (p (plus k M)))
          (plus-assoc j k M)
          (Eq-trans (ag (plus j k))
            (Eq-trans (cf (plus j k) (plus-ge-r j k)) (Eq-sym (ag k)))))
phiok-reindex p o M ag (mkSigma k (inr si)) = mkSigma (plus k M) (inr inc)
  where
    at : (t : Nat) -> LeN k t -> LeN (suc (p (plus t M))) (p (plus (suc t) M))
    at t lt =
      Eq-transport (\ z -> LeN (suc z) (p (plus (suc t) M))) (Eq-sym (ag t))
        (Eq-transport (\ z -> LeN (suc (o t)) z) (Eq-sym (ag (suc t))) (si t lt))

    inc : StrictIncFrom (plus k M) p
    inc m lm with le-add (plus k M) m lm
    ... | mkSigma j e =
      Eq-transport (\ z -> LeN (suc (p z)) (p (suc z))) (Eq-sym ee)
        (at (plus j k) (plus-ge-r j k))
      where
        ee : Eq m (plus (plus j k) M)
        ee = Eq-trans e (Eq-sym (plus-assoc j k M))

------------------------------------------------------------------------
-- THE SAME THREE RESHAPINGS FOR `HPass` -- needed because the WEAKER
-- invariant (I) + (H) already suffices for "index eventually constant +
-- semantics computable on infinite input", with no `PhiOK` anywhere
------------------------------------------------------------------------

hpass-shift : (u : Nat -> Nat) -> Mono u -> HPass u -> (D : Nat)
            -> HPass (\ z -> u (plus D z))
hpass-shift u mu hu D K = route (hu K)
  where
    route : Or (Sigma Nat (\ s -> LeN (suc K) (u s))) ((s : Nat) -> LeN (u s) K)
          -> Or (Sigma Nat (\ s -> LeN (suc K) (u (plus D s))))
                ((s : Nat) -> LeN (u (plus D s)) K)
    route (inl (mkSigma s p)) =
      inl (mkSigma s (LeN-trans {suc K} {u s} {u (plus D s)} p
                        (mu s (plus D s) (plus-ge-r D s))))
    route (inr q) = inr (\ s -> q (plus D s))

hpass-from-succ : (p u : Nat -> Nat) -> Mono p -> Mono u -> (T : Nat)
                -> ((m : Nat) -> LeN T m -> Eq (p (suc m)) (u m))
                -> HPass u -> HPass p
hpass-from-succ p u mp mu T ag hu K = route (hu K)
  where
    route : Or (Sigma Nat (\ s -> LeN (suc K) (u s))) ((s : Nat) -> LeN (u s) K)
          -> Or (Sigma Nat (\ s -> LeN (suc K) (p s))) ((s : Nat) -> LeN (p s) K)
    route (inl (mkSigma s pf)) =
      inl (mkSigma (suc M)
        (Eq-transport (\ z -> LeN (suc K) z) (Eq-sym (ag M (maxN-le-r s T)))
          (LeN-trans {suc K} {u s} {u M} pf (mu s M (maxN-le-l s T)))))
      where
        M : Nat
        M = maxN s T
    route (inr q) = inr bd
      where
        bd : (s : Nat) -> LeN (p s) K
        bd s = route' (LeN-dec (suc T) s)
          where
            route' : Dec (LeN (suc T) s) -> LeN (p s) K
            route' (yes le) with le-add (suc T) s le
            ... | mkSigma t e =
              Eq-transport (\ z -> LeN (p z) K) (Eq-sym e)
                (Eq-transport (\ z -> LeN (p z) K) (Eq-sym (plus-suc-r t T))
                  (Eq-transport (\ z -> LeN z K)
                    (Eq-sym (ag (plus t T) (plus-ge-r t T))) (q (plus t T))))
            route' (no nl) =
              LeN-trans {p s} {p (suc T)} {K}
                (mp s (suc T)
                  (LeN-trans {s} {T} {suc T} (nle-lt (suc T) s nl) (LeN-suc T)))
                (Eq-transport (\ z -> LeN z K)
                  (Eq-sym (ag T (LeN-refl T))) (q T))

hpass-reindex : (p o : Nat -> Nat) -> Mono p -> (M : Nat)
              -> ((t : Nat) -> Eq (p (plus t M)) (o t))
              -> HPass o -> HPass p
hpass-reindex p o mp M ag ho K = route (ho K)
  where
    route : Or (Sigma Nat (\ s -> LeN (suc K) (o s))) ((s : Nat) -> LeN (o s) K)
          -> Or (Sigma Nat (\ s -> LeN (suc K) (p s))) ((s : Nat) -> LeN (p s) K)
    route (inl (mkSigma t pf)) =
      inl (mkSigma (plus t M)
        (Eq-transport (\ z -> LeN (suc K) z) (Eq-sym (ag t)) pf))
    route (inr q) = inr bd
      where
        bd : (s : Nat) -> LeN (p s) K
        bd s = route' (LeN-dec M s)
          where
            route' : Dec (LeN M s) -> LeN (p s) K
            route' (yes le) with le-add M s le
            ... | mkSigma t e =
              Eq-transport (\ z -> LeN (p z) K) (Eq-sym e)
                (Eq-transport (\ z -> LeN z K) (Eq-sym (ag t)) (q t))
            route' (no nl) =
              LeN-trans {p s} {p M} {K}
                (mp s M (LeN-trans {s} {suc s} {M} (LeN-suc s) (nle-lt M s nl)))
                (Eq-transport (\ z -> LeN z K) (Eq-sym (ag zero)) (q zero))

------------------------------------------------------------------------
-- CLOSURE UNDER RECURSION
--
-- `orb f x0` is the height sequence of `f (S x) = g (x , f x , y~)` once
-- `g`'s ultimate demand is the RECURSIVE VALUE: past `g`'s index
-- threshold the available level at that coordinate is the previous
-- height, so the height is the orbit of `f = kv_g (D + -)`.
------------------------------------------------------------------------

module Orbit (f : Nat -> Nat) (mf : Mono f) (x0 : Nat)
             (up : LeN x0 (f x0)) where

  orb : Nat -> Nat
  orb zero    = x0
  orb (suc m) = f (orb m)

  orb-step : (m : Nat) -> LeN (orb m) (orb (suc m))
  orb-step zero    = up
  orb-step (suc m) = mf (orb m) (orb (suc m)) (orb-step m)

  orb-le : (m t : Nat) -> LeN (orb m) (orb (plus t m))
  orb-le m zero    = LeN-refl (orb m)
  orb-le m (suc t) =
    LeN-trans {orb m} {orb (plus t m)} {orb (suc (plus t m))}
      (orb-le m t) (orb-step (plus t m))

  orb-mono : (m m' : Nat) -> LeN m m' -> LeN (orb m) (orb m')
  orb-mono m m' le with le-add m m' le
  ... | mkSigma t e =
    Eq-transport (\ z -> LeN (orb m) (orb z)) (Eq-sym e) (orb-le m t)

  ----------------------------------------------------------------------
  -- a frozen step freezes the orbit for ever (determinism)
  ----------------------------------------------------------------------

  orb-fz : (m : Nat) -> Eq (orb (suc m)) (orb m)
         -> (t : Nat) -> Eq (orb (plus t m)) (orb m)
  orb-fz m fz zero    = refl
  orb-fz m fz (suc t) =
    Eq-trans (Eq-cong f (orb-fz m fz t)) fz

  orb-const : (m : Nat) -> Eq (orb (suc m)) (orb m) -> ConstFrom m orb
  orb-const m fz m' lm with le-add m m' lm
  ... | mkSigma t e =
    Eq-transport (\ z -> Eq (orb z) (orb m)) (Eq-sym e) (orb-fz m fz t)

  ----------------------------------------------------------------------
  -- the bounded search: either it froze by step K, or it has climbed to K
  ----------------------------------------------------------------------

  find-fz : (K : Nat)
          -> Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m))) (LeN K (orb K))
  find-fz zero    = inr tt
  find-fz (suc K) = route (find-fz K)
    where
      route : Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m))) (LeN K (orb K))
            -> Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m)))
                  (LeN (suc K) (orb (suc K)))
      route (inl w)  = inl w
      route (inr le) = inner (EqNat-dec (orb (suc K)) (orb K))
        where
          inner : Dec (Eq (orb (suc K)) (orb K))
                -> Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m)))
                      (LeN (suc K) (orb (suc K)))
          inner (yes e)  = inl (mkSigma K e)
          inner (no  ne) =
            inr (LeN-trans {suc K} {suc (orb K)} {orb (suc K)} le
                   (le-ne-lt (orb K) (orb (suc K)) (orb-step K) ne))

  ----------------------------------------------------------------------
  -- THE RECURSION CLAUSE
  ----------------------------------------------------------------------

  -- a BOUNDED orbit freezes within B+1 steps: it cannot climb past its
  -- own bound, so `find-fz` must return the freeze
  orb-bnd : (B : Nat) -> ((m : Nat) -> LeN (orb m) B) -> PhiOK orb
  orb-bnd B bd = route (find-fz (suc B))
    where
      route : Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m)))
                 (LeN (suc B) (orb (suc B)))
            -> PhiOK orb
      route (inl (mkSigma m fz)) = mkSigma m (inl (orb-const m fz))
      route (inr le) =
        Empty-elim
          (LeN-suc-not B
            (LeN-trans {suc B} {orb (suc B)} {B} le (bd (suc B))))

  phiok-orbit : PhiOK f -> PhiOK orb
  phiok-orbit (mkSigma k cl) = route (find-fz k)
    where
      route : Or (Sigma Nat (\ m -> Eq (orb (suc m)) (orb m))) (LeN k (orb k))
            -> PhiOK orb
      route (inl (mkSigma m fz)) = mkSigma m (inl (orb-const m fz))
      route (inr lek) = clause cl
        where
          -- past k the orbit stays above k, so f's own clause applies there
          above : (m : Nat) -> LeN k m -> LeN k (orb m)
          above m lm = LeN-trans {k} {orb k} {orb m} lek (orb-mono k m lm)

          clause : Or (ConstFrom k f) (StrictIncFrom k f) -> PhiOK orb
          -- f constant past k: the orbit is f k from step k+1 on
          clause (inl cff) = mkSigma (suc k) (inl con)
            where
              val : (m : Nat) -> LeN k m -> Eq (orb (suc m)) (f k)
              val m lm = cff (orb m) (above m lm)

              con : ConstFrom (suc k) orb
              con zero    ()
              con (suc m) lm =
                Eq-trans (val m lm) (Eq-sym (val k (LeN-refl k)))
          -- f strictly increasing past k: ONE comparison decides
          clause (inr sif) = decide (EqNat-dec (orb (suc k)) (orb k))
            where
              decide : Dec (Eq (orb (suc k)) (orb k)) -> PhiOK orb
              decide (yes e) = mkSigma k (inl (orb-const k e))
              decide (no ne) = mkSigma k (inr up-from)
                where
                  base : LeN (suc (orb k)) (orb (suc k))
                  base = le-ne-lt (orb k) (orb (suc k)) (orb-step k) ne

                  -- strict increase propagates along the orbit
                  climb : (t : Nat)
                        -> LeN (suc (orb (plus t k))) (orb (suc (plus t k)))
                  climb zero    = base
                  climb (suc t) =
                    sinc-gap f mf k sif (orb (plus t k)) (orb (suc (plus t k)))
                      (above (plus t k) (plus-ge-r t k)) (climb t)

                  up-from : StrictIncFrom k orb
                  up-from m lm with le-add k m lm
                  ... | mkSigma t e =
                    Eq-transport
                      (\ z -> LeN (suc (orb z)) (orb (suc z))) (Eq-sym e) (climb t)
