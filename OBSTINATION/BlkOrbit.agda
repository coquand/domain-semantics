{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkOrbit
--
-- THE POINTER ORBIT OF A BLOCK, AS PURE FINITE COMBINATORICS.
--
-- The block's ultimate demand is a map `C : Nat -> Nat` on components:
-- component i ultimately demands coordinate `C i`, which is a recursive call
-- when `C i < r` and a parameter otherwise.  Following it from a start i,
--
--     cit C n i = C^n(i)
--
-- either LEAVES the block (some `C (C^t i) >= r`) or stays inside for ever.
-- The point of this module is that ONE BOUNDED SEARCH decides which:
--
--   find-exit   -- look for the first exit among the first n+1 iterates;
--   orbit-stays -- and if none is found within r steps there is none at all,
--                  because r+1 iterates in a set of r components repeat
--                  (`Pigeon.pigeon`) and the orbit is then periodic from the
--                  repeat on, so every later iterate is one of those seen.
--
-- Nothing here knows about traces, heights or demands: it is the finite half
-- of the block index theorem, kept apart from the analytic half in
-- `BlkTraceR`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkOrbit where

open import OBSTINATION.Prelude
open import OBSTINATION.Pigeon using (Repeat ; pigeon)
open import OBSTINATION.BlkReplay using (plus ; plus-lt-l ; nle-lt)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

le-nle-eq : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
le-nle-eq zero    y       l nl = Empty-elim (nl tt)
le-nle-eq (suc x) zero    l nl = Eq-cong suc (LeN-antisym {x} {zero} l tt)
le-nle-eq (suc x) (suc y) l nl = Eq-cong suc (le-nle-eq x y l nl)

le-to-plus : (x y : Nat) -> LeN x y -> Sigma Nat (\ d -> Eq (plus x d) y)
le-to-plus zero    y       l  = mkSigma y refl
le-to-plus (suc x) zero    ()
le-to-plus (suc x) (suc y) l  = bump (le-to-plus x y l)
  where
    bump : Sigma Nat (\ d -> Eq (plus x d) y) ->
           Sigma Nat (\ d -> Eq (plus (suc x) d) (suc y))
    bump (mkSigma d e) = mkSigma d (Eq-cong suc e)

------------------------------------------------------------------------
-- Iterating the pointer
------------------------------------------------------------------------

module _ (C : Nat -> Nat) where

  cit : Nat -> Nat -> Nat
  cit zero    i = i
  cit (suc n) i = cit n (C i)

  cit-suc : (n i : Nat) -> Eq (cit (suc n) i) (C (cit n i))
  cit-suc zero    i = refl
  cit-suc (suc n) i = cit-suc n (C i)

  cit-add : (u v i : Nat) -> Eq (cit (plus u v) i) (cit v (cit u i))
  cit-add zero    v i = refl
  cit-add (suc u) v i = cit-add u v (C i)

------------------------------------------------------------------------
-- Where the orbit leaves the block
------------------------------------------------------------------------

module _ (r : Nat) (C : Nat -> Nat) where

  -- the first t <= n at which the pointer leaves the block
  FirstExit : Nat -> Nat -> Set
  FirstExit n i = Sigma Nat (\ t -> Pair (LeN t n)
    (Pair ((s : Nat) -> LeN (suc s) t -> LeN (suc (C (cit C s i))) r)
          (Not (LeN (suc (C (cit C t i))) r))))

  -- ... or the first n+1 steps all stay inside
  AllRec : Nat -> Nat -> Set
  AllRec n i = (s : Nat) -> LeN s n -> LeN (suc (C (cit C s i))) r

  find-exit : (n i : Nat) -> Or (FirstExit n i) (AllRec n i)
  find-exit zero    i = route (LeN-dec (suc (C i)) r)
    where
      route : Dec (LeN (suc (C i)) r) -> Or (FirstExit zero i) (AllRec zero i)
      route (yes p) = inr all0
        where
          all0 : AllRec zero i
          all0 s ls =
            Eq-transport (\ z -> LeN (suc (C (cit C z i))) r)
              (Eq-sym (LeN-antisym {s} {zero} ls tt)) p
      route (no np) = inl (mkSigma zero (mkSigma tt (mkSigma (\ s ()) np)))
  find-exit (suc n) i = step (find-exit n i)
    where
      step : Or (FirstExit n i) (AllRec n i) ->
             Or (FirstExit (suc n) i) (AllRec (suc n) i)
      step (inl (mkSigma t (mkSigma lt rest))) =
        inl (mkSigma t (mkSigma (LeN-trans {t} {n} {suc n} lt (LeN-suc n)) rest))
      step (inr all) = route (LeN-dec (suc (C (cit C (suc n) i))) r)
        where
          route : Dec (LeN (suc (C (cit C (suc n) i))) r) ->
                  Or (FirstExit (suc n) i) (AllRec (suc n) i)
          route (yes p) = inr allS
            where
              allS : AllRec (suc n) i
              allS s ls = pick (LeN-dec s n)
                where
                  pick : Dec (LeN s n) -> LeN (suc (C (cit C s i))) r
                  pick (yes l)  = all s l
                  pick (no  nl) =
                    Eq-transport (\ z -> LeN (suc (C (cit C z i))) r)
                      (Eq-sym (le-nle-eq s n ls nl)) p
          route (no np) =
            inl (mkSigma (suc n) (mkSigma (LeN-refl (suc n)) (mkSigma all np)))

  ----------------------------------------------------------------------
  -- NO EXIT WITHIN r STEPS  ==>  NO EXIT AT ALL
  --
  -- The first r+1 iterates are r+1 components of a block of r, so two of
  -- them agree: `cit a i = cit b i` with a < b <= r.  Then `cit n i` for
  -- n >= b equals `cit (n - (b - a)) i`, which is smaller; descending, every
  -- iterate equals one with index at most r, where the hypothesis applies.
  ----------------------------------------------------------------------

  orbit-in : (i : Nat) -> LeN (suc i) r -> AllRec r i ->
    (s : Nat) -> LeN s (suc r) -> LeN (suc (cit C s i)) r
  orbit-in i li hyp zero    ls = li
  orbit-in i li hyp (suc s) ls =
    Eq-transport (\ z -> LeN (suc z) r) (Eq-sym (cit-suc C s i)) (hyp s ls)

  orbit-stays : (i : Nat) -> LeN (suc i) r -> AllRec r i ->
    (n : Nat) -> LeN (suc (C (cit C n i))) r
  orbit-stays i li hyp = build (pigeon r (\ s -> cit C s i) rng)
    where
      rng : (s : Nat) -> LeN s r -> LeN (suc (cit C s i)) r
      rng s ls = orbit-in i li hyp s (LeN-trans {s} {r} {suc r} ls (LeN-suc r))

      build : Repeat r (\ s -> cit C s i) ->
              (n : Nat) -> LeN (suc (C (cit C n i))) r
      build (mkSigma a (mkSigma b (mkSigma ab (mkSigma br e)))) n =
        go n n (LeN-refl n)
        where
          -- the iterate at n coincides with the strictly earlier one at
          -- n - (b - a), obtained by cutting the repeated stretch out
          back : (m : Nat) -> LeN (suc r) m ->
            Sigma Nat (\ m' -> Pair (LeN (suc m') m) (Eq (cit C m i) (cit C m' i)))
          back m lrm = cut (le-to-plus b m (LeN-trans {b} {suc b} {m} (LeN-suc b) lbm))
            where
              lbm : LeN (suc b) m
              lbm = LeN-trans {suc b} {suc r} {m} br lrm

              cut : Sigma Nat (\ s -> Eq (plus b s) m) ->
                Sigma Nat (\ m' -> Pair (LeN (suc m') m) (Eq (cit C m i) (cit C m' i)))
              cut (mkSigma s eq) = mkSigma (plus a s) (mkSigma lt eqc)
                where
                  lt : LeN (suc (plus a s)) m
                  lt = Eq-transport (\ z -> LeN (suc (plus a s)) z) eq
                         (plus-lt-l a b s s ab (LeN-refl s))

                  eqc : Eq (cit C m i) (cit C (plus a s) i)
                  eqc =
                    Eq-trans
                      (Eq-cong (\ z -> cit C z i) (Eq-sym eq))
                      (Eq-trans (cit-add C b s i)
                        (Eq-trans (Eq-cong (cit C s) (Eq-sym e))
                                  (Eq-sym (cit-add C a s i))))

          go : (F m : Nat) -> LeN m F -> LeN (suc (C (cit C m i))) r
          go zero    m lmF = small (LeN-dec m r)
            where
              small : Dec (LeN m r) -> LeN (suc (C (cit C m i))) r
              small (yes lm) = hyp m lm
              small (no  nm) =
                Empty-elim (nm (Eq-transport (\ z -> LeN z r)
                  (Eq-sym (LeN-antisym {m} {zero} lmF tt)) tt))
          go (suc F) m lmF = small (LeN-dec m r)
            where
              small : Dec (LeN m r) -> LeN (suc (C (cit C m i))) r
              small (yes lm) = hyp m lm
              small (no  nm) = descend (back m (nle-lt m r nm))
                where
                  descend :
                    Sigma Nat (\ m' -> Pair (LeN (suc m') m)
                      (Eq (cit C m i) (cit C m' i))) ->
                    LeN (suc (C (cit C m i))) r
                  descend (mkSigma m' (mkSigma lt eqc)) =
                    Eq-transport (\ z -> LeN (suc (C z)) r) (Eq-sym eqc)
                      (go F m' (LeN-trans {suc m'} {m} {suc F} lt lmF))
