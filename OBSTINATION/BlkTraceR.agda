{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkTraceR
--
-- THE MUTUAL-BLOCK INDEX THEOREM AT GENERAL ARITY r, FROM THE TRACES ALONE.
--
--     main : (j : Nat) -> LeN (suc j) r -> EvConstN (q j)
--
-- Each component's sequentiality index is eventually constant, given only
-- the traces of the step terms (`iv`, `kv`, `Y`) and the induction
-- hypothesis (`st`: each step index is ultimately `C j`).  This generalises
-- `BlkTwoTrace.two-main` from r = 2 to every arity, and, as there, no
-- syntax of the step terms appears anywhere.
--
-- THE TWO HALVES.  One bounded search on the pointer map C decides:
--
--   * the orbit of j LEAVES the block within r steps -- then `path-const`
--     chains `step-const` down to the exit and `exit-const` finishes;
--   * or it never leaves (`BlkOrbit.orbit-stays`: r+1 iterates in a block
--     of r repeat, so the orbit is periodic and stays inside for ever) --
--     then `descent` shows no descent from any depth can answer a
--     parameter, so `q j` is identically 0.
--
-- `descent` is the analytic half, and the reason the r = 3 detour that
-- r = 2 could not express is impossible: see its comment below.
--
-- The block of r components, built from the traces of its step terms alone:
-- coordinates 0..r-1 are the recursive values, r+c the parameters.
--
--     av m c    -- available at depth m: hv m c for c < r, Y c otherwise
--     nn j m    -- how far g_j's walk replays there    (`ReplayLv.nOf`)
--     hv (m+1) j = kv j (nn j m)          the component's height
--     cIdx j m   = iv j (nn j m)          the step index
--
-- THE GENERAL PERMANENCE LEMMA (`perm`): if the coordinate g_j's replay is
-- stuck on does not grow, the replay -- hence the demand -- never moves.
-- Nothing here is about parameters; parameters are just the coordinates that
-- are constant by construction (`av-param`).  The consequences:
--
--   param-perm      -- a parameter demand is permanent, so a RECURSIVE
--   no-param           ultimate demand means no parameter demand ever;
--   param-freeze-h  -- and a component that demands a parameter has a FROZEN
--                      HEIGHT from the next depth on;
--   frozen-perm     -- so THAT coordinate is now constant too, and any
--                      component reading it at a later depth is stuck on it
--                      for ever -- its ultimate demand IS that component.
--
-- `frozen-perm` is what rules out the r = 3 configuration that `r = 2` could
-- not express: a 2-cycle (C 0 = 1, C 1 = 0) with a third component exiting to
-- a parameter, and component 0 detouring into it below the threshold.  For
-- the detour to change the answer it must happen at a depth where component 2
-- already answers a parameter -- but by then component 2's height is frozen,
-- so `frozen-perm` forces C 0 = 2, contradicting C 0 = 1.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkTraceR where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.ReplayLv using (nOf ; nOf-mono ; nOf-freeze)
open import OBSTINATION.BlkOrbit using
  (cit ; FirstExit ; AllRec ; find-exit ; orbit-stays)

-- s - r: the position of a parameter once the r component slots are dropped
subN : Nat -> Nat -> Nat
subN zero    s       = s
subN (suc n) zero    = zero
subN (suc n) (suc s) = subN n s

module _ (r a : Nat)
         (iv : Nat -> Nat -> Nat)
         (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
         (kv : Nat -> Nat -> Nat)
         (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         (Y : Nat -> Nat)
         where

  NO : Nat -> (Nat -> Nat) -> Nat
  NO j f = nOf a (iv j) (ivr j) f

  ----------------------------------------------------------------------
  -- THE BLOCK'S TRACE
  ----------------------------------------------------------------------

  -- what a coordinate offers: a component's height, or a parameter
  avf : (Nat -> Nat) -> Nat -> Nat
  avf f c with LeN-dec (suc c) r
  ... | yes _ = f c
  ... | no  _ = Y c

  hv : Nat -> Nat -> Nat
  hv zero    j = zero
  hv (suc m) j = kv j (NO j (avf (hv m)))

  av : Nat -> Nat -> Nat
  av m = avf (hv m)

  nn : Nat -> Nat -> Nat
  nn j m = NO j (av m)

  cIdx : Nat -> Nat -> Nat
  cIdx j m = iv j (nn j m)

  ----------------------------------------------------------------------
  -- monotone in the depth
  ----------------------------------------------------------------------

  mutual
    hv-mono1 : (m j : Nat) -> LeN (hv m j) (hv (suc m) j)
    hv-mono1 zero    j = tt
    hv-mono1 (suc m) j =
      kv-mono j (nn j m) (nn j (suc m))
        (nOf-mono a (iv j) (ivr j) (av m) (av (suc m)) (av-mono1 m))

    av-mono1 : (m c : Nat) -> LeN (av m c) (av (suc m) c)
    av-mono1 m c with LeN-dec (suc c) r
    ... | yes _ = hv-mono1 m c
    ... | no  _ = LeN-refl (Y c)

  av-mono : (m m' : Nat) -> LeN m m' -> (c : Nat) -> LeN (av m c) (av m' c)
  av-mono m zero     le c =
    Eq-transport (\ z -> LeN (av z c) (av zero c))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (av zero c))
  av-mono m (suc m') le c with LeN-dec m m'
  ... | yes l  =
        LeN-trans {av m c} {av m' c} {av (suc m') c}
          (av-mono m m' l c) (av-mono1 m' c)
  ... | no  nl =
        Eq-transport (\ z -> LeN (av z c) (av (suc m') c))
          (Eq-sym (le-eq m m' le nl)) (LeN-refl (av (suc m') c))
    where
      le-eq : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
      le-eq zero    y       l nl' = Empty-elim (nl' tt)
      le-eq (suc x) zero    l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
      le-eq (suc x) (suc y) l nl' = Eq-cong suc (le-eq x y l nl')

  ----------------------------------------------------------------------
  -- THE GENERAL PERMANENCE LEMMA
  --
  -- Nothing about parameters: any coordinate that does not grow pins the
  -- replay that is stuck on it.
  ----------------------------------------------------------------------

  perm : (j m : Nat) ->
    ((m' : Nat) -> LeN m m' -> Eq (av m' (cIdx j m)) (av m (cIdx j m))) ->
    (m' : Nat) -> LeN m m' -> Eq (nn j m') (nn j m)
  perm j m fix m' lm =
    nOf-freeze a (iv j) (ivr j) (av m) (av m') (av-mono m m' lm) (fix m' lm)

  perm-idx : (j m : Nat) ->
    ((m' : Nat) -> LeN m m' -> Eq (av m' (cIdx j m)) (av m (cIdx j m))) ->
    (m' : Nat) -> LeN m m' -> Eq (cIdx j m') (cIdx j m)
  perm-idx j m fix m' lm = Eq-cong (iv j) (perm j m fix m' lm)

  ----------------------------------------------------------------------
  -- PARAMETERS ARE CONSTANT, SO A PARAMETER DEMAND IS PERMANENT
  ----------------------------------------------------------------------

  av-param : (c : Nat) -> Not (LeN (suc c) r) -> (m m' : Nat) ->
    Eq (av m' c) (av m c)
  av-param c nc m m' = Eq-trans (at m') (Eq-sym (at m))
    where
      at : (n : Nat) -> Eq (av n c) (Y c)
      at n with LeN-dec (suc c) r
      ... | yes p = Empty-elim (nc p)
      ... | no  _ = refl

  -- ... and their value is the parameter height itself
  av-out : (c : Nat) -> Not (LeN (suc c) r) -> (m : Nat) -> Eq (av m c) (Y c)
  av-out c nc m with LeN-dec (suc c) r
  ... | yes p = Empty-elim (nc p)
  ... | no  _ = refl

  param-perm : (j m : Nat) -> Not (LeN (suc (cIdx j m)) r) ->
    (m' : Nat) -> LeN m m' -> Eq (nn j m') (nn j m)
  param-perm j m nc = perm j m (\ m' lm -> av-param (cIdx j m) nc m m')

  param-perm-idx : (j m : Nat) -> Not (LeN (suc (cIdx j m)) r) ->
    (m' : Nat) -> LeN m m' -> Eq (cIdx j m') (cIdx j m)
  param-perm-idx j m nc m' lm = Eq-cong (iv j) (param-perm j m nc m' lm)

  -- a recursive ultimate demand means no parameter demand at any depth
  no-param : (L : Nat) (C : Nat -> Nat) ->
    ((j m : Nat) -> LeN (suc j) r -> LeN L m -> Eq (cIdx j m) (C j)) ->
    (j : Nat) -> LeN (suc j) r ->
    LeN (suc (C j)) r -> (m : Nat) -> LeN (suc (cIdx j m)) r
  no-param L C st j lj lC m = route (LeN-dec (suc (cIdx j m)) r)
    where
      route : Dec (LeN (suc (cIdx j m)) r) -> LeN (suc (cIdx j m)) r
      route (yes p) = p
      route (no  nc) =
        Empty-elim
          (nc (Eq-transport (\ z -> LeN (suc z) r)
                (Eq-trans (Eq-sym (st j (maxN m L) lj (maxN-le-r m L)))
                          (param-perm-idx j m nc (maxN m L) (maxN-le-l m L)))
                lC))

  ----------------------------------------------------------------------
  -- A COMPONENT THAT DEMANDS A PARAMETER HAS A FROZEN HEIGHT
  ----------------------------------------------------------------------

  param-freeze-h : (j m : Nat) -> Not (LeN (suc (cIdx j m)) r) ->
    (m' : Nat) -> LeN (suc m) m' -> Eq (hv m' j) (hv (suc m) j)
  param-freeze-h j m nc zero     ()
  param-freeze-h j m nc (suc m') lm =
    Eq-cong (kv j) (param-perm j m nc m' lm)

  ----------------------------------------------------------------------
  -- ... AND THEN THAT COORDINATE PINS ANYONE READING IT
  --
  -- This is what rules out the r = 3 detour: a component whose demand at
  -- depth `d` is a coordinate already frozen at `d` has that demand for ever,
  -- so its ULTIMATE demand is that coordinate.
  ----------------------------------------------------------------------

  frozen-perm : (j d : Nat) -> LeN (suc (cIdx j d)) r ->
    ((m' : Nat) -> LeN d m' -> Eq (hv m' (cIdx j d)) (hv d (cIdx j d))) ->
    (m' : Nat) -> LeN d m' -> Eq (cIdx j m') (cIdx j d)
  frozen-perm j d lc fz = perm-idx j d fix
    where
      fix : (m' : Nat) -> LeN d m' -> Eq (av m' (cIdx j d)) (av d (cIdx j d))
      fix m' lm with LeN-dec (suc (cIdx j d)) r
      ... | yes _ = fz m' lm
      ... | no  n = Empty-elim (n lc)

  -- so its ultimate demand is that coordinate
  frozen-C : (L : Nat) (C : Nat -> Nat) ->
    ((j m : Nat) -> LeN (suc j) r -> LeN L m -> Eq (cIdx j m) (C j)) ->
    (j d : Nat) -> LeN (suc j) r -> LeN (suc (cIdx j d)) r ->
    ((m' : Nat) -> LeN d m' -> Eq (hv m' (cIdx j d)) (hv d (cIdx j d))) ->
    Eq (C j) (cIdx j d)
  frozen-C L C st j d lj lc fz =
    Eq-trans (Eq-sym (st j (maxN d L) lj (maxN-le-r d L)))
             (frozen-perm j d lc fz (maxN d L) (maxN-le-l d L))

  ----------------------------------------------------------------------
  -- A RECURSIVE COORDINATE IS JUST THE COMPONENT'S HEIGHT
  ----------------------------------------------------------------------

  av-rec : (c : Nat) -> LeN (suc c) r -> (m : Nat) -> Eq (av m c) (hv m c)
  av-rec c lc m with LeN-dec (suc c) r
  ... | yes _ = refl
  ... | no  n = Empty-elim (n lc)

  -- a coordinate whose height no longer moves from depth D on
  Frozen : Nat -> Nat -> Set
  Frozen c D = (m' : Nat) -> LeN D m' -> Eq (hv m' c) (hv D c)

  ----------------------------------------------------------------------
  -- FREEZING PROPAGATES BACKWARDS ALONG A DEMAND
  --
  -- If i's demand at depth D is a component whose height is already frozen
  -- at D, then g_i's replay cannot move either (`perm`), so i's own height
  -- is frozen from the next depth on.  Together with `frozen-C` -- which
  -- says that this demand IS i's ultimate demand -- this is what carries a
  -- parameter answer found deep in a descent back up to the pointer map C.
  ----------------------------------------------------------------------

  freeze-step : (i D : Nat) -> LeN (suc (cIdx i D)) r ->
    Frozen (cIdx i D) D -> Frozen i (suc D)
  freeze-step i D lc fz zero     ()
  freeze-step i D lc fz (suc m') lm = Eq-cong (kv i) (perm i D fix m' lm)
    where
      fix : (m'' : Nat) -> LeN D m'' ->
        Eq (av m'' (cIdx i D)) (av D (cIdx i D))
      fix m'' lm'' =
        Eq-trans (av-rec (cIdx i D) lc m'')
          (Eq-trans (fz m'' lm'') (Eq-sym (av-rec (cIdx i D) lc D)))

  ----------------------------------------------------------------------
  -- THE INDEX OF THE BLOCK COMPONENTS
  --
  -- q j 0 = 0 (the recursion argument); at depth m+1 the index of f_j is
  -- read off its step index: a recursive demand descends to that
  -- component one depth lower, a parameter demand answers 1 + (s - r).
  ----------------------------------------------------------------------

  pickQ : Nat -> (Nat -> Nat) -> Nat
  pickQ s rec with LeN-dec (suc s) r
  ... | yes _ = rec s
  ... | no  _ = suc (subN r s)

  pickQ-in : (s : Nat) (rec : Nat -> Nat) -> LeN (suc s) r ->
    Eq (pickQ s rec) (rec s)
  pickQ-in s rec lt with LeN-dec (suc s) r
  ... | yes _ = refl
  ... | no  n = Empty-elim (n lt)

  pickQ-out : (s : Nat) (rec : Nat -> Nat) -> Not (LeN (suc s) r) ->
    Eq (pickQ s rec) (suc (subN r s))
  pickQ-out s rec nt with LeN-dec (suc s) r
  ... | yes p = Empty-elim (nt p)
  ... | no  _ = refl

  q : Nat -> Nat -> Nat
  q j zero    = zero
  q j (suc m) = pickQ (cIdx j m) (\ s -> q s m)

  ----------------------------------------------------------------------
  -- THE POINTER CASES: LEAVING THE BLOCK, AND ONE STEP INSIDE IT
  ----------------------------------------------------------------------

  exit-const : (L Cj j : Nat) -> Not (LeN (suc Cj) r) ->
    ((m : Nat) -> LeN L m -> Eq (cIdx j m) Cj) -> EvConstN (q j)
  exit-const L Cj j nt stj = mkSigma (suc L) go
    where
      at : (m : Nat) -> LeN L m -> Eq (q j (suc m)) (suc (subN r Cj))
      at m lm =
        Eq-trans (Eq-cong (\ z -> pickQ z (\ s -> q s m)) (stj m lm))
                 (pickQ-out Cj (\ s -> q s m) nt)

      go : (n : Nat) -> LeN (suc L) n -> Eq (q j n) (q j (suc L))
      go zero    ()
      go (suc n) ln = Eq-trans (at n ln) (Eq-sym (at L (LeN-refl L)))

  step-const : (L Cj j : Nat) -> LeN (suc Cj) r ->
    ((m : Nat) -> LeN L m -> Eq (cIdx j m) Cj) ->
    EvConstN (q Cj) -> EvConstN (q j)
  step-const L Cj j lt stj (mkSigma M ev) = mkSigma (suc K) go
    where
      K : Nat
      K = maxN L M

      stepq : (m : Nat) -> LeN L m -> Eq (q j (suc m)) (q Cj m)
      stepq m lm =
        Eq-trans (Eq-cong (\ z -> pickQ z (\ s -> q s m)) (stj m lm))
                 (pickQ-in Cj (\ s -> q s m) lt)

      atK : Eq (q j (suc K)) (q Cj M)
      atK = Eq-trans (stepq K (maxN-le-l L M)) (ev K (maxN-le-r L M))

      go : (n : Nat) -> LeN (suc K) n -> Eq (q j n) (q j (suc K))
      go zero    ()
      go (suc n) ln =
        Eq-trans
          (Eq-trans (stepq n (LeN-trans {L} {K} {n} (maxN-le-l L M) ln))
                    (ev n (LeN-trans {M} {K} {n} (maxN-le-r L M) ln)))
          (Eq-sym atK)

  ----------------------------------------------------------------------
  -- THE INDUCTION HYPOTHESIS
  --
  -- From here on, `C j` is the ultimate step index of component j and `L`
  -- the depth past which it is attained.  Nothing else about the block is
  -- used.
  ----------------------------------------------------------------------

  module _ (L : Nat) (C : Nat -> Nat)
           (st : (j m : Nat) -> LeN (suc j) r -> LeN L m -> Eq (cIdx j m) (C j))
           where

    --------------------------------------------------------------------
    -- FOLLOWING THE POINTER UNTIL IT LEAVES THE BLOCK
    --------------------------------------------------------------------

    path-const : (t j : Nat) -> LeN (suc j) r ->
      ((s : Nat) -> LeN (suc s) t -> LeN (suc (C (cit C s j))) r) ->
      Not (LeN (suc (C (cit C t j))) r) ->
      EvConstN (q j)
    path-const zero    j lj ir nt = exit-const L (C j) j nt (\ m -> st j m lj)
    path-const (suc t) j lj ir nt =
      step-const L (C j) j (ir zero tt) (\ m -> st j m lj)
        (path-const t (C j) (ir zero tt) (\ s ls -> ir (suc s) ls) nt)

    --------------------------------------------------------------------
    -- THE DESCENT LEMMA
    --
    -- Read the definition of `q` as a descent: the index of f_j at depth
    -- m+1 is the index of f_{c_j(m)} at depth m, and the descent stops
    -- exactly when some step index points at a parameter.  Suppose it
    -- does, at (i_k, d).  Then
    --
    --   * i_k's height is frozen from depth d+1 (`param-freeze-h`), since
    --     a parameter demand never moves (`param-perm`);
    --   * the descent reached i_k from i_{k-1} at depth d+1, where the
    --     coordinate i_k is thus ALREADY frozen -- so `freeze-step` freezes
    --     i_{k-1} from depth d+2, and `frozen-C` gives C i_{k-1} = i_k;
    --   * iterating, C i_{t} = i_{t+1} all the way up to the start.
    --
    -- So a descent that answers a parameter forces the pointer orbit of
    -- its start to leave the block: the two conclusions of `descent` are
    -- exactly the two halves of that induction, carried simultaneously.
    --------------------------------------------------------------------

    Exits : Nat -> Set
    Exits i = Sigma Nat (\ k -> Not (LeN (suc (C (cit C k i))) r))

    descent : (m i : Nat) -> LeN (suc i) r -> Not (Eq (q i m) zero) ->
      Pair (Frozen i m) (Exits i)
    descent zero    i li ne = Empty-elim (ne refl)
    descent (suc m) i li ne = route (LeN-dec (suc (cIdx i m)) r)
      where
        -- the demand at depth m is a parameter: the descent stops here,
        -- and this parameter is already the ultimate demand of i
        route : Dec (LeN (suc (cIdx i m)) r) ->
                Pair (Frozen i (suc m)) (Exits i)
        route (no nc) =
          mkSigma (param-freeze-h i m nc)
            (mkSigma zero
              (Eq-transport (\ z -> Not (LeN (suc z) r)) (Eq-sym eC) nc))
          where
            eC : Eq (C i) (cIdx i m)
            eC = Eq-trans (Eq-sym (st i (maxN m L) li (maxN-le-r m L)))
                          (param-perm-idx i m nc (maxN m L) (maxN-le-l m L))
        -- a recursive demand: descend, and lift the answer back
        route (yes lc) = build (descent m (cIdx i m) lc ne')
          where
            ne' : Not (Eq (q (cIdx i m) m) zero)
            ne' e = ne (Eq-trans (pickQ-in (cIdx i m) (\ s -> q s m) lc) e)

            build : Pair (Frozen (cIdx i m) m) (Exits (cIdx i m)) ->
                    Pair (Frozen i (suc m)) (Exits i)
            build (mkSigma fz (mkSigma k ex)) =
              mkSigma (freeze-step i m lc fz)
                (mkSigma (suc k)
                  (Eq-transport (\ z -> Not (LeN (suc (C (cit C k z))) r))
                    (Eq-sym (frozen-C L C st i m li lc fz)) ex))

    -- so if the orbit never leaves the block, every index is the recursion
    -- argument
    q-zero : (i : Nat) -> LeN (suc i) r ->
      ((n : Nat) -> LeN (suc (C (cit C n i))) r) ->
      (m : Nat) -> Eq (q i m) zero
    q-zero i li all m = route (EqNat-dec (q i m) zero)
      where
        route : Dec (Eq (q i m) zero) -> Eq (q i m) zero
        route (yes e)  = e
        route (no  ne) = Empty-elim (bad (snd (descent m i li ne)))
          where
            bad : Exits i -> Empty
            bad (mkSigma k ex) = ex (all k)

    --------------------------------------------------------------------
    -- THE THEOREM AT GENERAL ARITY r
    --
    -- One bounded search on the pointer map decides the two cases: the
    -- orbit of j leaves the block within r steps -- and then the index is
    -- constant from the exit depth on -- or it never leaves, and then no
    -- descent ever reaches a parameter, so the index is identically 0.
    --------------------------------------------------------------------

    main : (j : Nat) -> LeN (suc j) r -> EvConstN (q j)
    main j lj = route (find-exit r C r j)
      where
        route : Or (FirstExit r C r j) (AllRec r C r j) -> EvConstN (q j)
        route (inl (mkSigma t (mkSigma lt (mkSigma ir nt)))) =
          path-const t j lj ir nt
        route (inr all) =
          mkSigma zero (\ n _ -> Eq-trans (z n) (Eq-sym (z zero)))
          where
            z : (m : Nat) -> Eq (q j m) zero
            z = q-zero j lj (orbit-stays r C j lj all)
