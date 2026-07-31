{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.ReplayLv
--
-- THE REPLAY, FROM THE FULL TRACE:  l_c(n), i(n).
--
-- `BlkReplay` took the replay depth `nOf` as an abstract parameter.  That was
-- enough for the first round -- "either the computation reaches the threshold
-- or it is stuck before" -- but not for the second: to know whether a stick is
-- PERMANENT one has to know WHICH coordinate the walk is stuck on, and that is
-- read off the LEVEL coordinate `l_c(n)` of the trace, not off `i` and `k`.
--
-- So this module builds the replay from the levels:
--
--     lv c n     -- the level of coordinate c after n steps of the walk,
--                   `lv c (n+1) = lv c n + 1` if `c = iv n`, else unchanged
--     Adv av n   -- the walk can take step n at available heights `av`:
--                   `lv (iv n) n < av (iv n)`   (decidable)
--     nOf av     -- the first n at which it cannot: the STUCK STEP
--
-- and proves the two things a replay must satisfy:
--
--     stuck     -- `nOf av` really is stuck: the bounded search does not run
--                  out of fuel.  The fuel `sum av + 1` is justified by the
--                  DIAGONAL INVARIANT `sumLv`: after n advancing steps the
--                  levels total exactly n, and while advancing they stay below
--                  `av`, so there can be at most `sum av` of them.
--     nOf-mono  -- more available height cannot make the replay stop earlier.
--
-- `sumLv` is the manuscript's `l_1(n) + ... + l_a(n) = n`, here for the walk
-- of a single term, and it is exactly what makes the search bounded.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.ReplayLv where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using
  (plus ; plus-mono ; plus-suc-r ; le-ne-lt ; LeN-suc-not ; Eq-cong2 ;
   nle-lt ; le-nlt-eq)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus-zero-r : (a : Nat) -> Eq (plus a zero) a
plus-zero-r zero    = refl
plus-zero-r (suc a) = Eq-cong suc (plus-zero-r a)

------------------------------------------------------------------------
-- Bumping one coordinate of a level assignment
------------------------------------------------------------------------

bump : Nat -> (Nat -> Nat) -> Nat -> Nat
bump i f c with EqNat-dec c i
... | yes _ = suc (f c)
... | no  _ = f c

bump-eq : (i : Nat) (f : Nat -> Nat) (c : Nat) -> Eq c i ->
  Eq (bump i f c) (suc (f c))
bump-eq i f c e with EqNat-dec c i
... | yes _ = refl
... | no  n = Empty-elim (n e)

bump-ne : (i : Nat) (f : Nat -> Nat) (c : Nat) -> Not (Eq c i) ->
  Eq (bump i f c) (f c)
bump-ne i f c ne with EqNat-dec c i
... | yes e = Empty-elim (ne e)
... | no  _ = refl

------------------------------------------------------------------------
-- Sums over the first k coordinates
------------------------------------------------------------------------

sumTo : Nat -> (Nat -> Nat) -> Nat
sumTo zero    f = zero
sumTo (suc k) f = plus (f k) (sumTo k f)

sumTo-zero : (k : Nat) -> Eq (sumTo k (\ c -> zero)) zero
sumTo-zero zero    = refl
sumTo-zero (suc k) = sumTo-zero k

sumTo-mono : (k : Nat) (f g : Nat -> Nat) -> ((c : Nat) -> LeN (f c) (g c)) ->
  LeN (sumTo k f) (sumTo k g)
sumTo-mono zero    f g le = tt
sumTo-mono (suc k) f g le =
  plus-mono (f k) (g k) (sumTo k f) (sumTo k g) (le k) (sumTo-mono k f g le)

-- bumping outside the range does not change the sum
sumTo-bump-out : (k i : Nat) -> Not (LeN (suc i) k) -> (f : Nat -> Nat) ->
  Eq (sumTo k (bump i f)) (sumTo k f)
sumTo-bump-out zero    i nt f = refl
sumTo-bump-out (suc k) i nt f = head (EqNat-dec k i)
  where
    -- i is out of [0,k+1), so i > k
    nlt : Not (LeN i k)
    nlt l = nt (LeN-trans {suc i} {suc k} {suc k} l (LeN-refl (suc k)))

    ne : Not (Eq k i)
    ne e = nlt (Eq-transport (\ z -> LeN z k) e (LeN-refl k))

    rest : Eq (sumTo k (bump i f)) (sumTo k f)
    rest = sumTo-bump-out k i (\ l -> nlt (LeN-trans {i} {suc i} {k} (LeN-suc i) l)) f

    head : Dec (Eq k i) -> Eq (sumTo (suc k) (bump i f)) (sumTo (suc k) f)
    head (yes e) = Empty-elim (ne e)
    head (no  n) = Eq-cong2 plus (bump-ne i f k n) rest

-- bumping an in-range coordinate raises the sum by one
sumTo-bump : (k i : Nat) -> LeN (suc i) k -> (f : Nat -> Nat) ->
  Eq (sumTo k (bump i f)) (suc (sumTo k f))
sumTo-bump zero    i ()  f
sumTo-bump (suc k) i li  f = head (EqNat-dec k i)
  where
    head : Dec (Eq k i) -> Eq (sumTo (suc k) (bump i f)) (suc (sumTo (suc k) f))
    -- the bumped coordinate is the top one: the rest is untouched
    head (yes e) =
      Eq-cong2 plus (bump-eq i f k e)
        (sumTo-bump-out k i
          (\ l -> LeN-suc-not k (Eq-transport (\ z -> LeN (suc z) k) (Eq-sym e) l)) f)
    -- the bumped coordinate is below: recurse
    head (no  n) =
      Eq-trans
        (Eq-cong2 plus (bump-ne i f k n) (sumTo-bump k i (le-ne-lt i k li n) f))
        (plus-suc-r (f k) (sumTo k f))

------------------------------------------------------------------------
-- THE WALK OF ONE TERM, AND ITS REPLAY
------------------------------------------------------------------------

module _ (a : Nat) (iv : Nat -> Nat)
         (iv-range : (n : Nat) -> LeN (suc (iv n)) a) where

  -- l_c(n)
  lv : Nat -> Nat -> Nat
  lv c zero    = zero
  lv c (suc n) = bump (iv n) (\ d -> lv d n) c

  ----------------------------------------------------------------------
  -- THE DIAGONAL INVARIANT:  l_1(n) + ... + l_a(n) = n
  ----------------------------------------------------------------------

  sumLv : (n : Nat) -> Eq (sumTo a (\ c -> lv c n)) n
  sumLv zero    = sumTo-zero a
  sumLv (suc n) =
    Eq-trans (sumTo-bump a (iv n) (iv-range n) (\ c -> lv c n))
             (Eq-cong suc (sumLv n))

  ----------------------------------------------------------------------
  -- CAN THE WALK TAKE STEP n AT AVAILABLE HEIGHTS `av`?
  ----------------------------------------------------------------------

  Adv : (Nat -> Nat) -> Nat -> Set
  Adv av n = LeN (suc (lv (iv n) n)) (av (iv n))

  Adv-dec : (av : Nat -> Nat) (n : Nat) -> Dec (Adv av n)
  Adv-dec av n = LeN-dec (suc (lv (iv n) n)) (av (iv n))

  ----------------------------------------------------------------------
  -- THE REPLAY: advance while you can, with fuel
  ----------------------------------------------------------------------

  find : (Nat -> Nat) -> Nat -> Nat -> Nat
  find av n zero    = n
  find av n (suc F) with Adv-dec av n
  ... | no  _ = n
  ... | yes _ = find av (suc n) F

  find-yes : (av : Nat -> Nat) (n F : Nat) -> Adv av n ->
    Eq (find av n (suc F)) (find av (suc n) F)
  find-yes av n F ad with Adv-dec av n
  ... | yes _ = refl
  ... | no  x = Empty-elim (x ad)

  find-no : (av : Nat -> Nat) (n F : Nat) -> Not (Adv av n) ->
    Eq (find av n (suc F)) n
  find-no av n F nd with Adv-dec av n
  ... | yes x = Empty-elim (nd x)
  ... | no  _ = refl

  find-ge : (av : Nat -> Nat) (n F : Nat) -> LeN n (find av n F)
  find-ge av n zero    = LeN-refl n
  find-ge av n (suc F) with Adv-dec av n
  ... | no  _ = LeN-refl n
  ... | yes _ =
        LeN-trans {n} {suc n} {find av (suc n) F} (LeN-suc n) (find-ge av (suc n) F)

  -- more height, or more fuel, gets at least as far
  find-mono : (av av' : Nat -> Nat) -> ((c : Nat) -> LeN (av c) (av' c)) ->
    (n F F' : Nat) -> LeN F F' -> LeN (find av n F) (find av' n F')
  find-mono av av' le n zero    F'       lf = find-ge av' n F'
  find-mono av av' le n (suc F) zero     ()
  find-mono av av' le n (suc F) (suc F') lf with Adv-dec av n
  ... | no  _  = find-ge av' n (suc F')
  ... | yes ad = inner (Adv-dec av' n)
    where
      inner : Dec (Adv av' n) -> LeN (find av (suc n) F) (find av' n (suc F'))
      inner (yes ad') =
        Eq-transport (\ z -> LeN (find av (suc n) F) z)
          (Eq-sym (find-yes av' n F' ad'))
          (find-mono av av' le (suc n) F F' lf)
      inner (no nd) =
        Empty-elim
          (nd (LeN-trans {suc (lv (iv n) n)} {av (iv n)} {av' (iv n)} ad (le (iv n))))

  ----------------------------------------------------------------------
  -- WHILE ADVANCING, THE LEVELS STAY BELOW WHAT IS AVAILABLE
  ----------------------------------------------------------------------

  Below : (Nat -> Nat) -> Nat -> Set
  Below av n = (c : Nat) -> LeN (lv c n) (av c)

  find-below : (av : Nat -> Nat) (n F : Nat) -> Below av n -> Below av (find av n F)
  find-below av n zero    h = h
  find-below av n (suc F) h with Adv-dec av n
  ... | no  _  = h
  ... | yes ad = find-below av (suc n) F h'
    where
      h' : Below av (suc n)
      h' c = route (EqNat-dec c (iv n))
        where
          route : Dec (Eq c (iv n)) -> LeN (lv c (suc n)) (av c)
          route (yes e) =
            Eq-transport (\ z -> LeN z (av c))
              (Eq-sym (bump-eq (iv n) (\ d -> lv d n) c e))
              (Eq-transport (\ z -> LeN (suc (lv z n)) (av z)) (Eq-sym e) ad)
          route (no ne) =
            Eq-transport (\ z -> LeN z (av c))
              (Eq-sym (bump-ne (iv n) (\ d -> lv d n) c ne)) (h c)

  ----------------------------------------------------------------------
  -- THE SEARCH EITHER STICKS OR EXHAUSTS ITS FUEL
  ----------------------------------------------------------------------

  find-case : (av : Nat -> Nat) (n F : Nat) ->
    Or (Not (Adv av (find av n F))) (Eq (find av n F) (plus F n))
  find-case av n zero    = inr refl
  find-case av n (suc F) with Adv-dec av n
  ... | no  na = inl na
  ... | yes _  = route (find-case av (suc n) F)
    where
      route : Or (Not (Adv av (find av (suc n) F))) (Eq (find av (suc n) F) (plus F (suc n))) ->
              Or (Not (Adv av (find av (suc n) F))) (Eq (find av (suc n) F) (suc (plus F n)))
      route (inl x) = inl x
      route (inr e) = inr (Eq-trans e (plus-suc-r F n))

  ----------------------------------------------------------------------
  -- THE STUCK STEP
  ----------------------------------------------------------------------

  nOf : (Nat -> Nat) -> Nat
  nOf av = find av zero (suc (sumTo a av))

  -- the fuel suffices: `nOf av` really is where the walk sticks
  stuck : (av : Nat -> Nat) -> Not (Adv av (nOf av))
  stuck av = route (find-case av zero (suc (sumTo a av)))
    where
      -- if it had exhausted its fuel, the levels would total more than `av`
      route : Or (Not (Adv av (nOf av))) (Eq (nOf av) (plus (suc (sumTo a av)) zero)) ->
              Not (Adv av (nOf av))
      route (inl na) = na
      route (inr e)  = Empty-elim (LeN-suc-not (sumTo a av) big)
        where
          bel : Below av (nOf av)
          bel = find-below av zero (suc (sumTo a av)) (\ c -> tt)

          le1 : LeN (sumTo a (\ c -> lv c (nOf av))) (sumTo a av)
          le1 = sumTo-mono a (\ c -> lv c (nOf av)) av bel

          le2 : LeN (nOf av) (sumTo a av)
          le2 = Eq-transport (\ z -> LeN z (sumTo a av)) (sumLv (nOf av)) le1

          big : LeN (suc (sumTo a av)) (sumTo a av)
          big =
            Eq-transport (\ z -> LeN z (sumTo a av))
              (Eq-trans e (Eq-cong suc (plus-zero-r (sumTo a av)))) le2

  -- and it is monotone in the available heights
  nOf-mono : (av av' : Nat -> Nat) -> ((c : Nat) -> LeN (av c) (av' c)) ->
    LeN (nOf av) (nOf av')
  nOf-mono av av' le =
    find-mono av av' le zero (suc (sumTo a av)) (suc (sumTo a av'))
      (sumTo-mono a av av' le)

  ----------------------------------------------------------------------
  -- ADVANCING THROUGH A PREFIX
  ----------------------------------------------------------------------

  -- while every step advances, the levels stay below what is available
  levels-below : (av : Nat -> Nat) (t : Nat) ->
    ((n : Nat) -> LeN (suc n) t -> Adv av n) -> (c : Nat) -> LeN (lv c t) (av c)
  levels-below av zero    hh c = tt
  levels-below av (suc t) hh c = route (EqNat-dec c (iv t))
    where
      ih : (d : Nat) -> LeN (lv d t) (av d)
      ih = levels-below av t
             (\ n ln -> hh n (LeN-trans {suc n} {t} {suc t} ln (LeN-suc t)))

      route : Dec (Eq c (iv t)) -> LeN (lv c (suc t)) (av c)
      route (yes e) =
        Eq-transport (\ z -> LeN z (av c))
          (Eq-sym (bump-eq (iv t) (\ d -> lv d t) c e))
          (Eq-transport (\ z -> LeN (suc (lv z t)) (av z)) (Eq-sym e)
            (hh t (LeN-refl t)))
      route (no ne) =
        Eq-transport (\ z -> LeN z (av c))
          (Eq-sym (bump-ne (iv t) (\ d -> lv d t) c ne)) (ih c)

  -- if the first t steps all advance, the replay gets at least that far
  find-adv : (av : Nat -> Nat) (s t F : Nat) ->
    ((j : Nat) -> LeN (suc j) t -> Adv av (plus j s)) -> LeN t F ->
    LeN (plus t s) (find av s F)
  find-adv av s zero    F       hh lf = find-ge av s F
  find-adv av s (suc t) zero    hh ()
  find-adv av s (suc t) (suc F) hh lf =
    Eq-transport (\ z -> LeN (suc (plus t s)) z)
      (Eq-sym (find-yes av s F (hh zero tt)))
      (Eq-transport (\ z -> LeN z (find av (suc s) F))
        (plus-suc-r t s)
        (find-adv av (suc s) t F
          (\ j lj ->
             Eq-transport (\ z -> Adv av z) (Eq-sym (plus-suc-r j s)) (hh (suc j) lj))
          lf))

  nOf-ge : (av : Nat -> Nat) (t : Nat) ->
    ((n : Nat) -> LeN (suc n) t -> Adv av n) -> LeN t (nOf av)
  nOf-ge av t hh =
    Eq-transport (\ z -> LeN z (nOf av)) (plus-zero-r t)
      (find-adv av zero t (suc (sumTo a av))
        (\ j lj -> Eq-transport (\ z -> Adv av z) (Eq-sym (plus-zero-r j)) (hh j lj))
        fuel)
    where
      fuel : LeN t (suc (sumTo a av))
      fuel =
        LeN-trans {t} {sumTo a av} {suc (sumTo a av)}
          (Eq-transport (\ z -> LeN z (sumTo a av)) (sumLv t)
            (sumTo-mono a (\ c -> lv c t) av (levels-below av t hh)))
          (LeN-suc (sumTo a av))

  -- the replay cannot pass a step it can never take
  find-le : (av : Nat -> Nat) (s F n0 : Nat) -> LeN s n0 -> Not (Adv av n0) ->
    LeN (find av s F) n0
  find-le av s zero    n0 ls nb = ls
  find-le av s (suc F) n0 ls nb = route (Adv-dec av s)
    where
      route : Dec (Adv av s) -> LeN (find av s (suc F)) n0
      route (no na) =
        Eq-transport (\ z -> LeN z n0) (Eq-sym (find-no av s F na)) ls
      route (yes ad) =
        Eq-transport (\ z -> LeN z n0) (Eq-sym (find-yes av s F ad))
          (find-le av (suc s) F n0 (le-ne-lt s n0 ls ne) nb)
        where
          ne : Not (Eq n0 s)
          ne e = nb (Eq-transport (\ z -> Adv av z) (Eq-sym e) ad)

  -- the replay stops at or before any step it cannot take
  nOf-le : (av : Nat -> Nat) (n0 : Nat) -> Not (Adv av n0) -> LeN (nOf av) n0
  nOf-le av n0 nb = find-le av zero (suc (sumTo a av)) n0 tt nb

  -- ... so every step strictly below the stuck one DOES advance
  nOf-below-adv : (av : Nat -> Nat) (j : Nat) -> LeN (suc j) (nOf av) -> Adv av j
  nOf-below-adv av j lt = route (Adv-dec av j)
    where
      route : Dec (Adv av j) -> Adv av j
      route (yes ad)  = ad
      route (no  nad) =
        Empty-elim (LeN-suc-not j
          (LeN-trans {suc j} {nOf av} {j} lt (nOf-le av j nad)))

  -- more available height can only make a step easier to take
  Adv-mono : (av av' : Nat -> Nat) -> ((c : Nat) -> LeN (av c) (av' c)) ->
    (n : Nat) -> Adv av n -> Adv av' n
  Adv-mono av av' le n ad =
    LeN-trans {suc (lv (iv n) n)} {av (iv n)} {av' (iv n)} ad (le (iv n))

  -- the same available heights get exactly as far
  nOf-cong : (av av' : Nat -> Nat) -> ((c : Nat) -> Eq (av c) (av' c)) ->
    Eq (nOf av) (nOf av')
  nOf-cong av av' e =
    LeN-antisym {nOf av} {nOf av'}
      (nOf-mono av av' (\ c -> Eq-transport (\ z -> LeN (av c) z) (e c) (LeN-refl (av c))))
      (nOf-mono av' av (\ c -> Eq-transport (\ z -> LeN z (av c)) (e c) (LeN-refl (av c))))

  -- a walk step needs no more of a coordinate than the step number
  lv-le : (c n : Nat) -> LeN (lv c n) n
  lv-le c zero    = tt
  lv-le c (suc n) = route (EqNat-dec c (iv n))
    where
      route : Dec (Eq c (iv n)) -> LeN (lv c (suc n)) (suc n)
      route (yes e) =
        Eq-transport (\ z -> LeN z (suc n))
          (Eq-sym (bump-eq (iv n) (\ d -> lv d n) c e)) (lv-le c n)
      route (no ne) =
        Eq-transport (\ z -> LeN z (suc n))
          (Eq-sym (bump-ne (iv n) (\ d -> lv d n) c ne))
          (LeN-trans {lv c n} {n} {suc n} (lv-le c n) (LeN-suc n))

  ----------------------------------------------------------------------
  -- SATURATION: A COORDINATE ALREADY ABOVE THE BOUND STOPS MATTERING
  --
  -- A replay that stops before step T needs at most T-1 levels of any
  -- coordinate (`lv-le`).  So a coordinate whose available height is
  -- already at least T can never block it, and its exact value is
  -- irrelevant: two height vectors that agree everywhere else and are both
  -- at least T there give the SAME replay depth.
  --
  -- This is what breaks the deadlock of a bounded component next to an
  -- unbounded one: once the growing coordinate is past the threshold, the
  -- bounded one's replay is a function of the bounded coordinates alone.
  ----------------------------------------------------------------------

  nOf-sat : (av av' : Nat -> Nat) (T c : Nat) ->
    ((d : Nat) -> Not (Eq d c) -> Eq (av d) (av' d)) ->
    LeN T (av c) -> LeN T (av' c) ->
    Not (LeN T (nOf av)) -> Eq (nOf av) (nOf av')
  nOf-sat av av' T c agree lc lc' nlt =
    LeN-antisym {nOf av} {nOf av'} (nOf-ge av' (nOf av) up) (nOf-le av' (nOf av) nadv')
    where
      ltT : LeN (suc (nOf av)) T
      ltT = nle-lt T (nOf av) nlt

      -- a step below the stuck one needs less than T of any coordinate
      small : (n : Nat) -> LeN (suc n) (nOf av) -> LeN (suc (lv (iv n) n)) T
      small n ln =
        LeN-trans {suc (lv (iv n) n)} {suc n} {T}
          (lv-le (iv n) n)
          (LeN-trans {suc n} {nOf av} {T} ln
            (LeN-trans {nOf av} {suc (nOf av)} {T} (LeN-suc (nOf av)) ltT))

      up : (n : Nat) -> LeN (suc n) (nOf av) -> Adv av' n
      up n ln = route (EqNat-dec (iv n) c)
        where
          route : Dec (Eq (iv n) c) -> Adv av' n
          route (yes e) =
            LeN-trans {suc (lv (iv n) n)} {T} {av' (iv n)} (small n ln)
              (Eq-transport (\ z -> LeN T (av' z)) (Eq-sym e) lc')
          route (no ne) =
            Eq-transport (\ z -> LeN (suc (lv (iv n) n)) z)
              (agree (iv n) ne) (nOf-below-adv av n ln)

      nadv' : Not (Adv av' (nOf av))
      nadv' ad = stuck av (route (EqNat-dec (iv (nOf av)) c))
        where
          -- the stuck coordinate cannot be the saturated one: at level
          -- below T it would have advanced there
          route : Dec (Eq (iv (nOf av)) c) -> Adv av (nOf av)
          route (yes e) =
            LeN-trans {suc (lv (iv (nOf av)) (nOf av))} {T} {av (iv (nOf av))}
              (LeN-trans {suc (lv (iv (nOf av)) (nOf av))} {suc (nOf av)} {T}
                (lv-le (iv (nOf av)) (nOf av)) ltT)
              (Eq-transport (\ z -> LeN T (av z)) (Eq-sym e) lc)
          route (no ne) =
            Eq-transport (\ z -> LeN (suc (lv (iv (nOf av)) (nOf av))) z)
              (Eq-sym (agree (iv (nOf av)) ne)) ad

  ----------------------------------------------------------------------
  -- PERMANENCE: A STICK ON A COORDINATE THAT DOES NOT GROW IS FOR EVER
  --
  -- `nOf av` is the first step the walk cannot take.  Raising the available
  -- heights can only move it up (`nOf-mono`); but if the coordinate it is
  -- stuck on has NOT been raised, it is still stuck exactly there, so the
  -- replay depth does not move at all.
  --
  -- Instantiated at a block's depth chain, where the parameters are constant,
  -- this says: once a step term demands a parameter it demands that same
  -- parameter for ever.
  ----------------------------------------------------------------------

  nOf-freeze : (av av' : Nat -> Nat) -> ((c : Nat) -> LeN (av c) (av' c)) ->
    Eq (av' (iv (nOf av))) (av (iv (nOf av))) -> Eq (nOf av') (nOf av)
  nOf-freeze av av' le e =
    LeN-antisym {nOf av'} {nOf av}
      (find-le av' zero (suc (sumTo a av')) (nOf av) tt notadv)
      (nOf-mono av av' le)
    where
      notadv : Not (Adv av' (nOf av))
      notadv ad =
        stuck av
          (Eq-transport (\ z -> LeN (suc (lv (iv (nOf av)) (nOf av))) z) e ad)

  ----------------------------------------------------------------------
  -- ROUND 2: THE REPLAY ALONG A MONOTONE FAMILY OF AVAILABLE HEIGHTS
  --
  -- Each coordinate comes with a verdict: either it is CAPPED (bounded by a
  -- value it does reach) or UNBOUNDED.  Then the index of the replay is
  -- eventually constant, and the argument is a bounded search over the
  -- finitely many steps below the term's own threshold:
  --
  --   * a step whose demanded coordinate is capped at or below the level the
  --     walk needs there is blocked FOR EVER;
  --   * every other step is eventually taken.
  --
  -- So either some step below the threshold blocks -- and the replay settles
  -- exactly there -- or none does, the replay passes the threshold, and the
  -- index is the term's own eventual one.
  ----------------------------------------------------------------------

  Cap : (Nat -> Nat -> Nat) -> Nat -> Set
  Cap av c =
    Sigma Nat (\ V -> Pair ((m : Nat) -> LeN (av m c) V)
                           (Sigma Nat (\ M -> LeN V (av M c))))

  Unb : (Nat -> Nat -> Nat) -> Nat -> Set
  Unb av c = (k : Nat) -> Sigma Nat (\ m -> LeN k (av m c))

  module Round2 (av : Nat -> Nat -> Nat)
                (av-step : (m c : Nat) -> LeN (av m c) (av (suc m) c))
                (N I : Nat)
                (iv-stab : (n : Nat) -> LeN N n -> Eq (iv n) I)
                (verd : (c : Nat) -> Or (Cap av c) (Unb av c))
                where

    av-le : (m m' c : Nat) -> LeN m m' -> LeN (av m c) (av m' c)
    av-le m zero     c le =
      Eq-transport (\ z -> LeN (av z c) (av zero c))
        (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (av zero c))
    av-le m (suc m') c le with LeN-dec m m'
    ... | yes l  =
          LeN-trans {av m c} {av m' c} {av (suc m') c}
            (av-le m m' c l) (av-step m' c)
    ... | no  nl =
          Eq-transport (\ z -> LeN (av z c) (av (suc m') c))
            (Eq-sym (le-nlt-eq' m m' le nl)) (LeN-refl (av (suc m') c))
      where
        le-nlt-eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
        le-nlt-eq' zero    y  l nl' = Empty-elim (nl' tt)
        le-nlt-eq' (suc x) zero l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
        le-nlt-eq' (suc x) (suc y) l nl' = Eq-cong suc (le-nlt-eq' x y l nl')

    EvAdv : Nat -> Set
    EvAdv n = Sigma Nat (\ m0 -> (m : Nat) -> LeN m0 m -> Adv (av m) n)

    Blk : Nat -> Set
    Blk n = (m : Nat) -> Not (Adv (av m) n)

    ------------------------------------------------------------------
    -- every step is blocked for ever, or eventually taken -- DECIDED
    ------------------------------------------------------------------

    blk : (n : Nat) -> Or (Blk n) (EvAdv n)
    blk n = route (verd (iv n))
      where
        L0 : Nat
        L0 = lv (iv n) n

        route : Or (Cap av (iv n)) (Unb av (iv n)) -> Or (Blk n) (EvAdv n)
        route (inr unb) =
          inr (mkSigma (fst (unb (suc L0)))
                (\ m lm ->
                   LeN-trans {suc L0} {av (fst (unb (suc L0))) (iv n)} {av m (iv n)}
                     (snd (unb (suc L0))) (av-le (fst (unb (suc L0))) m (iv n) lm)))
        route (inl (mkSigma V (mkSigma cap (mkSigma M reach)))) =
          inner (LeN-dec V L0)
          where
            inner : Dec (LeN V L0) -> Or (Blk n) (EvAdv n)
            -- the cap is at or below what the walk needs: blocked for ever
            inner (yes lvV) =
              inl (\ m ad ->
                LeN-suc-not L0
                  (LeN-trans {suc L0} {av m (iv n)} {L0} ad
                    (LeN-trans {av m (iv n)} {V} {L0} (cap m) lvV)))
            -- the cap is above it, and is reached: eventually taken
            inner (no nlvV) =
              inr (mkSigma M
                (\ m lm ->
                   LeN-trans {suc L0} {av M (iv n)} {av m (iv n)}
                     (LeN-trans {suc L0} {V} {av M (iv n)} (nle-lt V L0 nlvV) reach)
                     (av-le M m (iv n) lm)))

    ------------------------------------------------------------------
    -- a common threshold for finitely many steps
    ------------------------------------------------------------------

    allAdv : (t : Nat) -> ((j : Nat) -> LeN (suc j) t -> EvAdv j) ->
      Sigma Nat (\ m0 -> (m : Nat) -> LeN m0 m -> (j : Nat) -> LeN (suc j) t ->
                         Adv (av m) j)
    allAdv zero    hh = mkSigma zero (\ m lm j ())
    allAdv (suc t) hh = mkSigma (maxN m1 m2) go
      where
        r1 = allAdv t (\ j lj -> hh j (LeN-trans {suc j} {t} {suc t} lj (LeN-suc t)))
        m1 = fst r1
        r2 = hh t (LeN-refl t)
        m2 = fst r2

        go : (m : Nat) -> LeN (maxN m1 m2) m -> (j : Nat) -> LeN (suc j) (suc t) ->
             Adv (av m) j
        go m lm j lj with LeN-dec (suc j) t
        ... | yes l  =
              snd r1 m (LeN-trans {m1} {maxN m1 m2} {m} (maxN-le-l m1 m2) lm) j l
        ... | no  nl =
              Eq-transport (\ z -> Adv (av m) z) (Eq-sym (le-nlt-eq j t lj nl))
                (snd r2 m (LeN-trans {m2} {maxN m1 m2} {m} (maxN-le-r m1 m2) lm))

    ------------------------------------------------------------------
    -- the bounded search for the first blocked step below the threshold
    ------------------------------------------------------------------

    Found : Nat -> Set
    Found n0 = Pair ((j : Nat) -> LeN (suc j) n0 -> EvAdv j) (Blk n0)

    scan : (t : Nat) ->
      Or (Sigma Nat (\ n0 -> Found n0)) ((j : Nat) -> LeN (suc j) t -> EvAdv j)
    scan zero    = inr (\ j ())
    scan (suc t) = route (scan t)
      where
        route : Or (Sigma Nat (\ n0 -> Found n0)) ((j : Nat) -> LeN (suc j) t -> EvAdv j) ->
                Or (Sigma Nat (\ n0 -> Found n0)) ((j : Nat) -> LeN (suc j) (suc t) -> EvAdv j)
        route (inl f)  = inl f
        route (inr hh) = route2 (blk t)
          where
            route2 : Or (Blk t) (EvAdv t) ->
              Or (Sigma Nat (\ n0 -> Found n0)) ((j : Nat) -> LeN (suc j) (suc t) -> EvAdv j)
            route2 (inl bt) = inl (mkSigma t (mkSigma hh bt))
            route2 (inr et) = inr ext
              where
                ext : (j : Nat) -> LeN (suc j) (suc t) -> EvAdv j
                ext j lj with LeN-dec (suc j) t
                ... | yes l  = hh j l
                ... | no  nl =
                      Eq-transport EvAdv (Eq-sym (le-nlt-eq j t lj nl)) et

    ------------------------------------------------------------------
    -- THE RESULT: the index of the replay is eventually constant
    ------------------------------------------------------------------

    result : Sigma Nat (\ M0 -> (m : Nat) -> LeN M0 m ->
                                Eq (iv (nOf (av m))) (iv (nOf (av M0))))
    result = route (scan N)
      where
        -- a blocked step below the threshold: the replay settles exactly there
        route : Or (Sigma Nat (\ n0 -> Found n0)) ((j : Nat) -> LeN (suc j) N -> EvAdv j) ->
          Sigma Nat (\ M0 -> (m : Nat) -> LeN M0 m ->
                             Eq (iv (nOf (av m))) (iv (nOf (av M0))))
        route (inl (mkSigma n0 (mkSigma pre bl))) = mkSigma m0 go
          where
            r  = allAdv n0 pre
            m0 = fst r

            at : (m : Nat) -> LeN m0 m -> Eq (nOf (av m)) n0
            at m lm =
              LeN-antisym {nOf (av m)} {n0}
                (find-le (av m) zero (suc (sumTo a (av m))) n0 tt (bl m))
                (nOf-ge (av m) n0 (\ n ln -> snd r m lm n ln))

            go : (m : Nat) -> LeN m0 m -> Eq (iv (nOf (av m))) (iv (nOf (av m0)))
            go m lm =
              Eq-trans (Eq-cong iv (at m lm))
                       (Eq-sym (Eq-cong iv (at m0 (LeN-refl m0))))
        -- no blocked step below the threshold: the replay passes it
        route (inr hh) = mkSigma m0 go
          where
            r  = allAdv N hh
            m0 = fst r

            at : (m : Nat) -> LeN m0 m -> Eq (iv (nOf (av m))) I
            at m lm = iv-stab (nOf (av m)) (nOf-ge (av m) N (\ n ln -> snd r m lm n ln))

            go : (m : Nat) -> LeN m0 m -> Eq (iv (nOf (av m))) (iv (nOf (av m0)))
            go m lm = Eq-trans (at m lm) (Eq-sym (at m0 (LeN-refl m0)))
