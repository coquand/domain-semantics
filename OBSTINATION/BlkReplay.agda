{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkReplay
--
-- "EITHER THE COMPUTATION REACHES THE THRESHOLD, OR IT IS STUCK BEFORE" --
-- MADE COMPUTABLE, USING k.
--
-- A two-component block, analysed purely through the TRACES of its step
-- terms.  Writing `h j m` for the output height of component j at recursion
-- depth m, the block is a computable iteration on the pair of heights:
--
--     nOf j h0 h1  -- how far g_j's own walk can be replayed when its
--                     arguments have heights (h0, h1); monotone in them
--     h j (m+1)    = kv j (nOf j (h 0 m) (h 1 m))
--     c j m        = iv j (nOf j (h 0 m) (h 1 m))     -- the step index
--
-- with `iv j`, `kv j` the index and output-height coordinates of g_j's trace.
-- The induction hypothesis is `iv-stab`: `iv j n = I j` for `n >= N j`.
--
-- THE POINT.  Let `K j` bound `kv j` BELOW the threshold, and run the
-- iteration for `K 0 + K 1 + 1` steps.  The state is componentwise
-- non-decreasing and the map is deterministic, so a repeated state is a FIXED
-- POINT (`rep-stays`).  Hence exactly one of:
--
--   * the state repeated -- everything is constant from there, in particular
--     every step index (`rep-const`);
--   * it never repeated -- then every step raised the total by at least one
--     (`no-rep-inc`), so the total exceeds `K 0 + K 1`, so some `h j` exceeds
--     `K j`, which by the bound forces `nOf j` PAST the threshold `N j`; and
--     `nOf j` being monotone it stays past it, so `c j` is constantly `I j`
--     (`past-const`).
--
-- `decide` is that dichotomy, by bounded search.  It appeals nowhere to "a
-- bounded monotone sequence converges" -- which is exactly what carrying `k`
-- buys, and what the index-only induction hypothesis could not supply.
--
-- Everything here is the numeric dynamics: the step terms enter only through
-- `nOf`, `iv`, `kv`, `N`, `I`, `K`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkReplay where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus : Nat -> Nat -> Nat
plus zero    b = b
plus (suc a) b = suc (plus a b)

plus-ge-r : (a b : Nat) -> LeN b (plus a b)
plus-ge-r zero    b = LeN-refl b
plus-ge-r (suc a) b =
  LeN-trans {b} {plus a b} {suc (plus a b)} (plus-ge-r a b) (LeN-suc (plus a b))

plus-mono : (a a' b b' : Nat) -> LeN a a' -> LeN b b' ->
  LeN (plus a b) (plus a' b')
plus-mono zero    a'       b b' la lb =
  LeN-trans {b} {b'} {plus a' b'} lb (plus-ge-r a' b')
plus-mono (suc a) zero     b b' ()  lb
plus-mono (suc a) (suc a') b b' la lb = plus-mono a a' b b' la lb

plus-suc-r : (a b : Nat) -> Eq (plus a (suc b)) (suc (plus a b))
plus-suc-r zero    b = refl
plus-suc-r (suc a) b = Eq-cong suc (plus-suc-r a b)

plus-lt-l : (a a' b b' : Nat) -> LeN (suc a) a' -> LeN b b' ->
  LeN (suc (plus a b)) (plus a' b')
plus-lt-l a a' b b' la lb = plus-mono (suc a) a' b b' la lb

plus-lt-r : (a a' b b' : Nat) -> LeN a a' -> LeN (suc b) b' ->
  LeN (suc (plus a b)) (plus a' b')
plus-lt-r a a' b b' la lb =
  Eq-transport (\ z -> LeN z (plus a' b')) (plus-suc-r a b)
    (plus-mono a a' (suc b) b' la lb)

le-ne-lt : (a b : Nat) -> LeN a b -> Not (Eq b a) -> LeN (suc a) b
le-ne-lt zero    zero    le ne = Empty-elim (ne refl)
le-ne-lt zero    (suc b) le ne = tt
le-ne-lt (suc a) zero    () ne
le-ne-lt (suc a) (suc b) le ne = le-ne-lt a b le (\ e -> ne (Eq-cong suc e))

nle-lt : (a b : Nat) -> Not (LeN a b) -> LeN (suc b) a
nle-lt zero    b       nt = Empty-elim (nt tt)
nle-lt (suc a) zero    nt = tt
nle-lt (suc a) (suc b) nt = nle-lt a b nt

le-nlt-eq : (a b : Nat) -> LeN a b -> Not (LeN (suc a) b) -> Eq a b
le-nlt-eq zero    zero    le nt = refl
le-nlt-eq zero    (suc b) le nt = Empty-elim (nt tt)
le-nlt-eq (suc a) zero    () nt
le-nlt-eq (suc a) (suc b) le nt = Eq-cong suc (le-nlt-eq a b le nt)

LeN-suc-not : (a : Nat) -> LeN (suc a) a -> Empty
LeN-suc-not zero    ()
LeN-suc-not (suc a) le = LeN-suc-not a le

Eq-cong2 : {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f refl refl = refl

one : Nat
one = suc zero

two : Nat
two = suc (suc zero)

plus-cancel : (k a b : Nat) -> LeN (plus a k) (plus b k) -> LeN a b
plus-cancel k zero    b       le = tt
plus-cancel k (suc a) zero    le =
  Empty-elim (LeN-suc-not (plus a k)
    (LeN-trans {suc (plus a k)} {k} {plus a k} le (plus-ge-r a k)))
plus-cancel k (suc a) (suc b) le = plus-cancel k a b le

------------------------------------------------------------------------
-- A MONOTONE SEQUENCE BOUNDED BY B REPEATS WITHIN B+1 STEPS OF ANY START
------------------------------------------------------------------------

module _ (v : Nat -> Nat) (B M0 : Nat)
         (v-mono : (m : Nat) -> LeN (v m) (v (suc m)))
         (v-bdd  : (m : Nat) -> LeN (v m) B) where

  Rp : Nat -> Set
  Rp j = Eq (v (suc (plus j M0))) (v (plus j M0))

  -- t strictly increasing steps from M0 push v up by t
  climb : (t : Nat) -> ((j : Nat) -> LeN (suc j) t -> Not (Rp j)) ->
    LeN t (v (plus t M0))
  climb zero    nn = tt
  climb (suc t) nn =
    LeN-trans {suc t} {suc (v (plus t M0))} {v (suc (plus t M0))}
      (climb t (\ j lj -> nn j (LeN-trans {suc j} {t} {suc t} lj (LeN-suc t))))
      (le-ne-lt (v (plus t M0)) (v (suc (plus t M0)))
        (v-mono (plus t M0)) (nn t (LeN-refl t)))

  searchRp : (t : Nat) ->
    Or (Sigma Nat (\ j -> Pair (LeN (suc j) t) (Rp j)))
       ((j : Nat) -> LeN (suc j) t -> Not (Rp j))
  searchRp zero    = inr (\ j ())
  searchRp (suc t) = route (searchRp t)
    where
      route : Or (Sigma Nat (\ j -> Pair (LeN (suc j) t) (Rp j)))
                 ((j : Nat) -> LeN (suc j) t -> Not (Rp j)) ->
              Or (Sigma Nat (\ j -> Pair (LeN (suc j) (suc t)) (Rp j)))
                 ((j : Nat) -> LeN (suc j) (suc t) -> Not (Rp j))
      route (inl (mkSigma j (mkSigma lj rj))) =
        inl (mkSigma j (mkSigma (LeN-trans {suc j} {t} {suc t} lj (LeN-suc t)) rj))
      route (inr nn) = route2 (EqNat-dec (v (suc (plus t M0))) (v (plus t M0)))
        where
          route2 : Dec (Rp t) ->
            Or (Sigma Nat (\ j -> Pair (LeN (suc j) (suc t)) (Rp j)))
               ((j : Nat) -> LeN (suc j) (suc t) -> Not (Rp j))
          route2 (yes rt) = inl (mkSigma t (mkSigma (LeN-refl t) rt))
          route2 (no  nt) = inr ext
            where
              ext : (j : Nat) -> LeN (suc j) (suc t) -> Not (Rp j)
              ext j lj with LeN-dec (suc j) t
              ... | yes l  = nn j l
              ... | no  nl = Eq-transport (\ z -> Not (Rp z)) (Eq-sym (le-nlt-eq j t lj nl)) nt

  mono-bdd-rep : Sigma Nat (\ m -> Pair (LeN M0 m) (Eq (v (suc m)) (v m)))
  mono-bdd-rep = route (searchRp (suc B))
    where
      route : Or (Sigma Nat (\ j -> Pair (LeN (suc j) (suc B)) (Rp j)))
                 ((j : Nat) -> LeN (suc j) (suc B) -> Not (Rp j)) ->
              Sigma Nat (\ m -> Pair (LeN M0 m) (Eq (v (suc m)) (v m)))
      route (inl (mkSigma j (mkSigma lj rj))) =
        mkSigma (plus j M0) (mkSigma (plus-ge-r j M0) rj)
      route (inr nn) =
        Empty-elim
          (LeN-suc-not B
            (LeN-trans {suc B} {v (plus (suc B) M0)} {B}
              (climb (suc B) nn) (v-bdd (plus (suc B) M0))))

------------------------------------------------------------------------
-- THE ITERATION
------------------------------------------------------------------------

module _ (nOf : Nat -> Nat -> Nat -> Nat)
         (iv  : Nat -> Nat -> Nat)
         (kv  : Nat -> Nat -> Nat)
         (N I K : Nat -> Nat)
         (nOf-mono : (j a a' b b' : Nat) -> LeN a a' -> LeN b b' ->
                     LeN (nOf j a b) (nOf j a' b'))
         (kv-mono  : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         (kv-bound : (j n : Nat) -> Not (LeN (N j) n) -> LeN (kv j n) (K j))
         (iv-stab  : (j n : Nat) -> LeN (N j) n -> Eq (iv j n) (I j))
         where

  h : Nat -> Nat -> Nat
  h j zero    = zero
  h j (suc m) = kv j (nOf j (h zero m) (h one m))

  step : Nat -> Nat -> Nat
  step j m = nOf j (h zero m) (h one m)

  c : Nat -> Nat -> Nat
  c j m = iv j (step j m)

  ----------------------------------------------------------------------
  -- The state is componentwise non-decreasing
  ----------------------------------------------------------------------

  h-mono1 : (m j : Nat) -> LeN (h j m) (h j (suc m))
  h-mono1 zero    j = tt
  h-mono1 (suc m) j =
    kv-mono j (nOf j (h zero m) (h one m)) (nOf j (h zero (suc m)) (h one (suc m)))
      (nOf-mono j (h zero m) (h zero (suc m)) (h one m) (h one (suc m))
        (h-mono1 m zero) (h-mono1 m one))

  h-mono : (j m m' : Nat) -> LeN m m' -> LeN (h j m) (h j m')
  h-mono j m zero     le =
    Eq-transport (\ z -> LeN (h j z) (h j zero))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (h j zero))
  h-mono j m (suc m') le with LeN-dec m m'
  ... | yes l  =
        LeN-trans {h j m} {h j m'} {h j (suc m')}
          (h-mono j m m' l) (h-mono1 m' j)
  ... | no  nl =
        Eq-transport (\ z -> LeN (h j z) (h j (suc m')))
          (Eq-sym (le-eq m m' le nl)) (LeN-refl (h j (suc m')))
    where
      le-eq : (a b : Nat) -> LeN a (suc b) -> Not (LeN a b) -> Eq a (suc b)
      le-eq zero    b       l nl' = Empty-elim (nl' tt)
      le-eq (suc a) zero    l nl' = Eq-cong suc (LeN-antisym {a} {zero} l tt)
      le-eq (suc a) (suc b) l nl' = Eq-cong suc (le-eq a b l nl')

  step-mono : (j m m' : Nat) -> LeN m m' -> LeN (step j m) (step j m')
  step-mono j m m' le =
    nOf-mono j (h zero m) (h zero m') (h one m) (h one m')
      (h-mono zero m m' le) (h-mono one m m' le)

  ----------------------------------------------------------------------
  -- A REPEATED STATE IS A FIXED POINT
  ----------------------------------------------------------------------

  Rep : Nat -> Set
  Rep m = Pair (Eq (h zero (suc m)) (h zero m)) (Eq (h one (suc m)) (h one m))

  Rep-dec : (m : Nat) -> Dec (Rep m)
  Rep-dec m with EqNat-dec (h zero (suc m)) (h zero m)
  ... | no  n0 = no (\ p -> n0 (fst p))
  ... | yes e0 with EqNat-dec (h one (suc m)) (h one m)
  ...   | no  n1 = no (\ p -> n1 (snd p))
  ...   | yes e1 = yes (mkSigma e0 e1)

  -- the state map is deterministic
  state-cong : (a b : Nat) -> Eq (h zero a) (h zero b) -> Eq (h one a) (h one b) ->
    (j : Nat) -> Eq (h j (suc a)) (h j (suc b))
  state-cong a b e0 e1 j = Eq-cong (kv j) (Eq-cong2 (nOf j) e0 e1)

  rep-stays : (m : Nat) -> Rep m -> (n : Nat) -> LeN m n ->
    Pair (Eq (h zero n) (h zero m)) (Eq (h one n) (h one m))
  rep-stays m rp zero    le =
    Eq-transport
      (\ z -> Pair (Eq (h zero zero) (h zero z)) (Eq (h one zero) (h one z)))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (mkSigma refl refl)
  rep-stays m rp (suc n) le with LeN-dec m n
  ... | yes l  =
        mkSigma
          (Eq-trans (state-cong n m (fst ih) (snd ih) zero) (fst rp))
          (Eq-trans (state-cong n m (fst ih) (snd ih) one)  (snd rp))
    where
      ih : Pair (Eq (h zero n) (h zero m)) (Eq (h one n) (h one m))
      ih = rep-stays m rp n l
  ... | no  nl =
        Eq-transport
          (\ z -> Pair (Eq (h zero (suc n)) (h zero z)) (Eq (h one (suc n)) (h one z)))
          (Eq-sym (le-nlt-eq' m n le nl)) (mkSigma refl refl)
    where
      le-nlt-eq' : (a b : Nat) -> LeN a (suc b) -> Not (LeN a b) -> Eq a (suc b)
      le-nlt-eq' zero    b       l nl' = Empty-elim (nl' tt)
      le-nlt-eq' (suc a) zero    l nl' = Eq-cong suc (LeN-antisym {a} {zero} l tt)
      le-nlt-eq' (suc a) (suc b) l nl' = Eq-cong suc (le-nlt-eq' a b l nl')

  ----------------------------------------------------------------------
  -- WITHOUT A REPEAT, THE TOTAL HEIGHT GROWS BY AT LEAST ONE PER STEP
  ----------------------------------------------------------------------

  sumh : Nat -> Nat
  sumh m = plus (h zero m) (h one m)

  no-rep-inc : (m : Nat) -> Not (Rep m) -> LeN (suc (sumh m)) (sumh (suc m))
  no-rep-inc m nr with EqNat-dec (h zero (suc m)) (h zero m)
  ... | no  n0 =
        plus-lt-l (h zero m) (h zero (suc m)) (h one m) (h one (suc m))
          (le-ne-lt (h zero m) (h zero (suc m)) (h-mono1 m zero) n0)
          (h-mono1 m one)
  ... | yes e0 =
        plus-lt-r (h zero m) (h zero (suc m)) (h one m) (h one (suc m))
          (h-mono1 m zero)
          (le-ne-lt (h one m) (h one (suc m)) (h-mono1 m one)
            (\ e1 -> nr (mkSigma e0 e1)))

  no-rep-sum : (T : Nat) -> ((m : Nat) -> LeN (suc m) T -> Not (Rep m)) ->
    LeN T (sumh T)
  no-rep-sum zero    nn = tt
  no-rep-sum (suc T) nn =
    LeN-trans {suc T} {suc (sumh T)} {sumh (suc T)}
      (no-rep-sum T (\ m lm -> nn m (LeN-trans {suc m} {T} {suc T} lm (LeN-suc T))))
      (no-rep-inc T (nn T (LeN-refl T)))

  ----------------------------------------------------------------------
  -- THE BOUNDED SEARCH
  ----------------------------------------------------------------------

  findRep : (T : Nat) ->
    Or (Sigma Nat (\ m -> Rep m)) ((m : Nat) -> LeN (suc m) T -> Not (Rep m))
  findRep zero    = inr (\ m ())
  findRep (suc T) = route (findRep T)
    where
      route : Or (Sigma Nat (\ m -> Rep m)) ((m : Nat) -> LeN (suc m) T -> Not (Rep m)) ->
        Or (Sigma Nat (\ m -> Rep m)) ((m : Nat) -> LeN (suc m) (suc T) -> Not (Rep m))
      route (inl f)  = inl f
      route (inr nn) = route2 (Rep-dec T)
        where
          route2 : Dec (Rep T) ->
            Or (Sigma Nat (\ m -> Rep m)) ((m : Nat) -> LeN (suc m) (suc T) -> Not (Rep m))
          route2 (yes rp) = inl (mkSigma T rp)
          route2 (no  nr) = inr ext
            where
              ext : (m : Nat) -> LeN (suc m) (suc T) -> Not (Rep m)
              ext m lm with LeN-dec (suc m) T
              ... | yes l  = nn m l
              ... | no  nl = Eq-transport (\ z -> Not (Rep z)) (Eq-sym (le-nlt-eq m T lm nl)) nr

  ----------------------------------------------------------------------
  -- THE DICHOTOMY
  ----------------------------------------------------------------------

  Tm : Nat
  Tm = plus (K zero) (K one)

  decide :
    Or (Sigma Nat (\ m -> Rep m))
       (Sigma Nat (\ j -> LeN (N j) (step j Tm)))
  decide = route (findRep (suc Tm))
    where
      route : Or (Sigma Nat (\ m -> Rep m))
                 ((m : Nat) -> LeN (suc m) (suc Tm) -> Not (Rep m)) ->
        Or (Sigma Nat (\ m -> Rep m)) (Sigma Nat (\ j -> LeN (N j) (step j Tm)))
      route (inl f)  = inl f
      route (inr nn) = inr (pick (LeN-dec (h zero (suc Tm)) (K zero)))
        where
          big : LeN (suc Tm) (sumh (suc Tm))
          big = no-rep-sum (suc Tm) nn

          -- from `h j (suc Tm) > K j` the replay is past the threshold
          past : (j : Nat) -> Not (LeN (h j (suc Tm)) (K j)) ->
            LeN (N j) (step j Tm)
          past j nb = route2 (LeN-dec (N j) (step j Tm))
            where
              route2 : Dec (LeN (N j) (step j Tm)) -> LeN (N j) (step j Tm)
              route2 (yes l) = l
              route2 (no  n) = Empty-elim (nb (kv-bound j (step j Tm) n))

          pick : Dec (LeN (h zero (suc Tm)) (K zero)) ->
            Sigma Nat (\ j -> LeN (N j) (step j Tm))
          pick (no  n0) = mkSigma zero (past zero n0)
          pick (yes l0) = mkSigma one (past one n1)
            where
              n1 : Not (LeN (h one (suc Tm)) (K one))
              n1 l1 =
                LeN-suc-not Tm
                  (LeN-trans {suc Tm} {sumh (suc Tm)} {Tm} big
                    (plus-mono (h zero (suc Tm)) (K zero)
                               (h one (suc Tm)) (K one) l0 l1))

  ----------------------------------------------------------------------
  -- EITHER WAY, THE STEP INDEX SETTLES
  ----------------------------------------------------------------------

  -- past the threshold: the index is the trace's eventual one
  past-const : (j : Nat) -> LeN (N j) (step j Tm) -> EvConstN (c j)
  past-const j pj = mkSigma Tm go
    where
      at : (m : Nat) -> LeN Tm m -> Eq (c j m) (I j)
      at m lm =
        iv-stab j (step j m)
          (LeN-trans {N j} {step j Tm} {step j m} pj (step-mono j Tm m lm))

      go : (n : Nat) -> LeN Tm n -> Eq (c j n) (c j Tm)
      go n ln = Eq-trans (at n ln) (Eq-sym (at Tm (LeN-refl Tm)))

  -- a fixed point: everything is constant from there
  rep-const : (m : Nat) -> Rep m -> (j : Nat) -> EvConstN (c j)
  rep-const m rp j = mkSigma m go
    where
      go : (n : Nat) -> LeN m n -> Eq (c j n) (c j m)
      go n ln =
        Eq-cong (\ z -> iv j z)
          (Eq-cong2 (nOf j) (fst (rep-stays m rp n ln)) (snd (rep-stays m rp n ln)))

  ----------------------------------------------------------------------
  -- THE GROWTH LOWER BOUND
  --
  -- The counting says the TOTAL rises by at least one per non-repeating
  -- step.  So if one component is capped, the OTHER one must be carrying the
  -- growth, and it does so at least linearly:
  --
  --     no repeat up to T  and  h 1 T <= V   ==>   T <= h 0 T + V
  --
  -- This is what turns "does h 0 grow?" -- the self-referential question that
  -- blocked the second round -- into an explicit bound: once T exceeds
  -- V plus the largest level g_1's walk demands of coordinate 0 below its own
  -- threshold (at most N 1), coordinate 0 can no longer be what is holding
  -- g_1's replay back.  From there the replay depth of g_1 depends only on
  -- h 1, which is capped, so `step 1` and `h 1` become a monotone self-map on
  -- a finite range and reach their fixed point within that many further
  -- steps -- or h 1 exceeds its cap, i.e. component 1 passes its threshold.
  ----------------------------------------------------------------------

  lower-bound : (T : Nat) -> ((m : Nat) -> LeN (suc m) T -> Not (Rep m)) ->
    (V : Nat) -> LeN (h one T) V -> LeN T (plus (h zero T) V)
  lower-bound T nn V lv1 =
    LeN-trans {T} {sumh T} {plus (h zero T) V}
      (no-rep-sum T nn)
      (plus-mono (h zero T) (h zero T) (h one T) V (LeN-refl (h zero T)) lv1)

  ----------------------------------------------------------------------
  -- THE OTHER COMPONENT SETTLES
  --
  -- Suppose component 0 has grown past component 1's threshold from `M0` on
  -- (which `lower-bound` delivers once the state stops repeating), and that
  -- component 1 never passes its own threshold.  Then, by `sat`, coordinate 0
  -- is no longer what holds g_1's replay back, so from `M0` the replay depth
  -- depends only on `h 1`:
  --
  --     step 1 m = psi (h 1 m)      and     h 1 (m+1) = kv 1 (psi (h 1 m)).
  --
  -- That is a MONOTONE SELF-MAP on {0,...,K 1}: it repeats within K 1 + 1
  -- steps (`mono-bdd-rep`), a repeat is absorbing because the map is
  -- deterministic, and so `step 1` -- hence the index `c 1` -- is constant.
  --
  -- `sat` says: once coordinate 0 has at least `N 1`, raising it further
  -- cannot change a replay depth that is still below `N 1`.  It holds for the
  -- replay built from the levels (`ReplayLv`), because every demand g_1 makes
  -- of coordinate 0 below step `N 1` is at a level below `N 1`.
  ----------------------------------------------------------------------

  other-const :
    ((x x' y : Nat) -> LeN (N one) x -> LeN (N one) x' ->
       Not (LeN (N one) (nOf one x y)) -> Eq (nOf one x y) (nOf one x' y)) ->
    (M0 : Nat) -> ((m : Nat) -> LeN M0 m -> LeN (N one) (h zero m)) ->
    ((m : Nat) -> Not (LeN (N one) (step one m))) ->
    EvConstN (c one)
  other-const sat M0 big nopass = mkSigma mstar go
    where
      h1-bdd : (m : Nat) -> LeN (h one m) (K one)
      h1-bdd zero    = tt
      h1-bdd (suc m) = kv-bound one (step one m) (nopass m)

      psi : Nat -> Nat
      psi y = nOf one (N one) y

      step-psi : (m : Nat) -> LeN M0 m -> Eq (step one m) (psi (h one m))
      step-psi m lm =
        sat (h zero m) (N one) (h one m) (big m lm) (LeN-refl (N one)) (nopass m)

      h-F : (m : Nat) -> LeN M0 m -> Eq (h one (suc m)) (kv one (psi (h one m)))
      h-F m lm = Eq-cong (kv one) (step-psi m lm)

      rp : Sigma Nat (\ m -> Pair (LeN M0 m) (Eq (h one (suc m)) (h one m)))
      rp = mono-bdd-rep (h one) (K one) M0 (\ m -> h-mono1 m one) h1-bdd

      mstar : Nat
      mstar = fst rp

      lM0 : LeN M0 mstar
      lM0 = fst (snd rp)

      h-const : (m : Nat) -> LeN mstar m -> Eq (h one m) (h one mstar)
      h-const zero    lm =
        Eq-transport (\ z -> Eq (h one zero) (h one z))
          (Eq-sym (LeN-antisym {mstar} {zero} lm tt)) refl
      h-const (suc m) lm with LeN-dec mstar m
      ... | yes l =
            Eq-trans (h-F m (LeN-trans {M0} {mstar} {m} lM0 l))
              (Eq-trans (Eq-cong (\ z -> kv one (psi z)) (h-const m l))
                (Eq-trans (Eq-sym (h-F mstar lM0)) (snd (snd rp))))
      ... | no  nl =
            Eq-transport (\ z -> Eq (h one (suc m)) (h one z))
              (Eq-sym (le-eq' mstar m lm nl)) refl
        where
          le-eq' : (a b : Nat) -> LeN a (suc b) -> Not (LeN a b) -> Eq a (suc b)
          le-eq' zero    y       l nl' = Empty-elim (nl' tt)
          le-eq' (suc x) zero    l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
          le-eq' (suc x) (suc y) l nl' = Eq-cong suc (le-eq' x y l nl')

      go : (n : Nat) -> LeN mstar n -> Eq (c one n) (c one mstar)
      go n ln =
        Eq-cong (iv one)
          (Eq-trans (step-psi n (LeN-trans {M0} {mstar} {n} lM0 ln))
            (Eq-trans (Eq-cong psi (h-const n ln))
              (Eq-sym (step-psi mstar lM0))))

  ----------------------------------------------------------------------
  -- ... AND `big` COMES FROM THE GROWTH LOWER BOUND
  --
  -- One instance suffices: `h 0` is monotone, so `h 0 M0 >= N 1` gives it at
  -- every later depth.  And that one instance needs no repeat only BELOW
  -- `M0 = N 1 + K 1`, which is a bounded search -- if a repeat is found there
  -- the state is a fixed point and everything is constant anyway.
  ----------------------------------------------------------------------

  c1-const :
    ((x x' y : Nat) -> LeN (N one) x -> LeN (N one) x' ->
       Not (LeN (N one) (nOf one x y)) -> Eq (nOf one x y) (nOf one x' y)) ->
    ((m : Nat) -> Not (LeN (N one) (step one m))) ->
    EvConstN (c one)
  c1-const sat nopass = route (findRep (plus (N one) (K one)))
    where
      M0 : Nat
      M0 = plus (N one) (K one)

      h1b : (m : Nat) -> LeN (h one m) (K one)
      h1b zero    = tt
      h1b (suc m) = kv-bound one (step one m) (nopass m)

      route : Or (Sigma Nat (\ m -> Rep m))
                 ((m : Nat) -> LeN (suc m) M0 -> Not (Rep m)) ->
              EvConstN (c one)
      -- a fixed point: everything is constant from there
      route (inl (mkSigma m rp)) = rep-const m rp one
      -- no fixed point below M0: component 0 has outgrown N 1 by then
      route (inr nn) = other-const sat M0 big nopass
        where
          bigM0 : LeN (N one) (h zero M0)
          bigM0 =
            plus-cancel (K one) (N one) (h zero M0)
              (LeN-trans {plus (N one) (K one)} {M0} {plus (h zero M0) (K one)}
                (LeN-refl M0) (lower-bound M0 nn (K one) (h1b M0)))

          big : (m : Nat) -> LeN M0 m -> LeN (N one) (h zero m)
          big m lm =
            LeN-trans {N one} {h zero M0} {h zero m} bigM0 (h-mono zero M0 m lm)
