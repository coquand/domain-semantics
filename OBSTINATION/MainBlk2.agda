{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.MainBlk2
--
-- THE MAIN PROPERTY IS PRESERVED BY MUTUAL RECURSION, r = 2 -- traces only.
--
--     MP g_0  /\  MP g_1   ==>   MP f_0  /\  MP f_1
--
-- where f_0, f_1 are defined from the step terms g_0, g_1 by mutual
-- recursion, and MP is "the demand is eventually constant" for a function
-- with a trace.  Nothing but the traces (iv, kv, Y) is used.
--
-- The block's trace is `BlkTraceR`'s: `hgt m j` is component j's height at
-- depth m, `stp j m` how far g_j's walk replays against what is available
-- there, `idx j m = iv j (stp j m)` its demand.  `BlkTraceR.main` already
-- gets from "every `idx j` is eventually constant" to MP of f_j; what is
-- proved here is that HYPOTHESIS, from MP of g_0 and g_1 alone.
--
-- WHY IT IS NOT IMMEDIATE.  `stp j m` is monotone in the depth, so either
-- it passes g_j's own threshold -- and then `idx j` is settled -- or it is
-- bounded and stalls.  Classically that is the whole proof; constructively
-- the stalling point has to be produced, and a monotone bounded sequence
-- does not hand it over.
--
-- WHAT PRODUCES IT.  Two facts, and their interaction is the content:
--
--   * DETERMINISM.  The state (hgt m 0, hgt m 1) is monotone and the step
--     is a function of it, so a repeated state is a FIXED point
--     (`rep-stays`), and then everything is settled (`rep-const`).  In a
--     finite box a repeat is found by counting (`no-rep-sum`).
--   * SATURATION (`ReplayLv.nOf-sat`).  A replay that stops before step T
--     needs fewer than T levels of any coordinate, so a coordinate already
--     at height >= T cannot block it and its value is IRRELEVANT.
--
-- The box argument alone fails exactly when one component grows without
-- bound -- then no state ever repeats.  But a component that has not passed
-- its threshold is bounded by `kv j (N j)`, so if no repeat is found in a
-- window of `N j + kv j (N j) + 1` steps, the OTHER component must have
-- climbed past `N j` -- and then saturation makes it irrelevant, so the
-- unpassed component's height is a deterministic monotone self-map on a
-- finite range, which repeats, and freezes (`frozen`).  Either way `idx j`
-- settles: `comp-const`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.MainBlk2 where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-suc-r ; plus-mono ; plus-lt-l ; plus-lt-r ;
   nle-lt ; le-ne-lt ; LeN-suc-not)
open import OBSTINATION.ReplayLv using (nOf ; nOf-mono ; nOf-cong ; nOf-sat)
open import OBSTINATION.BlkTraceR using
  (hv ; av ; nn ; cIdx ; hv-mono1 ; av-mono ; av-param ; av-rec ; q ; main)

one : Nat
one = suc zero

two : Nat
two = suc one

-- the other component of a two-element block
oth : Nat -> Nat
oth zero    = one
oth (suc _) = zero

oth-range : (j : Nat) -> LeN (suc (oth j)) two
oth-range zero    = tt
oth-range (suc j) = tt

-- in a two-element block, "not the other one" means "this one"
oth-uniq : (d j : Nat) -> LeN (suc d) two -> LeN (suc j) two ->
  Not (Eq d (oth j)) -> Eq d j
oth-uniq zero          zero          ld lj nd = refl
oth-uniq zero          (suc zero)    ld lj nd = Empty-elim (nd refl)
oth-uniq zero          (suc (suc j)) ld ()  nd
oth-uniq (suc zero)    zero          ld lj nd = Empty-elim (nd refl)
oth-uniq (suc zero)    (suc zero)    ld lj nd = refl
oth-uniq (suc zero)    (suc (suc j)) ld ()  nd
oth-uniq (suc (suc d)) j             ()  lj  nd

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus-zero-r : (x : Nat) -> Eq (plus x zero) x
plus-zero-r zero    = refl
plus-zero-r (suc x) = Eq-cong suc (plus-zero-r x)

plus-comm : (x y : Nat) -> Eq (plus x y) (plus y x)
plus-comm zero    y = Eq-sym (plus-zero-r y)
plus-comm (suc x) y =
  Eq-trans (Eq-cong suc (plus-comm x y)) (Eq-sym (plus-suc-r y x))

plus-ge-l : (x y : Nat) -> LeN x (plus x y)
plus-ge-l zero    y = tt
plus-ge-l (suc x) y = plus-ge-l x y

-- if x + y outgrows u + v while x stays under v, then y passes u
cut : (u v x y : Nat) -> LeN (suc (plus u v)) (plus x y) -> LeN x v -> LeN (suc u) y
cut u v x y big lxv = route (LeN-dec (suc u) y)
  where
    route : Dec (LeN (suc u) y) -> LeN (suc u) y
    route (yes l)  = l
    route (no  nl) = Empty-elim (LeN-suc-not (plus u v) bad)
      where
        lyu : LeN y u
        lyu = nle-lt (suc u) y nl

        bad : LeN (suc (plus u v)) (plus u v)
        bad =
          LeN-trans {suc (plus u v)} {plus x y} {plus u v} big
            (LeN-trans {plus x y} {plus v u} {plus u v}
              (plus-mono x v y u lxv lyu)
              (Eq-transport (\ z -> LeN (plus v u) z) (plus-comm v u)
                (LeN-refl (plus v u))))

-- the two coordinates of a pair, listed from either end
pair-swap : (f : Nat -> Nat) (j : Nat) -> LeN (suc j) two ->
  Eq (plus (f j) (f (oth j))) (plus (f zero) (f one))
pair-swap f zero          lj = refl
pair-swap f (suc zero)    lj = plus-comm (f one) (f zero)
pair-swap f (suc (suc j)) ()

------------------------------------------------------------------------
-- THE DATA: the two step terms' traces, and their Main Property
------------------------------------------------------------------------

module _ (a : Nat)
         (iv : Nat -> Nat -> Nat)
         (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
         (kv : Nat -> Nat -> Nat)
         (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         (Y : Nat -> Nat)
         (N I : Nat -> Nat)
         (iv-stab : (j n : Nat) -> LeN (N j) n -> Eq (iv j n) (I j))
         where

  ----------------------------------------------------------------------
  -- the block's trace, at r = 2
  ----------------------------------------------------------------------

  hgt : Nat -> Nat -> Nat                 -- height of component j at depth m
  hgt = hv two a iv ivr kv kv-mono Y

  avl : Nat -> Nat -> Nat                 -- what is available at depth m
  avl = av two a iv ivr kv kv-mono Y

  stp : Nat -> Nat -> Nat                 -- g_j's replay depth there
  stp = nn two a iv ivr kv kv-mono Y

  idx : Nat -> Nat -> Nat                 -- g_j's demand there
  idx = cIdx two a iv ivr kv kv-mono Y

  -- the bound on a component that has not passed its own threshold
  K : Nat -> Nat
  K j = kv j (N j)

  ----------------------------------------------------------------------
  -- monotonicity
  ----------------------------------------------------------------------

  avl-mono : (m m' : Nat) -> LeN m m' -> (c : Nat) -> LeN (avl m c) (avl m' c)
  avl-mono = av-mono two a iv ivr kv kv-mono Y

  stp-mono : (j m m' : Nat) -> LeN m m' -> LeN (stp j m) (stp j m')
  stp-mono j m m' le =
    nOf-mono a (iv j) (ivr j) (avl m) (avl m') (avl-mono m m' le)

  hgt-mono : (j : Nat) -> LeN (suc j) two -> (m m' : Nat) -> LeN m m' ->
    LeN (hgt m j) (hgt m' j)
  hgt-mono j lj m m' le =
    Eq-transport (\ z -> LeN z (hgt m' j)) (av-rec two a iv ivr kv kv-mono Y j lj m)
      (Eq-transport (\ z -> LeN (avl m j) z)
        (av-rec two a iv ivr kv kv-mono Y j lj m') (avl-mono m m' le j))

  ----------------------------------------------------------------------
  -- THE STATE, AND DETERMINISM
  ----------------------------------------------------------------------

  -- two depths with the same component heights offer the same everywhere
  avl-eq : (m m' : Nat) ->
    ((c : Nat) -> LeN (suc c) two -> Eq (hgt m c) (hgt m' c)) ->
    (c : Nat) -> Eq (avl m c) (avl m' c)
  avl-eq m m' e c = route (LeN-dec (suc c) two)
    where
      route : Dec (LeN (suc c) two) -> Eq (avl m c) (avl m' c)
      route (yes lc) =
        Eq-trans (av-rec two a iv ivr kv kv-mono Y c lc m)
          (Eq-trans (e c lc)
            (Eq-sym (av-rec two a iv ivr kv kv-mono Y c lc m')))
      route (no nc) = Eq-sym (av-param two a iv ivr kv kv-mono Y c nc m m')

  state-cong : (m m' : Nat) ->
    ((c : Nat) -> LeN (suc c) two -> Eq (hgt m c) (hgt m' c)) ->
    (j : Nat) -> Eq (stp j m) (stp j m')
  state-cong m m' e j =
    nOf-cong a (iv j) (ivr j) (avl m) (avl m') (avl-eq m m' e)

  Rep : Nat -> Set
  Rep m = (c : Nat) -> LeN (suc c) two -> Eq (hgt (suc m) c) (hgt m c)

  Diff : Nat -> Set
  Diff m = Or (Not (Eq (hgt (suc m) zero) (hgt m zero)))
              (Not (Eq (hgt (suc m) one) (hgt m one)))

  repOrDiff : (m : Nat) -> Or (Rep m) (Diff m)
  repOrDiff m = r0 (EqNat-dec (hgt (suc m) zero) (hgt m zero))
    where
      r0 : Dec (Eq (hgt (suc m) zero) (hgt m zero)) -> Or (Rep m) (Diff m)
      r0 (no n0)  = inr (inl n0)
      r0 (yes e0) = r1 (EqNat-dec (hgt (suc m) one) (hgt m one))
        where
          r1 : Dec (Eq (hgt (suc m) one) (hgt m one)) -> Or (Rep m) (Diff m)
          r1 (no n1)  = inr (inr n1)
          r1 (yes e1) = inl rp
            where
              rp : Rep m
              rp zero          lc = e0
              rp (suc zero)    lc = e1
              rp (suc (suc c)) ()
  -- a repeated state is a fixed point
  rep-stays : (m : Nat) -> Rep m -> (n : Nat) -> LeN m n ->
    (c : Nat) -> LeN (suc c) two -> Eq (hgt n c) (hgt m c)
  rep-stays m rp zero    le c lc =
    Eq-transport (\ z -> Eq (hgt zero c) (hgt z c))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) refl
  rep-stays m rp (suc n) le c lc = route (LeN-dec m n)
    where
      route : Dec (LeN m n) -> Eq (hgt (suc n) c) (hgt m c)
      route (yes l) =
        Eq-trans
          (Eq-cong (kv c) (state-cong n m (\ d ld -> rep-stays m rp n l d ld) c))
          (rp c lc)
      route (no nl) =
        Eq-transport (\ z -> Eq (hgt (suc n) c) (hgt z c))
          (Eq-sym (eq' m n le nl)) refl
        where
          eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
          eq' zero    y       l nl' = Empty-elim (nl' tt)
          eq' (suc x) zero    l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
          eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

  ----------------------------------------------------------------------
  -- WITHOUT A REPEAT THE TOTAL GROWS
  ----------------------------------------------------------------------

  tot : Nat -> Nat
  tot m = plus (hgt m zero) (hgt m one)

  no-rep-inc : (m : Nat) -> Diff m -> LeN (suc (tot m)) (tot (suc m))
  no-rep-inc m (inl n0) =
    plus-lt-l (hgt m zero) (hgt (suc m) zero) (hgt m one) (hgt (suc m) one)
      (le-ne-lt (hgt m zero) (hgt (suc m) zero) (hv-mono1 two a iv ivr kv kv-mono Y m zero) n0)
      (hv-mono1 two a iv ivr kv kv-mono Y m one)
  no-rep-inc m (inr n1) =
    plus-lt-r (hgt m zero) (hgt (suc m) zero) (hgt m one) (hgt (suc m) one)
      (hv-mono1 two a iv ivr kv kv-mono Y m zero)
      (le-ne-lt (hgt m one) (hgt (suc m) one) (hv-mono1 two a iv ivr kv kv-mono Y m one) n1)

  no-rep-sum : (T : Nat) -> ((m : Nat) -> LeN (suc m) T -> Diff m) -> LeN T (tot T)
  no-rep-sum zero    nn' = tt
  no-rep-sum (suc T) nn' =
    LeN-trans {suc T} {suc (tot T)} {tot (suc T)}
      (no-rep-sum T (\ m lm -> nn' m (LeN-trans {suc m} {T} {suc T} lm (LeN-suc T))))
      (no-rep-inc T (nn' T (LeN-refl T)))

  findRep : (T : Nat) ->
    Or (Sigma Nat Rep) ((m : Nat) -> LeN (suc m) T -> Diff m)
  findRep zero    = inr (\ m ())
  findRep (suc T) = route (findRep T)
    where
      route : Or (Sigma Nat Rep) ((m : Nat) -> LeN (suc m) T -> Diff m) ->
              Or (Sigma Nat Rep) ((m : Nat) -> LeN (suc m) (suc T) -> Diff m)
      route (inl w)   = inl w
      route (inr nn') = route2 (repOrDiff T)
        where
          route2 : Or (Rep T) (Diff T) ->
            Or (Sigma Nat Rep) ((m : Nat) -> LeN (suc m) (suc T) -> Diff m)
          route2 (inl rp) = inl (mkSigma T rp)
          route2 (inr df) = inr sub
            where
              sub : (m : Nat) -> LeN (suc m) (suc T) -> Diff m
              sub m lm = pick (LeN-dec (suc m) T)
                where
                  pick : Dec (LeN (suc m) T) -> Diff m
                  pick (yes l)  = nn' m l
                  pick (no  nl) =
                    Eq-transport (\ z -> Diff z) (Eq-sym (eq' m T lm nl)) df
                    where
                      eq' : (x y : Nat) -> LeN x y -> Not (LeN (suc x) y) -> Eq x y
                      eq' zero    zero    l nl' = refl
                      eq' zero    (suc y) l nl' = Empty-elim (nl' tt)
                      eq' (suc x) zero    () nl'
                      eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

  ----------------------------------------------------------------------
  -- THE TWO WAYS A COMPONENT'S DEMAND CAN SETTLE
  ----------------------------------------------------------------------

  -- it has passed its own threshold
  past-const : (j T : Nat) -> LeN (N j) (stp j T) -> EvConstN (idx j)
  past-const j T pj = mkSigma T go
    where
      at : (m : Nat) -> LeN T m -> Eq (idx j m) (I j)
      at m lm =
        iv-stab j (stp j m)
          (LeN-trans {N j} {stp j T} {stp j m} pj (stp-mono j T m lm))

      go : (n : Nat) -> LeN T n -> Eq (idx j n) (idx j T)
      go n ln = Eq-trans (at n ln) (Eq-sym (at T (LeN-refl T)))

  -- or the whole state has reached a fixed point
  rep-const : (m : Nat) -> Rep m -> (j : Nat) -> EvConstN (idx j)
  rep-const m rp j = mkSigma m go
    where
      go : (n : Nat) -> LeN m n -> Eq (idx j n) (idx j m)
      go n ln =
        Eq-cong (iv j) (state-cong n m (\ c lc -> rep-stays m rp n ln c lc) j)

  ----------------------------------------------------------------------
  -- THE VERDICT ON A COMPONENT
  --
  -- What the endgame actually produces, and what the height clause (H) needs
  -- of it (`BlkPass2`): either the component's height AND its replay depth are
  -- FROZEN from a known depth on -- and then its index is trivially settled --
  -- or its replay has PASSED its own threshold at a known depth, and then its
  -- demand is `I j` from there on and `WalkAffine` applies.  `comp-const` is
  -- the index half of it (`from-verdict`).
  ----------------------------------------------------------------------

  Verdict : Nat -> Set
  Verdict j =
    Or (Sigma Nat (\ T -> (n : Nat) -> LeN T n ->
           Pair (Eq (hgt n j) (hgt T j)) (Eq (stp j n) (stp j T))))
       (Sigma Nat (\ T -> LeN (N j) (stp j T)))

  from-verdict : (j : Nat) -> Verdict j -> EvConstN (idx j)
  from-verdict j (inl (mkSigma T fz)) =
    mkSigma T (\ n ln -> Eq-cong (iv j) (snd (fz n ln)))
  from-verdict j (inr (mkSigma T p)) = past-const j T p

  comp-verdict : (j : Nat) -> LeN (suc j) two -> Verdict j
  comp-verdict j lj = route (findRep T)
    where
      T' : Nat
      T' = plus (N j) (K j)

      T : Nat
      T = suc T'

      route : Or (Sigma Nat Rep) ((m : Nat) -> LeN (suc m) T -> Diff m) ->
              Verdict j
      route (inl (mkSigma m rp)) = inl (mkSigma m fz)
        where
          fz : (n : Nat) -> LeN m n ->
            Pair (Eq (hgt n j) (hgt m j)) (Eq (stp j n) (stp j m))
          fz n ln =
            mkSigma (rep-stays m rp n ln j lj)
              (state-cong n m (\ c lc -> rep-stays m rp n ln c lc) j)
      route (inr nn') = pass (LeN-dec (N j) (stp j T))
        where
          big : LeN T (tot T)
          big = no-rep-sum T nn'

          pass : Dec (LeN (N j) (stp j T)) -> Verdict j
          pass (yes p)  = inr (mkSigma T p)
          pass (no  np) = finish (search (suc (K j)))
            where
              -- unpassed at T', hence bounded there
              npT' : Not (LeN (N j) (stp j T'))
              npT' p = np (LeN-trans {N j} {stp j T'} {stp j T} p
                             (stp-mono j T' T (LeN-suc T')))

              hgtT : LeN (hgt T j) (K j)
              hgtT =
                kv-mono j (stp j T') (N j)
                  (LeN-trans {stp j T'} {suc (stp j T')} {N j}
                    (LeN-suc (stp j T')) (nle-lt (N j) (stp j T') npT'))

              -- so the OTHER component has climbed past N j
              sat0 : LeN (suc (N j)) (hgt T (oth j))
              sat0 =
                cut (N j) (K j) (hgt T j) (hgt T (oth j))
                  (Eq-transport (\ z -> LeN (suc (plus (N j) (K j))) z)
                    (Eq-sym (pair-swap (hgt T) j lj)) big)
                  hgtT

              satm : (m : Nat) -> LeN T m -> LeN (N j) (avl m (oth j))
              satm m lm =
                Eq-transport (\ z -> LeN (N j) z)
                  (Eq-sym (av-rec two a iv ivr kv kv-mono Y (oth j) (oth-range j) m))
                  (LeN-trans {N j} {hgt T (oth j)} {hgt m (oth j)}
                    (LeN-trans {N j} {suc (N j)} {hgt T (oth j)} (LeN-suc (N j)) sat0)
                    (hgt-mono (oth j) (oth-range j) T m lm))

              -- SATURATION: past T, the unpassed component's replay depends
              -- only on its own height
              satstep : (m m' : Nat) -> LeN T m -> LeN T m' ->
                Eq (hgt m j) (hgt m' j) -> Not (LeN (N j) (stp j m)) ->
                Eq (stp j m) (stp j m')
              satstep m m' lm lm' e nps =
                nOf-sat a (iv j) (ivr j) (avl m) (avl m') (N j) (oth j)
                  agree (satm m lm) (satm m' lm') nps
                where
                  agree : (d : Nat) -> Not (Eq d (oth j)) -> Eq (avl m d) (avl m' d)
                  agree d nd = pickd (LeN-dec (suc d) two)
                    where
                      pickd : Dec (LeN (suc d) two) -> Eq (avl m d) (avl m' d)
                      pickd (yes ld) =
                        Eq-trans (av-rec two a iv ivr kv kv-mono Y d ld m)
                          (Eq-trans ehd
                            (Eq-sym (av-rec two a iv ivr kv kv-mono Y d ld m')))
                        where
                          ehd : Eq (hgt m d) (hgt m' d)
                          ehd =
                            Eq-transport (\ z -> Eq (hgt m z) (hgt m' z))
                              (Eq-sym (oth-uniq d j ld lj nd)) e
                      pickd (no nd') =
                        Eq-sym (av-param two a iv ivr kv kv-mono Y d nd' m m')

              -- a repeated height, past T and unpassed, freezes everything
              frozen : (m : Nat) -> LeN T m -> Not (LeN (N j) (stp j m)) ->
                Eq (hgt (suc m) j) (hgt m j) -> Verdict j
              frozen m lm nps eqh = inl (mkSigma m fr)
                where
                  fr : (n : Nat) -> LeN m n ->
                    Pair (Eq (hgt n j) (hgt m j)) (Eq (stp j n) (stp j m))
                  fr zero    ln =
                    Eq-transport
                      (\ z -> Pair (Eq (hgt zero j) (hgt z j))
                                   (Eq (stp j zero) (stp j z)))
                      (Eq-sym (LeN-antisym {m} {zero} ln tt))
                      (mkSigma refl refl)
                  fr (suc n) ln = pickn (LeN-dec m n)
                    where
                      pickn : Dec (LeN m n) ->
                        Pair (Eq (hgt (suc n) j) (hgt m j))
                             (Eq (stp j (suc n)) (stp j m))
                      pickn (yes l) = mkSigma eh es
                        where
                          ih : Pair (Eq (hgt n j) (hgt m j)) (Eq (stp j n) (stp j m))
                          ih = fr n l

                          eh : Eq (hgt (suc n) j) (hgt m j)
                          eh = Eq-trans (Eq-cong (kv j) (snd ih)) eqh

                          es : Eq (stp j (suc n)) (stp j m)
                          es =
                            Eq-sym
                              (satstep m (suc n) lm
                                (LeN-trans {T} {m} {suc n} lm
                                  (LeN-trans {m} {n} {suc n} l (LeN-suc n)))
                                (Eq-sym eh) nps)
                      pickn (no nl) =
                        Eq-transport
                          (\ z -> Pair (Eq (hgt (suc n) j) (hgt z j))
                                       (Eq (stp j (suc n)) (stp j z)))
                          (Eq-sym (eq' m n ln nl)) (mkSigma refl refl)
                        where
                          eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) ->
                            Eq x (suc y)
                          eq' zero    y       l nl' = Empty-elim (nl' tt)
                          eq' (suc x) zero    l nl' =
                            Eq-cong suc (LeN-antisym {x} {zero} l tt)
                          eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

              -- either something settles, or the height has grown k times
              search : (k : Nat) ->
                Or (Verdict j) (LeN k (hgt (plus k T) j))
              search zero    = inr tt
              search (suc k) = step (search k)
                where
                  n : Nat
                  n = plus k T

                  step : Or (Verdict j) (LeN k (hgt n j)) ->
                         Or (Verdict j) (LeN (suc k) (hgt (suc n) j))
                  step (inl w)  = inl w
                  step (inr le) = d1 (LeN-dec (N j) (stp j n))
                    where
                      d1 : Dec (LeN (N j) (stp j n)) ->
                           Or (Verdict j) (LeN (suc k) (hgt (suc n) j))
                      d1 (yes p)  = inl (inr (mkSigma n p))
                      d1 (no  npn) = d2 (EqNat-dec (hgt (suc n) j) (hgt n j))
                        where
                          d2 : Dec (Eq (hgt (suc n) j) (hgt n j)) ->
                               Or (Verdict j) (LeN (suc k) (hgt (suc n) j))
                          d2 (yes e)  = inl (frozen n (plus-ge-r k T) npn e)
                          d2 (no  ne) =
                            inr (LeN-trans {suc k} {suc (hgt n j)} {hgt (suc n) j}
                                   le
                                   (le-ne-lt (hgt n j) (hgt (suc n) j)
                                     (hv-mono1 two a iv ivr kv kv-mono Y n j) ne))

              -- and it cannot have grown K j + 1 times while unpassed
              finish : Or (Verdict j)
                          (LeN (suc (K j)) (hgt (plus (suc (K j)) T) j)) ->
                       Verdict j
              finish (inl w)  = w
              finish (inr le) = d (LeN-dec (N j) (stp j (plus (K j) T)))
                where
                  d : Dec (LeN (N j) (stp j (plus (K j) T))) -> Verdict j
                  d (yes p)   = inr (mkSigma (plus (K j) T) p)
                  d (no  npn) = Empty-elim (LeN-suc-not (K j) bad)
                    where
                      bad : LeN (suc (K j)) (K j)
                      bad =
                        LeN-trans {suc (K j)} {hgt (suc (plus (K j) T)) j} {K j}
                          le
                          (kv-mono j (stp j (plus (K j) T)) (N j)
                            (LeN-trans {stp j (plus (K j) T)}
                                       {suc (stp j (plus (K j) T))} {N j}
                              (LeN-suc (stp j (plus (K j) T)))
                              (nle-lt (N j) (stp j (plus (K j) T)) npn)))

  comp-const : (j : Nat) -> LeN (suc j) two -> EvConstN (idx j)
  comp-const j lj = from-verdict j (comp-verdict j lj)

  ----------------------------------------------------------------------
  -- MP g_0 /\ MP g_1  ==>  MP f_0 /\ MP f_1
  --
  -- The two thresholds are put under one, and `BlkTraceR.main` -- which
  -- turns "every step index settles" into "every component's sequentiality
  -- index settles" -- finishes.
  ----------------------------------------------------------------------

  ev0 : EvConstN (idx zero)
  ev0 = comp-const zero tt

  ev1 : EvConstN (idx one)
  ev1 = comp-const one tt

  L2 : Nat
  L2 = maxN (fst ev0) (fst ev1)

  C2 : Nat -> Nat
  C2 j = idx j L2

  from-ev : (j m M : Nat) ->
    ((n : Nat) -> LeN M n -> Eq (idx j n) (idx j M)) ->
    LeN M L2 -> LeN L2 m -> Eq (idx j m) (C2 j)
  from-ev j m M ev leML lm =
    Eq-trans (ev m (LeN-trans {M} {L2} {m} leML lm)) (Eq-sym (ev L2 leML))

  st2 : (j m : Nat) -> LeN (suc j) two -> LeN L2 m -> Eq (idx j m) (C2 j)
  st2 zero          m lj lm =
    from-ev zero m (fst ev0) (snd ev0) (maxN-le-l (fst ev0) (fst ev1)) lm
  st2 (suc zero)    m lj lm =
    from-ev one m (fst ev1) (snd ev1) (maxN-le-r (fst ev0) (fst ev1)) lm
  st2 (suc (suc j)) m ()  lm

  -- THE THEOREM
  MPblock : (j : Nat) -> LeN (suc j) two ->
    EvConstN (q two a iv ivr kv kv-mono Y j)
  MPblock = main two a iv ivr kv kv-mono Y L2 C2 st2
