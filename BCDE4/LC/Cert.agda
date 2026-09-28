{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Cert
--
-- The loop certificate.  Let c be the capped least fixpoint above g
-- (LC.Iter.Run over all clauses of Th), and n a number with
--   * a GAP below n:   every finite value j of c satisfies j > n or
--                       j + MaxG ≤ n,
--   * g ≤ n:           every finite value of g is ≤ n.
-- Then every variable whose c-value exceeds n (the set W) is infinite:
-- all its atoms are derivable.
--
-- Proof.  Iterate only the PURE clauses (head in W, body over W ∪ ∞)
-- from s0 = (W ↦ n, ∞ ↦ ∞, else none), giving e ≤ c.  The function c°
-- = (e on W, c elsewhere) is a capped fixpoint above g (impure clauses
-- with head in W fire at most n thanks to the gap and the gain bound),
-- so c ≤ c° by leastness: e reaches n+1 on W.  Derivations from s0 are
-- invariant under upward shifts, hence W+n derives W+(n+s) for all s.
------------------------------------------------------------------------

module BCDE4.LC.Cert where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn
open import BCDE4.LC.Model
open import BCDE4.LC.Iter
open import BCDE4.LC.Equiv using (ShiftP ; der-shift)
open import BCDE4.LC.Solve using (MaxG ; gain-bound ; head-in-vars ; body-in-vars ; varsTh ; plus-mono-r)

------------------------------------------------------------------------
-- Classifying a value with respect to n
------------------------------------------------------------------------

data Cls (n : Nat) : Val -> Set where
  isHi  : {j : Nat} -> Le (suc n) j -> Cls n (fin j)
  isLo  : {j : Nat} -> Le j n -> Cls n (fin j)
  isNo  : Cls n none
  isInf : Cls n inf

cls : (n : Nat) (v : Val) -> Cls n v
cls n none    = isNo
cls n (fin j) = go (le? j n)
  where
    go : Either (Le j n) (Le (suc n) j) -> Cls n (fin j)
    go (inl p) = isLo p
    go (inr p) = isHi p
cls n inf     = isInf

-- start value of the pure iteration
s0v : (n : Nat) (v : Val) -> Cls n v -> Val
s0v n .(fin _) (isHi p) = fin n
s0v n .(fin _) (isLo p) = none
s0v n .none    isNo     = none
s0v n .inf     isInf    = inf

-- c° : e on W, c elsewhere
mixv : (n : Nat) (v w : Val) -> Cls n v -> Val
mixv n .(fin _) w (isHi p) = w
mixv n .(fin j) w (isLo {j} p) = fin j
mixv n .none    w isNo     = none
mixv n .inf     w isInf    = inf

------------------------------------------------------------------------
-- Generic lemmas
------------------------------------------------------------------------

-- values above n, or infinite
HiInf : Nat -> Val -> Set
HiInf n none    = Empty
HiInf n (fin j) = Le (suc n) j
HiInf n inf     = Top

hiInf? : (n : Nat) (v : Val) -> Either (HiInf n v) (HiInf n v -> Empty)
hiInf? n none    = inr (\ ())
hiInf? n (fin j) = go (le? (suc n) j)
  where
    go : Either (Le (suc n) j) (Le (suc j) (suc n)) -> Either (Le (suc n) j) (Le (suc n) j -> Empty)
    go (inl p) = inl p
    go (inr p) = inr (\ q -> Le-antisym-suc j (Le-trans (suc j) (suc n) j p q))
hiInf? n inf     = inl tt

Hi : Nat -> Val -> Set
Hi n none    = Empty
Hi n (fin j) = Le (suc n) j
Hi n inf     = Empty

hi? : (n : Nat) (v : Val) -> Either (Hi n v) (Hi n v -> Empty)
hi? n none    = inr (\ ())
hi? n (fin j) = hiInf? n (fin j)
hi? n inf     = inr (\ ())

-- firing only depends on the values of the body variables
shiftBody-ext : (g h : Fn) (B : List Atom) -> ((a : Atom) -> Mem a B -> Eq (g (fst a)) (h (fst a))) ->
  Eq (shiftBody g B) (shiftBody h B)
shiftBody-ext g h []      e = refl
shiftBody-ext g h (a ∷ B) e =
  Eq-cong2 meetS (Eq-cong (shiftVal (snd a)) (e a here)) (shiftBody-ext g h B (\ b m -> e b (there m)))

fire-ext : (g h : Fn) (cl : Clause) -> ((a : Atom) -> Mem a (body cl) -> Eq (g (fst a)) (h (fst a))) ->
  Eq (fire g cl) (fire h cl)
fire-ext g h cl e = Eq-cong (\ x -> fireFrom x (snd (head cl))) (shiftBody-ext g h (body cl) e)

-- a bound on all admissible shifts bounds the fired value
fireFrom-bound : (x : Shift) (l n : Nat) -> ((s : Nat) -> InShift s x -> Le (s + l) n) -> LeV (fireFrom x l) (fin n)
fireFrom-bound fail    l n h = tt
fireFrom-bound (bnd t) l n h = h t (Le-refl t)
fireFrom-bound unb     l n h = absurd (Le-antisym-suc n (Le-trans (suc n) (suc n + l) n (Le-plus-l (suc n) l) (h (suc n) tt)))

-- search for a body atom outside W ∪ ∞
data PureDec (n : Nat) (c : Fn) (B : List Atom) : Set where
  pure   : ((a : Atom) -> Mem a B -> HiInf n (c (fst a))) -> PureDec n c B
  impure : (a : Atom) -> Mem a B -> (HiInf n (c (fst a)) -> Empty) -> PureDec n c B

pureDec : (n : Nat) (c : Fn) (B : List Atom) -> PureDec n c B
pureDec n c []      = pure (\ a ())
pureDec n c (a ∷ B) = go (hiInf? n (c (fst a))) (pureDec n c B)
  where
    go : Either (HiInf n (c (fst a))) (HiInf n (c (fst a)) -> Empty) -> PureDec n c B -> PureDec n c (a ∷ B)
    go (inr q) r              = impure a here q
    go (inl p) (pure f)       = pure (\ { b here -> p ; b (there m) -> f b m })
    go (inl p) (impure b m q) = impure b (there m) q

-- filtering a list by a decidable predicate
filterStep : {A : Set} {Q : A -> Set} (x : A) -> List A -> Either (Q x) (Q x -> Empty) -> List A
filterStep x rest (inl q) = x ∷ rest
filterStep x rest (inr n) = rest

filterD : {A : Set} (Q : A -> Set) -> ((x : A) -> Either (Q x) (Q x -> Empty)) -> List A -> List A
filterD Q d []       = []
filterD Q d (x ∷ xs) = filterStep {Q = Q} x (filterD Q d xs) (d x)

filterD-mem : {A : Set} (Q : A -> Set) (d : (x : A) -> Either (Q x) (Q x -> Empty)) (xs : List A) {y : A} ->
  Mem y (filterD Q d xs) -> Pair (Mem y xs) (Q y)
filterD-mem Q d (x ∷ xs) {y} m = go (d x) m
  where
    go : (e : Either (Q x) (Q x -> Empty)) ->
      Mem y (filterStep {Q = Q} x (filterD Q d xs) e) -> Pair (Mem y (x ∷ xs)) (Q y)
    go (inl q) here      = mkSigma here q
    go (inl q) (there h) = let r = filterD-mem Q d xs h in mkSigma (there (fst r)) (snd r)
    go (inr n) h         = let r = filterD-mem Q d xs h in mkSigma (there (fst r)) (snd r)

filterD-intro : {A : Set} (Q : A -> Set) (d : (x : A) -> Either (Q x) (Q x -> Empty)) (xs : List A) {y : A} ->
  Mem y xs -> Q y -> Mem y (filterD Q d xs)
filterD-intro Q d (x ∷ xs) {.x} here q = go (d x)
  where
    go : (e : Either (Q x) (Q x -> Empty)) -> Mem x (filterStep {Q = Q} x (filterD Q d xs) e)
    go (inl q') = here
    go (inr n)  = absurd (n q)
filterD-intro Q d (x ∷ xs) {y} (there m) q = go (d x)
  where
    go : (e : Either (Q x) (Q x -> Empty)) -> Mem y (filterStep {Q = Q} x (filterD Q d xs) e)
    go (inl q') = there (filterD-intro Q d xs m q)
    go (inr n)  = filterD-intro Q d xs m q

------------------------------------------------------------------------
-- The certificate
------------------------------------------------------------------------

module Cert (Th : LCtx) (P : Atom -> Set) (V : List Nat)
            (hvV : (c : Clause) -> Mem c (clausesTh Th) -> Mem (fst (head c)) V)
            (K : Nat) where

  module RA = Run Th (clausesTh Th) (\ c m -> m) V hvV K P

  -- the pure clauses for c and n
  PureCl : (n : Nat) (c : Fn) -> Clause -> Set
  PureCl n c cl = Pair (Hi n (c (fst (head cl)))) ((a : Atom) -> Mem a (body cl) -> HiInf n (c (fst a)))

  pureCl? : (n : Nat) (c : Fn) (cl : Clause) -> Either (PureCl n c cl) (PureCl n c cl -> Empty)
  pureCl? n c cl = go (hi? n (c (fst (head cl)))) (pureDec n c (body cl))
    where
      go : Either (Hi n (c (fst (head cl)))) (Hi n (c (fst (head cl))) -> Empty) -> PureDec n c (body cl) ->
        Either (PureCl n c cl) (PureCl n c cl -> Empty)
      go (inr q) r              = inr (\ p -> q (fst p))
      go (inl h) (pure f)       = inl (mkSigma h f)
      go (inl h) (impure a m q) = inr (\ p -> q (snd p a m))

  csP : (n : Nat) (c : Fn) -> List Clause
  csP n c = filterD (PureCl n c) (pureCl? n c) (clausesTh Th)

  csP-sub : (n : Nat) (c : Fn) (cl : Clause) -> Mem cl (csP n c) -> Mem cl (clausesTh Th)
  csP-sub n c cl m = fst (filterD-mem (PureCl n c) (pureCl? n c) (clausesTh Th) m)

  s0 : (n : Nat) (c : Fn) -> Fn
  s0 n c x = s0v n (c x) (cls n (c x))

  module RP (n : Nat) (c : Fn) =
    Run Th (csP n c) (csP-sub n c) V (\ cl m -> hvV cl (csP-sub n c cl m)) K (SatA (s0 n c))

  ----------------------------------------------------------------------
  -- value lemmas (generalised over the value of c at x)
  ----------------------------------------------------------------------

  s0-le : (n : Nat) (v : Val) (k : Cls n v) -> LeV (s0v n v k) v
  s0-le n .(fin _) (isHi {j} p) = Le-trans n (suc n) j (Le-suc n n (Le-refl n)) p
  s0-le n .(fin _) (isLo p)     = tt
  s0-le n .none    isNo         = tt
  s0-le n .inf     isInf        = tt

  s0-bnd : (n : Nat) (v : Val) (k : Cls n v) -> BndV K v -> BndV K (s0v n v k)
  s0-bnd n .(fin _) (isHi {j} p) b = Le-trans n (suc n) K (Le-suc n n (Le-refl n)) (Le-trans (suc n) j K p b)
  s0-bnd n .(fin _) (isLo p)     b = tt
  s0-bnd n .none    isNo         b = tt
  s0-bnd n .inf     isInf        b = tt

  mix-le : (n : Nat) (v w : Val) (k : Cls n v) -> LeV w v -> LeV (mixv n v w k) v
  mix-le n .(fin _) w (isHi p) le = le
  mix-le n .(fin j) w (isLo {j} p) le = Le-refl j
  mix-le n .none    w isNo     le = tt
  mix-le n .inf     w isInf    le = tt

  -- on W ∪ ∞ the mix agrees with e (which is ≥ s0)
  mix-agree : (n : Nat) (v w : Val) (k : Cls n v) -> HiInf n v -> LeV (s0v n v k) w -> Eq (mixv n v w k) w
  mix-agree n .(fin _) w (isHi p) h le = refl
  mix-agree n .(fin j) w (isLo {j} p) h le = absurd (Le-antisym-suc n (Le-trans (suc n) j n h p))
  mix-agree n .none    w isNo     () le
  mix-agree n .inf     none    isInf h ()
  mix-agree n .inf     (fin i) isInf h ()
  mix-agree n .inf     inf     isInf h le = refl

  -- off W the mix is c
  mix-off : (n : Nat) (v w : Val) (k : Cls n v) -> (Hi n v -> Empty) -> Eq (mixv n v w k) v
  mix-off n .(fin _) w (isHi p) nh = absurd (nh p)
  mix-off n .(fin j) w (isLo {j} p) nh = refl
  mix-off n .none    w isNo     nh = refl
  mix-off n .inf     w isInf    nh = refl

  -- on W the mix is e
  mix-on : (n : Nat) (v w : Val) (k : Cls n v) -> Hi n v -> Eq (mixv n v w k) w
  mix-on n .(fin _) w (isHi p) h = refl
  mix-on n .(fin j) w (isLo {j} p) h = absurd (Le-antisym-suc n (Le-trans (suc n) j n h p))
  mix-on n .none    w isNo     ()
  mix-on n .inf     w isInf    ()

  -- s0 is fin n on W
  s0-on : (n : Nat) (v : Val) (k : Cls n v) -> Hi n v -> Eq (s0v n v k) (fin n)
  s0-on n .(fin _) (isHi p) h = refl
  s0-on n .(fin j) (isLo {j} p) h = absurd (Le-antisym-suc n (Le-trans (suc n) j n h p))
  s0-on n .none    isNo     ()
  s0-on n .inf     isInf    ()

  ----------------------------------------------------------------------
  -- the certificate
  ----------------------------------------------------------------------

  -- no finite value in (n - MaxG, n]: every value not above n is ≤ n - MaxG
  Gap : Nat -> Fn -> Set
  Gap n c = (x : Nat) -> (HiInf n (c x) -> Empty) -> (j : Nat) -> InV j (c x) -> Le (j + MaxG Th) n

  -- the finite values of g are ≤ n
  GLe : Nat -> Fn -> Set
  GLe n g = (x : Nat) (a : Nat) -> Eq (g x) (fin a) -> Le a n

  sat-s0 : (n : Nat) (v : Val) (kc : Cls n v) (j : Nat) -> InV j (s0v n v kc) ->
    Either (Pair (Hi n v) (Le j n)) (Pair ((i : Nat) -> InV i (s0v n v kc)) ((i : Nat) -> InV i v))
  sat-s0 n .(fin _) (isHi p) j q = inl (mkSigma p q)
  sat-s0 n .(fin _) (isLo p) j ()
  sat-s0 n .none    isNo     j ()
  sat-s0 n .inf     isInf    j q = inr (mkSigma (\ i -> tt) (\ i -> tt))

  hi-in : (n : Nat) (v : Val) (j : Nat) -> Hi n v -> Le j n -> InV j v
  hi-in n none    j () le
  hi-in n (fin i) j h le = Le-trans j n i le (Le-trans n (suc n) i (Le-suc n n (Le-refl n)) h)
  hi-in n inf     j () le

  hi-up : (n : Nat) (v w : Val) -> Hi n v -> LeV v w -> InV (suc n) w
  hi-up n none    w       () le
  hi-up n (fin j) none    h ()
  hi-up n (fin j) (fin i) h le = Le-trans (suc n) j i h le
  hi-up n (fin j) inf     h le = tt
  hi-up n inf     w       () le

  g-below : (n : Nat) (v w : Val) -> LeV v w -> Hi n w -> ((a : Nat) -> Eq v (fin a) -> Le a n) -> LeV v (fin n)
  g-below n none    w       le h gl = tt
  g-below n (fin a) w       le h gl = gl a refl
  g-below n inf     none    () h gl
  g-below n inf     (fin i) () h gl
  g-below n inf     inf     le () gl

  hiInf-hi : (n : Nat) (v : Val) -> (HiInf n v -> Empty) -> Hi n v -> Empty
  hiInf-hi n none    nh ()
  hiInf-hi n (fin j) nh h = nh h
  hiInf-hi n inf     nh ()

  plus-assoc' : (a b c : Nat) -> Eq (a + (b + c)) ((a + b) + c)
  plus-assoc' zero    b c = refl
  plus-assoc' (suc a) b c = Eq-cong suc (plus-assoc' a b c)

  -- the loop behind the certificate: from the atoms of W up to n (and
  -- the infinite variables), every variable of W reaches n + 1
  certLoop : (g c : Fn) (n : Nat) -> RA.Inv g c -> RA.CFix c -> Gap n c -> GLe n g ->
    (z : Nat) -> Hi n (c z) -> Der Th (SatA (s0 n c)) (mkSigma z (suc n))
  certLoop g c n ivc fixc gap gle = derE
    where
      s : Fn
      s = s0 n c
      out = RP.run n c s (\ a sa -> d-hyp sa) (\ z m -> s0-bnd n (c z) (cls n (c z)) (RA.Inv.bndd ivc z m))
      e : Fn
      e = RP.Out.res out
      ive = RP.Out.inv out
      fixe = RP.Out.fix out
      eLe : LeF e c
      eLe = RP.Inv.least ive c (\ cl m -> fixc cl (csP-sub n c cl m)) (\ z -> s0-le n (c z) (cls n (c z)))
      cm : Fn
      cm z = mixv n (c z) (e z) (cls n (c z))
      cmLe : LeF cm c
      cmLe z = mix-le n (c z) (e z) (cls n (c z)) (eLe z)

      fixcm : RA.CFix cm
      fixcm cl m = go (hi? n (c y))
        where
          y = fst (head cl)
          go : Either (Hi n (c y)) (Hi n (c y) -> Empty) -> LeV (capV K (fire cm cl)) (cm y)
          go (inr nh) =
            Eq-transport (\ X -> LeV (capV K (fire cm cl)) X) (Eq-sym (mix-off n (c y) (e y) (cls n (c y)) nh))
              (LeV-trans (capV K (fire cm cl)) (capV K (fire c cl)) (c y)
                 (capV-mono K (fire cm cl) (fire c cl) (fire-mono cm c cmLe cl)) (fixc cl m))
          go (inl h) = Eq-transport (\ X -> LeV (capV K (fire cm cl)) X) (Eq-sym (mix-on n (c y) (e y) (cls n (c y)) h))
                         (pd (pureDec n c (body cl)))
            where
              pd : PureDec n c (body cl) -> LeV (capV K (fire cm cl)) (e y)
              pd (pure f) =
                Eq-transport (\ X -> LeV (capV K X) (e y))
                  (Eq-sym (fire-ext cm e cl (\ a ma -> mix-agree n (c (fst a)) (e (fst a)) (cls n (c (fst a))) (f a ma)
                                                          (RP.Inv.ge ive (fst a)))))
                  (fixe cl (filterD-intro (PureCl n c) (pureCl? n c) (clausesTh Th) m (mkSigma h f)))
              pd (impure a ma q) =
                LeV-trans (capV K (fire cm cl)) (fin n) (e y)
                  (LeV-trans (capV K (fire cm cl)) (fire cm cl) (fin n) (capV-le K (fire cm cl)) bound)
                  (Eq-transport (\ X -> LeV X (e y)) (s0-on n (c y) (cls n (c y)) h) (RP.Inv.ge ive y))
                where
                  z = fst a
                  cmz : Eq (cm z) (c z)
                  cmz = mix-off n (c z) (e z) (cls n (c z)) (hiInf-hi n (c z) q)
                  bound : LeV (fire cm cl) (fin n)
                  bound = fireFrom-bound (shiftBody cm (body cl)) (snd (head cl)) n
                    (\ s' p ->
                       let sat : InV (s' + snd a) (c z)
                           sat = Eq-transport (InV (s' + snd a)) cmz (shiftBody-sound cm (body cl) s' p a ma)
                       in Le-trans (s' + snd (head cl)) ((s' + snd a) + MaxG Th) n
                            (Eq-transport (\ X -> Le (s' + snd (head cl)) X) (plus-assoc' s' (snd a) (MaxG Th))
                               (plus-mono-r s' (snd (head cl)) (snd a + MaxG Th)
                                  (gain-bound Th cl m a ma)))
                            (gap z q (s' + snd a) sat))

      gcm : LeF g cm
      gcm z = go (hi? n (c z))
        where
          go : Either (Hi n (c z)) (Hi n (c z) -> Empty) -> LeV (g z) (cm z)
          go (inr nh) = Eq-transport (LeV (g z)) (Eq-sym (mix-off n (c z) (e z) (cls n (c z)) nh)) (RA.Inv.ge ivc z)
          go (inl h)  = Eq-transport (LeV (g z)) (Eq-sym (mix-on n (c z) (e z) (cls n (c z)) h))
                          (LeV-trans (g z) (fin n) (e z)
                             (g-below n (g z) (c z) (RA.Inv.ge ivc z) h (gle z))
                             (Eq-transport (\ X -> LeV X (e z)) (s0-on n (c z) (cls n (c z)) h) (RP.Inv.ge ive z)))

      cLe : LeF c cm
      cLe = RA.Inv.least ivc cm fixcm gcm

      derE : (z : Nat) -> Hi n (c z) -> Der Th (SatA s) (mkSigma z (suc n))
      derE z h = RP.Inv.der ive (mkSigma z (suc n))
                   (Eq-transport (InV (suc n)) (mix-on n (c z) (e z) (cls n (c z)) h) (hi-up n (c z) (cm z) h (cLe z)))


  cert : (g c : Fn) (n : Nat) -> RA.Inv g c -> RA.CFix c -> Gap n c -> GLe n g ->
    (x : Nat) -> Hi n (c x) -> (k : Nat) -> Der Th P (mkSigma x k)
  cert g c n ivc fixc gap gle x hx k = der-cut toP (Q k x hx k (Le-plus-l k n))
    where
      s : Fn
      s = s0 n c
      derE : (z : Nat) -> Hi n (c z) -> Der Th (SatA s) (mkSigma z (suc n))
      derE = certLoop g c n ivc fixc gap gle

      Q : (t : Nat) (z : Nat) -> Hi n (c z) -> (j : Nat) -> Le j (t + n) -> Der Th (SatA s) (mkSigma z j)
      Q zero    z h j le = d-hyp (Eq-transport (InV j) (Eq-sym (s0-on n (c z) (cls n (c z)) h)) le)
      Q (suc t) z h j le =
        der-down z (suc (t + n)) j le
          (Eq-transport (\ X -> Der Th (SatA s) (mkSigma z X)) (plus-comm-suc t n)
             (der-cut back (der-shift t (derE z h))))
        where
          back : (a : Atom) -> ShiftP t (SatA s) a -> Der Th (SatA s) a
          back a (mkSigma a' (mkSigma sa' refl)) = sel (sat-s0 n (c (fst a')) (cls n (c (fst a'))) (snd a') sa')
            where
              sel : Either (Pair (Hi n (c (fst a'))) (Le (snd a') n))
                           (Pair ((i : Nat) -> InV i (s (fst a'))) ((i : Nat) -> InV i (c (fst a')))) ->
                    Der Th (SatA s) (shiftA t a')
              sel (inl hl) = Q t (fst a') (fst hl) (t + snd a') (plus-mono-r t (snd a') n (snd hl))
              sel (inr ii) = d-hyp (fst ii (t + snd a'))

      toP : (a : Atom) -> SatA s a -> Der Th P a
      toP a sa = sel (sat-s0 n (c (fst a)) (cls n (c (fst a))) (snd a) sa)
        where
          sel : Either (Pair (Hi n (c (fst a))) (Le (snd a) n))
                       (Pair ((i : Nat) -> InV i (s (fst a))) ((i : Nat) -> InV i (c (fst a)))) -> Der Th P a
          sel (inl hl) = RA.Inv.der ivc a (hi-in n (c (fst a)) (snd a) (fst hl) (snd hl))
          sel (inr ii) = RA.Inv.der ivc a (snd ii (snd a))
