{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Decide
--
-- The outer loop of the decision procedure (see BCDE4.LC.Solve), and
-- the decidability of derivability, of level equality (Corollary 3.4 of
-- Bezem–Coquand), and the canonical codes of levels (LDecAll).
------------------------------------------------------------------------

module BCDE4.LC.Decide where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn
open import BCDE4.LC.Model
open import BCDE4.LC.Iter
open import BCDE4.LC.Solve
open import BCDE4.LC.Cert
open import BCDE4.LC.Equiv using (valid-from-der ; der-from-valid)
open import BCDE4.LC.Codes using (ldec-from-dec)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

_*_ : Nat -> Nat -> Nat
zero  * n = zero
suc m * n = n + m * n
infixl 21 _*_

plus-comm : (m n : Nat) -> Eq (m + n) (n + m)
plus-comm zero    n = Eq-sym (plus-zero n)
plus-comm (suc m) n = Eq-trans (Eq-cong suc (plus-comm m n)) (Eq-sym (plus-comm-suc n m))

plus-assoc : (a b c : Nat) -> Eq ((a + b) + c) (a + (b + c))
plus-assoc zero    b c = refl
plus-assoc (suc a) b c = Eq-cong suc (plus-assoc a b c)

le-plus-mono : (a b c d : Nat) -> Le a b -> Le c d -> Le (a + c) (b + d)
le-plus-mono zero    b       c d p q = Le-trans c d (b + d) q (le-plus-r b d)
  where le-plus-r : (b d : Nat) -> Le d (b + d)
        le-plus-r zero    d = Le-refl d
        le-plus-r (suc b) d = Le-suc d (b + d) (le-plus-r b d)
le-plus-mono (suc a) zero    c d () q
le-plus-mono (suc a) (suc b) c d p q = le-plus-mono a b c d p q

mul-mono : (c c' g : Nat) -> Le c c' -> Le (c * g) (c' * g)
mul-mono zero    c'       g p = tt
mul-mono (suc c) zero     g ()
mul-mono (suc c) (suc c') g p = le-plus-mono g g (c * g) (c' * g) (Le-refl g) (mul-mono c c' g p)

-- t ≤ m0 + c·(G+1)  ⇒  t + G + 1 ≤ m0 + (c+1)·(G+1)
step-bound : (t m0 c G : Nat) -> Le t (m0 + c * suc G) -> Le (suc (t + G)) (m0 + suc c * suc G)
step-bound t m0 c G p =
  Eq-transport (\ X -> Le (suc (t + G)) X) eqR
    (Eq-transport (\ X -> Le X ((m0 + c * suc G) + suc G)) (plus-comm-suc t G)
       (le-plus-mono t (m0 + c * suc G) (suc G) (suc G) p (Le-refl G)))
  where
    eqR : Eq ((m0 + c * suc G) + suc G) (m0 + suc c * suc G)
    eqR = Eq-trans (plus-assoc m0 (c * suc G) (suc G))
            (Eq-cong (\ X -> m0 + X) (plus-comm (c * suc G) (suc G)))

------------------------------------------------------------------------
-- Counting the variables of V with a finite value ≤ t
------------------------------------------------------------------------

FinLe : Nat -> Val -> Set
FinLe t none    = Empty
FinLe t (fin j) = Le j t
FinLe t inf     = Empty

finLe? : (t : Nat) (v : Val) -> Either (FinLe t v) (FinLe t v -> Empty)
finLe? t none    = inr (\ ())
finLe? t (fin j) = go (le? j t)
  where
    go : Either (Le j t) (Le (suc t) j) -> Either (Le j t) (Le j t -> Empty)
    go (inl p) = inl p
    go (inr p) = inr (\ q -> Le-antisym-suc t (Le-trans (suc t) j t p q))
finLe? t inf     = inr (\ ())

length : {A : Set} -> List A -> Nat
length []       = zero
length (x ∷ xs) = suc (length xs)

cntStep : (t : Nat) (v : Val) -> Either (FinLe t v) (FinLe t v -> Empty) -> Nat -> Nat
cntStep t v (inl p) r = suc r
cntStep t v (inr n) r = r

cnt : Fn -> Nat -> List Nat -> Nat
cnt c t []       = zero
cnt c t (x ∷ xs) = cntStep t (c x) (finLe? t (c x)) (cnt c t xs)

cnt-le : (c : Fn) (t : Nat) (V : List Nat) -> Le (cnt c t V) (length V)
cnt-le c t []       = tt
cnt-le c t (x ∷ xs) = go (finLe? t (c x))
  where
    go : (d : Either (FinLe t (c x)) (FinLe t (c x) -> Empty)) -> Le (cntStep t (c x) d (cnt c t xs)) (suc (length xs))
    go (inl p) = cnt-le c t xs
    go (inr n) = Le-suc (cnt c t xs) (length xs) (cnt-le c t xs)

finLe-mono : (t t' : Nat) (v : Val) -> Le t t' -> FinLe t v -> FinLe t' v
finLe-mono t t' none    le ()
finLe-mono t t' (fin j) le p = Le-trans j t t' p le
finLe-mono t t' inf     le ()

cnt-mono : (c : Fn) (t t' : Nat) -> Le t t' -> (V : List Nat) -> Le (cnt c t V) (cnt c t' V)
cnt-mono c t t' le []       = tt
cnt-mono c t t' le (x ∷ xs) = go (finLe? t (c x)) (finLe? t' (c x))
  where
    go : (d : Either (FinLe t (c x)) (FinLe t (c x) -> Empty)) (d' : Either (FinLe t' (c x)) (FinLe t' (c x) -> Empty)) ->
      Le (cntStep t (c x) d (cnt c t xs)) (cntStep t' (c x) d' (cnt c t' xs))
    go (inl p) (inl p') = cnt-mono c t t' le xs
    go (inl p) (inr n') = absurd (n' (finLe-mono t t' (c x) le p))
    go (inr n) (inl p') = Le-suc (cnt c t xs) (cnt c t' xs) (cnt-mono c t t' le xs)
    go (inr n) (inr n') = cnt-mono c t t' le xs

-- a variable of V with value in (t, t'] makes the count grow
cnt-strict : (c : Fn) (t t' : Nat) -> Le t t' -> (V : List Nat) (x : Nat) -> Mem x V ->
  FinLe t' (c x) -> (FinLe t (c x) -> Empty) -> Le (suc (cnt c t V)) (cnt c t' V)
cnt-strict c t t' le (y ∷ xs) .y here p' n = go (finLe? t (c y)) (finLe? t' (c y))
  where
    go : (d : Either (FinLe t (c y)) (FinLe t (c y) -> Empty)) (d' : Either (FinLe t' (c y)) (FinLe t' (c y) -> Empty)) ->
      Le (suc (cntStep t (c y) d (cnt c t xs))) (cntStep t' (c y) d' (cnt c t' xs))
    go (inl p) d'        = absurd (n p)
    go (inr m) (inl q')  = cnt-mono c t t' le xs
    go (inr m) (inr m')  = absurd (m' p')
cnt-strict c t t' le (y ∷ xs) x (there h) p' n = go (finLe? t (c y)) (finLe? t' (c y))
  where
    ih = cnt-strict c t t' le xs x h p' n
    go : (d : Either (FinLe t (c y)) (FinLe t (c y) -> Empty)) (d' : Either (FinLe t' (c y)) (FinLe t' (c y) -> Empty)) ->
      Le (suc (cntStep t (c y) d (cnt c t xs))) (cntStep t' (c y) d' (cnt c t' xs))
    go (inl p) (inl p') = ih
    go (inl p) (inr m') = absurd (m' (finLe-mono t t' (c y) le p))
    go (inr m) (inl p') = Le-suc (suc (cnt c t xs)) (cnt c t' xs) ih
    go (inr m) (inr m') = ih

------------------------------------------------------------------------
-- The gap search
------------------------------------------------------------------------

-- v is a finite value in the window (t, t+G]
WinAt : Nat -> Nat -> Val -> Set
WinAt t G v = Sigma Nat (\ j -> Pair (Eq v (fin j)) (Pair (Le (suc t) j) (Le j (t + G))))

winAt? : (t G : Nat) (v : Val) -> Either (WinAt t G v) (WinAt t G v -> Empty)
winAt? t G none    = inr (\ { (mkSigma j (mkSigma () _)) })
winAt? t G inf     = inr (\ { (mkSigma j (mkSigma () _)) })
winAt? t G (fin j) = go (le? (suc t) j) (le? j (t + G))
  where
    go : Either (Le (suc t) j) (Le (suc j) (suc t)) -> Either (Le j (t + G)) (Le (suc (t + G)) j) ->
      Either (WinAt t G (fin j)) (WinAt t G (fin j) -> Empty)
    go (inl p) (inl q) = inl (mkSigma j (mkSigma refl (mkSigma p q)))
    go (inr p) q       = inr (\ { (mkSigma .j (mkSigma refl r)) -> Le-antisym-suc j (Le-trans (suc j) (suc t) j p (fst r)) })
    go (inl p) (inr q) = inr (\ { (mkSigma .j (mkSigma refl r)) -> Le-antisym-suc (t + G) (Le-trans (suc (t + G)) j (t + G) q (snd r)) })

-- search a list of variables for one satisfying a decidable property
data Find (Q : Nat -> Set) (V : List Nat) : Set where
  yes : (x : Nat) -> Mem x V -> Q x -> Find Q V
  no  : ((x : Nat) -> Mem x V -> Q x -> Empty) -> Find Q V

find : (Q : Nat -> Set) -> ((x : Nat) -> Either (Q x) (Q x -> Empty)) -> (V : List Nat) -> Find Q V
find Q d []       = no (\ x ())
find Q d (y ∷ ys) = go (d y) (find Q d ys)
  where
    go : Either (Q y) (Q y -> Empty) -> Find Q ys -> Find Q (y ∷ ys)
    go (inl q) r        = yes y here q
    go (inr n) (yes x m q) = yes x (there m) q
    go (inr n) (no f)   = no (\ { x here q -> n q ; x (there m) q -> f x m q })

le-antisym : (a b : Nat) -> Le a b -> Le b a -> Eq a b
le-antisym zero    zero    p q = refl
le-antisym zero    (suc b) p ()
le-antisym (suc a) zero    () q
le-antisym (suc a) (suc b) p q = Eq-cong suc (le-antisym a b p q)

GapT : LCtx -> Nat -> Fn -> Set
GapT Th n c = (x : Nat) -> (HiInf n (c x) -> Empty) -> (j : Nat) -> InV j (c x) -> Le (j + MaxG Th) n

memV? : (V : List Nat) (x : Nat) -> Either (Mem x V) (Mem x V -> Empty)
memV? V x = go' (find (\ y -> Eq y x) (\ y -> eqN? y x) V)
  where
    go' : Find (\ y -> Eq y x) V -> Either (Mem x V) (Mem x V -> Empty)
    go' (yes y m refl) = inl m
    go' (no f)         = inr (\ m -> f x m refl)

module Window (Th : LCtx) (c : Fn) (V : List Nat) (m0 : Nat)
              (offV : (x : Nat) -> (Mem x V -> Empty) -> Eq (c x) none) where

  G : Nat
  G = MaxG Th
  L : Nat
  L = length V
  K : Nat
  K = m0 + suc L * suc G

  record Gapped : Set where
    constructor mkGapped
    field
      n     : Nat
      gap   : GapT Th n c
      m0le  : Le m0 n
      ltK   : Le (suc n) K

  gapFrom : (t : Nat) -> ((x : Nat) -> Mem x V -> WinAt t G (c x) -> Empty) -> GapT Th (t + G) c
  gapFrom t nowin x nh j q = go (memV? V x)
    where
      go : Either (Mem x V) (Mem x V -> Empty) -> Le (j + G) (t + G)
      go (inr nm) = absurd (Eq-transport (InV j) (offV x nm) q)
      go (inl m)  = val (c x) refl nh q
        where
          val : (v : Val) -> Eq (c x) v -> (HiInf (t + G) v -> Empty) -> InV j v -> Le (j + G) (t + G)
          val none    e nh' ()
          val inf     e nh' q' = absurd (nh' tt)
          val (fin i) e nh' q' = sel (le? i t)
            where
              sel : Either (Le i t) (Le (suc t) i) -> Le (j + G) (t + G)
              sel (inl p) = le-plus-mono j t G G (Le-trans j i t q' p) (Le-refl G)
              sel (inr p) = absurd (nowin x m (mkSigma i (mkSigma e (mkSigma p (sel2 (le? (suc (t + G)) i))))))
                where
                  sel2 : Either (Le (suc (t + G)) i) (Le (suc i) (suc (t + G))) -> Le i (t + G)
                  sel2 (inl r) = absurd (nh' r)
                  sel2 (inr r) = r

  win : (f t : Nat) -> Le (suc L) (cnt c t V + f) -> Le t (m0 + cnt c t V * suc G) -> Le m0 t -> Gapped
  win zero    t p q r = absurd (Le-antisym-suc L (Le-trans (suc L) (cnt c t V) L
                          (Eq-transport (Le (suc L)) (plus-zero (cnt c t V)) p) (cnt-le c t V)))
  win (suc f) t p q r = go (find (\ x -> WinAt t G (c x)) (\ x -> winAt? t G (c x)) V)
    where
      go : Find (\ x -> WinAt t G (c x)) V -> Gapped
      go (no nowin) = mkGapped (t + G) (gapFrom t nowin)
                        (Le-trans m0 t (t + G) r (Le-plus-l t G))
                        (Le-trans (suc (t + G)) (m0 + suc (cnt c t V) * suc G) K
                           (step-bound t m0 (cnt c t V) G q)
                           (le-plus-mono m0 m0 _ _ (Le-refl m0) (mul-mono (suc (cnt c t V)) (suc L) (suc G) (cnt-le c t V))))
      go (yes x m (mkSigma j (mkSigma e (mkSigma tj jt)))) = win f j p' q' r'
        where
          fl : FinLe j (c x)
          fl = Eq-transport (FinLe j) (Eq-sym e) (Le-refl j)
          nfl : FinLe t (c x) -> Empty
          nfl h = Le-antisym-suc t (Le-trans (suc t) j t tj (Eq-transport (FinLe t) e h))
          tlej : Le t j
          tlej = Le-trans t (suc t) j (Le-suc t t (Le-refl t)) tj
          strict : Le (suc (cnt c t V)) (cnt c j V)
          strict = cnt-strict c t j tlej V x m fl nfl
          p' : Le (suc L) (cnt c j V + f)
          p' = Le-trans (suc L) (cnt c t V + suc f) (cnt c j V + f) p
                 (Eq-transport (\ X -> Le X (cnt c j V + f)) (Eq-sym (plus-comm-suc (cnt c t V) f))
                    (le-plus-mono (suc (cnt c t V)) (cnt c j V) f f strict (Le-refl f)))
          q' : Le j (m0 + cnt c j V * suc G)
          q' = Le-trans j (m0 + suc (cnt c t V) * suc G) (m0 + cnt c j V * suc G)
                 (Le-trans j (suc (t + G)) _ (Le-suc j (t + G) jt) (step-bound t m0 (cnt c t V) G q))
                 (le-plus-mono m0 m0 _ _ (Le-refl m0) (mul-mono (suc (cnt c t V)) (cnt c j V) (suc G) strict))
          r' : Le m0 j
          r' = Le-trans m0 t j r tlej

  gapped : Gapped
  gapped = win (suc L) m0 (Eq-transport (Le (suc L)) (Eq-sym (plus-comm (cnt c m0 V) (suc L)))
                             (Le-plus-l (suc L) (cnt c m0 V)))
                 (Le-plus-l m0 (cnt c m0 V * suc G)) (Le-refl m0)

------------------------------------------------------------------------
-- Maximum of the finite values, and the number of non-∞ variables
------------------------------------------------------------------------

finOr0 : Val -> Nat
finOr0 none    = zero
finOr0 (fin a) = a
finOr0 inf     = zero

maxFin : List Nat -> Fn -> Nat
maxFin V g = maxL (map (\ x -> finOr0 (g x)) V)

maxFin-ub : (V : List Nat) (g : Fn) (x : Nat) -> Mem x V -> (a : Nat) -> Eq (g x) (fin a) -> Le a (maxFin V g)
maxFin-ub V g x m a e =
  Eq-transport (\ X -> Le X (maxFin V g)) (Eq-cong finOr0 e)
    (maxL-ub (map (\ y -> finOr0 (g y)) V) (finOr0 (g x)) (mem-map (\ y -> finOr0 (g y)) V m))

NotInf : Val -> Set
NotInf none    = Top
NotInf (fin a) = Top
NotInf inf     = Empty

notInf? : (v : Val) -> Either (NotInf v) (NotInf v -> Empty)
notInf? none    = inl tt
notInf? (fin a) = inl tt
notInf? inf     = inr (\ ())

nInfStep : (v : Val) -> Either (NotInf v) (NotInf v -> Empty) -> Nat -> Nat
nInfStep v (inl p) r = suc r
nInfStep v (inr n) r = r

nInf : Fn -> List Nat -> Nat
nInf g []       = zero
nInf g (x ∷ xs) = nInfStep (g x) (notInf? (g x)) (nInf g xs)

-- if g' is finite only where g is, and some x of V becomes infinite, the count drops
nInf-le : (g g' : Fn) -> ((x : Nat) -> NotInf (g' x) -> NotInf (g x)) -> (V : List Nat) -> Le (nInf g' V) (nInf g V)
nInf-le g g' h []       = tt
nInf-le g g' h (x ∷ xs) = go (notInf? (g x)) (notInf? (g' x))
  where
    go : (d : Either (NotInf (g x)) (NotInf (g x) -> Empty)) (d' : Either (NotInf (g' x)) (NotInf (g' x) -> Empty)) ->
      Le (nInfStep (g' x) d' (nInf g' xs)) (nInfStep (g x) d (nInf g xs))
    go (inl p) (inl p') = nInf-le g g' h xs
    go (inl p) (inr n') = Le-suc (nInf g' xs) (nInf g xs) (nInf-le g g' h xs)
    go (inr n) (inl p') = absurd (n (h x p'))
    go (inr n) (inr n') = nInf-le g g' h xs

nInf-lt : (g g' : Fn) -> ((x : Nat) -> NotInf (g' x) -> NotInf (g x)) -> (V : List Nat) (x : Nat) -> Mem x V ->
  NotInf (g x) -> (NotInf (g' x) -> Empty) -> Le (suc (nInf g' V)) (nInf g V)
nInf-lt g g' h (y ∷ xs) .y here p n = go (notInf? (g y)) (notInf? (g' y))
  where
    go : (d : Either (NotInf (g y)) (NotInf (g y) -> Empty)) (d' : Either (NotInf (g' y)) (NotInf (g' y) -> Empty)) ->
      Le (suc (nInfStep (g' y) d' (nInf g' xs))) (nInfStep (g y) d (nInf g xs))
    go (inl q) (inl q') = absurd (n q')
    go (inl q) (inr n') = nInf-le g g' h xs
    go (inr m) d'       = absurd (m p)
nInf-lt g g' h (y ∷ xs) x (there mx) p n = go (notInf? (g y)) (notInf? (g' y))
  where
    ih = nInf-lt g g' h xs x mx p n
    go : (d : Either (NotInf (g y)) (NotInf (g y) -> Empty)) (d' : Either (NotInf (g' y)) (NotInf (g' y) -> Empty)) ->
      Le (suc (nInfStep (g' y) d' (nInf g' xs))) (nInfStep (g y) d (nInf g xs))
    go (inl q) (inl q') = ih
    go (inl q) (inr n') = Le-suc (suc (nInf g' xs)) (nInf g xs) ih
    go (inr m) (inl q') = absurd (m (h y q'))
    go (inr m) (inr n') = ih

------------------------------------------------------------------------
-- The outer loop
------------------------------------------------------------------------

module Solver (Th : LCtx) (A : List Atom) where

  V : List Nat
  V = varsTh Th ++ map fst A

  hvV : (c : Clause) -> Mem c (clausesTh Th) -> Mem (fst (head c)) V
  hvV c mc = mem-++-l (varsTh Th) (map fst A) (head-in-vars Th c mc)

  P : Atom -> Set
  P = InL A

  f0 : Fn
  f0 = startOf A

  record St (g : Fn) : Set where
    constructor mkSt
    field
      der  : DerAll Th P g
      ge0  : LeF f0 g
      off  : (x : Nat) -> (Mem x V -> Empty) -> Eq (g x) none

  record Final : Set where
    constructor mkFinal
    field
      res   : Fn
      st    : St res
      model : Model Th res

  -- an uncapped model from a capped fixpoint that never reaches the cap
  uncap : (K : Nat) (v w : Val) -> LeV (capV K v) w -> BndV K w -> ((j : Nat) -> Eq w (fin j) -> Le K j -> Empty) -> LeV v w
  uncap K none    w       le b nh = tt
  uncap K (fin s) none    () b nh
  uncap K (fin s) (fin i) le b nh = sel (le? s K)
    where
      sel : Either (Le s K) (Le (suc K) s) -> Le s i
      sel (inl p) = Eq-transport (\ X -> Le X i) (min-of s K p) le
        where
          min-of : (a b : Nat) -> Le a b -> Eq (min a b) a
          min-of zero    b       p = refl
          min-of (suc a) zero    ()
          min-of (suc a) (suc b) p = Eq-cong suc (min-of a b p)
      sel (inr p) = absurd (nh i refl (Eq-transport (\ X -> Le X i) (min-of' s K p) le))
        where
          min-of' : (a b : Nat) -> Le (suc b) a -> Eq (min a b) b
          min-of' zero    b       ()
          min-of' (suc a) zero    p = refl
          min-of' (suc a) (suc b) p = Eq-cong suc (min-of' a b p)
  uncap K (fin s) inf     le b nh = tt
  uncap K inf     none    () b nh
  uncap K inf     (fin i) le b nh = absurd (nh i refl le)
  uncap K inf     inf     le b nh = tt

  HitK : Nat -> Val -> Set
  HitK K v = Sigma Nat (\ j -> Pair (Eq v (fin j)) (Le K j))

  hitK? : (K : Nat) (v : Val) -> Either (HitK K v) (HitK K v -> Empty)
  hitK? K none    = inr (\ { (mkSigma j (mkSigma () _)) })
  hitK? K inf     = inr (\ { (mkSigma j (mkSigma () _)) })
  hitK? K (fin j) = go (le? K j)
    where
      go : Either (Le K j) (Le (suc j) K) -> Either (HitK K (fin j)) (HitK K (fin j) -> Empty)
      go (inl p) = inl (mkSigma j (mkSigma refl p))
      go (inr p) = inr (\ { (mkSigma .j (mkSigma refl q)) -> Le-antisym-suc j (Le-trans (suc j) K j p q) })

  hiv : (n : Nat) (v : Val) -> Either (Hi n v) (Hi n v -> Empty) -> Val
  hiv n v (inl h) = inf
  hiv n v (inr h) = v

  -- one round
  round : (g : Fn) -> St g -> Either Final (Sigma Fn (\ g' -> Pair (St g') (Le (suc (nInf g' V)) (nInf g V))))
  round g (mkSt der ge0 off) = go (find (\ x -> HitK K (c x)) (\ x -> hitK? K (c x)) V)
    where
      m0 : Nat
      m0 = maxFin V g
      K : Nat
      K = m0 + suc (length V) * suc (MaxG Th)
      bndg : (x : Nat) -> Mem x V -> BndV K (g x)
      bndg x m = val (g x) refl
        where
          val : (v : Val) -> Eq (g x) v -> BndV K v
          val none    e = tt
          val (fin a) e = Le-trans a m0 K (maxFin-ub V g x m a e) (Le-plus-l m0 _)
          val inf     e = tt
      module CT = Cert Th P V hvV K
      out = CT.RA.run g der bndg
      c : Fn
      c = CT.RA.Out.res out
      ivc = CT.RA.Out.inv out
      fixc = CT.RA.Out.fix out
      offc : (x : Nat) -> (Mem x V -> Empty) -> Eq (c x) none
      offc x nm = Eq-trans (CT.RA.Inv.offV ivc x nm) (off x nm)
      go : Find (\ x -> HitK K (c x)) V -> Either Final (Sigma Fn (\ g' -> Pair (St g') (Le (suc (nInf g' V)) (nInf g V))))
      go (no nohit) =
        inl (mkFinal c (mkSt (CT.RA.Inv.der ivc) (\ x -> LeV-trans (f0 x) (g x) (c x) (ge0 x) (CT.RA.Inv.ge ivc x)) offc)
               (\ cl mc -> fire-SatC c cl
                  (uncap K (fire c cl) (c (fst (head cl))) (fixc cl mc)
                     (CT.RA.Inv.bndd ivc (fst (head cl)) (hvV cl mc))
                     (\ j e le -> nohit (fst (head cl)) (hvV cl mc) (mkSigma j (mkSigma e le))))))
      go (yes xs mxs (mkSigma js (mkSigma ejs Kjs))) = inr (mkSigma g' (mkSigma st' prog))
        where
          module W = Window Th c V m0 offc
          gp = W.gapped
          n : Nat
          n = W.Gapped.n gp
          gle : (x : Nat) (a : Nat) -> Eq (g x) (fin a) -> Le a n
          gle x a e = sel (memV? V x)
            where
              sel : Either (Mem x V) (Mem x V -> Empty) -> Le a n
              sel (inl m)  = Le-trans a m0 n (maxFin-ub V g x m a e) (W.Gapped.m0le gp)
              sel (inr nm) = absurd (noneFin (Eq-trans (Eq-sym e) (off x nm)))
                where noneFin : Eq (fin a) none -> Empty
                      noneFin ()
          allAtoms : (x : Nat) -> Hi n (c x) -> (k : Nat) -> Der Th P (mkSigma x k)
          allAtoms = CT.cert g c n ivc fixc (W.Gapped.gap gp) gle
          g' : Fn
          g' x = hiv n (c x) (hi? n (c x))
          c-le-g' : LeF c g'
          c-le-g' x = go' (hi? n (c x))
            where
              go' : (d : Either (Hi n (c x)) (Hi n (c x) -> Empty)) -> LeV (c x) (hiv n (c x) d)
              go' (inl h) = le-inf (c x)
                where le-inf : (v : Val) -> LeV v inf
                      le-inf none = tt
                      le-inf (fin a) = tt
                      le-inf inf = tt
              go' (inr h) = LeV-refl (c x)
          der' : DerAll Th P g'
          der' a sa = go' (hi? n (c (fst a))) sa
            where
              go' : (d : Either (Hi n (c (fst a))) (Hi n (c (fst a)) -> Empty)) -> InV (snd a) (hiv n (c (fst a)) d) -> Der Th P a
              go' (inl h) q = allAtoms (fst a) h (snd a)
              go' (inr h) q = CT.RA.Inv.der ivc a q
          off' : (x : Nat) -> (Mem x V -> Empty) -> Eq (g' x) none
          off' x nm = go' (hi? n (c x))
            where
              go' : (d : Either (Hi n (c x)) (Hi n (c x) -> Empty)) -> Eq (hiv n (c x) d) none
              go' (inl h) = absurd (Eq-transport (Hi n) (offc x nm) h)
              go' (inr h) = offc x nm
          st' : St g'
          st' = mkSt der' (\ x -> LeV-trans (f0 x) (c x) (g' x)
                                    (LeV-trans (f0 x) (g x) (c x) (ge0 x) (CT.RA.Inv.ge ivc x)) (c-le-g' x)) off'
          g-le-g' : LeF g g'
          g-le-g' x = LeV-trans (g x) (c x) (g' x) (CT.RA.Inv.ge ivc x) (c-le-g' x)
          notInf-back : (x : Nat) -> NotInf (g' x) -> NotInf (g x)
          notInf-back x p = back (g x) (g' x) (g-le-g' x) p
            where back : (v w : Val) -> LeV v w -> NotInf w -> NotInf v
                  back none    w le p = tt
                  back (fin a) w le p = tt
                  back inf     none    () p
                  back inf     (fin b) () p
                  back inf     inf     le ()
          hiS : Hi n (c xs)
          hiS = Eq-transport (Hi n) (Eq-sym ejs) (Le-trans (suc n) K js (W.Gapped.ltK gp) Kjs)
          gs-notInf : NotInf (g xs)
          gs-notInf = back (g xs) (Eq-transport (LeV (g xs)) ejs (CT.RA.Inv.ge ivc xs))
            where back : (v : Val) -> LeV v (fin js) -> NotInf v
                  back none    le = tt
                  back (fin a) le = tt
                  back inf     ()
          g's-inf : NotInf (g' xs) -> Empty
          g's-inf = go' (hi? n (c xs))
            where
              go' : (d : Either (Hi n (c xs)) (Hi n (c xs) -> Empty)) -> NotInf (hiv n (c xs) d) -> Empty
              go' (inl h) ()
              go' (inr nh) q = nh hiS
          prog : Le (suc (nInf g' V)) (nInf g V)
          prog = nInf-lt g g' notInf-back V xs mxs gs-notInf g's-inf

  loop : (fuel : Nat) (g : Fn) -> St g -> Le (nInf g V) fuel -> Final
  loop zero    g s le = go (round g s)
    where
      go : Either Final (Sigma Fn (\ g' -> Pair (St g') (Le (suc (nInf g' V)) (nInf g V)))) -> Final
      go (inl fin') = fin'
      go (inr r)    = absurd (Le-trans (suc (nInf (fst r) V)) (nInf g V) zero (snd (snd r)) le)
  loop (suc f) g s le = go (round g s)
    where
      go : Either Final (Sigma Fn (\ g' -> Pair (St g') (Le (suc (nInf g' V)) (nInf g V)))) -> Final
      go (inl fin') = fin'
      go (inr r)    = loop f (fst r) (fst (snd r)) (Le-trans (suc (nInf (fst r) V)) (nInf g V) (suc f) (snd (snd r)) le)

  f0-off : (x : Nat) -> (Mem x V -> Empty) -> Eq (f0 x) none
  f0-off x nm = go A (\ y m -> m)
    where
      go : (as : List Atom) -> ((y : Nat) -> Mem y (map fst as) -> Mem y (map fst A)) -> Eq (startOf as x) none
      go []       sub = refl
      go (a ∷ as) sub = sel (eqN? (fst a) x)
        where
          sel : (d : Either (Eq (fst a) x) (Eq (fst a) x -> Empty)) -> Eq (startStep a (startOf as x) x d) none
          sel (inl e) = absurd (nm (mem-++-r (varsTh Th) (map fst A)
                          (Eq-transport (\ z -> Mem z (map fst A)) e (sub (fst a) here))))
          sel (inr n) = go as (\ y m -> sub y (there m))

  solve : Final
  solve = loop (nInf f0 V) f0 (mkSt (startOf-der A) (\ x -> LeV-refl (f0 x)) f0-off) (Le-refl (nInf f0 V))

------------------------------------------------------------------------
-- Decisions
------------------------------------------------------------------------

inV? : (j : Nat) (v : Val) -> Either (InV j v) (InV j v -> Empty)
inV? j none    = inr (\ ())
inV? j (fin i) = go (le? j i)
  where
    go : Either (Le j i) (Le (suc i) j) -> Either (Le j i) (Le j i -> Empty)
    go (inl p) = inl p
    go (inr p) = inr (\ q -> Le-antisym-suc i (Le-trans (suc i) j i p q))
inV? j inf     = inl tt

-- Corollary 3.4: derivability is decidable
decDer : (Th : LCtx) (A : List Atom) (b : Atom) -> Either (Der Th (InL A) b) (Der Th (InL A) b -> Empty)
decDer Th A b = go (inV? (snd b) (h (fst b)))
  where
    open Solver Th A
    fl = solve
    h : Fn
    h = Final.res fl
    go : Either (SatA h b) (SatA h b -> Empty) -> Either (Der Th (InL A) b) (Der Th (InL A) b -> Empty)
    go (inl p) = inl (St.der (Final.st fl) b p)
    go (inr n) = inr (\ d -> n (sound h (Final.model fl)
                        (\ a ma -> InV-mono (snd a) (f0 (fst a)) (h (fst a)) (St.ge0 (Final.st fl) (fst a))
                                     (startOf-sat A a ma)) d))

-- all atoms of a list derivable: decidable
decAll : (Th : LCtx) (A B : List Atom) ->
  Either ((b : Atom) -> Mem b B -> Der Th (InL A) b) (((b : Atom) -> Mem b B -> Der Th (InL A) b) -> Empty)
decAll Th A []      = inl (\ b ())
decAll Th A (b ∷ B) = go (decDer Th A b) (decAll Th A B)
  where
    go : Either (Der Th (InL A) b) (Der Th (InL A) b -> Empty) ->
         Either ((c : Atom) -> Mem c B -> Der Th (InL A) c) (((c : Atom) -> Mem c B -> Der Th (InL A) c) -> Empty) ->
         Either ((c : Atom) -> Mem c (b ∷ B) -> Der Th (InL A) c) (((c : Atom) -> Mem c (b ∷ B) -> Der Th (InL A) c) -> Empty)
    go (inr n) r       = inr (\ f -> n (f b here))
    go (inl d) (inr n) = inr (\ f -> n (\ c m -> f c (there m)))
    go (inl d) (inl f) = inl (\ { c here -> d ; c (there m) -> f c m })

-- the uniform word problem: equality of levels in a theory is decidable
decValid : (Th : LCtx) (l m : LExpr) -> Either (Valid Th l m) (Valid Th l m -> Empty)
decValid Th l m = go (decAll Th (atomsL l) (atomsL m)) (decAll Th (atomsL m) (atomsL l))
  where
    go : Either _ _ -> Either _ _ -> Either (Valid Th l m) (Valid Th l m -> Empty)
    go (inl f) (inl g) = inl (valid-from-der l m f g)
    go (inr n) g       = inr (\ v -> n (fst (der-from-valid v)))
    go (inl f) (inr n) = inr (\ v -> n (snd (der-from-valid v)))

-- canonical codes of levels, for every theory
ldecAll : LDecAll
ldecAll T = ldec-from-dec T (decValid T)
