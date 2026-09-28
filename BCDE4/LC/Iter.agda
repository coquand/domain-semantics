{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Iter
--
-- Capped forward iteration.  Given a finite list cs of base clauses of
-- a theory Th (all with head variable in the finite list V), a cap K and
-- a start function g0, repeatedly fire a clause that raises the value of
-- its head variable, truncating at K.  The result
--   * is a capped fixpoint:  capV K (fire g c) ≤ g (head c) for c ∈ cs,
--   * is above g0, bounded by K on V, equal to g0 on inf and off V,
--   * has all its atoms derivable (with the clauses cs) from the atoms of g0,
--   * is below every capped fixpoint above g0 (leastness).
-- Termination: a rank measure over V decreases strictly.
------------------------------------------------------------------------

module BCDE4.LC.Iter where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn
open import BCDE4.LC.Model

------------------------------------------------------------------------
-- Small utilities
------------------------------------------------------------------------

eqN? : (x y : Nat) -> Either (Eq x y) (Eq x y -> Empty)
eqN? zero    zero    = inl refl
eqN? zero    (suc y) = inr (\ ())
eqN? (suc x) zero    = inr (\ ())
eqN? (suc x) (suc y) = go (eqN? x y)
  where
    go : Either (Eq x y) (Eq x y -> Empty) -> Either (Eq (suc x) (suc y)) (Eq (suc x) (suc y) -> Empty)
    go (inl e) = inl (Eq-cong suc e)
    go (inr n) = inr (\ e -> n (suc-inj e))
      where suc-inj : {a b : Nat} -> Eq (suc a) (suc b) -> Eq a b
            suc-inj refl = refl

updW : Fn -> (y : Nat) -> Val -> (x : Nat) -> Either (Eq x y) (Eq x y -> Empty) -> Val
updW g y v x (inl e) = v
updW g y v x (inr n) = g x

upd : Fn -> Nat -> Val -> Fn
upd g y v x = updW g y v x (eqN? x y)

upd-at : (g : Fn) (y : Nat) (v : Val) -> Eq (upd g y v y) v
upd-at g y v = go (eqN? y y)
  where
    go : (d : Either (Eq y y) (Eq y y -> Empty)) -> Eq (updW g y v y d) v
    go (inl e) = refl
    go (inr n) = absurd (n refl)

upd-other : (g : Fn) (y : Nat) (v : Val) (x : Nat) -> (Eq x y -> Empty) -> Eq (upd g y v x) (g x)
upd-other g y v x ne = go (eqN? x y)
  where
    go : (d : Either (Eq x y) (Eq x y -> Empty)) -> Eq (updW g y v x d) (g x)
    go (inl e) = absurd (ne e)
    go (inr n) = refl

-- pointwise order
LeF : Fn -> Fn -> Set
LeF g h = (x : Nat) -> LeV (g x) (h x)

-- decidability of the value order
leV? : (v w : Val) -> Either (LeV v w) (LeV v w -> Empty)
leV? none    w       = inl tt
leV? (fin j) none    = inr (\ ())
leV? (fin j) (fin i) = go (le? j i)
  where
    go : Either (Le j i) (Le (suc i) j) -> Either (Le j i) (Le j i -> Empty)
    go (inl p) = inl p
    go (inr p) = inr (\ q -> Le-antisym-suc i (Le-trans (suc i) j i p q))
leV? (fin j) inf     = inl tt
leV? inf     none    = inr (\ ())
leV? inf     (fin i) = inr (\ ())
leV? inf     inf     = inl tt

------------------------------------------------------------------------
-- Capping
------------------------------------------------------------------------

capV : Nat -> Val -> Val
capV K none    = none
capV K (fin s) = fin (min s K)
capV K inf     = fin K

capV-mono : (K : Nat) (v w : Val) -> LeV v w -> LeV (capV K v) (capV K w)
capV-mono K none    w       le = tt
capV-mono K (fin j) none    ()
capV-mono K (fin j) (fin i) le = min-mono j i K le
  where
    min-mono : (a b k : Nat) -> Le a b -> Le (min a k) (min b k)
    min-mono zero    b       k       p = tt
    min-mono (suc a) zero    k       ()
    min-mono (suc a) (suc b) zero    p = tt
    min-mono (suc a) (suc b) (suc k) p = min-mono a b k p
capV-mono K (fin j) inf     le = min-r j K
capV-mono K inf     none    ()
capV-mono K inf     (fin i) ()
capV-mono K inf     inf     le = Le-refl K

-- the capped value is below the uncapped one, and bounded by K
capV-le : (K : Nat) (v : Val) -> LeV (capV K v) v
capV-le K none    = tt
capV-le K (fin s) = min-l s K
capV-le K inf     = tt

BndV : Nat -> Val -> Set
BndV K none    = Top
BndV K (fin j) = Le j K
BndV K inf     = Top

capV-bnd : (K : Nat) (v : Val) -> BndV K (capV K v)
capV-bnd K none    = tt
capV-bnd K (fin s) = min-r s K
capV-bnd K inf     = Le-refl K

------------------------------------------------------------------------
-- Monotonicity of firing
------------------------------------------------------------------------

LeS : Shift -> Shift -> Set
LeS x y = (s : Nat) -> InShift s x -> InShift s y

shiftBody-mono : (g h : Fn) -> LeF g h -> (B : List Atom) -> LeS (shiftBody g B) (shiftBody h B)
shiftBody-mono g h le B s p =
  shiftBody-complete h B s (\ a m -> InV-mono (s + snd a) (g (fst a)) (h (fst a)) (le (fst a))
                                        (shiftBody-sound g B s p a m))

fireFrom-mono : (x y : Shift) (l : Nat) -> LeS x y -> LeV (fireFrom x l) (fireFrom y l)
fireFrom-mono fail    y       l p = tt
fireFrom-mono (bnd a) fail    l p = p a (Le-refl a)
fireFrom-mono (bnd a) (bnd b) l p = plus-mono-l a b l (p a (Le-refl a))
  where
    plus-mono-l : (a b k : Nat) -> Le a b -> Le (a + k) (b + k)
    plus-mono-l zero    b       k q = plus-le k b
      where plus-le : (k b : Nat) -> Le k (b + k)
            plus-le k zero    = Le-refl k
            plus-le k (suc b) = Le-suc k (b + k) (plus-le k b)
    plus-mono-l (suc a) zero    k ()
    plus-mono-l (suc a) (suc b) k q = plus-mono-l a b k q
fireFrom-mono (bnd a) unb     l p = tt
fireFrom-mono unb     fail    l p = p zero tt
fireFrom-mono unb     (bnd b) l p = absurd (Le-antisym-suc b (p (suc b) tt))
fireFrom-mono unb     unb     l p = tt

fire-mono : (g h : Fn) -> LeF g h -> (c : Clause) -> LeV (fire g c) (fire h c)
fire-mono g h le c =
  fireFrom-mono (shiftBody g (body c)) (shiftBody h (body c)) (snd (head c)) (shiftBody-mono g h le (body c))

------------------------------------------------------------------------
-- Derivability of the fired atoms
------------------------------------------------------------------------

-- all atoms of g are derivable from P using the clauses of Th
DerAll : LCtx -> (Atom -> Set) -> Fn -> Set
DerAll Th P g = (a : Atom) -> SatA g a -> Der Th P a

der-down : {Th : LCtx} {P : Atom -> Set} (x n j : Nat) -> Le j n ->
  Der Th P (mkSigma x n) -> Der Th P (mkSigma x j)
der-down x zero    zero    p d = d
der-down x zero    (suc j) () d
der-down x (suc n) j       p d = go (le? j n)
  where
    go : Either (Le j n) (Le (suc n) j) -> Der _ _ (mkSigma x j)
    go (inl q) = der-down x n j q (d-pred d)
    go (inr q) = Eq-transport (\ i -> Der _ _ (mkSigma x i)) (le-antisym (suc n) j q p) d
      where
        le-antisym : (a b : Nat) -> Le a b -> Le b a -> Eq a b
        le-antisym zero    zero    p q = refl
        le-antisym zero    (suc b) p ()
        le-antisym (suc a) zero    () q
        le-antisym (suc a) (suc b) p q = Eq-cong suc (le-antisym a b p q)

-- the atoms up to the fired value are derivable
Le-plus-l : (j l : Nat) -> Le j (j + l)
Le-plus-l zero    l = tt
Le-plus-l (suc j) l = Le-plus-l j l

fire-der : {Th : LCtx} {P : Atom -> Set} (g : Fn) -> DerAll Th P g ->
  (c : Clause) -> Mem c (clausesTh Th) ->
  (j : Nat) -> InV j (fire g c) -> Der Th P (mkSigma (fst (head c)) j)
fire-der {Th} {P} g da c mc j p =
  helper (shiftBody g (body c)) (shiftBody-sound g (body c)) p
  where
    derAt : (s : Nat) -> SatBody g s (body c) -> Der Th P (shiftA s (head c))
    derAt s sb = d-clause mc s (\ a m -> da (shiftA s a) (sb a m))
    helper : (x : Shift) -> ((s : Nat) -> InShift s x -> SatBody g s (body c)) ->
      InV j (fireFrom x (snd (head c))) -> Der Th P (mkSigma (fst (head c)) j)
    helper fail    snd' ()
    helper (bnd s) snd' q = der-down (fst (head c)) (s + snd (head c)) j q (derAt s (snd' s (Le-refl s)))
    helper unb     snd' q = der-down (fst (head c)) (j + snd (head c)) j (Le-plus-l j (snd (head c))) (derAt j (snd' j tt))

------------------------------------------------------------------------
-- A single step raises the head of a violated clause
------------------------------------------------------------------------

-- a violated capped clause raises the value strictly
data Raise : Val -> Val -> Set where
  r-none : {a : Nat} -> Raise none (fin a)
  r-fin  : {b a : Nat} -> Le (suc b) a -> Raise (fin b) (fin a)

raise-of : (K : Nat) (v w : Val) -> (LeV (capV K v) w -> Empty) -> Raise w (capV K v)
raise-of K none    w       n = absurd (n tt)
raise-of K (fin s) none    n = r-none
raise-of K (fin s) (fin b) n = go (le? (min s K) b)
  where
    go : Either (Le (min s K) b) (Le (suc b) (min s K)) -> Raise (fin b) (fin (min s K))
    go (inl p) = absurd (n p)
    go (inr p) = r-fin p
raise-of K (fin s) inf     n = absurd (n tt)
raise-of K inf     none    n = r-none
raise-of K inf     (fin b) n = go (le? K b)
  where
    go : Either (Le K b) (Le (suc b) K) -> Raise (fin b) (fin K)
    go (inl p) = absurd (n p)
    go (inr p) = r-fin p
raise-of K inf     inf     n = absurd (n tt)

raise-le : {w v : Val} -> Raise w v -> LeV w v
raise-le r-none = tt
raise-le {fin b} (r-fin p) = Le-trans b (suc b) _ (Le-suc b b (Le-refl b)) p

-- ranks
rk : Nat -> Val -> Nat
rk K none    = suc (suc K)
rk K (fin j) = suc (K ∸ j)
rk K inf     = zero

monus-le : (K j : Nat) -> Le (K ∸ j) K
monus-le K       zero    = Le-refl K
monus-le zero    (suc j) = tt
monus-le (suc K) (suc j) = Le-suc (K ∸ j) K (monus-le K j)

monus-strict : (K b a : Nat) -> Le (suc b) a -> Le a K -> Le (suc (K ∸ a)) (K ∸ b)
monus-strict K       b       zero    () q
monus-strict zero    b       (suc a) p ()
monus-strict (suc K) zero    (suc a) p q = monus-le K a
monus-strict (suc K) (suc b) (suc a) p q = monus-strict K b a p q

rk-raise : (K : Nat) {w v : Val} -> Raise w v -> BndV K v -> Lt (rk K v) (rk K w)
rk-raise K (r-none {a}) q = monus-le K a
rk-raise K (r-fin {b} {a} p) q = monus-strict K b a p q

sumRk : Nat -> List Nat -> Fn -> Nat
sumRk K []       g = zero
sumRk K (x ∷ xs) g = rk K (g x) + sumRk K xs g

plus-le-mono : (a b c d : Nat) -> Le a b -> Le c d -> Le (a + c) (b + d)
plus-le-mono zero    b       c d p q = Le-trans c d (b + d) q (plus-le-r b d)
  where plus-le-r : (b d : Nat) -> Le d (b + d)
        plus-le-r zero    d = Le-refl d
        plus-le-r (suc b) d = Le-suc d (b + d) (plus-le-r b d)
plus-le-mono (suc a) zero    c d () q
plus-le-mono (suc a) (suc b) c d p q = plus-le-mono a b c d p q

-- updating one variable of V to a strictly smaller rank decreases the sum
sumRk-upd : (K : Nat) (g : Fn) (y : Nat) (v : Val) -> Lt (rk K v) (rk K (g y)) ->
  (V : List Nat) -> Mem y V -> Lt (sumRk K V (upd g y v)) (sumRk K V g)
sumRk-upd K g y v lt V m = strict V m
  where
    rk-upd-le : (x : Nat) -> Le (rk K (upd g y v x)) (rk K (g x))
    rk-upd-le x = go (eqN? x y)
      where
        go : (d : Either (Eq x y) (Eq x y -> Empty)) -> Le (rk K (updW g y v x d)) (rk K (g x))
        go (inl refl) = Le-trans (rk K v) (suc (rk K v)) (rk K (g x)) (Le-suc (rk K v) (rk K v) (Le-refl (rk K v))) lt
        go (inr n)    = Le-refl (rk K (g x))
    rk-upd-y : Lt (rk K (upd g y v y)) (rk K (g y))
    rk-upd-y = Eq-transport (\ X -> Lt (rk K X) (rk K (g y))) (Eq-sym (upd-at g y v)) lt
    weak : (V : List Nat) -> Le (sumRk K V (upd g y v)) (sumRk K V g)
    weak []       = tt
    weak (x ∷ xs) = plus-le-mono (rk K (upd g y v x)) (rk K (g x)) (sumRk K xs (upd g y v)) (sumRk K xs g)
                      (rk-upd-le x) (weak xs)
    strict : (V : List Nat) -> Mem y V -> Lt (sumRk K V (upd g y v)) (sumRk K V g)
    strict (x ∷ xs) here      = plus-le-mono (suc (rk K (upd g y v y))) (rk K (g y))
                                  (sumRk K xs (upd g y v)) (sumRk K xs g) rk-upd-y (weak xs)
    strict (x ∷ xs) (there m) =
      Eq-transport (\ X -> Le X (rk K (g x) + sumRk K xs g))
        (plus-comm-suc (rk K (upd g y v x)) (sumRk K xs (upd g y v)))
        (plus-le-mono (rk K (upd g y v x)) (rk K (g x)) (suc (sumRk K xs (upd g y v))) (sumRk K xs g)
           (rk-upd-le x) (strict xs m))

------------------------------------------------------------------------
-- The iteration
------------------------------------------------------------------------

module Run (Th : LCtx) (cs : List Clause) (cs-sub : (c : Clause) -> Mem c cs -> Mem c (clausesTh Th))
           (V : List Nat) (hv : (c : Clause) -> Mem c cs -> Mem (fst (head c)) V)
           (K : Nat) (P : Atom -> Set) where

  CFix : Fn -> Set
  CFix g = (c : Clause) -> Mem c cs -> LeV (capV K (fire g c)) (g (fst (head c)))

  Bnd : Fn -> Set
  Bnd g = (x : Nat) -> Mem x V -> BndV K (g x)

  -- search for a violated clause
  data Search (g : Fn) : Set where
    found : (c : Clause) -> Mem c cs -> (LeV (capV K (fire g c)) (g (fst (head c))) -> Empty) -> Search g
    fixd  : CFix g -> Search g

  OK : Fn -> Clause -> Set
  OK g c = LeV (capV K (fire g c)) (g (fst (head c)))

  searchL : (g : Fn) (xs : List Clause) -> ((c : Clause) -> Mem c xs -> Mem c cs) ->
    Either (Sigma Clause (\ c -> Pair (Mem c cs) (OK g c -> Empty)))
           ((c : Clause) -> Mem c xs -> OK g c)
  searchL g []       sub = inr (\ c ())
  searchL g (c ∷ xs) sub = go (leV? (capV K (fire g c)) (g (fst (head c))))
                              (searchL g xs (\ d m -> sub d (there m)))
    where
      go : Either (OK g c) (OK g c -> Empty) ->
           Either (Sigma Clause (\ d -> Pair (Mem d cs) (OK g d -> Empty))) ((d : Clause) -> Mem d xs -> OK g d) ->
           Either (Sigma Clause (\ d -> Pair (Mem d cs) (OK g d -> Empty))) ((d : Clause) -> Mem d (c ∷ xs) -> OK g d)
      go (inr n) r       = inl (mkSigma c (mkSigma (sub c here) n))
      go (inl o) (inl f) = inl f
      go (inl o) (inr a) = inr (\ { d here -> o ; d (there m) -> a d m })

  search : (g : Fn) -> Search g
  search g = go (searchL g cs (\ c m -> m))
    where
      go : Either (Sigma Clause (\ c -> Pair (Mem c cs) (OK g c -> Empty))) ((c : Clause) -> Mem c cs -> OK g c) -> Search g
      go (inl f) = found (fst f) (fst (snd f)) (snd (snd f))
      go (inr a) = fixd a

  -- the state of the iteration, relative to the start g0
  record Inv (g0 g : Fn) : Set where
    constructor mkInv
    field
      ge    : LeF g0 g
      der   : DerAll Th P g
      bndd  : Bnd g
      least : (h : Fn) -> CFix h -> LeF g0 h -> LeF g h
      offV  : (x : Nat) -> (Mem x V -> Empty) -> Eq (g x) (g0 x)

  record Out (g0 : Fn) : Set where
    constructor mkOut
    field
      res  : Fn
      inv  : Inv g0 res
      fix  : CFix res

  -- one step
  step : (g0 g : Fn) -> Inv g0 g -> (c : Clause) -> Mem c cs -> (OK g c -> Empty) ->
    Pair (Inv g0 (upd g (fst (head c)) (capV K (fire g c))))
         (Lt (sumRk K V (upd g (fst (head c)) (capV K (fire g c)))) (sumRk K V g))
  step g0 g (mkInv ge der bd least off) c mc bad =
    mkSigma (mkInv ge' der' bnd' least' off') dec
    where
      y  = fst (head c)
      v  = capV K (fire g c)
      g' = upd g y v
      r  = raise-of K (fire g c) (g y) bad
      g-le : LeF g g'
      g-le x = go (eqN? x y)
        where
          go : (d : Either (Eq x y) (Eq x y -> Empty)) -> LeV (g x) (updW g y v x d)
          go (inl refl) = raise-le r
          go (inr n)    = LeV-refl (g x)
      ge' : LeF g0 g'
      ge' x = LeV-trans (g0 x) (g x) (g' x) (ge x) (g-le x)
      der' : DerAll Th P g'
      der' a sa = go (eqN? (fst a) y) sa
        where
          go : (d : Either (Eq (fst a) y) (Eq (fst a) y -> Empty)) -> InV (snd a) (updW g y v (fst a) d) -> Der Th P a
          go (inl refl) p = fire-der g der c (cs-sub c mc) (snd a)
                              (InV-mono (snd a) v (fire g c) (capV-le K (fire g c)) p)
          go (inr n)    p = der a p
      bnd' : Bnd g'
      bnd' x m = go (eqN? x y)
        where
          go : (d : Either (Eq x y) (Eq x y -> Empty)) -> BndV K (updW g y v x d)
          go (inl refl) = capV-bnd K (fire g c)
          go (inr n)    = bd x m
      least' : (h : Fn) -> CFix h -> LeF g0 h -> LeF g' h
      least' h fh g0h x = go (eqN? x y)
        where
          go : (d : Either (Eq x y) (Eq x y -> Empty)) -> LeV (updW g y v x d) (h x)
          go (inl refl) = LeV-trans v (capV K (fire h c)) (h y)
                            (capV-mono K (fire g c) (fire h c) (fire-mono g h (least h fh g0h) c))
                            (fh c mc)
          go (inr n)    = least h fh g0h x
      off' : (x : Nat) -> (Mem x V -> Empty) -> Eq (g' x) (g0 x)
      off' x nm = Eq-trans (upd-other g y v x (\ e -> nm (Eq-transport (\ z -> Mem z V) (Eq-sym e) (hv c mc)))) (off x nm)
      dec : Lt (sumRk K V g') (sumRk K V g)
      dec = sumRk-upd K g y v (rk-raise K r (capV-bnd K (fire g c))) V (hv c mc)

  -- the iteration, by recursion on a bound for the measure
  iter : (n : Nat) (g0 g : Fn) -> Inv g0 g -> Lt (sumRk K V g) n -> Out g0
  iter zero    g0 g iv ()
  iter (suc n) g0 g iv lt = go (search g)
    where
      go : Search g -> Out g0
      go (fixd f)        = mkOut g iv f
      go (found c mc bad) =
        let st = step g0 g iv c mc bad
        in iter n g0 _ (fst st) (Le-trans (suc (sumRk K V _)) (sumRk K V g) n (snd st) lt)

  run : (g0 : Fn) -> DerAll Th P g0 -> Bnd g0 -> Out g0
  run g0 d b = iter (suc (sumRk K V g0)) g0 g0 (mkInv (\ x -> LeV-refl (g0 x)) d b (\ h fh le -> le) (\ x nm -> refl))
                    (Le-refl (suc (sumRk K V g0)))
