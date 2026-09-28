{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Model
--
-- Models of the Horn clauses of a level theory (Bezem–Coquand §3).
-- A model assigns to each variable x a value in {none} ∪ ℕ ∪ {∞}: the
-- downward-closed set of atoms x+k it satisfies (none: no atom; fin j:
-- the atoms x+k with k ≤ j; inf: all).  Predecessor clauses hold by
-- downward closure.
--
--   * sound  : derivable atoms hold in every model of the hypotheses;
--   * fire   : the best one-step instance of a clause (Lemma 3.1): the
--              largest shift under which its body holds, decided.
------------------------------------------------------------------------

module BCDE4.LC.Model where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Val : Set where
  none : Val
  fin  : Nat -> Val
  inf  : Val

-- the atom x + k is in the downward closed set described by v
InV : Nat -> Val -> Set
InV k none    = Empty
InV k (fin j) = Le k j
InV k inf     = Top

-- order on values
LeV : Val -> Val -> Set
LeV none    w       = Top
LeV (fin j) none    = Empty
LeV (fin j) (fin i) = Le j i
LeV (fin j) inf     = Top
LeV inf     none    = Empty
LeV inf     (fin i) = Empty
LeV inf     inf     = Top

InV-mono : (k : Nat) (v w : Val) -> LeV v w -> InV k v -> InV k w
InV-mono k none    w       le ()
InV-mono k (fin j) none    () p
InV-mono k (fin j) (fin i) le p = Le-trans k j i p le
InV-mono k (fin j) inf     le p = tt
InV-mono k inf     none    () p
InV-mono k inf     (fin i) () p
InV-mono k inf     inf     le p = tt

InV-pred : (k : Nat) (v : Val) -> InV (suc k) v -> InV k v
InV-pred k none    ()
InV-pred k (fin j) p = Le-trans k (suc k) j (Le-suc k k (Le-refl k)) p
InV-pred k inf     p = tt

LeV-refl : (v : Val) -> LeV v v
LeV-refl none    = tt
LeV-refl (fin j) = Le-refl j
LeV-refl inf     = tt

LeV-trans : (u v w : Val) -> LeV u v -> LeV v w -> LeV u w
LeV-trans none    v       w       p q = tt
LeV-trans (fin j) none    w       () q
LeV-trans (fin j) (fin i) none    p ()
LeV-trans (fin j) (fin i) (fin h) p q = Le-trans j i h p q
LeV-trans (fin j) (fin i) inf     p q = tt
LeV-trans (fin j) inf     none    p ()
LeV-trans (fin j) inf     (fin h) p ()
LeV-trans (fin j) inf     inf     p q = tt
LeV-trans inf     none    w       () q
LeV-trans inf     (fin i) w       () q
LeV-trans inf     inf     w       p q = q

------------------------------------------------------------------------
-- Functions and satisfaction
------------------------------------------------------------------------

Fn : Set
Fn = Nat -> Val

SatA : Fn -> Atom -> Set
SatA g a = InV (snd a) (g (fst a))

SatBody : Fn -> Nat -> List Atom -> Set
SatBody g s B = (a : Atom) -> Mem a B -> SatA g (shiftA s a)

-- a clause holds under every upward shift
SatC : Fn -> Clause -> Set
SatC g c = (s : Nat) -> SatBody g s (body c) -> SatA g (shiftA s (head c))

Model : LCtx -> Fn -> Set
Model Th g = (c : Clause) -> Mem c (clausesTh Th) -> SatC g c

-- the hypotheses given by a function
AtomsOf : Fn -> Atom -> Set
AtomsOf g a = SatA g a

------------------------------------------------------------------------
-- Soundness of derivations
------------------------------------------------------------------------

sound : {Th : LCtx} {P : Atom -> Set} (g : Fn) -> Model Th g ->
  ((a : Atom) -> P a -> SatA g a) -> {b : Atom} -> Der Th P b -> SatA g b
sound g mo hp (d-hyp p) = hp _ p
sound g mo hp (d-pred {x} {k} d) = InV-pred k (g x) (sound g mo hp d)
sound g mo hp (d-clause {c} mc s ds) = mo c mc s (\ a ma -> sound g mo hp (ds a ma))

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

Le-zero : (n : Nat) -> Le zero n
Le-zero n = tt

Le-antisym-suc : (n : Nat) -> Le (suc n) n -> Empty
Le-antisym-suc zero    ()
Le-antisym-suc (suc n) p = Le-antisym-suc n p

-- decidable ≤
le? : (m n : Nat) -> Either (Le m n) (Le (suc n) m)
le? zero    n       = inl tt
le? (suc m) zero    = inr tt
le? (suc m) (suc n) = le? m n

-- truncated subtraction and its laws
_∸_ : Nat -> Nat -> Nat
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

plus-comm-suc : (m n : Nat) -> Eq (m + suc n) (suc (m + n))
plus-comm-suc zero    n = refl
plus-comm-suc (suc m) n = Eq-cong suc (plus-comm-suc m n)

plus-zero : (m : Nat) -> Eq (m + zero) m
plus-zero zero    = refl
plus-zero (suc m) = Eq-cong suc (plus-zero m)

-- s + k ≤ j  iff  s ≤ j ∸ k   (when k ≤ j)
Le-plus-monus : (s k j : Nat) -> Le k j -> Le (s + k) j -> Le s (j ∸ k)
Le-plus-monus s zero    j       p q = Eq-transport (\ X -> Le X j) (plus-zero s) q
Le-plus-monus s (suc k) zero    () q
Le-plus-monus s (suc k) (suc j) p q =
  Le-plus-monus s k j p (Eq-transport (\ X -> Le X (suc j)) (plus-comm-suc s k) q)

Le-monus-plus : (s k j : Nat) -> Le k j -> Le s (j ∸ k) -> Le (s + k) j
Le-monus-plus s zero    j       p q = Eq-transport (\ X -> Le X j) (Eq-sym (plus-zero s)) q
Le-monus-plus s (suc k) zero    () q
Le-monus-plus s (suc k) (suc j) p q =
  Eq-transport (\ X -> Le X (suc j)) (Eq-sym (plus-comm-suc s k)) (Le-monus-plus s k j p q)

min : Nat -> Nat -> Nat
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

min-glb : (s m n : Nat) -> Le s m -> Le s n -> Le s (min m n)
min-glb zero    m       n       p q = tt
min-glb (suc s) zero    n       () q
min-glb (suc s) (suc m) zero    p ()
min-glb (suc s) (suc m) (suc n) p q = min-glb s m n p q

min-l : (m n : Nat) -> Le (min m n) m
min-l zero    n       = tt
min-l (suc m) zero    = tt
min-l (suc m) (suc n) = min-l m n

min-r : (m n : Nat) -> Le (min m n) n
min-r zero    n       = tt
min-r (suc m) zero    = tt
min-r (suc m) (suc n) = min-r m n

------------------------------------------------------------------------
-- Lemma 3.1: the best shift of a body
------------------------------------------------------------------------

-- fail: the body holds under no shift; bnd s: it holds exactly under the
-- shifts ≤ s; unb: it holds under every shift
data Shift : Set where
  fail : Shift
  bnd  : Nat -> Shift
  unb  : Shift

InShift : Nat -> Shift -> Set
InShift s fail    = Empty
InShift s (bnd t) = Le s t
InShift s unb     = Top

-- best shift of a single atom x + k, given the value v of x
selFin : (k j : Nat) -> Either (Le k j) (Le (suc j) k) -> Shift
selFin k j (inl p) = bnd (j ∸ k)
selFin k j (inr p) = fail

shiftVal : Nat -> Val -> Shift
shiftVal k none    = fail
shiftVal k (fin j) = selFin k j (le? k j)
shiftVal k inf     = unb

shiftAtom : Fn -> Atom -> Shift
shiftAtom g a = shiftVal (snd a) (g (fst a))

meetS : Shift -> Shift -> Shift
meetS fail    t       = fail
meetS (bnd s) fail    = fail
meetS (bnd s) (bnd t) = bnd (min s t)
meetS (bnd s) unb     = bnd s
meetS unb     t       = t

shiftBody : Fn -> List Atom -> Shift
shiftBody g []       = unb
shiftBody g (a ∷ as) = meetS (shiftAtom g a) (shiftBody g as)

-- correctness (both directions) of the single-atom shift
selFin-sound : (s k j : Nat) (e : Either (Le k j) (Le (suc j) k)) -> InShift s (selFin k j e) -> Le (s + k) j
selFin-sound s k j (inl p) q = Le-monus-plus s k j p q
selFin-sound s k j (inr p) ()

selFin-complete : (s k j : Nat) (e : Either (Le k j) (Le (suc j) k)) -> Le (s + k) j -> InShift s (selFin k j e)
selFin-complete s k j (inl p) q = Le-plus-monus s k j p q
selFin-complete s k j (inr p) q = absurd (Le-antisym-suc j (Le-trans (suc j) k j p (Le-trans k (s + k) j (Le-plus-r s k) q)))
  where
    Le-plus-r : (s k : Nat) -> Le k (s + k)
    Le-plus-r zero    k = Le-refl k
    Le-plus-r (suc s) k = Le-suc k (s + k) (Le-plus-r s k)

shiftVal-sound : (s k : Nat) (v : Val) -> InShift s (shiftVal k v) -> InV (s + k) v
shiftVal-sound s k none    ()
shiftVal-sound s k (fin j) q = selFin-sound s k j (le? k j) q
shiftVal-sound s k inf     q = tt

shiftVal-complete : (s k : Nat) (v : Val) -> InV (s + k) v -> InShift s (shiftVal k v)
shiftVal-complete s k none    ()
shiftVal-complete s k (fin j) q = selFin-complete s k j (le? k j) q
shiftVal-complete s k inf     q = tt

meetS-l : (s : Nat) (x y : Shift) -> InShift s (meetS x y) -> InShift s x
meetS-l s fail    y       ()
meetS-l s (bnd a) fail    ()
meetS-l s (bnd a) (bnd b) q = Le-trans s (min a b) a q (min-l a b)
meetS-l s (bnd a) unb     q = q
meetS-l s unb     y       q = tt

meetS-r : (s : Nat) (x y : Shift) -> InShift s (meetS x y) -> InShift s y
meetS-r s fail    y       ()
meetS-r s (bnd a) fail    ()
meetS-r s (bnd a) (bnd b) q = Le-trans s (min a b) b q (min-r a b)
meetS-r s (bnd a) unb     q = tt
meetS-r s unb     y       q = q

meetS-intro : (s : Nat) (x y : Shift) -> InShift s x -> InShift s y -> InShift s (meetS x y)
meetS-intro s fail    y       () q
meetS-intro s (bnd a) fail    p ()
meetS-intro s (bnd a) (bnd b) p q = min-glb s a b p q
meetS-intro s (bnd a) unb     p q = p
meetS-intro s unb     y       p q = q

-- Lemma 3.1: the body holds under shift s iff s is below the best shift
shiftBody-sound : (g : Fn) (B : List Atom) (s : Nat) -> InShift s (shiftBody g B) -> SatBody g s B
shiftBody-sound g (a ∷ B) s q .a here =
  shiftVal-sound s (snd a) (g (fst a)) (meetS-l s (shiftAtom g a) (shiftBody g B) q)
shiftBody-sound g (b ∷ B) s q a (there m) =
  shiftBody-sound g B s (meetS-r s (shiftAtom g b) (shiftBody g B) q) a m

shiftBody-complete : (g : Fn) (B : List Atom) (s : Nat) -> SatBody g s B -> InShift s (shiftBody g B)
shiftBody-complete g []      s sb = tt
shiftBody-complete g (a ∷ B) s sb =
  meetS-intro s (shiftAtom g a) (shiftBody g B)
    (shiftVal-complete s (snd a) (g (fst a)) (sb a here))
    (shiftBody-complete g B s (\ b m -> sb b (there m)))

------------------------------------------------------------------------
-- The value a clause forces on its head variable
------------------------------------------------------------------------

-- fired value: the largest offset of the head variable produced by some
-- shift of the clause (none if no shift applies)
fireFrom : Shift -> Nat -> Val
fireFrom fail    l = none
fireFrom (bnd s) l = fin (s + l)
fireFrom unb     l = inf

fire : Fn -> Clause -> Val
fire g c = fireFrom (shiftBody g (body c)) (snd (head c))

-- a clause holds in g iff its fired value is below the value of its head
fire-SatC : (g : Fn) (c : Clause) -> LeV (fire g c) (g (fst (head c))) -> SatC g c
fire-SatC g c le s sb =
  InV-mono (s + snd (head c)) (fire g c) (g (fst (head c)))
    le (fire-in (shiftBody g (body c)) (shiftBody-complete g (body c) s sb))
  where
    fire-in : (x : Shift) -> InShift s x -> InV (s + snd (head c)) (fireFrom x (snd (head c)))
    fire-in fail    ()
    fire-in (bnd t) p = Le-plus-mono s t (snd (head c)) p
      where
        Le-plus-mono : (a b k : Nat) -> Le a b -> Le (a + k) (b + k)
        Le-plus-mono zero    b       k p = Le-plus-l b k
          where
            Le-plus-l : (b k : Nat) -> Le k (b + k)
            Le-plus-l zero    k = Le-refl k
            Le-plus-l (suc b) k = Le-suc k (b + k) (Le-plus-l b k)
        Le-plus-mono (suc a) zero    k () 
        Le-plus-mono (suc a) (suc b) k p = Le-plus-mono a b k p
    fire-in unb     p = tt
