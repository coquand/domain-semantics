{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Prelude
--
-- Self-contained basic types for the ultimate-obstination development
-- (Coquand, "Une preuve directe du Theoreme d'Ultime Obstination").
--
-- Spartan: the only indexed inductive type used anywhere is Eq (the
-- identity type).  Sequences are plain (non-indexed) Lists indexed into
-- by Nat -- no Fin, no Vec.  No stdlib, no postulates, no holes, no
-- TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Prelude where

------------------------------------------------------------------------
-- Unit, empty, sums, decidability
------------------------------------------------------------------------

data Top : Set where
  tt : Top

data Empty : Set where

Empty-elim : {A : Set} -> Empty -> A
Empty-elim ()

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

Not : Set -> Set
Not A = A -> Empty

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no  : Not A -> Dec A

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

------------------------------------------------------------------------
-- Propositional equality (the one identity type we rely on)
------------------------------------------------------------------------

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

Eq-sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
Eq-sym refl = refl

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans refl q = q

Eq-cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
Eq-cong f refl = refl

Eq-transport : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
Eq-transport P refl px = px

suc-inj : {m n : Nat} -> Eq (suc m) (suc n) -> Eq m n
suc-inj refl = refl

EqNat-dec : (m n : Nat) -> Dec (Eq m n)
EqNat-dec zero    zero    = yes refl
EqNat-dec zero    (suc n) = no (\ ())
EqNat-dec (suc m) zero    = no (\ ())
EqNat-dec (suc m) (suc n) with EqNat-dec m n
... | yes p = yes (Eq-cong suc p)
... | no  k = no (\ e -> k (suc-inj e))

------------------------------------------------------------------------
-- Sigma / Pair
------------------------------------------------------------------------

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst

open Sigma public

Pair : Set -> Set -> Set
Pair A B = Sigma A (\ _ -> B)

------------------------------------------------------------------------
-- Order on Nat
------------------------------------------------------------------------

LeN : Nat -> Nat -> Set
LeN zero    n       = Top
LeN (suc m) zero    = Empty
LeN (suc m) (suc n) = LeN m n

LeN-refl : (n : Nat) -> LeN n n
LeN-refl zero    = tt
LeN-refl (suc n) = LeN-refl n

LeN-trans : {a b c : Nat} -> LeN a b -> LeN b c -> LeN a c
LeN-trans {zero}  {b}     {c}     p q = tt
LeN-trans {suc a} {zero}  {c}     () q
LeN-trans {suc a} {suc b} {zero}  p ()
LeN-trans {suc a} {suc b} {suc c} p q = LeN-trans {a} {b} {c} p q

LeN-antisym : {a b : Nat} -> LeN a b -> LeN b a -> Eq a b
LeN-antisym {zero}  {zero}  p q = refl
LeN-antisym {zero}  {suc b} p ()
LeN-antisym {suc a} {zero}  () q
LeN-antisym {suc a} {suc b} p q = Eq-cong suc (LeN-antisym {a} {b} p q)

-- Nat is a total order (constructive comparison)
LeN-total : (m n : Nat) -> Or (LeN m n) (LeN n m)
LeN-total zero    n       = inl tt
LeN-total (suc m) zero    = inr tt
LeN-total (suc m) (suc n) = LeN-total m n

LeN-dec : (m n : Nat) -> Dec (LeN m n)
LeN-dec zero    n       = yes tt
LeN-dec (suc m) zero    = no (\ ())
LeN-dec (suc m) (suc n) = LeN-dec m n

LeN-suc : (n : Nat) -> LeN n (suc n)
LeN-suc zero    = tt
LeN-suc (suc n) = LeN-suc n

------------------------------------------------------------------------
-- min and max on Nat
------------------------------------------------------------------------

minN : Nat -> Nat -> Nat
minN zero    n       = zero
minN (suc m) zero    = zero
minN (suc m) (suc n) = suc (minN m n)

maxN : Nat -> Nat -> Nat
maxN zero    n       = n
maxN (suc m) zero    = suc m
maxN (suc m) (suc n) = suc (maxN m n)

minN-zero-r : (m : Nat) -> Eq (minN m zero) zero
minN-zero-r zero    = refl
minN-zero-r (suc m) = refl

-- min/max under an order assumption (the bounded case)
minN-l : {m n : Nat} -> LeN m n -> Eq (minN m n) m
minN-l {zero}  {n}     le = refl
minN-l {suc m} {zero}  ()
minN-l {suc m} {suc n} le = Eq-cong suc (minN-l {m} {n} le)

maxN-r : {m n : Nat} -> LeN m n -> Eq (maxN m n) n
maxN-r {zero}  {n}     le = refl
maxN-r {suc m} {zero}  ()
maxN-r {suc m} {suc n} le = Eq-cong suc (maxN-r {m} {n} le)

minN-le-l : (m n : Nat) -> LeN (minN m n) m
minN-le-l zero    n       = tt
minN-le-l (suc m) zero    = tt
minN-le-l (suc m) (suc n) = minN-le-l m n

minN-le-r : (m n : Nat) -> LeN (minN m n) n
minN-le-r zero    n       = tt
minN-le-r (suc m) zero    = tt
minN-le-r (suc m) (suc n) = minN-le-r m n

maxN-le-l : (m n : Nat) -> LeN m (maxN m n)
maxN-le-l zero    n       = tt
maxN-le-l (suc m) zero    = LeN-refl m
maxN-le-l (suc m) (suc n) = maxN-le-l m n

maxN-le-r : (m n : Nat) -> LeN n (maxN m n)
maxN-le-r zero    n       = LeN-refl n
maxN-le-r (suc m) zero    = tt
maxN-le-r (suc m) (suc n) = maxN-le-r m n

------------------------------------------------------------------------
-- Lists  (plain inductive; used for n-tuples, indexed into by Nat)
------------------------------------------------------------------------

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

length : {A : Set} -> List A -> Nat
length nil         = zero
length (cons _ xs) = suc (length xs)

-- coordinate access with an explicit default for the out-of-range case
nth : {A : Set} -> A -> Nat -> List A -> A
nth d i       nil         = d
nth d zero    (cons x xs) = x
nth d (suc i) (cons x xs) = nth d i xs

-- delete the i-th component (identity if out of range)
del : {A : Set} -> Nat -> List A -> List A
del i       nil         = nil
del zero    (cons x xs) = xs
del (suc i) (cons x xs) = cons x (del i xs)
