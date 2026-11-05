{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/Basic.agda        (L0)
--
-- Finite elements of the Henderson-Morris value domain
--
--     V  =  A  +  (V x V)  +  (V -> V)
--
-- (henderson.pdf, section III, "The Domains"), presented -- as in
-- MIN/ -- entirely through its FINITE elements.  Reynolds's separated
-- sum, so Bot, (QUOTE Bot), (CONS Bot Bot) and (LAMBDA x Bot) are all
-- distinct; that is exactly `Bot', `At a', `Prd Bot Bot', `Fn nil'.
--
-- Differences from MIN/Domain/Basic.agda:
--   * UCode   is replaced by  At   : Atom -> FinEl            (the A summand)
--   * PiCode  is replaced by  Prd  : FinEl -> FinEl -> FinEl  (V x V)
--   * FunEl / FinFun are unchanged -- the reflexive summand.
--
-- 0 postulates, 0 pragmas beyond BUILTIN NATURAL.
------------------------------------------------------------------------

module LAZY.Domain.Basic where

------------------------------------------------------------------------
-- Basic types
------------------------------------------------------------------------

data Top : Set where
  tt : Top

data Empty : Set where

Neg : Set -> Set
Neg A = A -> Empty

data Bool : Set where
  true  : Bool
  false : Bool

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

Eq-transport : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
Eq-transport P refl px = px

Eq-sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
Eq-sym refl = refl

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans refl q = q

Eq-cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
Eq-cong f refl = refl

------------------------------------------------------------------------
-- Sigma, pairs, lists, Maybe
------------------------------------------------------------------------

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst

open Sigma public

Pair : Set -> Set -> Set
Pair A B = Sigma A (\ _ -> B)

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

max : Nat -> Nat -> Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

min : Nat -> Nat -> Nat
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

add : Nat -> Nat -> Nat
add zero    n = n
add (suc m) n = suc (add m n)

isPos : Nat -> Set
isPos zero    = Empty
isPos (suc n) = Top

min-isPos : (m n : Nat) -> isPos (min m n) -> Pair (isPos m) (isPos n)
min-isPos zero    n       ()
min-isPos (suc m) zero    ()
min-isPos (suc m) (suc n) _ = mkSigma tt tt

isPos-min : (m n : Nat) -> isPos m -> isPos n -> isPos (min m n)
isPos-min zero    n       () _
isPos-min (suc m) zero    _  ()
isPos-min (suc m) (suc n) _  _ = tt

------------------------------------------------------------------------
-- The <= order on Nat (stage arithmetic)
------------------------------------------------------------------------

Le : Nat -> Nat -> Set
Le zero    n       = Top
Le (suc m) zero    = Empty
Le (suc m) (suc n) = Le m n

Le-refl : (n : Nat) -> Le n n
Le-refl zero    = tt
Le-refl (suc n) = Le-refl n

Le-suc : (m n : Nat) -> Le m n -> Le m (suc n)
Le-suc zero    n       h = tt
Le-suc (suc m) zero    ()
Le-suc (suc m) (suc n) h = Le-suc m n h

Le-trans : (l m n : Nat) -> Le l m -> Le m n -> Le l n
Le-trans zero    m       n       h1 h2 = tt
Le-trans (suc l) zero    n       ()
Le-trans (suc l) (suc m) zero    h1 ()
Le-trans (suc l) (suc m) (suc n) h1 h2 = Le-trans l m n h1 h2

Le-max-l : (m n : Nat) -> Le m (max m n)
Le-max-l zero    n       = tt
Le-max-l (suc m) zero    = Le-refl m
Le-max-l (suc m) (suc n) = Le-max-l m n

Le-max-r : (m n : Nat) -> Le n (max m n)
Le-max-r zero    n       = Le-refl n
Le-max-r (suc m) zero    = tt
Le-max-r (suc m) (suc n) = Le-max-r m n

Le-max-lub : (a b c : Nat) -> Le a c -> Le b c -> Le (max a b) c
Le-max-lub zero    b       c       h1 h2 = h2
Le-max-lub (suc a) zero    c       h1 h2 = h1
Le-max-lub (suc a) (suc b) zero    () h2
Le-max-lub (suc a) (suc b) (suc c) h1 h2 = Le-max-lub a b c h1 h2

max-mono : (a b c d : Nat) -> Le a c -> Le b d -> Le (max a b) (max c d)
max-mono a b c d hac hbd =
  Le-max-lub a b (max c d)
    (Le-trans a c (max c d) hac (Le-max-l c d))
    (Le-trans b d (max c d) hbd (Le-max-r c d))

------------------------------------------------------------------------
-- Decidable equality, given as a NUMERIC decision (0 = no, 1 = yes)
-- with the Set-valued form defined from it, so the two agree
-- definitionally -- exactly the `lei'/`leq' pairing MIN's OrderStage
-- relies on.
------------------------------------------------------------------------

natEqN : Nat -> Nat -> Nat
natEqN zero    zero    = suc zero
natEqN zero    (suc n) = zero
natEqN (suc m) zero    = zero
natEqN (suc m) (suc n) = natEqN m n

NatEq : Nat -> Nat -> Set
NatEq m n = isPos (natEqN m n)

NatEq-refl : (n : Nat) -> NatEq n n
NatEq-refl zero    = tt
NatEq-refl (suc n) = NatEq-refl n

NatEq-sound : (m n : Nat) -> NatEq m n -> Eq m n
NatEq-sound zero    zero    _  = refl
NatEq-sound zero    (suc n) ()
NatEq-sound (suc m) zero    ()
NatEq-sound (suc m) (suc n) h  = Eq-cong suc (NatEq-sound m n h)

NatEq-sym : (m n : Nat) -> NatEq m n -> NatEq n m
NatEq-sym zero    zero    h = tt
NatEq-sym zero    (suc n) ()
NatEq-sym (suc m) zero    ()
NatEq-sym (suc m) (suc n) h = NatEq-sym m n h

------------------------------------------------------------------------
-- Atoms
--
-- The paper's <atom> ::= any string of capital letters, together with
-- the numerals of Example 4 ("numerals are understood to be QUOTEd
-- atoms").  T and NIL are singled out because IF, ATOM and EQ mention
-- them by name.
------------------------------------------------------------------------

data Atom : Set where
  T   : Atom
  NIL : Atom
  num : Nat -> Atom
  sym : Nat -> Atom

-- All 16 clauses written out: --exact-split forbids a catch-all.

atEqN : Atom -> Atom -> Nat
atEqN T       T       = suc zero
atEqN T       NIL     = zero
atEqN T       (num n) = zero
atEqN T       (sym n) = zero
atEqN NIL     T       = zero
atEqN NIL     NIL     = suc zero
atEqN NIL     (num n) = zero
atEqN NIL     (sym n) = zero
atEqN (num m) T       = zero
atEqN (num m) NIL     = zero
atEqN (num m) (num n) = natEqN m n
atEqN (num m) (sym n) = zero
atEqN (sym m) T       = zero
atEqN (sym m) NIL     = zero
atEqN (sym m) (num n) = zero
atEqN (sym m) (sym n) = natEqN m n

AtEq : Atom -> Atom -> Set
AtEq a b = isPos (atEqN a b)

AtEq-refl : (a : Atom) -> AtEq a a
AtEq-refl T       = tt
AtEq-refl NIL     = tt
AtEq-refl (num n) = NatEq-refl n
AtEq-refl (sym n) = NatEq-refl n

AtEq-sym : (a b : Atom) -> AtEq a b -> AtEq b a
AtEq-sym T       T       h = tt
AtEq-sym T       NIL     ()
AtEq-sym T       (num n) ()
AtEq-sym T       (sym n) ()
AtEq-sym NIL     T       ()
AtEq-sym NIL     NIL     h = tt
AtEq-sym NIL     (num n) ()
AtEq-sym NIL     (sym n) ()
AtEq-sym (num m) T       ()
AtEq-sym (num m) NIL     ()
AtEq-sym (num m) (num n) h = NatEq-sym m n h
AtEq-sym (num m) (sym n) ()
AtEq-sym (sym m) T       ()
AtEq-sym (sym m) NIL     ()
AtEq-sym (sym m) (num n) ()
AtEq-sym (sym m) (sym n) h = NatEq-sym m n h

AtEq-of-Eq : (a b : Atom) -> Eq a b -> AtEq a b
AtEq-of-Eq a b e = Eq-transport (\ x -> AtEq a x) e (AtEq-refl a)

AtEq-sound : (a b : Atom) -> AtEq a b -> Eq a b
AtEq-sound T       T       h = refl
AtEq-sound T       NIL     ()
AtEq-sound T       (num n) ()
AtEq-sound T       (sym n) ()
AtEq-sound NIL     T       ()
AtEq-sound NIL     NIL     h = refl
AtEq-sound NIL     (num n) ()
AtEq-sound NIL     (sym n) ()
AtEq-sound (num m) T       ()
AtEq-sound (num m) NIL     ()
AtEq-sound (num m) (num n) h = Eq-cong num (NatEq-sound m n h)
AtEq-sound (num m) (sym n) ()
AtEq-sound (sym m) T       ()
AtEq-sound (sym m) NIL     ()
AtEq-sound (sym m) (num n) ()
AtEq-sound (sym m) (sym n) h = Eq-cong sym (NatEq-sound m n h)

------------------------------------------------------------------------
-- Finite elements
------------------------------------------------------------------------

mutual
  data FinEl : Set where
    Bot : FinEl                       -- the bottom of the whole lattice
    At  : Atom -> FinEl               -- the A summand
    Prd : FinEl -> FinEl -> FinEl     -- the V x V summand
    Fn  : FinFun -> FinEl             -- the V -> V summand

  -- A finite function is a finite set of input/output observations:
  -- "if the argument supplies at least u, the application supplies v".
  FinFun : Set
  FinFun = List (Pair FinEl FinEl)

-- Membership in a finite graph.

data InFun (u v : FinEl) : FinFun -> Set where
  in-here  : {g : FinFun} -> InFun u v (cons (mkSigma u v) g)
  in-there : {w : Pair FinEl FinEl} {g : FinFun} ->
             InFun u v g -> InFun u v (cons w g)

append : FinFun -> FinFun -> FinFun
append nil         g = g
append (cons p ps) g = cons p (append ps g)

------------------------------------------------------------------------
-- Shape of an element: what an "answer" reveals (section III).
------------------------------------------------------------------------

NotBot : FinEl -> Set
NotBot Bot       = Empty
NotBot (At a)    = Top
NotBot (Prd u v) = Top
NotBot (Fn g)    = Top

------------------------------------------------------------------------
-- RANK
--
-- The stage-relevant rank (MIN's RANK, not its rk): every immediate
-- component of a code has strictly smaller RANK, which is what makes
-- one Stage step strip one level in OrderStage.
--
-- NB: RANK measures the nesting of the code, NOT the number of
-- recursive unfoldings needed to observe it.  See LAZY/README.
------------------------------------------------------------------------

mutual
  RANK : FinEl -> Nat
  RANK Bot       = zero
  RANK (At a)    = zero
  RANK (Prd u v) = suc (max (RANK u) (RANK v))
  RANK (Fn g)    = suc (RANKFun g)

  RANKFun : FinFun -> Nat
  RANKFun nil         = zero
  RANKFun (cons p ps) = max (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

AtEq-trans : (a b c : Atom) -> AtEq a b -> AtEq b c -> AtEq a c
AtEq-trans a b c hab hbc = Eq-transport (\ x -> AtEq a x) (AtEq-sound b c hbc) hab

absurd : {A : Set} -> Empty -> A
absurd ()
