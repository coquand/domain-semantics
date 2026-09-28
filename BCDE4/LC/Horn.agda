{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Horn
--
-- Horn-clause presentation of a level theory (Bezem–Coquand, TCS 2022,
-- "Loop-checking and the uniform word problem for join-semilattices
-- with an inflationary endomorphism", §2).
--
-- An ATOM (x , k) stands for the level x + k.  A level expression is the
-- join of its atoms (atomsL).  A constraint l = m gives the clauses
-- atoms(l) → b for b ∈ atoms(m) and atoms(m) → a for a ∈ atoms(l).
-- Derivability `Der Th P b` : b follows from the atoms satisfying P by
-- forward reasoning with all upward shifts of these clauses and the
-- predecessor clauses x + (k+1) → x + k.
------------------------------------------------------------------------

module BCDE4.LC.Horn where

open import BCDE4.Basic
open import BCDE4.Levels

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A -> List A -> List A
infixr 5 _∷_

data Mem {A : Set} (a : A) : List A -> Set where
  here  : {xs : List A} -> Mem a (a ∷ xs)
  there : {b : A} {xs : List A} -> Mem a xs -> Mem a (b ∷ xs)

_++_ : {A : Set} -> List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : {A B : Set} -> (A -> List B) -> List A -> List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

mem-++-l : {A : Set} {a : A} (xs ys : List A) -> Mem a xs -> Mem a (xs ++ ys)
mem-++-l (x ∷ xs) ys here      = here
mem-++-l (x ∷ xs) ys (there h) = there (mem-++-l xs ys h)

mem-++-r : {A : Set} {a : A} (xs ys : List A) -> Mem a ys -> Mem a (xs ++ ys)
mem-++-r []       ys h = h
mem-++-r (x ∷ xs) ys h = there (mem-++-r xs ys h)

mem-++-split : {A : Set} {a : A} (xs ys : List A) -> Mem a (xs ++ ys) -> Either (Mem a xs) (Mem a ys)
mem-++-split []       ys h         = inr h
mem-++-split (x ∷ xs) ys here      = inl here
mem-++-split (x ∷ xs) ys (there h) with mem-++-split xs ys h
... | inl h' = inl (there h')
... | inr h' = inr h'

mem-map : {A B : Set} {a : A} (f : A -> B) (xs : List A) -> Mem a xs -> Mem (f a) (map f xs)
mem-map f (x ∷ xs) here      = here
mem-map f (x ∷ xs) (there h) = there (mem-map f xs h)

mem-map-inv : {A B : Set} {b : B} (f : A -> B) (xs : List A) -> Mem b (map f xs) ->
  Sigma A (\ a -> Pair (Mem a xs) (Eq b (f a)))
mem-map-inv f (x ∷ xs) here      = mkSigma x (mkSigma here refl)
mem-map-inv f (x ∷ xs) (there h) =
  let r = mem-map-inv f xs h in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r)))

mem-concatMap : {A B : Set} {a : A} {b : B} (f : A -> List B) (xs : List A) ->
  Mem a xs -> Mem b (f a) -> Mem b (concatMap f xs)
mem-concatMap f (x ∷ xs) here      hb = mem-++-l (f x) (concatMap f xs) hb
mem-concatMap f (x ∷ xs) (there h) hb = mem-++-r (f x) (concatMap f xs) (mem-concatMap f xs h hb)

mem-concatMap-inv : {A B : Set} {b : B} (f : A -> List B) (xs : List A) ->
  Mem b (concatMap f xs) -> Sigma A (\ a -> Pair (Mem a xs) (Mem b (f a)))
mem-concatMap-inv f (x ∷ xs) h with mem-++-split (f x) (concatMap f xs) h
... | inl h' = mkSigma x (mkSigma here h')
... | inr h' = let r = mem-concatMap-inv f xs h' in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r)))

------------------------------------------------------------------------
-- Atoms and clauses
------------------------------------------------------------------------

Atom : Set
Atom = Pair Nat Nat          -- (variable , offset)

shiftA : Nat -> Atom -> Atom
shiftA s a = mkSigma (fst a) (s + snd a)

atomsL : LExpr -> List Atom
atomsL (lvar i)   = mkSigma i zero ∷ []
atomsL (lsup l m) = atomsL l ++ atomsL m
atomsL (lnext l)  = map (shiftA (suc zero)) (atomsL l)

-- the level denoted by an atom
atomL : Atom -> LExpr
atomL a = nexts (snd a) (lvar (fst a))
  where
    nexts : Nat -> LExpr -> LExpr
    nexts zero    l = l
    nexts (suc k) l = lnext (nexts k l)

record Clause : Set where
  constructor mkClause
  field
    body : List Atom       -- non-empty for clauses coming from constraints
    head : Atom
open Clause public

-- clauses of one constraint l = m
clausesC : Constr -> List Clause
clausesC (ceq l m) =
  map (mkClause (atomsL l)) (atomsL m) ++ map (mkClause (atomsL m)) (atomsL l)

-- the finite set of base clauses of a theory
clausesTh : LCtx -> List Clause
clausesTh lnil         = []
clausesTh (lcons c Th) = clausesC c ++ clausesTh Th

------------------------------------------------------------------------
-- Derivability (forward reasoning), hypotheses given by a predicate
------------------------------------------------------------------------

data Der (Th : LCtx) (P : Atom -> Set) : Atom -> Set where
  d-hyp    : {b : Atom} -> P b -> Der Th P b
  d-pred   : {x k : Nat} -> Der Th P (mkSigma x (suc k)) -> Der Th P (mkSigma x k)
  d-clause : {c : Clause} -> Mem c (clausesTh Th) -> (s : Nat) ->
             ((a : Atom) -> Mem a (body c) -> Der Th P (shiftA s a)) ->
             Der Th P (shiftA s (head c))

-- hypotheses from a list of atoms
InL : List Atom -> Atom -> Set
InL A b = Mem b A

-- derivability is monotone in the hypotheses and transitive (cut)
der-mono : {Th : LCtx} {P Q : Atom -> Set} -> ((a : Atom) -> P a -> Q a) ->
  {b : Atom} -> Der Th P b -> Der Th Q b
der-mono h (d-hyp p)          = d-hyp (h _ p)
der-mono h (d-pred d)         = d-pred (der-mono h d)
der-mono h (d-clause mc s ds) = d-clause mc s (\ a ma -> der-mono h (ds a ma))

der-cut : {Th : LCtx} {P Q : Atom -> Set} -> ((a : Atom) -> Q a -> Der Th P a) ->
  {b : Atom} -> Der Th Q b -> Der Th P b
der-cut h (d-hyp q)          = h _ q
der-cut h (d-pred d)         = d-pred (der-cut h d)
der-cut h (d-clause mc s ds) = d-clause mc s (\ a ma -> der-cut h (ds a ma))
