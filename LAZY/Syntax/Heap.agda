{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Syntax/Heap.agda        (L2)
--
-- Hyper-Pure LISP expressions and the paper's memory
-- (henderson.pdf, section II).
--
--   <expression> ::= <variable> | (QUOTE <atom>) | (CONS e e) | (CAR e)
--                  | (CDR e) | (ATOM e) | (EQ e e) | (IF e e e)
--                  | (e e) | (LAMBDA v e) | (LABEL v e) | (FUNARG e <alist>)
--
-- "each cell is capable of holding any of the forms listed as
-- <expression>s where ADDRESSES are used for any component of type
-- expression" -- so every subexpression position is an Addr.
--
-- PLUS is the paper's assumed extra primitive ("we shall assume that
-- PLUS is a primitive operator with the same general characteristics as
-- EQ"), needed for Example 4.
------------------------------------------------------------------------

module LAZY.Syntax.Heap where

open import LAZY.Domain.Basic

------------------------------------------------------------------------
-- Variables and addresses
------------------------------------------------------------------------

Var : Set
Var = Nat

Addr : Set
Addr = Nat

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

mutual
  data Expr : Set where
    evar    : Var -> Expr
    equote  : Atom -> Expr
    econs   : Addr -> Addr -> Expr
    ecar    : Addr -> Expr
    ecdr    : Addr -> Expr
    eatom   : Addr -> Expr
    eeq     : Addr -> Addr -> Expr
    eif     : Addr -> Addr -> Addr -> Expr
    eapp    : Addr -> Addr -> Expr
    elam    : Var -> Addr -> Expr
    elabel  : Var -> Addr -> Expr
    efunarg : Addr -> Alist -> Expr
    eplus   : Addr -> Addr -> Expr        -- the paper's assumed primitive

  -- <alist> ::= <empty> | <variable> <expression> <alist>
  Alist : Set
  Alist = List (Pair Var Addr)

------------------------------------------------------------------------
-- Memories
--
-- "the state of a computation is described by a PARTIAL memory
-- function": addresses on which mu is undefined are the free cells.
------------------------------------------------------------------------

Heap : Set
Heap = Addr -> Maybe Expr

InDom : Heap -> Addr -> Set
InDom mu p = Sigma Expr (\ e -> Eq (mu p) (just e))

Fresh : Heap -> Addr -> Set
Fresh mu p = Eq (mu p) nothing

------------------------------------------------------------------------
-- Cell update:  mu [ e / p0 ]
--
--   mu[ e / p0 ] = \ p . if p = p0 then e else mu p
------------------------------------------------------------------------

ifNatEq : {A : Set} -> Nat -> Nat -> A -> A -> A
ifNatEq zero    zero    t e = t
ifNatEq zero    (suc n) t e = e
ifNatEq (suc m) zero    t e = e
ifNatEq (suc m) (suc n) t e = ifNatEq m n t e

upd : Heap -> Addr -> Expr -> Heap
upd mu p0 e = \ p -> ifNatEq p p0 (just e) (mu p)

------------------------------------------------------------------------
-- Addresses occurring in an expression, and the paper's consistency
-- property: "if a particular address occurs as a component anywhere in
-- the memory, then mu(p) is defined ... no non-free cell points at a
-- free one."
------------------------------------------------------------------------

appendL : {A : Set} -> List A -> List A -> List A
appendL nil         ys = ys
appendL (cons x xs) ys = cons x (appendL xs ys)

alistAddrs : Alist -> List Addr
alistAddrs nil         = nil
alistAddrs (cons b bs) = cons (snd b) (alistAddrs bs)

addrs : Expr -> List Addr
addrs (evar x)         = nil
addrs (equote a)       = nil
addrs (econs p q)      = cons p (cons q nil)
addrs (ecar p)         = cons p nil
addrs (ecdr p)         = cons p nil
addrs (eatom p)        = cons p nil
addrs (eeq p q)        = cons p (cons q nil)
addrs (eif p q r)      = cons p (cons q (cons r nil))
addrs (eapp p q)       = cons p (cons q nil)
addrs (elam x p)       = cons p nil
addrs (elabel x p)     = cons p nil
addrs (efunarg p th)   = cons p (alistAddrs th)
addrs (eplus p q)      = cons p (cons q nil)

All : {A : Set} -> (A -> Set) -> List A -> Set
All P nil         = Top
All P (cons x xs) = Pair (P x) (All P xs)

WfHeap : Heap -> Set
WfHeap mu = (p : Addr) (e : Expr) -> Eq (mu p) (just e) -> All (InDom mu) (addrs e)

------------------------------------------------------------------------
-- Discriminating the twelve (+PLUS) expression forms.
--
-- Two derivations at the SAME cell carry two `Eq (mu p) (just e)'
-- premises; `cell-clash' turns them into NatEq of the tags, which
-- reduces to Empty on the nose whenever the two forms differ.  That is
-- what makes the impossible cases of the inversion lemmas uniform
-- one-liners.
------------------------------------------------------------------------

just-inj : {A : Set} {x y : A} -> Eq (just x) (just y) -> Eq x y
just-inj refl = refl

tag : Expr -> Nat
tag (evar _)      = 0
tag (equote _)    = 1
tag (econs _ _)   = 2
tag (ecar _)      = 3
tag (ecdr _)      = 4
tag (eatom _)     = 5
tag (eeq _ _)     = 6
tag (eif _ _ _)   = 7
tag (eapp _ _)    = 8
tag (elam _ _)    = 9
tag (elabel _ _)  = 10
tag (efunarg _ _) = 11
tag (eplus _ _)   = 12

tag-Eq : {e1 e2 : Expr} -> Eq e1 e2 -> NatEq (tag e1) (tag e2)
tag-Eq {e1 = e1} refl = NatEq-refl (tag e1)

cell-eq : {mu : Heap} {p : Addr} {e1 e2 : Expr} ->
  Eq (mu p) (just e1) -> Eq (mu p) (just e2) -> Eq e1 e2
cell-eq q1 q2 = just-inj (Eq-trans (Eq-sym q1) q2)

cell-clash : (mu : Heap) (p : Addr) {e1 e2 : Expr} ->
  Eq (mu p) (just e1) -> Eq (mu p) (just e2) -> NatEq (tag e1) (tag e2)
cell-clash mu p q1 q2 = tag-Eq (cell-eq {mu = mu} {p = p} q1 q2)

-- injectivity of the forms we invert at
evar-inj : {x y : Var} -> Eq (evar x) (evar y) -> Eq x y
evar-inj refl = refl

equote-inj : {a b : Atom} -> Eq (equote a) (equote b) -> Eq a b
equote-inj refl = refl

econs-inj1 : {p1 p2 q1 q2 : Addr} -> Eq (econs p1 p2) (econs q1 q2) -> Eq p1 q1
econs-inj1 refl = refl

econs-inj2 : {p1 p2 q1 q2 : Addr} -> Eq (econs p1 p2) (econs q1 q2) -> Eq p2 q2
econs-inj2 refl = refl

------------------------------------------------------------------------
-- Decidable address equality, and how `upd' reads back.
------------------------------------------------------------------------

data Either (A B : Set) : Set where
  inl : A -> Either A B
  inr : B -> Either A B

decEqNat : (m n : Nat) -> Either (Eq m n) (Neg (Eq m n))
decEqNat zero    zero    = inl refl
decEqNat zero    (suc n) = inr (\ ())
decEqNat (suc m) zero    = inr (\ ())
decEqNat (suc m) (suc n) with decEqNat m n
... | inl e  = inl (Eq-cong suc e)
... | inr ne = inr (\ e -> ne (suc-inj e))
  where
    suc-inj : {a b : Nat} -> Eq (suc a) (suc b) -> Eq a b
    suc-inj refl = refl

ifNatEq-refl : {A : Set} (n : Nat) (t e : A) -> Eq (ifNatEq n n t e) t
ifNatEq-refl zero    t e = refl
ifNatEq-refl (suc n) t e = ifNatEq-refl n t e

ifNatEq-neq : {A : Set} (m n : Nat) (t e : A) -> Neg (Eq m n) -> Eq (ifNatEq m n t e) e
ifNatEq-neq zero    zero    t e ne = absurd (ne refl)
ifNatEq-neq zero    (suc n) t e ne = refl
ifNatEq-neq (suc m) zero    t e ne = refl
ifNatEq-neq (suc m) (suc n) t e ne =
  ifNatEq-neq m n t e (\ q -> ne (Eq-cong suc q))

upd-hit : (mu : Heap) (p0 : Addr) (e : Expr) -> Eq (upd mu p0 e p0) (just e)
upd-hit mu p0 e = ifNatEq-refl p0 (just e) (mu p0)

upd-miss : (mu : Heap) (p0 p : Addr) (e : Expr) ->
  Neg (Eq p p0) -> Eq (upd mu p0 e p) (mu p)
upd-miss mu p0 p e ne = ifNatEq-neq p p0 (just e) (mu p) ne

elabel-inj1 : {x y : Var} {p q : Addr} -> Eq (elabel x p) (elabel y q) -> Eq x y
elabel-inj1 refl = refl

elabel-inj2 : {x y : Var} {p q : Addr} -> Eq (elabel x p) (elabel y q) -> Eq p q
elabel-inj2 refl = refl

efunarg-inj1 : {p q : Addr} {th ta : Alist} -> Eq (efunarg p th) (efunarg q ta) -> Eq p q
efunarg-inj1 refl = refl

efunarg-inj2 : {p q : Addr} {th ta : Alist} -> Eq (efunarg p th) (efunarg q ta) -> Eq th ta
efunarg-inj2 refl = refl
