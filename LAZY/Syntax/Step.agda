{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Syntax/Step.agda        (L5, part 3)
--
-- The paper's transformation rules (henderson.pdf section II), as a
-- relation on memories.  Each rule rewrites ONE cell; rules Fc and Fd,
-- the only ones that allocate ("Rules Fc and Fd are the only ones which
-- use additional storage"), are kept separate.
--
-- The paper's convention that "mu(pi0) = (CAR (CONS pi2 pi3))
-- implicitly asserts the existence of a pi1" is made explicit here.
------------------------------------------------------------------------

module LAZY.Syntax.Step where

open import LAZY.Domain.Basic
open import LAZY.Syntax.Heap

-- the paper's "choose the smallest i" in rule Fa
data AlistLookup : Alist -> Var -> Addr -> Set where
  al-here  : {x : Var} {q : Addr} {th : Alist} ->
             AlistLookup (cons (mkSigma x q) th) x q
  al-there : {y : Var} {r : Addr} {th : Alist} {x : Var} {q : Addr} ->
             Neg (Eq y x) -> AlistLookup th x q ->
             AlistLookup (cons (mkSigma y r) th) x q

data Step (mu : Heap) : Heap -> Set where

  -- [C]  mu(p0) = (CAR (CONS p2 p3))  =>  mu' = mu[ mu(p2) / p0 ]
  st-car : {p0 p1 p2 p3 : Addr} {e : Expr} ->
    Eq (mu p0) (just (ecar p1)) -> Eq (mu p1) (just (econs p2 p3)) ->
    Eq (mu p2) (just e) ->
    Step mu (upd mu p0 e)

  st-cdr : {p0 p1 p2 p3 : Addr} {e : Expr} ->
    Eq (mu p0) (just (ecdr p1)) -> Eq (mu p1) (just (econs p2 p3)) ->
    Eq (mu p3) (just e) ->
    Step mu (upd mu p0 e)

  -- [A]  "atom-hood is simply the property of being QUOTEd"
  st-atom-T : {p0 p1 : Addr} {a : Atom} ->
    Eq (mu p0) (just (eatom p1)) -> Eq (mu p1) (just (equote a)) ->
    Step mu (upd mu p0 (equote T))

  st-atom-NIL : {p0 p1 p2 p3 : Addr} ->
    Eq (mu p0) (just (eatom p1)) -> Eq (mu p1) (just (econs p2 p3)) ->
    Step mu (upd mu p0 (equote NIL))

  -- [E]
  st-eq-T : {p0 p1 p2 : Addr} {a1 a2 : Atom} ->
    Eq (mu p0) (just (eeq p1 p2)) ->
    Eq (mu p1) (just (equote a1)) -> Eq (mu p2) (just (equote a2)) ->
    AtEq a1 a2 ->
    Step mu (upd mu p0 (equote T))

  st-eq-NIL : {p0 p1 p2 : Addr} {a1 a2 : Atom} ->
    Eq (mu p0) (just (eeq p1 p2)) ->
    Eq (mu p1) (just (equote a1)) -> Eq (mu p2) (just (equote a2)) ->
    Neg (AtEq a1 a2) ->
    Step mu (upd mu p0 (equote NIL))

  -- [I]
  st-if-T : {p p0 p1 p2 : Addr} {e : Expr} ->
    Eq (mu p) (just (eif p0 p1 p2)) -> Eq (mu p0) (just (equote T)) ->
    Eq (mu p1) (just e) ->
    Step mu (upd mu p e)

  st-if-NIL : {p p0 p1 p2 : Addr} {e : Expr} ->
    Eq (mu p) (just (eif p0 p1 p2)) -> Eq (mu p0) (just (equote NIL)) ->
    Eq (mu p2) (just e) ->
    Step mu (upd mu p e)

  -- [P]  the assumed primitive
  st-plus : {p p1 p2 : Addr} {m n : Nat} ->
    Eq (mu p) (just (eplus p1 p2)) ->
    Eq (mu p1) (just (equote (num m))) -> Eq (mu p2) (just (equote (num n))) ->
    Step mu (upd mu p (equote (num (add m n))))

  -- [Fa]  a variable is looked up in the FUNARG's alist
  st-Fa : {p p0 q : Addr} {th : Alist} {x : Var} {e : Expr} ->
    Eq (mu p) (just (efunarg p0 th)) -> Eq (mu p0) (just (evar x)) ->
    AlistLookup th x q -> Eq (mu q) (just e) ->
    Step mu (upd mu p e)

  -- [Fb]
  st-Fb : {p p0 : Addr} {th : Alist} {a : Atom} ->
    Eq (mu p) (just (efunarg p0 th)) -> Eq (mu p0) (just (equote a)) ->
    Step mu (upd mu p (equote a))

  -- [G]  beta at a FUNARG closure
  st-G : {p pf pl p1 p2 : Addr} {th : Alist} {x : Var} ->
    Eq (mu p) (just (eapp pf p2)) ->
    Eq (mu pf) (just (efunarg pl th)) ->
    Eq (mu pl) (just (elam x p1)) ->
    Step mu (upd mu p (efunarg p1 (cons (mkSigma x p2) th)))

  -- [L]  "The following rule creates a circular structure."
  --      the new binding for the recursive variable points back at p
  st-L : {p pl p1 : Addr} {th : Alist} {x : Var} ->
    Eq (mu p) (just (efunarg pl th)) ->
    Eq (mu pl) (just (elabel x p1)) ->
    Step mu (upd mu p (efunarg p1 (cons (mkSigma x p) th)))
