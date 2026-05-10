{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.TarskiTyping
--
-- Typing and βη-conversion for the Tarski-style theory T_T (slides 8).
--
-- Five mutually defined judgements (parallel to RussellTyping):
--   WfCtx, IsType, HasType, ConvTy, ConvTm.
--
-- Universe structure (Tarski):
--   * U n is a *type only*; it is not a term.
--   * The code of U n in U m (with n < m) is the term UCode m n : U m.
--   * El n a is the type associated to a code a : U n.
--   * Lift m n a is the lift of a code a : U n into U m, for n < m.
--
-- The six judgemental equations:
--   (1)  El m (UCode m l)       ≡  U l                        (type)
--   (2)  El l (PiCode l a b)    ≡  Π (El l a) (El l b)        (type)
--   (3)  El m (Lift m l a)      ≡  El l a                     (type)
--   (4)  Lift n m (Lift m l a)  ≡  Lift n l a   : U n
--   (5)  Lift m l (UCode l n)   ≡  UCode m n    : U m
--   (6)  Lift m l (PiCode l a b)≡  PiCode m (Lift m l a) (Lift m l b)
--                                                : U m
------------------------------------------------------------------------

module Sterbac.TarskiTyping where

open import Sterbac.Basic
open import Sterbac.TarskiSyntax

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data Ctx : Nat -> Set where
  empty  : Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

------------------------------------------------------------------------
-- Judgement forms (mutual)
------------------------------------------------------------------------

data WfCtx   : {n : Nat} -> Ctx n -> Set
data IsType  : {n : Nat} -> Ctx n -> Expr n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTy  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

------------------------------------------------------------------------
-- WfCtx
------------------------------------------------------------------------

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- IsType  ("Γ ⊢ A type")
------------------------------------------------------------------------

data IsType where

  is-Ty-U : {n : Nat} {G : Ctx n} {l : Nat}
    -> WfCtx G
    -> IsType G (U l)

  is-Ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (Pi A B)

  is-Ty-El : {n : Nat} {G : Ctx n} {a : Expr n} {l : Nat}
    -> HasType G a (U l)
    -> IsType G (El l a)

------------------------------------------------------------------------
-- HasType  ("Γ ⊢ M : A")
------------------------------------------------------------------------

data HasType where

  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTy G A B
    -> HasType G M B

  -- λ(A,B,b) : Π(A,B)
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G (Lam A B b) (Pi A B)

  -- app(A,B,c,a) : B[a]
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> HasType G (App A B c a) (subst1 B a)

  -- Π^l(a,b) : U_l
  ty-PiCode : {n : Nat} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} {l : Nat}
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> HasType G (PiCode l a b) (U l)

  -- U^m_n : U_m  (when n < m)
  ty-UCode : {n : Nat} {G : Ctx n} {m l : Nat}
    -> WfCtx G
    -> Lt l m
    -> HasType G (UCode m l) (U m)

  -- ↑^m_n a : U_m  (when n < m, a : U_n)
  ty-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {m l : Nat}
    -> Lt l m
    -> HasType G a (U l)
    -> HasType G (Lift m l a) (U m)

------------------------------------------------------------------------
-- ConvTy  ("Γ ⊢ A = B")
------------------------------------------------------------------------

data ConvTy where

  conv-Ty-refl : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> ConvTy G A A

  conv-Ty-sym : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B
    -> ConvTy G B A

  conv-Ty-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
    -> ConvTy G A B
    -> ConvTy G B C
    -> ConvTy G A C

  -- congruences for type formers
  conv-Ty-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> ConvTy G (Pi A B) (Pi A' B')

  conv-Ty-El : {n : Nat} {G : Ctx n} {a a' : Expr n} {l : Nat}
    -> ConvTm G a a' (U l)
    -> ConvTy G (El l a) (El l a')

  ----------------------------------------------------------------------
  -- The three Tarski judgemental equations at the type level
  ----------------------------------------------------------------------

  -- (1)  El m (UCode m l)  =  U l
  conv-Ty-El-UCode : {n : Nat} {G : Ctx n} {m l : Nat}
    -> WfCtx G
    -> Lt l m
    -> ConvTy G (El m (UCode m l)) (U l)

  -- (2)  El l (PiCode l a b)  =  Π (El l a) (El l b)
  conv-Ty-El-PiCode : {n : Nat} {G : Ctx n}
    {a : Expr n} {b : Expr (suc n)} {l : Nat}
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTy G (El l (PiCode l a b)) (Pi (El l a) (El l b))

  -- (3)  El m (Lift m l a)  =  El l a
  conv-Ty-El-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {m l : Nat}
    -> Lt l m
    -> HasType G a (U l)
    -> ConvTy G (El m (Lift m l a)) (El l a)

------------------------------------------------------------------------
-- ConvTm  ("Γ ⊢ M = N : A")
------------------------------------------------------------------------

data ConvTm where

  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A
    -> ConvTm G M M A

  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N M A

  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N P A
    -> ConvTm G M P A

  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTy G A B
    -> ConvTm G M N B

  ----------------------------------------------------------------------
  -- congruences for term formers
  ----------------------------------------------------------------------

  -- Lam congruences (split for cleaner presupposition; the strong
  -- "all four change" form is derivable by transitivity).
  conv-cong-Lam-body : {n : Nat} {G : Ctx n}
    {A : Expr n} {B b b' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm (extend G A) b b' B
    -> ConvTm G (Lam A B b) (Lam A B b') (Pi A B)

  conv-cong-Lam-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' b : Expr (suc n)}
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType (extend G A) b B
    -> ConvTm G (Lam A B b) (Lam A' B' b) (Pi A B)

  -- App congruences (split for cleaner presupposition).
  -- App-arg carries an explicit ConvTy capturing the cross-substitution
  -- subst1 B a = subst1 B a', because Tarski lacks cross-substitution
  -- as a primitive lemma in this development.
  conv-cong-App-fun : {n : Nat} {G : Ctx n}
    {A : Expr n} {B : Expr (suc n)} {c c' a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm G c c' (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A B c' a) (subst1 B a)

  conv-cong-App-arg : {n : Nat} {G : Ctx n}
    {A : Expr n} {B : Expr (suc n)} {c a a' : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G a a' A
    -> ConvTy G (subst1 B a) (subst1 B a')
    -> ConvTm G (App A B c a) (App A B c a') (subst1 B a)

  conv-cong-App-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)} {c a : Expr n}
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)

  conv-cong-PiCode : {n : Nat} {G : Ctx n}
    {a a' : Expr n} {b b' : Expr (suc n)} {l : Nat}
    -> ConvTm G a a' (U l)
    -> ConvTm (extend G (El l a)) b b' (U l)
    -> ConvTm G (PiCode l a b) (PiCode l a' b') (U l)

  conv-cong-Lift : {n : Nat} {G : Ctx n} {a a' : Expr n} {m l : Nat}
    -> Lt l m
    -> ConvTm G a a' (U l)
    -> ConvTm G (Lift m l a) (Lift m l a') (U m)

  ----------------------------------------------------------------------
  -- β
  -- app(A,B, λ(A,B,b), a) = b[a] : B[a]
  ----------------------------------------------------------------------
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G a A
    -> ConvTm G (App A B (Lam A B b) a) (subst1 b a) (subst1 B a)

  ----------------------------------------------------------------------
  -- η
  -- c = λ(A,B, app(A↑, B↑, c↑, v_0)) : Π(A,B)
  ----------------------------------------------------------------------
  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G c
       (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B)
                     (wkExpr c) (Var fzero)))
       (Pi A B)

  ----------------------------------------------------------------------
  -- The three Tarski judgemental equations on terms (codes)
  ----------------------------------------------------------------------

  -- (4)  Lift n m (Lift m l a) = Lift n l a  : U n
  conv-Lift-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {nu m l : Nat}
    -> Lt l m
    -> Lt m nu
    -> HasType G a (U l)
    -> ConvTm G (Lift nu m (Lift m l a)) (Lift nu l a) (U nu)

  -- (5)  Lift m l (UCode l n) = UCode m n  : U m
  conv-Lift-UCode : {n : Nat} {G : Ctx n} {m l nu : Nat}
    -> WfCtx G
    -> Lt nu l
    -> Lt l m
    -> ConvTm G (Lift m l (UCode l nu)) (UCode m nu) (U m)

  -- (6)  Lift m l (PiCode l a b) = PiCode m (Lift m l a) (Lift m l b) : U m
  conv-Lift-PiCode : {n : Nat} {G : Ctx n}
    {a : Expr n} {b : Expr (suc n)} {m l : Nat}
    -> Lt l m
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTm G (Lift m l (PiCode l a b))
                (PiCode m (Lift m l a) (Lift m l b))
                (U m)
