{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiTyping
--
-- The Tarski-style theory T_T with internal levels, cumulative
-- universes (bcde.pdf §4 and App. A), constraint products, level
-- products, ∅ and the loop-collapse rules (Fig. 12–14, App. C).
--
--   U_l type,  El_l a type (a : U_l),  Π, [ψ]A, [α]A, ∅ types;
--   codes  Π^l a b : U_l,  U^m_l : U_m (l < m),  ↑^m_l a : U_m (l ⩽ m),
--   ∅^l : U_l,  with the decoding equations
--     El_m U^m_l = U_l,  El_l (Π^l a b) = Π (El_l a) (El_l b),
--     El_m (↑^m_l a) = El_l a,  El_l ∅^l = ∅,
--   and the lift equations of App. A.
--
-- Judgements are invariant under level equality (bcde.pdf): U_l = U_l',
-- El_l a = El_l' a, and the codes are congruent in their levels.
-- The binder congruences carry the typings of their left components
-- (as in BCDE4.RussellTyping).
------------------------------------------------------------------------

module BCDE4.TarskiTyping where

open import BCDE4.Basic
open import BCDE4.TarskiSyntax
open import BCDE4.Levels

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

-- A context carries its level constraints at the bottom.
data Ctx : Nat -> Set where
  empty  : LCtx -> Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lctx : {n : Nat} -> Ctx n -> LCtx
lctx (empty Th)   = Th
lctx (extend G A) = lctx G

-- Γ, ψ : add a constraint (the term variables are unchanged)
addC : {n : Nat} -> Ctx n -> Constr -> Ctx n
addC (empty Th)   c = empty (lcons c Th)
addC (extend G A) c = extend (addC G c) A

lctx-addC : {n : Nat} (G : Ctx n) (c : Constr) -> Eq (lctx (addC G c)) (lcons c (lctx G))
lctx-addC (empty Th)   c = refl
lctx-addC (extend G A) c = lctx-addC G c

-- Γ, α : a fresh level variable (index 0); all levels of Γ are shifted
addL : {n : Nat} -> Ctx n -> Ctx n
addL (empty Th)   = empty (lsubTh lwkS Th)
addL (extend G A) = extend (addL G) (lshiftE A)

lctx-addL : {n : Nat} (G : Ctx n) -> Eq (lctx (addL G)) (lsubTh lwkS (lctx G))
lctx-addL (empty Th)   = refl
lctx-addL (extend G A) = lctx-addL G

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

lookup-addC : {n : Nat} (G : Ctx n) (c : Constr) (i : Fin n) -> Eq (lookup (addC G c) i) (lookup G i)
lookup-addC (extend G A) c fzero    = refl
lookup-addC (extend G A) c (fsuc i) = Eq-cong wkExpr (lookup-addC G c i)

lookup-addL : {n : Nat} (G : Ctx n) (i : Fin n) -> Eq (lookup (addL G) i) (lshiftE (lookup G i))
lookup-addL (extend G A) fzero    = Eq-sym (lsubE-ren lwkS wkRen A)
lookup-addL (extend G A) (fsuc i) =
  Eq-trans (Eq-cong wkExpr (lookup-addL G i)) (Eq-sym (lsubE-ren lwkS wkRen (lookup G i)))

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
  wf-empty  : {Th : LCtx} -> WfCtx (empty Th)
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- IsType
------------------------------------------------------------------------

data IsType where
  is-U : {n : Nat} {G : Ctx n} {l : LExpr}
    -> WfCtx G
    -> IsType G (U l)

  is-El : {n : Nat} {G : Ctx n} {a : Expr n} {l : LExpr}
    -> HasType G a (U l)
    -> IsType G (El l a)

  is-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (Pi A B)

  -- [ψ]A type
  is-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> IsType G (Grd c A)

  -- [α]A type
  is-LPi : {n : Nat} {G : Ctx n} {A : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> IsType G (LPi A)

  -- ∅ type
  is-Emp : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> IsType G Emp

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

data HasType where

  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTy G A B
    -> HasType G M B

  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G (Lam A B b) (Pi A B)

  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
           {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> HasType G (App A B c a) (subst1 B a)

  -- ⟨ψ⟩t : [ψ]A
  ty-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> HasType (addC G c) t A
    -> HasType G (GLam c A t) (Grd c A)

  -- ⟨α⟩u : [α]A
  ty-LLam : {n : Nat} {G : Ctx n} {A u : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> HasType (addL G) u A
    -> HasType G (LLam A u) (LPi A)

  -- t l : A(l/α)
  ty-LApp : {n : Nat} {G : Ctx n} {A t : Expr n} {l : LExpr}
    -> IsType (addL G) A
    -> HasType G t (LPi A)
    -> HasType G (LApp A t l) (lsub1 A l)

  -- in a context with a loop, ∅ : A
  ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> HasType G Emp A

  -- codes
  -- Π^l a b : U_l
  ty-PiCode : {n : Nat} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} {l : LExpr}
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> HasType G (PiCode l a b) (U l)

  -- U^m_l : U_m   (l < m)
  ty-UCode : {n : Nat} {G : Ctx n} {m l : LExpr}
    -> WfCtx G
    -> LtL (lctx G) l m
    -> HasType G (UCode m l) (U m)

  -- ↑^m_l a : U_m   (l ⩽ m, a : U_l)
  ty-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {m l : LExpr}
    -> LeL (lctx G) l m
    -> HasType G a (U l)
    -> HasType G (Lift m l a) (U m)

  -- ∅^l : U_l
  ty-EmpCode : {n : Nat} {G : Ctx n} {l : LExpr}
    -> WfCtx G
    -> HasType G (EmpCode l) (U l)

------------------------------------------------------------------------
-- ConvTy
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

  conv-Ty-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> ConvTy G (Pi A B) (Pi A' B')

  conv-Ty-El : {n : Nat} {G : Ctx n} {a a' : Expr n} {l : LExpr}
    -> ConvTm G a a' (U l)
    -> ConvTy G (El l a) (El l a')

  conv-Ty-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A B : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> ConvTy (addC G c) A B
    -> ConvTy G (Grd c A) (Grd c B)

  conv-Ty-LPi : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> ConvTy (addL G) A B
    -> ConvTy G (LPi A) (LPi B)

  -- [ψ]A = A when ψ is valid
  conv-Ty-Grd-beta : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n}
    -> ValidC (lctx G) c
    -> IsType G A
    -> ConvTy G (Grd c A) A

  -- [ψ]A = [ψ']A when ψ ⇔ ψ'
  conv-Ty-Grd-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A : Expr n}
    -> WfCtx G
    -> EquivC (lctx G) c c'
    -> IsType (addC G c) A
    -> ConvTy G (Grd c A) (Grd c' A)

  -- collapse
  conv-Ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> ConvTy G A Emp

  -- level equality
  conv-Ty-U-lvl : {n : Nat} {G : Ctx n} {l l' : LExpr}
    -> WfCtx G
    -> Valid (lctx G) l l'
    -> ConvTy G (U l) (U l')

  conv-Ty-El-lvl : {n : Nat} {G : Ctx n} {a : Expr n} {l l' : LExpr}
    -> Valid (lctx G) l l'
    -> HasType G a (U l)
    -> ConvTy G (El l a) (El l' a)

  -- the decoding equations
  conv-Ty-El-UCode : {n : Nat} {G : Ctx n} {m l : LExpr}
    -> WfCtx G
    -> LtL (lctx G) l m
    -> ConvTy G (El m (UCode m l)) (U l)

  conv-Ty-El-PiCode : {n : Nat} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} {l : LExpr}
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTy G (El l (PiCode l a b)) (Pi (El l a) (El l b))

  conv-Ty-El-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {m l : LExpr}
    -> LeL (lctx G) l m
    -> HasType G a (U l)
    -> ConvTy G (El m (Lift m l a)) (El l a)

  conv-Ty-El-EmpCode : {n : Nat} {G : Ctx n} {l : LExpr}
    -> WfCtx G
    -> ConvTy G (El l (EmpCode l)) Emp

------------------------------------------------------------------------
-- ConvTm
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

  conv-cong-Lam-body : {n : Nat} {G : Ctx n}
    {A : Expr n} {B b b' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> ConvTm (extend G A) b b' B
    -> ConvTm G (Lam A B b) (Lam A B b') (Pi A B)

  conv-cong-Lam-Ty : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType (extend G A) b B
    -> ConvTm G (Lam A B b) (Lam A' B' b) (Pi A B)

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
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)

  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
              {a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G a A
    -> ConvTm G (App A B (Lam A B b) a) (subst1 b a) (subst1 B a)

  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
             {c : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G c
       (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B)
                     (wkExpr c) (Var fzero)))
       (Pi A B)

  -- constraint products
  conv-cong-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t t' : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> HasType (addC G c) t A
    -> ConvTm (addC G c) t t' A
    -> ConvTm G (GLam c A t) (GLam c A t') (Grd c A)

  conv-GLam-beta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
    -> ValidC (lctx G) c
    -> IsType G A
    -> HasType G t A
    -> ConvTm G (GLam c A t) t A

  conv-GLam-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A t : Expr n}
    -> WfCtx G
    -> EquivC (lctx G) c c'
    -> IsType (addC G c) A
    -> HasType (addC G c) t A
    -> ConvTm G (GLam c A t) (GLam c' A t) (Grd c A)

  -- level products
  conv-cong-LLam : {n : Nat} {G : Ctx n} {A u u' : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> HasType (addL G) u A
    -> ConvTm (addL G) u u' A
    -> ConvTm G (LLam A u) (LLam A u') (LPi A)

  -- congruence in the annotations
  conv-cong-GLam-Ty : {n : Nat} {G : Ctx n} {c : Constr} {A A' t : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> ConvTy (addC G c) A A'
    -> HasType (addC G c) t A
    -> ConvTm G (GLam c A t) (GLam c A' t) (Grd c A)

  conv-cong-LLam-Ty : {n : Nat} {G : Ctx n} {A A' u : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> ConvTy (addL G) A A'
    -> HasType (addL G) u A
    -> ConvTm G (LLam A u) (LLam A' u) (LPi A)

  conv-cong-LApp-Ty : {n : Nat} {G : Ctx n} {A A' t : Expr n} {l : LExpr}
    -> IsType (addL G) A
    -> ConvTy (addL G) A A'
    -> HasType G t (LPi A)
    -> ConvTm G (LApp A t l) (LApp A' t l) (lsub1 A l)

  conv-cong-LApp-fun : {n : Nat} {G : Ctx n} {A t t' : Expr n} {l : LExpr}
    -> IsType (addL G) A
    -> ConvTm G t t' (LPi A)
    -> ConvTm G (LApp A t l) (LApp A t' l) (lsub1 A l)

  conv-cong-LApp-lvl : {n : Nat} {G : Ctx n} {A t : Expr n} {l l' : LExpr}
    -> IsType (addL G) A
    -> HasType G t (LPi A)
    -> Valid (lctx G) l l'
    -> ConvTy G (lsub1 A l) (lsub1 A l')
    -> ConvTm G (LApp A t l) (LApp A t l') (lsub1 A l)

  conv-LApp-beta : {n : Nat} {G : Ctx n} {A u : Expr n} {l : LExpr}
    -> IsType (addL G) A
    -> HasType (addL G) u A
    -> ConvTm G (LApp A (LLam A u) l) (lsub1 u l) (lsub1 A l)

  conv-LApp-eta : {n : Nat} {G : Ctx n} {A t : Expr n}
    -> IsType (addL G) A
    -> HasType G t (LPi A)
    -> ConvTm G t (LLam A (LApp (lsubE (liftL lwkS) A) (lshiftE t) (lvar zero))) (LPi A)

  -- guard η:  t = ⟨ψ⟩t : [ψ]A  (not in bcde.pdf Fig. 13; sound, since a
  -- term of type [ψ]A denotes ⊥ where ψ fails).  The typing of t in Γ,ψ
  -- is a presupposition carried as a premise (admissible:
  -- TarskiMeta.mk-conv-GLam-eta).
  conv-GLam-eta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> HasType G t (Grd c A)
    -> HasType (addC G c) t A
    -> ConvTm G t (GLam c A t) (Grd c A)

  -- collapse
  conv-collapse : {n : Nat} {G : Ctx n} {t A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> HasType G t A
    -> ConvTm G t Emp A

  -- codes: congruences
  conv-cong-PiCode : {n : Nat} {G : Ctx n}
    {a a' : Expr n} {b b' : Expr (suc n)} {l : LExpr}
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTm G a a' (U l)
    -> ConvTm (extend G (El l a)) b b' (U l)
    -> ConvTm G (PiCode l a b) (PiCode l a' b') (U l)

  conv-cong-Lift : {n : Nat} {G : Ctx n} {a a' : Expr n} {m l : LExpr}
    -> LeL (lctx G) l m
    -> ConvTm G a a' (U l)
    -> ConvTm G (Lift m l a) (Lift m l a') (U m)

  -- the lift equations (App. A)
  conv-Lift-refl : {n : Nat} {G : Ctx n} {a : Expr n} {m l : LExpr}
    -> Valid (lctx G) l m
    -> HasType G a (U l)
    -> ConvTm G (Lift m l a) a (U m)

  conv-Lift-Lift : {n : Nat} {G : Ctx n} {a : Expr n} {p m l : LExpr}
    -> LeL (lctx G) l m
    -> LeL (lctx G) m p
    -> HasType G a (U l)
    -> ConvTm G (Lift p m (Lift m l a)) (Lift p l a) (U p)

  conv-Lift-UCode : {n : Nat} {G : Ctx n} {m l k : LExpr}
    -> WfCtx G
    -> LtL (lctx G) k l
    -> LeL (lctx G) l m
    -> ConvTm G (Lift m l (UCode l k)) (UCode m k) (U m)

  conv-Lift-PiCode : {n : Nat} {G : Ctx n}
    {a : Expr n} {b : Expr (suc n)} {m l : LExpr}
    -> LeL (lctx G) l m
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTm G (Lift m l (PiCode l a b)) (PiCode m (Lift m l a) (Lift m l b)) (U m)

  conv-Lift-EmpCode : {n : Nat} {G : Ctx n} {m l : LExpr}
    -> WfCtx G
    -> LeL (lctx G) l m
    -> ConvTm G (Lift m l (EmpCode l)) (EmpCode m) (U m)

  -- codes: level equality
  conv-UCode-lvl : {n : Nat} {G : Ctx n} {m m' l l' : LExpr}
    -> WfCtx G
    -> Valid (lctx G) l l'
    -> Valid (lctx G) m m'
    -> LtL (lctx G) l m
    -> ConvTm G (UCode m l) (UCode m' l') (U m)

  conv-Lift-lvl : {n : Nat} {G : Ctx n} {a : Expr n} {m m' l l' : LExpr}
    -> Valid (lctx G) l l'
    -> Valid (lctx G) m m'
    -> LeL (lctx G) l m
    -> HasType G a (U l)
    -> ConvTm G (Lift m l a) (Lift m' l' a) (U m)

  conv-PiCode-lvl : {n : Nat} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} {l l' : LExpr}
    -> Valid (lctx G) l l'
    -> HasType G a (U l)
    -> HasType (extend G (El l a)) b (U l)
    -> ConvTm G (PiCode l a b) (PiCode l' a b) (U l)

  conv-EmpCode-lvl : {n : Nat} {G : Ctx n} {l l' : LExpr}
    -> WfCtx G
    -> Valid (lctx G) l l'
    -> ConvTm G (EmpCode l) (EmpCode l') (U l)
