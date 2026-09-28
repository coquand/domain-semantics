{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.RussellTyping
--
-- Typing and βη-conversion for the Russell-style theory T_R.
--
-- Five mutually defined judgements:
--
--   WfCtx   G            "Γ ctx"
--   IsType  G A          "Γ ⊢ A type"
--   HasType G M A        "Γ ⊢ M : A"
--   ConvTy  G A B        "Γ ⊢ A = B"
--   ConvTm  G M N A      "Γ ⊢ M = N : A"
--
-- Cumulative universes U_l à la Russell (bcde.pdf App. B):
--   U_l : U_m (l < m),  A : U_l ⇒ A : U_m (l ⩽ m),  Π A B : U_l,
-- and a separate type judgement: A : U_l ⇒ A type, Π of types, and the
-- large types [α]A and [ψ]A (which live in no universe).
--
-- λ and app keep their (A,B) annotations.
------------------------------------------------------------------------

module BCDE4.RussellTyping where

open import BCDE4.Basic
open import BCDE4.RussellSyntax
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
-- IsType  ("Γ ⊢ A type")
--
--   Γ ⊢ A : U
--   ────────────
--   Γ ⊢ A type
------------------------------------------------------------------------

data IsType where
  is-Ty-from-U : {n : Nat} {G : Ctx n} {A : Expr n} {l : LExpr}
    -> HasType G A (U l)
    -> IsType G A

  is-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (Pi A B)

  -- [ψ]A type   (bcde.pdf Fig. 13)
  is-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> IsType G (Grd c A)

  -- [α]A type   (bcde.pdf Fig. 12)
  is-LPi : {n : Nat} {G : Ctx n} {A : Expr n}
    -> WfCtx G
    -> IsType (addL G) A
    -> IsType G (LPi A)

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

data HasType where

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

  -- ∅ : U_l
  ty-Emp : {n : Nat} {G : Ctx n} {l : LExpr}
    -> WfCtx G
    -> HasType G Emp (U l)

  -- in a context with a loop, ∅ : A   (bcde.pdf Fig. 14)
  ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> HasType G Emp A

  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  -- type conversion uses ConvTy, not ConvTm
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTy G A B
    -> HasType G M B

  -- U_l : U_m   (l < m)
  ty-U : {n : Nat} {G : Ctx n} {l m : LExpr}
    -> WfCtx G
    -> LtL (lctx G) l m
    -> HasType G (U l) (U m)

  -- cumulativity:  A : U_l,  l ⩽ m  ⇒  A : U_m
  ty-cum : {n : Nat} {G : Ctx n} {A : Expr n} {l m : LExpr}
    -> HasType G A (U l)
    -> LeL (lctx G) l m
    -> HasType G A (U m)

  -- Γ ⊢ A : U_l   Γ.A ⊢ B : U_l
  -- ───────────────────────────────
  -- Γ ⊢ Π(A,B) : U_l
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {l : LExpr}
    -> HasType G A (U l)
    -> HasType (extend G A) B (U l)
    -> HasType G (Pi A B) (U l)

  -- Γ ⊢ A type   Γ.A ⊢ B type   Γ.A ⊢ b : B
  -- ──────────────────────────────────────────────
  -- Γ ⊢ λ(A,B,b) : Π(A,B)
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G (Lam A B b) (Pi A B)

  -- Γ ⊢ A type   Γ.A ⊢ B type   Γ ⊢ c : Π(A,B)   Γ ⊢ a : A
  -- ────────────────────────────────────────────────────────────
  -- Γ ⊢ app(A,B,c,a) : B[a]
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
           {c a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> HasType G a A
    -> HasType G (App A B c a) (subst1 B a)

------------------------------------------------------------------------
-- ConvTy  ("Γ ⊢ A = B")
--
-- Inherits all structure from ConvTm at U, plus its own equivalence
-- rules so we can manipulate type-equality without naming a level.
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

  -- congruence for Π at the type level.  The binder congruences (here,
  -- conv-cong-Pi, conv-cong-Lam-body, conv-cong-Lam-Ty) carry the
  -- typings of the LEFT-hand components as extra premises.  These are
  -- presuppositions (admissible: see the mk-* rules of RussellMeta,
  -- which have the paper's premises only); having them as subderivations
  -- keeps the metatheory and the adequacy proof structurally recursive.
  conv-Ty-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTy G A A'
    -> ConvTy (extend G A) B B'
    -> ConvTy G (Pi A B) (Pi A' B')

  -- A = B : U  ⇒  A = B
  -- congruence for [ψ]
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

  -- [ψ]A = A when ψ is valid  (bcde.pdf Fig. 13)
  conv-Ty-Grd-beta : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n}
    -> ValidC (lctx G) c
    -> IsType G A
    -> ConvTy G (Grd c A) A

  -- [ψ]A = [ψ']A when ψ ⇔ ψ' is valid
  conv-Ty-Grd-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A : Expr n}
    -> WfCtx G
    -> EquivC (lctx G) c c'
    -> IsType (addC G c) A
    -> ConvTy G (Grd c A) (Grd c' A)

  -- collapse: in a context with a loop, A = ∅   (bcde.pdf Fig. 14)
  conv-Ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> ConvTy G A Emp

  conv-Ty-from-U : {n : Nat} {G : Ctx n} {A B : Expr n} {l : LExpr}
    -> ConvTm G A B (U l)
    -> ConvTy G A B

------------------------------------------------------------------------
-- ConvTm  (judgemental βη conversion)
------------------------------------------------------------------------

data ConvTm where

  -- equivalence
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

  -- propagate type equality on the type of the conversion
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTy G A B
    -> ConvTm G M N B

  -- congruence rules
  conv-cong-Pi : {n : Nat} {G : Ctx n}
    {A A' : Expr n} {B B' : Expr (suc n)} {l : LExpr}
    -> HasType G A (U l)
    -> HasType (extend G A) B (U l)
    -> ConvTm G A A' (U l)
    -> ConvTm (extend G A) B B' (U l)
    -> ConvTm G (Pi A B) (Pi A' B') (U l)

  -- cumulativity of conversion
  conv-cum : {n : Nat} {G : Ctx n} {A B : Expr n} {l m : LExpr}
    -> ConvTm G A B (U l)
    -> LeL (lctx G) l m
    -> ConvTm G A B (U m)

  -- U_l = U_l' : U_m  for  l = l'  (invariance under level equality)
  conv-U-lvl : {n : Nat} {G : Ctx n} {l l' m : LExpr}
    -> WfCtx G
    -> Valid (lctx G) l l'
    -> LtL (lctx G) l m
    -> ConvTm G (U l) (U l') (U m)

  -- Lam / App congruences split (matches Tarski).
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

  -- β
  -- app(A,B, λ(A,B,b), a) = b[a] : B[a]
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
              {a : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) b B
    -> HasType G a A
    -> ConvTm G (App A B (Lam A B b) a) (subst1 b a) (subst1 B a)

  -- η
  -- c = λ(A,B, app(A↑, B↑, c↑, v_0)) : Π(A,B)
  -- congruences for [ψ] and ⟨ψ⟩
  conv-cong-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t t' : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> HasType (addC G c) t A
    -> ConvTm (addC G c) t t' A
    -> ConvTm G (GLam c A t) (GLam c A t') (Grd c A)

  -- [ψ]A = A and ⟨ψ⟩t = t when ψ is valid  (bcde.pdf Fig. 13).  The
  -- premises are stated in Γ (equivalent to Γ,ψ since ψ is valid).
  conv-GLam-beta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
    -> ValidC (lctx G) c
    -> IsType G A
    -> HasType G t A
    -> ConvTm G (GLam c A t) t A

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

  -- invariance under level equality (bcde.pdf): t l = t l' when l = l'
  -- is valid.  The instance conversion A(l/α) = A(l'/α) is a premise, as
  -- in conv-cong-App-arg (admissible: BCDE4.RussellLeq, whose
  -- mk-conv-cong-LApp-lvl has the paper's premises only).
  conv-cong-LApp-lvl : {n : Nat} {G : Ctx n} {A t : Expr n} {l l' : LExpr}
    -> IsType (addL G) A
    -> HasType G t (LPi A)
    -> Valid (lctx G) l l'
    -> ConvTy G (lsub1 A l) (lsub1 A l')
    -> ConvTm G (LApp A t l) (LApp A t l') (lsub1 A l)

  -- [ψ]A = [ψ']A  and  ⟨ψ⟩t = ⟨ψ'⟩t : [ψ]A  when ψ ⇔ ψ' is valid
  conv-GLam-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A t : Expr n}
    -> WfCtx G
    -> EquivC (lctx G) c c'
    -> IsType (addC G c) A
    -> HasType (addC G c) t A
    -> ConvTm G (GLam c A t) (GLam c' A t) (Grd c A)

  -- (⟨α⟩u) l = u(l/α)
  conv-LApp-beta : {n : Nat} {G : Ctx n} {A u : Expr n} {l : LExpr}
    -> IsType (addL G) A
    -> HasType (addL G) u A
    -> ConvTm G (LApp A (LLam A u) l) (lsub1 u l) (lsub1 A l)

  -- t = ⟨α⟩(t α)
  conv-LApp-eta : {n : Nat} {G : Ctx n} {A t : Expr n}
    -> IsType (addL G) A
    -> HasType G t (LPi A)
    -> ConvTm G t (LLam A (LApp (lsubE (liftL lwkS) A) (lshiftE t) (lvar zero))) (LPi A)

  -- guard η:  t = ⟨ψ⟩t : [ψ]A  (not in bcde.pdf Fig. 13; sound, since a
  -- term of type [ψ]A denotes ⊥ where ψ fails).  The typing of t in Γ,ψ
  -- is a presupposition carried as a premise (admissible:
  -- RussellMeta.mk-conv-GLam-eta).
  conv-GLam-eta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
    -> WfCtx G
    -> IsType (addC G c) A
    -> HasType G t (Grd c A)
    -> HasType (addC G c) t A
    -> ConvTm G t (GLam c A t) (Grd c A)

  -- collapse: in a context with a loop, t = ∅ : A   (bcde.pdf Fig. 14)
  conv-collapse : {n : Nat} {G : Ctx n} {t A : Expr n}
    -> Loop (lctx G)
    -> IsType G A
    -> HasType G t A
    -> ConvTm G t Emp A

  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
             {c : Expr n}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G c (Pi A B)
    -> ConvTm G c
       (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B)
                     (wkExpr c) (Var fzero)))
       (Pi A B)
