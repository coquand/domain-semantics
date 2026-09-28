{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.PTyping
--
-- The unannotated Russell theory T_P: bcde.pdf's Russell presentation
-- (App. B, Fig. 12–14) without the annotations of Remark 2.  Its syntax
-- is the core syntax of the model (BCDE4.Model.Core):
--
--   A, B, a, b ::= v_i | Π A B | U_l | λ A b | c a
--                | [ψ]A | ⟨ψ⟩t | ∅ | [α]A | ⟨α⟩u | t l
--
-- i.e. λ keeps its domain, and application, ⟨ψ⟩, ⟨α⟩ and level
-- application keep nothing; BCDE4.Model.Strip.strip : T_R -> T_P
-- forgets the annotations.
--
-- The rules are those of T_R (BCDE4.RussellTyping) with the annotations
-- removed (the annotation congruences of app, ⟨ψ⟩, ⟨α⟩ and t l become
-- reflexivity; the one of λ keeps its domain part).  As in T_R the
-- binder rules carry their presuppositions as premises (ERT.PTyping);
-- this keeps the section of strip (Thm 4.19) structural.  Guard η is
-- included, as in T_R.
------------------------------------------------------------------------

module BCDE4.PTyping where

open import BCDE4.Basic using (Nat ; zero ; suc ; Fin ; fzero ; fsuc ; liftRen ; wkRen ; Eq ; refl ; Eq-cong)
open import BCDE4.Levels
open import BCDE4.Model.Core

------------------------------------------------------------------------
-- Context operations
------------------------------------------------------------------------

addC : {n : Nat} -> Ctx n -> Constr -> Ctx n
addC (empty Th)   c = empty (lcons c Th)
addC (extend G A) c = extend (addC G c) A

addL : {n : Nat} -> Ctx n -> Ctx n
addL (empty Th)   = empty (lsubTh lwkS Th)
addL (extend G A) = extend (addL G) (lshiftE A)

lctx-addC : {n : Nat} (G : Ctx n) (c : Constr) -> Eq (lctx (addC G c)) (lcons c (lctx G))
lctx-addC (empty Th)   c = refl
lctx-addC (extend G A) c = lctx-addC G c

lctx-addL : {n : Nat} (G : Ctx n) -> Eq (lctx (addL G)) (lsubTh lwkS (lctx G))
lctx-addL (empty Th)   = refl
lctx-addL (extend G A) = lctx-addL G

------------------------------------------------------------------------
-- Judgements
------------------------------------------------------------------------

data WfCtx   : {n : Nat} -> Ctx n -> Set
data IsType  : {n : Nat} -> Ctx n -> Expr n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTy  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtx where
  wf-empty  : {Th : LCtx} -> WfCtx (empty Th)
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx (extend G A)

data IsType where
  is-Ty-from-U : {n : Nat} {G : Ctx n} {A : Expr n} {l : LExpr} ->
    HasType G A (U l) -> IsType G A
  is-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> IsType G (Pi A B)
  is-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n} ->
    WfCtx G -> IsType (addC G c) A -> IsType G (Grd c A)
  is-LPi : {n : Nat} {G : Ctx n} {A : Expr n} ->
    WfCtx G -> IsType (addL G) A -> IsType G (LPi A)

data HasType where
  ty-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n} ->
    WfCtx G -> IsType (addC G c) A -> HasType (addC G c) t A -> HasType G (GLam c t) (Grd c A)
  ty-LLam : {n : Nat} {G : Ctx n} {A u : Expr n} ->
    WfCtx G -> IsType (addL G) A -> HasType (addL G) u A -> HasType G (LLam u) (LPi A)
  ty-LApp : {n : Nat} {G : Ctx n} {A t : Expr n} {l : LExpr} ->
    IsType (addL G) A -> HasType G t (LPi A) -> HasType G (LApp t l) (lsub1 A l)
  ty-Emp : {n : Nat} {G : Ctx n} {l : LExpr} ->
    WfCtx G -> HasType G Emp (U l)
  ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n} ->
    Loop (lctx G) -> IsType G A -> HasType G Emp A
  ty-var : {n : Nat} {G : Ctx n} {i : Fin n} ->
    WfCtx G -> HasType G (Var i) (lookup G i)
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n} ->
    HasType G M A -> ConvTy G A B -> HasType G M B
  ty-U : {n : Nat} {G : Ctx n} {l m : LExpr} ->
    WfCtx G -> LtL (lctx G) l m -> HasType G (U l) (U m)
  ty-cum : {n : Nat} {G : Ctx n} {A : Expr n} {l m : LExpr} ->
    HasType G A (U l) -> LeL (lctx G) l m -> HasType G A (U m)
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {l : LExpr} ->
    HasType G A (U l) -> HasType (extend G A) B (U l) -> HasType G (Pi A B) (U l)
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B ->
    HasType (extend G A) b B -> HasType G (Lam A b) (Pi A B)
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a : Expr n} ->
    IsType G A -> IsType (extend G A) B ->
    HasType G c (Pi A B) -> HasType G a A -> HasType G (App c a) (subst1 B a)

data ConvTy where
  conv-Ty-refl : {n : Nat} {G : Ctx n} {A : Expr n} ->
    IsType G A -> ConvTy G A A
  conv-Ty-sym : {n : Nat} {G : Ctx n} {A B : Expr n} ->
    ConvTy G A B -> ConvTy G B A
  conv-Ty-trans : {n : Nat} {G : Ctx n} {A B C : Expr n} ->
    ConvTy G A B -> ConvTy G B C -> ConvTy G A C
  conv-Ty-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' ->
    ConvTy G (Pi A B) (Pi A' B')
  conv-Ty-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A B : Expr n} ->
    WfCtx G -> IsType (addC G c) A -> ConvTy (addC G c) A B -> ConvTy G (Grd c A) (Grd c B)
  conv-Ty-LPi : {n : Nat} {G : Ctx n} {A B : Expr n} ->
    WfCtx G -> IsType (addL G) A -> ConvTy (addL G) A B -> ConvTy G (LPi A) (LPi B)
  conv-Ty-Grd-beta : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n} ->
    ValidC (lctx G) c -> IsType G A -> ConvTy G (Grd c A) A
  conv-Ty-Grd-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A : Expr n} ->
    WfCtx G -> EquivC (lctx G) c c' -> IsType (addC G c) A -> ConvTy G (Grd c A) (Grd c' A)
  conv-Ty-collapse : {n : Nat} {G : Ctx n} {A : Expr n} ->
    Loop (lctx G) -> IsType G A -> ConvTy G A Emp
  conv-Ty-from-U : {n : Nat} {G : Ctx n} {A B : Expr n} {l : LExpr} ->
    ConvTm G A B (U l) -> ConvTy G A B

data ConvTm where
  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n} ->
    HasType G M A -> ConvTm G M M A
  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A -> ConvTm G N M A
  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n} ->
    ConvTm G M N A -> ConvTm G N P A -> ConvTm G M P A
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n} ->
    ConvTm G M N A -> ConvTy G A B -> ConvTm G M N B
  conv-cong-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} {l : LExpr} ->
    HasType G A (U l) -> HasType (extend G A) B (U l) -> ConvTm G A A' (U l) -> ConvTm (extend G A) B B' (U l) ->
    ConvTm G (Pi A B) (Pi A' B') (U l)
  conv-cum : {n : Nat} {G : Ctx n} {A B : Expr n} {l m : LExpr} ->
    ConvTm G A B (U l) -> LeL (lctx G) l m -> ConvTm G A B (U m)
  conv-U-lvl : {n : Nat} {G : Ctx n} {l l' m : LExpr} ->
    WfCtx G -> Valid (lctx G) l l' -> LtL (lctx G) l m -> ConvTm G (U l) (U l') (U m)
  conv-cong-Lam-body : {n : Nat} {G : Ctx n} {A : Expr n} {B b b' : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
    ConvTm (extend G A) b b' B -> ConvTm G (Lam A b) (Lam A b') (Pi A B)
  conv-cong-Lam-dom : {n : Nat} {G : Ctx n} {A A' : Expr n} {B b : Expr (suc n)} ->
    IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> HasType (extend G A) b B ->
    ConvTm G (Lam A b) (Lam A' b) (Pi A B)
  conv-cong-App-fun : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c c' a : Expr n} ->
    IsType G A -> IsType (extend G A) B -> ConvTm G c c' (Pi A B) -> HasType G a A ->
    ConvTm G (App c a) (App c' a) (subst1 B a)
  conv-cong-App-arg : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a a' : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) -> ConvTm G a a' A ->
    ConvTy G (subst1 B a) (subst1 B a') ->
    ConvTm G (App c a) (App c a') (subst1 B a)
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {a : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B -> HasType G a A ->
    ConvTm G (App (Lam A b) a) (subst1 b a) (subst1 B a)
  conv-cong-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t t' : Expr n} ->
    WfCtx G -> IsType (addC G c) A -> HasType (addC G c) t A -> ConvTm (addC G c) t t' A ->
    ConvTm G (GLam c t) (GLam c t') (Grd c A)
  conv-GLam-beta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n} ->
    ValidC (lctx G) c -> IsType G A -> HasType G t A -> ConvTm G (GLam c t) t A
  conv-cong-LLam : {n : Nat} {G : Ctx n} {A u u' : Expr n} ->
    WfCtx G -> IsType (addL G) A -> HasType (addL G) u A -> ConvTm (addL G) u u' A ->
    ConvTm G (LLam u) (LLam u') (LPi A)
  conv-cong-LApp-fun : {n : Nat} {G : Ctx n} {A t t' : Expr n} {l : LExpr} ->
    IsType (addL G) A -> ConvTm G t t' (LPi A) -> ConvTm G (LApp t l) (LApp t' l) (lsub1 A l)
  conv-cong-LApp-lvl : {n : Nat} {G : Ctx n} {A t : Expr n} {l l' : LExpr} ->
    IsType (addL G) A -> HasType G t (LPi A) -> Valid (lctx G) l l' ->
    ConvTy G (lsub1 A l) (lsub1 A l') -> ConvTm G (LApp t l) (LApp t l') (lsub1 A l)
  conv-GLam-equiv : {n : Nat} {G : Ctx n} {c c' : Constr} {A t : Expr n} ->
    WfCtx G -> EquivC (lctx G) c c' -> IsType (addC G c) A -> HasType (addC G c) t A ->
    ConvTm G (GLam c t) (GLam c' t) (Grd c A)
  conv-LApp-beta : {n : Nat} {G : Ctx n} {A u : Expr n} {l : LExpr} ->
    IsType (addL G) A -> HasType (addL G) u A -> ConvTm G (LApp (LLam u) l) (lsub1 u l) (lsub1 A l)
  conv-LApp-eta : {n : Nat} {G : Ctx n} {A t : Expr n} ->
    IsType (addL G) A -> HasType G t (LPi A) ->
    ConvTm G t (LLam (LApp (lshiftE t) (lvar zero))) (LPi A)
  conv-GLam-eta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n} ->
    WfCtx G -> IsType (addC G c) A -> HasType G t (Grd c A) -> HasType (addC G c) t A ->
    ConvTm G t (GLam c t) (Grd c A)
  conv-collapse : {n : Nat} {G : Ctx n} {t A : Expr n} ->
    Loop (lctx G) -> IsType G A -> HasType G t A -> ConvTm G t Emp A
  conv-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c : Expr n} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) ->
    ConvTm G c (Lam A (App (wkExpr c) (Var fzero))) (Pi A B)
