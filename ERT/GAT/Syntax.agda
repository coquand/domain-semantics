{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.GAT.Syntax
--
-- Raw syntax of the Ehrhard-style GAT (sterbac4 §4), scoped:
--   GE n     types and terms over a context of length n (one family)
--   GS n m   substitutions from a context of length n to one of length m
--   GC n     contexts
-- Generators id, o, (), p, lift_A(s), sec_A(a); no context annotations
-- (U_l, U^m_l, id, (), p, q are bare).  Levels as in ERT's T_T:
-- guc m l : U_m and glf m l a : U_m for l < m.
-- Erasure (Definition 11) into ERT's T_T: eT, eS, eC.
------------------------------------------------------------------------

module ERT.GAT.Syntax where

open import ERT.Basic
import ERT.TarskiSyntax as T
import ERT.TarskiTyping as TT

data GE : Nat -> Set
data GS : Nat -> Nat -> Set

data GE where
  gpi  : {n : Nat} -> GE n -> GE (suc n) -> GE n
  guu  : {n : Nat} -> Nat -> GE n
  gel  : {n : Nat} -> Nat -> GE n -> GE n
  gsb  : {n m : Nat} -> GE m -> GS n m -> GE n
  glam : {n : Nat} -> GE n -> GE (suc n) -> GE (suc n) -> GE n
  gapp : {n : Nat} -> GE n -> GE (suc n) -> GE n -> GE n -> GE n
  gpic : {n : Nat} -> Nat -> GE n -> GE (suc n) -> GE n
  guc  : {n : Nat} -> Nat -> Nat -> GE n
  glf  : {n : Nat} -> Nat -> Nat -> GE n -> GE n
  gq   : {n : Nat} -> GE (suc n)

data GS where
  gid   : {n : Nat} -> GS n n
  gcomp : {n k m : Nat} -> GS k m -> GS n k -> GS n m
  geps  : {n : Nat} -> GS n zero
  gp    : {n : Nat} -> GS (suc n) n
  glift : {n m : Nat} -> GE m -> GS n m -> GS (suc n) (suc m)
  gsec  : {n : Nat} -> GE n -> GE n -> GS n (suc n)

data GC : Nat -> Set where
  gnil : GC zero
  gext : {n : Nat} -> GC n -> GE n -> GC (suc n)

------------------------------------------------------------------------
-- erasure

fin0 : {n : Nat} -> Fin zero -> T.Expr n
fin0 ()

eT : {n : Nat} -> GE n -> T.Expr n
eS : {n m : Nat} -> GS n m -> T.Sub n m

eT (gpi A B)      = T.Pi (eT A) (eT B)
eT (guu l)        = T.U l
eT (gel l a)      = T.El l (eT a)
eT (gsb t s)      = T.substExpr (eS s) (eT t)
eT (glam A B b)   = T.Lam (eT A) (eT B) (eT b)
eT (gapp A B c a) = T.App (eT A) (eT B) (eT c) (eT a)
eT (gpic l a b)   = T.PiCode l (eT a) (eT b)
eT (guc m l)      = T.UCode m l
eT (glf m l a)    = T.Lift m l (eT a)
eT gq             = T.Var fzero

eS gid          = \ i -> T.Var i
eS (gcomp s d)  = \ i -> T.substExpr (eS d) (eS s i)
eS geps         = fin0
eS gp           = \ i -> T.Var (fsuc i)
eS (glift A s)  = T.liftSub (eS s)
eS (gsec A a)   = T.subst1Sub (eT a)

eC : {n : Nat} -> GC n -> TT.Ctx n
eC gnil       = TT.empty
eC (gext G A) = TT.extend (eC G) (eT A)
