{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/TarskiSyntax.agda   (FROZEN shared module: edit only via coordinator)
--
-- Raw syntax of the Tarski-style Mahlo universe: Setzer's internal
-- Mahlo universe with RECURSIVE subuniverses and full decoding
-- (setzer1 Def. 3.5 (a)), in the conventions of MAHLO/Syntax.agda:
-- de Bruijn, non-curried constructors, families as Lam-terms (Lam is
-- the ONLY binder).  One sort Expr for types and terms, as in
-- ERT/TarskiSyntax.agda.
--
-- Types   V, T_V(a), U_{f,g}, T_{U,f,g}(a), Pi, Sigma, N.
-- Codes   in V        : Pi^_V, Sigma^_V, N^_V, U^_{f,g}, T^_{f,g}(a)
--         in U_{f,g}  : Pi^_U, Sigma^_U, N^_U, f^, g^.
-- Unlike the Russell syntax, App, Pair, Fst, Snd carry their type
-- annotations (A, F) -- free under erasure, and they make Tarski types
-- unique up to conversion (needed for uniqueness, ERT Lemma 4.10).
------------------------------------------------------------------------

module MAHLORT.TarskiSyntax where

open import MAHLO.Basic using (Eq ; refl ; Eq-sym ; Eq-trans ; Eq-cong)
open import MAHLO.Syntax public using (Num ; zero ; suc ; Fin ; fzero ; fsuc ;
  Ren ; liftRen ; wkRen ; cong2 ; cong4 ; cong5)

data Expr : Num -> Set where
  Var   : {n : Num} -> Fin n -> Expr n                                                -- de Bruijn variable
  Lam   : {n : Num} -> Expr n -> Expr (suc n) -> Expr n                               -- \x:A.t   (the only binder)
  App   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- app(A,F,c,a)  annotated, F = \x:A.B
  Pi    : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- Pi(A,F)   type
  Sigma : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- Sigma(A,F) type
  Pair  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- pair(A,F,a,b) annotated
  Fst   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n                           -- fst(A,F,t) annotated
  Snd   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n                           -- snd(A,F,t) annotated
  Nat   : {n : Num} -> Expr n                                                         -- N  type
  Zero  : {n : Num} -> Expr n                                                         -- 0
  Suc   : {n : Num} -> Expr n -> Expr n                                               -- S(t)
  Rec   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- rec(\x:N.C, z, s, k)
  V     : {n : Num} -> Expr n                                                         -- V  type (the Mahlo universe)
  ElV   : {n : Num} -> Expr n -> Expr n                                               -- T_V(a)  type
  TyU   : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- U_{f,g}  type (a subuniverse)
  ElU   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n                           -- T_{U,f,g}(a)  type
  PiV   : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- Pi^_V(a, F)   code in V
  SigV  : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- Sigma^_V(a, F) code in V
  NatV  : {n : Num} -> Expr n                                                         -- N^_V  code in V
  UV    : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- U^_{f,g}  code in V of U_{f,g}
  PiU   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- Pi^_U(f,g,a,F)  code in U_{f,g}
  SigU  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- Sigma^_U(f,g,a,F) code in U_{f,g}
  NatU  : {n : Num} -> Expr n -> Expr n -> Expr n                                     -- N^_U(f,g)  code in U_{f,g}
  Fhat  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n                 -- f^_{f,g}(a, F)  code in U_{f,g}
  Ghat  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n       -- g^_{f,g}(a, F, c)  code in U_{f,g}
  That  : {n : Num} -> Expr n -> Expr n                                               -- T^(a)  embedding of any U_{f,g} into V (unannotated)

------------------------------------------------------------------------
-- Renaming and substitution
------------------------------------------------------------------------

renExpr : {n m : Num} -> Ren n m -> Expr n -> Expr m
renExpr r (Var x0) = Var (r x0)
renExpr r (Lam x0 x1) = Lam (renExpr r x0) (renExpr (liftRen r) x1)
renExpr r (App x0 x1 x2 x3) = App (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r (Pi x0 x1) = Pi (renExpr r x0) (renExpr r x1)
renExpr r (Sigma x0 x1) = Sigma (renExpr r x0) (renExpr r x1)
renExpr r (Pair x0 x1 x2 x3) = Pair (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r (Fst x0 x1 x2) = Fst (renExpr r x0) (renExpr r x1) (renExpr r x2)
renExpr r (Snd x0 x1 x2) = Snd (renExpr r x0) (renExpr r x1) (renExpr r x2)
renExpr r Nat = Nat
renExpr r Zero = Zero
renExpr r (Suc x0) = Suc (renExpr r x0)
renExpr r (Rec x0 x1 x2 x3) = Rec (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r V = V
renExpr r (ElV x0) = ElV (renExpr r x0)
renExpr r (TyU x0 x1) = TyU (renExpr r x0) (renExpr r x1)
renExpr r (ElU x0 x1 x2) = ElU (renExpr r x0) (renExpr r x1) (renExpr r x2)
renExpr r (PiV x0 x1) = PiV (renExpr r x0) (renExpr r x1)
renExpr r (SigV x0 x1) = SigV (renExpr r x0) (renExpr r x1)
renExpr r NatV = NatV
renExpr r (UV x0 x1) = UV (renExpr r x0) (renExpr r x1)
renExpr r (PiU x0 x1 x2 x3) = PiU (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r (SigU x0 x1 x2 x3) = SigU (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r (NatU x0 x1) = NatU (renExpr r x0) (renExpr r x1)
renExpr r (Fhat x0 x1 x2 x3) = Fhat (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3)
renExpr r (Ghat x0 x1 x2 x3 x4) = Ghat (renExpr r x0) (renExpr r x1) (renExpr r x2) (renExpr r x3) (renExpr r x4)
renExpr r (That x0) = That (renExpr r x0)

wkExpr : {n : Num} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

Sub : Num -> Num -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Num} -> Sub h g -> Sub (suc h) (suc g)
liftSub s fzero    = Var fzero
liftSub s (fsuc i) = wkExpr (s i)

substExpr : {h g : Num} -> Sub h g -> Expr g -> Expr h
substExpr s (Var x0) = s x0
substExpr s (Lam x0 x1) = Lam (substExpr s x0) (substExpr (liftSub s) x1)
substExpr s (App x0 x1 x2 x3) = App (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s (Pi x0 x1) = Pi (substExpr s x0) (substExpr s x1)
substExpr s (Sigma x0 x1) = Sigma (substExpr s x0) (substExpr s x1)
substExpr s (Pair x0 x1 x2 x3) = Pair (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s (Fst x0 x1 x2) = Fst (substExpr s x0) (substExpr s x1) (substExpr s x2)
substExpr s (Snd x0 x1 x2) = Snd (substExpr s x0) (substExpr s x1) (substExpr s x2)
substExpr s Nat = Nat
substExpr s Zero = Zero
substExpr s (Suc x0) = Suc (substExpr s x0)
substExpr s (Rec x0 x1 x2 x3) = Rec (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s V = V
substExpr s (ElV x0) = ElV (substExpr s x0)
substExpr s (TyU x0 x1) = TyU (substExpr s x0) (substExpr s x1)
substExpr s (ElU x0 x1 x2) = ElU (substExpr s x0) (substExpr s x1) (substExpr s x2)
substExpr s (PiV x0 x1) = PiV (substExpr s x0) (substExpr s x1)
substExpr s (SigV x0 x1) = SigV (substExpr s x0) (substExpr s x1)
substExpr s NatV = NatV
substExpr s (UV x0 x1) = UV (substExpr s x0) (substExpr s x1)
substExpr s (PiU x0 x1 x2 x3) = PiU (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s (SigU x0 x1 x2 x3) = SigU (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s (NatU x0 x1) = NatU (substExpr s x0) (substExpr s x1)
substExpr s (Fhat x0 x1 x2 x3) = Fhat (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3)
substExpr s (Ghat x0 x1 x2 x3 x4) = Ghat (substExpr s x0) (substExpr s x1) (substExpr s x2) (substExpr s x3) (substExpr s x4)
substExpr s (That x0) = That (substExpr s x0)

subst1Sub : {n : Num} -> Expr n -> Sub n (suc n)
subst1Sub a fzero    = a
subst1Sub a (fsuc i) = Var i

subst1 : {n : Num} -> Expr (suc n) -> Expr n -> Expr n
subst1 B a = substExpr (subst1Sub a) B

------------------------------------------------------------------------
-- Derived formers
------------------------------------------------------------------------

x0 : {n : Num} -> Expr (suc n)
x0 = Var fzero

x1 : {n : Num} -> Expr (suc (suc n))
x1 = Var (fsuc fzero)

-- Pi x:A. B,  Sigma x:A. B,  A -> B
PiB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n
PiB A B = Pi A (Lam A B)

SigmaB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n
SigmaB A B = Sigma A (Lam A B)

Arr : {n : Num} -> Expr n -> Expr n -> Expr n
Arr A B = PiB A (wkExpr B)

-- annotated application / pairs at a family \x:A.B
appB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n -> Expr n -> Expr n
appB A B c a = App A (Lam A B) c a

-- the operator types  IOper(V, T_V)
--   f : Pi a:V. (T_V(a) -> V) -> V
--   g : Pi a:V. Pi F:(T_V(a) -> V). T_V(f a F) -> V
OpF : {n : Num} -> Expr n
OpF = PiB V (Arr (Arr (ElV x0) V) V)

-- f a F, with all annotations
fApp : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n
fApp f a F = appB (Arr (ElV a) V) (wkExpr V)
               (appB V (Arr (Arr (ElV x0) V) V) f a) F

OpG : {n : Num} -> Expr n -> Expr n
OpG f = PiB V (PiB (Arr (ElV x0) V)
          (Arr (ElV (fApp (wkExpr (wkExpr f)) x1 x0)) V))

-- g a F c, with all annotations
gApp : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n
gApp f g a F c =
  appB (ElV (fApp f a F)) (wkExpr V)
    (appB (Arr (ElV a) V) (Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V)
       (appB V (PiB (Arr (ElV x0) V) (Arr (ElV (fApp (wkExpr (wkExpr f)) x1 x0)) V)) g a) F) c

-- the step type of rec
sucSub : {n : Num} -> Sub (suc n) (suc n)
sucSub fzero    = Suc x0
sucSub (fsuc i) = Var (fsuc i)

RecStep : {n : Num} -> Expr (suc n) -> Expr n
RecStep C = PiB Nat (Arr C (substExpr sucSub C))

