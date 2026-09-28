{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiSyntax
--
-- Raw syntax for the Tarski-style theory T_T with internal levels and
-- cumulativity (bcde.pdf §4, App. A), extending the Russell syntax
-- (BCDE4.RussellSyntax) by
--
--   El_l a      decoding of a code a : U_l
--   Π^l a b     code of Π(El_l a, El_l b) in U_l   (binds one variable in b)
--   U^m_l       code of U_l in U_m                  (l < m)
--   ↑^m_l a     lift of a code a : U_l into U_m     (l ⩽ m)
--   ∅^l         code of ∅ in U_l
--
-- Types and terms share one sort; erasure (BCDE4.Erasure) forgets El,
-- the lifts and the code constructors.
--
-- de Bruijn variables. Renaming, parallel substitution, structural
-- lemmas (ren-ren, ren-subst, subst-ren, subst-subst). No postulates.
------------------------------------------------------------------------

module BCDE4.TarskiSyntax where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.Basic public using (Fin ; fzero ; fsuc ; Ren ; wkRen ; liftRen ; Eq-trans)

------------------------------------------------------------------------
-- Expr
------------------------------------------------------------------------

data Expr : Nat -> Set where
  Var : {n : Nat} -> Fin n -> Expr n
  U   : {n : Nat} -> LExpr -> Expr n                            -- U_l
  Pi  : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n           -- Π(A,B)
  Lam : {n : Nat} -> Expr n -> Expr (suc n) -> Expr (suc n) -> Expr n
                                                                -- λ(A,B,b)
  App : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n -> Expr n -> Expr n
                                                                -- app(A,B,c,a)
  Grd  : {n : Nat} -> Constr -> Expr n -> Expr n                -- [ψ]A
  GLam : {n : Nat} -> Constr -> Expr n -> Expr n -> Expr n       -- ⟨ψ⟩t, annotated [ψ]A
  Emp  : {n : Nat} -> Expr n                                    -- ∅
  LPi  : {n : Nat} -> Expr n -> Expr n                -- [α]A   (binds level 0)
  LLam : {n : Nat} -> Expr n -> Expr n -> Expr n      -- ⟨α⟩u : [α]A, annotated A   (binds level 0)
  LApp : {n : Nat} -> Expr n -> Expr n -> LExpr -> Expr n  -- t l, annotated [α]A
  El      : {n : Nat} -> LExpr -> Expr n -> Expr n              -- El_l a
  PiCode  : {n : Nat} -> LExpr -> Expr n -> Expr (suc n) -> Expr n  -- Π^l a b
  UCode   : {n : Nat} -> LExpr -> LExpr -> Expr n               -- U^m_l
  Lift    : {n : Nat} -> LExpr -> LExpr -> Expr n -> Expr n     -- ↑^m_l a
  EmpCode : {n : Nat} -> LExpr -> Expr n                        -- ∅^l

------------------------------------------------------------------------
-- Renamings (Ren / liftRen / wkRen are shared in BCDE4.Basic)
------------------------------------------------------------------------

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)         = Var (r i)
renExpr r (U l)         = U l
renExpr r (El l a)      = El l (renExpr r a)
renExpr r (PiCode l a b) = PiCode l (renExpr r a) (renExpr (liftRen r) b)
renExpr r (UCode m l)   = UCode m l
renExpr r (Lift m l a)  = Lift m l (renExpr r a)
renExpr r (EmpCode l)   = EmpCode l
renExpr r (Grd c A)     = Grd c (renExpr r A)
renExpr r (GLam c A t)  = GLam c (renExpr r A) (renExpr r t)
renExpr r Emp           = Emp
renExpr r (LPi A)       = LPi (renExpr r A)
renExpr r (LLam A u)    = LLam (renExpr r A) (renExpr r u)
renExpr r (LApp A t l)  = LApp (renExpr r A) (renExpr r t) l
renExpr r (Pi A B)        = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A B b)     = Lam (renExpr r A) (renExpr (liftRen r) B)
                                (renExpr (liftRen r) b)
renExpr r (App A B c a)   = App (renExpr r A) (renExpr (liftRen r) B)
                                (renExpr r c) (renExpr r a)

wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

------------------------------------------------------------------------
-- Level substitution
------------------------------------------------------------------------

lsubE : {n : Nat} -> LSub -> Expr n -> Expr n
lsubE z (Var i)       = Var i
lsubE z (U l)         = U (lsubL z l)
lsubE z (El l a)      = El (lsubL z l) (lsubE z a)
lsubE z (PiCode l a b) = PiCode (lsubL z l) (lsubE z a) (lsubE z b)
lsubE z (UCode m l)   = UCode (lsubL z m) (lsubL z l)
lsubE z (Lift m l a)  = Lift (lsubL z m) (lsubL z l) (lsubE z a)
lsubE z (EmpCode l)   = EmpCode (lsubL z l)
lsubE z (Pi A B)      = Pi (lsubE z A) (lsubE z B)
lsubE z (Lam A B b)   = Lam (lsubE z A) (lsubE z B) (lsubE z b)
lsubE z (App A B c a) = App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a)
lsubE z (Grd c A)     = Grd (lsubC z c) (lsubE z A)
lsubE z (GLam c A t)  = GLam (lsubC z c) (lsubE z A) (lsubE z t)
lsubE z Emp           = Emp
lsubE z (LPi A)       = LPi (lsubE (liftL z) A)
lsubE z (LLam A u)    = LLam (lsubE (liftL z) A) (lsubE (liftL z) u)
lsubE z (LApp A t l)  = LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l)

lshiftE : {n : Nat} -> Expr n -> Expr n
lshiftE = lsubE lwkS

-- instantiation of the bound level
lsub1 : {n : Nat} -> Expr n -> LExpr -> Expr n
lsub1 A l = lsubE (lsub1S l) A

------------------------------------------------------------------------
-- Parallel substitution
------------------------------------------------------------------------

Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub sigma fzero    = Var fzero
liftSub sigma (fsuc i) = wkExpr (sigma i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr sigma (Var i)       = sigma i
substExpr sigma (U l)       = U l
substExpr sigma (El l a)    = El l (substExpr sigma a)
substExpr sigma (PiCode l a b) = PiCode l (substExpr sigma a) (substExpr (liftSub sigma) b)
substExpr sigma (UCode m l) = UCode m l
substExpr sigma (Lift m l a) = Lift m l (substExpr sigma a)
substExpr sigma (EmpCode l) = EmpCode l
substExpr sigma (Grd c A)   = Grd c (substExpr sigma A)
substExpr sigma (GLam c A t) = GLam c (substExpr sigma A) (substExpr sigma t)
substExpr sigma Emp         = Emp
substExpr sigma (LPi A)     = LPi (substExpr (\ i -> lshiftE (sigma i)) A)
substExpr sigma (LLam A u)  = LLam (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr (\ i -> lshiftE (sigma i)) u)
substExpr sigma (LApp A t l) = LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l
substExpr sigma (Pi A B)      = Pi (substExpr sigma A)
                                   (substExpr (liftSub sigma) B)
substExpr sigma (Lam A B b)   = Lam (substExpr sigma A)
                                    (substExpr (liftSub sigma) B)
                                    (substExpr (liftSub sigma) b)
substExpr sigma (App A B c a) = App (substExpr sigma A)
                                    (substExpr (liftSub sigma) B)
                                    (substExpr sigma c)
                                    (substExpr sigma a)

------------------------------------------------------------------------
-- Single substitution
------------------------------------------------------------------------

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub s fzero    = s
subst1Sub s (fsuc i) = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 M s = substExpr (subst1Sub s) M

------------------------------------------------------------------------
-- Pointwise extensionality
------------------------------------------------------------------------

liftRen-ext : {n m : Nat} (r1 r2 : Ren n m)
  -> ((i : Fin n) -> Eq (r1 i) (r2 i))
  -> (j : Fin (suc n)) -> Eq (liftRen r1 j) (liftRen r2 j)
liftRen-ext r1 r2 ext fzero    = refl
liftRen-ext r1 r2 ext (fsuc i) = Eq-cong fsuc (ext i)

renExpr-ext : {n m : Nat} (r1 r2 : Ren n m)
  -> ((i : Fin n) -> Eq (r1 i) (r2 i))
  -> (e : Expr n) -> Eq (renExpr r1 e) (renExpr r2 e)
renExpr-ext r1 r2 ext (Var i)       = Eq-cong Var (ext i)
renExpr-ext r1 r2 ext (U l)       = refl
renExpr-ext r1 r2 ext (El l a)   = Eq-cong (El l) (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (PiCode l a b) =
  Eq-cong2 (PiCode l) (renExpr-ext r1 r2 ext a)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 ext) b)
renExpr-ext r1 r2 ext (UCode m l) = refl
renExpr-ext r1 r2 ext (Lift m l a) = Eq-cong (Lift m l) (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (EmpCode l) = refl
renExpr-ext r1 r2 ext (Grd c A)  = Eq-cong (Grd c) (renExpr-ext r1 r2 ext A)
renExpr-ext r1 r2 ext (GLam c A t) = Eq-cong2 (GLam c) (renExpr-ext r1 r2 ext A) (renExpr-ext r1 r2 ext t)
renExpr-ext r1 r2 ext Emp        = refl
renExpr-ext r1 r2 ext (LPi A)  = Eq-cong LPi (renExpr-ext r1 r2 ext A)
renExpr-ext r1 r2 ext (LLam A u) = Eq-cong2 LLam (renExpr-ext r1 r2 ext A) (renExpr-ext r1 r2 ext u)
renExpr-ext r1 r2 ext (LApp A t l) = Eq-cong2 (\ X Y -> LApp X Y l) (renExpr-ext r1 r2 ext A) (renExpr-ext r1 r2 ext t)
renExpr-ext r1 r2 ext (Pi A B)      =
  Eq-cong2 Pi (renExpr-ext r1 r2 ext A)
              (renExpr-ext (liftRen r1) (liftRen r2)
                           (liftRen-ext r1 r2 ext) B)
renExpr-ext r1 r2 ext (Lam A B b)   =
  Eq-cong3 Lam (renExpr-ext r1 r2 ext A)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) B)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) b)
renExpr-ext r1 r2 ext (App A B c a) =
  Eq-cong4 App (renExpr-ext r1 r2 ext A)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) B)
               (renExpr-ext r1 r2 ext c)
               (renExpr-ext r1 r2 ext a)

liftSub-ext : {h g : Nat} (s1 s2 : Sub h g)
  -> ((i : Fin g) -> Eq (s1 i) (s2 i))
  -> (j : Fin (suc g)) -> Eq (liftSub s1 j) (liftSub s2 j)
liftSub-ext s1 s2 ext fzero    = refl
liftSub-ext s1 s2 ext (fsuc i) = Eq-cong wkExpr (ext i)

substExpr-ext : {h g : Nat} (s1 s2 : Sub h g)
  -> ((i : Fin g) -> Eq (s1 i) (s2 i))
  -> (e : Expr g) -> Eq (substExpr s1 e) (substExpr s2 e)
substExpr-ext s1 s2 ext (Var i)       = ext i
substExpr-ext s1 s2 ext (U l)       = refl
substExpr-ext s1 s2 ext (El l a)   = Eq-cong (El l) (substExpr-ext s1 s2 ext a)
substExpr-ext s1 s2 ext (PiCode l a b) =
  Eq-cong2 (PiCode l) (substExpr-ext s1 s2 ext a)
    (substExpr-ext (liftSub s1) (liftSub s2) (liftSub-ext s1 s2 ext) b)
substExpr-ext s1 s2 ext (UCode m l) = refl
substExpr-ext s1 s2 ext (Lift m l a) = Eq-cong (Lift m l) (substExpr-ext s1 s2 ext a)
substExpr-ext s1 s2 ext (EmpCode l) = refl
substExpr-ext s1 s2 ext (Grd c A)  = Eq-cong (Grd c) (substExpr-ext s1 s2 ext A)
substExpr-ext s1 s2 ext (GLam c A t) = Eq-cong2 (GLam c) (substExpr-ext s1 s2 ext A) (substExpr-ext s1 s2 ext t)
substExpr-ext s1 s2 ext Emp        = refl
substExpr-ext s1 s2 ext (LPi A)  =
  Eq-cong LPi (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) A)
substExpr-ext s1 s2 ext (LLam A u) =
  Eq-cong2 LLam (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) A)
    (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) u)
substExpr-ext s1 s2 ext (LApp A t l) = Eq-cong2 (\ X Y -> LApp X Y l) (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) A) (substExpr-ext s1 s2 ext t)
substExpr-ext s1 s2 ext (Pi A B)      =
  Eq-cong2 Pi (substExpr-ext s1 s2 ext A)
              (substExpr-ext (liftSub s1) (liftSub s2)
                             (liftSub-ext s1 s2 ext) B)
substExpr-ext s1 s2 ext (Lam A B b)   =
  Eq-cong3 Lam (substExpr-ext s1 s2 ext A)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) B)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) b)
substExpr-ext s1 s2 ext (App A B c a) =
  Eq-cong4 App (substExpr-ext s1 s2 ext A)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) B)
               (substExpr-ext s1 s2 ext c)
               (substExpr-ext s1 s2 ext a)

------------------------------------------------------------------------
-- Level substitution: laws
------------------------------------------------------------------------

liftL-ext : (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (i : Nat) -> Eq (liftL z i) (liftL z' i)
liftL-ext z z' e zero    = refl
liftL-ext z z' e (suc i) = Eq-cong lshift (e i)

lsubE-ext : {n : Nat} (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (M : Expr n) ->
  Eq (lsubE z M) (lsubE z' M)
lsubE-ext z z' e (Var i)       = refl
lsubE-ext z z' e (U l)         = Eq-cong U (lsubL-ext z z' e l)
lsubE-ext z z' e (El l a)      = Eq-cong2 El (lsubL-ext z z' e l) (lsubE-ext z z' e a)
lsubE-ext z z' e (PiCode l a b) = Eq-cong3 PiCode (lsubL-ext z z' e l) (lsubE-ext z z' e a) (lsubE-ext z z' e b)
lsubE-ext z z' e (UCode m l)   = Eq-cong2 UCode (lsubL-ext z z' e m) (lsubL-ext z z' e l)
lsubE-ext z z' e (Lift m l a)  = Eq-cong3 Lift (lsubL-ext z z' e m) (lsubL-ext z z' e l) (lsubE-ext z z' e a)
lsubE-ext z z' e (EmpCode l)   = Eq-cong EmpCode (lsubL-ext z z' e l)
lsubE-ext z z' e (Pi A B)      = Eq-cong2 Pi (lsubE-ext z z' e A) (lsubE-ext z z' e B)
lsubE-ext z z' e (Lam A B b)   = Eq-cong3 Lam (lsubE-ext z z' e A) (lsubE-ext z z' e B) (lsubE-ext z z' e b)
lsubE-ext z z' e (App A B c a) =
  Eq-cong4 App (lsubE-ext z z' e A) (lsubE-ext z z' e B) (lsubE-ext z z' e c) (lsubE-ext z z' e a)
lsubE-ext z z' e (Grd c A)     = Eq-cong2 Grd (lsubC-ext z z' e c) (lsubE-ext z z' e A)
lsubE-ext z z' e (GLam c A t)  = Eq-cong3 GLam (lsubC-ext z z' e c) (lsubE-ext z z' e A) (lsubE-ext z z' e t)
lsubE-ext z z' e Emp           = refl
lsubE-ext z z' e (LPi A)       = Eq-cong LPi (lsubE-ext _ _ (liftL-ext z z' e) A)
lsubE-ext z z' e (LLam A u)    = Eq-cong2 LLam (lsubE-ext _ _ (liftL-ext z z' e) A) (lsubE-ext _ _ (liftL-ext z z' e) u)
lsubE-ext z z' e (LApp A t l)  = Eq-cong3 LApp (lsubE-ext _ _ (liftL-ext z z' e) A) (lsubE-ext z z' e t) (lsubL-ext z z' e l)

liftL-comp : (z2 z1 : LSub) (i : Nat) -> Eq (lcomp (liftL z2) (liftL z1) i) (liftL (lcomp z2 z1) i)
liftL-comp z2 z1 zero    = refl
liftL-comp z2 z1 (suc i) = liftL-shift z2 (z1 i)

lsubE-comp : {n : Nat} (z2 z1 : LSub) (M : Expr n) -> Eq (lsubE z2 (lsubE z1 M)) (lsubE (lcomp z2 z1) M)
lsubE-comp z2 z1 (Var i)       = refl
lsubE-comp z2 z1 (U l)         = Eq-cong U (lsubL-comp z2 z1 l)
lsubE-comp z2 z1 (El l a)      = Eq-cong2 El (lsubL-comp z2 z1 l) (lsubE-comp z2 z1 a)
lsubE-comp z2 z1 (PiCode l a b) = Eq-cong3 PiCode (lsubL-comp z2 z1 l) (lsubE-comp z2 z1 a) (lsubE-comp z2 z1 b)
lsubE-comp z2 z1 (UCode m l)   = Eq-cong2 UCode (lsubL-comp z2 z1 m) (lsubL-comp z2 z1 l)
lsubE-comp z2 z1 (Lift m l a)  = Eq-cong3 Lift (lsubL-comp z2 z1 m) (lsubL-comp z2 z1 l) (lsubE-comp z2 z1 a)
lsubE-comp z2 z1 (EmpCode l)   = Eq-cong EmpCode (lsubL-comp z2 z1 l)
lsubE-comp z2 z1 (Pi A B)      = Eq-cong2 Pi (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 B)
lsubE-comp z2 z1 (Lam A B b)   = Eq-cong3 Lam (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 B) (lsubE-comp z2 z1 b)
lsubE-comp z2 z1 (App A B c a) =
  Eq-cong4 App (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 B) (lsubE-comp z2 z1 c) (lsubE-comp z2 z1 a)
lsubE-comp z2 z1 (Grd c A)     = Eq-cong2 Grd (lsubC-comp z2 z1 c) (lsubE-comp z2 z1 A)
lsubE-comp z2 z1 (GLam c A t)  = Eq-cong3 GLam (lsubC-comp z2 z1 c) (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 t)
lsubE-comp z2 z1 Emp           = refl
lsubE-comp z2 z1 (LPi A)       =
  Eq-cong LPi (Eq-trans (lsubE-comp _ _ A) (lsubE-ext _ _ (liftL-comp z2 z1) A))
lsubE-comp z2 z1 (LLam A u)    =
  Eq-cong2 LLam (Eq-trans (lsubE-comp _ _ A) (lsubE-ext _ _ (liftL-comp z2 z1) A))
    (Eq-trans (lsubE-comp _ _ u) (lsubE-ext _ _ (liftL-comp z2 z1) u))
lsubE-comp z2 z1 (LApp A t l)  = Eq-cong3 LApp (Eq-trans (lsubE-comp _ _ A) (lsubE-ext _ _ (liftL-comp z2 z1) A)) (lsubE-comp z2 z1 t) (lsubL-comp z2 z1 l)

liftL-id : (i : Nat) -> Eq (liftL lidS i) (lidS i)
liftL-id zero    = refl
liftL-id (suc i) = refl

lsubE-id : {n : Nat} (M : Expr n) -> Eq (lsubE lidS M) M
lsubE-id (Var i)       = refl
lsubE-id (U l)         = Eq-cong U (lsubL-id l)
lsubE-id (El l a)      = Eq-cong2 El (lsubL-id l) (lsubE-id a)
lsubE-id (PiCode l a b) = Eq-cong3 PiCode (lsubL-id l) (lsubE-id a) (lsubE-id b)
lsubE-id (UCode m l)   = Eq-cong2 UCode (lsubL-id m) (lsubL-id l)
lsubE-id (Lift m l a)  = Eq-cong3 Lift (lsubL-id m) (lsubL-id l) (lsubE-id a)
lsubE-id (EmpCode l)   = Eq-cong EmpCode (lsubL-id l)
lsubE-id (Pi A B)      = Eq-cong2 Pi (lsubE-id A) (lsubE-id B)
lsubE-id (Lam A B b)   = Eq-cong3 Lam (lsubE-id A) (lsubE-id B) (lsubE-id b)
lsubE-id (App A B c a) = Eq-cong4 App (lsubE-id A) (lsubE-id B) (lsubE-id c) (lsubE-id a)
lsubE-id (Grd c A)     = Eq-cong2 Grd (lsubC-id c) (lsubE-id A)
lsubE-id (GLam c A t)  = Eq-cong3 GLam (lsubC-id c) (lsubE-id A) (lsubE-id t)
lsubE-id Emp           = refl
lsubE-id (LPi A)       = Eq-cong LPi (Eq-trans (lsubE-ext _ _ liftL-id A) (lsubE-id A))
lsubE-id (LLam A u)    = Eq-cong2 LLam (Eq-trans (lsubE-ext _ _ liftL-id A) (lsubE-id A)) (Eq-trans (lsubE-ext _ _ liftL-id u) (lsubE-id u))
lsubE-id (LApp A t l)  = Eq-cong3 LApp (Eq-trans (lsubE-ext _ _ liftL-id A) (lsubE-id A)) (lsubE-id t) (lsubL-id l)

-- level substitution commutes with renaming
lsubE-ren : {n m : Nat} (z : LSub) (r : Ren n m) (M : Expr n) ->
  Eq (lsubE z (renExpr r M)) (renExpr r (lsubE z M))
lsubE-ren z r (Var i)       = refl
lsubE-ren z r (U l)         = refl
lsubE-ren z r (El l a)      = Eq-cong (El (lsubL z l)) (lsubE-ren z r a)
lsubE-ren z r (PiCode l a b) = Eq-cong2 (PiCode (lsubL z l)) (lsubE-ren z r a) (lsubE-ren z (liftRen r) b)
lsubE-ren z r (UCode m l)   = refl
lsubE-ren z r (Lift m l a)  = Eq-cong (Lift (lsubL z m) (lsubL z l)) (lsubE-ren z r a)
lsubE-ren z r (EmpCode l)   = refl
lsubE-ren z r (Pi A B)      = Eq-cong2 Pi (lsubE-ren z r A) (lsubE-ren z (liftRen r) B)
lsubE-ren z r (Lam A B b)   =
  Eq-cong3 Lam (lsubE-ren z r A) (lsubE-ren z (liftRen r) B) (lsubE-ren z (liftRen r) b)
lsubE-ren z r (App A B c a) =
  Eq-cong4 App (lsubE-ren z r A) (lsubE-ren z (liftRen r) B) (lsubE-ren z r c) (lsubE-ren z r a)
lsubE-ren z r (Grd c A)     = Eq-cong (Grd (lsubC z c)) (lsubE-ren z r A)
lsubE-ren z r (GLam c A t)  = Eq-cong2 (GLam (lsubC z c)) (lsubE-ren z r A) (lsubE-ren z r t)
lsubE-ren z r Emp           = refl
lsubE-ren z r (LPi A)       = Eq-cong LPi (lsubE-ren (liftL z) r A)
lsubE-ren z r (LLam A u)    = Eq-cong2 LLam (lsubE-ren (liftL z) r A) (lsubE-ren (liftL z) r u)
lsubE-ren z r (LApp A t l)  = Eq-cong2 (\ X Y -> LApp X Y (lsubL z l)) (lsubE-ren (liftL z) r A) (lsubE-ren z r t)

-- lifting past a level binder commutes with the shift
lsubE-liftL-shift : {n : Nat} (z : LSub) (M : Expr n) ->
  Eq (lsubE (liftL z) (lshiftE M)) (lshiftE (lsubE z M))
lsubE-liftL-shift z M = Eq-trans (lsubE-comp (liftL z) lwkS M) (Eq-sym (lsubE-comp lwkS z M))

-- the same, one level binder further in (for the η-expansion's annotation)
lsubE-liftL2-shift : {n : Nat} (z : LSub) (M : Expr n) ->
  Eq (lsubE (liftL (liftL z)) (lsubE (liftL lwkS) M)) (lsubE (liftL lwkS) (lsubE (liftL z) M))
lsubE-liftL2-shift z M =
  Eq-trans (lsubE-comp (liftL (liftL z)) (liftL lwkS) M)
    (Eq-trans (lsubE-ext _ _ (\ i -> Eq-trans (liftL-comp (liftL z) lwkS i) (Eq-sym (liftL-comp lwkS z i))) M)
      (Eq-sym (lsubE-comp (liftL lwkS) (liftL z) M)))

liftSub-lsub : {h g : Nat} (z : LSub) (sigma : Sub h g) (i : Fin (suc g)) ->
  Eq (lsubE z (liftSub sigma i)) (liftSub (\ j -> lsubE z (sigma j)) i)
liftSub-lsub z sigma fzero    = refl
liftSub-lsub z sigma (fsuc i) = lsubE-ren z wkRen (sigma i)

-- level substitution commutes with term substitution
lsubE-subst : {h g : Nat} (z : LSub) (sigma : Sub h g) (M : Expr g) ->
  Eq (lsubE z (substExpr sigma M)) (substExpr (\ i -> lsubE z (sigma i)) (lsubE z M))
lsubE-subst z sigma (Var i)       = refl
lsubE-subst z sigma (U l)         = refl
lsubE-subst z sigma (El l a)      = Eq-cong (El (lsubL z l)) (lsubE-subst z sigma a)
lsubE-subst z sigma (PiCode l a b) =
  Eq-cong2 (PiCode (lsubL z l)) (lsubE-subst z sigma a)
    (Eq-trans (lsubE-subst z (liftSub sigma) b) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z b)))
lsubE-subst z sigma (UCode m l)   = refl
lsubE-subst z sigma (Lift m l a)  = Eq-cong (Lift (lsubL z m) (lsubL z l)) (lsubE-subst z sigma a)
lsubE-subst z sigma (EmpCode l)   = refl
lsubE-subst z sigma (Pi A B)      =
  Eq-cong2 Pi (lsubE-subst z sigma A)
    (Eq-trans (lsubE-subst z (liftSub sigma) B) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z B)))
lsubE-subst z sigma (Lam A B b)   =
  Eq-cong3 Lam (lsubE-subst z sigma A)
    (Eq-trans (lsubE-subst z (liftSub sigma) B) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z B)))
    (Eq-trans (lsubE-subst z (liftSub sigma) b) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z b)))
lsubE-subst z sigma (App A B c a) =
  Eq-cong4 App (lsubE-subst z sigma A)
    (Eq-trans (lsubE-subst z (liftSub sigma) B) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z B)))
    (lsubE-subst z sigma c) (lsubE-subst z sigma a)
lsubE-subst z sigma (Grd c A)     = Eq-cong (Grd (lsubC z c)) (lsubE-subst z sigma A)
lsubE-subst z sigma (GLam c A t)  = Eq-cong2 (GLam (lsubC z c)) (lsubE-subst z sigma A) (lsubE-subst z sigma t)
lsubE-subst z sigma Emp           = refl
lsubE-subst z sigma (LPi A)       =
  Eq-cong LPi (Eq-trans (lsubE-subst (liftL z) _ A)
    (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) A)))
lsubE-subst z sigma (LLam A u)    =
  Eq-cong2 LLam
    (Eq-trans (lsubE-subst (liftL z) _ A)
      (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) A)))
    (Eq-trans (lsubE-subst (liftL z) _ u)
      (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) u)))
lsubE-subst z sigma (LApp A t l)  =
  Eq-cong2 (\ X Y -> LApp X Y (lsubL z l))
    (Eq-trans (lsubE-subst (liftL z) _ A)
      (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) A)))
    (lsubE-subst z sigma t)


------------------------------------------------------------------------
-- Renaming composition

------------------------------------------------------------------------

ren-ren : {n m k : Nat} (r1 : Ren m k) (r2 : Ren n m) (e : Expr n)
  -> Eq (renExpr r1 (renExpr r2 e)) (renExpr (\ i -> r1 (r2 i)) e)
ren-ren r1 r2 (Var i)       = refl
ren-ren r1 r2 (U l)       = refl
ren-ren r1 r2 (El l a)   = Eq-cong (El l) (ren-ren r1 r2 a)
ren-ren r1 r2 (PiCode l a b) =
  Eq-cong2 (PiCode l) (ren-ren r1 r2 a)
    (Eq-trans (ren-ren (liftRen r1) (liftRen r2) b)
      (renExpr-ext _ (liftRen (\ i -> r1 (r2 i))) (\ { fzero -> refl ; (fsuc i) -> refl }) b))
ren-ren r1 r2 (UCode m l) = refl
ren-ren r1 r2 (Lift m l a) = Eq-cong (Lift m l) (ren-ren r1 r2 a)
ren-ren r1 r2 (EmpCode l) = refl
ren-ren r1 r2 (Grd c A)  = Eq-cong (Grd c) (ren-ren r1 r2 A)
ren-ren r1 r2 (GLam c A t) = Eq-cong2 (GLam c) (ren-ren r1 r2 A) (ren-ren r1 r2 t)
ren-ren r1 r2 Emp        = refl
ren-ren r1 r2 (LPi A)  = Eq-cong LPi (ren-ren r1 r2 A)
ren-ren r1 r2 (LLam A u) = Eq-cong2 LLam (ren-ren r1 r2 A) (ren-ren r1 r2 u)
ren-ren r1 r2 (LApp A t l) = Eq-cong2 (\ X Y -> LApp X Y l) (ren-ren r1 r2 A) (ren-ren r1 r2 t)
ren-ren r1 r2 (Pi A B)      =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      adj = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
ren-ren r1 r2 (Lam A B b)   =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      ihb = ren-ren (liftRen r1) (liftRen r2) b
      adjB = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
      adjb = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
ren-ren r1 r2 (App A B c a) =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      ihc = ren-ren r1 r2 c
      iha = ren-ren r1 r2 a
      adjB = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha

------------------------------------------------------------------------
-- Renaming/substitution interaction
------------------------------------------------------------------------

subst-ren : {h g k : Nat} (sigma : Sub h g) (r : Ren k g) (e : Expr k)
  -> Eq (substExpr sigma (renExpr r e)) (substExpr (\ i -> sigma (r i)) e)
subst-ren sigma r (Var i)       = refl
subst-ren sigma r (U l)       = refl
subst-ren sigma r (El l a)   = Eq-cong (El l) (subst-ren sigma r a)
subst-ren sigma r (PiCode l a b) =
  Eq-cong2 (PiCode l) (subst-ren sigma r a)
    (Eq-trans (subst-ren (liftSub sigma) (liftRen r) b)
      (substExpr-ext _ (liftSub (\ i -> sigma (r i))) (\ { fzero -> refl ; (fsuc i) -> refl }) b))
subst-ren sigma r (UCode m l) = refl
subst-ren sigma r (Lift m l a) = Eq-cong (Lift m l) (subst-ren sigma r a)
subst-ren sigma r (EmpCode l) = refl
subst-ren sigma r (Grd c A)  = Eq-cong (Grd c) (subst-ren sigma r A)
subst-ren sigma r (GLam c A t) = Eq-cong2 (GLam c) (subst-ren sigma r A) (subst-ren sigma r t)
subst-ren sigma r Emp        = refl
subst-ren sigma r (LPi A)  = Eq-cong LPi (subst-ren _ r A)
subst-ren sigma r (LLam A u) = Eq-cong2 LLam (subst-ren _ r A) (subst-ren _ r u)
subst-ren sigma r (LApp A t l) = Eq-cong2 (\ X Y -> LApp X Y l) (subst-ren _ r A) (subst-ren sigma r t)
subst-ren sigma r (Pi A B)      =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      adj = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
subst-ren sigma r (Lam A B b)   =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      ihb = subst-ren (liftSub sigma) (liftRen r) b
      adjB = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
      adjb = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
subst-ren sigma r (App A B c a) =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      ihc = subst-ren sigma r c
      iha = subst-ren sigma r a
      adjB = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha

ren-wk-comm : {n m : Nat} (r : Ren n m) (e : Expr n)
  -> Eq (renExpr (liftRen r) (wkExpr e)) (wkExpr (renExpr r e))
ren-wk-comm r e =
  Eq-trans (ren-ren (liftRen r) wkRen e) (Eq-sym (ren-ren wkRen r e))

liftSub-ren-ext : {h g k : Nat} (r : Ren g k) (sigma : Sub g h)
  -> (j : Fin (suc h))
  -> Eq (renExpr (liftRen r) (liftSub sigma j))
        (liftSub (\ i -> renExpr r (sigma i)) j)
liftSub-ren-ext r sigma fzero    = refl
liftSub-ren-ext r sigma (fsuc i) = ren-wk-comm r (sigma i)

ren-subst : {h g k : Nat} (r : Ren g k) (sigma : Sub g h) (e : Expr h)
  -> Eq (renExpr r (substExpr sigma e))
        (substExpr (\ i -> renExpr r (sigma i)) e)
ren-subst r sigma (Var i)       = refl
ren-subst r sigma (U l)       = refl
ren-subst r sigma (El l a)   = Eq-cong (El l) (ren-subst r sigma a)
ren-subst r sigma (PiCode l a b) =
  Eq-cong2 (PiCode l) (ren-subst r sigma a)
    (Eq-trans (ren-subst (liftRen r) (liftSub sigma) b)
      (substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i))) (liftSub-ren-ext r sigma) b))
ren-subst r sigma (UCode m l) = refl
ren-subst r sigma (Lift m l a) = Eq-cong (Lift m l) (ren-subst r sigma a)
ren-subst r sigma (EmpCode l) = refl
ren-subst r sigma (Grd c A)  = Eq-cong (Grd c) (ren-subst r sigma A)
ren-subst r sigma (GLam c A t) = Eq-cong2 (GLam c) (ren-subst r sigma A) (ren-subst r sigma t)
ren-subst r sigma Emp        = refl
ren-subst r sigma (LPi A)  =
  Eq-cong LPi (Eq-trans (ren-subst r _ A)
    (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) A))
ren-subst r sigma (LLam A u) =
  Eq-cong2 LLam
    (Eq-trans (ren-subst r _ A)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) A))
    (Eq-trans (ren-subst r _ u)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) u))
ren-subst r sigma (LApp A t l) =
  Eq-cong2 (\ X Y -> LApp X Y l)
    (Eq-trans (ren-subst r _ A)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) A))
    (ren-subst r sigma t)
ren-subst r sigma (Pi A B)      =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      adj = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
              (liftSub-ren-ext r sigma) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
ren-subst r sigma (Lam A B b)   =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      ihb = ren-subst (liftRen r) (liftSub sigma) b
      adjB = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) B
      adjb = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
ren-subst r sigma (App A B c a) =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      ihc = ren-subst r sigma c
      iha = ren-subst r sigma a
      adjB = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha

------------------------------------------------------------------------
-- Substitution composition
------------------------------------------------------------------------

subst-wk-comm : {h g : Nat} (tau : Sub g h) (e : Expr h)
  -> Eq (substExpr (liftSub tau) (wkExpr e)) (wkExpr (substExpr tau e))
subst-wk-comm tau e =
  Eq-trans (subst-ren (liftSub tau) wkRen e) (Eq-sym (ren-subst wkRen tau e))

liftSub-subst-ext : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h)
  -> (j : Fin (suc h))
  -> Eq (substExpr (liftSub tau) (liftSub sigma j))
        (liftSub (\ i -> substExpr tau (sigma i)) j)
liftSub-subst-ext tau sigma fzero    = refl
liftSub-subst-ext tau sigma (fsuc i) = subst-wk-comm tau (sigma i)

subst-subst : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h) (e : Expr h)
  -> Eq (substExpr tau (substExpr sigma e))
        (substExpr (\ i -> substExpr tau (sigma i)) e)
subst-subst tau sigma (Var i)       = refl
subst-subst tau sigma (U l)       = refl
subst-subst tau sigma (El l a)   = Eq-cong (El l) (subst-subst tau sigma a)
subst-subst tau sigma (PiCode l a b) =
  Eq-cong2 (PiCode l) (subst-subst tau sigma a)
    (Eq-trans (subst-subst (liftSub tau) (liftSub sigma) b)
      (substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i))) (liftSub-subst-ext tau sigma) b))
subst-subst tau sigma (UCode m l) = refl
subst-subst tau sigma (Lift m l a) = Eq-cong (Lift m l) (subst-subst tau sigma a)
subst-subst tau sigma (EmpCode l) = refl
subst-subst tau sigma (Grd c A)  = Eq-cong (Grd c) (subst-subst tau sigma A)
subst-subst tau sigma (GLam c A t) = Eq-cong2 (GLam c) (subst-subst tau sigma A) (subst-subst tau sigma t)
subst-subst tau sigma Emp        = refl
subst-subst tau sigma (LPi A)  =
  Eq-cong LPi (Eq-trans (subst-subst _ _ A)
    (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) A))
subst-subst tau sigma (LLam A u) =
  Eq-cong2 LLam
    (Eq-trans (subst-subst _ _ A)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) A))
    (Eq-trans (subst-subst _ _ u)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) u))
subst-subst tau sigma (LApp A t l) =
  Eq-cong2 (\ X Y -> LApp X Y l)
    (Eq-trans (subst-subst _ _ A)
      (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) A))
    (subst-subst tau sigma t)
subst-subst tau sigma (Pi A B)      =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      adj = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
              (liftSub-subst-ext tau sigma) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
subst-subst tau sigma (Lam A B b)   =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      ihb = subst-subst (liftSub tau) (liftSub sigma) b
      adjB = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) B
      adjb = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
subst-subst tau sigma (App A B c a) =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      ihc = subst-subst tau sigma c
      iha = subst-subst tau sigma a
      adjB = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha
