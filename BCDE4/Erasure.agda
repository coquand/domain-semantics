{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Erasure
--
-- Erasure |·| : T_T → T_R (bcde.pdf App. B): forget the decoding El,
-- the lifts and the code constructors.
--
--   |El_l a| = |a|      |Π^l a b| = Π |a| |b|     |U^m_l| = U_l
--   |↑^m_l a| = |a|     |∅^l| = ∅
--
-- and commutation with renaming, substitution and level substitution.
------------------------------------------------------------------------

module BCDE4.Erasure where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax as R
import BCDE4.TarskiSyntax  as T

erase : {n : Nat} -> T.Expr n -> R.Expr n
erase (T.Var i)        = R.Var i
erase (T.U l)          = R.U l
erase (T.Pi A B)       = R.Pi (erase A) (erase B)
erase (T.Lam A B b)    = R.Lam (erase A) (erase B) (erase b)
erase (T.App A B c a)  = R.App (erase A) (erase B) (erase c) (erase a)
erase (T.Grd c A)      = R.Grd c (erase A)
erase (T.GLam c A t)   = R.GLam c (erase A) (erase t)
erase T.Emp            = R.Emp
erase (T.LPi A)        = R.LPi (erase A)
erase (T.LLam A u)     = R.LLam (erase A) (erase u)
erase (T.LApp A t l)   = R.LApp (erase A) (erase t) l
erase (T.El l a)       = erase a
erase (T.PiCode l a b) = R.Pi (erase a) (erase b)
erase (T.UCode m l)    = R.U l
erase (T.Lift m l a)   = erase a
erase (T.EmpCode l)    = R.Emp

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

erase-ren : {n m : Nat} (r : Ren n m) (e : T.Expr n)
  -> Eq (erase (T.renExpr r e)) (R.renExpr r (erase e))
erase-ren r (T.Var i)        = refl
erase-ren r (T.U l)          = refl
erase-ren r (T.Pi A B)       = Eq-cong2 R.Pi (erase-ren r A) (erase-ren (liftRen r) B)
erase-ren r (T.Lam A B b)    =
  Eq-cong3 R.Lam (erase-ren r A) (erase-ren (liftRen r) B) (erase-ren (liftRen r) b)
erase-ren r (T.App A B c a)  =
  Eq-cong4 R.App (erase-ren r A) (erase-ren (liftRen r) B) (erase-ren r c) (erase-ren r a)
erase-ren r (T.Grd c A)      = Eq-cong (R.Grd c) (erase-ren r A)
erase-ren r (T.GLam c A t)   = Eq-cong2 (R.GLam c) (erase-ren r A) (erase-ren r t)
erase-ren r T.Emp            = refl
erase-ren r (T.LPi A)        = Eq-cong R.LPi (erase-ren r A)
erase-ren r (T.LLam A u)     = Eq-cong2 R.LLam (erase-ren r A) (erase-ren r u)
erase-ren r (T.LApp A t l)   = Eq-cong2 (\ X Y -> R.LApp X Y l) (erase-ren r A) (erase-ren r t)
erase-ren r (T.El l a)       = erase-ren r a
erase-ren r (T.PiCode l a b) = Eq-cong2 R.Pi (erase-ren r a) (erase-ren (liftRen r) b)
erase-ren r (T.UCode m l)    = refl
erase-ren r (T.Lift m l a)   = erase-ren r a
erase-ren r (T.EmpCode l)    = refl

erase-wk : {n : Nat} (e : T.Expr n) -> Eq (erase (T.wkExpr e)) (R.wkExpr (erase e))
erase-wk e = erase-ren wkRen e

------------------------------------------------------------------------
-- Level substitution
------------------------------------------------------------------------

erase-lsub : {n : Nat} (z : LSub) (e : T.Expr n)
  -> Eq (erase (T.lsubE z e)) (R.lsubE z (erase e))
erase-lsub z (T.Var i)        = refl
erase-lsub z (T.U l)          = refl
erase-lsub z (T.Pi A B)       = Eq-cong2 R.Pi (erase-lsub z A) (erase-lsub z B)
erase-lsub z (T.Lam A B b)    = Eq-cong3 R.Lam (erase-lsub z A) (erase-lsub z B) (erase-lsub z b)
erase-lsub z (T.App A B c a)  =
  Eq-cong4 R.App (erase-lsub z A) (erase-lsub z B) (erase-lsub z c) (erase-lsub z a)
erase-lsub z (T.Grd c A)      = Eq-cong (R.Grd (lsubC z c)) (erase-lsub z A)
erase-lsub z (T.GLam c A t)   = Eq-cong2 (R.GLam (lsubC z c)) (erase-lsub z A) (erase-lsub z t)
erase-lsub z T.Emp            = refl
erase-lsub z (T.LPi A)        = Eq-cong R.LPi (erase-lsub (liftL z) A)
erase-lsub z (T.LLam A u)     = Eq-cong2 R.LLam (erase-lsub (liftL z) A) (erase-lsub (liftL z) u)
erase-lsub z (T.LApp A t l)   = Eq-cong2 (\ X Y -> R.LApp X Y (lsubL z l)) (erase-lsub (liftL z) A) (erase-lsub z t)
erase-lsub z (T.El l a)       = erase-lsub z a
erase-lsub z (T.PiCode l a b) = Eq-cong2 R.Pi (erase-lsub z a) (erase-lsub z b)
erase-lsub z (T.UCode m l)    = refl
erase-lsub z (T.Lift m l a)   = erase-lsub z a
erase-lsub z (T.EmpCode l)    = refl

erase-lshift : {n : Nat} (e : T.Expr n) -> Eq (erase (T.lshiftE e)) (R.lshiftE (erase e))
erase-lshift = erase-lsub lwkS

erase-lsub1 : {n : Nat} (e : T.Expr n) (l : LExpr) -> Eq (erase (T.lsub1 e l)) (R.lsub1 (erase e) l)
erase-lsub1 e l = erase-lsub (lsub1S l) e

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

eraseSub : {h g : Nat} -> T.Sub h g -> R.Sub h g
eraseSub sigma i = erase (sigma i)

eraseSub-lift : {h g : Nat} (sigma : T.Sub h g) (j : Fin (suc g))
  -> Eq (eraseSub (T.liftSub sigma) j) (R.liftSub (eraseSub sigma) j)
eraseSub-lift sigma fzero    = refl
eraseSub-lift sigma (fsuc i) = erase-wk (sigma i)

private
  under : {h g : Nat} (sigma : T.Sub h g) (e : T.Expr (suc g)) ->
    Eq (erase (T.substExpr (T.liftSub sigma) e)) (R.substExpr (eraseSub (T.liftSub sigma)) (erase e)) ->
    Eq (erase (T.substExpr (T.liftSub sigma) e)) (R.substExpr (R.liftSub (eraseSub sigma)) (erase e))
  under sigma e ih = Eq-trans ih (R.substExpr-ext _ _ (eraseSub-lift sigma) (erase e))

erase-subst : {h g : Nat} (sigma : T.Sub h g) (e : T.Expr g)
  -> Eq (erase (T.substExpr sigma e)) (R.substExpr (eraseSub sigma) (erase e))
erase-subst sigma (T.Var i)        = refl
erase-subst sigma (T.U l)          = refl
erase-subst sigma (T.Pi A B)       =
  Eq-cong2 R.Pi (erase-subst sigma A) (under sigma B (erase-subst (T.liftSub sigma) B))
erase-subst sigma (T.Lam A B b)    =
  Eq-cong3 R.Lam (erase-subst sigma A) (under sigma B (erase-subst (T.liftSub sigma) B))
    (under sigma b (erase-subst (T.liftSub sigma) b))
erase-subst sigma (T.App A B c a)  =
  Eq-cong4 R.App (erase-subst sigma A) (under sigma B (erase-subst (T.liftSub sigma) B))
    (erase-subst sigma c) (erase-subst sigma a)
erase-subst sigma (T.Grd c A)      = Eq-cong (R.Grd c) (erase-subst sigma A)
erase-subst sigma (T.GLam c A t)   = Eq-cong2 (R.GLam c) (erase-subst sigma A) (erase-subst sigma t)
erase-subst sigma T.Emp            = refl
erase-subst sigma (T.LPi A)        =
  Eq-cong R.LPi (Eq-trans (erase-subst _ A)
    (R.substExpr-ext _ _ (\ i -> erase-lshift (sigma i)) (erase A)))
erase-subst sigma (T.LLam A u)     =
  Eq-cong2 R.LLam
    (Eq-trans (erase-subst _ A) (R.substExpr-ext _ _ (\ i -> erase-lshift (sigma i)) (erase A)))
    (Eq-trans (erase-subst _ u) (R.substExpr-ext _ _ (\ i -> erase-lshift (sigma i)) (erase u)))
erase-subst sigma (T.LApp A t l)   =
  Eq-cong2 (\ X Y -> R.LApp X Y l)
    (Eq-trans (erase-subst _ A) (R.substExpr-ext _ _ (\ i -> erase-lshift (sigma i)) (erase A)))
    (erase-subst sigma t)
erase-subst sigma (T.El l a)       = erase-subst sigma a
erase-subst sigma (T.PiCode l a b) =
  Eq-cong2 R.Pi (erase-subst sigma a) (under sigma b (erase-subst (T.liftSub sigma) b))
erase-subst sigma (T.UCode m l)    = refl
erase-subst sigma (T.Lift m l a)   = erase-subst sigma a
erase-subst sigma (T.EmpCode l)    = refl

eraseSub-subst1 : {n : Nat} (s : T.Expr n) (j : Fin (suc n))
  -> Eq (eraseSub (T.subst1Sub s) j) (R.subst1Sub (erase s) j)
eraseSub-subst1 s fzero    = refl
eraseSub-subst1 s (fsuc i) = refl

erase-subst1 : {n : Nat} (e : T.Expr (suc n)) (s : T.Expr n)
  -> Eq (erase (T.subst1 e s)) (R.subst1 (erase e) (erase s))
erase-subst1 e s =
  Eq-trans (erase-subst (T.subst1Sub s) e)
           (R.substExpr-ext _ _ (eraseSub-subst1 s) (erase e))
