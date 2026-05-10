{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.Erasure
--
-- The erasure map  |·| : Expr_T → Expr_R   from Tarski raw syntax to
-- Russell raw syntax (slide 11):
--
--   |v_i|              = v_i
--   |Π(A,B)|           = Π(|A|, |B|)
--   |U n|              = U n
--   |El n a|           = |a|
--   |λ(A,B,b)|         = λ(|A|, |B|, |b|)
--   |app(A,B,c,a)|     = app(|A|, |B|, |c|, |a|)
--   |Π^l a b|          = Π(|a|, |b|)
--   |U^m_n|            = U n
--   |↑^m_n a|          = |a|
--
-- We then prove that erasure commutes with renaming and with
-- parallel substitution.
------------------------------------------------------------------------

module Sterbac.Erasure where

open import Sterbac.Basic
import Sterbac.RussellSyntax as R
import Sterbac.TarskiSyntax   as T

------------------------------------------------------------------------
-- The erasure map
------------------------------------------------------------------------

erase : {n : Nat} -> T.Expr n -> R.Expr n
erase (T.Var i)        = R.Var i
erase (T.Pi A B)       = R.Pi (erase A) (erase B)
erase (T.U l)          = R.U l
erase (T.El l a)       = erase a
erase (T.Lam A B b)    = R.Lam (erase A) (erase B) (erase b)
erase (T.App A B c a)  = R.App (erase A) (erase B) (erase c) (erase a)
erase (T.PiCode l a b) = R.Pi (erase a) (erase b)
erase (T.UCode m l)    = R.U l
erase (T.Lift m l a)   = erase a

------------------------------------------------------------------------
-- Renamings on Tarski coincide with renamings on Russell at the
-- level of indices — both Ren live in Sterbac.Basic now (as Fin → Fin
-- functions), so a Tarski Ren is the same data as a Russell Ren.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Erasure commutes with renaming
------------------------------------------------------------------------

erase-ren : {n m : Nat} (r : Ren n m) (e : T.Expr n)
  -> Eq (erase (T.renExpr r e)) (R.renExpr r (erase e))
erase-ren r (T.Var i)        = refl
erase-ren r (T.Pi A B)       =
  Eq-cong2 R.Pi (erase-ren r A) (erase-ren (liftRen r) B)
erase-ren r (T.U l)          = refl
erase-ren r (T.El l a)       = erase-ren r a
erase-ren r (T.Lam A B b)    =
  Eq-cong3 R.Lam (erase-ren r A)
                 (erase-ren (liftRen r) B)
                 (erase-ren (liftRen r) b)
erase-ren r (T.App A B c a)  =
  Eq-cong4 R.App (erase-ren r A)
                 (erase-ren (liftRen r) B)
                 (erase-ren r c)
                 (erase-ren r a)
erase-ren r (T.PiCode l a b) =
  Eq-cong2 R.Pi (erase-ren r a) (erase-ren (liftRen r) b)
erase-ren r (T.UCode m l)    = refl
erase-ren r (T.Lift m l a)   = erase-ren r a

erase-wk : {n : Nat} (e : T.Expr n)
  -> Eq (erase (T.wkExpr e)) (R.wkExpr (erase e))
erase-wk e = erase-ren wkRen e

------------------------------------------------------------------------
-- Erasure of a substitution
------------------------------------------------------------------------

eraseSub : {h g : Nat} -> T.Sub h g -> R.Sub h g
eraseSub sigma i = erase (sigma i)

eraseSub-lift : {h g : Nat} (sigma : T.Sub h g) (j : Fin (suc g))
  -> Eq (eraseSub (T.liftSub sigma) j) (R.liftSub (eraseSub sigma) j)
eraseSub-lift sigma fzero    = refl
eraseSub-lift sigma (fsuc i) = erase-wk (sigma i)

------------------------------------------------------------------------
-- Erasure commutes with substitution
------------------------------------------------------------------------

erase-subst : {h g : Nat} (sigma : T.Sub h g) (e : T.Expr g)
  -> Eq (erase (T.substExpr sigma e))
        (R.substExpr (eraseSub sigma) (erase e))
erase-subst sigma (T.Var i)        = refl
erase-subst sigma (T.Pi A B)       =
  Eq-cong2 R.Pi (erase-subst sigma A)
    (Eq-trans (erase-subst (T.liftSub sigma) B)
              (R.substExpr-ext (eraseSub (T.liftSub sigma))
                               (R.liftSub (eraseSub sigma))
                               (eraseSub-lift sigma)
                               (erase B)))
erase-subst sigma (T.U l)          = refl
erase-subst sigma (T.El l a)       = erase-subst sigma a
erase-subst sigma (T.Lam A B b)    =
  Eq-cong3 R.Lam
    (erase-subst sigma A)
    (Eq-trans (erase-subst (T.liftSub sigma) B)
              (R.substExpr-ext (eraseSub (T.liftSub sigma))
                               (R.liftSub (eraseSub sigma))
                               (eraseSub-lift sigma)
                               (erase B)))
    (Eq-trans (erase-subst (T.liftSub sigma) b)
              (R.substExpr-ext (eraseSub (T.liftSub sigma))
                               (R.liftSub (eraseSub sigma))
                               (eraseSub-lift sigma)
                               (erase b)))
erase-subst sigma (T.App A B c a)  =
  Eq-cong4 R.App
    (erase-subst sigma A)
    (Eq-trans (erase-subst (T.liftSub sigma) B)
              (R.substExpr-ext (eraseSub (T.liftSub sigma))
                               (R.liftSub (eraseSub sigma))
                               (eraseSub-lift sigma)
                               (erase B)))
    (erase-subst sigma c)
    (erase-subst sigma a)
erase-subst sigma (T.PiCode l a b) =
  Eq-cong2 R.Pi (erase-subst sigma a)
    (Eq-trans (erase-subst (T.liftSub sigma) b)
              (R.substExpr-ext (eraseSub (T.liftSub sigma))
                               (R.liftSub (eraseSub sigma))
                               (eraseSub-lift sigma)
                               (erase b)))
erase-subst sigma (T.UCode m l)    = refl
erase-subst sigma (T.Lift m l a)   = erase-subst sigma a

------------------------------------------------------------------------
-- Erasure commutes with single substitution
------------------------------------------------------------------------

eraseSub-subst1 : {n : Nat} (s : T.Expr n) (j : Fin (suc n))
  -> Eq (eraseSub (T.subst1Sub s) j) (R.subst1Sub (erase s) j)
eraseSub-subst1 s fzero    = refl
eraseSub-subst1 s (fsuc i) = refl

erase-subst1 : {n : Nat} (e : T.Expr (suc n)) (s : T.Expr n)
  -> Eq (erase (T.subst1 e s)) (R.subst1 (erase e) (erase s))
erase-subst1 e s =
  Eq-trans (erase-subst (T.subst1Sub s) e)
           (R.substExpr-ext (eraseSub (T.subst1Sub s))
                            (R.subst1Sub (erase s))
                            (eraseSub-subst1 s)
                            (erase e))
