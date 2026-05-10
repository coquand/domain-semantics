{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.Postulates
--
-- Assumed lemmas (per discussion with Thierry, 2026-05-10):
--
--   "ASSUME Pi-injection and no confusion. (We should be able to prove
--   it later but this is another story.)"
--
-- These are the structural properties that the Sterbac slides flag as
-- "necessary" for the uniqueness lemma (slide 17):
--
--   * Injectivity of U•
--   * No-confusion between U• and Π(−,−)
--   * Injectivity of Π(−,−)
--
-- They are stated for both T_T (Tarski) and T_R (Russell). Each is
-- intended to be discharged later by a normalisation / logical-relation
-- argument; for now we postulate them.
------------------------------------------------------------------------

module Sterbac.Postulates where

open import Sterbac.Basic
import Sterbac.RussellSyntax  as R
import Sterbac.RussellTyping  as RT
import Sterbac.TarskiSyntax   as T
import Sterbac.TarskiTyping   as TT

------------------------------------------------------------------------
-- T_T  (Tarski)
------------------------------------------------------------------------

-- Π-injectivity at the type level
postulate
  Pi-inj-Ty-T :
    {n : Nat} {G : TT.Ctx n} {A A' : T.Expr n} {B B' : T.Expr (suc n)}
    -> TT.ConvTy G (T.Pi A B) (T.Pi A' B')
    -> Pair (TT.ConvTy G A A')
            (TT.ConvTy (TT.extend G A) B B')

-- U-injectivity at the type level
postulate
  U-inj-Ty-T :
    {n : Nat} {G : TT.Ctx n} {l l' : Nat}
    -> TT.ConvTy G (T.U l) (T.U l')
    -> Eq l l'

-- No-confusion between U• and Π(−,−) at the type level
postulate
  U-Pi-noconf-Ty-T :
    {n : Nat} {G : TT.Ctx n} {l : Nat} {A : T.Expr n} {B : T.Expr (suc n)}
    -> TT.ConvTy G (T.U l) (T.Pi A B)
    -> Empty

------------------------------------------------------------------------
-- T_T (Tarski) — code-level injectivity / no-confusion
--
-- These talk about ConvTm at type U_l, and identify the head shape of
-- a code (UCode, PiCode, Lift, …) up to conversion. They are the term
-- analogues of the type-level postulates above and are likewise
-- expected to be discharged by normalisation.
------------------------------------------------------------------------

-- Two U-codes equal at U_m must code the same level
postulate
  UCode-inj-T :
    {n : Nat} {G : TT.Ctx n} {m l l' : Nat}
    -> TT.ConvTm G (T.UCode m l) (T.UCode m l') (T.U m)
    -> Eq l l'

-- Π-codes are injective in their components
postulate
  PiCode-inj-T :
    {n : Nat} {G : TT.Ctx n} {l : Nat}
    {a a' : T.Expr n} {b b' : T.Expr (suc n)}
    -> TT.ConvTm G (T.PiCode l a b) (T.PiCode l a' b') (T.U l)
    -> Pair (TT.ConvTm G a a' (T.U l))
            (TT.ConvTm (TT.extend G (T.El l a)) b b' (T.U l))

-- A U-code and a Π-code are never convertible
postulate
  UCode-PiCode-noconf-T :
    {n : Nat} {G : TT.Ctx n} {m l l' : Nat}
    {a : T.Expr n} {b : T.Expr (suc n)}
    -> TT.ConvTm G (T.UCode m l) (T.PiCode l' a b) (T.U m)
    -> Empty

------------------------------------------------------------------------
-- T_R  (Russell)
------------------------------------------------------------------------

-- Π-injectivity at the type level
postulate
  Pi-inj-Ty-R :
    {n : Nat} {G : RT.Ctx n} {A A' : R.Expr n} {B B' : R.Expr (suc n)}
    -> RT.ConvTy G (R.Pi A B) (R.Pi A' B')
    -> Pair (RT.ConvTy G A A')
            (RT.ConvTy (RT.extend G A) B B')

-- U-injectivity at the type level (used by the lift-back argument)
postulate
  U-inj-Ty-R :
    {n : Nat} {G : RT.Ctx n} {l l' : Nat}
    -> RT.ConvTy G (R.U l) (R.U l')
    -> Eq l l'

-- No-confusion U / Π in Russell
postulate
  U-Pi-noconf-Ty-R :
    {n : Nat} {G : RT.Ctx n} {l : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
    -> RT.ConvTy G (R.U l) (R.Pi A B)
    -> Empty
