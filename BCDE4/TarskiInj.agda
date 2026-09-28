{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiInj
--
-- Injectivity of universes in T_T, in loop-free contexts:
--
--   Γ ⊢ U_l = U_m,  Γ loop-free   ⇒   l = m valid in Γ
--
-- by erasure (Lemma 4.6) to T_R and U-injectivity there, which is
-- proved in the domain model (BCDE4.Main.UInj).  In a context with a
-- loop all types are equal (collapse), so loop-freeness is needed.
------------------------------------------------------------------------

module BCDE4.TarskiInj where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellTyping  as RT
open import BCDE4.TarskiSyntax
open import BCDE4.TarskiTyping
open import BCDE4.EraseDeriv using (eraseCtx ; lctx-erase ; erase-ConvTy)
import BCDE4.Main as Main

U-inj : {n : Nat} {G : Ctx n} {l m : LExpr} ->
  LoopFree (lctx G) -> ConvTy G (U l) (U m) -> Valid (lctx G) l m
U-inj {G = G} {l} {m} lf c =
  Eq-transport (\ T -> Valid T l m) (lctx-erase G)
    (Main.UInj (Eq-transport LoopFree (Eq-sym (lctx-erase G)) lf) (erase-ConvTy c))
