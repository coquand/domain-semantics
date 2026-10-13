{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/Syn.agda
--
-- Syntactic helpers for the soundness of the algorithm: beta under a
-- weakening (with a convertible annotation), application of a weakened
-- function to the fresh variable, eta for functions, congruence of
-- abstractions.
------------------------------------------------------------------------

module MAHLOINJ.Algo.Syn where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.CtxConv

module _ {n : Num} {G : Ctx n} where

  -- (\x:A'.b) applied, after weakening, to x0  reduces to  b
  betaWk : {A A' : Expr n} {B b : Expr (suc n)} -> IsType G A -> IsType G A' -> TyEq G A A' ->
    IsType (extend G A) B -> HasType (extend G A) b B ->
    ConvTm (extend G A) (App (wkExpr (Lam A' b)) x0) b B
  betaWk {A} {A'} {B} {b} iA iA' qA iB hb =
    trCv refl (subst1-liftWk-cancel b) (subst1-liftWk-cancel B)
      (conv-beta iA1 (rTy (liftRen wkRen) rt (wf-extend iA1) (ccTy iA' (tyeq-sym qA) iB))
         (rTm (liftRen wkRen) rt (wf-extend iA1) (ccTm iA' (tyeq-sym qA) hb))
         (ty-conv (ty-var (wf-extend iA)) (wkTE iA qA)))
    where
      iA1 = wkTy iA iA'
      rt = liftRT {A = A'} (wkRT {G = G} {C = A})

  -- t x0 : B  in  (G, A)  for  t : Pi A B
  appWk : {A t : Expr n} {B : Expr (suc n)} -> IsType G A -> IsType (extend G A) B ->
    HasType G t (PiB A B) -> HasType (extend G A) (App (wkExpr t) x0) B
  appWk {A} {t} {B} iA iB ht =
    trHT refl (subst1-liftWk-cancel B)
      (ty-App iA0 (rTy (liftRen wkRen) rt (wf-extend iA0) iB) (wkTm iA ht) (ty-var (wf-extend iA)))
    where
      iA0 = wkTy iA iA
      rt = liftRT {A = A} (wkRT {G = G} {C = A})

  -- eta:  \x:A.b = t  from  b = t x0
  etaLam : {A t : Expr n} {B b : Expr (suc n)} -> IsType G A -> IsType (extend G A) B ->
    HasType (extend G A) b B -> HasType G t (PiB A B) ->
    ConvTm (extend G A) b (App (wkExpr t) x0) B -> ConvTm G (Lam A b) t (PiB A B)
  etaLam iA iB hb ht c =
    conv-funext iA iB (ty-Lam iA iB hb) ht (conv-trans (betaWk iA iA (tyeq-refl iA) iB hb) c)

  -- congruence of abstractions, the annotations being convertible
  lamConvB : {A A' : Expr n} {B b b' : Expr (suc n)} -> IsType G A -> IsType G A' -> TyEq G A A' ->
    IsType (extend G A) B -> HasType (extend G A) b B -> HasType (extend G A) b' B ->
    ConvTm (extend G A) b b' B -> ConvTm G (Lam A b) (Lam A' b') (PiB A B)
  lamConvB {A} {A'} {B} iA iA' qA iB hb hb' c =
    conv-funext iA iB (ty-Lam iA iB hb) hL'
      (conv-trans (betaWk iA iA (tyeq-refl iA) iB hb) (conv-trans c (conv-sym (betaWk iA iA' qA iB hb'))))
    where
      iBA' = ccTy iA' (tyeq-sym qA) iB
      hL' = ty-conv (ty-Lam iA' iBA' (ccTm iA' (tyeq-sym qA) hb'))
              (tyeq-Pi iA' iBA' iBA' (tyeq-sym qA) (tyeq-refl iBA'))
