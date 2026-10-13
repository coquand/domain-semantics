{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/CtxConv.agda  (port of MAHLOINJ)
--
-- Context conversion: if A' = A then judgements in (G, A) hold in
-- (G, A'), via the identity substitution.
------------------------------------------------------------------------

module MAHLORT.Syntax.CtxConv where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst

module _ {n : Num} {G : Ctx n} {A A' : Expr n}
         (hA' : IsType G A') (q : TyEq G A' A) where

  ccWS : WtSub (extend G A') (extend G A) idSub
  ccWS fzero =
    trHT refl (Eq-sym (substExpr-id (wkExpr A))) (ty-conv (ty-var (wf-extend hA')) (wkTE hA' q))
  ccWS (fsuc i) =
    trHT refl (Eq-sym (substExpr-id (wkExpr (lookup G i)))) (ty-var (wf-extend hA'))

  private
    w' = wf-extend hA'

  ccTy : {B : Expr (suc n)} -> IsType (extend G A) B -> IsType (extend G A') B
  ccTy {B} h = trTy (substExpr-id B) (sbTy idSub ccWS w' h)

  ccTm : {t B : Expr (suc n)} -> HasType (extend G A) t B -> HasType (extend G A') t B
  ccTm {t} {B} h = trHT (substExpr-id t) (substExpr-id B) (sbTm idSub ccWS w' h)

  ccTE : {B B' : Expr (suc n)} -> TyEq (extend G A) B B' -> TyEq (extend G A') B B'
  ccTE {B} {B'} h = trTE (substExpr-id B) (substExpr-id B') (sbTE idSub ccWS w' h)

  ccCv : {t u B : Expr (suc n)} -> ConvTm (extend G A) t u B -> ConvTm (extend G A') t u B
  ccCv {t} {u} {B} h =
    trCv (substExpr-id t) (substExpr-id u) (substExpr-id B) (sbCv idSub ccWS w' h)
