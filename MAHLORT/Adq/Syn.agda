{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Syn.agda  (Tarski port of the recursor part of
-- MAHLOINJ/Adq/Syn; the delta-chain helpers are not needed, the
-- T^-equations are handled with MAHLORT/Syntax/Ops)
--
-- Syntactic helpers for the fundamental lemma: the recursor step type.
------------------------------------------------------------------------

module MAHLORT.Adq.Syn where

open import MAHLO.Basic
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.SubstLemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf

-- the step type of the recursor at k
stepE : {n : Num} (C : Expr (suc n)) (k : Expr n) ->
        Eq (subst1 (Arr C (substExpr sucSub C)) k) (Arr (subst1 C k) (subst1 C (Suc k)))
stepE C k =
  Eq-cong (\ z -> Pi (subst1 C k) (Lam (subst1 C k) z))
    (Eq-trans (subst-wk-comm (subst1Sub k) (substExpr sucSub C))
              (Eq-cong wkExpr (subst1-sucSub C k)))

-- substitution  x0 := S x0  is well typed in  (G, Nat)
wsSuc : {n : Num} {G : Ctx n} -> WfCtx G -> WtSub (extend G Nat) (extend G Nat) sucSub
wsSuc w fzero = ty-Suc (ty-var (wf-extend (NatTy w)))
wsSuc {G = G} w (fsuc i) =
  trHT refl (Eq-sym (sucSub-wk (lookup G i))) (ty-var (wf-extend (NatTy w)))

cS-Ty : {n : Num} {G : Ctx n} {C : Expr (suc n)} -> WfCtx G ->
        IsType (extend G Nat) C -> IsType (extend G Nat) (substExpr sucSub C)
cS-Ty w hC = sbTy sucSub (wsSuc w) (wf-extend (NatTy w)) hC

stepTy : {n : Num} {G : Ctx n} {C : Expr (suc n)} -> WfCtx G -> IsType (extend G Nat) C ->
  IsType (extend G Nat) (Arr C (substExpr sucSub C))
stepTy w hC = isty-Pi hC (wkTy hC (cS-Ty w hC))

stepEq : {n : Num} {G : Ctx n} {C C' : Expr (suc n)} -> WfCtx G ->
  IsType (extend G Nat) C -> IsType (extend G Nat) C' -> TyEq (extend G Nat) C C' -> TyEq G (RecStep C) (RecStep C')
stepEq w hC hC' q =
  tyeq-Pi (NatTy w) (stepTy w hC) (isty-Pi hC' (wkTy hC' (cS-Ty w hC'))) (tyeq-refl (NatTy w))
    (tyeq-Pi hC (wkTy hC (cS-Ty w hC)) (wkTy hC (cS-Ty w hC')) q (wkTE hC eCS))
  where
    eCS = sbTE sucSub (wsSuc w) (wf-extend (NatTy w)) q

-- the step families of two equal motives
stepFamEq : {n : Num} {G : Ctx n} {C C' : Expr (suc n)} -> WfCtx G ->
  IsType (extend G Nat) C -> IsType (extend G Nat) C' -> TyEq (extend G Nat) C C' ->
  TyEq (extend G Nat) (Arr C (substExpr sucSub C)) (Arr C' (substExpr sucSub C'))
stepFamEq w hC hC' q =
  tyeq-Pi hC (wkTy hC (cS-Ty w hC)) (wkTy hC (cS-Ty w hC')) q (wkTE hC (sbTE sucSub (wsSuc w) (wf-extend (NatTy w)) q))
