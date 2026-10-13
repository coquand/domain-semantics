{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Syn.agda
--
-- Syntactic helpers for the fundamental lemma: congruence of
-- abstractions into V, the types of the delta-g chain (copied from the
-- private part of Syntax/Presup), and the recursor step type.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Syn where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.CtxConv
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup

-- \x:A.B = \x:A'.B' : A -> V
lamConv : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  IsType G A -> IsType G A' -> TyEq G A A' -> HasType (extend G A) B V -> HasType (extend G A) B' V ->
  ConvTm (extend G A) B B' V -> ConvTm G (Lam A B) (Lam A' B') (Arr A V)
lamConv {G = G} {A} {A'} {B} {B'} iA iA' qA hB hB' cB =
  conv-funext iA vA hL hL' (conv-trans betaL (conv-trans cB (conv-sym betaR)))
  where
    wA = wf-extend iA
    vA = isty-V wA
    hB'A' = ccTm iA' (tyeq-sym qA) hB'
    hL = ty-Lam iA vA hB
    hL' = ty-conv (ty-Lam iA' (isty-V (wf-extend iA')) hB'A')
            (tyeq-Pi iA' (isty-V (wf-extend iA')) (isty-V (wf-extend iA')) (tyeq-sym qA) (tyeq-refl (isty-V (wf-extend iA'))))
    wA0 = wkTy iA iA
    rtL = liftRT {A = A} (wkRT {G = G} {C = A})
    betaL = trCv refl (subst1-liftWk-cancel B) refl
              (conv-beta wA0 (isty-V (wf-extend wA0)) (rTm (liftRen wkRen) rtL (wf-extend wA0) hB) (ty-var wA))
    wA1 = wkTy iA iA'
    rtR = liftRT {A = A'} (wkRT {G = G} {C = A})
    betaR = trCv refl (subst1-liftWk-cancel B') refl
              (conv-beta wA1 (isty-V (wf-extend wA1)) (rTm (liftRen wkRen) rtR (wf-extend wA1) hB'A')
                 (ty-conv (ty-var wA) (wkTE iA qA)))

-- the type of  g A  for  g : OpG f
gAE : {n : Num} (f A : Expr n) ->
      Eq (subst1 (PiB (Arr x0 V) (Arr (App (App (wkExpr (wkExpr f)) x1) x0) V)) A)
         (PiB (Arr A V) (Arr (App (App (wkExpr f) (wkExpr A)) x0) V))
gAE f A =
  Eq-cong (\ z -> PiB (Arr A V) (Arr (App (App z (wkExpr A)) x0) V))
    (Eq-trans (subst-wk-comm (subst1Sub A) (wkExpr f)) (Eq-cong wkExpr (subst1-wk f A)))

-- the type of  g A F
gAFE : {n : Num} (f A L : Expr n) ->
       Eq (subst1 (Arr (App (App (wkExpr f) (wkExpr A)) x0) V) L)
          (Arr (App (App f A) L) V)
gAFE f A L =
  Eq-cong (\ z -> Arr z V)
    (cong2 App (cong2 App (subst1-wk f L) (subst1-wk A L)) refl)

-- typings along the delta-g chain
gA-ty : {n : Num} {G : Ctx n} {f g A : Expr n} -> HasType G f OpF -> HasType G g (OpG f) -> HasType G A V ->
  HasType G (App g A) (PiB (Arr A V) (Arr (App (App (wkExpr f) (wkExpr A)) x0) V))
gA-ty {f = f} {A = A} hf hg hA = trHT refl (gAE f A) (ty-App (isty-V w) (opGBody w hf) hg hA)
  where w = wfTm hf

gAL-ty : {n : Num} {G : Ctx n} {f g A L : Expr n} -> HasType G f OpF -> HasType G g (OpG f) -> HasType G A V ->
  HasType G L (Arr A V) -> HasType G (App (App g A) L) (Arr (App (App f A) L) V)
gAL-ty {G = G} {f} {g} {A} {L} hf hg hA hL =
  trHT refl (gAFE f A L) (ty-App (arrV hAty) (arrV (isty-el fa1)) (gA-ty hf hg hA) hL)
  where
    hAty = isty-el hA
    wA = wf-extend (arrV hAty)
    fa1 = ty-App (arrV (isty-el (wkTm (arrV hAty) hA)))
            (isty-V (wf-extend (arrV (isty-el (wkTm (arrV hAty) hA)))))
            (ty-App (isty-V wA) (bodyF wA) (wkTm (arrV hAty) hf) (wkTm (arrV hAty) hA))
            (ty-var wA)

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
