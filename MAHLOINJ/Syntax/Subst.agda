{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Subst.agda
--
-- Well-typed substitutions preserve the four judgements of
-- MAHLO/Typing.agda; single substitution as an instance.
-- (Generated from Weaken.agda: same proof, with liftWS for liftRT.)
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Subst where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken

WtSub : {h g : Num} -> Ctx h -> Ctx g -> Sub h g -> Set
WtSub H G s = (i : Fin _) -> HasType H (s i) (substExpr s (lookup G i))

liftWS : {h g : Num} {H : Ctx h} {G : Ctx g} {s : Sub h g} {A : Expr g} ->
         WtSub H G s -> IsType H (substExpr s A) ->
         WtSub (extend H (substExpr s A)) (extend G A) (liftSub s)
liftWS {s = s} {A} ws hA fzero =
  trHT refl (Eq-sym (subst-wk-comm s A)) (ty-var (wf-extend hA))
liftWS {G = G} {s = s} ws hA (fsuc i) =
  trHT refl (Eq-sym (subst-wk-comm s (lookup G i))) (wkTm hA (ws i))

substUniv : {h g : Num} (s : Sub h g) {u : Expr g} -> Univ u -> Univ (substExpr s u)
substUniv s (univ-V e) = univ-V (Eq-cong (substExpr s) e)
substUniv s (univ-U f g e) = univ-U (substExpr s f) (substExpr s g) (Eq-cong (substExpr s) e)

mutual
  sbTy : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {A : Expr n} -> IsType G A -> IsType H (substExpr s A)
  sbTy s ws w (isty-V _) = isty-V w
  sbTy s ws w (isty-el h) = isty-el (sbTm s ws w h)
  sbTy s ws w (isty-Pi hA hB) =
    isty-Pi (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
  sbTy s ws w (isty-Sigma hA hB) =
    isty-Sigma (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)

  sbTm : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {t A : Expr n} -> HasType G t A -> HasType H (substExpr s t) (substExpr s A)
  sbTm s ws w (ty-var {i = i} _) = ws i
  sbTm s ws w (ty-conv h q) = ty-conv (sbTm s ws w h) (sbTE s ws w q)
  sbTm s ws w (ty-sub h) = ty-sub (sbTm s ws w h)
  sbTm s ws w (ty-Pi {u = u} un hA hB) =
    ty-Pi (substUniv s un) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s u)
        (sbTm (liftSub s) (liftWS ws ((elTy (substUniv s un) (sbTm s ws w hA)))) (wf-extend ((elTy (substUniv s un) (sbTm s ws w hA)))) hB))
  sbTm s ws w (ty-Sigma {u = u} un hA hB) =
    ty-Sigma (substUniv s un) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s u)
        (sbTm (liftSub s) (liftWS ws ((elTy (substUniv s un) (sbTm s ws w hA)))) (wf-extend ((elTy (substUniv s un) (sbTm s ws w hA)))) hB))
  sbTm s ws w (ty-Nat-V _) = ty-Nat-V w
  sbTm s ws w (ty-Nat-U h) = ty-Nat-U (sbTm s ws w h)
  sbTm s ws w (ty-Ucode {f = f} hf hg) =
    ty-Ucode (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg))
  sbTm s ws w (ty-Fhat {f = f} {g} hf hg hA hB) =
    ty-Fhat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g))
        (sbTm (liftSub s) (liftWS ws ((isty-el (ty-sub (sbTm s ws w hA))))) (wf-extend ((isty-el (ty-sub (sbTm s ws w hA))))) hB))
  sbTm s ws w (ty-Ghat {f = f} {g} hf hg hA hB hc) =
    ty-Ghat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g))
        (sbTm (liftSub s) (liftWS ws ((isty-el (ty-sub (sbTm s ws w hA))))) (wf-extend ((isty-el (ty-sub (sbTm s ws w hA))))) hB))
      (sbTm s ws w hc)
  sbTm s ws w (ty-Lam hA hB ht) =
    ty-Lam (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws hX) w' hB)
           (sbTm (liftSub s) (liftWS ws hX) w' ht)
    where hX = (sbTy s ws w hA)
          w' = wf-extend hX
  sbTm s ws w (ty-App {a = a} {B} hA hB ht ha) =
    trHT refl (Eq-sym (subst-subst1-comm s B a))
      (ty-App (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
              (sbTm s ws w ht) (sbTm s ws w ha))
  sbTm s ws w (ty-Pair {t = t} {B = B} hA hB ht hu) =
    ty-Pair (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
            (sbTm s ws w ht) (trHT refl (subst-subst1-comm s B t) (sbTm s ws w hu))
  sbTm s ws w (ty-Fst hA hB ht) =
    ty-Fst (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
           (sbTm s ws w ht)
  sbTm s ws w (ty-Snd {t = t} {B} hA hB ht) =
    trHT refl (Eq-sym (subst-subst1-comm s B (Fst t)))
      (ty-Snd (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
              (sbTm s ws w ht))
  sbTm s ws w (ty-Zero _) = ty-Zero w
  sbTm s ws w (ty-Suc h) = ty-Suc (sbTm s ws w h)
  sbTm s ws w (ty-Rec {k = k} {C} hC hz hs hk) =
    trHT refl (Eq-sym (subst-subst1-comm s C k))
      (ty-Rec (sbTy (liftSub s) (liftWS ws ((isty-el (ty-Nat-V w)))) (wf-extend ((isty-el (ty-Nat-V w)))) hC)
              (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
              (trHT refl (subst-RecStep s C) (sbTm s ws w hs))
              (sbTm s ws w hk))

  sbTE : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {A B : Expr n} -> TyEq G A B -> TyEq H (substExpr s A) (substExpr s B)
  sbTE s ws w (tyeq-refl h) = tyeq-refl (sbTy s ws w h)
  sbTE s ws w (tyeq-sym q) = tyeq-sym (sbTE s ws w q)
  sbTE s ws w (tyeq-trans q q') = tyeq-trans (sbTE s ws w q) (sbTE s ws w q')
  sbTE s ws w (tyeq-el c) = tyeq-el (sbCv s ws w c)
  sbTE s ws w (tyeq-Pi hA hB hB' qA qB) =
    tyeq-Pi (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws hX) w' hB)
            (sbTy (liftSub s) (liftWS ws hX) w' hB') (sbTE s ws w qA)
            (sbTE (liftSub s) (liftWS ws hX) w' qB)
    where hX = (sbTy s ws w hA)
          w' = wf-extend hX
  sbTE s ws w (tyeq-Sigma hA hB hB' qA qB) =
    tyeq-Sigma (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws hX) w' hB)
               (sbTy (liftSub s) (liftWS ws hX) w' hB') (sbTE s ws w qA)
               (sbTE (liftSub s) (liftWS ws hX) w' qB)
    where hX = (sbTy s ws w hA)
          w' = wf-extend hX

  sbCv : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {t u A : Expr n} -> ConvTm G t u A -> ConvTm H (substExpr s t) (substExpr s u) (substExpr s A)
  sbCv s ws w (conv-refl h) = conv-refl (sbTm s ws w h)
  sbCv s ws w (conv-sym c) = conv-sym (sbCv s ws w c)
  sbCv s ws w (conv-trans c c') = conv-trans (sbCv s ws w c) (sbCv s ws w c')
  sbCv s ws w (conv-conv c q) = conv-conv (sbCv s ws w c) (sbTE s ws w q)
  sbCv s ws w (conv-sub c) = conv-sub (sbCv s ws w c)
  sbCv s ws w (conv-R' hA hB c) = conv-R' (sbTm s ws w hA) (sbTm s ws w hB) (sbCv s ws w c)
  sbCv s ws w (conv-delta-f {f = f} {g} hf hg hA hB) =
    conv-delta-f (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g))
        (sbTm (liftSub s) (liftWS ws ((isty-el (ty-sub (sbTm s ws w hA))))) (wf-extend ((isty-el (ty-sub (sbTm s ws w hA))))) hB))
  sbCv s ws w (conv-delta-g {f = f} {g} hf hg hA hB hc) =
    conv-delta-g (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g))
        (sbTm (liftSub s) (liftWS ws ((isty-el (ty-sub (sbTm s ws w hA))))) (wf-extend ((isty-el (ty-sub (sbTm s ws w hA))))) hB))
      (sbTm s ws w hc)
  sbCv s ws w (conv-beta {a = a} {B} {t} hA hB ht ha) =
    trCv refl (Eq-sym (subst-subst1-comm s t a)) (Eq-sym (subst-subst1-comm s B a))
      (conv-beta (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws hX) w' hB)
                 (sbTm (liftSub s) (liftWS ws hX) w' ht) (sbTm s ws w ha))
    where hX = (sbTy s ws w hA)
          w' = wf-extend hX
  sbCv s ws w (conv-funext {t = t} {t'} hA hB ht ht' c) =
    conv-funext (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws hX) w' hB)
                (sbTm s ws w ht) (sbTm s ws w ht')
      (trCv (Eq-cong (\ z -> App z x0) (subst-wk-comm s t))
            (Eq-cong (\ z -> App z x0) (subst-wk-comm s t')) refl
            (sbCv (liftSub s) (liftWS ws hX) w' c))
    where hX = (sbTy s ws w hA)
          w' = wf-extend hX
  sbCv s ws w (conv-fst-beta {t = t} {B = B} hA hB ht hu) =
    conv-fst-beta (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
                  (sbTm s ws w ht) (trHT refl (subst-subst1-comm s B t) (sbTm s ws w hu))
  sbCv s ws w (conv-snd-beta {t = t} {B = B} hA hB ht hu) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B t))
      (conv-snd-beta (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
                     (sbTm s ws w ht) (trHT refl (subst-subst1-comm s B t) (sbTm s ws w hu)))
  sbCv s ws w (conv-pairext {t = t} {B = B} hA hB ht ht' cf cs) =
    conv-pairext (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
                 (sbTm s ws w ht) (sbTm s ws w ht') (sbCv s ws w cf)
                 (trCv refl refl (subst-subst1-comm s B (Fst t)) (sbCv s ws w cs))
  sbCv s ws w (conv-rec-zero {C = C} hC hz hs) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C Zero))
      (conv-rec-zero (sbTy (liftSub s) (liftWS ws ((isty-el (ty-Nat-V w)))) (wf-extend ((isty-el (ty-Nat-V w)))) hC)
                     (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
                     (trHT refl (subst-RecStep s C) (sbTm s ws w hs)))
  sbCv s ws w (conv-rec-suc {k = k} {C} hC hz hs hk) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C (Suc k)))
      (conv-rec-suc (sbTy (liftSub s) (liftWS ws ((isty-el (ty-Nat-V w)))) (wf-extend ((isty-el (ty-Nat-V w)))) hC)
                    (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
                    (trHT refl (subst-RecStep s C) (sbTm s ws w hs))
                    (sbTm s ws w hk))
  sbCv s ws w (conv-App {a = a} {B = B} hA hB c ca) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B a))
      (conv-App (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
                (sbCv s ws w c) (sbCv s ws w ca))
  sbCv s ws w (conv-Fst hA hB c) =
    conv-Fst (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
             (sbCv s ws w c)
  sbCv s ws w (conv-Snd {t = t} {B = B} hA hB c) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B (Fst t)))
      (conv-Snd (sbTy s ws w hA) (sbTy (liftSub s) (liftWS ws ((sbTy s ws w hA))) (wf-extend ((sbTy s ws w hA))) hB)
                (sbCv s ws w c))
  sbCv s ws w (conv-Pi {u = u} un hA hB hB' cA cB) =
    conv-Pi (substUniv s un) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (liftWS ws hX) w' hB))
      (trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (liftWS ws hX) w' hB'))
      (sbCv s ws w cA)
      (trCv refl refl (subst-wk-comm s u) (sbCv (liftSub s) (liftWS ws hX) w' cB))
    where hX = (elTy (substUniv s un) (sbTm s ws w hA))
          w' = wf-extend hX
  sbCv s ws w (conv-Sigma {u = u} un hA hB hB' cA cB) =
    conv-Sigma (substUniv s un) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (liftWS ws hX) w' hB))
      (trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (liftWS ws hX) w' hB'))
      (sbCv s ws w cA)
      (trCv refl refl (subst-wk-comm s u) (sbCv (liftSub s) (liftWS ws hX) w' cB))
    where hX = (elTy (substUniv s un) (sbTm s ws w hA))
          w' = wf-extend hX
  sbCv s ws w (conv-Suc c) = conv-Suc (sbCv s ws w c)
  sbCv s ws w (conv-Rec {k = k} {C = C} hC hC' q cz cs ck) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C k))
      (conv-Rec (sbTy (liftSub s) (liftWS ws hX) w' hC) (sbTy (liftSub s) (liftWS ws hX) w' hC')
                (sbTE (liftSub s) (liftWS ws hX) w' q)
                (trCv refl refl (subst-subst1-comm s C Zero) (sbCv s ws w cz))
                (trCv refl refl (subst-RecStep s C) (sbCv s ws w cs))
                (sbCv s ws w ck))
    where hX = (isty-el (ty-Nat-V w))
          w' = wf-extend hX
  sbCv s ws w (conv-Ucode {f = f} hf hg cf cg) =
    conv-Ucode (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbCv s ws w cf)
               (trCv refl refl (subst-OpG s f) (sbCv s ws w cg))
  sbCv s ws w (conv-Fhat {f = f} {g = g} cf cg hA hB hB' cA cB) =
    conv-Fhat (sbCv s ws w cf) (trCv refl refl (subst-OpG s f) (sbCv s ws w cg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (liftWS ws hX) w' hB))
      (trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (liftWS ws hX) w' hB'))
      (sbCv s ws w cA)
      (trCv refl refl (subst-wk-comm s (Ucode f g)) (sbCv (liftSub s) (liftWS ws hX) w' cB))
    where hX = (isty-el (ty-sub (sbTm s ws w hA)))
          w' = wf-extend hX
  sbCv s ws w (conv-Ghat {f = f} {g = g} cf cg hA hB hB' cA cB cc) =
    conv-Ghat (sbCv s ws w cf) (trCv refl refl (subst-OpG s f) (sbCv s ws w cg)) (sbTm s ws w hA)
      (trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (liftWS ws hX) w' hB))
      (trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (liftWS ws hX) w' hB'))
      (sbCv s ws w cA)
      (trCv refl refl (subst-wk-comm s (Ucode f g)) (sbCv (liftSub s) (liftWS ws hX) w' cB))
      (sbCv s ws w cc)
    where hX = (isty-el (ty-sub (sbTm s ws w hA)))
          w' = wf-extend hX

------------------------------------------------------------------------
-- Single substitution
------------------------------------------------------------------------

ws1 : {n : Num} {G : Ctx n} {A a : Expr n} -> WfCtx G -> HasType G a A ->
      WtSub G (extend G A) (subst1Sub a)
ws1 {A = A} {a} w ha fzero = trHT refl (Eq-sym (subst1-wk A a)) ha
ws1 {G = G} {a = a} w ha (fsuc i) = trHT refl (Eq-sym (subst1-wk (lookup G i) a)) (ty-var w)

module _ {n : Num} {G : Ctx n} {A a : Expr n} (w : WfCtx G) (ha : HasType G a A) where

  s1Ty : {B : Expr (suc n)} -> IsType (extend G A) B -> IsType G (subst1 B a)
  s1Ty = sbTy (subst1Sub a) (ws1 w ha) w

  s1Tm : {t B : Expr (suc n)} -> HasType (extend G A) t B -> HasType G (subst1 t a) (subst1 B a)
  s1Tm = sbTm (subst1Sub a) (ws1 w ha) w

  s1TE : {B B' : Expr (suc n)} -> TyEq (extend G A) B B' -> TyEq G (subst1 B a) (subst1 B' a)
  s1TE = sbTE (subst1Sub a) (ws1 w ha) w

  s1Cv : {t u B : Expr (suc n)} -> ConvTm (extend G A) t u B ->
         ConvTm G (subst1 t a) (subst1 u a) (subst1 B a)
  s1Cv = sbCv (subst1Sub a) (ws1 w ha) w
