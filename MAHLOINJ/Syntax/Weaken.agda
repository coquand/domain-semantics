{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Weaken.agda
--
-- Type-preserving renamings preserve the four judgements of
-- MAHLO/Typing.agda (IsType, HasType, TyEq, ConvTm); weakening is the
-- instance  r = wkRen.
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Weaken where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas

RenTypes : {n m : Num} -> Ctx n -> Ctx m -> Ren n m -> Set
RenTypes G H r = (i : Fin _) -> Eq (lookup H (r i)) (renExpr r (lookup G i))

liftRT : {n m : Num} {G : Ctx n} {H : Ctx m} {r : Ren n m} {A : Expr n} ->
         RenTypes G H r -> RenTypes (extend G A) (extend H (renExpr r A)) (liftRen r)
liftRT {r = r} {A} rt fzero = Eq-sym (ren-wk-comm r A)
liftRT {G = G} {r = r} rt (fsuc i) =
  Eq-trans (Eq-cong wkExpr (rt i)) (Eq-sym (ren-wk-comm r (lookup G i)))

renUniv : {n m : Num} (r : Ren n m) {u : Expr n} -> Univ u -> Univ (renExpr r u)
renUniv r (univ-V e) = univ-V (Eq-cong (renExpr r) e)
renUniv r (univ-U f g e) = univ-U (renExpr r f) (renExpr r g) (Eq-cong (renExpr r) e)

mutual
  rTy : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {A : Expr n} -> IsType G A -> IsType H (renExpr r A)
  rTy r rt w (isty-V _) = isty-V w
  rTy r rt w (isty-el h) = isty-el (rTm r rt w h)
  rTy r rt w (isty-Pi hA hB) =
    isty-Pi (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
  rTy r rt w (isty-Sigma hA hB) =
    isty-Sigma (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)

  rTm : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {t A : Expr n} -> HasType G t A -> HasType H (renExpr r t) (renExpr r A)
  rTm r rt w (ty-var {i = i} _) = trHT refl (rt i) (ty-var w)
  rTm r rt w (ty-conv h q) = ty-conv (rTm r rt w h) (rTE r rt w q)
  rTm r rt w (ty-sub h) = ty-sub (rTm r rt w h)
  rTm r rt w (ty-Pi {u = u} un hA hB) =
    ty-Pi (renUniv r un) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r u)
        (rTm (liftRen r) (liftRT rt) (wf-extend (elTy (renUniv r un) (rTm r rt w hA))) hB))
  rTm r rt w (ty-Sigma {u = u} un hA hB) =
    ty-Sigma (renUniv r un) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r u)
        (rTm (liftRen r) (liftRT rt) (wf-extend (elTy (renUniv r un) (rTm r rt w hA))) hB))
  rTm r rt w (ty-Nat-V _) = ty-Nat-V w
  rTm r rt w (ty-Nat-U h) = ty-Nat-U (rTm r rt w h)
  rTm r rt w (ty-Ucode {f = f} hf hg) =
    ty-Ucode (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg))
  rTm r rt w (ty-Fhat {f = f} {g} hf hg hA hB) =
    ty-Fhat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g))
        (rTm (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-sub (rTm r rt w hA)))) hB))
  rTm r rt w (ty-Ghat {f = f} {g} hf hg hA hB hc) =
    ty-Ghat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g))
        (rTm (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-sub (rTm r rt w hA)))) hB))
      (rTm r rt w hc)
  rTm r rt w (ty-Lam hA hB ht) =
    ty-Lam (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) w' hB)
           (rTm (liftRen r) (liftRT rt) w' ht)
    where w' = wf-extend (rTy r rt w hA)
  rTm r rt w (ty-App {a = a} {B} hA hB ht ha) =
    trHT refl (Eq-sym (ren-subst1 r B a))
      (ty-App (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
              (rTm r rt w ht) (rTm r rt w ha))
  rTm r rt w (ty-Pair {t = t} {B = B} hA hB ht hu) =
    ty-Pair (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
            (rTm r rt w ht) (trHT refl (ren-subst1 r B t) (rTm r rt w hu))
  rTm r rt w (ty-Fst hA hB ht) =
    ty-Fst (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
           (rTm r rt w ht)
  rTm r rt w (ty-Snd {t = t} {B} hA hB ht) =
    trHT refl (Eq-sym (ren-subst1 r B (Fst t)))
      (ty-Snd (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
              (rTm r rt w ht))
  rTm r rt w (ty-Zero _) = ty-Zero w
  rTm r rt w (ty-Suc h) = ty-Suc (rTm r rt w h)
  rTm r rt w (ty-Rec {k = k} {C} hC hz hs hk) =
    trHT refl (Eq-sym (ren-subst1 r C k))
      (ty-Rec (rTy (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-Nat-V w))) hC)
              (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
              (trHT refl (ren-RecStep r C) (rTm r rt w hs))
              (rTm r rt w hk))

  rTE : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {A B : Expr n} -> TyEq G A B -> TyEq H (renExpr r A) (renExpr r B)
  rTE r rt w (tyeq-refl h) = tyeq-refl (rTy r rt w h)
  rTE r rt w (tyeq-sym q) = tyeq-sym (rTE r rt w q)
  rTE r rt w (tyeq-trans q q') = tyeq-trans (rTE r rt w q) (rTE r rt w q')
  rTE r rt w (tyeq-el c) = tyeq-el (rCv r rt w c)
  rTE r rt w (tyeq-Pi hA hB hB' qA qB) =
    tyeq-Pi (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) w' hB)
            (rTy (liftRen r) (liftRT rt) w' hB') (rTE r rt w qA)
            (rTE (liftRen r) (liftRT rt) w' qB)
    where w' = wf-extend (rTy r rt w hA)
  rTE r rt w (tyeq-Sigma hA hB hB' qA qB) =
    tyeq-Sigma (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) w' hB)
               (rTy (liftRen r) (liftRT rt) w' hB') (rTE r rt w qA)
               (rTE (liftRen r) (liftRT rt) w' qB)
    where w' = wf-extend (rTy r rt w hA)

  rCv : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {t u A : Expr n} -> ConvTm G t u A -> ConvTm H (renExpr r t) (renExpr r u) (renExpr r A)
  rCv r rt w (conv-refl h) = conv-refl (rTm r rt w h)
  rCv r rt w (conv-sym c) = conv-sym (rCv r rt w c)
  rCv r rt w (conv-trans c c') = conv-trans (rCv r rt w c) (rCv r rt w c')
  rCv r rt w (conv-conv c q) = conv-conv (rCv r rt w c) (rTE r rt w q)
  rCv r rt w (conv-sub c) = conv-sub (rCv r rt w c)
  rCv r rt w (conv-R' hA hB c) = conv-R' (rTm r rt w hA) (rTm r rt w hB) (rCv r rt w c)
  rCv r rt w (conv-delta-f {f = f} {g} hf hg hA hB) =
    conv-delta-f (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g))
        (rTm (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-sub (rTm r rt w hA)))) hB))
  rCv r rt w (conv-delta-g {f = f} {g} hf hg hA hB hc) =
    conv-delta-g (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g))
        (rTm (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-sub (rTm r rt w hA)))) hB))
      (rTm r rt w hc)
  rCv r rt w (conv-beta {a = a} {B} {t} hA hB ht ha) =
    trCv refl (Eq-sym (ren-subst1 r t a)) (Eq-sym (ren-subst1 r B a))
      (conv-beta (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) w' hB)
                 (rTm (liftRen r) (liftRT rt) w' ht) (rTm r rt w ha))
    where w' = wf-extend (rTy r rt w hA)
  rCv r rt w (conv-funext {t = t} {t'} hA hB ht ht' c) =
    conv-funext (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) w' hB)
                (rTm r rt w ht) (rTm r rt w ht')
      (trCv (Eq-cong (\ z -> App z x0) (ren-wk-comm r t))
            (Eq-cong (\ z -> App z x0) (ren-wk-comm r t')) refl
            (rCv (liftRen r) (liftRT rt) w' c))
    where w' = wf-extend (rTy r rt w hA)
  rCv r rt w (conv-fst-beta {t = t} {B = B} hA hB ht hu) =
    conv-fst-beta (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
                  (rTm r rt w ht) (trHT refl (ren-subst1 r B t) (rTm r rt w hu))
  rCv r rt w (conv-snd-beta {t = t} {B = B} hA hB ht hu) =
    trCv refl refl (Eq-sym (ren-subst1 r B t))
      (conv-snd-beta (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
                     (rTm r rt w ht) (trHT refl (ren-subst1 r B t) (rTm r rt w hu)))
  rCv r rt w (conv-pairext {t = t} {B = B} hA hB ht ht' cf cs) =
    conv-pairext (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
                 (rTm r rt w ht) (rTm r rt w ht') (rCv r rt w cf)
                 (trCv refl refl (ren-subst1 r B (Fst t)) (rCv r rt w cs))
  rCv r rt w (conv-rec-zero {C = C} hC hz hs) =
    trCv refl refl (Eq-sym (ren-subst1 r C Zero))
      (conv-rec-zero (rTy (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-Nat-V w))) hC)
                     (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
                     (trHT refl (ren-RecStep r C) (rTm r rt w hs)))
  rCv r rt w (conv-rec-suc {k = k} {C} hC hz hs hk) =
    trCv refl refl (Eq-sym (ren-subst1 r C (Suc k)))
      (conv-rec-suc (rTy (liftRen r) (liftRT rt) (wf-extend (isty-el (ty-Nat-V w))) hC)
                    (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
                    (trHT refl (ren-RecStep r C) (rTm r rt w hs))
                    (rTm r rt w hk))
  rCv r rt w (conv-App {a = a} {B = B} hA hB c ca) =
    trCv refl refl (Eq-sym (ren-subst1 r B a))
      (conv-App (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
                (rCv r rt w c) (rCv r rt w ca))
  rCv r rt w (conv-Fst hA hB c) =
    conv-Fst (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
             (rCv r rt w c)
  rCv r rt w (conv-Snd {t = t} {B = B} hA hB c) =
    trCv refl refl (Eq-sym (ren-subst1 r B (Fst t)))
      (conv-Snd (rTy r rt w hA) (rTy (liftRen r) (liftRT rt) (wf-extend (rTy r rt w hA)) hB)
                (rCv r rt w c))
  rCv r rt w (conv-Pi {u = u} un hA hB hB' cA cB) =
    conv-Pi (renUniv r un) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r u) (rTm (liftRen r) (liftRT rt) w' hB))
      (trHT refl (ren-wk-comm r u) (rTm (liftRen r) (liftRT rt) w' hB'))
      (rCv r rt w cA)
      (trCv refl refl (ren-wk-comm r u) (rCv (liftRen r) (liftRT rt) w' cB))
    where w' = wf-extend (elTy (renUniv r un) (rTm r rt w hA))
  rCv r rt w (conv-Sigma {u = u} un hA hB hB' cA cB) =
    conv-Sigma (renUniv r un) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r u) (rTm (liftRen r) (liftRT rt) w' hB))
      (trHT refl (ren-wk-comm r u) (rTm (liftRen r) (liftRT rt) w' hB'))
      (rCv r rt w cA)
      (trCv refl refl (ren-wk-comm r u) (rCv (liftRen r) (liftRT rt) w' cB))
    where w' = wf-extend (elTy (renUniv r un) (rTm r rt w hA))
  rCv r rt w (conv-Suc c) = conv-Suc (rCv r rt w c)
  rCv r rt w (conv-Rec {k = k} {C = C} hC hC' q cz cs ck) =
    trCv refl refl (Eq-sym (ren-subst1 r C k))
      (conv-Rec (rTy (liftRen r) (liftRT rt) w' hC) (rTy (liftRen r) (liftRT rt) w' hC')
                (rTE (liftRen r) (liftRT rt) w' q)
                (trCv refl refl (ren-subst1 r C Zero) (rCv r rt w cz))
                (trCv refl refl (ren-RecStep r C) (rCv r rt w cs))
                (rCv r rt w ck))
    where w' = wf-extend (isty-el (ty-Nat-V w))
  rCv r rt w (conv-Ucode {f = f} hf hg cf cg) =
    conv-Ucode (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rCv r rt w cf)
               (trCv refl refl (ren-OpG r f) (rCv r rt w cg))
  rCv r rt w (conv-Fhat {f = f} {g = g} cf cg hA hB hB' cA cB) =
    conv-Fhat (rCv r rt w cf) (trCv refl refl (ren-OpG r f) (rCv r rt w cg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g)) (rTm (liftRen r) (liftRT rt) w' hB))
      (trHT refl (ren-wk-comm r (Ucode f g)) (rTm (liftRen r) (liftRT rt) w' hB'))
      (rCv r rt w cA)
      (trCv refl refl (ren-wk-comm r (Ucode f g)) (rCv (liftRen r) (liftRT rt) w' cB))
    where w' = wf-extend (isty-el (ty-sub (rTm r rt w hA)))
  rCv r rt w (conv-Ghat {f = f} {g = g} cf cg hA hB hB' cA cB cc) =
    conv-Ghat (rCv r rt w cf) (trCv refl refl (ren-OpG r f) (rCv r rt w cg)) (rTm r rt w hA)
      (trHT refl (ren-wk-comm r (Ucode f g)) (rTm (liftRen r) (liftRT rt) w' hB))
      (trHT refl (ren-wk-comm r (Ucode f g)) (rTm (liftRen r) (liftRT rt) w' hB'))
      (rCv r rt w cA)
      (trCv refl refl (ren-wk-comm r (Ucode f g)) (rCv (liftRen r) (liftRT rt) w' cB))
      (rCv r rt w cc)
    where w' = wf-extend (isty-el (ty-sub (rTm r rt w hA)))

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

wkRT : {n : Num} {G : Ctx n} {C : Expr n} -> RenTypes G (extend G C) wkRen
wkRT i = refl

module _ {n : Num} {G : Ctx n} {C : Expr n} (hC : IsType G C) where

  wkTy : {A : Expr n} -> IsType G A -> IsType (extend G C) (wkExpr A)
  wkTy = rTy wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkTm : {t A : Expr n} -> HasType G t A -> HasType (extend G C) (wkExpr t) (wkExpr A)
  wkTm = rTm wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkTE : {A B : Expr n} -> TyEq G A B -> TyEq (extend G C) (wkExpr A) (wkExpr B)
  wkTE = rTE wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkCv : {t u A : Expr n} -> ConvTm G t u A ->
         ConvTm (extend G C) (wkExpr t) (wkExpr u) (wkExpr A)
  wkCv = rCv wkRen (wkRT {G = G} {C}) (wf-extend hC)
