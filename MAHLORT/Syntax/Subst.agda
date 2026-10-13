{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Subst.agda
--
-- Well-typed substitutions preserve the judgements of
-- MAHLORT/TarskiTyping.agda; single substitution as an instance.
-- (Generated from Weaken.agda: same proof, liftWS for liftRT.)
------------------------------------------------------------------------

module MAHLORT.Syntax.Subst where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken

WtSub : {h g : Num} -> Ctx h -> Ctx g -> Sub h g -> Set
WtSub H G s = (i : Fin _) -> HasType H (s i) (substExpr s (lookup G i))

liftWS : {h g : Num} {H : Ctx h} {G : Ctx g} {s : Sub h g} {A : Expr g} ->
         WtSub H G s -> IsType H (substExpr s A) ->
         WtSub (extend H (substExpr s A)) (extend G A) (liftSub s)
liftWS {s = s} {A} ws hA fzero =
  trHT refl (Eq-sym (subst-wk-comm s A)) (ty-var (wf-extend hA))
liftWS {G = G} {s = s} ws hA (fsuc i) =
  trHT refl (Eq-sym (subst-wk-comm s (lookup G i))) (wkTm hA (ws i))

mutual
  sbTy : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {A : Expr n} -> IsType G A -> IsType H (substExpr s A)
  sbTy s ws w (isty-V _) = isty-V w
  sbTy s ws w (isty-ElV h) = isty-ElV (sbTm s ws w h)
  sbTy s ws w (isty-TyU {f = f} hf hg) =
    isty-TyU (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg))
  sbTy s ws w (isty-ElU h) = isty-ElU (sbTm s ws w h)
  sbTy s ws w (isty-Pi hA hB) =
    isty-Pi hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
    where hX = sbTy s ws w hA
  sbTy s ws w (isty-Sigma hA hB) =
    isty-Sigma hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
    where hX = sbTy s ws w hA
  sbTy s ws w (isty-Nat _) = isty-Nat w

  sbTm : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {t A : Expr n} -> HasType G t A -> HasType H (substExpr s t) (substExpr s A)
  sbTm s ws w (ty-var {i = i} _) = ws i
  sbTm s ws w (ty-conv h q) = ty-conv (sbTm s ws w h) (sbTE s ws w q)
  sbTm s ws w (ty-Lam hA hB ht) =
    ty-Lam hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
              (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) ht)
    where hX = sbTy s ws w hA
  sbTm s ws w (ty-App {a = a} {B} hA hB ht ha) =
    trHT refl (Eq-sym (subst-subst1-comm s B a))
      (ty-App hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTm s ws w ht) (sbTm s ws w ha))
    where hX = sbTy s ws w hA
  sbTm s ws w (ty-Pair {a = a} {B = B} hA hB ha hb) =
    ty-Pair hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
            (sbTm s ws w ha) (trHT refl (subst-subst1-comm s B a) (sbTm s ws w hb))
    where hX = sbTy s ws w hA
  sbTm s ws w (ty-Fst hA hB ht) =
    ty-Fst hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTm s ws w ht)
    where hX = sbTy s ws w hA
  sbTm s ws w (ty-Snd {A = A} {t = t} {B} hA hB ht) =
    trHT refl (Eq-sym (subst-subst1-comm s B (Fst A (Lam A B) t)))
      (ty-Snd hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTm s ws w ht))
    where hX = sbTy s ws w hA
  sbTm s ws w (ty-Zero _) = ty-Zero w
  sbTm s ws w (ty-Suc h) = ty-Suc (sbTm s ws w h)
  sbTm s ws w (ty-Rec {k = k} {C} hC hz hs hk) =
    trHT refl (Eq-sym (subst-subst1-comm s C k))
      (ty-Rec (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hC)
              (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
              (trHT refl (subst-RecStep s C) (sbTm s ws w hs))
              (sbTm s ws w hk))
    where hX = isty-Nat w
  sbTm s ws w (ty-PiV ha hb) =
    ty-PiV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbTm s ws w (ty-SigV ha hb) =
    ty-SigV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbTm s ws w (ty-NatV _) = ty-NatV w
  sbTm s ws w (ty-UV {f = f} hf hg) =
    ty-UV (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg))
  sbTm s ws w (ty-PiU {f = f} {g} ha hb) =
    ty-PiU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbTm s ws w (ty-SigU {f = f} {g} ha hb) =
    ty-SigU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbTm s ws w (ty-NatU hU) = ty-NatU (sbTy s ws w hU)
  sbTm s ws w (ty-Fhat {f = f} {g} hf hg ha hb) =
    ty-Fhat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbTm s ws w (ty-Ghat {f = f} {g} hf hg ha hb hc) =
    ty-Ghat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
      (sbTm s ws w hc)
    where hX = isty-ElU (sbTm s ws w ha)
  sbTm s ws w (ty-That h) = ty-That (sbTm s ws w h)

  sbTE : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {A B : Expr n} -> TyEq G A B -> TyEq H (substExpr s A) (substExpr s B)
  sbTE s ws w (tyeq-refl h) = tyeq-refl (sbTy s ws w h)
  sbTE s ws w (tyeq-sym q) = tyeq-sym (sbTE s ws w q)
  sbTE s ws w (tyeq-trans q q') = tyeq-trans (sbTE s ws w q) (sbTE s ws w q')
  sbTE s ws w (tyeq-ElV c) = tyeq-ElV (sbCv s ws w c)
  sbTE s ws w (tyeq-ElU c) = tyeq-ElU (sbCv s ws w c)
  sbTE s ws w (tyeq-TyU {f = f} hf hg cf cg) =
    tyeq-TyU (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbCv s ws w cf)
             (trCv refl refl (subst-OpG s f) (sbCv s ws w cg))
  sbTE s ws w (tyeq-Pi hA hB hB' qA qB) =
    tyeq-Pi hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
            (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB') (sbTE s ws w qA)
            (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB)
    where hX = sbTy s ws w hA
  sbTE s ws w (tyeq-Sigma hA hB hB' qA qB) =
    tyeq-Sigma hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
               (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB') (sbTE s ws w qA)
               (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB)
    where hX = sbTy s ws w hA
  sbTE s ws w (tyeq-El-PiV ha hb) =
    tyeq-El-PiV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbTE s ws w (tyeq-El-SigV ha hb) =
    tyeq-El-SigV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbTE s ws w (tyeq-El-NatV _) = tyeq-El-NatV w
  sbTE s ws w (tyeq-El-UV {f = f} hf hg) =
    tyeq-El-UV (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg))
  sbTE s ws w (tyeq-ElU-That h) = tyeq-ElU-That (sbTm s ws w h)

  sbCv : {n m : Num} {G : Ctx n} {H : Ctx m} (s : Sub m n) -> WtSub H G s -> WfCtx H ->
        {t u A : Expr n} -> ConvTm G t u A -> ConvTm H (substExpr s t) (substExpr s u) (substExpr s A)
  sbCv s ws w (conv-refl h) = conv-refl (sbTm s ws w h)
  sbCv s ws w (conv-sym c) = conv-sym (sbCv s ws w c)
  sbCv s ws w (conv-trans c c') = conv-trans (sbCv s ws w c) (sbCv s ws w c')
  sbCv s ws w (conv-conv c q) = conv-conv (sbCv s ws w c) (sbTE s ws w q)
  sbCv s ws w (conv-beta {a = a} {B} {t} hA hB ht ha) =
    trCv refl (Eq-sym (subst-subst1-comm s t a)) (Eq-sym (subst-subst1-comm s B a))
      (conv-beta hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
                 (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) ht) (sbTm s ws w ha))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-funext {A = A} {t} {t'} {B} hA hB ht ht' c) =
    conv-funext hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
                (sbTm s ws w ht) (sbTm s ws w ht')
      (trCv (subst-FunB s A B t) (subst-FunB s A B t') refl
            (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) c))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-fst-beta {a = a} {B = B} hA hB ha hb) =
    conv-fst-beta hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
                  (sbTm s ws w ha) (trHT refl (subst-subst1-comm s B a) (sbTm s ws w hb))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-snd-beta {a = a} {B = B} hA hB ha hb) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B a))
      (conv-snd-beta hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
                     (sbTm s ws w ha) (trHT refl (subst-subst1-comm s B a) (sbTm s ws w hb)))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-pairext {A = A} {t = t} {B = B} hA hB ht ht' cf cs) =
    conv-pairext hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB)
                 (sbTm s ws w ht) (sbTm s ws w ht') (sbCv s ws w cf)
                 (trCv refl refl (subst-subst1-comm s B (Fst A (Lam A B) t)) (sbCv s ws w cs))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-rec-zero {C = C} hC hz hs) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C Zero))
      (conv-rec-zero (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hC)
                     (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
                     (trHT refl (subst-RecStep s C) (sbTm s ws w hs)))
    where hX = isty-Nat w
  sbCv s ws w (conv-rec-suc {z = z} {s = sv} {k} {C} hC hz hs hk) =
    trCv refl (Eq-sym (subst-RecSuc s C z sv k)) (Eq-sym (subst-subst1-comm s C (Suc k)))
      (conv-rec-suc (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hC)
                    (trHT refl (subst-subst1-comm s C Zero) (sbTm s ws w hz))
                    (trHT refl (subst-RecStep s C) (sbTm s ws w hs))
                    (sbTm s ws w hk))
    where hX = isty-Nat w
  sbCv s ws w (conv-Lam hA hB q c) =
    conv-Lam hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTE s ws w q)
             (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) c)
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-App {a = a} {B = B} hA hB qA qB c ca) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B a))
      (conv-App hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTE s ws w qA)
                (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB) (sbCv s ws w c) (sbCv s ws w ca))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-Pair {a = a} {B = B} hA hB qA qB ca cb) =
    conv-Pair hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTE s ws w qA)
              (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB) (sbCv s ws w ca)
              (trCv refl refl (subst-subst1-comm s B a) (sbCv s ws w cb))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-Fst hA hB qA qB c) =
    conv-Fst hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTE s ws w qA)
             (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB) (sbCv s ws w c)
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-Snd {A = A} {t = t} {B = B} hA hB qA qB c) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B (Fst A (Lam A B) t)))
      (conv-Snd hX (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hB) (sbTE s ws w qA)
                (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) qB) (sbCv s ws w c))
    where hX = sbTy s ws w hA
  sbCv s ws w (conv-Suc c) = conv-Suc (sbCv s ws w c)
  sbCv s ws w (conv-Rec {k = k} {C = C} hC hC' q cz cs ck) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C k))
      (conv-Rec (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hC)
                (sbTy (liftSub s) (liftWS ws hX) (wf-extend hX) hC')
                (sbTE (liftSub s) (liftWS ws hX) (wf-extend hX) q)
                (trCv refl refl (subst-subst1-comm s C Zero) (sbCv s ws w cz))
                (trCv refl refl (subst-RecStep s C) (sbCv s ws w cs))
                (sbCv s ws w ck))
    where hX = isty-Nat w
  sbCv s ws w (conv-PiV ha hb hb' ca cb) =
    conv-PiV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
             (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb') (sbCv s ws w ca)
             (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbCv s ws w (conv-SigV ha hb hb' ca cb) =
    conv-SigV (sbTm s ws w ha) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb)
              (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb') (sbCv s ws w ca)
              (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb)
    where hX = isty-ElV (sbTm s ws w ha)
  sbCv s ws w (conv-UV {f = f} hf hg cf cg) =
    conv-UV (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbCv s ws w cf)
            (trCv refl refl (subst-OpG s f) (sbCv s ws w cg))
  sbCv s ws w (conv-PiU {f = f} {g} ha hb hb' ca cb) =
    conv-PiU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb'))
      (sbCv s ws w ca)
      (trCv refl refl (subst-wk-comm s (TyU f g)) (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-SigU {f = f} {g} ha hb hb' ca cb) =
    conv-SigU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb'))
      (sbCv s ws w ca)
      (trCv refl refl (subst-wk-comm s (TyU f g)) (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-Fhat {f = f} {g} hf hg ha hb hb' ca cb) =
    conv-Fhat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb'))
      (sbCv s ws w ca)
      (trCv refl refl (subst-wk-comm s (TyU f g)) (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-Ghat {f = f} {g} hf hg ha hb hb' ca cb cc) =
    conv-Ghat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb'))
      (sbCv s ws w ca)
      (trCv refl refl (subst-wk-comm s (TyU f g)) (sbCv (liftSub s) (liftWS ws hX) (wf-extend hX) cb))
      (sbCv s ws w cc)
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-That c) = conv-That (sbCv s ws w c)
  sbCv s ws w (conv-That-PiU {f = f} {g} ha hb) =
    conv-That-PiU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-That-SigU {f = f} {g} ha hb) =
    conv-That-SigU (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-That-NatU hU) = conv-That-NatU (sbTy s ws w hU)
  sbCv s ws w (conv-That-Fhat {f = f} {g} hf hg ha hb) =
    conv-That-Fhat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
      (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-That-Ghat {f = f} {g} {a} {c} {b} hf hg ha hb hc) =
    trCv refl (Eq-sym (subst-gApp s f g (That a) (Lam (ElV (That a)) (That b)) c)) refl
      (conv-That-Ghat (sbTm s ws w hf) (trHT refl (subst-OpG s f) (sbTm s ws w hg)) (sbTm s ws w ha)
        (trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (liftWS ws hX) (wf-extend hX) hb))
        (sbTm s ws w hc))
    where hX = isty-ElU (sbTm s ws w ha)
  sbCv s ws w (conv-reflect ha hb c) = conv-reflect (sbTm s ws w ha) (sbTm s ws w hb) (sbCv s ws w c)

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
