{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Funct.agda
--
-- Functionality of substitution for MAHLORT/TarskiTyping (port of
-- MAHLOINJ): pointwise convertible well-typed substitutions (CSub) send
-- types to equal types and terms to convertible terms; the term case
-- also returns the equality of the substituted types.  Lam and Pair use
-- the primitive conv-Lam / conv-Pair; the codes of U_{f,g}, whose f, g
-- move under the substitution, use the reflection-derived congruences
-- of CodeCong.
------------------------------------------------------------------------

module MAHLORT.Syntax.Funct where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.CodeCong

record CSub {h g : Num} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) : Set where
  constructor csub
  field
    w1 : WtSub H G s
    w2 : WtSub H G s'
    cv : (i : Fin g) -> ConvTm H (s i) (s' i) (substExpr s (lookup G i))
    te : (i : Fin g) -> TyEq H (substExpr s (lookup G i)) (substExpr s' (lookup G i))
open CSub

substCons : {h g : Num} (r : Sub h g) (B : Expr (suc g)) (x : Expr g) ->
  Eq (substExpr (consSub r (substExpr r x)) B) (substExpr r (subst1 B x))
substCons r B x = Eq-trans (subst-consSub r (substExpr r x) B) (Eq-sym (subst-subst1-comm r B x))

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} where

  liftC : CSub H G s s' -> {A : Expr g} -> IsType H (substExpr s A) ->
          TyEq H (substExpr s A) (substExpr s' A) ->
          CSub (extend H (substExpr s A)) (extend G A) (liftSub s) (liftSub s')
  liftC c {A} hA qA = csub (liftWS (w1 c) hA) w2' cv' te'
    where
      w2' : WtSub (extend H (substExpr s A)) (extend G A) (liftSub s')
      w2' fzero =
        trHT refl (Eq-sym (subst-wk-comm s' A)) (ty-conv (ty-var (wf-extend hA)) (wkTE hA qA))
      w2' (fsuc i) = trHT refl (Eq-sym (subst-wk-comm s' (lookup G i))) (wkTm hA (w2 c i))
      cv' : (i : Fin (suc g)) -> ConvTm (extend H (substExpr s A)) (liftSub s i) (liftSub s' i)
              (substExpr (liftSub s) (lookup (extend G A) i))
      cv' fzero =
        trCv refl refl (Eq-sym (subst-wk-comm s A)) (conv-refl (ty-var (wf-extend hA)))
      cv' (fsuc i) = trCv refl refl (Eq-sym (subst-wk-comm s (lookup G i))) (wkCv hA (cv c i))
      te' : (i : Fin (suc g)) -> TyEq (extend H (substExpr s A))
              (substExpr (liftSub s) (lookup (extend G A) i))
              (substExpr (liftSub s') (lookup (extend G A) i))
      te' fzero = trTE (Eq-sym (subst-wk-comm s A)) (Eq-sym (subst-wk-comm s' A)) (wkTE hA qA)
      te' (fsuc i) =
        trTE (Eq-sym (subst-wk-comm s (lookup G i))) (Eq-sym (subst-wk-comm s' (lookup G i)))
             (wkTE hA (te c i))

  consC : CSub H G s s' -> {A : Expr g} {a a' : Expr h} ->
          HasType H a (substExpr s A) -> HasType H a' (substExpr s' A) ->
          ConvTm H a a' (substExpr s A) -> TyEq H (substExpr s A) (substExpr s' A) ->
          CSub H (extend G A) (consSub s a) (consSub s' a')
  consC c {A} {a} {a'} ha ha' ca qa = csub w1' w2' cv' te'
    where
      w1' : WtSub H (extend G A) (consSub s a)
      w1' fzero = trHT refl (Eq-sym (consSub-wk s a A)) ha
      w1' (fsuc i) = trHT refl (Eq-sym (consSub-wk s a (lookup G i))) (w1 c i)
      w2' : WtSub H (extend G A) (consSub s' a')
      w2' fzero = trHT refl (Eq-sym (consSub-wk s' a' A)) ha'
      w2' (fsuc i) = trHT refl (Eq-sym (consSub-wk s' a' (lookup G i))) (w2 c i)
      cv' : (i : Fin (suc g)) -> ConvTm H (consSub s a i) (consSub s' a' i)
              (substExpr (consSub s a) (lookup (extend G A) i))
      cv' fzero = trCv refl refl (Eq-sym (consSub-wk s a A)) ca
      cv' (fsuc i) = trCv refl refl (Eq-sym (consSub-wk s a (lookup G i))) (cv c i)
      te' : (i : Fin (suc g)) -> TyEq H (substExpr (consSub s a) (lookup (extend G A) i))
              (substExpr (consSub s' a') (lookup (extend G A) i))
      te' fzero = trTE (Eq-sym (consSub-wk s a A)) (Eq-sym (consSub-wk s' a' A)) qa
      te' (fsuc i) =
        trTE (Eq-sym (consSub-wk s a (lookup G i))) (Eq-sym (consSub-wk s' a' (lookup G i)))
             (te c i)

-- a well-typed substitution is convertible to itself
reflC : {h g : Num} {H : Ctx h} {G : Ctx g} {s : Sub h g} ->
        WfCtx G -> WtSub H G s -> WfCtx H -> CSub H G s s
reflC {s = s} wG ws w =
  csub ws ws (\ i -> conv-refl (ws i)) (\ i -> tyeq-refl (sbTy s ws w (lookupTy wG i)))

------------------------------------------------------------------------
-- The functionality lemma
------------------------------------------------------------------------

mutual
  fTy : {h g : Num} {H : Ctx h} {G : Ctx g} (s s' : Sub h g) -> CSub H G s s' -> WfCtx H ->
        {A : Expr g} -> IsType G A -> TyEq H (substExpr s A) (substExpr s' A)
  fTy s s' c w (isty-V _) = tyeq-refl (isty-V w)
  fTy s s' c w (isty-ElV h) = tyeq-ElV (fst (fTm s s' c w h))
  fTy s s' c w (isty-TyU {f = f} hf hg) =
    tyeq-TyU (sbTm s (w1 c) w hf) (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg))
             (fst (fTm s s' c w hf)) (trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg)))
  fTy s s' c w (isty-ElU h) = elUEq (sbTm s (w1 c) w h) (sbTm s' (w2 c) w h) (fst (fTm s s' c w h))
  fTy s s' c w (isty-Pi hA hB) =
    tyeq-Pi hsA (sbTy (liftSub s) (w1 cU) wU hB) (sbTy (liftSub s') (w2 cU) wU hB)
            qA (fTy (liftSub s) (liftSub s') cU wU hB)
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
  fTy s s' c w (isty-Sigma hA hB) =
    tyeq-Sigma hsA (sbTy (liftSub s) (w1 cU) wU hB) (sbTy (liftSub s') (w2 cU) wU hB)
               qA (fTy (liftSub s) (liftSub s') cU wU hB)
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
  fTy s s' c w (isty-Nat _) = tyeq-refl (isty-Nat w)

  fTm : {h g : Num} {H : Ctx h} {G : Ctx g} (s s' : Sub h g) -> CSub H G s s' -> WfCtx H ->
        {t A : Expr g} -> HasType G t A ->
        ConvTm H (substExpr s t) (substExpr s' t) (substExpr s A) *
        TyEq H (substExpr s A) (substExpr s' A)
  fTm s s' c w (ty-var {i = i} _) = cv c i , te c i
  fTm s s' c w (ty-conv h q) =
    conv-conv (fst ih) qs , tyeq-trans (tyeq-sym qs) (tyeq-trans (snd ih) qs')
    where
      ih = fTm s s' c w h
      qs = sbTE s (w1 c) w q
      qs' = sbTE s' (w2 c) w q
  fTm s s' c w (ty-Lam hA hB ht) =
    conv-Lam hsA hsB qA (fst (fTm (liftSub s) (liftSub s') cU wU ht)) ,
    tyeq-Pi hsA hsB (sbTy (liftSub s') (w2 cU) wU hB) qA (fTy (liftSub s) (liftSub s') cU wU hB)
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      hsB = sbTy (liftSub s) (w1 cU) wU hB
  fTm s s' c w (ty-App {a = a} {B} hA hB ht ha) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B a))
      (conv-App hsA (sbTy (liftSub s) (w1 cU) wU hB) qA (fTy (liftSub s) (liftSub s') cU wU hB)
                (fst (fTm s s' c w ht)) ca) ,
    trTE (substCons s B a) (substCons s' B a)
      (fTy (consSub s (substExpr s a)) (consSub s' (substExpr s' a))
           (consC c (sbTm s (w1 c) w ha) (sbTm s' (w2 c) w ha) ca (snd iha)) w hB)
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      iha = fTm s s' c w ha
      ca = fst iha
  fTm s s' c w (ty-Pair {a = a} {B = B} hA hB ha hb) =
    conv-Pair hsA hsB qA qB (fst (fTm s s' c w ha))
      (trCv refl refl (subst-subst1-comm s B a) (fst (fTm s s' c w hb))) ,
    tyeq-Sigma hsA hsB (sbTy (liftSub s') (w2 cU) wU hB) qA qB
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      hsB = sbTy (liftSub s) (w1 cU) wU hB
      qB = fTy (liftSub s) (liftSub s') cU wU hB
  fTm s s' c w (ty-Fst hA hB ht) =
    conv-Fst hsA (sbTy (liftSub s) (w1 cU) wU hB) qA (fTy (liftSub s) (liftSub s') cU wU hB)
             (fst (fTm s s' c w ht)) ,
    qA
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
  fTm s s' c w (ty-Snd {A = A} {t} {B} hA hB ht) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B (Fst A (Lam A B) t))) (conv-Snd hsA hsB qA qB ct) ,
    trTE (substCons s B (Fst A (Lam A B) t)) (substCons s' B (Fst A (Lam A B) t))
      (fTy (consSub s (substExpr s (Fst A (Lam A B) t))) (consSub s' (substExpr s' (Fst A (Lam A B) t)))
           (consC c (ty-Fst hsA hsB (sbTm s (w1 c) w ht)) (ty-Fst hs'A hs'B (sbTm s' (w2 c) w ht))
                  (conv-Fst hsA hsB qA qB ct) qA)
           w hB)
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      hsB = sbTy (liftSub s) (w1 cU) wU hB
      qB = fTy (liftSub s) (liftSub s') cU wU hB
      hs'A = sbTy s' (w2 c) w hA
      hs'B = sbTy (liftSub s') (liftWS (w2 c) hs'A) (wf-extend hs'A) hB
      ct = fst (fTm s s' c w ht)
  fTm s s' c w (ty-Zero _) = conv-refl (ty-Zero w) , tyeq-refl (NatTy w)
  fTm s s' c w (ty-Suc h) = conv-Suc (fst (fTm s s' c w h)) , tyeq-refl (NatTy w)
  fTm s s' c w (ty-Rec {k = k} {C} hC hz hs hk) =
    trCv refl refl (Eq-sym (subst-subst1-comm s C k))
      (conv-Rec (sbTy (liftSub s) (w1 cU) wU hC) (sbTy (liftSub s') (w2 cU) wU hC)
                (fTy (liftSub s) (liftSub s') cU wU hC)
                (trCv refl refl (subst-subst1-comm s C Zero) (fst (fTm s s' c w hz)))
                (trCv refl refl (subst-RecStep s C) (fst (fTm s s' c w hs)))
                ck) ,
    trTE (substCons s C k) (substCons s' C k)
      (fTy (consSub s (substExpr s k)) (consSub s' (substExpr s' k))
           (consC c (sbTm s (w1 c) w hk) (sbTm s' (w2 c) w hk) ck (snd ihk)) w hC)
    where
      cU = liftC c (NatTy w) (tyeq-refl (NatTy w))
      wU = wf-extend (NatTy w)
      ihk = fTm s s' c w hk
      ck = fst ihk
  fTm s s' c w (ty-PiV ha hb) =
    conv-PiV hsa (sbTm (liftSub s) (w1 cU) wU hb) (sbTm (liftSub s') (w2 cU) wU hb) ca
             (fst (fTm (liftSub s) (liftSub s') cU wU hb)) ,
    tyeq-refl (isty-V w)
    where
      hsa = sbTm s (w1 c) w ha
      ca = fst (fTm s s' c w ha)
      cU = liftC c (isty-ElV hsa) (tyeq-ElV ca)
      wU = wf-extend (isty-ElV hsa)
  fTm s s' c w (ty-SigV ha hb) =
    conv-SigV hsa (sbTm (liftSub s) (w1 cU) wU hb) (sbTm (liftSub s') (w2 cU) wU hb) ca
              (fst (fTm (liftSub s) (liftSub s') cU wU hb)) ,
    tyeq-refl (isty-V w)
    where
      hsa = sbTm s (w1 c) w ha
      ca = fst (fTm s s' c w ha)
      cU = liftC c (isty-ElV hsa) (tyeq-ElV ca)
      wU = wf-extend (isty-ElV hsa)
  fTm s s' c w (ty-NatV _) = conv-refl (ty-NatV w) , tyeq-refl (isty-V w)
  fTm s s' c w (ty-UV {f = f} hf hg) =
    conv-UV (sbTm s (w1 c) w hf) (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg))
      (fst (fTm s s' c w hf)) (trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg))) ,
    tyeq-refl (isty-V w)
  fTm s s' c w (ty-PiU {f = f} {g} ha hb) =
    ccPiU hsa hs'a ca hsb hs'b cb eU , eU
    where
      iha = fTm s s' c w ha
      ca = fst iha
      eU = snd iha
      hsa = sbTm s (w1 c) w ha
      hs'a = sbTm s' (w2 c) w ha
      cU = liftC c (isty-ElU hsa) (elUEq hsa hs'a ca)
      wU = wf-extend (isty-ElU hsa)
      hsb = trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (w1 cU) wU hb)
      hs'b = trHT refl (subst-wk-comm s' (TyU f g))
               (sbTm (liftSub s') (liftWS (w2 c) (isty-ElU hs'a)) (wf-extend (isty-ElU hs'a)) hb)
      cb = trCv refl refl (subst-wk-comm s (TyU f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hb))
  fTm s s' c w (ty-SigU {f = f} {g} ha hb) =
    ccSigU hsa hs'a ca hsb hs'b cb eU , eU
    where
      iha = fTm s s' c w ha
      ca = fst iha
      eU = snd iha
      hsa = sbTm s (w1 c) w ha
      hs'a = sbTm s' (w2 c) w ha
      cU = liftC c (isty-ElU hsa) (elUEq hsa hs'a ca)
      wU = wf-extend (isty-ElU hsa)
      hsb = trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (w1 cU) wU hb)
      hs'b = trHT refl (subst-wk-comm s' (TyU f g))
               (sbTm (liftSub s') (liftWS (w2 c) (isty-ElU hs'a)) (wf-extend (isty-ElU hs'a)) hb)
      cb = trCv refl refl (subst-wk-comm s (TyU f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hb))
  fTm s s' c w (ty-NatU hU) =
    ccNatU (sbTy s (w1 c) w hU) (sbTy s' (w2 c) w hU) eU , eU
    where eU = fTy s s' c w hU
  fTm s s' c w (ty-Fhat {f = f} {g} hf hg ha hb) =
    ccFhat hsa hs'a ca hsb hs'b cb eU (sbTm s (w1 c) w hf) (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg))
      (sbTm s' (w2 c) w hf) (trHT refl (subst-OpG s' f) (sbTm s' (w2 c) w hg)) (fst (fTm s s' c w hf)) ,
    eU
    where
      iha = fTm s s' c w ha
      ca = fst iha
      eU = snd iha
      hsa = sbTm s (w1 c) w ha
      hs'a = sbTm s' (w2 c) w ha
      cU = liftC c (isty-ElU hsa) (elUEq hsa hs'a ca)
      wU = wf-extend (isty-ElU hsa)
      hsb = trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (w1 cU) wU hb)
      hs'b = trHT refl (subst-wk-comm s' (TyU f g))
               (sbTm (liftSub s') (liftWS (w2 c) (isty-ElU hs'a)) (wf-extend (isty-ElU hs'a)) hb)
      cb = trCv refl refl (subst-wk-comm s (TyU f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hb))
  fTm s s' c w (ty-Ghat {f = f} {g} hf hg ha hb hc) =
    ccGhat hsa hs'a ca hsb hs'b cb eU (sbTm s (w1 c) w hf) (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg))
      (sbTm s' (w2 c) w hf) (trHT refl (subst-OpG s' f) (sbTm s' (w2 c) w hg)) (fst (fTm s s' c w hf))
      (trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg)))
      (sbTm s (w1 c) w hc) (sbTm s' (w2 c) w hc) (fst (fTm s s' c w hc)) ,
    eU
    where
      iha = fTm s s' c w ha
      ca = fst iha
      eU = snd iha
      hsa = sbTm s (w1 c) w ha
      hs'a = sbTm s' (w2 c) w ha
      cU = liftC c (isty-ElU hsa) (elUEq hsa hs'a ca)
      wU = wf-extend (isty-ElU hsa)
      hsb = trHT refl (subst-wk-comm s (TyU f g)) (sbTm (liftSub s) (w1 cU) wU hb)
      hs'b = trHT refl (subst-wk-comm s' (TyU f g))
               (sbTm (liftSub s') (liftWS (w2 c) (isty-ElU hs'a)) (wf-extend (isty-ElU hs'a)) hb)
      cb = trCv refl refl (subst-wk-comm s (TyU f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hb))
  fTm s s' c w (ty-That h) = conv-That (fst (fTm s s' c w h)) , tyeq-refl (isty-V w)

------------------------------------------------------------------------
-- Single substitution of convertible terms
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} {A a a' : Expr n} (w : WfCtx G) (hA : IsType G A)
         (ha : HasType G a A) (ha' : HasType G a' A) (ca : ConvTm G a a' A) where

  s1C : CSub G (extend G A) (subst1Sub a) (subst1Sub a')
  s1C = csub (ws1 w ha) (ws1 w ha') cv' te'
    where
      cv' : (i : Fin (suc n)) -> ConvTm G (subst1Sub a i) (subst1Sub a' i)
              (substExpr (subst1Sub a) (lookup (extend G A) i))
      cv' fzero = trCv refl refl (Eq-sym (subst1-wk A a)) ca
      cv' (fsuc i) = trCv refl refl (Eq-sym (subst1-wk (lookup G i) a))
                       (conv-refl (ty-var w))
      te' : (i : Fin (suc n)) -> TyEq G (substExpr (subst1Sub a) (lookup (extend G A) i))
              (substExpr (subst1Sub a') (lookup (extend G A) i))
      te' fzero = trTE (Eq-sym (subst1-wk A a)) (Eq-sym (subst1-wk A a'))
                       (tyeq-refl hA)
      te' (fsuc i) = trTE (Eq-sym (subst1-wk (lookup G i) a)) (Eq-sym (subst1-wk (lookup G i) a'))
                          (tyeq-refl (lookupTy w i))

  -- B[a] = B[a'] and t[a] = t[a'] for a = a'
  s1fTy : {B : Expr (suc n)} -> IsType (extend G A) B -> TyEq G (subst1 B a) (subst1 B a')
  s1fTy = fTy (subst1Sub a) (subst1Sub a') s1C w

  s1fTm : {t B : Expr (suc n)} -> HasType (extend G A) t B ->
          ConvTm G (subst1 t a) (subst1 t a') (subst1 B a)
  s1fTm h = fst (fTm (subst1Sub a) (subst1Sub a') s1C w h)
