{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Funct.agda
--
-- Functionality of substitution: pointwise convertible well-typed
-- substitutions (CSub, MIN's WtConvSub) send types to equal types and
-- terms to convertible terms.  The term case also returns the equality
-- of the substituted types; this replaces any use of inversion (e.g.
-- for Pi into a code U(f,g), whose type depends on the substitution).
-- Lam and Pair congruences are derived (funext + beta, pairext + beta).
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Funct where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Wf

record CSub {h g : Num} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) : Set where
  constructor csub
  field
    w1 : WtSub H G s
    w2 : WtSub H G s'
    cv : (i : Fin g) -> ConvTm H (s i) (s' i) (substExpr s (lookup G i))
    te : (i : Fin g) -> TyEq H (substExpr s (lookup G i)) (substExpr s' (lookup G i))
open CSub

-- conversion in a universe gives type equality
cvTE : {n : Num} {H : Ctx n} {u X Y : Expr n} -> Univ u -> ConvTm H X Y u -> TyEq H X Y
cvTE (univ-V refl) c = tyeq-el c
cvTE (univ-U f g refl) c = tyeq-el (conv-sub c)

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
  fTy s s' c w (isty-el h) = tyeq-el (fst (fTm s s' c w h))
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
  fTm s s' c w (ty-sub h) = conv-sub (fst (fTm s s' c w h)) , tyeq-refl (isty-V w)
  fTm s s' c w (ty-Pi {u = u} un hA hB) =
    conv-Pi uS (sbTm s (w1 c) w hA) hB1 hB2 cA
      (trCv refl refl (subst-wk-comm s u) (fst (fTm (liftSub s) (liftSub s') cU wU hB))) , eU
    where
      uS = substUniv s un
      ihA = fTm s s' c w hA
      cA = fst ihA
      eU = snd ihA
      hsA = elTy uS (sbTm s (w1 c) w hA)
      cU = liftC c hsA (cvTE uS cA)
      wU = wf-extend hsA
      hB1 = trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (w1 cU) wU hB)
      hB2 = ty-conv (trHT refl (subst-wk-comm s' u) (sbTm (liftSub s') (w2 cU) wU hB))
                    (wkTE hsA (tyeq-sym eU))
  fTm s s' c w (ty-Sigma {u = u} un hA hB) =
    conv-Sigma uS (sbTm s (w1 c) w hA) hB1 hB2 cA
      (trCv refl refl (subst-wk-comm s u) (fst (fTm (liftSub s) (liftSub s') cU wU hB))) , eU
    where
      uS = substUniv s un
      ihA = fTm s s' c w hA
      cA = fst ihA
      eU = snd ihA
      hsA = elTy uS (sbTm s (w1 c) w hA)
      cU = liftC c hsA (cvTE uS cA)
      wU = wf-extend hsA
      hB1 = trHT refl (subst-wk-comm s u) (sbTm (liftSub s) (w1 cU) wU hB)
      hB2 = ty-conv (trHT refl (subst-wk-comm s' u) (sbTm (liftSub s') (w2 cU) wU hB))
                    (wkTE hsA (tyeq-sym eU))
  fTm s s' c w (ty-Nat-V _) = conv-refl (ty-Nat-V w) , tyeq-refl (isty-V w)
  fTm s s' c w (ty-Nat-U h) =
    conv-refl (ty-Nat-U (sbTm s (w1 c) w h)) , tyeq-el (fst (fTm s s' c w h))
  fTm s s' c w (ty-Ucode {f = f} hf hg) =
    conv-Ucode (sbTm s (w1 c) w hf) (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg))
      (fst (fTm s s' c w hf)) (trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg))) ,
    tyeq-refl (isty-V w)
  fTm s s' c w (ty-Fhat {f = f} {g} hf hg hA hB) =
    conv-Fhat cf cg (sbTm s (w1 c) w hA) hB1 hB2 cA
      (trCv refl refl (subst-wk-comm s (Ucode f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hB))) ,
    eUc
    where
      cf = fst (fTm s s' c w hf)
      cg = trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg))
      eUc = tyeq-el (conv-Ucode (sbTm s (w1 c) w hf)
                       (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg)) cf cg)
      cA = fst (fTm s s' c w hA)
      hsA = isty-el (ty-sub (sbTm s (w1 c) w hA))
      cU = liftC c hsA (tyeq-el (conv-sub cA))
      wU = wf-extend hsA
      hB1 = trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (w1 cU) wU hB)
      hB2 = ty-conv (trHT refl (subst-wk-comm s' (Ucode f g)) (sbTm (liftSub s') (w2 cU) wU hB))
                    (wkTE hsA (tyeq-sym eUc))
  fTm s s' c w (ty-Ghat {f = f} {g} hf hg hA hB hc) =
    conv-Ghat cf cg (sbTm s (w1 c) w hA) hB1 hB2 cA
      (trCv refl refl (subst-wk-comm s (Ucode f g)) (fst (fTm (liftSub s) (liftSub s') cU wU hB)))
      (fst (fTm s s' c w hc)) ,
    eUc
    where
      cf = fst (fTm s s' c w hf)
      cg = trCv refl refl (subst-OpG s f) (fst (fTm s s' c w hg))
      eUc = tyeq-el (conv-Ucode (sbTm s (w1 c) w hf)
                       (trHT refl (subst-OpG s f) (sbTm s (w1 c) w hg)) cf cg)
      cA = fst (fTm s s' c w hA)
      hsA = isty-el (ty-sub (sbTm s (w1 c) w hA))
      cU = liftC c hsA (tyeq-el (conv-sub cA))
      wU = wf-extend hsA
      hB1 = trHT refl (subst-wk-comm s (Ucode f g)) (sbTm (liftSub s) (w1 cU) wU hB)
      hB2 = ty-conv (trHT refl (subst-wk-comm s' (Ucode f g)) (sbTm (liftSub s') (w2 cU) wU hB))
                    (wkTE hsA (tyeq-sym eUc))
  fTm {H = H} s s' c w (ty-Lam {A = A} {B} {t} hA hB ht) =
    conv-funext hsA hsB hL hL' body , eP
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      hs'A = sbTy s' (w2 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      qB = fTy (liftSub s) (liftSub s') cU wU hB
      hsB = sbTy (liftSub s) (w1 cU) wU hB
      eP = tyeq-Pi hsA hsB (sbTy (liftSub s') (w2 cU) wU hB) qA qB
      hL = sbTm s (w1 c) w (ty-Lam hA hB ht)
      hL' = ty-conv (sbTm s' (w2 c) w (ty-Lam hA hB ht)) (tyeq-sym eP)
      ct = fst (fTm (liftSub s) (liftSub s') cU wU ht)
      hst = sbTm (liftSub s) (w1 cU) wU ht
      -- s' lifted in its own context
      wsP = liftWS (w2 c) hs'A
      wP = wf-extend hs'A
      hs'B = sbTy (liftSub s') wsP wP hB
      hs't = sbTm (liftSub s') wsP wP ht
      -- beta on the left
      wA0 = wkTy hsA hsA
      rtL = liftRT {A = substExpr s A} (wkRT {G = H} {C = substExpr s A})
      betaL = trCv refl (subst1-liftWk-cancel (substExpr (liftSub s) t))
                (subst1-liftWk-cancel (substExpr (liftSub s) B))
                (conv-beta wA0 (rTy (liftRen wkRen) rtL (wf-extend wA0) hsB)
                           (rTm (liftRen wkRen) rtL (wf-extend wA0) hst) (ty-var wU))
      -- beta on the right
      wA1 = wkTy hsA hs'A
      rtR = liftRT {A = substExpr s' A} (wkRT {G = H} {C = substExpr s A})
      betaR = trCv refl (subst1-liftWk-cancel (substExpr (liftSub s') t))
                (subst1-liftWk-cancel (substExpr (liftSub s') B))
                (conv-beta wA1 (rTy (liftRen wkRen) rtR (wf-extend wA1) hs'B)
                           (rTm (liftRen wkRen) rtR (wf-extend wA1) hs't)
                           (ty-conv (ty-var wU) (wkTE hsA qA)))
      body = conv-trans betaL (conv-trans ct (conv-sym (conv-conv betaR (tyeq-sym qB))))
  fTm s s' c w (ty-App {a = a} {B} hA hB ht ha) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B a))
      (conv-App hsA (sbTy (liftSub s) (liftWS (w1 c) hsA) (wf-extend hsA) hB)
                (fst (fTm s s' c w ht)) ca) ,
    trTE (substCons s B a) (substCons s' B a)
      (fTy (consSub s (substExpr s a)) (consSub s' (substExpr s' a))
           (consC c (sbTm s (w1 c) w ha) (sbTm s' (w2 c) w ha) ca (snd iha)) w hB)
    where
      hsA = sbTy s (w1 c) w hA
      iha = fTm s s' c w ha
      ca = fst iha
  fTm s s' c w (ty-Pair {A = A} {t} {u} {B} hA hB ht hu) =
    conv-pairext hsA hsB hP hP' cf (conv-conv cs0 eF) , eS
    where
      qA = fTy s s' c w hA
      hsA = sbTy s (w1 c) w hA
      hs'A = sbTy s' (w2 c) w hA
      cU = liftC c hsA qA
      wU = wf-extend hsA
      qB = fTy (liftSub s) (liftSub s') cU wU hB
      hsB = sbTy (liftSub s) (w1 cU) wU hB
      hs'B = sbTy (liftSub s') (liftWS (w2 c) hs'A) (wf-extend hs'A) hB
      eS = tyeq-Sigma hsA hsB (sbTy (liftSub s') (w2 cU) wU hB) qA qB
      hP = sbTm s (w1 c) w (ty-Pair hA hB ht hu)
      hP' = ty-conv (sbTm s' (w2 c) w (ty-Pair hA hB ht hu)) (tyeq-sym eS)
      hst = sbTm s (w1 c) w ht
      hs't = sbTm s' (w2 c) w ht
      hsu = trHT refl (subst-subst1-comm s B t) (sbTm s (w1 c) w hu)
      hs'u = trHT refl (subst-subst1-comm s' B t) (sbTm s' (w2 c) w hu)
      iht = fTm s s' c w ht
      ct = fst iht
      fbL = conv-fst-beta hsA hsB hst hsu
      fbR = conv-conv (conv-fst-beta hs'A hs'B hs't hs'u) (tyeq-sym qA)
      cf = conv-trans fbL (conv-trans ct (conv-sym fbR))
      sbL = conv-snd-beta hsA hsB hst hsu
      cu = trCv refl refl (subst-subst1-comm s B t) (fst (fTm s s' c w hu))
      eT = trTE (subst-consSub s (substExpr s t) B) (subst-consSub s' (substExpr s' t) B)
             (fTy (consSub s (substExpr s t)) (consSub s' (substExpr s' t))
                  (consC c hst hs't ct (snd iht)) w hB)
      sbR = conv-conv (conv-snd-beta hs'A hs'B hs't hs'u) (tyeq-sym eT)
      cs0 = conv-trans sbL (conv-trans cu (conv-sym sbR))
      hFst = ty-Fst hsA hsB hP
      eF = trTE (subst-consSub s (substExpr s t) B) (subst-consSub s _ B)
             (fTy (consSub s (substExpr s t)) (consSub s (Fst (substExpr s (Pair t u))))
                  (consC (reflC (wfTy hA) (w1 c) w) hst hFst (conv-sym fbL) (tyeq-refl hsA))
                  w hB)
  fTm s s' c w (ty-Fst hA hB ht) =
    conv-Fst (sbTy s (w1 c) w hA)
             (sbTy (liftSub s) (liftWS (w1 c) (sbTy s (w1 c) w hA)) (wf-extend (sbTy s (w1 c) w hA)) hB)
             (fst (fTm s s' c w ht)) ,
    fTy s s' c w hA
  fTm s s' c w (ty-Snd {A = A} {t} {B} hA hB ht) =
    trCv refl refl (Eq-sym (subst-subst1-comm s B (Fst t))) (conv-Snd hsA hsB ct) ,
    trTE (substCons s B (Fst t)) (substCons s' B (Fst t))
      (fTy (consSub s (Fst (substExpr s t))) (consSub s' (Fst (substExpr s' t)))
           (consC c (ty-Fst hsA hsB (sbTm s (w1 c) w ht)) (ty-Fst hs'A hs'B (sbTm s' (w2 c) w ht))
                  (conv-Fst hsA hsB ct) (fTy s s' c w hA))
           w hB)
    where
      hsA = sbTy s (w1 c) w hA
      hsB = sbTy (liftSub s) (liftWS (w1 c) hsA) (wf-extend hsA) hB
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
