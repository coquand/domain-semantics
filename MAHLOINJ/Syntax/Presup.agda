{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Presup.agda
--
-- Presupposition for MAHLO/Typing.agda:
--   G |- t : A      ==>  G |- A
--   G |- A = B      ==>  G |- A  and  G |- B
--   G |- t = u : A  ==>  G |- t : A  and  G |- u : A
-- together with the typing of the operator types (OpF, OpG f) and
--   G |- f = f' : OpF  ==>  G |- OpG f = OpG f'.
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Presup where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.CtxConv
open import MAHLOINJ.Syntax.Funct

------------------------------------------------------------------------
-- The operator types
------------------------------------------------------------------------

-- X -> V
arrV : {n : Num} {G : Ctx n} {X : Expr n} -> IsType G X -> IsType G (Arr X V)
arrV hX = isty-Pi hX (isty-V (wf-extend hX))

-- (x0 -> V) -> V  in  (G, V)
bodyF : {n : Num} {G : Ctx n} -> WfCtx G -> IsType (extend G V) (Arr (Arr x0 V) V)
bodyF w = arrV (arrV (isty-el (ty-var (wf-extend (isty-V w)))))

opFTy : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G OpF
opFTy w = isty-Pi (isty-V w) (bodyF w)

-- f A F : V  in the context  (G, A : V, F : A -> V)  for f : OpF
private
  ctx2 : {n : Num} -> Ctx n -> Ctx (suc (suc n))
  ctx2 G = extend (extend G V) (Arr x0 V)

  w2 : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctx2 G)
  w2 w = wf-extend (arrV (isty-el (ty-var (wf-extend (isty-V w)))))

faV : {n : Num} {G : Ctx n} {ff : Expr (suc (suc n))} -> WfCtx G ->
      HasType (ctx2 G) ff OpF -> HasType (ctx2 G) (App (App ff x1) x0) V
faV w hff =
  ty-App (arrV (isty-el x1V)) (isty-V (wf-extend (arrV (isty-el x1V))))
    (ty-App (isty-V (w2 w)) (bodyF (w2 w)) hff x1V)
    (ty-var (w2 w))
  where
    x1V = ty-var {i = fsuc fzero} (w2 w)

-- OpG f is a type
opGBody : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF ->
          IsType (extend G V) (PiB (Arr x0 V) (Arr (App (App (wkExpr (wkExpr f)) x1) x0) V))
opGBody w hf =
  isty-Pi h1 (arrV (isty-el (faV w (wkTm h1 (wkTm (isty-V w) hf)))))
  where h1 = arrV (isty-el (ty-var (wf-extend (isty-V w))))

opGTy : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF -> IsType G (OpG f)
opGTy w hf = isty-Pi (isty-V w) (opGBody w hf)

-- f = f' : OpF  ==>  OpG f = OpG f'
opGEq : {n : Num} {G : Ctx n} {f f' : Expr n} -> WfCtx G ->
        HasType G f OpF -> HasType G f' OpF -> ConvTm G f f' OpF -> TyEq G (OpG f) (OpG f')
opGEq w hf hf' cf =
  s1fTy w (opFTy w) hf hf' cf (opGTy (wf-extend (opFTy w)) (ty-var (wf-extend (opFTy w))))

------------------------------------------------------------------------
-- Auxiliary typings for the right-hand sides of delta-g and rec-suc
------------------------------------------------------------------------

private
  -- substitution  x0 := S x0  is well typed in  (G, Nat)
  wsSuc : {n : Num} {G : Ctx n} -> WfCtx G -> WtSub (extend G Nat) (extend G Nat) sucSub
  wsSuc w fzero = ty-Suc (ty-var (wf-extend (NatTy w)))
  wsSuc {G = G} w (fsuc i) =
    trHT refl (Eq-sym (sucSub-wk (lookup G i))) (ty-var (wf-extend (NatTy w)))

  cS-Ty : {n : Num} {G : Ctx n} {C : Expr (suc n)} -> WfCtx G ->
          IsType (extend G Nat) C -> IsType (extend G Nat) (substExpr sucSub C)
  cS-Ty w hC = sbTy sucSub (wsSuc w) (wf-extend (NatTy w)) hC

  -- the type of the step at k
  stepE : {n : Num} (C : Expr (suc n)) (k : Expr n) ->
          Eq (subst1 (Arr C (substExpr sucSub C)) k) (Arr (subst1 C k) (subst1 C (Suc k)))
  stepE C k =
    Eq-cong (\ z -> Pi (subst1 C k) (Lam (subst1 C k) z))
      (Eq-trans (subst-wk-comm (subst1Sub k) (substExpr sucSub C))
                (Eq-cong wkExpr (subst1-sucSub C k)))

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

lamV : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} ->
       HasType G A (Ucode f g) -> HasType (extend G A) B (wkExpr (Ucode f g)) ->
       HasType G (Lam A B) (Arr A V)
lamV hA hB = ty-Lam hAty (isty-V (wf-extend hAty)) (ty-sub hB)
  where hAty = isty-el (ty-sub hA)


-- the right-hand side of delta-f:  f A (\x:A.B) : V
deltaF : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} ->
         HasType G f OpF -> HasType G A (Ucode f g) ->
         HasType (extend G A) B (wkExpr (Ucode f g)) ->
         HasType G (App (App f A) (Lam A B)) V
deltaF hf hA hB =
  ty-App (arrV hAty) (isty-V (wf-extend (arrV hAty)))
    (ty-App (isty-V (wfTm hf)) (bodyF (wfTm hf)) hf (ty-sub hA))
    (lamV hA hB)
  where hAty = isty-el (ty-sub hA)

------------------------------------------------------------------------
-- Presupposition
------------------------------------------------------------------------

mutual
  pTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> IsType G A
  pTm (ty-var {i = i} w) = lookupTy w i
  pTm (ty-conv h q) = snd (pTE q)
  pTm (ty-sub h) = isty-V (wfTm h)
  pTm (ty-Pi (univ-V refl) hA hB) = isty-V (wfTm hA)
  pTm (ty-Pi (univ-U f g refl) hA hB) = pTm hA
  pTm (ty-Sigma (univ-V refl) hA hB) = isty-V (wfTm hA)
  pTm (ty-Sigma (univ-U f g refl) hA hB) = pTm hA
  pTm (ty-Nat-V w) = isty-V w
  pTm (ty-Nat-U h) = isty-el h
  pTm (ty-Ucode hf hg) = isty-V (wfTm hf)
  pTm (ty-Fhat hf hg hA hB) = pTm hA
  pTm (ty-Ghat hf hg hA hB hc) = pTm hA
  pTm (ty-Lam hA hB ht) = isty-Pi hA hB
  pTm (ty-App hA hB ht ha) = s1Ty (wfTy hA) ha hB
  pTm (ty-Pair hA hB ht hu) = isty-Sigma hA hB
  pTm (ty-Fst hA hB ht) = hA
  pTm (ty-Snd hA hB ht) = s1Ty (wfTy hA) (ty-Fst hA hB ht) hB
  pTm (ty-Zero w) = NatTy w
  pTm (ty-Suc h) = NatTy (wfTm h)
  pTm (ty-Rec hC hz hs hk) = s1Ty (wfTm hk) hk hC

  pTE : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> IsType G A * IsType G B
  pTE (tyeq-refl h) = h , h
  pTE (tyeq-sym q) = snd (pTE q) , fst (pTE q)
  pTE (tyeq-trans q q') = fst (pTE q) , snd (pTE q')
  pTE (tyeq-el c) = isty-el (fst (pCv c)) , isty-el (snd (pCv c))
  pTE (tyeq-Pi hA hB hB' qA qB) =
    isty-Pi hA hB , isty-Pi hA' (ccTy hA' (tyeq-sym qA) (snd (pTE qB)))
    where hA' = snd (pTE qA)
  pTE (tyeq-Sigma hA hB hB' qA qB) =
    isty-Sigma hA hB , isty-Sigma hA' (ccTy hA' (tyeq-sym qA) (snd (pTE qB)))
    where hA' = snd (pTE qA)

  pCv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
        HasType G t A * HasType G u A
  pCv (conv-refl h) = h , h
  pCv (conv-sym c) = snd (pCv c) , fst (pCv c)
  pCv (conv-trans c c') = fst (pCv c) , snd (pCv c')
  pCv (conv-conv c q) = ty-conv (fst (pCv c)) q , ty-conv (snd (pCv c)) q
  pCv (conv-sub c) = ty-sub (fst (pCv c)) , ty-sub (snd (pCv c))
  pCv (conv-R' hA hB c) = hA , hB
  pCv (conv-delta-f hf hg hA hB) = ty-sub (ty-Fhat hf hg hA hB) , deltaF hf hA hB
  pCv (conv-delta-g {f = f} {g} {A} {c} {B} hf hg hA hB hc) =
    ty-sub (ty-Ghat hf hg hA hB hc) ,
    ty-App (isty-el fAL) (isty-V (wf-extend (isty-el fAL)))
      (trHT refl (gAFE f A (Lam A B))
        (ty-App (arrV hAty) (arrV (isty-el fa1))
          (trHT refl (gAE f A)
            (ty-App (isty-V w) (opGBody w hf) hg (ty-sub hA)))
          (lamV hA hB)))
      (ty-conv hc (tyeq-el (conv-delta-f hf hg hA hB)))
    where
      w = wfTm hf
      hAty = isty-el (ty-sub hA)
      fAL = deltaF hf hA hB
      wA = wf-extend (arrV hAty)
      fa1 = ty-App (arrV (isty-el (wkTm (arrV hAty) (ty-sub hA))))
              (isty-V (wf-extend (arrV (isty-el (wkTm (arrV hAty) (ty-sub hA))))))
              (ty-App (isty-V wA) (bodyF wA) (wkTm (arrV hAty) hf) (wkTm (arrV hAty) (ty-sub hA)))
              (ty-var wA)
  pCv (conv-beta hA hB ht ha) = ty-App hA hB (ty-Lam hA hB ht) ha , s1Tm (wfTy hA) ha ht
  pCv (conv-funext hA hB ht ht' c) = ht , ht'
  pCv (conv-fst-beta hA hB ht hu) = ty-Fst hA hB (ty-Pair hA hB ht hu) , ht
  pCv (conv-snd-beta hA hB ht hu) =
    ty-conv (ty-Snd hA hB (ty-Pair hA hB ht hu))
      (s1fTy (wfTy hA) hA (ty-Fst hA hB (ty-Pair hA hB ht hu)) ht
             (conv-fst-beta hA hB ht hu) hB) ,
    hu
  pCv (conv-pairext hA hB ht ht' cf cs) = ht , ht'
  pCv (conv-rec-zero hC hz hs) = ty-Rec hC hz hs (ty-Zero (wfTm hz)) , hz
  pCv (conv-rec-suc {z = z} {s} {k} {C} hC hz hs hk) =
    ty-Rec hC hz hs (ty-Suc hk) ,
    trHT refl (subst1-wk (subst1 C (Suc k)) (Rec (Lam Nat C) z s k))
      (ty-App hCk (wkTy hCk hCSk)
        (trHT refl (stepE C k)
          (ty-App (NatTy w) (arrV' hC (cS-Ty w hC)) hs hk))
        (ty-Rec hC hz hs hk))
    where
      w = wfTm hk
      hCk = s1Ty w hk hC
      hCSk = s1Ty w (ty-Suc hk) hC
      arrV' : {m : Num} {H : Ctx m} {X Y : Expr m} -> IsType H X -> IsType H Y -> IsType H (Arr X Y)
      arrV' hX hY = isty-Pi hX (wkTy hX hY)
  pCv (conv-App hA hB c ca) =
    ty-App hA hB (fst (pCv c)) (fst (pCv ca)) ,
    ty-conv (ty-App hA hB (snd (pCv c)) (snd (pCv ca)))
      (tyeq-sym (s1fTy (wfTy hA) hA (fst (pCv ca)) (snd (pCv ca)) ca hB))
  pCv (conv-Fst hA hB c) = ty-Fst hA hB (fst (pCv c)) , ty-Fst hA hB (snd (pCv c))
  pCv (conv-Snd hA hB c) =
    ty-Snd hA hB (fst (pCv c)) ,
    ty-conv (ty-Snd hA hB (snd (pCv c)))
      (tyeq-sym (s1fTy (wfTy hA) hA (ty-Fst hA hB (fst (pCv c))) (ty-Fst hA hB (snd (pCv c)))
                       (conv-Fst hA hB c) hB))
  pCv (conv-Pi un hA hB hB' cA cB) =
    ty-Pi un hA hB ,
    ty-Pi un hA' (ccTm (elTy un hA') (tyeq-sym (cvTE un cA)) hB')
    where hA' = snd (pCv cA)
  pCv (conv-Sigma un hA hB hB' cA cB) =
    ty-Sigma un hA hB ,
    ty-Sigma un hA' (ccTm (elTy un hA') (tyeq-sym (cvTE un cA)) hB')
    where hA' = snd (pCv cA)
  pCv (conv-Suc c) = ty-Suc (fst (pCv c)) , ty-Suc (snd (pCv c))
  pCv (conv-Rec {k = k} {k'} {C} {C'} hC hC' q cz cs ck) =
    ty-Rec hC (fst (pCv cz)) (fst (pCv cs)) (fst (pCv ck)) ,
    ty-conv (ty-Rec hC' (ty-conv (snd (pCv cz)) (s1TE w (ty-Zero w) q))
                        (ty-conv (snd (pCv cs)) eStep)
                        (snd (pCv ck)))
      (tyeq-sym (tyeq-trans (s1fTy w (NatTy w) (fst (pCv ck)) (snd (pCv ck)) ck hC)
                            (s1TE w (snd (pCv ck)) q)))
    where
      w = wfTm (fst (pCv ck))
      wN = wf-extend (NatTy w)
      eCS : TyEq (extend _ Nat) (substExpr sucSub C) (substExpr sucSub C')
      eCS = sbTE sucSub (wsSuc w) wN q
      eStep : TyEq _ (RecStep C) (RecStep C')
      eStep = tyeq-Pi (NatTy w) (isty-Pi hC (wkTy hC (cS-Ty w hC)))
                (isty-Pi hC' (wkTy hC' (cS-Ty w hC')))
                (tyeq-refl (NatTy w))
                (tyeq-Pi hC (wkTy hC (cS-Ty w hC)) (wkTy hC (cS-Ty w hC')) q (wkTE hC eCS))
  pCv (conv-Ucode hf hg cf cg) =
    ty-Ucode hf hg ,
    ty-Ucode (snd (pCv cf)) (ty-conv (snd (pCv cg)) (opGEq (wfTm hf) hf (snd (pCv cf)) cf))
  pCv (conv-Fhat cf cg hA hB hB' cA cB) =
    ty-Fhat f1 g1 hA hB ,
    ty-conv (ty-Fhat f2 (ty-conv g2 (opGEq w f1 f2 cf)) (ty-conv A2 eU)
                     (ty-conv (ccTm hA'ty qA'A hB') (wkTE hA'ty eU)))
            (tyeq-sym eU)
    where
      f1 = fst (pCv cf)
      f2 = snd (pCv cf)
      g1 = fst (pCv cg)
      g2 = snd (pCv cg)
      w = wfTm f1
      eU = tyeq-el (conv-Ucode f1 g1 cf cg)
      A2 = snd (pCv cA)
      hA'ty = isty-el (ty-sub A2)
      qA'A = tyeq-sym (tyeq-el (conv-sub cA))
  pCv (conv-Ghat cf cg hA hB hB' cA cB cc) =
    ty-Ghat f1 g1 hA hB (fst (pCv cc)) ,
    ty-conv (ty-Ghat f2 (ty-conv g2 (opGEq w f1 f2 cf)) (ty-conv A2 eU)
                     (ty-conv (ccTm hA'ty qA'A hB') (wkTE hA'ty eU))
                     (ty-conv (snd (pCv cc)) (tyeq-el (conv-sub (conv-Fhat cf cg hA hB hB' cA cB)))))
            (tyeq-sym eU)
    where
      f1 = fst (pCv cf)
      f2 = snd (pCv cf)
      g1 = fst (pCv cg)
      g2 = snd (pCv cg)
      w = wfTm f1
      eU = tyeq-el (conv-Ucode f1 g1 cf cg)
      A2 = snd (pCv cA)
      hA'ty = isty-el (ty-sub A2)
      qA'A = tyeq-sym (tyeq-el (conv-sub cA))

