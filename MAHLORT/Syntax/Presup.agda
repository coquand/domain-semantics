{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Presup.agda
--
-- Presupposition for MAHLORT/TarskiTyping (port of MAHLOINJ):
--   G |- t : A      ==>  G |- A
--   G |- A = B      ==>  G |- A  and  G |- B
--   G |- t = u : A  ==>  G |- t : A  and  G |- u : A
-- No inversion and no injectivity is used.  In particular
--   a : U_{f,g}  ==>  U_{f,g} type  ==>  f : OpF, g : OpG f   (tyU-of, invTyU).
------------------------------------------------------------------------

module MAHLORT.Syntax.Presup where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.CtxConv
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Ops

------------------------------------------------------------------------
-- Auxiliary typings
------------------------------------------------------------------------

-- the family  \x:T_V(T^ a). T^ b  of a code  b  over  a : U_{f,g}
hEl : {n : Num} {G : Ctx n} {f g a : Expr n} -> HasType G a (TyU f g) -> IsType G (ElV (That a))
hEl ha = isty-ElV (ty-That ha)

famBody : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
          HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
          HasType (extend G (ElV (That a))) (That b) V
famBody ha hb = ccTm (hEl ha) (tyeq-sym (tyeq-ElU-That ha)) (ty-That hb)

famTy : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
        HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
        HasType G (Lam (ElV (That a)) (That b)) (Arr (ElV (That a)) V)
famTy ha hb = ty-Lam (hEl ha) (isty-V (wf-extend (hEl ha))) (famBody ha hb)

private
  wsSuc : {n : Num} {G : Ctx n} -> WfCtx G -> WtSub (extend G Nat) (extend G Nat) sucSub
  wsSuc w fzero = ty-Suc (ty-var (wf-extend (NatTy w)))
  wsSuc {G = G} w (fsuc i) =
    trHT refl (Eq-sym (sucSub-wk (lookup G i))) (ty-var (wf-extend (NatTy w)))

  cS-Ty : {n : Num} {G : Ctx n} {C : Expr (suc n)} -> WfCtx G ->
          IsType (extend G Nat) C -> IsType (extend G Nat) (substExpr sucSub C)
  cS-Ty w hC = sbTy sucSub (wsSuc w) (wf-extend (NatTy w)) hC

  stepE : {n : Num} (C : Expr (suc n)) (k : Expr n) ->
          Eq (subst1 (Arr C (substExpr sucSub C)) k) (Arr (subst1 C k) (subst1 C (Suc k)))
  stepE C k =
    Eq-cong (\ z -> Pi (subst1 C k) (Lam (subst1 C k) z))
      (Eq-trans (subst-wk-comm (subst1Sub k) (substExpr sucSub C))
                (Eq-cong wkExpr (subst1-sucSub C k)))

  arrTy : {m : Num} {H : Ctx m} {X Y : Expr m} -> IsType H X -> IsType H Y -> IsType H (Arr X Y)
  arrTy hX hY = isty-Pi hX (wkTy hX hY)

------------------------------------------------------------------------
-- Presupposition
------------------------------------------------------------------------

mutual
  pTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> IsType G A
  pTm (ty-var {i = i} w) = lookupTy w i
  pTm (ty-conv h q) = snd (pTE q)
  pTm (ty-Lam hA hB ht) = isty-Pi hA hB
  pTm (ty-App hA hB ht ha) = s1Ty (wfTy hA) ha hB
  pTm (ty-Pair hA hB ha hb) = isty-Sigma hA hB
  pTm (ty-Fst hA hB ht) = hA
  pTm (ty-Snd hA hB ht) = s1Ty (wfTy hA) (ty-Fst hA hB ht) hB
  pTm (ty-Zero w) = NatTy w
  pTm (ty-Suc h) = NatTy (wfTm h)
  pTm (ty-Rec hC hz hs hk) = s1Ty (wfTm hk) hk hC
  pTm (ty-PiV ha hb) = isty-V (wfTm ha)
  pTm (ty-SigV ha hb) = isty-V (wfTm ha)
  pTm (ty-NatV w) = isty-V w
  pTm (ty-UV hf hg) = isty-V (wfTm hf)
  pTm (ty-PiU ha hb) = pTm ha
  pTm (ty-SigU ha hb) = pTm ha
  pTm (ty-NatU hU) = hU
  pTm (ty-Fhat hf hg ha hb) = isty-TyU hf hg
  pTm (ty-Ghat hf hg ha hb hc) = isty-TyU hf hg
  pTm (ty-That h) = isty-V (wfTm h)

  pTE : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> IsType G A * IsType G B
  pTE (tyeq-refl h) = h , h
  pTE (tyeq-sym q) = snd (pTE q) , fst (pTE q)
  pTE (tyeq-trans q q') = fst (pTE q) , snd (pTE q')
  pTE (tyeq-ElV c) = isty-ElV (fst (pCv c)) , isty-ElV (snd (pCv c))
  pTE (tyeq-ElU c) = isty-ElU (fst (pCv c)) , isty-ElU (snd (pCv c))
  pTE (tyeq-TyU hf hg cf cg) =
    isty-TyU hf hg ,
    isty-TyU (snd (pCv cf)) (ty-conv (snd (pCv cg)) (opGEq (wfTm hf) hf (snd (pCv cf)) cf))
  pTE (tyeq-Pi hA hB hB' qA qB) =
    isty-Pi hA hB , isty-Pi hA' (ccTy hA' (tyeq-sym qA) (snd (pTE qB)))
    where hA' = snd (pTE qA)
  pTE (tyeq-Sigma hA hB hB' qA qB) =
    isty-Sigma hA hB , isty-Sigma hA' (ccTy hA' (tyeq-sym qA) (snd (pTE qB)))
    where hA' = snd (pTE qA)
  pTE (tyeq-El-PiV ha hb) = isty-ElV (ty-PiV ha hb) , isty-Pi (isty-ElV ha) (isty-ElV hb)
  pTE (tyeq-El-SigV ha hb) = isty-ElV (ty-SigV ha hb) , isty-Sigma (isty-ElV ha) (isty-ElV hb)
  pTE (tyeq-El-NatV w) = isty-ElV (ty-NatV w) , isty-Nat w
  pTE (tyeq-El-UV hf hg) = isty-ElV (ty-UV hf hg) , isty-TyU hf hg
  pTE (tyeq-ElU-That h) = isty-ElU h , isty-ElV (ty-That h)

  pCv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
        HasType G t A * HasType G u A
  pCv (conv-refl h) = h , h
  pCv (conv-sym c) = snd (pCv c) , fst (pCv c)
  pCv (conv-trans c c') = fst (pCv c) , snd (pCv c')
  pCv (conv-conv c q) = ty-conv (fst (pCv c)) q , ty-conv (snd (pCv c)) q
  pCv (conv-beta hA hB ht ha) = ty-App hA hB (ty-Lam hA hB ht) ha , s1Tm (wfTy hA) ha ht
  pCv (conv-funext hA hB ht ht' c) = ht , ht'
  pCv (conv-fst-beta hA hB ha hb) = ty-Fst hA hB (ty-Pair hA hB ha hb) , ha
  pCv (conv-snd-beta hA hB ha hb) =
    ty-conv (ty-Snd hA hB (ty-Pair hA hB ha hb))
      (s1fTy (wfTy hA) hA (ty-Fst hA hB (ty-Pair hA hB ha hb)) ha
             (conv-fst-beta hA hB ha hb) hB) ,
    hb
  pCv (conv-pairext hA hB ht ht' cf cs) = ht , ht'
  pCv (conv-rec-zero hC hz hs) = ty-Rec hC hz hs (ty-Zero (wfTm hz)) , hz
  pCv (conv-rec-suc {z = z} {s} {k} {C} hC hz hs hk) =
    ty-Rec hC hz hs (ty-Suc hk) ,
    trHT refl (subst1-wk (subst1 C (Suc k)) (Rec (Lam Nat C) z s k))
      (ty-App hCk (wkTy hCk hCSk)
        (trHT refl (stepE C k) (ty-App (NatTy w) (arrTy hC (cS-Ty w hC)) hs hk))
        (ty-Rec hC hz hs hk))
    where
      w = wfTm hk
      hCk = s1Ty w hk hC
      hCSk = s1Ty w (ty-Suc hk) hC
  pCv (conv-Lam hA hB q c) =
    ty-Lam hA hB (fst (pCv c)) ,
    ty-conv (ty-Lam hA' hB' (ccTm hA' (tyeq-sym q) (snd (pCv c))))
            (tyeq-Pi hA' hB' hB' (tyeq-sym q) (tyeq-refl hB'))
    where
      hA' = snd (pTE q)
      hB' = ccTy hA' (tyeq-sym q) hB
  pCv (conv-App hA hB qA qB cc ca) =
    ty-App hA hB (fst (pCv cc)) ha ,
    ty-conv (ty-App hA' hB'A' (ty-conv (snd (pCv cc)) (tyeq-Pi hA hB hB'A qA qB)) (ty-conv ha' qA))
      (tyeq-sym (tyeq-trans (s1fTy w hA ha ha' ca hB) (s1TE w ha' qB)))
    where
      w = wfTy hA
      ha = fst (pCv ca)
      ha' = snd (pCv ca)
      hA' = snd (pTE qA)
      hB'A = snd (pTE qB)
      hB'A' = ccTy hA' (tyeq-sym qA) hB'A
  pCv (conv-Pair hA hB qA qB ca cb) =
    ty-Pair hA hB ha (fst (pCv cb)) ,
    ty-conv (ty-Pair hA' hB'A' (ty-conv ha' qA)
               (ty-conv (snd (pCv cb)) (tyeq-trans (s1fTy w hA ha ha' ca hB) (s1TE w ha' qB))))
      (tyeq-sym (tyeq-Sigma hA hB hB'A qA qB))
    where
      w = wfTy hA
      ha = fst (pCv ca)
      ha' = snd (pCv ca)
      hA' = snd (pTE qA)
      hB'A = snd (pTE qB)
      hB'A' = ccTy hA' (tyeq-sym qA) hB'A
  pCv (conv-Fst hA hB qA qB ct) =
    ty-Fst hA hB (fst (pCv ct)) ,
    ty-conv (ty-Fst hA' hB'A' (ty-conv (snd (pCv ct)) (tyeq-Sigma hA hB hB'A qA qB))) (tyeq-sym qA)
    where
      hA' = snd (pTE qA)
      hB'A = snd (pTE qB)
      hB'A' = ccTy hA' (tyeq-sym qA) hB'A
  pCv (conv-Snd hA hB qA qB ct) =
    ty-Snd hA hB (fst (pCv ct)) ,
    ty-conv (ty-Snd hA' hB'A' ht')
      (tyeq-sym (tyeq-trans (s1fTy w hA hF1 hF2 (conv-Fst hA hB qA qB ct) hB) (s1TE w hF2 qB)))
    where
      w = wfTy hA
      hA' = snd (pTE qA)
      hB'A = snd (pTE qB)
      hB'A' = ccTy hA' (tyeq-sym qA) hB'A
      ht' = ty-conv (snd (pCv ct)) (tyeq-Sigma hA hB hB'A qA qB)
      hF1 = ty-Fst hA hB (fst (pCv ct))
      hF2 = ty-conv (ty-Fst hA' hB'A' ht') (tyeq-sym qA)
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
  pCv (conv-PiV ha hb hb' ca cb) =
    ty-PiV ha hb , ty-PiV ha' (ccTm (isty-ElV ha') (tyeq-sym (tyeq-ElV ca)) hb')
    where ha' = snd (pCv ca)
  pCv (conv-SigV ha hb hb' ca cb) =
    ty-SigV ha hb , ty-SigV ha' (ccTm (isty-ElV ha') (tyeq-sym (tyeq-ElV ca)) hb')
    where ha' = snd (pCv ca)
  pCv (conv-UV hf hg cf cg) =
    ty-UV hf hg , ty-UV (snd (pCv cf)) (ty-conv (snd (pCv cg)) (opGEq (wfTm hf) hf (snd (pCv cf)) cf))
  pCv (conv-PiU ha hb hb' ca cb) =
    ty-PiU ha hb , ty-PiU ha' (ccTm (isty-ElU ha') (tyeq-sym (tyeq-ElU ca)) hb')
    where ha' = snd (pCv ca)
  pCv (conv-SigU ha hb hb' ca cb) =
    ty-SigU ha hb , ty-SigU ha' (ccTm (isty-ElU ha') (tyeq-sym (tyeq-ElU ca)) hb')
    where ha' = snd (pCv ca)
  pCv (conv-Fhat hf hg ha hb hb' ca cb) =
    ty-Fhat hf hg ha hb , ty-Fhat hf hg ha' (ccTm (isty-ElU ha') (tyeq-sym (tyeq-ElU ca)) hb')
    where ha' = snd (pCv ca)
  pCv (conv-Ghat hf hg ha hb hb' ca cb cc) =
    ty-Ghat hf hg ha hb (fst (pCv cc)) ,
    ty-Ghat hf hg ha' (ccTm (isty-ElU ha') (tyeq-sym (tyeq-ElU ca)) hb')
      (ty-conv (snd (pCv cc)) (tyeq-ElU (conv-Fhat hf hg ha hb hb' ca cb)))
    where ha' = snd (pCv ca)
  pCv (conv-That c) = ty-That (fst (pCv c)) , ty-That (snd (pCv c))
  pCv (conv-That-PiU ha hb) = ty-That (ty-PiU ha hb) , ty-PiV (ty-That ha) (famBody ha hb)
  pCv (conv-That-SigU ha hb) = ty-That (ty-SigU ha hb) , ty-SigV (ty-That ha) (famBody ha hb)
  pCv (conv-That-NatU hU) = ty-That (ty-NatU hU) , ty-NatV (wfTy hU)
  pCv (conv-That-Fhat hf hg ha hb) =
    ty-That (ty-Fhat hf hg ha hb) , fAppTy hf (ty-That ha) (famTy ha hb)
  pCv (conv-That-Ghat hf hg ha hb hc) =
    ty-That (ty-Ghat hf hg ha hb hc) ,
    gAppTy hf hg (ty-That ha) (famTy ha hb)
      (ty-conv hc (tyeq-trans (tyeq-ElU-That (ty-Fhat hf hg ha hb))
                              (tyeq-ElV (conv-That-Fhat hf hg ha hb))))
  pCv (conv-reflect ha hb c) = ha , hb

------------------------------------------------------------------------
-- The subuniverse of an element:  a : U_{f,g}  ==>  f : OpF, g : OpG f
------------------------------------------------------------------------

tyU-of : {n : Num} {G : Ctx n} {f g a : Expr n} -> HasType G a (TyU f g) -> IsType G (TyU f g)
tyU-of = pTm

opF-of : {n : Num} {G : Ctx n} {f g a : Expr n} -> HasType G a (TyU f g) -> HasType G f OpF
opF-of ha = fst (invTyU (pTm ha))

opG-of : {n : Num} {G : Ctx n} {f g a : Expr n} -> HasType G a (TyU f g) -> HasType G g (OpG f)
opG-of ha = snd (invTyU (pTm ha))

------------------------------------------------------------------------
-- RecStep along a motive equality
------------------------------------------------------------------------

recStepEq : {n : Num} {G : Ctx n} {C C' : Expr (suc n)} -> WfCtx G ->
            IsType (extend G Nat) C -> IsType (extend G Nat) C' -> TyEq (extend G Nat) C C' ->
            TyEq G (RecStep C) (RecStep C')
recStepEq w hC hC' q =
  tyeq-Pi (NatTy w) (isty-Pi hC (wkTy hC (cS-Ty w hC))) (isty-Pi hC' (wkTy hC' (cS-Ty w hC')))
    (tyeq-refl (NatTy w))
    (tyeq-Pi hC (wkTy hC (cS-Ty w hC)) (wkTy hC (cS-Ty w hC')) q
       (wkTE hC (sbTE sucSub (wsSuc w) (wf-extend (NatTy w)) q)))

recStepTy : {n : Num} {G : Ctx n} {C : Expr (suc n)} -> WfCtx G ->
            IsType (extend G Nat) C -> IsType G (RecStep C)
recStepTy w hC = isty-Pi (NatTy w) (isty-Pi hC (wkTy hC (cS-Ty w hC)))
