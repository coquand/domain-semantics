{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/RussellCong.agda
--
-- Derived congruences of MAHLO/Typing (Russell) for Lam and Pair, the
-- erasures of the Tarski rules conv-Lam / conv-Pair:
--   cvLam  : A = A',  t = t' : B          ==>  Lam A t = Lam A' t' : Pi A B
--   cvPair : a = a' : A,  b = b' : B[a]   ==>  Pair a b = Pair a' b' : Sigma A B
-- via conv-funext + conv-beta, resp. conv-pairext + fst/snd-beta.
------------------------------------------------------------------------

module MAHLORT.RussellCong where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.CtxConv
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup

private
  -- (Lam (wk A0) (lift wk t)) x0 = t : B, in context (G, A), for x0 : wk A0
  -- and t : B in (G, A0)
  etaBeta : {n : Num} {G : Ctx n} {A A0 : Expr n} {B t : Expr (suc n)} ->
    IsType G A -> IsType G A0 -> TyEq G A A0 ->
    IsType (extend G A0) B -> HasType (extend G A0) t B ->
    ConvTm (extend G A) (App (Lam (wkExpr A0) (renExpr (liftRen wkRen) t)) x0) t B
  etaBeta {G = G} {A} {A0} {B} {t} hA hA0 q hB ht =
    trCv refl (subst1-liftWk-cancel t) (subst1-liftWk-cancel B)
      (conv-beta (wkTy hA hA0) (rTy (liftRen wkRen) rt w' hB) (rTm (liftRen wkRen) rt w' ht)
                 (ty-conv (ty-var (wf-extend hA)) (wkTE hA q)))
    where
      w' = wf-extend (wkTy hA hA0)
      rt = liftRT {r = wkRen} {A = A0} (wkRT {G = G} {A})

cvLam : {n : Num} {G : Ctx n} {A A' : Expr n} {B t t' : Expr (suc n)} ->
  IsType G A -> IsType (extend G A) B -> TyEq G A A' -> ConvTm (extend G A) t t' B ->
  ConvTm G (Lam A t) (Lam A' t') (PiB A B)
cvLam {A = A} {A'} {B} {t} {t'} hA hB q c =
  conv-funext hA hB (ty-Lam hA hB ht) lam2
    (conv-trans (etaBeta hA hA (tyeq-refl hA) hB ht)
      (conv-trans c (conv-sym (etaBeta hA hA' q hB' ht'A'))))
  where
    hA' = snd (pTE q)
    ht = fst (pCv c)
    hB' = ccTy hA' (tyeq-sym q) hB
    ht'A' = ccTm hA' (tyeq-sym q) (snd (pCv c))
    lam2 = ty-conv (ty-Lam hA' hB' ht'A') (tyeq-Pi hA' hB' hB' (tyeq-sym q) (tyeq-refl hB'))

cvPair : {n : Num} {G : Ctx n} {A a a' b b' : Expr n} {B : Expr (suc n)} ->
  IsType G A -> IsType (extend G A) B -> ConvTm G a a' A -> ConvTm G b b' (subst1 B a) ->
  ConvTm G (Pair a b) (Pair a' b') (SigmaB A B)
cvPair {A = A} {a} {a'} {b} {b'} {B} hA hB ca cb =
  conv-pairext hA hB p1 p2 fstc sndc
  where
    w = wfTy hA
    ha = fst (pCv ca)
    ha' = snd (pCv ca)
    hb = fst (pCv cb)
    eB = s1fTy w hA ha ha' ca hB
    hb'' = ty-conv (snd (pCv cb)) eB
    p1 = ty-Pair hA hB ha hb
    p2 = ty-Pair hA hB ha' hb''
    fb1 = conv-fst-beta hA hB ha hb
    fstc = conv-trans fb1 (conv-trans ca (conv-sym (conv-fst-beta hA hB ha' hb'')))
    eF = s1fTy w hA ha (ty-Fst hA hB p1) (conv-sym fb1) hB
    sndc = conv-conv
             (conv-trans (conv-snd-beta hA hB ha hb)
               (conv-trans cb (conv-conv (conv-sym (conv-snd-beta hA hB ha' hb'')) (tyeq-sym eB))))
             eF
