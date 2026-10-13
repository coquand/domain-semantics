{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/AnnRel.agda
--
-- The record fields of a related Sigma-term, at ALL convertible
-- annotations, from the data at one annotation: the projections are
-- re-annotated by annotation change in head position (AR) and the
-- conversions of the generalised conv-Fst / conv-Snd.
------------------------------------------------------------------------

module MAHLORT.Adq.AnnRel where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLOINJ.Domain.Basic using (FinEl ; UCode)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLORT.Syntax.Wf using (wfTy)
open import MAHLORT.Syntax.Funct using (s1fTy)
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Ann
open import MAHLORT.Valid.Public

module SigAnn {n : Num} {G : Ctx n} {M M' A Ar : Expr n} {B Br : Expr (suc n)} {u1 u2 b c : FinEl}
  (iA : IsType G A) (iB : IsType (extend G A) B) (eAr : TyEq G A Ar) (eBr : TyEq (extend G A) B Br)
  (hM : HasType G M (SigmaB A B)) (hM' : HasType G M' (SigmaB A B))
  (m1 : FinMem u1 b) (bU : FinMem b UCode) (VA : RTy G A A b)
  (m2 : FinMem u2 c) (cU : FinMem c UCode) (VT : RTy G (subst1 B (Fst A (Lam A B) M)) (subst1 B (Fst A (Lam A B) M)) c)
  (c0 : ConvTm G (Fst A (Lam A B) M) (Fst Ar (Lam Ar Br) M') A)
  (f0 : RTm G (Fst A (Lam A B) M) (Fst Ar (Lam Ar Br) M') A u1 b)
  (s0 : RTm G (Snd A (Lam A B) M) (Snd Ar (Lam Ar Br) M') (subst1 B (Fst A (Lam A B) M)) u2 c) where

  private
    rA = tyeq-refl iA ; rB = tyeq-refl iB
    FA = Lam A B
    -- Fst A1 M' = Fst Ar M'   and   Snd A1 M' = Snd Ar M'
    convF : {A1 : Expr n} {B1 : Expr (suc n)} -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
      ConvTm G (Fst A1 (Lam A1 B1) M') (Fst Ar (Lam Ar Br) M') A
    convF e2 e3 = conv-trans (conv-sym (conv-Fst iA iB e2 e3 (conv-refl hM'))) (conv-Fst iA iB eAr eBr (conv-refl hM'))
    cFst : ConvTm G (Fst A FA M) (Fst A FA M') A
    cFst = conv-trans c0 (conv-sym (conv-Fst iA iB eAr eBr (conv-refl hM')))
    convS : {A1 : Expr n} {B1 : Expr (suc n)} -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
      ConvTm G (Snd A1 (Lam A1 B1) M') (Snd Ar (Lam Ar Br) M') (subst1 B (Fst A FA M))
    convS e2 e3 =
      conv-conv (conv-trans (conv-sym (conv-Snd iA iB e2 e3 (conv-refl hM'))) (conv-Snd iA iB eAr eBr (conv-refl hM')))
        (s1fTy (wfTy iA) iA (snd (pCv cFst)) (fst (pCv cFst)) (conv-sym cFst) iB)

  cFq : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
    TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
    ConvTm G (Fst A0 (Lam A0 B0) M) (Fst A1 (Lam A1 B1) M') A
  cFq A0 A1 B0 B1 e0 e1 e2 e3 =
    conv-trans (fstEq iA iB e0 e1 rA rB hM (conv-refl hM)) (conv-trans c0 (conv-sym (convF e2 e3)))

  fstq : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
    TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
    RTm G (Fst A0 (Lam A0 B0) M) (Fst A1 (Lam A1 B1) M') A u1 b
  fstq A0 A1 B0 B1 e0 e1 e2 e3 =
    pExpM u1 b m1 bU (ar _ (ann-fst ann-refl) hrs-refl) (fstEq iA iB e0 e1 rA rB hM (conv-refl hM)) VA
      (pExpM' u1 b m1 bU (ar _ (ann-fst ann-refl) hrs-refl) (convF e2 e3) VA f0)

  sndq : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
    TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
    RTm G (Snd A0 (Lam A0 B0) M) (Snd A1 (Lam A1 B1) M') (subst1 B (Fst A (Lam A B) M)) u2 c
  sndq A0 A1 B0 B1 e0 e1 e2 e3 =
    pExpM u2 c m2 cU (ar _ (ann-snd ann-refl) hrs-refl) (sndEq iA iB e0 e1 rA rB hM (conv-refl hM)) VT
      (pExpM' u2 c m2 cU (ar _ (ann-snd ann-refl) hrs-refl) (convS e2 e3) VT s0)
