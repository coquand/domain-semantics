{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/RecSyn.agda  (Tarski port of MAHLOINJ/Adq/RecSyn)
--
-- The syntactic iota steps of the recursor, two-sided, at a fixed
-- (substituted) motive / base / step.
------------------------------------------------------------------------

module MAHLORT.Adq.RecSyn where

open import MAHLO.Basic
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Wf using (NatTy)
open import MAHLORT.Syntax.Presup using (pCv)

module RecSyn {h : Num} {H : Ctx h} (wH : WfCtx H) {Cl Cr : Expr (suc h)} {zl zr sl sr : Expr h}
  (hC : IsType (extend H Nat) Cl) (hCr : IsType (extend H Nat) Cr) (qC : TyEq (extend H Nat) Cl Cr)
  (hz : HasType H zl (subst1 Cl Zero)) (hzr : HasType H zr (subst1 Cr Zero)) (cz : ConvTm H zl zr (subst1 Cl Zero))
  (hs : HasType H sl (RecStep Cl)) (hsr : HasType H sr (RecStep Cr)) (cst : ConvTm H sl sr (RecStep Cl)) where

  private
    iN = NatTy wH
    hZ = ty-Zero wH
    RL = \ (K : Expr h) -> Rec (Lam Nat Cl) zl sl K
    RR = \ (K : Expr h) -> Rec (Lam Nat Cr) zr sr K
    -- subst1 Cr K' = subst1 Cl K  for K = K'
    eK : (K K' : Expr h) -> ConvTm H K K' Nat -> TyEq H (subst1 Cr K') (subst1 Cl K)
    eK K K' c = tyeq-sym (tyeq-trans (s1fTy wH iN (fst (pCv c)) (snd (pCv c)) c hC) (s1TE wH (snd (pCv c)) qC))

  cRec : (P P' : Expr h) -> ConvTm H P P' Nat -> ConvTm H (RL P) (RR P') (subst1 Cl P)
  cRec P P' cP = conv-Rec hC hCr qC cz cst cP

  izL : (K : Expr h) -> ConvTm H K Zero Nat -> ConvTm H (RL K) zl (subst1 Cl K)
  izL K c0 = conv-trans (conv-Rec hC hC (tyeq-refl hC) (conv-refl hz) (conv-refl hs) c0)
               (conv-conv (conv-rec-zero hC hz hs) (tyeq-sym (s1fTy wH iN (fst (pCv c0)) hZ c0 hC)))

  izR : (K K' : Expr h) -> ConvTm H K K' Nat -> ConvTm H K' Zero Nat -> ConvTm H (RR K') zr (subst1 Cl K)
  izR K K' c c0 =
    conv-conv (conv-trans (conv-Rec hCr hCr (tyeq-refl hCr) (conv-refl hzr) (conv-refl hsr) c0)
                 (conv-conv (conv-rec-zero hCr hzr hsr) (tyeq-sym (s1fTy wH iN (fst (pCv c0)) hZ c0 hCr))))
      (eK K K' c)

  isL : (K P : Expr h) -> HasType H P Nat -> ConvTm H K (Suc P) Nat ->
    ConvTm H (RL K) (RecSuc Cl zl sl P) (subst1 Cl K)
  isL K P hP c1 = conv-trans (conv-Rec hC hC (tyeq-refl hC) (conv-refl hz) (conv-refl hs) c1)
                    (conv-conv (conv-rec-suc hC hz hs hP) (tyeq-sym (s1fTy wH iN (fst (pCv c1)) (ty-Suc hP) c1 hC)))

  isR : (K K' P' : Expr h) -> HasType H P' Nat -> ConvTm H K K' Nat -> ConvTm H K' (Suc P') Nat ->
    ConvTm H (RR K') (RecSuc Cr zr sr P') (subst1 Cl K)
  isR K K' P' hP' c c1 =
    conv-conv (conv-trans (conv-Rec hCr hCr (tyeq-refl hCr) (conv-refl hzr) (conv-refl hsr) c1)
                 (conv-conv (conv-rec-suc hCr hzr hsr hP') (tyeq-sym (s1fTy wH iN (fst (pCv c1)) (ty-Suc hP') c1 hCr))))
      (eK K K' c)
