{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Valid.AnnLemmas
--
-- Syntactic facts about application annotations (A1, B1) convertible to
-- (A0, B0) (`Ann`, BCDE4.Valid.Stratified): they are well formed, the
-- products agree, and an application with such annotations is typed,
-- and congruent in its function, at B0[N].  Likewise for level
-- application annotations A1 convertible to A0 (`LAnn`), at A0(l/α).
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Valid.AnnLemmas (D : LDecAll) where

open import BCDE4.Basic
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.Levels using (LExpr)
open import BCDE4.RussellLsub using (lsub-ConvTy ; lsk-inst ; lok-inst)
open import BCDE4.Valid.Stratified D using (Ann ; mkAnn ; LAnn)

module _ {n : Nat} {G : Ctx n} {A0 A1 : Expr n} {B0 B1 : Expr (suc n)}
         (dA0 : IsType G A0) (an : Ann G A0 B0 A1 B1) where

  private
    annA = Ann.annA an
    annB = Ann.annB an

  ann-dA1 : IsType G A1
  ann-dA1 = presup-l-ConvTy annA

  ann-dB1 : IsType (extend G A1) B1
  ann-dB1 = ctx-conv-IsType dA0 ann-dA1 (conv-Ty-sym annA) (presup-l-ConvTy annB)

  ann-Pi : ConvTy G (Pi A0 B0) (Pi A1 B1)
  ann-Pi = mk-conv-Ty-Pi (conv-Ty-sym annA) (conv-Ty-sym annB)

  ann-subst : {N : Expr n} -> HasType G N A0 -> ConvTy G (subst1 B1 N) (subst1 B0 N)
  ann-subst hN = subst-ConvTy (subst1-WtSub dA0 hN) (isType-WfCtx dA0) annB

  ann-App-ty : {M N : Expr n} -> HasType G M (Pi A0 B0) -> HasType G N A0
    -> HasType G (App A1 B1 M N) (subst1 B0 N)
  ann-App-ty hM hN =
    ty-conv (ty-App ann-dA1 ann-dB1 (ty-conv hM ann-Pi) (ty-conv hN (conv-Ty-sym annA)))
            (ann-subst hN)

  ann-App-fun : {M M' N : Expr n} -> ConvTm G M M' (Pi A0 B0) -> HasType G N A0
    -> ConvTm G (App A1 B1 M N) (App A1 B1 M' N) (subst1 B0 N)
  ann-App-fun cM hN =
    conv-conv (conv-cong-App-fun ann-dA1 ann-dB1 (conv-conv cM ann-Pi)
                                 (ty-conv hN (conv-Ty-sym annA)))
              (ann-subst hN)

module _ {n : Nat} {G : Ctx n} {A0 A1 : Expr n}
         (dA0 : IsType (addL G) A0) (an : LAnn G A0 A1) where

  lann-dA1 : IsType (addL G) A1
  lann-dA1 = presup-l-ConvTy an

  lann-LPi : ConvTy G (LPi A0) (LPi A1)
  lann-LPi = conv-Ty-LPi (unL-WfCtx (isType-WfCtx dA0)) dA0 (conv-Ty-sym an)

  lann-lsub : (l : LExpr) -> ConvTy G (lsub1 A1 l) (lsub1 A0 l)
  lann-lsub l = lsub-ConvTy (lsk-inst G l) (lok-inst G l) an

  lann-LApp-ty : {M : Expr n} {l : LExpr} -> HasType G M (LPi A0)
    -> HasType G (LApp A1 M l) (lsub1 A0 l)
  lann-LApp-ty {l = l} hM = ty-conv (ty-LApp lann-dA1 (ty-conv hM lann-LPi)) (lann-lsub l)

  lann-LApp-fun : {M M' : Expr n} {l : LExpr} -> ConvTm G M M' (LPi A0)
    -> ConvTm G (LApp A1 M l) (LApp A1 M' l) (lsub1 A0 l)
  lann-LApp-fun {l = l} cM =
    conv-conv (conv-cong-LApp-fun lann-dA1 (conv-conv cM lann-LPi)) (lann-lsub l)

  -- β for a level application whose two annotations are convertible to
  -- A0: (LApp A1 (LLam A2 u) l) = u(l/α) at A0(l/α)
  lann-LApp-beta : {A2 u : Expr n} {l : LExpr} -> ConvTy (addL G) A0 A2 -> HasType (addL G) u A0
    -> ConvTm G (LApp A1 (LLam A2 u) l) (lsub1 u l) (lsub1 A0 l)
  lann-LApp-beta {A2 = A2} {u = u} {l = l} c2 hu =
    conv-trans
      (conv-conv (conv-cong-LApp-Ty lann-dA1 c12 hT) (lann-lsub l))
      (conv-conv (conv-LApp-beta dA2 hu2) (lsub-ConvTy (lsk-inst G l) (lok-inst G l) (conv-Ty-sym c2)))
    where
      wf  = unL-WfCtx (isType-WfCtx dA0)
      dA2 = presup-r-ConvTy c2
      hu2 = ty-conv hu c2
      c12 = conv-Ty-trans an c2
      hT : HasType G (LLam A2 u) (LPi A1)
      hT = ty-conv (ty-LLam wf dA2 hu2) (conv-Ty-LPi wf dA2 (conv-Ty-sym c12))

  -- the annotation itself may be replaced by A0
  lann-LApp-ann : {M : Expr n} {l : LExpr} -> HasType G M (LPi A0)
    -> ConvTm G (LApp A1 M l) (LApp A0 M l) (lsub1 A0 l)
  lann-LApp-ann {l = l} hM =
    conv-conv (conv-cong-LApp-Ty lann-dA1 an (ty-conv hM lann-LPi)) (lann-lsub l)
