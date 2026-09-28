{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Valid.AnnLemmas
--
-- Syntactic facts about application annotations (A1, B1) convertible to
-- (A0, B0) (`Ann`, ERTUU.Valid.Stratified): they are well formed, the
-- products agree, and an application with such annotations is typed,
-- and congruent in its function, at B0[N].
------------------------------------------------------------------------

module ERTUU.Valid.AnnLemmas where

open import ERTUU.Basic
open import ERTUU.RussellSyntax
open import ERTUU.RussellTyping
open import ERTUU.RussellMeta
open import ERTUU.Valid.Stratified using (Ann ; mkAnn)

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
