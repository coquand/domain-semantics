{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Lam.agda
--
-- The abstraction step of the fundamental lemma (two-sided): from the
-- relation of the bodies under related arguments, the relation of the
-- abstractions at every Pi code of their type.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Lam where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons ; mkSigma)
  renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Coherent ; LeCode-refl ; FinMem-coh-u
        ; finMem-funel-coh ; finMem-funel-wf ; cft-from-cf)
open import MAHLOINJ.Model.Selection using (Selection)
open import MAHLOINJ.Model.Comb using (Pred ; Ideal ; BodyOK ; PiS ; LamS)
open import MAHLOINJ.Syntax.Presup using (pCv)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Props using (CodeU ; piU)
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base using (adj ; selKey ; selVal ; efU)
open import MAHLOINJ.Adq.Sem

module LamCore {h : Num} {H : Ctx h} (Al Ar : Expr h) (tl tr Bl : Expr (suc h))
  (PA : Pred) (Bt Bb : FinEl -> Pred) (iA : Ideal PA) (okt : BodyOK Bt) (okb : BodyOK Bb)
  (iAl : IsType H Al) (iBl : IsType (extend H Al) Bl)
  (VA : (a : FinEl) -> PA a -> FinMem a UCode -> RTy H Al Al a)
  (betaL : (N : Expr h) -> HasType H N Al -> ConvTm H (App (Lam Al tl) N) (subst1 tl N) (subst1 Bl N))
  (betaR : (N N' : Expr h) -> ConvTm H N N' Al -> ConvTm H (App (Lam Ar tr) N') (subst1 tr N') (subst1 Bl N))
  -- body hypotheses, for related arguments N ~ N' at a point w of the domain
  (VB : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' Al ->
        ((a : FinEl) -> PA a -> FinMem a UCode -> FinMem w a -> RTm H N N' Al w a) ->
        (b : FinEl) -> PA b -> FinMem w b ->
        (c : FinEl) -> Bb w c -> FinMem c UCode -> RTy H (subst1 Bl N) (subst1 Bl N) c)
  (FT : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' Al ->
        ((a : FinEl) -> PA a -> FinMem a UCode -> FinMem w a -> RTm H N N' Al w a) ->
        (b : FinEl) -> PA b -> FinMem w b ->
        (c v : FinEl) -> Bb w c -> FinMem c UCode -> Bt w v -> FinMem v c ->
        RTm H (subst1 tl N) (subst1 tr N') (subst1 Bl N) v c) where

  lam : (c u : FinEl) -> PiS PA (LamS PA Bb) c -> FinMem c UCode -> LamS PA Bt u -> FinMem u c ->
    RTm H (Lam Al tl) (Lam Ar tr) (PiB Al Bl) u c
  lam c Bot ec cU eu um = tt
  lam (PiCode b f) (FunEl g) ec cU eu gm = lamM (record
    { A = Al ; B = Bl ; rT = hrs-refl ; tT = tyeq-refl (isty-Pi iAl iBl) ; iA = iAl ; iB = iBl
    ; app = \ w v sel N N' cv rm ->
        let cu = piU b f cU
            bU = CodeU.bU cu
            eb = dfst (dsnd ec)
            wb = selKey gm cU sel
            cw = FinMem-coh-u w b wb
            ef = EvalFun f w
            efm = efU b f cu wb
            eBb = famEval PA Bb okb f (CodeU.cft cu) (dsnd (dsnd ec)) w cw
            eBt = lamAt PA Bt okt g eu sel cw
            vm = selVal gm cU sel
            RN = \ a ea aU wa -> adj PA iA VA w b eb bU wb rm w a ea aU (LeCode-refl w cw) wa
            vt = VB N N' w cv RN b eb wb ef eBb efm
            body = FT N N' w cv RN b eb wb ef v eBb efm eBt vm
            hN = fst (pCv cv)
        in pExpM v ef vm efm (hrs-step hr-beta hrs-refl) (betaL N hN) vt
             (pExpM' v ef vm efm (hrs-step hr-beta hrs-refl) (betaR N N' cv) vt body) })
