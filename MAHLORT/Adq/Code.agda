{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Code.agda  (Tarski port of MAHLOINJ/Adq/Code)
--
-- The formation step of the fundamental lemma (Pi and Sigma, two-sided):
-- from the relation of the domains and of the codomains under related
-- arguments, the relation of the formed types at every code.
------------------------------------------------------------------------

module MAHLORT.Adq.Code where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; PiCode ; SigmaCode ; FinFun ; nil ; cons ; mkSigma)
  renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (FinMem ; LeCode-refl ; FinMem-coh-u ; coh-from-aU)
open import MAHLOINJ.Model.Selection using (Selection ; FinMem-Selection-UCode ; FinMemAllU-Selection)
open import MAHLOINJ.Model.Comb using (Pred ; Ideal ; BodyOK ; PiS ; SigS ; LamS ; FamRel)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (CodeU ; piU ; sigU)
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base using (adj)
open import MAHLOINJ.Adq.Sem

module CodeCore {h : Num} {H : Ctx h} (Al Ar : Expr h) (Bl Br : Expr (suc h))
  (PA : Pred) (Bb : FinEl -> Pred) (iA : Ideal PA) (okb : BodyOK Bb)
  (iAl : IsType H Al) (iBl : IsType (extend H Al) Bl) (iAr : IsType H Ar) (iBr : IsType (extend H Ar) Br)
  (eA : TyEq H Al Ar) (eB : TyEq (extend H Al) Bl Br)
  (VA : (a : FinEl) -> PA a -> FinMem a UCode -> RTy H Al Al a)
  (DA : (a : FinEl) -> PA a -> FinMem a UCode -> RTy H Al Ar a)
  (FB : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' Al ->
        ((a : FinEl) -> PA a -> FinMem a UCode -> FinMem w a -> RTm H N N' Al w a) ->
        (b : FinEl) -> PA b -> FinMem w b ->
        (c : FinEl) -> Bb w c -> FinMem c UCode -> RTy H (subst1 Bl N) (subst1 Br N') c) where

  core : (S : Shape) -> IsType H (S Al Bl) -> IsType H (S Ar Br) -> (b : FinEl) (f : FinFun) -> CodeU b f -> PA b ->
    FamRel (LamS PA Bb) f -> CodeTy S RTy RTm H (S Al Bl) (S Ar Br) b f
  core S iL iR b f cu eb fr = record
    { A = Al ; A' = Ar ; B = Bl ; B' = Br ; rT = hrs-refl ; rT' = hrs-refl
    ; tT = tyeq-refl iL ; tT' = tyeq-refl iR
    ; iA = iAl ; iB = iBl ; iA' = iAr ; iB' = iBr ; eA = eA ; eB = eB
    ; dom = DA b eb bU
    ; cod = \ w c sel N N' cv rm ->
        let wb = FinMemAllU-Selection b sel (CodeU.allU cu) (CodeU.cft cu) (coh-from-aU b bU) bU
            cw = FinMem-coh-u w b wb
            RN = \ a ea aU wa -> adj PA iA VA w b eb bU wb rm w a ea aU (LeCode-refl w cw) wa
        in FB N N' w cv RN b eb wb c (famAt PA Bb okb f fr sel cw)
             (FinMem-Selection-UCode b sel (CodeU.allU cu) (CodeU.cft cu)) }
    where bU = CodeU.bU cu

  piTy : (c : FinEl) -> PiS PA (LamS PA Bb) c -> FinMem c UCode -> RTy H (PiB Al Bl) (PiB Ar Br) c
  piTy Bot e cU = tt
  piTy (PiCode b f) e cU = piTyM (core PiB (isty-Pi iAl iBl) (isty-Pi iAr iBr) b f (piU b f cU) (dfst (dsnd e)) (dsnd (dsnd e)))

  sigTy : (c : FinEl) -> SigS PA (LamS PA Bb) c -> FinMem c UCode -> RTy H (SigmaB Al Bl) (SigmaB Ar Br) c
  sigTy Bot e cU = tt
  sigTy (SigmaCode b f) e cU =
    sigTyM (core SigmaB (isty-Sigma iAl iBl) (isty-Sigma iAr iBr) b f (sigU b f cU) (dfst (dsnd e)) (dsnd (dsnd e)))
