{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Adeq.Driver
--
-- The fundamental theorem (adequacy of the domain model) for T_R, by
-- case analysis on the derivation and STRUCTURAL induction: every
-- recursive call is on an immediate subderivation, every informative
-- case is a combinator taking the IHs as parameters.
--
--   adqTy  : IsType  G A      -> AdqTy     G A       (one substitution)
--   adqTyC : IsType  G A      -> AdqConvTy G A       (two substitutions)
--   adqTm  : HasType G M A    -> Adq       G M A
--   adqTmC : HasType G M A    -> AdqConv   G M A
--   adqCTy : ConvTy  G A B    -> AdqETy    G A B
--   adqCTm : ConvTm  G M N A  -> AdqE1     G M N A
--
-- No postulates, no pragmas.
------------------------------------------------------------------------

module ERTUU.Adeq.Driver where

open import ERTUU.Adeq.HeadRed
open import ERTUU.Adeq.Stmt
open import ERTUU.Adeq.Pi using (AdqTy-Pi)
open import ERTUU.Adeq.PiConv using (AdqConvTy-Pi ; AdqETy-Pi)
open import ERTUU.Adeq.Lam using (Adq-Lam)
open import ERTUU.Adeq.LamConv using (AdqConv-Lam)
open import ERTUU.Adeq.LamCong using (AdqE1-Lam-body ; AdqE1-Lam-Ty)
open import ERTUU.Adeq.App using (Adq-App ; AdqConv-App)
open import ERTUU.Adeq.AppCong using (AdqE1-App-fun ; AdqE1-App-arg)
open import ERTUU.Adeq.Beta using (AdqE1-beta)
open import ERTUU.Adeq.Eta using (AdqE1-eta)

import ERTUU.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; mkSigma ; fst ; snd ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode)
open import ERTUU.Dom.Kernel using (FinMem ; FinMem-coh-u ; FinMem-a-in-U)
open import ERTUU.Model.Eval using (EvalRel-coh)
open import ERTUU.Model.Strip using (strip)
open import ERTUU.RussellSyntax using (Expr ; U ; Pi)
open import ERTUU.RussellTyping
open import ERTUU.RussellMeta using (presup-l-ConvTy)

------------------------------------------------------------------------
-- Universes
------------------------------------------------------------------------

AdqTy-U : {g : Nat} {G : Ctx g} -> AdqTy G U
AdqTy-U sigma rho crho vs fits wt wfH Bot          ev aU = tt
AdqTy-U sigma rho crho vs fits wt wfH (UCode k)    ev aU = valTyU 0 wfH
AdqTy-U sigma rho crho vs fits wt wfH (FunEl _)    () aU
AdqTy-U sigma rho crho vs fits wt wfH (PiCode _ _) () aU

AdqConvTy-U : {g : Nat} {G : Ctx g} -> AdqConvTy G U
AdqConvTy-U {G = G} sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a ev aU =
  ValTy2-to-EqValTy2 a (AdqTy-U {G = G} sigma rho crho vs fits wt wfH a ev aU)

------------------------------------------------------------------------
-- The driver
------------------------------------------------------------------------

mutual

  adqTy : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> AdqTy G A
  adqTy (is-Ty-from-U {A = A} d) = Adq-U-to-AdqTy {A = A} (adqTm d)

  adqTyC : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> AdqConvTy G A
  adqTyC (is-Ty-from-U {A = A} d) = AdqConv-U-to-AdqConvTy {A = A} (adqTmC d)

  adqTm : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> Adq G M A
  adqTm (ty-var {i = i} _) sigma rho crho vs fits wt wfH u hu a evA fm =
    vs i u (fst hu) (snd hu) a evA fm
  adqTm (ty-conv {A = A} d dAB) sigma rho crho vs fits wt wfH u hu a evB fm =
    let evA = evBwd-Ty dAB rho fits a evB
        ca  = EvalRel-coh (strip A) rho a evA
    in Val2-EqValTy2-fwd u a ca
         (adqCTy dAB sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
         (adqTm d sigma rho crho vs fits wt wfH u hu a evA fm)
  adqTm (ty-U _) = AdqTy-to-Adq-U {T = U} AdqTy-U
  adqTm (ty-Pi {A = A} {B = B} dA dB) =
    AdqTy-to-Adq-U {T = Pi A B} (AdqTy-Pi (is-Ty-from-U dA) (is-Ty-from-U dB)
      (Adq-U-to-AdqTy {A = A} (adqTm dA)) (Adq-U-to-AdqTy {A = B} (adqTm dB))
      (AdqConv-U-to-AdqConvTy {A = B} (adqTmC dB)))
  adqTm (ty-Lam dA dB db) =
    Adq-Lam dA dB db (conv-Ty-refl dA) (conv-Ty-refl dB) (adqTy dA)
      (AdqTy-Pi dA dB (adqTy dA) (adqTy dB) (adqTyC dB)) (adqTm db) (adqTmC db)
  adqTm (ty-App dA dB dc da) = Adq-App dA dB dc da (adqTm dc) (adqTm da) (adqTy dB)

  adqTmC : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> AdqConv G M A
  adqTmC (ty-var {i = i} _) sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm =
    vcs i u (fst hu) (snd hu) a evA fm
  adqTmC (ty-conv {A = A} d dAB) sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evB fm =
    let evA = evBwd-Ty dAB rho fits a evB
        ca  = EvalRel-coh (strip A) rho a evA
    in EqVal2-EqValTy2-fwd u a ca
         (adqCTy dAB sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
         (adqTmC d sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm)
  adqTmC (ty-U _) = AdqConvTy-to-AdqConv-U {T = U} AdqConvTy-U
  adqTmC (ty-Pi {A = A} {B = B} dA dB) =
    AdqConvTy-to-AdqConv-U {T = Pi A B} (AdqConvTy-Pi (is-Ty-from-U dA) (is-Ty-from-U dB)
      (AdqConv-U-to-AdqConvTy {A = A} (adqTmC dA)) (AdqConv-U-to-AdqConvTy {A = B} (adqTmC dB)))
  adqTmC (ty-Lam dA dB db) =
    AdqConv-Lam dA dB db (adqTy dA) (adqTyC dA)
      (AdqTy-Pi dA dB (adqTy dA) (adqTy dB) (adqTyC dB))
      (AdqConvTy-Pi dA dB (adqTyC dA) (adqTyC dB))
      (adqTm db) (adqTmC db)
  adqTmC (ty-App dA dB dc da) =
    AdqConv-App dA dB dc da (adqTm da) (adqTy dB) (adqTmC dc) (adqTmC da)

  adqCTy : {g : Nat} {G : Ctx g} {A B : Expr g} -> ConvTy G A B -> AdqETy G A B
  adqCTy (conv-Ty-refl dA) sigma rho crho vs fits wt wfH a evA aU =
    ValTy2-to-EqValTy2 a (adqTy dA sigma rho crho vs fits wt wfH a evA aU)
  adqCTy (conv-Ty-sym {A = A} d) sigma rho crho vs fits wt wfH a evB aU =
    let evA = evBwd-Ty d rho fits a evB
    in EqValTy2-sym a (EvalRel-coh (strip A) rho a evA)
         (adqCTy d sigma rho crho vs fits wt wfH a evA aU)
  adqCTy (conv-Ty-trans {A = A} d1 d2) sigma rho crho vs fits wt wfH a evA aU =
    EqValTy2-trans a (EvalRel-coh (strip A) rho a evA)
      (adqCTy d1 sigma rho crho vs fits wt wfH a evA aU)
      (adqCTy d2 sigma rho crho vs fits wt wfH a (evFwd-Ty d1 rho fits a evA) aU)
  adqCTy (conv-Ty-Pi dA dB cA cB) =
    AdqETy-Pi dA dB cA cB (adqTyC dA) (adqTyC dB) (adqCTy cA) (adqCTy cB)
  adqCTy (conv-Ty-from-U {A = A} {B = B} d) = AdqE1-U-to-AdqETy {A = A} {B = B} (adqCTm d)

  adqCTm : {g : Nat} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> AdqE1 G M N A
  adqCTm (conv-refl d) sigma rho crho vs fits wt wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adqTm d sigma rho crho vs fits wt wfH u hu a evA fm)
  adqCTm (conv-sym {A = A} d) sigma rho crho vs fits wt wfH u hu a evA fm =
    let huM = evBwd-Tm d rho fits u hu
    in EqVal2-sym u a (FinMem-coh-u u a fm) (EvalRel-coh (strip A) rho a evA)
         (adqCTm d sigma rho crho vs fits wt wfH u huM a evA fm)
  adqCTm (conv-trans {A = A} d1 d2) sigma rho crho vs fits wt wfH u hu a evA fm =
    EqVal2-trans u a (FinMem-coh-u u a fm) (EvalRel-coh (strip A) rho a evA)
      (adqCTm d1 sigma rho crho vs fits wt wfH u hu a evA fm)
      (adqCTm d2 sigma rho crho vs fits wt wfH u (evFwd-Tm d1 rho fits u hu) a evA fm)
  adqCTm (conv-conv {A = A} d dAB) sigma rho crho vs fits wt wfH u hu a evB fm =
    let evA = evBwd-Ty dAB rho fits a evB
        ca  = EvalRel-coh (strip A) rho a evA
    in EqVal2-EqValTy2-fwd u a ca
         (adqCTy dAB sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
         (adqCTm d sigma rho crho vs fits wt wfH u hu a evA fm)
  adqCTm (conv-cong-Pi {A = A} {A' = A'} {B = B} {B' = B'} dA dB cA cB) =
    AdqETy-to-AdqE1-U {T = Pi A B} {T' = Pi A' B'} (AdqETy-Pi (is-Ty-from-U dA) (is-Ty-from-U dB)
      (conv-Ty-from-U cA) (conv-Ty-from-U cB)
      (AdqConv-U-to-AdqConvTy {A = A} (adqTmC dA)) (AdqConv-U-to-AdqConvTy {A = B} (adqTmC dB))
      (AdqE1-U-to-AdqETy {A = A} {B = A'} (adqCTm cA)) (AdqE1-U-to-AdqETy {A = B} {B = B'} (adqCTm cB)))
  adqCTm (conv-cong-Lam-body dA dB db0 db) =
    AdqE1-Lam-body dA dB db0 db (adqTy dA)
      (AdqTy-Pi dA dB (adqTy dA) (adqTy dB) (adqTyC dB)) (adqTyC dB)
      (adqTm db0) (adqTmC db0) (adqCTm db)
  adqCTm (conv-cong-Lam-Ty dA dB cA cB db) =
    AdqE1-Lam-Ty dA dB cA cB db (adqTy dA)
      (AdqTy-Pi dA dB (adqTy dA) (adqTy dB) (adqTyC dB)) (adqTm db) (adqTmC db)
  adqCTm (conv-cong-App-fun dA dB dc da) =
    AdqE1-App-fun dA dB dc da (adqCTm dc) (adqTm da) (adqTy dB)
  adqCTm (conv-cong-App-arg dA dB dc da _) =
    AdqE1-App-arg dA dB dc da (Ann-refl dA dB) (Ann-refl dA dB) (adqTm dc) (adqTy dB) (adqCTm da)
  adqCTm (conv-cong-App-Ty {B = B} {B' = B'} dA dB cA cB dc da) =
    AdqE1-App-arg dA dB dc (conv-refl da)
      (Ann-refl dA dB) (mkAnn (conv-Ty-sym cA) (conv-Ty-sym cB))
      (adqTm dc) (AdqETy-to-AdqTy {A = B} {B = B'} (adqCTy cB))
      (\ sigma rho crho vs fits wt wfH u hu a evA fm ->
         Val2-to-EqVal2 u a (adqTm da sigma rho crho vs fits wt wfH u hu a evA fm))
  adqCTm (conv-beta dA dB db da) = AdqE1-beta dA dB db da (adqTm db) (adqTm da)
  adqCTm (conv-eta dA dB dc) = AdqE1-eta dA dB dc (adqTm dc)
