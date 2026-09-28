{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.LamCong
--
-- The λ congruences of T_R:
--
--   conv-cong-Lam-body : λ(A,B,b) = λ(A,B,b')   : Π(A,B)
--   conv-cong-Lam-Ty   : λ(A,B,b) = λ(A',B',b)  : Π(A,B)
--
-- Both sides are valid λ's (Adeq.Lam); pointwise, their applications
-- β-reduce to b[P] and b'[P] (resp. b[P] twice), related by the body's
-- conversion IH (resp. reflexivity).  The right λ of Lam-body needs the
-- validity of b', obtained from the conversion IH and the two-sub
-- validity of b (Adq-right / AdqConv-right).
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.LamCong (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D
open import BCDE4.Adeq.Lam D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import BCDE4.Dom.Kernel using (EvalFun ; FinMem ; FinMem-coh-u ; FinMem-a-in-U ;
  finMem-funel-fun ; finMem-funel-coh)
open import BCDE4.Model.Eval D using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ; EvalRel-coh)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; Lam ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  liftSub-WtSub ; isType-Pi ; presup-r-ConvTm)
open import BCDE4.RussellReduction using (headred-refl ; headred-step ; headred-beta)

open import BCDE4.Levels using (LCtx ; LSub ; lidS)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- The right end of a conversion is valid.
------------------------------------------------------------------------

Adq-right : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  ConvTm G M N A -> AdqE1 G M N A -> Adq G N A
Adq-right d IH sigma rho crho vs fits wt wfH u hu a evA fm =
  Val2-from-EqVal2-second u a (IH sigma rho crho vs fits wt wfH u (evBwd-Tm d rho fits u hu) a evA fm)

AdqConv-right : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  ConvTm G M N A -> AdqE1 G M N A -> AdqConv G M A -> AdqConvTy G A -> AdqConv G N A
AdqConv-right {A = A} d IH IH-cM IH-cA sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm =
  EqVal2-trans u a cu ca e1 (EqVal2-trans u a cu ca e2 e3)
  where
    huM = evBwd-Tm d rho fits u hu
    cu  = FinMem-coh-u u a fm
    ca  = EvalRel-coh (strip A) rho a evA
    e1  = EqVal2-sym u a cu ca (IH sigma rho crho vs fits wt wfH u huM a evA fm)
    e2  = IH-cM sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u huM a evA fm
    tyE = IH-cA sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a evA (FinMem-a-in-U u a fm)
    e3  = EqVal2-EqValTy2-fwd u a ca (EqValTy2-sym a ca tyE)
            (IH sigma' rho crho vs' fits wt' wfH u huM a evA fm)

------------------------------------------------------------------------
-- conv-cong-Lam-body
------------------------------------------------------------------------

private
  lamBody-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B M M' : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) M B -> ConvTm (extend G A) M M' B ->
    AdqTy G A -> AdqTy G (Pi A B) -> AdqConvTy (extend G A) B ->
    Adq (extend G A) M B -> AdqConv (extend G A) M B -> AdqE1 (extend G A) M M' B ->
    (sigma : Sub h g) -> (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) -> EvalRel (strip (Lam A B M)) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) -> EvalRel (strip (Pi A B)) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    EqVal2 H (substExpr sigma (Lam A B M)) (substExpr sigma (Lam A B M'))
             (substExpr sigma (Pi A B)) (FunEl g0) (PiCode b f0)
  lamBody-core {H = H} {G = G} {A = A} {B = B} {M = M} {M' = M'} d1 d2 d3 dM
      IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
    mk-EqValPi (valPi-ty L) (un-ValPi L) (un-ValPi R)
      (record { domA0 = sA ; codB0 = sB ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
              ; cohG = finMem-funel-coh g0 b f0 fm ; fmG = finMem-funel-fun g0 b f0 fm ; appEV = ev })
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sM  = substExpr (liftSub sigma) M
      sM' = substExpr (liftSub sigma) M'
      wsL = liftSub-WtSub wtsub wfH d1
      htA = subst-IsType wtsub wfH d1
      htB = subst-IsType wsL (wf-extend htA) d2
      htM = subst-HasType wsL (wf-extend htA) d3
      htM' = subst-HasType wsL (wf-extend htA) (presup-r-ConvTm dM)
      rflA = conv-Ty-refl d1 ; rflB = conv-Ty-refl d2
      hu'  = evFwd-Tm (conv-cong-Lam-body d1 d2 d3 dM) rho fits (FunEl g0) hu
      L = adequacy-ty-Lam d1 d2 d3 rflA rflB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm
      R = adequacy-ty-Lam d1 d2 (presup-r-ConvTm dM) rflA rflB IH-A IH-Pi
            (Adq-right dM IH-E) (AdqConv-right dM IH-E IH-cM IH-cB)
            sigma rho crho vs fits wtsub wfH g0 hu' b f0 evA fm
      ev : PiAppEqVal2 H (Lam sA sB sM) (Lam sA sB sM') sA sB b f0 g0
      ev u' v' sel an1 an2 P htP valP =
        let ls  = lamSel {A = A} {A' = A} {B = B} {B' = B} {M = M} IH-A sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm
                    u' v' sel P htP valP
            open LamSel ls
            raw = IH-E (extSub sigma P) (extendEnv rho u') crho' vs' fits' wt' wfH v' evM (EvalFun f0 u') evB fmv
            raw' = S.Eq-transport (\ T -> EqVal2 H (subst1 sM P) T (subst1 sB P) v' (EvalFun f0 u'))
                     (S.Eq-sym (substExpr-comp sigma M' P))
                     (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma P) M') (subst1 sB P) v' (EvalFun f0 u'))
                        (S.Eq-sym (substExpr-comp sigma M P))
                        (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u'))
                           (S.Eq-sym (substExpr-comp sigma B P)) raw))
        in EqVal2-headred-expand v' (EvalFun f0 u')
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
             (beta-ann htA htB htM an1 htP) (beta-ann htA htB htM' an2 htP) raw'

AdqE1-Lam-body : {g : Nat} {G : Ctx g} {A : Expr g} {B M M' : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) M B -> ConvTm (extend G A) M M' B ->
  AdqTy G A -> AdqTy G (Pi A B) -> AdqConvTy (extend G A) B ->
  Adq (extend G A) M B -> AdqConv (extend G A) M B -> AdqE1 (extend G A) M M' B ->
  AdqE1 G (Lam A B M) (Lam A B M') (Pi A B)
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH Bot          hu a evA fm = EqVal2-Bot a
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (UCode _)    () a evA fm
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (PiCode _ _) () a evA fm
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (FunEl g0) hu Bot evA fm = tt
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (FunEl g0) hu (UCode _) () fm
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (FunEl g0) hu (FunEl _) () fm
AdqE1-Lam-body d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH (FunEl g0) hu (PiCode b f0) evA fm =
  lamBody-core d1 d2 d3 dM IH-A IH-Pi IH-cB IH-M IH-cM IH-E sigma rho crho vs fits wt wfH g0 hu b f0 evA fm

------------------------------------------------------------------------
-- conv-cong-Lam-Ty
------------------------------------------------------------------------

private
  lamTy-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' M : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' ->
    HasType (extend G A) M B ->
    AdqTy G A -> AdqTy G (Pi A B) -> Adq (extend G A) M B -> AdqConv (extend G A) M B ->
    (sigma : Sub h g) -> (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) -> EvalRel (strip (Lam A B M)) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) -> EvalRel (strip (Pi A B)) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    EqVal2 H (substExpr sigma (Lam A B M)) (substExpr sigma (Lam A' B' M))
             (substExpr sigma (Pi A B)) (FunEl g0) (PiCode b f0)
  lamTy-core {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'} {M = M} d1 d2 cA cB d3
      IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
    mk-EqValPi (valPi-ty L) (un-ValPi L) (un-ValPi R)
      (record { domA0 = sA ; codB0 = sB ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
              ; cohG = finMem-funel-coh g0 b f0 fm ; fmG = finMem-funel-fun g0 b f0 fm ; appEV = ev })
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sM  = substExpr (liftSub sigma) M
      wsL = liftSub-WtSub wtsub wfH d1
      htA = subst-IsType wtsub wfH d1
      htB = subst-IsType wsL (wf-extend htA) d2
      htM = subst-HasType wsL (wf-extend htA) d3
      scA = subst-ConvTy wtsub wfH cA
      scB = subst-ConvTy wsL (wf-extend htA) cB
      rflA = conv-Ty-refl d1 ; rflB = conv-Ty-refl d2
      hu'  = evFwd-Tm (conv-cong-Lam-Ty d1 d2 cA cB d3) rho fits (FunEl g0) hu
      L = adequacy-ty-Lam d1 d2 d3 rflA rflB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm
      R = adequacy-ty-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu' b f0 evA fm
      ev : PiAppEqVal2 H (Lam sA sB sM) (substExpr sigma (Lam A' B' M)) sA sB b f0 g0
      ev u' v' sel an1 an2 P htP valP =
        let ls  = lamSel {A = A} {A' = A} {B = B} {B' = B} {M = M} IH-A sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm
                    u' v' sel P htP valP
            open LamSel ls
            raw = IH-M (extSub sigma P) (extendEnv rho u') crho' vs' fits' wt' wfH v' evM (EvalFun f0 u') evB fmv
            raw' = S.Eq-transport (\ T -> Val2 H T (subst1 sB P) v' (EvalFun f0 u'))
                     (S.Eq-sym (substExpr-comp sigma M P))
                     (S.Eq-transport (\ T -> Val2 H _ T v' (EvalFun f0 u'))
                        (S.Eq-sym (substExpr-comp sigma B P)) raw)
        in EqVal2-headred-expand v' (EvalFun f0 u')
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
             (beta-ann htA htB htM an1 htP) (beta-ann-conv htA htB htM scA scB an2 htP)
             (Val2-to-EqVal2 v' (EvalFun f0 u') raw')

AdqE1-Lam-Ty : {g : Nat} {G : Ctx g} {A A' : Expr g} {B B' M : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' ->
  HasType (extend G A) M B ->
  AdqTy G A -> AdqTy G (Pi A B) -> Adq (extend G A) M B -> AdqConv (extend G A) M B ->
  AdqE1 G (Lam A B M) (Lam A' B' M) (Pi A B)
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH Bot          hu a evA fm = EqVal2-Bot a
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (UCode _)    () a evA fm
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (PiCode _ _) () a evA fm
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (FunEl g0) hu Bot evA fm = tt
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (FunEl g0) hu (UCode _) () fm
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (FunEl g0) hu (FunEl _) () fm
AdqE1-Lam-Ty d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH (FunEl g0) hu (PiCode b f0) evA fm =
  lamTy-core d1 d2 cA cB d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wt wfH g0 hu b f0 evA fm
