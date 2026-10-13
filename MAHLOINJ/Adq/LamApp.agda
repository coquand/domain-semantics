{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/LamApp.agda
--
-- Case lemmas: abstraction and application, from relation-functions.
------------------------------------------------------------------------

module MAHLOINJ.Adq.LamApp where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (FinEl ; UCode)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst using (EvalRel-subst1-backward)
open import MAHLOINJ.Model.SoundBase using (bodyOK)
open import MAHLOINJ.Model.Soundness using (sTm)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup using (pCv)
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Env
open import MAHLOINJ.Adq.Form using (CodRel)
open import MAHLOINJ.Adq.Lam
open import MAHLOINJ.Adq.App

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- body relations under every extension
  BodyRel : {A : Expr g} (t t' B : Expr (suc g)) -> Set
  BodyRel {A} t t' B = {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G A) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
    TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) t t' B

  lamR : (E : Env H G s s' rho) {A : Expr g} {B t : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) t B ->
    TyRelAt H s s' rho A A -> CodRel {A = A} B B -> BodyRel {A = A} t t B ->
    TmRelAt H s s' rho (Lam A t) (Lam A t) (PiB A B)
  lamR E {A} {B} {t} iA iB dt VA FB Ft c u ec cU eu uc = LC.lam c u ec cU eu uc
    where
      wH = Env.wH E ; cs = Env.cs E
      w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iAr = sbTy s' w2 wH iA
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) iB
      iBr = sbTy (liftSub s') (liftWS {A = A} w2 iAr) (wf-extend iAr) iB
      htl = sbTm (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) dt
      htr = sbTm (liftSub s') (liftWS {A = A} w2 iAr) (wf-extend iAr) dt
      eA = fTy s s' cs wH iA
      Bl = substExpr (liftSub s) B ; Br = substExpr (liftSub s') B
      qB : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) -> TyEq H (subst1 Bl N) (subst1 Br N')
      qB N N' cv = trTE (subst-consSub s N B) (subst-consSub s' N' B)
                     (fTy (consSub s N) (consSub s' N') (consC cs {A = A} (fst (pCv cv)) (ty-conv (snd (pCv cv)) eA) cv eA) wH iB)
      betaL : (N : Expr h) -> HasType H N (substExpr s A) ->
        ConvTm H (App (Lam (substExpr s A) (substExpr (liftSub s) t)) N) (subst1 (substExpr (liftSub s) t) N) (subst1 Bl N)
      betaL N hN = conv-beta iAl iBl htl hN
      betaR : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) ->
        ConvTm H (App (Lam (substExpr s' A) (substExpr (liftSub s') t)) N') (subst1 (substExpr (liftSub s') t) N') (subst1 Bl N)
      betaR N N' cv = conv-conv (conv-beta iAr iBr htr (ty-conv (snd (pCv cv)) eA)) (tyeq-sym (qB N N' cv))
      VB : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' (substExpr s A) ->
        ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> FinMem w a -> RTm H N N' (substExpr s A) w a) ->
        (b : FinEl) -> EvalRel A rho b -> FinMem w b ->
        (c : FinEl) -> EvalRel B (extendEnv rho w) c -> FinMem c UCode -> RTy H (subst1 Bl N) (subst1 Bl N) c
      VB N N' w cv RN b eb wb c ec cU =
        diagL {G = H} {T = subst1 Bl N} {T' = subst1 Br N'} c cU
          (transport2 (\ X Y -> RTy H X Y c) (subst-consSub s N B) (subst-consSub s' N' B)
            (FB (envExt E iA VA cv w b eb wb RN) c ec cU))
      FT : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' (substExpr s A) ->
        ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> FinMem w a -> RTm H N N' (substExpr s A) w a) ->
        (b : FinEl) -> EvalRel A rho b -> FinMem w b ->
        (c v : FinEl) -> EvalRel B (extendEnv rho w) c -> FinMem c UCode -> EvalRel t (extendEnv rho w) v -> FinMem v c ->
        RTm H (subst1 (substExpr (liftSub s) t) N) (subst1 (substExpr (liftSub s') t) N') (subst1 Bl N) v c
      FT N N' w cv RN b eb wb c v ec cU ev vc =
        transport3 (\ X Y Z -> RTm H X Y Z v c) (subst-consSub s N t) (subst-consSub s' N' t) (subst-consSub s N B)
          (Ft (envExt E iA VA cv w b eb wb RN) c v ec cU ev vc)
      module LC = LamCore (substExpr s A) (substExpr s' A) (substExpr (liftSub s) t) (substExpr (liftSub s') t) Bl
                    (EvalRel A rho) (\ x -> EvalRel t (extendEnv rho x)) (\ x -> EvalRel B (extendEnv rho x))
                    (EvalRel-ideal A rho (Env.crho E)) (bodyOK t rho (Env.crho E)) (bodyOK B rho (Env.crho E))
                    iAl iBl (\ a ea aU -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} a aU (VA a ea aU))
                    betaL betaR VB FT

  -- application, two-sided
  appR : (E : Env H G s s' rho) {A : Expr g} {B : Expr (suc g)} {t t' a a' : Expr g} ->
    HasType G t (PiB A B) -> ConvTm H (substExpr s a) (substExpr s' a') (substExpr s A) ->
    TmRelAt H s s' rho t t' (PiB A B) -> TmRelAt H s s' rho a a' A ->
    TyRelAt H s s' rho (subst1 B a) (subst1 B a) ->
    TmRelAt H s s' rho (App t a) (App t' a') (subst1 B a)
  appR E {A} {B} {t} {t'} {a} {a'} dt cN FM FN VT c v ec cU ev vc =
    transport (\ X -> RTm H (App (substExpr s t) (substExpr s a)) (App (substExpr s' t') (substExpr s' a')) X v c)
      (Eq-sym (subst-subst1-comm s B a)) (AC.app c v ec cU ev vc)
    where
      crho = Env.crho E
      VT' : (c : FinEl) -> EvalRel (subst1 B a) rho c -> FinMem c UCode ->
        RTy H (subst1 (substExpr (liftSub s) B) (substExpr s a)) (subst1 (substExpr (liftSub s) B) (substExpr s a)) c
      VT' c ec cU = transport (\ X -> RTy H X X c) (subst-subst1-comm s B a)
                      (diagL {G = H} {T = substExpr s (subst1 B a)} {T' = substExpr s' (subst1 B a)} c cU (VT c ec cU))
      module AC = AppCore (substExpr s t) (substExpr s' t') (substExpr s a) (substExpr s' a') (substExpr s A)
                    (substExpr (liftSub s) B)
                    (EvalRel t rho) (EvalRel a rho) (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (EvalRel (subst1 B a) rho)
                    (EvalRel-ideal t rho crho) (EvalRel-ideal a rho crho) (bodyOK B rho crho) (EvalRel-ideal (subst1 B a) rho crho)
                    (sTm dt rho (Env.fits E))
                    (\ w v ew ev -> EvalRel-subst1-backward B a rho w v crho ew ev)
                    FM (\ b w eb bU ew wb -> FN b w eb bU ew wb) cN VT'
