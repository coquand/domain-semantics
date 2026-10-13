{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/LamApp.agda  (Tarski port of MAHLOINJ/Adq/LamApp)
--
-- Case lemmas: abstraction and application, from relation-functions.
------------------------------------------------------------------------

module MAHLORT.Adq.LamApp where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (FinEl ; UCode)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Syntax.CtxConv using (ccTE ; ccTm ; ccTy)
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Form using (CodRel)
open import MAHLORT.Adq.Lam
open import MAHLORT.Adq.App

-- beta at an arbitrary convertible annotation
betaAnn : {n : Num} {H : Ctx n} {A A0 N : Expr n} {B B0 t : Expr (suc n)} ->
  IsType H A -> IsType (extend H A) B -> HasType (extend H A) t B ->
  TyEq H A A0 -> TyEq (extend H A) B B0 -> HasType H N A ->
  ConvTm H (appB A0 B0 (Lam A t) N) (subst1 t N) (subst1 B N)
betaAnn iA iB ht e0 e1 hN =
  conv-trans (conv-sym (conv-App iA iB e0 e1 (conv-refl (ty-Lam iA iB ht)) (conv-refl hN))) (conv-beta iA iB ht hN)

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- body relations under every extension
  BodyRel : {A : Expr g} (t t' B : Expr (suc g)) -> Set
  BodyRel {A} t t' B = {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G A) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
    TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) t t' B

  -- abstraction, two-sided:  \x:A.t = \x:A'.t'  (conv-Lam; t' typed in the context of A)
  lamR : (E : Env H G s s' rho) {A A' : Expr g} {B t t' : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) t B -> IsType G A' -> TyEq G A A' ->
    HasType (extend G A) t' B ->
    TyRelAt H s s' rho A A -> CodRel {A = A} B B -> BodyRel {A = A} t t' B ->
    TmRelAt H s s' rho (Lam A t) (Lam A' t') (PiB A B)
  lamR E {A} {A'} {B} {t} {t'} iA iB dt iA' eAA' dt' VA FB Ft c u ec cU eu uc = LC.lam c u ec cU eu uc
    where
      wH = Env.wH E ; cs = Env.cs E
      w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iAr = sbTy s' w2 wH iA'
      eA = fTy s s' cs wH iA
      eAr : TyEq H (substExpr s A) (substExpr s' A')
      eAr = tyeq-trans eA (sbTE s' w2 wH eAA')
      cU' = liftC cs iAl eA
      iBl = sbTy (liftSub s) (CSub.w1 cU') (wf-extend iAl) iB
      htl = sbTm (liftSub s) (CSub.w1 cU') (wf-extend iAl) dt
      -- the right body, in the context of A'
      dt'' : HasType (extend G A') t' B
      dt'' = ccTm iA' (tyeq-sym eAA') dt'
      iB' : IsType (extend G A') B
      iB' = ccTy iA' (tyeq-sym eAA') iB
      iBr = sbTy (liftSub s') (liftWS {A = A'} w2 iAr) (wf-extend iAr) iB'
      htr = sbTm (liftSub s') (liftWS {A = A'} w2 iAr) (wf-extend iAr) dt''
      Bl = substExpr (liftSub s) B ; Br = substExpr (liftSub s') B
      eB : TyEq (extend H (substExpr s A)) Bl Br
      eB = fTy (liftSub s) (liftSub s') cU' (wf-extend iAl) iB
      qB : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) -> TyEq H (subst1 Bl N) (subst1 Br N')
      qB N N' cv = trTE (subst-consSub s N B) (subst-consSub s' N' B)
                     (fTy (consSub s N) (consSub s' N') (consC cs {A = A} (fst (pCv cv)) (ty-conv (snd (pCv cv)) eA) cv eA) wH iB)
      betaL : (A0 : Expr h) (B0 : Expr (suc h)) -> TyEq H (substExpr s A) A0 -> TyEq (extend H (substExpr s A)) Bl B0 ->
        (N : Expr h) -> HasType H N (substExpr s A) ->
        ConvTm H (appB A0 B0 (Lam (substExpr s A) (substExpr (liftSub s) t)) N) (subst1 (substExpr (liftSub s) t) N) (subst1 Bl N)
      betaL A0 B0 e0 e1 N hN = betaAnn iAl iBl htl e0 e1 hN
      betaR : (A1 : Expr h) (B1 : Expr (suc h)) -> TyEq H (substExpr s A) A1 -> TyEq (extend H (substExpr s A)) Bl B1 ->
        (N N' : Expr h) -> ConvTm H N N' (substExpr s A) ->
        ConvTm H (appB A1 B1 (Lam (substExpr s' A') (substExpr (liftSub s') t')) N') (subst1 (substExpr (liftSub s') t') N') (subst1 Bl N)
      betaR A1 B1 e2 e3 N N' cv =
        conv-conv (betaAnn iAr iBr htr (tyeq-trans (tyeq-sym eAr) e2)
                     (ccTE iAr (tyeq-sym eAr) (tyeq-trans (tyeq-sym eB) e3))
                     (ty-conv (snd (pCv cv)) eAr))
                  (tyeq-sym (qB N N' cv))
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
        RTm H (subst1 (substExpr (liftSub s) t) N) (subst1 (substExpr (liftSub s') t') N') (subst1 Bl N) v c
      FT N N' w cv RN b eb wb c v ec cU ev vc =
        transport3 (\ X Y Z -> RTm H X Y Z v c) (subst-consSub s N t) (subst-consSub s' N' t') (subst-consSub s N B)
          (Ft (envExt E iA VA cv w b eb wb RN) c v ec cU ev vc)
      module LC = LamCore (substExpr s A) (substExpr s' A') (substExpr (liftSub s) t) (substExpr (liftSub s') t') Bl
                    (EvalRel A rho) (\ x -> EvalRel t (extendEnv rho x)) (\ x -> EvalRel B (extendEnv rho x))
                    (EvalRel-ideal A rho (Env.crho E)) (bodyOK t rho (Env.crho E)) (bodyOK B rho (Env.crho E))
                    iAl iBl (\ a ea aU -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} a aU (VA a ea aU))
                    betaL betaR VB FT

  -- application, two-sided:  app(A,B,t,a) = app(A',B',t',a')  (conv-App)
  appR : (E : Env H G s s' rho) {A A' : Expr g} {B B' : Expr (suc g)} {t t' a a' : Expr g} ->
    IsType G A -> IsType (extend G A) B -> TyEq G A A' -> TyEq (extend G A) B B' ->
    HasType G t (PiB A B) -> ConvTm H (substExpr s a) (substExpr s' a') (substExpr s A) ->
    TmRelAt H s s' rho t t' (PiB A B) -> TmRelAt H s s' rho a a' A ->
    TyRelAt H s s' rho (subst1 B a) (subst1 B a) ->
    TmRelAt H s s' rho (appB A B t a) (appB A' B' t' a') (subst1 B a)
  appR E {A} {A'} {B} {B'} {t} {t'} {a} {a'} iA iB eAA' eBB' dt cN FM FN VT c v ec cU ev vc =
    transport (\ X -> RTm H (substExpr s (appB A B t a)) (substExpr s' (appB A' B' t' a')) X v c)
      (Eq-sym (subst-subst1-comm s B a)) (AC.app c v ec cU ev vc)
    where
      crho = Env.crho E
      wH = Env.wH E ; cs = Env.cs E
      iAs = sbTy s (CSub.w1 cs) wH iA
      eA = fTy s s' cs wH iA
      cU' = liftC cs iAs eA
      iBs = sbTy (liftSub s) (CSub.w1 cU') (wf-extend iAs) iB
      e2 : TyEq H (substExpr s A) (substExpr s' A')
      e2 = tyeq-trans eA (sbTE s' (CSub.w2 cs) wH eAA')
      e3 : TyEq (extend H (substExpr s A)) (substExpr (liftSub s) B) (substExpr (liftSub s') B')
      e3 = tyeq-trans (fTy (liftSub s) (liftSub s') cU' (wf-extend iAs) iB)
             (sbTE (liftSub s') (CSub.w2 cU') (wf-extend iAs) eBB')
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
                    FM (\ b w eb bU ew wb -> FN b w eb bU ew wb)
                    (substExpr s A) (substExpr s' A') (substExpr (liftSub s) B) (substExpr (liftSub s') B')
                    (tyeq-refl iAs) (tyeq-refl iBs) e2 e3 cN VT'
