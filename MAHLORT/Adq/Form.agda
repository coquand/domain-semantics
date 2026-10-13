{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Form.agda  (Tarski port of MAHLOINJ/Adq/Form)
--
-- Case lemma: Pi / Sigma formation, two-sided, from the relations of
-- the domains and (under extended environments) of the codomains.
------------------------------------------------------------------------

module MAHLORT.Adq.Form where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (FinEl ; UCode)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLORT.Model
open import MAHLORT.Model using (bodyOK)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.CtxConv using (ccTy)
open import MAHLORT.Syntax.Presup using (pTE)
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Code

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- codomain relations under every extension
  CodRel : {A : Expr g} (B B' : Expr (suc g)) -> Set
  CodRel {A} B B' = {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G A) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
    TyRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) B B'

  module FormX (E : Env H G s s' rho) {A A' : Expr g} {B B' : Expr (suc g)}
    (iA : IsType G A) (iB : IsType (extend G A) B) (iA' : IsType G A') (iB' : IsType (extend G A') B')
    (qA : TyEq G A A') (qB : TyEq (extend G A) B B')
    (VA : TyRelAt H s s' rho A A) (DA : TyRelAt H s s' rho A A') (FB : CodRel {A} B B') where

    private
      wH = Env.wH E ; cs = Env.cs E
      w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iAr = sbTy s' w2 wH iA'
      wl = wf-extend iAl
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) wl iB
      iBr = sbTy (liftSub s') (liftWS {A = A'} w2 iAr) (wf-extend iAr) iB'
      eAA = fTy s s' cs wH iA
      eA = tyeq-trans eAA (sbTE s' w2 wH qA)
      lc = liftC cs {A = A} iAl eAA
      eB = tyeq-trans (fTy (liftSub s) (liftSub s') lc wl iB) (sbTE (liftSub s') (CSub.w2 lc) wl qB)
      FBc : (N N' : Expr h) (w : FinEl) -> ConvTm H N N' (substExpr s A) ->
        ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> FinMem w a -> RTm H N N' (substExpr s A) w a) ->
        (b : FinEl) -> EvalRel A rho b -> FinMem w b ->
        (c : FinEl) -> EvalRel B (extendEnv rho w) c -> FinMem c UCode ->
        RTy H (subst1 (substExpr (liftSub s) B) N) (subst1 (substExpr (liftSub s') B') N') c
      FBc N N' w cv RN b eb wb c ec cU =
        transport2 (\ X Y -> RTy H X Y c) (subst-consSub s N B) (subst-consSub s' N' B')
          (FB (envExt E iA VA cv w b eb wb RN) c ec cU)
      module CC = CodeCore (substExpr s A) (substExpr s' A') (substExpr (liftSub s) B) (substExpr (liftSub s') B')
                    (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (EvalRel-ideal A rho (Env.crho E))
                    (bodyOK B rho (Env.crho E)) iAl iBl iAr iBr eA eB
                    (\ a ea aU -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} a aU (VA a ea aU)) DA FBc

    piR : TyRelAt H s s' rho (PiB A B) (PiB A' B')
    piR = CC.piTy

    sigR : TyRelAt H s s' rho (SigmaB A B) (SigmaB A' B')
    sigR = CC.sigTy

  -- the diagonal instance
  module Form (E : Env H G s s' rho) {A : Expr g} {B : Expr (suc g)}
    (iA : IsType G A) (iB : IsType (extend G A) B) (VA : TyRelAt H s s' rho A A) (FB : CodRel {A} B B) where

    open FormX E iA iB iA iB (tyeq-refl iA) (tyeq-refl iB) VA VA FB public
