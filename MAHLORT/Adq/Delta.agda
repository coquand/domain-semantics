{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Delta.agda  (Tarski port: the generic part of MAHLOINJ/Adq/Delta)
--
-- Helpers for the fundamental lemma: V, change of universe, instances
-- of a Pi-type's codomain, diagonals of two-sided relations, two-sided
-- abstraction.  (The Russell delta chains are replaced by the
-- T^-equations, MAHLORT/Adq/Codes.)
------------------------------------------------------------------------

module MAHLORT.Adq.Delta where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (LeCode ; FinMem)
open import MAHLOINJ.Model.Comb using (AtomS)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.CtxConv using (ccTy)
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Cod
open import MAHLORT.Adq.Lam
open import MAHLORT.Adq.Form using (CodRel)
open import MAHLORT.Adq.LamApp

------------------------------------------------------------------------
-- V, and changing the universe of an element relation
------------------------------------------------------------------------

vRel : {h g : Num} {H : Ctx h} {G : Ctx g} -> TyIH H G V V
vRel E a ea aU = uTy (univR (univ-V refl) (isty-V (Env.wH E))) (univR (univ-V refl) (isty-V (Env.wH E))) kV a ea

tmBot : {n : Num} {H : Ctx n} {M M' T : Expr n} (u : FinEl) -> RTm H M M' T u Bot
tmBot Bot = tt
tmBot UCode = tt
tmBot (FunEl _) = tt
tmBot (PiCode _ _) = tt
tmBot NatCode = tt
tmBot ZeroEl = tt
tmBot (SucEl _) = tt
tmBot (PairEl _ _) = tt
tmBot (SigmaCode _ _) = tt

-- the element of V coding V
uUC : AtomS UCode UCode
uUC = mkSigma tt tt

------------------------------------------------------------------------
-- instances of a Pi-type's codomain, via singleton codes
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  substTyPi : (E : Env H G s s' rho) {A : Expr g} {B : Expr (suc g)} {N : Expr g} ->
    TyRelAt H s s' rho (PiB A B) (PiB A B) -> HasType G N A -> TmRelAt H s s' rho N N A ->
    TyRelAt H s s' rho (subst1 B N) (subst1 B N)
  substTyPi E {A} {B} {N} DT dN FN c ec cU =
    let crho = Env.crho E
        fw = EvalRel-subst1-forward B N rho c crho ec
        x = dfst fw ; ex = dfst (dsnd fw) ; cx = dsnd (dsnd fw)
        t = sTm dN rho (Env.fits E) x ex
        y = dfst t ; a' = dfst (dsnd t) ; lxy = dfst (dsnd (dsnd t)) ; ey = dfst (dsnd (dsnd (dsnd t)))
        ya = dfst (dsnd (dsnd (dsnd (dsnd t)))) ; ea = dsnd (dsnd (dsnd (dsnd (dsnd t))))
        cohx = EvalRel-coh N rho crho x ex
        cohy = EvalRel-coh N rho crho y ey
        cy = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho y)
               (mkSigma (EnvLe-refl rho crho) (mkSigma cohx (mkSigma cohy lxy))) c cx
        cN = fst (fTm s s' (Env.cs E) (Env.wH E) dN)
        r = CodCore.PiCod.cod (substExpr s A) (substExpr s' A) (substExpr (liftSub s) B) (substExpr (liftSub s') B)
              (EvalRel A rho) (\ z -> EvalRel B (extendEnv rho z)) (EvalRel-ideal A rho crho) (bodyOK B rho crho)
              DT (substExpr s N) (substExpr s' N) y a' c cN (\ a0 ea0 aU0 ya0 -> FN a0 y ea0 aU0 ey ya0)
              ea (FinMem-a-in-U' y a' ya) ya cy cU
    in transport2 (\ X Y -> RTy H X Y c) (Eq-sym (subst-subst1-comm s B N)) (Eq-sym (subst-subst1-comm s' B N)) r
    where
      FinMem-a-in-U' = MAHLOINJ.Domain.Kernel.FinMem-a-in-U

------------------------------------------------------------------------
-- diagonal of a two-sided relation
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  diagC : {M M' T : Expr g} -> TmIH H G M M' T -> TyIH H G T T -> TmIH H G M M T
  diagC {M} {M'} {T} F VT {s} {s'} {rho} E a u ea aU eu ua =
    let r1 = F E a u ea aU eu ua
        r2 = F (envR E) a u ea aU eu ua
        vt = VT E a ea aU
        r2' = pConvM {G = H} {M = substExpr s' M'} {M' = substExpr s' M} {T = substExpr s' T} {T' = substExpr s T}
                u a ua aU (pSymT {G = H} {T = substExpr s T} {T' = substExpr s' T} a aU vt)
                (pSymM {G = H} {M = substExpr s' M} {M' = substExpr s' M'} {T = substExpr s' T} u a ua aU
                   (diagR {G = H} {T = substExpr s T} {T' = substExpr s' T} a aU vt) r2)
    in pTransM {G = H} {M1 = substExpr s M} {M2 = substExpr s' M'} {M3 = substExpr s' M} {T = substExpr s T}
         u a ua aU (diagL {G = H} {T = substExpr s T} {T' = substExpr s' T} a aU vt) r1 r2'

