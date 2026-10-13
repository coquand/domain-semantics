{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Delta.agda
--
-- Helpers for the fundamental lemma: V, change of universe, instances
-- of a Pi-type's codomain, diagonals of two-sided relations, two-sided
-- abstraction, and the delta chains  f A F  and  g A F c.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Delta where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (LeCode ; FinMem)
open import MAHLOINJ.Model.Comb using (AtomS)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalFwd using (EvalRel-subst1-forward)
open import MAHLOINJ.Model.SoundBase using (bodyOK)
open import MAHLOINJ.Model.Soundness using (sTm)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.CtxConv using (ccTy)
open import MAHLOINJ.Syntax.Presup using (pCv ; bodyF)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Env
open import MAHLOINJ.Adq.Cod
open import MAHLOINJ.Adq.Lam
open import MAHLOINJ.Adq.Form using (CodRel)
open import MAHLOINJ.Adq.LamApp
open import MAHLOINJ.Adq.Syn

------------------------------------------------------------------------
-- V, and changing the universe of an element relation
------------------------------------------------------------------------

vRel : {h g : Num} {H : Ctx h} {G : Ctx g} -> TyIH H G V V
vRel E a ea aU = uTy (univR (univ-V refl) (isty-V (Env.wH E))) (univR (univ-V refl) (isty-V (Env.wH E))) a ea

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

reUnivAt : {n : Num} {H : Ctx n} {M M' T T' : Expr n} -> UnivR H T' -> (a u : FinEl) -> AtomS UCode a ->
  RTm H M M' T u a -> RTm H M M' T' u a
reUnivAt q Bot u e r = tmBot u
reUnivAt q UCode u e r = reUniv q u r

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

------------------------------------------------------------------------
-- two-sided abstraction  \x:A.t ~ \x:A'.t'  (common codomain B)
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  lamRX : (E : Env H G s s' rho) {A A' : Expr g} {B t t' : Expr (suc g)} ->
    IsType G A -> IsType G A' -> TyEq G A A' -> IsType (extend G A) B ->
    HasType (extend G A) t B -> HasType (extend G A') t' B ->
    TyRelAt H s s' rho A A -> CodRel {A = A} B B -> BodyRel {A = A} t t' B ->
    TmRelAt H s s' rho (Lam A t) (Lam A' t') (PiB A B)
  lamRX E {A} {A'} {B} {t} {t'} iA iA' qA iB dt dt' VA FB Ft c u ec cU eu uc = LC.lam c u ec cU eu uc
    where
      wH = Env.wH E ; cs = Env.cs E
      w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iAr = sbTy s' w2 wH iA'
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) iB
      iBr = sbTy (liftSub s') (liftWS {A = A'} w2 iAr) (wf-extend iAr) (ccTy iA' (tyeq-sym qA) iB)
      htl = sbTm (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) dt
      htr = sbTm (liftSub s') (liftWS {A = A'} w2 iAr) (wf-extend iAr) dt'
      eA = fTy s s' cs wH iA
      eA' = tyeq-trans eA (sbTE s' w2 wH qA)
      Bl = substExpr (liftSub s) B ; Br = substExpr (liftSub s') B
      qB : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) -> TyEq H (subst1 Bl N) (subst1 Br N')
      qB N N' cv = trTE (subst-consSub s N B) (subst-consSub s' N' B)
                     (fTy (consSub s N) (consSub s' N') (consC cs {A = A} (fst (pCv cv)) (ty-conv (snd (pCv cv)) eA) cv eA) wH iB)
      betaL : (N : Expr h) -> HasType H N (substExpr s A) ->
        ConvTm H (App (Lam (substExpr s A) (substExpr (liftSub s) t)) N) (subst1 (substExpr (liftSub s) t) N) (subst1 Bl N)
      betaL N hN = conv-beta iAl iBl htl hN
      betaR : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) ->
        ConvTm H (App (Lam (substExpr s' A') (substExpr (liftSub s') t')) N') (subst1 (substExpr (liftSub s') t') N') (subst1 Bl N)
      betaR N N' cv = conv-conv (conv-beta iAr iBr htr (ty-conv (snd (pCv cv)) eA')) (tyeq-sym (qB N N' cv))
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

------------------------------------------------------------------------
-- the delta chains
------------------------------------------------------------------------

  -- f A L : V
  fhatC : (E : Env H G s s' rho) {ff ff' A A' L L' : Expr g} ->
    HasType G ff OpF -> HasType G A V -> HasType G L (Arr A V) ->
    ConvTm H (substExpr s A) (substExpr s' A') V -> ConvTm H (substExpr s L) (substExpr s' L') (substExpr s (Arr A V)) ->
    TyRelAt H s s' rho OpF OpF -> TmRelAt H s s' rho ff ff' OpF ->
    TmRelAt H s s' rho A A V -> TmRelAt H s s' rho A A' V -> TmRelAt H s s' rho L L' (Arr A V) ->
    TmRelAt H s s' rho (App (App ff A) L) (App (App ff' A') L') V
  fhatC E {ff} {ff'} {A} {A'} {L} {L'} df dA dL cA cL DTf FMf FAd FA FL =
    appR E {A = Arr A V} {B = V} {t = App ff A} {t' = App ff' A'} {a = L} {a' = L'} dtFA cL FM1 FL (vRel E)
    where
      wG = Env.wG E
      Bf : Expr (suc g)
      Bf = Arr (Arr x0 V) V
      dtFA = ty-App (isty-V wG) (bodyF wG) df dA
      VT1 = substTyPi E {A = V} {B = Bf} {N = A} DTf dA FAd
      FM1 = appR E {A = V} {B = Bf} {t = ff} {t' = ff'} {a = A} {a' = A'} df cA FMf FA VT1

  -- g A L c : V
  ghatC : (E : Env H G s s' rho) {ff gg gg' A A' L L' c c' : Expr g} ->
    HasType G ff OpF -> HasType G gg (OpG ff) -> HasType G A V -> HasType G L (Arr A V) ->
    ConvTm H (substExpr s A) (substExpr s' A') V -> ConvTm H (substExpr s L) (substExpr s' L') (substExpr s (Arr A V)) ->
    ConvTm H (substExpr s c) (substExpr s' c') (substExpr s (App (App ff A) L)) ->
    TyRelAt H s s' rho (OpG ff) (OpG ff) -> TmRelAt H s s' rho gg gg' (OpG ff) ->
    TmRelAt H s s' rho A A V -> TmRelAt H s s' rho A A' V ->
    TmRelAt H s s' rho L L (Arr A V) -> TmRelAt H s s' rho L L' (Arr A V) ->
    TmRelAt H s s' rho c c' (App (App ff A) L) ->
    TmRelAt H s s' rho (App (App (App gg A) L) c) (App (App (App gg' A') L') c') V
  ghatC E {ff} {gg} {gg'} {A} {A'} {L} {L'} {c} {c'} df dg dA dL cA cL cC DTg FMg FAd FA FLd FL FC =
    appR E {A = App (App ff A) L} {B = V} {t = App (App gg A) L} {t' = App (App gg' A') L'} {a = c} {a' = c'}
      (gAL-ty df dg dA dL) cC r2' FC (vRel E)
    where
      Bg : Expr (suc g)
      Bg = PiB (Arr x0 V) (Arr (App (App (wkExpr (wkExpr ff)) x1) x0) V)
      C2 : Expr (suc g)
      C2 = Arr (App (App (wkExpr ff) (wkExpr A)) x0) V
      VT1 = substTyPi E {A = V} {B = Bg} {N = A} DTg dA FAd
      r1 = appR E {A = V} {B = Bg} {t = gg} {t' = gg'} {a = A} {a' = A'} dg cA FMg FA VT1
      r1' = transport (\ X -> TmRelAt H s s' rho (App gg A) (App gg' A') X) (gAE ff A) r1
      VT1' = transport (\ X -> TyRelAt H s s' rho X X) (gAE ff A) VT1
      VT2 = substTyPi E {A = Arr A V} {B = C2} {N = L} VT1' dL FLd
      r2 = appR E {A = Arr A V} {B = C2} {t = App gg A} {t' = App gg' A'} {a = L} {a' = L'} (gA-ty df dg dA) cL r1' FL VT2
      r2' = transport (\ X -> TmRelAt H s s' rho (App (App gg A) L) (App (App gg' A') L') X) (gAFE ff A L) r2
