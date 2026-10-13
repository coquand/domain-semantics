{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Sig.agda
--
-- Case lemmas for Sigma: projections, pairs, pair extensionality.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Sig where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; PairEl ; SigmaCode ; FinFun ; mkSigma)
  renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; NotBot ; FinMem-a-in-U ; FinMem-coh-u ; finMemC-pair-fst ; finMemC-pair-snd)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-elim)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst using (EvalRel-subst1-backward)
open import MAHLOINJ.Model.SoundBase using (bodyOK)
open import MAHLOINJ.Model.Soundness using (sTm)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup using (pCv ; pTm)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Props using (CodeU ; sigU)
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Sem
open import MAHLOINJ.Adq.Env

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  -- first projection
  fstR : {A : Expr g} {B : Expr (suc g)} {t t' : Expr g} -> HasType G t (SigmaB A B) ->
    TyIH H G A A -> TmIH H G t t' (SigmaB A B) -> TmIH H G (Fst t) (Fst t') A
  fstR {A} {B} {t} {t'} dt VA Ft {s} {s'} {rho} E a u ea aU eu ua = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> RTm H (Fst (substExpr s t)) (Fst (substExpr s' t')) (substExpr s A) u a
      go (left refl) = tt
      go (right nb) = pick (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                        (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
        where
          ts = sTm dt rho (Env.fits E) (PairEl u Bot) (guard-elim u nb eu)
          pick : (p1 a1 : FinEl) -> LeCode (PairEl u Bot) p1 -> EvalRel t rho p1 -> FinMem p1 a1 ->
                 EvalRel (SigmaB A B) rho a1 -> RTm H (Fst (substExpr s t)) (Fst (substExpr s' t')) (substExpr s A) u a
          pick (PairEl x1 x2) (SigmaCode b f) le ep1 m ea1 =
            let a1U = FinMem-a-in-U (PairEl x1 x2) (SigmaCode b f) m
                cu = sigU b f a1U
                r = pairV (Ft E (SigmaCode b f) (PairEl x1 x2) ea1 a1U ep1 m)
                fr = sigFst r
            in adj (EvalRel A rho) (EvalRel-ideal A rho (Env.crho E))
                 (\ c ec cU -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} c cU (VA E c ec cU))
                 x1 b (dfst (dsnd ea1)) (CodeU.bU cu) (finMemC-pair-fst x1 x2 b f m) fr u a ea aU (dfst le) ua

  -- second projection
  sndR : {A : Expr g} {B : Expr (suc g)} {t t' : Expr g} -> IsType (extend G A) B -> HasType G t (SigmaB A B) ->
    TyIH H G (subst1 B (Fst t)) (subst1 B (Fst t)) -> TmIH H G t t' (SigmaB A B) ->
    TmIH H G (Snd t) (Snd t') (subst1 B (Fst t))
  sndR {A} {B} {t} {t'} iB dt VT Ft {s} {s'} {rho} E c u ec cU eu uc = go (bot-or u)
    where
      crho = Env.crho E
      T = subst1 B (Fst t)
      go : Or (Eq u Bot) (NotBot u) -> RTm H (Snd (substExpr s t)) (Snd (substExpr s' t')) (substExpr s T) u c
      go (left refl) = tt
      go (right nb) = pick (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                        (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
        where
          ts = sTm dt rho (Env.fits E) (PairEl Bot u) (guard-elim u nb eu)
          pick : (p1 a1 : FinEl) -> LeCode (PairEl Bot u) p1 -> EvalRel t rho p1 -> FinMem p1 a1 ->
                 EvalRel (SigmaB A B) rho a1 -> RTm H (Snd (substExpr s t)) (Snd (substExpr s' t')) (substExpr s T) u c
          pick (PairEl x1 x2) (SigmaCode b f) le ep1 m ea1 =
            let a1U = FinMem-a-in-U (PairEl x1 x2) (SigmaCode b f) m
                cu = sigU b f a1U
                x1b = finMemC-pair-fst x1 x2 b f m
                r = pairV (Ft E (SigmaCode b f) (PairEl x1 x2) ea1 a1U ep1 m)
                sr = transport (\ X -> RTm H (Snd (substExpr s t)) (Snd (substExpr s' t')) X x2 (EvalFun f x1))
                       (Eq-sym (subst-subst1-comm s B (Fst t))) (sigSnd r)
                cx1 = FinMem-coh-u x1 b x1b
                ex1 = fstOf (EvalRel t rho) (EvalRel-ideal t rho crho) x1 x2 ep1
                ee = EvalRel-subst1-backward B (Fst t) rho x1 (EvalFun f x1) crho ex1
                       (famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                          (CodeU.cft cu) (dsnd (dsnd ea1)) x1 cx1)
            in adj (EvalRel T rho) (EvalRel-ideal T rho crho)
                 (\ c' ec' cU' -> diagL {G = H} {T = substExpr s T} {T' = substExpr s' T} c' cU' (VT E c' ec' cU'))
                 x2 (EvalFun f x1) ee (efU b f cu x1b) (finMemC-pair-snd x1 x2 b f m) sr u c ec cU (dsnd le) uc

  -- pair extensionality (two-sided)
  pairextR : {A : Expr g} {B : Expr (suc g)} {t t' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    HasType G t (SigmaB A B) -> HasType G t' (SigmaB A B) -> ConvTm G (Fst t) (Fst t') A ->
    TmIH H G (Fst t) (Fst t') A -> TmIH H G (Snd t) (Snd t') (subst1 B (Fst t)) ->
    TmIH H G t t' (SigmaB A B)
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 F1 F2 {s} {s'} {rho} E Bot p ec cU ep pc = goB p
    where
      goB : (p : FinEl) -> RTm H (substExpr s t) (substExpr s' t') (substExpr s (SigmaB A B)) p Bot
      goB Bot = tt
      goB UCode = tt
      goB (D.FunEl _) = tt
      goB (D.PiCode _ _) = tt
      goB D.NatCode = tt
      goB D.ZeroEl = tt
      goB (D.SucEl _) = tt
      goB (PairEl _ _) = tt
      goB (SigmaCode _ _) = tt
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 F1 F2 {s} {s'} {rho} E (SigmaCode b f) Bot ec cU ep pc = tt
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 F1 F2 {s} {s'} {rho} E (SigmaCode b f) (PairEl u1 u2) ec cU ep pc =
    pairM (record
      { A = substExpr s A ; B = substExpr (liftSub s) B ; rT = hrs-refl
      ; tT = tyeq-refl (isty-Sigma iAl iBl) ; iA = iAl ; iB = iBl
      ; cF = conv-trans (sbCv s w1 wH d1) (fst (fTm s s' cs wH (ty-Fst iA iB dt')))
      ; fstR = F1 E b u1 eb (CodeU.bU cu) eu1 u1b
      ; sndR = transport (\ X -> RTm H (Snd (substExpr s t)) (Snd (substExpr s' t')) X u2 (EvalFun f u1))
                 (subst-subst1-comm s B (Fst t)) (F2 E (EvalFun f u1) u2 ee (efU b f cu u1b) eu2 u2e) })
    where
      crho = Env.crho E ; wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      iAl = sbTy s w1 wH iA
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) iB
      cu = sigU b f cU
      eb = dfst (dsnd ec)
      u1b = finMemC-pair-fst u1 u2 b f pc
      u2e = finMemC-pair-snd u1 u2 b f pc
      eu1 = fstOf (EvalRel t rho) (EvalRel-ideal t rho crho) u1 u2 ep
      eu2 = sndOf (EvalRel t rho) (EvalRel-ideal t rho crho) u1 u2 ep
      ee = EvalRel-subst1-backward B (Fst t) rho u1 (EvalFun f u1) crho eu1
             (famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                (CodeU.cft cu) (dsnd (dsnd ec)) u1 (FinMem-coh-u u1 b u1b))

  -- pairs
  pairR : {A : Expr g} {B : Expr (suc g)} {t u : Expr g} -> IsType G A -> IsType (extend G A) B ->
    HasType G t A -> HasType G u (subst1 B t) ->
    TyIH H G A A -> TyIH H (extend G A) B B -> TmIH H G t t A -> TmIH H G u u (subst1 B t) ->
    TmIH H G (Pair t u) (Pair t u) (SigmaB A B)
  pairR {A} {B} {t} {u} iA iB dt du VA ATB Ft Fu {s} {s'} {rho} E Bot p ec cU ep pc = goB p
    where
      goB : (p : FinEl) -> RTm H (substExpr s (Pair t u)) (substExpr s' (Pair t u)) (substExpr s (SigmaB A B)) p Bot
      goB Bot = tt
      goB UCode = tt
      goB (D.FunEl _) = tt
      goB (D.PiCode _ _) = tt
      goB D.NatCode = tt
      goB D.ZeroEl = tt
      goB (D.SucEl _) = tt
      goB (PairEl _ _) = tt
      goB (SigmaCode _ _) = tt
  pairR {A} {B} {t} {u} iA iB dt du VA ATB Ft Fu {s} {s'} {rho} E (SigmaCode b f) Bot ec cU ep pc = tt
  pairR {A} {B} {t} {u} iA iB dt du VA ATB Ft Fu {s} {s'} {rho} E (SigmaCode b f) (PairEl u1 u2) ec cU ep pc =
    pairM (record
      { A = substExpr s A ; B = Bs ; rT = hrs-refl
      ; tT = tyeq-refl (isty-Sigma iAl iBl) ; iA = iAl ; iB = iBl
      ; cF = fst (fTm s s' cs wH (ty-Fst iA iB (ty-Pair iA iB dt du)))
      ; fstR = pExpM u1 b u1b bU hfst fbl VAd (pExpM' u1 b u1b bU hfst fbr VAd (Ft E b u1 eb bU eu1 u1b))
      ; sndR = pConvM u2 e u2e eU rT0T2 r0 })
    where
      crho = Env.crho E ; wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) iB
      Bs = substExpr (liftSub s) B
      Pl = substExpr s (Pair t u) ; Pr = substExpr s' (Pair t u)
      eA = fTy s s' cs wH iA
      cu = sigU b f cU
      bU = CodeU.bU cu
      eb = dfst (dsnd ec)
      u1b = finMemC-pair-fst u1 u2 b f pc
      u2e = finMemC-pair-snd u1 u2 b f pc
      eu1 = dfst (dsnd ep)
      eu2 = dsnd (dsnd ep)
      VAd = diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} b bU (VA E b eb bU)
      hfst : {X Y : Expr h} -> HRs (Fst (Pair X Y)) X
      hfst = hrs-step hr-fst-pair hrs-refl
      hsnd : {X Y : Expr h} -> HRs (Snd (Pair X Y)) Y
      hsnd = hrs-step hr-snd-pair hrs-refl
      fb = conv-fst-beta iA iB dt du
      fbl = sbCv s w1 wH fb
      fbr = conv-conv (sbCv s' w2 wH fb) (tyeq-sym eA)
      e = EvalFun f u1
      eU = efU b f cu u1b
      ebx = famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
              (CodeU.cft cu) (dsnd (dsnd ec)) u1 (FinMem-coh-u u1 b u1b)
      ee = EvalRel-subst1-backward B t rho u1 e crho eu1 ebx
      T0 = substExpr s (subst1 B t)
      sb = conv-snd-beta iA iB dt du
      sbl = sbCv s w1 wH sb
      qT = fTy s s' cs wH (pTm du)
      sbr = conv-conv (sbCv s' w2 wH sb) (tyeq-sym qT)
      VT0 = diagL {G = H} {T = T0} {T' = substExpr s' (subst1 B t)} e eU
              (substTy E {A = A} {B = B} {N = t} iA (VA E) (\ E' -> ATB E') dt (Ft E) e ee eU)
      r0 = pExpM u2 e u2e eU hsnd sbl VT0 (pExpM' u2 e u2e eU hsnd sbr VT0 (Fu E e u2 ee eU eu2 u2e))
      EL = envL E
      RN : (a' : FinEl) -> EvalRel A rho a' -> FinMem a' UCode -> FinMem u1 a' ->
           RTm H (substExpr s t) (Fst Pl) (substExpr s A) u1 a'
      RN a' ea' aU' m' = pExpM' u1 a' m' aU' hfst fbl
                           (diagL {G = H} {T = substExpr s A} {T' = substExpr s A} a' aU' (VA EL a' ea' aU'))
                           (Ft EL a' u1 ea' aU' eu1 m')
      E2 = envExt EL iA (VA EL) (conv-sym fbl) u1 b eb u1b RN
      rT0T2 : RTy H T0 (subst1 Bs (Fst Pl)) e
      rT0T2 = transport2 (\ X Y -> RTy H X Y e) (substCons s B t) (subst-consSub s (Fst Pl) B) (ATB E2 e ebx eU)
