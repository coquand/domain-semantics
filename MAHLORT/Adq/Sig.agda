{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Sig.agda  (Tarski port of MAHLOINJ/Adq/Sig)
--
-- Case lemmas for Sigma: projections, pairs, pair extensionality.
-- Tarski: the projections and pairs are annotated; the congruences
-- conv-Fst / conv-Snd / conv-Pair are two-sided with convertible
-- annotations, and the Sigma-term records are built at all
-- annotations by MAHLORT/Adq/AnnRel.
------------------------------------------------------------------------

module MAHLORT.Adq.Sig where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; PairEl ; SigmaCode ; FinFun ; mkSigma)
  renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; NotBot ; FinMem-a-in-U ; FinMem-coh-u ; finMemC-pair-fst ; finMemC-pair-snd)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-elim)
open import MAHLORT.Model
open import MAHLORT.Model using (EvalRel-subst1-backward)
open import MAHLORT.Model using (bodyOK)
open import MAHLORT.Model using (sTm)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Presup using (pCv ; pTm ; pTE)
open import MAHLORT.Syntax.CtxConv using (ccTy ; ccTE)
open import MAHLORT.Syntax.Wf using (wfTy ; wfTm)
open import MAHLORT.Valid.Ann
open import MAHLORT.Adq.AnnRel
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (CodeU ; sigU)
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLOINJ.Adq.Sem
open import MAHLORT.Adq.Env

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  -- substitution data for a Sigma type and a second annotation
  private
    module SD {A A' : Expr g} {B B' : Expr (suc g)} {s s' : Sub h g} {rho : EnvApprox g} (E : Env H G s s' rho)
      (iA : IsType G A) (iB : IsType (extend G A) B) (eAA' : TyEq G A A') (eBB' : TyEq (extend G A) B B') where
      wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      eA = fTy s s' cs wH iA
      cU' = liftC cs {A = A} iAl eA
      iBl = sbTy (liftSub s) (CSub.w1 cU') (wf-extend iAl) iB
      Bs = substExpr (liftSub s) B
      eB : TyEq (extend H (substExpr s A)) Bs (substExpr (liftSub s') B)
      eB = fTy (liftSub s) (liftSub s') cU' (wf-extend iAl) iB
      e2 : TyEq H (substExpr s A) (substExpr s' A')
      e2 = tyeq-trans eA (sbTE s' w2 wH eAA')
      e3 : TyEq (extend H (substExpr s A)) Bs (substExpr (liftSub s') B')
      e3 = tyeq-trans eB (sbTE (liftSub s') (CSub.w2 cU') (wf-extend iAl) eBB')
      eSig : TyEq H (substExpr s (SigmaB A B)) (substExpr s' (SigmaB A B))
      eSig = fTy s s' cs wH (isty-Sigma iA iB)

  -- first projection, two-sided
  fstR : {A A' : Expr g} {B B' : Expr (suc g)} {t t' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    TyEq G A A' -> TyEq (extend G A) B B' -> HasType G t (SigmaB A B) ->
    TyIH H G A A -> TmIH H G t t' (SigmaB A B) -> TmIH H G (Fst A (Lam A B) t) (Fst A' (Lam A' B') t') A
  fstR {A} {A'} {B} {B'} {t} {t'} iA iB eAA' eBB' dt VA Ft {s} {s'} {rho} E a u ea aU eu ua = go (bot-or u)
    where
      open SD {A = A} {A'} {B} {B'} E iA iB eAA' eBB'
      go : Or (Eq u Bot) (NotBot u) ->
        RTm H (substExpr s (Fst A (Lam A B) t)) (substExpr s' (Fst A' (Lam A' B') t')) (substExpr s A) u a
      go (left refl) = tt
      go (right nb) = pick (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                        (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
        where
          ts = sTm dt rho (Env.fits E) (PairEl u Bot) (guard-elim u nb eu)
          pick : (p1 a1 : FinEl) -> LeCode (PairEl u Bot) p1 -> EvalRel t rho p1 -> FinMem p1 a1 ->
                 EvalRel (SigmaB A B) rho a1 ->
                 RTm H (substExpr s (Fst A (Lam A B) t)) (substExpr s' (Fst A' (Lam A' B') t')) (substExpr s A) u a
          pick (PairEl x1 x2) (SigmaCode b f) le ep1 m ea1 =
            let a1U = FinMem-a-in-U (PairEl x1 x2) (SigmaCode b f) m
                cu = sigU b f a1U
                r = pairV (Ft E (SigmaCode b f) (PairEl x1 x2) ea1 a1U ep1 m)
                fr = sigFst r _ _ _ _ (tyeq-refl iAl) (tyeq-refl iBl) e2 e3
            in adj (EvalRel A rho) (EvalRel-ideal A rho (Env.crho E))
                 (\ c ec cU -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} c cU (VA E c ec cU))
                 x1 b (dfst (dsnd ea1)) (CodeU.bU cu) (finMemC-pair-fst x1 x2 b f m) fr u a ea aU (dfst le) ua

  -- second projection, two-sided
  sndR : {A A' : Expr g} {B B' : Expr (suc g)} {t t' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    TyEq G A A' -> TyEq (extend G A) B B' -> HasType G t (SigmaB A B) ->
    TyIH H G (subst1 B (Fst A (Lam A B) t)) (subst1 B (Fst A (Lam A B) t)) -> TmIH H G t t' (SigmaB A B) ->
    TmIH H G (Snd A (Lam A B) t) (Snd A' (Lam A' B') t') (subst1 B (Fst A (Lam A B) t))
  sndR {A} {A'} {B} {B'} {t} {t'} iA iB eAA' eBB' dt VT Ft {s} {s'} {rho} E c u ec cU eu uc = go (bot-or u)
    where
      open SD {A = A} {A'} {B} {B'} E iA iB eAA' eBB'
      crho = Env.crho E
      T = subst1 B (Fst A (Lam A B) t)
      go : Or (Eq u Bot) (NotBot u) ->
        RTm H (substExpr s (Snd A (Lam A B) t)) (substExpr s' (Snd A' (Lam A' B') t')) (substExpr s T) u c
      go (left refl) = tt
      go (right nb) = pick (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                        (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
        where
          ts = sTm dt rho (Env.fits E) (PairEl Bot u) (guard-elim u nb eu)
          pick : (p1 a1 : FinEl) -> LeCode (PairEl Bot u) p1 -> EvalRel t rho p1 -> FinMem p1 a1 ->
                 EvalRel (SigmaB A B) rho a1 ->
                 RTm H (substExpr s (Snd A (Lam A B) t)) (substExpr s' (Snd A' (Lam A' B') t')) (substExpr s T) u c
          pick (PairEl x1 x2) (SigmaCode b f) le ep1 m ea1 =
            let a1U = FinMem-a-in-U (PairEl x1 x2) (SigmaCode b f) m
                cu = sigU b f a1U
                x1b = finMemC-pair-fst x1 x2 b f m
                r = pairV (Ft E (SigmaCode b f) (PairEl x1 x2) ea1 a1U ep1 m)
                sr = transport (\ X -> RTm H (substExpr s (Snd A (Lam A B) t)) (substExpr s' (Snd A' (Lam A' B') t')) X x2 (EvalFun f x1))
                       (Eq-sym (subst-subst1-comm s B (Fst A (Lam A B) t)))
                       (sigSnd r _ _ _ _ (tyeq-refl iAl) (tyeq-refl iBl) e2 e3)
                cx1 = FinMem-coh-u x1 b x1b
                ex1 = fstOf (EvalRel t rho) (EvalRel-ideal t rho crho) x1 x2 ep1
                ee = EvalRel-subst1-backward B (Fst A (Lam A B) t) rho x1 (EvalFun f x1) crho ex1
                       (famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                          (CodeU.cft cu) (dsnd (dsnd ea1)) x1 cx1)
            in adj (EvalRel T rho) (EvalRel-ideal T rho crho)
                 (\ c' ec' cU' -> diagL {G = H} {T = substExpr s T} {T' = substExpr s' T} c' cU' (VT E c' ec' cU'))
                 x2 (EvalFun f x1) ee (efU b f cu x1b) (finMemC-pair-snd x1 x2 b f m) sr u c ec cU (dsnd le) uc

  -- pair extensionality (two-sided; the projections carry the type's annotation)
  pairextR : {A : Expr g} {B : Expr (suc g)} {t t' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    HasType G t (SigmaB A B) -> HasType G t' (SigmaB A B) ->
    ConvTm G (Fst A (Lam A B) t) (Fst A (Lam A B) t') A ->
    TyIH H G A A -> TyIH H G (subst1 B (Fst A (Lam A B) t)) (subst1 B (Fst A (Lam A B) t)) ->
    TmIH H G (Fst A (Lam A B) t) (Fst A (Lam A B) t') A ->
    TmIH H G (Snd A (Lam A B) t) (Snd A (Lam A B) t') (subst1 B (Fst A (Lam A B) t)) ->
    TmIH H G t t' (SigmaB A B)
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 VA VT F1 F2 {s} {s'} {rho} E Bot p ec cU ep pc = goB p
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
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 VA VT F1 F2 {s} {s'} {rho} E (SigmaCode b f) Bot ec cU ep pc = tt
  pairextR {A} {B} {t} {t'} iA iB dt dt' d1 VA VT F1 F2 {s} {s'} {rho} E (SigmaCode b f) (PairEl u1 u2) ec cU ep pc =
    pairM (record
      { A = substExpr s A ; B = Bs ; rT = hrs-refl
      ; tT = tyeq-refl (isty-Sigma iAl iBl) ; iA = iAl ; iB = iBl
      ; cF = SA.cFq ; fstR = SA.fstq ; sndR = SA.sndq })
    where
      open SD {A = A} {A} {B} {B} E iA iB (tyeq-refl iA) (tyeq-refl iB)
      crho = Env.crho E
      cu = sigU b f cU
      eb = dfst (dsnd ec)
      u1b = finMemC-pair-fst u1 u2 b f pc
      u2e = finMemC-pair-snd u1 u2 b f pc
      eu1 = fstOf (EvalRel t rho) (EvalRel-ideal t rho crho) u1 u2 ep
      eu2 = sndOf (EvalRel t rho) (EvalRel-ideal t rho crho) u1 u2 ep
      ee = EvalRel-subst1-backward B (Fst A (Lam A B) t) rho u1 (EvalFun f u1) crho eu1
             (famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                (CodeU.cft cu) (dsnd (dsnd ec)) u1 (FinMem-coh-u u1 b u1b))
      eU = efU b f cu u1b
      hl = sbTm s w1 wH dt
      hr = ty-conv (sbTm s' w2 wH dt') (tyeq-sym eSig)
      c0 = conv-trans (sbCv s w1 wH d1) (fst (fTm s s' cs wH (ty-Fst iA iB dt')))
      VAd = diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} b (CodeU.bU cu) (VA E b eb (CodeU.bU cu))
      Tl = substExpr s (subst1 B (Fst A (Lam A B) t))
      VTd = transport (\ X -> RTy H X X (EvalFun f u1)) (subst-subst1-comm s B (Fst A (Lam A B) t))
              (diagL {G = H} {T = Tl} {T' = substExpr s' (subst1 B (Fst A (Lam A B) t))} (EvalFun f u1) eU (VT E (EvalFun f u1) ee eU))
      s0 = transport (\ X -> RTm H (Snd (substExpr s A) (Lam (substExpr s A) Bs) (substExpr s t))
                                   (Snd (substExpr s' A) (Lam (substExpr s' A) (substExpr (liftSub s') B)) (substExpr s' t')) X u2 (EvalFun f u1))
             (subst-subst1-comm s B (Fst A (Lam A B) t)) (F2 E (EvalFun f u1) u2 ee eU eu2 u2e)
      module SA = SigAnn iAl iBl eA eB hl hr u1b (CodeU.bU cu) VAd u2e eU VTd c0 (F1 E b u1 eb (CodeU.bU cu) eu1 u1b) s0

  -- pairs, two-sided (conv-Pair):  pair(A,B,t,u) = pair(A',B',t',u')
  pairR : {A A' : Expr g} {B B' : Expr (suc g)} {t t' u u' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    TyEq G A A' -> TyEq (extend G A) B B' -> ConvTm G t t' A -> ConvTm G u u' (subst1 B t) ->
    TyIH H G A A -> TyIH H (extend G A) B B -> TyIH H G (subst1 B t) (subst1 B t) ->
    TmIH H G t t' A -> TmIH H G u u' (subst1 B t) ->
    TmIH H G (Pair A (Lam A B) t u) (Pair A' (Lam A' B') t' u') (SigmaB A B)
  pairR {A} {A'} {B} {B'} {t} {t'} {u} {u'} iA iB eAA' eBB' ct cuu VA ATB VT Ft Fu {s} {s'} {rho} E Bot p ec cU ep pc = goB p
    where
      goB : (p : FinEl) -> RTm H (substExpr s (Pair A (Lam A B) t u)) (substExpr s' (Pair A' (Lam A' B') t' u'))
                               (substExpr s (SigmaB A B)) p Bot
      goB Bot = tt
      goB UCode = tt
      goB (D.FunEl _) = tt
      goB (D.PiCode _ _) = tt
      goB D.NatCode = tt
      goB D.ZeroEl = tt
      goB (D.SucEl _) = tt
      goB (PairEl _ _) = tt
      goB (SigmaCode _ _) = tt
  pairR {A} {A'} {B} {B'} {t} {t'} {u} {u'} iA iB eAA' eBB' ct cuu VA ATB VT Ft Fu {s} {s'} {rho} E (SigmaCode b f) Bot ec cU ep pc = tt
  pairR {A} {A'} {B} {B'} {t} {t'} {u} {u'} iA iB eAA' eBB' ct cuu VA ATB VT Ft Fu {s} {s'} {rho} E (SigmaCode b f) (PairEl u1 u2) ec cU ep pc =
    pairM (record
      { A = substExpr s A ; B = Bs ; rT = hrs-refl
      ; tT = tyeq-refl (isty-Sigma iAl iBl) ; iA = iAl ; iB = iBl
      ; cF = SA.cFq ; fstR = SA.fstq ; sndR = SA.sndq })
    where
      open SD {A = A} {A'} {B} {B'} E iA iB eAA' eBB'
      crho = Env.crho E
      wG = wfTy iA
      cu = sigU b f cU
      bU = CodeU.bU cu
      eb = dfst (dsnd ec)
      u1b = finMemC-pair-fst u1 u2 b f pc
      u2e = finMemC-pair-snd u1 u2 b f pc
      eu1 = dfst (dsnd ep)
      eu2 = dsnd (dsnd ep)
      e = EvalFun f u1
      eU = efU b f cu u1b
      -- typings in G
      dt = fst (pCv ct) ; dt' = snd (pCv ct) ; du = fst (pCv cuu) ; du' = snd (pCv cuu)
      iA' = snd (pTE eAA')
      iB'A = snd (pTE eBB')
      iB' = ccTy iA' (tyeq-sym eAA') iB'A
      dtA' = ty-conv dt' eAA'
      qBt : TyEq G (subst1 B t) (subst1 B' t')
      qBt = tyeq-trans (s1fTy wG iA dt dt' ct iB) (s1TE wG dt' eBB')
      duB' = ty-conv du' qBt
      hPRA : HasType G (Pair A' (Lam A' B') t' u') (SigmaB A B)
      hPRA = ty-conv (ty-Pair iA' iB' dtA' duB') (tyeq-sym (tyeq-Sigma iA iB iB'A eAA' eBB'))
      -- the two pairs in H
      Pl = substExpr s (Pair A (Lam A B) t u) ; Pr = substExpr s' (Pair A' (Lam A' B') t' u')
      Fl = Lam (substExpr s A) Bs
      hPl : HasType H Pl (SigmaB (substExpr s A) Bs)
      hPl = sbTm s w1 wH (ty-Pair iA iB dt du)
      hPr : HasType H Pr (SigmaB (substExpr s A) Bs)
      hPr = ty-conv (sbTm s' w2 wH hPRA) (tyeq-sym eSig)
      hfst : {X F Y F' a c : Expr h} -> HRs (Fst X F (Pair Y F' a c)) a
      hfst = hrs-step hr-fst-pair hrs-refl
      hsnd : {X F Y F' a c : Expr h} -> HRs (Snd X F (Pair Y F' a c)) c
      hsnd = hrs-step hr-snd-pair hrs-refl
      -- first components
      fbl : ConvTm H (Fst (substExpr s A) Fl Pl) (substExpr s t) (substExpr s A)
      fbl = sbCv s w1 wH (conv-fst-beta iA iB dt du)
      ctS : ConvTm H (substExpr s t) (substExpr s' t') (substExpr s A)
      ctS = conv-trans (sbCv s w1 wH ct) (fst (fTm s s' cs wH dt'))
      fbr : ConvTm H (Fst (substExpr s A) Fl Pr) (substExpr s' t') (substExpr s A)
      fbr = conv-trans (conv-Fst iAl iBl e2 e3 (conv-refl hPr))
              (conv-conv (sbCv s' w2 wH (conv-fst-beta iA' iB' dtA' duB')) (tyeq-sym e2))
      c0 = conv-trans fbl (conv-trans ctS (conv-sym fbr))
      VAd = diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} b bU (VA E b eb bU)
      f0 = pExpM u1 b u1b bU (ar-hrs hfst) fbl VAd (pExpM' u1 b u1b bU (ar-hrs hfst) fbr VAd (Ft E b u1 eb bU eu1 u1b))
      -- second components
      T0 = substExpr s (subst1 B t)
      ebx = famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
              (CodeU.cft cu) (dsnd (dsnd ec)) u1 (FinMem-coh-u u1 b u1b)
      ee = EvalRel-subst1-backward B t rho u1 e crho eu1 ebx
      VT0 = diagL {G = H} {T = T0} {T' = substExpr s' (subst1 B t)} e eU (VT E e ee eU)
      sbl : ConvTm H (Snd (substExpr s A) Fl Pl) (substExpr s u) T0
      sbl = sbCv s w1 wH (conv-snd-beta iA iB dt du)
      cFr : ConvTm H (Fst (substExpr s A) Fl Pr) (substExpr s t) (substExpr s A)
      cFr = conv-trans fbr (conv-sym ctS)
      q1 : TyEq H (subst1 Bs (Fst (substExpr s A) Fl Pr)) T0
      q1 = transport (TyEq H (subst1 Bs (Fst (substExpr s A) Fl Pr))) (Eq-sym (subst-subst1-comm s B t))
             (s1fTy wH iAl (fst (pCv cFr)) (snd (pCv cFr)) cFr iBl)
      q2 : TyEq H (substExpr s' (subst1 B' t')) T0
      q2 = tyeq-trans (sbTE s' w2 wH (tyeq-sym qBt)) (tyeq-sym (fTy s s' cs wH (pTm du)))
      sbr : ConvTm H (Snd (substExpr s A) Fl Pr) (substExpr s' u') T0
      sbr = conv-trans (conv-conv (conv-Snd iAl iBl e2 e3 (conv-refl hPr)) q1)
              (conv-conv (sbCv s' w2 wH (conv-snd-beta iA' iB' dtA' duB')) q2)
      r0 = pExpM u2 e u2e eU (ar-hrs hsnd) sbl VT0 (pExpM' u2 e u2e eU (ar-hrs hsnd) sbr VT0 (Fu E e u2 ee eU eu2 u2e))
      -- T0 = B[fst Pl], through the extended left-diagonal environment
      EL = envL E
      RN : (a' : FinEl) -> EvalRel A rho a' -> FinMem a' UCode -> FinMem u1 a' ->
           RTm H (substExpr s t) (Fst (substExpr s A) Fl Pl) (substExpr s A) u1 a'
      RN a' ea' aU' m' =
        let Vd = diagL {G = H} {T = substExpr s A} {T' = substExpr s A} a' aU' (VA EL a' ea' aU')
            x = Ft EL a' u1 ea' aU' eu1 m'
        in pExpM' u1 a' m' aU' (ar-hrs hfst) fbl Vd (pTransM u1 a' m' aU' Vd x (pSymM u1 a' m' aU' Vd x))
      E2 = envExt EL iA (VA EL) (conv-sym fbl) u1 b eb u1b RN
      rT0T2 : RTy H T0 (subst1 Bs (Fst (substExpr s A) Fl Pl)) e
      rT0T2 = transport2 (\ X Y -> RTy H X Y e) (substCons s B t) (subst-consSub s (Fst (substExpr s A) Fl Pl) B) (ATB E2 e ebx eU)
      s0 = pConvM u2 e u2e eU rT0T2 r0
      VTd = diagR {G = H} {T = T0} {T' = subst1 Bs (Fst (substExpr s A) Fl Pl)} e eU rT0T2
      module SA = SigAnn iAl iBl (tyeq-refl iAl) (tyeq-refl iBl) hPl hPr u1b bU VAd u2e eU VTd c0 f0 s0
