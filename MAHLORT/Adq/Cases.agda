{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Cases.agda  (Tarski port of MAHLOINJ/Adq/Cases)
--
-- Case lemmas of the fundamental lemma needing more glue: beta, the
-- recursor (with its syntax), and iota on successors.
------------------------------------------------------------------------

module MAHLORT.Adq.Cases where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (LeCode ; FinMem ; NotBot ; Coherent ; Sup ; FinMem-coh-u ; LeCode-trans ; LeCode-Sup-left ; LeCode-Sup-right
        ; Coherent-Sup)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (Ideal ; bot-or ; guard-elim ; guard-intro ; LamBody-edge ; sing-key-coh ; sing-val-coh
  ; NotBot-from-Le ; RecB)
open import MAHLOINJ.Model.Selection using (here)
open import MAHLORT.Model
open import MAHLORT.Model using (EvalRel-subst1-forward)
open import MAHLORT.Model using (bodyOK)
open import MAHLORT.Model using (sTm)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Weaken using (wkTy)
open import MAHLORT.Syntax.Wf using (NatTy)
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.LamApp using (appR)
open import MAHLORT.Adq.Small using (sucR)
open import MAHLORT.Adq.Delta using (substTyPi)
open import MAHLORT.Adq.Rec
open import MAHLORT.Adq.RecSyn
open import MAHLORT.Adq.Syn

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  natRel : {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> TyRelAt H s s' rho Nat Nat
  natRel E a ea aU = natTy (NatTy (Env.wH E)) a ea

  ----------------------------------------------------------------------
  -- beta
  ----------------------------------------------------------------------

  betaCv : {A a : Expr g} {B t : Expr (suc g)} -> IsType G A -> IsType (extend G A) B ->
    HasType (extend G A) t B -> HasType G a A ->
    TyIH H G A A -> TyIH H (extend G A) B B -> TmIH H (extend G A) t t B -> TmIH H G a a A ->
    TmIH H G (appB A B (Lam A t) a) (subst1 t a) (subst1 B a)
  betaCv {A} {a} {B} {t} iA iB dt da VA ATB Ft Fa {s} {s'} {rho} E c x ec cU ex xc = go (bot-or x)
    where
      crho = Env.crho E ; wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      go : Or (Eq x Bot) (NotBot x) ->
           RTm H (substExpr s (appB A B (Lam A t) a)) (substExpr s' (subst1 t a)) (substExpr s (subst1 B a)) x c
      go (left refl) = tt
      go (right nb) =
        pExpM x c xc cU (ar-hrs hr) (sbCv s w1 wH (conv-beta iA iB dt da)) VT r'
        where
          bd = guard-elim x nb ex
          w = dfst bd ; ew = dfst (dsnd bd) ; el = dsnd (dsnd bd)
          edge = LamBody-edge (dfst el) (\ y -> EvalRel t (extendEnv rho y)) _ (dsnd (dsnd (dsnd (dsnd el)))) (mkSigma w x) here
          x' = dfst edge ; lx'w = dfst (dsnd edge) ; ext' = dsnd (dsnd (dsnd edge))
          cx' = FinMem-coh-u x' (dfst el) (dfst (dsnd (dsnd edge)))
          ex' = EvalRel-down a rho crho w x' ew cx' lx'w
          fw = EvalRel-subst1-forward B a rho c crho ec
          q = dfst fw ; eq = dfst (dsnd fw) ; cq = dsnd (dsnd fw)
          ia = EvalRel-ideal a rho crho
          cp = Ideal.comp ia x' q ex' eq
          coq = EvalRel-coh a rho crho q eq
          cp0 = Coherent-Sup x' q cp cx' coq
          ts = sTm da rho (Env.fits E) (Sup x' q) (Ideal.sup ia x' q ex' eq)
          p = dfst ts ; a1 = dfst (dsnd ts) ; lp = dfst (dsnd (dsnd ts)) ; ep = dfst (dsnd (dsnd (dsnd ts)))
          pa1 = dfst (dsnd (dsnd (dsnd (dsnd ts)))) ; ea1 = dsnd (dsnd (dsnd (dsnd (dsnd ts))))
          cop = FinMem-coh-u p a1 pa1
          lx'p = LeCode-trans x' (Sup x' q) p cx' cp0 cop (LeCode-Sup-left x' q cp cx' coq) lp
          lqp = LeCode-trans q (Sup x' q) p coq cp0 cop (LeCode-Sup-right x' q cp cx' coq) lp
          extp = EvalRel-mon-env t (extendEnv rho x') (extendEnv rho p)
                   (mkSigma (EnvLe-refl rho crho) (mkSigma cx' (mkSigma cop lx'p))) x ext'
          ecp = EvalRel-mon-env B (extendEnv rho q) (extendEnv rho p)
                   (mkSigma (EnvLe-refl rho crho) (mkSigma coq (mkSigma cop lqp))) c cq
          cN = fst (fTm s s' cs wH da)
          E' = envExt E iA (VA E) cN p a1 ea1 pa1 (\ a' ea' aU' pa' -> Fa E a' p ea' aU' ep pa')
          r' = transport3 (\ X Y Z -> RTm H X Y Z x c) (substCons s t a) (substCons s' t a) (substCons s B a)
                 (Ft E' c x ecp cU extp xc)
          hr = transport (\ X -> HRs (substExpr s (appB A B (Lam A t) a)) X) (Eq-sym (subst-subst1-comm s t a))
                 (hrs-step hr-beta hrs-refl)
          VT = diagL {G = H} {T = substExpr s (subst1 B a)} {T' = substExpr s' (subst1 B a)} c cU
                 (substTy E {A = A} {B = B} {N = a} iA (VA E) (\ E2 -> ATB E2) da (Fa E) c ec cU)

  ----------------------------------------------------------------------
  -- the recursor, two-sided
  ----------------------------------------------------------------------

  recX : {C C' : Expr (suc g)} {z z' st st' k k' : Expr g} ->
    IsType (extend G Nat) C -> IsType (extend G Nat) C' -> TyEq (extend G Nat) C C' ->
    ConvTm G z z' (subst1 C Zero) -> ConvTm G st st' (RecStep C) -> ConvTm G k k' Nat ->
    TyIH H (extend G Nat) C C -> TmIH H G z z' (subst1 C Zero) -> TmIH H G st st' (RecStep C) -> TmIH H G k k' Nat ->
    TmIH H G (Rec (Lam Nat C) z st k) (Rec (Lam Nat C') z' st' k') (subst1 C k)
  recX {C} {C'} {z} {z'} {st} {st'} {k} {k'} iC iC' qC cz cst ck ATC Fz Fs Fk {s} {s'} {rho} E =
    RC.recEntry {k = k} {k' = k'} (fst (pCv ck)) cK (Fk E)
    where
      wH = Env.wH E ; wG = Env.wG E ; cs = Env.cs E ; w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iNH = NatTy wH
      wN = wf-extend iNH
      lw1 = liftWS {A = Nat} w1 iNH
      lw2 = liftWS {A = Nat} w2 iNH
      hC = sbTy (liftSub s) lw1 wN iC
      hCr = sbTy (liftSub s') lw2 wN iC'
      lc = liftC cs {A = Nat} iNH (tyeq-refl iNH)
      qCH = tyeq-trans (fTy (liftSub s) (liftSub s') lc wN iC) (sbTE (liftSub s') (CSub.w2 lc) wN qC)
      dz = fst (pCv cz) ; dst = fst (pCv cst)
      dz' = ty-conv (snd (pCv cz)) (s1TE wG (ty-Zero wG) qC)
      dst' = ty-conv (snd (pCv cst)) (stepEq wG iC iC' qC)
      hz = trHT refl (subst-subst1-comm s C Zero) (sbTm s w1 wH dz)
      hzr = trHT refl (subst-subst1-comm s' C' Zero) (sbTm s' w2 wH dz')
      czH = trCv refl refl (subst-subst1-comm s C Zero) (conv-trans (sbCv s w1 wH cz) (fst (fTm s s' cs wH (snd (pCv cz)))))
      hs = trHT refl (subst-RecStep s C) (sbTm s w1 wH dst)
      hsr = trHT refl (subst-RecStep s' C') (sbTm s' w2 wH dst')
      csH = trCv refl refl (subst-RecStep s C) (conv-trans (sbCv s w1 wH cst) (fst (fTm s s' cs wH (snd (pCv cst)))))
      cK = conv-trans (sbCv s w1 wH ck) (fst (fTm s s' cs wH (snd (pCv ck))))
      module RS = RecSyn wH hC hCr qCH hz hzr czH hs hsr csH
      module RC = RecCore E {C} {C'} {z} {z'} {st} {st'} hC hCr qCH dst ATC (Fz E) (Fs E) RS.izL RS.izR RS.isL RS.isR RS.cRec

  ----------------------------------------------------------------------
  -- iota on a successor
  ----------------------------------------------------------------------

  recSucCv : {C : Expr (suc g)} {z st k : Expr g} -> IsType (extend G Nat) C ->
    HasType G z (subst1 C Zero) -> HasType G st (RecStep C) -> HasType G k Nat ->
    TyIH H (extend G Nat) C C -> TmIH H G z z (subst1 C Zero) -> TmIH H G st st (RecStep C) ->
    TyIH H G (RecStep C) (RecStep C) -> TmIH H G k k Nat ->
    TmIH H G (Rec (Lam Nat C) z st (Suc k)) (RecSuc C z st k) (subst1 C (Suc k))
  recSucCv {C} {z} {st} {k} iC dz ds dk ATC Fz Fs TS Fk {s} {s'} {rho} E c u ec cU eu uc = go (bot-or u)
    where
      crho = Env.crho E ; wH = Env.wH E ; wG = Env.wG E ; cs = Env.cs E ; w1 = CSub.w1 cs
      RecK = Rec (Lam Nat C) z st k
      Lhs = Rec (Lam Nat C) z st (Suc k)
      Rhs = RecSuc C z st k
      SB = Arr C (substExpr sucSub C)
      iN = NatTy wG ; iSB = stepTy wG iC
      iA2 = s1Ty wG dk iC
      iB2 = wkTy iA2 (s1Ty wG (ty-Suc dk) iC)
      VTsk : TyRelAt H s s' rho (subst1 C (Suc k)) (subst1 C (Suc k))
      VTsk = substTy E {A = Nat} {B = C} {N = Suc k} (NatTy wG) (natRel E) (\ E2 -> ATC E2) (ty-Suc dk)
               (sucR dk dk (conv-refl dk) Fk E)
      VT1 = substTyPi E {A = Nat} {B = Arr C (substExpr sucSub C)} {N = k} (TS E) dk (Fk E)
      r1 = appR E {A = Nat} {A' = Nat} {B = SB} {B' = SB} {t = st} {t' = st} {a = k} {a' = k}
             iN iSB (tyeq-refl iN) (tyeq-refl iSB) ds (fst (fTm s s' cs wH dk)) (Fs E) (Fk E) VT1
      r1' = transport (\ X -> TmRelAt H s s' rho (appB Nat SB st k) (appB Nat SB st k) X) (stepE C k) r1
      dtSK = trHT refl (stepE C k) (ty-App (NatTy wG) (stepTy wG iC) ds dk)
      cRK = fst (fTm s s' cs wH (ty-Rec iC dz ds dk))
      FRK = recX {C = C} {C' = C} {z = z} {z' = z} {st = st} {st' = st} {k = k} {k' = k}
              iC iC (tyeq-refl iC) (conv-refl dz) (conv-refl ds) (conv-refl dk) ATC Fz Fs Fk E
      VT2 = transport (\ X -> TyRelAt H s s' rho X X) (Eq-sym (subst1-wk (subst1 C (Suc k)) RecK)) VTsk
      r2 = appR E {A = subst1 C k} {A' = subst1 C k} {B = wkExpr (subst1 C (Suc k))} {B' = wkExpr (subst1 C (Suc k))}
             {t = appB Nat SB st k} {t' = appB Nat SB st k} {a = RecK} {a' = RecK}
             iA2 iB2 (tyeq-refl iA2) (tyeq-refl iB2) dtSK cRK r1' FRK VT2
      chain = transport (\ X -> TmRelAt H s s' rho Rhs Rhs X) (subst1-wk (subst1 C (Suc k)) RecK) r2
      go : Or (Eq u Bot) (NotBot u) -> RTm H (substExpr s Lhs) (substExpr s' Rhs) (substExpr s (subst1 C (Suc k))) u c
      go (left refl) = tt
      go (right nb) = pickW (dfst bd) (dfst (dsnd bd)) (dsnd (dsnd bd))
        where
          bd = guard-elim u nb eu
          pickW : (w : FinEl) -> EvalRel (Suc k) rho w -> RecB (EvalRel z rho) (EvalRel st rho) u w ->
            RTm H (substExpr s Lhs) (substExpr s' Rhs) (substExpr s (subst1 C (Suc k))) u c
          pickW (SucEl w2) ew rb =
            pExpM u c uc cU (ar-post (hrs-step hr-rec-suc hrs-refl) (ann-app (ann-app ann-refl))) (sbCv s w1 wH (conv-rec-suc iC dz ds dk))
              (diagL {G = H} {T = substExpr s (subst1 C (Suc k))} {T' = substExpr s' (subst1 C (Suc k))} c cU (VTsk c ec cU))
              (chain c u ec cU eApp uc)
            where
              v = dfst (dsnd ew) ; ev = dfst (dsnd (dsnd ew)) ; lwv = dsnd (dsnd (dsnd ew))
              r = dfst rb ; gr = dfst (dsnd rb) ; es = dsnd (dsnd rb)
              cx = EvalRel-coh st rho crho _ es
              cw2 = sing-key-coh w2 _ cx
              ew2 = EvalRel-down k rho crho v w2 ev cw2 lwv
              eRec : EvalRel RecK rho r
              eRec = goR (bot-or r)
                where
                  goR : Or (Eq r Bot) (NotBot r) -> EvalRel RecK rho r
                  goR (left refl) = tt
                  goR (right nbr) = guard-intro r nbr (mkSigma w2 (mkSigma ew2 (guard-elim r nbr gr)))
              nbs : NotBot (D.FunEl (D.cons (mkSigma r u) D.nil))
              nbs = tt
              eApp : EvalRel Rhs rho u
              eApp = guard-intro u nb (mkSigma r (mkSigma eRec (guard-intro (D.FunEl (D.cons (mkSigma r u) D.nil)) nbs (mkSigma w2 (mkSigma ew2 es)))))
