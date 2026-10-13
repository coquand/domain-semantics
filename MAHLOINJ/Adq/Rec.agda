{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Rec.agda
--
-- The recursor case of the fundamental lemma (two-sided), by an inner
-- induction on the semantic numeral, with iota-expansion on both sides.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Rec where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; NotBot ; Coherent ; Sup ; FinMem-a-in-U ; FinMem-coh-u ; LeCode-refl ; LeCode-trans
        ; finMem-funel-coh ; cft-from-cf ; sucNat-to ; LeCode-Sup-left ; LeCode-Sup-right)
open import MAHLOINJ.Model.Selection using (Selection ; selectionBelow ; Coherent-Selection ; Or ; left ; right)
open import MAHLOINJ.Model.Comb
  using (Ideal ; AtomS ; bot-or ; guard-elim ; sing ; sing-key-coh ; sing-val-coh ; RecB ; module RecProps ; NotBot-from-Le)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst using (EvalRel-unwk ; EvalRel-subst1-backward ; MaxSubRel ; EvalRel-subst-fwd-max)
open import MAHLOINJ.Model.EvalFwd using (EvalRel-subst1-forward)
open import MAHLOINJ.Model.SoundBase using (bodyOK)
open import MAHLOINJ.Model.Soundness using (sTm)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf using (NatTy)
open import MAHLOINJ.Syntax.Presup using (pCv)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Props using (CodeU ; piU)
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Sem
open import MAHLOINJ.Adq.Env
open import MAHLOINJ.Adq.Delta using (tmBot)
open import MAHLOINJ.Adq.Syn using (stepE)

-- the semantics of the successor substitution
sucSem : {n : Num} (C : Expr (suc n)) (rho : EnvApprox n) -> CoherentEnv rho -> (x c : FinEl) -> Coherent x ->
  EvalRel (substExpr sucSub C) (extendEnv rho x) c -> EvalRel C (extendEnv rho (SucEl x)) c
sucSem C rho crho x c cx e = EvalRel-subst-fwd-max sucSub C (extendEnv rho x) (extendEnv rho (SucEl x)) (mkSigma crho cx) m c e
  where
    m : MaxSubRel sucSub (extendEnv rho x) (extendEnv rho (SucEl x))
    m fzero u eu = LeCode-trans u (SucEl (dfst (dsnd eu))) (SucEl x) (dfst eu) (dfst (dfst (dsnd (dsnd eu)))) cx
                     (dsnd (dsnd (dsnd eu))) (dsnd (dfst (dsnd (dsnd eu))))
    m (fsuc i) u eu = dsnd eu

natE : {n : Num} {rho : EnvApprox n} -> EvalRel Nat rho NatCode
natE = mkSigma tt (LeCode-refl NatCode tt)

NcU : FinMem NatCode UCode
NcU = tt

module RecCore {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} (E : Env H G s s' rho)
  {C C' : Expr (suc g)} {z z' st st' : Expr g}
  (dst : HasType G st (RecStep C))
  (ATC : TyIH H (extend G Nat) C C)
  (Fz : TmRelAt H s s' rho z z' (subst1 C Zero))
  (Fs : TmRelAt H s s' rho st st' (RecStep C))
  -- the syntactic iota steps and congruence, at the substituted level
  (izL : (K : Expr h) -> ConvTm H K Zero Nat ->
         ConvTm H (Rec (Lam Nat (substExpr (liftSub s) C)) (substExpr s z) (substExpr s st) K) (substExpr s z)
                  (subst1 (substExpr (liftSub s) C) K))
  (izR : (K K' : Expr h) -> ConvTm H K K' Nat -> ConvTm H K' Zero Nat ->
         ConvTm H (Rec (Lam Nat (substExpr (liftSub s') C')) (substExpr s' z') (substExpr s' st') K') (substExpr s' z')
                  (subst1 (substExpr (liftSub s) C) K))
  (isL : (K P : Expr h) -> HasType H P Nat -> ConvTm H K (Suc P) Nat ->
         ConvTm H (Rec (Lam Nat (substExpr (liftSub s) C)) (substExpr s z) (substExpr s st) K)
                  (App (App (substExpr s st) P) (Rec (Lam Nat (substExpr (liftSub s) C)) (substExpr s z) (substExpr s st) P))
                  (subst1 (substExpr (liftSub s) C) K))
  (isR : (K K' P' : Expr h) -> HasType H P' Nat -> ConvTm H K K' Nat -> ConvTm H K' (Suc P') Nat ->
         ConvTm H (Rec (Lam Nat (substExpr (liftSub s') C')) (substExpr s' z') (substExpr s' st') K')
                  (App (App (substExpr s' st') P') (Rec (Lam Nat (substExpr (liftSub s') C')) (substExpr s' z') (substExpr s' st') P'))
                  (subst1 (substExpr (liftSub s) C) K))
  (cRec : (P P' : Expr h) -> ConvTm H P P' Nat ->
          ConvTm H (Rec (Lam Nat (substExpr (liftSub s) C)) (substExpr s z) (substExpr s st) P)
                   (Rec (Lam Nat (substExpr (liftSub s') C')) (substExpr s' z') (substExpr s' st') P')
                   (subst1 (substExpr (liftSub s) C) P)) where

  private
    crho = Env.crho E
    wH = Env.wH E
    iN = NatTy wH
    Cl = substExpr (liftSub s) C
    zl = substExpr s z ; sl = substExpr s st
    zr = substExpr s' z' ; sr = substExpr s' st'
    Cr = substExpr (liftSub s') C'
    Pz = EvalRel z rho ; Ps = EvalRel st rho
    module RP = RecProps Pz Ps (EvalRel-ideal z rho crho) (EvalRel-ideal st rho crho)
    natEr : EvalRel Nat rho NatCode
    natEr = natE {rho = rho}
    natV : RTy H Nat Nat NatCode
    natV = natTy iN NatCode natEr

  RecL : Expr h -> Expr h
  RecL K = Rec (Lam Nat Cl) zl sl K

  RecR : Expr h -> Expr h
  RecR K = Rec (Lam Nat Cr) zr sr K

  private
    -- the motive at related numerals, on the left
    VTat : (K K' : Expr h) (w : FinEl) -> FinMem w NatCode -> ConvTm H K K' Nat -> RTm H K K' Nat w NatCode ->
      (c : FinEl) -> EvalRel C (extendEnv rho w) c -> FinMem c UCode -> RTy H (subst1 Cl K) (subst1 Cl K') c
    VTat K K' w wN cv rK c ec cU =
      transport2 (\ X Y -> RTy H X Y c) (subst-consSub s K C) (subst-consSub s K' C)
        (ATC (envExt (envL E) (NatTy (Env.wG E)) (\ a ea aU -> natTy iN a ea) cv w NatCode natEr wN RN) c ec cU)
      where
        RN : (a : FinEl) -> EvalRel Nat rho a -> FinMem a UCode -> FinMem w a -> RTm H K K' (substExpr s Nat) w a
        RN Bot ea aU wa = tmBot w
        RN NatCode ea aU wa = rK

    diagN : {K K' : Expr h} (w : FinEl) -> FinMem w NatCode -> RTm H K K' Nat w NatCode -> RTm H K K Nat w NatCode
    diagN {K} {K'} w wN r = pTransM {G = H} {M1 = K} {M2 = K'} {M3 = K} {T = Nat} w NatCode wN NcU natV r
                              (pSymM {G = H} {M = K} {M' = K'} {T = Nat} w NatCode wN NcU natV r)

  recGo : (w : FinEl) -> FinMem w NatCode -> (K K' : Expr h) -> ConvTm H K K' Nat -> RTm H K K' Nat w NatCode ->
    (c : FinEl) -> EvalRel C (extendEnv rho w) c -> FinMem c UCode ->
    (w2 u : FinEl) -> LeCode w2 w -> RecB Pz Ps u w2 -> FinMem u c ->
    RTm H (RecL K) (RecR K') (subst1 Cl K) u c
  recGo ZeroEl wN K K' cK rK c ec cU ZeroEl u le rb uc =
    pExpM u c uc cU hrL (izL K (snd zK)) VTK (pExpM' u c uc cU hrR (izR K K' cK (snd zK')) VTK zr2)
    where
      zK = fst (snd rK) ; zK' = snd (snd rK)
      hK = fst (pCv cK)
      ecz = EvalRel-subst1-backward C Zero rho ZeroEl c crho (mkSigma tt (LeCode-refl ZeroEl tt)) ec
      zr1 = transport (\ X -> RTm H zl zr X u c) (subst-subst1-comm s C Zero) (Fz c u ecz cU rb uc)
      RZK : RTm H Zero K Nat ZeroEl NatCode
      RZK = tyeq-refl iN , ((hrs-refl , conv-refl (ty-Zero wH)) , zK)
      tyZK = VTat Zero K ZeroEl wN (conv-sym (snd zK)) RZK c ec cU
      zr2 = pConvM {G = H} {M = zl} {M' = zr} {T = subst1 Cl Zero} {T' = subst1 Cl K} u c uc cU tyZK zr1
      VTK = VTat K K ZeroEl wN (conv-refl hK) (fst rK , (zK , zK)) c ec cU
      hrL = HRs-trans (HRs-rec (fst zK)) (hrs-step hr-rec-zero hrs-refl)
      hrR = HRs-trans (HRs-rec (fst zK')) (hrs-step hr-rec-zero hrs-refl)
  recGo (SucEl w1) wN K K' cK rK c ec cU (SucEl w2) u le rb uc = go (bot-or u)
    where
      sp = snd (sucV rK)
      open SucTm sp
      w1N = sucNat-to w1 wN
      hK = fst (pCv cK)
      hP = fst (pCv cP)
      diagP = diagN {K = P} {K' = P'} w1 w1N pred
      RSK : RTm H (Suc P) K Nat (SucEl w1) NatCode
      RSK = sucM (tyeq-refl iN) (record { P = P ; P' = P ; rM = hrs-refl ; rM' = rM ; cM = conv-refl (ty-Suc hP)
                                         ; cM' = cM ; cP = conv-refl hP ; pred = diagP })
      RSS : RTm H (Suc P) (Suc P) Nat (SucEl w1) NatCode
      RSS = sucM (tyeq-refl iN) (record { P = P ; P' = P ; rM = hrs-refl ; rM' = hrs-refl ; cM = conv-refl (ty-Suc hP)
                                         ; cM' = conv-refl (ty-Suc hP) ; cP = conv-refl hP ; pred = diagP })
      VTK = VTat K K (SucEl w1) wN (conv-refl hK) (diagN {K = K} {K' = K'} (SucEl w1) wN rK) c ec cU
      hrL = HRs-trans (HRs-rec rM) (hrs-step hr-rec-suc hrs-refl)
      hrR = HRs-trans (HRs-rec rM') (hrs-step hr-rec-suc hrs-refl)
      AppL = App (App sl P) (RecL P)
      AppR = App (App sr P') (RecR P')
      SC = subst1 Cl (Suc P)
      Bst = \ x -> EvalRel (Arr C (substExpr sucSub C)) (extendEnv rho x)

      go : Or (Eq u Bot) (NotBot u) -> RTm H (RecL K) (RecR K') (subst1 Cl K) u c
      go (left refl) = tt
      go (right nbu) =
        pExpM u c uc cU hrL (isL K P hP cM) VTK (pExpM' u c uc cU hrR (isR K K' P' (snd (pCv cP)) cK cM') VTK rB)
        where
          r = dfst rb ; gr = dfst (dsnd rb) ; es = dsnd (dsnd rb)
          x = sing w2 (sing r u)
          cx = EvalRel-coh st rho crho x es
          cw2 = sing-key-coh w2 (sing r u) cx
          cr = sing-key-coh r u (sing-val-coh w2 (sing r u) cx)
          ts = sTm dst rho (Env.fits E) x es

          cw1 = FinMem-coh-u w1 NatCode w1N

          recRel : (u1 b2 : FinEl) -> Coherent u1 -> LeCode u1 r -> EvalRel C (extendEnv rho w1) b2 -> FinMem b2 UCode ->
            FinMem u1 b2 -> RTm H (RecL P) (RecR P') (subst1 Cl P) u1 b2
          recRel u1 b2 cu1 lu1r eb2 b2U u1b2 = gor (bot-or u1)
            where
              gor : Or (Eq u1 Bot) (NotBot u1) -> RTm H (RecL P) (RecR P') (subst1 Cl P) u1 b2
              gor (left refl) = tt
              gor (right nbu1) =
                let nbr = NotBot-from-Le u1 r nbu1 lu1r
                    rb1 = RP.down-B r u1 w2 (guard-elim r nbr gr) nbu1 cu1 lu1r
                in recGo w1 w1N P P' cP pred b2 eb2 b2U w2 u1 le rb1 u1b2

          step2 : (u0 : FinEl) -> Coherent u0 -> LeCode u0 w1 ->
            (v e0 : FinEl) -> LeCode (sing r u) v -> FinMem v e0 -> FinMem e0 UCode -> Bst u0 e0 ->
            RTm H (App sl P) (App sr P') (Arr (subst1 Cl P) SC) v e0 -> RTm H AppL AppR SC u c
          step2 u0 cu0 lu0w1 (FunEl g2) (PiCode b2 f2) lsr vm0 e0U ef0 r2' =
            let cu2 = piU b2 f2 e0U
                rel2 = lamV r2'
                ctg2 = cft-from-cf g2 (finMem-funel-coh g2 b2 f2 vm0)
                sb2 = selectionBelow g2 r ctg2 cr
                u1 = dfst sb2 ; v1 = dfst (dsnd sb2) ; sel2 = dfst (dsnd (dsnd sb2))
                lu1r = dfst (dsnd (dsnd (dsnd sb2))) ; eq2 = dsnd (dsnd (dsnd (dsnd sb2)))
                luv1 = D.Eq-transport (LeCode u) eq2 (dfst lsr)
                cu1 = Coherent-Selection sel2 ctg2
                u1b2 = selKey vm0 e0U sel2
                le0 = mkSigma (EnvLe-refl rho crho) (mkSigma cu0 (mkSigma cw1 lu0w1))
                eb2 = EvalRel-mon-env C (extendEnv rho u0) (extendEnv rho w1) le0 b2 (dfst (dsnd ef0))
                rRec = recRel u1 b2 cu1 lu1r eb2 (CodeU.bU cu2) u1b2
                r3 = piApp rel2 u1 v1 sel2 (RecL P) (RecR P') (cRec P P' cP) rRec
                r3' = transport (\ X -> RTm H AppL AppR X v1 (EvalFun f2 u1)) (subst1-wk SC (RecL P)) r3
                ef2 = famEval (EvalRel C (extendEnv rho u0))
                        (\ y -> EvalRel (wkExpr (substExpr sucSub C)) (extendEnv (extendEnv rho u0) y))
                        (bodyOK (wkExpr (substExpr sucSub C)) (extendEnv rho u0) (mkSigma crho cu0))
                        f2 (CodeU.cft cu2) (dsnd (dsnd ef0)) u1 cu1
                e1s = EvalRel-unwk (substExpr sucSub C) (extendEnv rho u0) u1 (EvalFun f2 u1) ef2
                e1c = sucSem C rho crho u0 (EvalFun f2 u1) cu0 e1s
                e1c' = EvalRel-mon-env C (extendEnv rho (SucEl u0)) (extendEnv rho (SucEl w1)) le0 (EvalFun f2 u1) e1c
                VTsp = \ c' ec' cU' -> VTat (Suc P) (Suc P) (SucEl w1) wN (conv-refl (ty-Suc hP)) RSS c' ec' cU'
            in adj (EvalRel C (extendEnv rho (SucEl w1))) (EvalRel-ideal C (extendEnv rho (SucEl w1)) (mkSigma crho cw1)) VTsp
                 v1 (EvalFun f2 u1) e1c' (efU b2 f2 cu2 u1b2) (selVal vm0 e0U sel2) r3' u c ec cU luv1 uc

          pickS : (y a : FinEl) -> LeCode x y -> EvalRel st rho y -> FinMem y a -> EvalRel (RecStep C) rho a ->
            RTm H AppL AppR SC u c
          pickS (FunEl gg) (PiCode b f) lxy ey ya ea =
            let aU = FinMem-a-in-U (FunEl gg) (PiCode b f) ya
                cu = piU b f aU
                FsT = transport (\ X -> RTm H sl sr X (FunEl gg) (PiCode b f)) (subst-RecStep s C) (Fs (PiCode b f) (FunEl gg) ea aU ey ya)
                rel1 = lamV FsT
                ctg = cft-from-cf gg (finMem-funel-coh gg b f ya)
                sb = selectionBelow gg w2 ctg cw2
                u0 = dfst sb ; v0 = dfst (dsnd sb) ; sel = dfst (dsnd (dsnd sb))
                lu0 = dfst (dsnd (dsnd (dsnd sb))) ; eq0 = dsnd (dsnd (dsnd (dsnd sb)))
                lsr = D.Eq-transport (LeCode (sing r u)) eq0 (dfst lxy)
                cu0 = Coherent-Selection sel ctg
                u0b = selKey ya aU sel
                lu0w1 = LeCode-trans u0 w2 w1 cu0 cw2 cw1 lu0 le
                rP0 = adj (EvalRel Nat rho) (EvalRel-ideal Nat rho crho) (\ c' ec' cU' -> natTy iN c' ec')
                        w1 NatCode natEr NcU w1N pred u0 b (dfst (dsnd ea)) (CodeU.bU cu) lu0w1 u0b
                r2 = piApp rel1 u0 v0 sel P P' cP rP0
                r2' = transport (\ X -> RTm H (App sl P) (App sr P') X v0 (EvalFun f u0)) (stepE Cl P) r2
                ef0 = famEval (EvalRel Nat rho) Bst (bodyOK (Arr C (substExpr sucSub C)) rho crho) f (CodeU.cft cu)
                        (dsnd (dsnd ea)) u0 cu0
            in step2 u0 cu0 lu0w1 v0 (EvalFun f u0) lsr (selVal ya aU sel) (efU b f cu u0b) ef0 r2'

          rA : RTm H AppL AppR SC u c
          rA = pickS (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                 (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
          rB = pConvM {G = H} {M = AppL} {M' = AppR} {T = SC} {T' = subst1 Cl K} u c uc cU
                 (VTat (Suc P) K (SucEl w1) wN (conv-sym cM) RSK c ec cU) rA

  private
    absurdW : (u w : FinEl) -> LeCode w Bot -> RecB Pz Ps u w -> Empty
    absurdW u Bot l ()

  recEntry : {k k' : Expr g} -> HasType G k Nat -> ConvTm H (substExpr s k) (substExpr s' k') Nat ->
    TmRelAt H s s' rho k k' Nat ->
    TmRelAt H s s' rho (Rec (Lam Nat C) z st k) (Rec (Lam Nat C') z' st' k') (subst1 C k)
  recEntry {k} {k'} dk cK Fk a u ea aU eu ua = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> RTm H (RecL (substExpr s k)) (RecR (substExpr s' k')) (substExpr s (subst1 C k)) u a
      go (left refl) = tt
      go (right nb) = pickK (dfst ts) (dfst (dsnd ts)) (dfst (dsnd (dsnd ts))) (dfst (dsnd (dsnd (dsnd ts))))
                        (dfst (dsnd (dsnd (dsnd (dsnd ts))))) (dsnd (dsnd (dsnd (dsnd (dsnd ts)))))
        where
          bd = guard-elim u nb eu
          w = dfst bd ; ew = dfst (dsnd bd) ; rb = dsnd (dsnd bd)
          fw = EvalRel-subst1-forward C k rho a crho ea
          x = dfst fw ; ex = dfst (dsnd fw) ; ax = dsnd (dsnd fw)
          ik = EvalRel-ideal k rho crho
          cp = Ideal.comp ik w x ew ex
          wx = Sup w x
          ts = sTm dk rho (Env.fits E) wx (Ideal.sup ik w x ew ex)
          cw = EvalRel-coh k rho crho w ew
          cx = EvalRel-coh k rho crho x ex
          cwx = MAHLOINJ.Domain.Kernel.Coherent-Sup w x cp cw cx
          pickK : (y a' : FinEl) -> LeCode wx y -> EvalRel k rho y -> FinMem y a' -> EvalRel Nat rho a' ->
            RTm H (RecL (substExpr s k)) (RecR (substExpr s' k')) (substExpr s (subst1 C k)) u a
          pickK y NatCode lwxy ey yN ea' =
            let cy = FinMem-coh-u y NatCode yN
                lwy = LeCode-trans w wx y cw cwx cy (LeCode-Sup-left w x cp cw cx) lwxy
                lxy = LeCode-trans x wx y cx cwx cy (LeCode-Sup-right w x cp cw cx) lwxy
                ay = EvalRel-mon-env C (extendEnv rho x) (extendEnv rho y)
                       (mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cy lxy))) a ax
                rK = Fk NatCode y natEr NcU ey yN
                r = recGo y yN (substExpr s k) (substExpr s' k') cK rK a ay aU w u lwy rb ua
            in transport (\ X -> RTm H (RecL (substExpr s k)) (RecR (substExpr s' k')) X u a)
                 (Eq-sym (subst-subst1-comm s C k)) r
          pickK Bot Bot lwxy ey yb ea' =
            Empty-elim (absurdW u w (LeCode-trans w wx Bot cw cwx tt (LeCode-Sup-left w x cp cw cx) lwxy) rb)
