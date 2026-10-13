{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/App.agda  (Tarski port of MAHLOINJ/Adq/App)
--
-- The application step of the fundamental lemma, semantically generic:
-- from the relation of the function (at every Pi code of its type) and
-- of the argument (at every code of the domain), the relation of the
-- application at every code of the result type.
------------------------------------------------------------------------

module MAHLORT.Adq.App where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; nil ; cons ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Coherent ; NotBot ; LeCode-trans ; Coherent-EvalFun
        ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ; cft-from-cf ; coh-from-aU)
open import MAHLOINJ.Model.Selection
  using (Selection ; selectionBelow ; Coherent-Selection ; Or ; left ; right)
open import MAHLOINJ.Model.Comb
  using (Pred ; Ideal ; BodyOK ; AppS ; PiS ; LamS ; bot-or ; guard-elim)
open import MAHLOINJ.Model.SemLam using (InvTypP ; module AppTyping)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (CodeU ; piU)
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base using (adj ; selKey ; selVal ; efU)

module AppCore {h : Num} {H : Ctx h} (Ml Mr Nl Nr As : Expr h) (Bs : Expr (suc h))
  (PM PN PA : Pred) (Bb : FinEl -> Pred) (PT : Pred)
  (iM : Ideal PM) (iN : Ideal PN) (okb : BodyOK Bb) (iT : Ideal PT)
  (invM : InvTypP PM (PiS PA (LamS PA Bb)))
  (toT : (w v : FinEl) -> PN w -> Bb w v -> PT v)
  (FM : (a u : FinEl) -> PiS PA (LamS PA Bb) a -> FinMem a UCode -> PM u -> FinMem u a ->
        RTm H Ml Mr (PiB As Bs) u a)
  (FN : (b w : FinEl) -> PA b -> FinMem b UCode -> PN w -> FinMem w b -> RTm H Nl Nr As w b)
  (A0 A1 : Expr h) (B0 B1 : Expr (suc h))
  (e0 : TyEq H As A0) (e1 : TyEq (extend H As) Bs B0) (e2 : TyEq H As A1) (e3 : TyEq (extend H As) Bs B1)
  (cN : ConvTm H Nl Nr As)
  (VT : (c : FinEl) -> PT c -> FinMem c UCode -> RTy H (subst1 Bs Nl) (subst1 Bs Nl) c) where

  private
    module AT = AppTyping PM PN PA Bb PT iM iN okb invM toT (Ideal.bot iT)

  -- the main step, at a typing code of a function approximant above (w |-> v)
  step : (w v c : FinEl) -> PN w -> PT c -> FinMem c UCode -> FinMem v c ->
    (g : FinFun) (b : FinEl) (f : FinFun) -> LeCode (D.FunEl (cons (mkSigma w v) nil)) (FunEl g) -> PM (FunEl g) ->
    FinMem (FunEl g) (PiCode b f) -> PiS PA (LamS PA Bb) (PiCode b f) ->
    RTm H (appB A0 B0 Ml Nl) (appB A1 B1 Mr Nr) (subst1 Bs Nl) v c
  step w v c ew ec cU vm g b f le em gm evPi =
    let pU = finMem-funel-wf g b f gm
        cu = piU b f pU
        ctg = cft-from-cf g (finMem-funel-coh g b f gm)
        cw = Ideal.coh iN w ew
        sb = selectionBelow g w ctg cw
        u0 = dfst sb ; v0 = dfst (dsnd sb) ; sel = dfst (dsnd (dsnd sb))
        le-u0-w = dfst (dsnd (dsnd (dsnd sb))) ; eq-v0 = dsnd (dsnd (dsnd (dsnd sb)))
        le-v-v0 = D.Eq-transport (LeCode v) eq-v0 (dfst le)
        cu0 = Coherent-Selection sel ctg
        eu0 = Ideal.down iN w u0 ew cu0 le-u0-w
        u0b = selKey gm pU sel
        bU = CodeU.bU cu
        rN = FN b u0 (dfst (dsnd evPi)) bU eu0 u0b
        rel = lamV (FM (PiCode b f) (FunEl g) evPi pU em gm)
        r1 = piApp rel u0 v0 sel A0 A1 B0 B1 e0 e1 e2 e3 Nl Nr cN rN
        ecod = AT.cod w u0 b f ew cu0 le-u0-w (CodeU.cft cu) (dsnd (dsnd evPi))
    in adj PT iT VT v0 (EvalFun f u0) ecod (efU b f cu u0b) (selVal gm pU sel) r1 v c ec cU le-v-v0 vm

  app : (c v : FinEl) -> PT c -> FinMem c UCode -> AppS PM PN v -> FinMem v c ->
    RTm H (appB A0 B0 Ml Nl) (appB A1 B1 Mr Nr) (subst1 Bs Nl) v c
  app c v ec cU ev vm = go (bot-or v)
    where
      go : Or (Eq v Bot) (NotBot v) -> RTm H (appB A0 B0 Ml Nl) (appB A1 B1 Mr Nr) (subst1 Bs Nl) v c
      go (left refl) = tt
      go (right nb) =
        let bd = guard-elim v nb ev
            w = dfst bd ; ew = dfst (dsnd bd) ; em = dsnd (dsnd bd)
            t = invM (D.FunEl (cons (mkSigma w v) nil)) em
        in pick w ew (dfst t) (dfst (dsnd t)) (dfst (dsnd (dsnd t))) (dfst (dsnd (dsnd (dsnd t))))
             (dfst (dsnd (dsnd (dsnd (dsnd t))))) (dsnd (dsnd (dsnd (dsnd (dsnd t)))))
        where
          pick : (w : FinEl) -> PN w -> (hh piaf : FinEl) -> LeCode (D.FunEl (cons (mkSigma w v) nil)) hh -> PM hh ->
                 FinMem hh piaf -> PiS PA (LamS PA Bb) piaf -> RTm H (appB A0 B0 Ml Nl) (appB A1 B1 Mr Nr) (subst1 Bs Nl) v c
          pick w ew (FunEl g) (PiCode b f) le em gm evPi = step w v c ew ec cU vm g b f le em gm evPi
