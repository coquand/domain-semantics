{-# OPTIONS --without-K #-}
module Validity5Sup where
open import Validity5SymTrans public

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              codeFst ; codeSnd)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ; Fst ; Snd ; MkPair ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; conv-Sigma ; conv-Fst ; conv-Snd ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-Sigma ; ty-Fst ; ty-Snd ; ty-App)
open import ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma)
open import PaperSemanticsSigma using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ;
  LeCode ; LeCode-trans ; LeCode-Bot ;
  Comp-down ; finMem-upward ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMemUCode-Sup ; FinMem-Sup-element ;
  EvalFun-in-UCode ; EvalFun-mon ; EvalFun-mon-arg ;
  comp-EvalFun ; EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMemAllU-append-Sup ;
  LeFunCode-refl ; LeFunCode ; append ;
  Comp-refl ; comp-Sup ; comp-Bot-r ;
  Comp-value-EvalFun ; coherentWith-to-compStepFun ;
  CFTcons ; CoherentFunTail ; CoherentWith ;
  FinMem-Prop-to-U)
open import SelectionSigma using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import ValiditySigma using (Red-unique-Pi ; Red-unique-Sigma ;
  bU-from-cf-fmFun ; FinMem-Coherent)
open import SubstitutionLemmaSigma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

{-# TERMINATING #-}
mutual

  ValTy2-Sup : {n : Nat} (G : Ctx n) (T : Expr n) (a1 a2 : FinEl) ->
    Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
    ValTy2 G T a1 -> ValTy2 G T a2 -> ValTy2 G T (Sup a1 a2)
  ValTy2-Sup G T Bot a2 comp fm1 fm2 vt1 vt2 = vt2
  ValTy2-Sup G T PropCode Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode UCode ()
  ValTy2-Sup G T PropCode PropCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode (FunEl g) ()
  ValTy2-Sup G T PropCode (PiCode b g) ()
  ValTy2-Sup G T PropCode (SigmaCode b g) ()
  ValTy2-Sup G T PropCode (PairCode x y) ()
  ValTy2-Sup G T UCode Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T UCode UCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T UCode (FunEl g) ()
  ValTy2-Sup G T UCode (PiCode b g) ()
  ValTy2-Sup G T UCode (SigmaCode b g) ()
  ValTy2-Sup G T UCode (PairCode x y) ()
  ValTy2-Sup G T (FunEl g) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) UCode ()
  ValTy2-Sup G T (FunEl g) (FunEl h) comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) (PiCode b h) ()
  ValTy2-Sup G T (FunEl g) (SigmaCode b h) ()
  ValTy2-Sup G T (FunEl g) (PairCode x y) ()
  ValTy2-Sup G T (PiCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (PiCode b1 f1) UCode ()
  ValTy2-Sup G T (PiCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (PiCode b1 f1) (SigmaCode b2 f2) ()
  ValTy2-Sup G T (PiCode b1 f1) (PairCode x y) ()
  ValTy2-Sup G T (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = RValTyPi.domA vt1
        B1    = RValTyPi.codB vt1
        red1  = RValTyPi.red vt1
        cf1   = RValTyPi.cohF vt1
        allU1 = RValTyPi.fmAllU vt1
        htA1  = RValTyPi.htA vt1
        htB1  = RValTyPi.htB vt1
        vtAb1 = RValTyPi.valA vt1
        piEV1 = RValTyPi.edgeV vt1
        piEE1 = RValTyPi.edgeE vt1
        A2    = RValTyPi.domA vt2
        B2    = RValTyPi.codB vt2
        red2  = RValTyPi.red vt2
        cf2   = RValTyPi.cohF vt2
        allU2 = RValTyPi.fmAllU vt2
        vtAb2 = RValTyPi.valA vt2
        piEV2 = RValTyPi.edgeV vt2
        piEE2 = RValTyPi.edgeE vt2
        uniq  = Red3-unique-Pi red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        piEV2' : PiEdgeVal2 G A1 B1 b2 f2
        piEV2' = Eq-transport (\ Y -> PiEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> PiEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) piEV2)
        piEE2' : PiEdgeEq2 G A1 B1 b2 f2
        piEE2' = Eq-transport (\ Y -> PiEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> PiEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) piEE2)
        comp-b = fst comp
        comp-f = snd comp
        b1U    = fst fm1
        allU1' = fst (snd fm1)
        b2U    = fst fm2
        allU2' = fst (snd fm2)
        cb1    = coh-from-aU b1 b1U
        cb2    = coh-from-aU b2 b2U
        supU   = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup  = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1   = cf1
        ctf2   = cf2
        cf-app = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        vtA-sup = ValTy2-Sup G A1 b1 b2 comp-b b1U b2U vtAb1 vtAb2'
        piEV : PiEdgeVal2 G A1 B1 (Sup b1 b2) (append f1 f2)
        piEV = \ u v sel N htN valN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valN
              val-u1-b1  = downVal2 _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valN
              val-u2-b2  = downVal2 _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              vt-v1  = piEV1 u1 v1 sel1 N htN val-u1-b1
              vt-v2  = piEV2' u2 v2 sel2 N htN val-u2-b2
              vt-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downValTy2 _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
        piEE : PiEdgeEq2 G A1 B1 (Sup b1 b2) (append f1 f2)
        piEE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              eqv-u1-sup = restrictEqVal2 _ _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup eqN
              eqv-u1-b1  = downEqVal2 _ _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU eqv-u1-sup
              eqv-u2-sup = restrictEqVal2 _ _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup eqN
              eqv-u2-b2  = downEqVal2 _ _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU eqv-u2-sup
              eqt-v1 = piEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
              eqt-v2 = piEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in record
      { domA   = A1
      ; codB   = B1
      ; red    = red1
      ; cohF   = cf-app
      ; fmAllU = allU-app
      ; htA    = htA1
      ; htB    = htB1
      ; valA   = vtA-sup
      ; edgeV  = piEV
      ; edgeE  = piEE
      }
  -- SigmaCode ValTy2-Sup (mirrors PiCode case exactly in structure)
  ValTy2-Sup G T (SigmaCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (SigmaCode b1 f1) UCode ()
  ValTy2-Sup G T (SigmaCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PiCode b2 f2) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PairCode x y) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = RValTySigma.domA vt1
        B1    = RValTySigma.codB vt1
        red1  = RValTySigma.red vt1
        cf1   = RValTySigma.cohF vt1
        allU1 = RValTySigma.fmAllU vt1
        htA1  = RValTySigma.htA vt1
        htB1  = RValTySigma.htB vt1
        vtAb1 = RValTySigma.valA vt1
        sigEV1 = RValTySigma.edgeV vt1
        sigEE1 = RValTySigma.edgeE vt1
        A2    = RValTySigma.domA vt2
        B2    = RValTySigma.codB vt2
        red2  = RValTySigma.red vt2
        cf2   = RValTySigma.cohF vt2
        allU2 = RValTySigma.fmAllU vt2
        vtAb2 = RValTySigma.valA vt2
        sigEV2 = RValTySigma.edgeV vt2
        sigEE2 = RValTySigma.edgeE vt2
        uniq  = Red3-unique-Sigma red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        sigEV2' : SigmaEdgeVal2 G A1 B1 b2 f2
        sigEV2' = Eq-transport (\ Y -> SigmaEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) sigEV2)
        sigEE2' : SigmaEdgeEq2 G A1 B1 b2 f2
        sigEE2' = Eq-transport (\ Y -> SigmaEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) sigEE2)
        comp-b = fst comp
        comp-f = snd comp
        b1U    = fst fm1
        allU1' = fst (snd fm1)
        b2U    = fst fm2
        allU2' = fst (snd fm2)
        cb1    = coh-from-aU b1 b1U
        cb2    = coh-from-aU b2 b2U
        supU   = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup  = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1   = cf1
        ctf2   = cf2
        cf-app = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        vtA-sup = ValTy2-Sup G A1 b1 b2 comp-b b1U b2U vtAb1 vtAb2'
        sigEV : SigmaEdgeVal2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sigEV = \ u v sel N htN valN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valN
              val-u1-b1  = downVal2 _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valN
              val-u2-b2  = downVal2 _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              vt-v1  = sigEV1 u1 v1 sel1 N htN val-u1-b1
              vt-v2  = sigEV2' u2 v2 sel2 N htN val-u2-b2
              vt-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downValTy2 _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
        sigEE : SigmaEdgeEq2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sigEE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              eqv-u1-sup = restrictEqVal2 _ _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup eqN
              eqv-u1-b1  = downEqVal2 _ _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU eqv-u1-sup
              eqv-u2-sup = restrictEqVal2 _ _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup eqN
              eqv-u2-b2  = downEqVal2 _ _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU eqv-u2-sup
              eqt-v1 = sigEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
              eqt-v2 = sigEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in record
      { domA   = A1
      ; codB   = B1
      ; red    = red1
      ; cohF   = cf-app
      ; fmAllU = allU-app
      ; fmBU   = supU
      ; htA    = htA1
      ; htB    = htB1
      ; valA   = vtA-sup
      ; edgeV  = sigEV
      ; edgeE  = sigEE
      }
  ValTy2-Sup G T (PairCode u v) a2 comp ()

  ------------------------------------------------------------------
  -- EqValTy2-Sup
  ------------------------------------------------------------------

  EqValTy2-Sup : {n : Nat} (G : Ctx n) (M N : Expr n) (u1 u2 : FinEl) ->
    Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
    EqValTy2 G M N u1 -> EqValTy2 G M N u2 -> EqValTy2 G M N (Sup u1 u2)
  EqValTy2-Sup G M N Bot u2 comp fm1 fm2 eq1 eq2 = eq2
  EqValTy2-Sup G M N PropCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode UCode ()
  EqValTy2-Sup G M N PropCode PropCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode (FunEl g) ()
  EqValTy2-Sup G M N PropCode (PiCode b g) ()
  EqValTy2-Sup G M N PropCode (SigmaCode b g) ()
  EqValTy2-Sup G M N PropCode (PairCode x y) ()
  EqValTy2-Sup G M N UCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode UCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode (FunEl g) ()
  EqValTy2-Sup G M N UCode (PiCode b g) ()
  EqValTy2-Sup G M N UCode (SigmaCode b g) ()
  EqValTy2-Sup G M N UCode (PairCode x y) ()
  EqValTy2-Sup G M N (FunEl g) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) UCode ()
  EqValTy2-Sup G M N (FunEl g) (FunEl h) comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) (PiCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (SigmaCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (PairCode x y) ()
  EqValTy2-Sup G M N (PiCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (PiCode b1 f1) UCode ()
  EqValTy2-Sup G M N (PiCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (SigmaCode b2 f2) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PairCode x y) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM1-eq1 = fst eq1
        vtN1-eq1 = fst (snd eq1)
        eqPi1    = snd (snd eq1)
        vtM2-eq2 = fst eq2
        vtN2-eq2 = fst (snd eq2)
        eqPi2    = snd (snd eq2)
        AM      = REqValTyPi.domA eqPi1
        BM      = REqValTyPi.codB eqPi1
        AN      = REqValTyPi.domA' eqPi1
        BN      = REqValTyPi.codB' eqPi1
        redM1   = REqValTyPi.redM eqPi1
        redN1   = REqValTyPi.redN eqPi1
        cfEq1   = REqValTyPi.cohF eqPi1
        allUEq1 = REqValTyPi.fmAllU eqPi1
        convAA1 = REqValTyPi.convA eqPi1
        convBB1 = REqValTyPi.convB eqPi1
        eqvtA1  = REqValTyPi.eqA eqPi1
        piEET1  = REqValTyPi.edgeET eqPi1
        AM2     = REqValTyPi.domA eqPi2
        BM2     = REqValTyPi.codB eqPi2
        AN2     = REqValTyPi.domA' eqPi2
        BN2     = REqValTyPi.codB' eqPi2
        redM2   = REqValTyPi.redM eqPi2
        redN2   = REqValTyPi.redN eqPi2
        cfEq2   = REqValTyPi.cohF eqPi2
        allUEq2 = REqValTyPi.fmAllU eqPi2
        convAA2 = REqValTyPi.convA eqPi2
        convBB2 = REqValTyPi.convB eqPi2
        eqvtA2  = REqValTyPi.eqA eqPi2
        piEET2  = REqValTyPi.edgeET eqPi2
        uniqM   = Red3-unique-Pi redM1 redM2
        eqAM    = fst uniqM
        eqBM    = snd uniqM
        uniqN   = Red3-unique-Pi redN1 redN2
        eqAN    = fst uniqN
        eqBN    = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) eqvtA2)
        piEET2' : PiEdgeEqTy2 G AM BM BN b2 f2
        piEET2' = Eq-transport (\ X -> PiEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                    (Eq-transport (\ X -> PiEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                      (Eq-transport (\ X -> PiEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) piEET2))
        comp-b  = fst comp
        comp-f  = snd comp
        b1U     = fst fm1
        allU1'  = fst (snd fm1)
        b2U     = fst fm2
        allU2'  = fst (snd fm2)
        cb1     = coh-from-aU b1 b1U
        cb2     = coh-from-aU b2 b2U
        supU    = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup   = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1    = cfEq1
        ctf2    = cfEq2
        cf-app  = CoherentFunTail-append f1 f2 cfEq1 cfEq2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        eqvtA-sup = EqValTy2-Sup G AM AN b1 b2 comp-b b1U b2U eqvtA1 eqvtA2'
        piEET : PiEdgeEqTy2 G AM BM BN (Sup b1 b2) (append f1 f2)
        piEET = \ u v sel P htP valP ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ AM u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valP
              val-u1-b1  = downVal2 _ _ AM u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ AM u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valP
              val-u2-b2  = downVal2 _ _ AM u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              eqt-v1  = piEET1 u1 v1 sel1 P htP val-u1-b1
              eqt-v2  = piEET2' u2 v2 sel2 P htP val-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        vtM-sup = ValTy2-Sup G M (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtM1-eq1 vtM2-eq2
        vtN-sup = ValTy2-Sup G N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtN1-eq1 vtN2-eq2
        eqTyPi = record
          { domA   = AM
          ; codB   = BM
          ; domA'  = AN
          ; codB'  = BN
          ; redM   = redM1
          ; redN   = redN1
          ; cohF   = cf-app
          ; fmAllU = allU-app
          ; convA  = convAA1
          ; convB  = convBB1
          ; eqA    = eqvtA-sup
          ; edgeET = piEET
          }
    in mkSigma vtM-sup (mkSigma vtN-sup eqTyPi)
  -- SigmaCode EqValTy2-Sup (mirrors PiCode)
  EqValTy2-Sup G M N (SigmaCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (SigmaCode b1 f1) UCode ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PiCode b2 f2) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PairCode x y) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM1 = fst eq1
        vtN1 = fst (snd eq1)
        eqS1 = snd (snd eq1)
        vtM2 = fst eq2
        vtN2 = fst (snd eq2)
        eqS2 = snd (snd eq2)
        AM   = REqValTySigma.domA eqS1
        BM   = REqValTySigma.codB eqS1
        AN   = REqValTySigma.domA' eqS1
        BN   = REqValTySigma.codB' eqS1
        redM1 = REqValTySigma.redM eqS1
        redN1 = REqValTySigma.redN eqS1
        AM2  = REqValTySigma.domA eqS2
        BM2  = REqValTySigma.codB eqS2
        AN2  = REqValTySigma.domA' eqS2
        BN2  = REqValTySigma.codB' eqS2
        redM2 = REqValTySigma.redM eqS2
        redN2 = REqValTySigma.redN eqS2
        uniqM = Red3-unique-Sigma redM1 redM2
        eqAM  = fst uniqM
        eqBM  = snd uniqM
        uniqN = Red3-unique-Sigma redN1 redN2
        eqAN  = fst uniqN
        eqBN  = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) (REqValTySigma.eqA eqS2))
        sigEET2' : SigmaEdgeEqTy2 G AM BM BN b2 f2
        sigEET2' = Eq-transport (\ X -> SigmaEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                    (Eq-transport (\ X -> SigmaEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                      (Eq-transport (\ X -> SigmaEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) (REqValTySigma.edgeET eqS2)))
        comp-b = fst comp
        comp-f = snd comp
        b1U    = fst fm1
        allU1' = fst (snd fm1)
        b2U    = fst fm2
        allU2' = fst (snd fm2)
        cb1    = coh-from-aU b1 b1U
        cb2    = coh-from-aU b2 b2U
        supU   = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup  = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1   = REqValTySigma.cohF eqS1
        ctf2   = REqValTySigma.cohF eqS2
        cf-app = CoherentFunTail-append f1 f2 ctf1 ctf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        eqvtA-sup = EqValTy2-Sup G AM AN b1 b2 comp-b b1U b2U (REqValTySigma.eqA eqS1) eqvtA2'
        sigEET : SigmaEdgeEqTy2 G AM BM BN (Sup b1 b2) (append f1 f2)
        sigEET = \ u v sel P htP valP ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ AM u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valP
              val-u1-b1  = downVal2 _ _ AM u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ AM u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valP
              val-u2-b2  = downVal2 _ _ AM u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              eqt-v1  = REqValTySigma.edgeET eqS1 u1 v1 sel1 P htP val-u1-b1
              eqt-v2  = sigEET2' u2 v2 sel2 P htP val-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        vtM-sup = ValTy2-Sup G M (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vtM1 vtM2
        vtN-sup = ValTy2-Sup G N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vtN1 vtN2
        eqTySigma = record
          { domA = AM ; codB = BM ; domA' = AN ; codB' = BN
          ; redM = redM1 ; redN = redN1
          ; cohF = cf-app ; fmAllU = allU-app
          ; convA = REqValTySigma.convA eqS1 ; convB = REqValTySigma.convB eqS1
          ; eqA = eqvtA-sup ; edgeET = sigEET
          }
    in mkSigma vtM-sup (mkSigma vtN-sup eqTySigma)
  EqValTy2-Sup G M N (PairCode u v) a2 comp ()
