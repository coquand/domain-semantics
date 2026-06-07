{-# OPTIONS --without-K #-}
module SigmaProp.Validity5DownUpRestrict where
open import SigmaProp.Validity5Core public

import SigmaProp.BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              codeFst ; codeSnd)
import SigmaProp.RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ; Fst ; Snd ; MkPair ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import SigmaProp.TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ;
  WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; conv-Sigma ; conv-Fst ; conv-Snd ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-Sigma ; ty-Fst ; ty-Snd ; ty-App)
open import SigmaProp.ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma)
open import SigmaProp.PaperSemanticsSigma using (EvalFun ;
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
open import SigmaProp.SelectionSigma using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import SigmaProp.ValiditySigma using (Red-unique-Pi ; Red-unique-Sigma ;
  bU-from-cf-fmFun ;
  FinMem-Coherent)
open import SigmaProp.SubstitutionLemmaSigma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Transport functions: downVal2, downEqVal2, downValTy2, downEqValTy2,
--   upVal2, upEqVal2, restrictVal2, restrictEqVal2, and helpers.
--
-- Mechanical port from Validity4.agda lines 1056-3051, with only
-- record/field name changes:
--   RValPair -> RValSigma, REqValPair -> REqValSigma
--   .cohU -> .cohW1, .fmU -> .fmW1
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  ------------------------------------------------------------------
  -- downVal2 / downEqVal2 / downValTy2 / downEqValTy2
  ------------------------------------------------------------------

  downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
    Val2 G M T u a1 -> Val2 G M T u a0
  downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
    EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
  downValTy2 : {n : Nat} (G : Ctx n) (M : Expr n) (u0 u1 : FinEl) ->
    LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
    ValTy2 G M u1 -> ValTy2 G M u0
  downEqValTy2 : {n : Nat} (G : Ctx n) (M N : Expr n) (u0 u1 : FinEl) ->
    LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
    EqValTy2 G M N u1 -> EqValTy2 G M N u0

  upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    Val2 G M T u a0 -> ValTy2 G T a1 ->
    Val2 G M T u a1
  upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    EqVal2 G M N T u a0 -> ValTy2 G T a1 ->
    EqVal2 G M N T u a1

  restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    EqVal2 G M N T u a -> EqVal2 G M N T u' a

  -- downVal2 cases
  downVal2 G M T u Bot          a1             le mem ca0 ca1 src = tt
  downVal2 G M T u UCode        Bot            ()
  downVal2 G M T u UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T u UCode        (FunEl h)      ()
  downVal2 G M T u UCode        (PiCode b f)   ()
  downVal2 G M T u UCode        (SigmaCode b f) ()
  downVal2 G M T u UCode        (PairCode x y) ()
  downVal2 G M T u UCode        PropCode       ()
  downVal2 G M T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T u PropCode       Bot            ()
  downVal2 G M T u PropCode       UCode          ()
  downVal2 G M T u PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T u PropCode       (FunEl h)      ()
  downVal2 G M T u PropCode       (PiCode b f)   ()
  downVal2 G M T u PropCode       (SigmaCode b f) ()
  downVal2 G M T u PropCode       (PairCode x y) ()
  downVal2 G M T u (PiCode b0 f0) Bot          ()
  downVal2 G M T u (PiCode b0 f0) UCode        ()
  downVal2 G M T u (PiCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (PiCode b0 f0) PropCode     ()
  downVal2 G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty  = fst src
        vpiM = snd src
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        vty'  = downValTy2 G _ (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
        -- Extract vtAb1 from vty (RValTyPi)
        vtAb1 : ValTy2 G (RValPi.domA0 vpiM) b1
        vtAb1 = Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vty))))
                   (RValTyPi.valA vty)
        -- Extract PiEdgeVal2 from vty for piEV
        piEV-raw = RValTyPi.edgeV vty
        uniq-v = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vty)
        piEV : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b1 f1
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b1 f1) (Eq-sym (snd uniq-v))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vty) b1 f1) (Eq-sym (fst uniq-v)) piEV-raw)
        vpi' = record
          { domA0 = RValPi.domA0 vpiM
          ; codB0 = RValPi.codB0 vpiM
          ; red   = RValPi.red vpiM
          ; cohG  = RValPi.cohG vpiM
          ; fmG   = fst mem
          ; appV  = downPiAppVal2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appV vpiM)
          ; appE  = downPiAppEq2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appE vpiM)
          }
    in mkSigma vty' vpi'
  downVal2 G M T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode cases
  downVal2 G M T u (SigmaCode b0 f0) Bot          ()
  downVal2 G M T u (SigmaCode b0 f0) UCode        ()
  downVal2 G M T u (SigmaCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downVal2 G M T u (SigmaCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (SigmaCode b0 f0) PropCode     ()
  downVal2 G M T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let vty   = fst src
        vpair = snd src
        fmu'0 = fst (fst mem)
        v2Fst' = downVal2 G (Fst _) (RValSigma.domA vpair) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpair)
        ctf0  = snd ca0
        ctf1  = snd (snd ca1)
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 (RValSigma.cohW1 vpair) (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 (RValSigma.cohW1 vpair)
        ca1_ef = EvalFun-in-UCode f1 u' b1 ctf1 (RValSigma.cohW1 vpair) (fst (snd ca1))
        v2Snd' = downVal2 G (Snd _) (subst1 (RValSigma.codB vpair) (Fst _)) v' (EvalFun f0 u') (EvalFun f1 u')
                   le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpair)
        vty'  = downValTy2 G _ (SigmaCode b0 f0) (SigmaCode b1 f1) le (snd (snd mem)) ca1 vty
        vpair' = record
          { domA   = RValSigma.domA vpair
          ; codB   = RValSigma.codB vpair
          ; red    = RValSigma.red vpair
          ; htFst  = RValSigma.htFst vpair
          ; cohW1  = RValSigma.cohW1 vpair
          ; fmW1   = fmu'0
          ; valFst = v2Fst'
          ; valSnd = v2Snd'
          }
    in mkSigma vty' vpair'
  -- PairCode: all Val2 cases at PairCode = Top
  downVal2 G M T Bot (PairCode x0 y0) a1 le ()
  downVal2 G M T UCode (PairCode x0 y0) a1 le ()
  downVal2 G M T PropCode (PairCode x0 y0) a1 le ()
  downVal2 G M T (FunEl g) (PairCode x0 y0) a1 le ()
  downVal2 G M T (PiCode a' ff) (PairCode x0 y0) a1 le ()
  downVal2 G M T (SigmaCode a' ff) (PairCode x0 y0) a1 le ()
  downVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le ()

  -- downEqVal2 cases
  downEqVal2 G M N T u Bot          a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T u UCode        Bot            ()
  downEqVal2 G M N T u UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T u UCode        (FunEl h)      ()
  downEqVal2 G M N T u UCode        (PiCode b f)   ()
  downEqVal2 G M N T u UCode        (SigmaCode b f) ()
  downEqVal2 G M N T u UCode        (PairCode x y) ()
  downEqVal2 G M N T u UCode        PropCode       ()
  downEqVal2 G M N T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T u PropCode       Bot            ()
  downEqVal2 G M N T u PropCode       UCode          ()
  downEqVal2 G M N T u PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T u PropCode       (FunEl h)      ()
  downEqVal2 G M N T u PropCode       (PiCode b f)   ()
  downEqVal2 G M N T u PropCode       (SigmaCode b f) ()
  downEqVal2 G M N T u PropCode       (PairCode x y) ()
  downEqVal2 G M N T u (PiCode b0 f0) Bot          ()
  downEqVal2 G M N T u (PiCode b0 f0) UCode        ()
  downEqVal2 G M N T u (PiCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T u (PiCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty   = fst src
        vpiM  = fst (snd src)
        vpiN  = fst (snd (snd src))
        epi   = snd (snd (snd src))
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        vtAb1 : ValTy2 G (REqValPi.domA0 epi) b1
        vtAb1 = Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vty))))
                   (RValTyPi.valA vty)
        valM  = mkSigma vty vpiM
        valN  = mkSigma vty vpiN
        valM' = downVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
        valN' = downVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
        -- piEV for downPiAppEqVal2
        uniq-v = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vty)
        piEV-raw = RValTyPi.edgeV vty
        piEV : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b1 f1
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b1 f1) (Eq-sym (snd uniq-v))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vty) b1 f1) (Eq-sym (fst uniq-v)) piEV-raw)
        epi'  = record
          { domA0 = REqValPi.domA0 epi
          ; codB0 = REqValPi.codB0 epi
          ; red   = REqValPi.red epi
          ; cohG  = REqValPi.cohG epi
          ; fmG   = fst mem
          ; appEV = downPiAppEqVal2 G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (REqValPi.cohG epi) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (REqValPi.fmG epi) vtAb1 (REqValPi.appEV epi)
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  downEqVal2 G M N T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode cases
  downEqVal2 G M N T u (SigmaCode b0 f0) Bot          ()
  downEqVal2 G M N T u (SigmaCode b0 f0) UCode        ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let vpairM = fst (snd src)
        vpairN = fst (snd (snd src))
        eqp   = snd (snd (snd src))
        fmu'0 = fst (fst mem)
        ctf0  = snd ca0
        ctf1  = snd (snd ca1)
        cu'   = REqValSigma.cohW1 eqp
        v2FstM' = downVal2 G (Fst M) (RValSigma.domA vpairM) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpairM)
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 cu' (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 cu'
        ca1_ef = EvalFun-in-UCode f1 u' b1 ctf1 cu' (fst (snd ca1))
        v2SndM' = downVal2 G (Snd M) (subst1 (RValSigma.codB vpairM) (Fst M)) v' (EvalFun f0 u') (EvalFun f1 u')
                    le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpairM)
        v2FstN' = downVal2 G (Fst N) (RValSigma.domA vpairN) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpairN)
        v2SndN' = downVal2 G (Snd N) (subst1 (RValSigma.codB vpairN) (Fst N)) v' (EvalFun f0 u') (EvalFun f1 u')
                    le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpairN)
        vty'  = downValTy2 G _ (SigmaCode b0 f0) (SigmaCode b1 f1) le (snd (snd mem)) ca1 (fst src)
        eqFst' = downEqVal2 G (Fst M) (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.eqFst eqp)
        -- Compute val for eqp' separately from the REqValSigma fields
        v2FstM-eq = downVal2 G (Fst M) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.valFstM eqp)
        v2SndM-eq = downVal2 G (Snd M) (subst1 (REqValSigma.codB eqp) (Fst M)) v' (EvalFun f0 u') (EvalFun f1 u')
                      le_ef (snd (fst mem)) ca0_ef ca1_ef (REqValSigma.valSndM eqp)
        v2FstN-eq = downVal2 G (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.valFstN eqp)
        v2SndN-eq = downVal2 G (Snd N) (subst1 (REqValSigma.codB eqp) (Fst N)) v' (EvalFun f0 u') (EvalFun f1 u')
                      le_ef (snd (fst mem)) ca0_ef ca1_ef (REqValSigma.valSndN eqp)
        vpairM' = record
          { domA = RValSigma.domA vpairM ; codB = RValSigma.codB vpairM ; red = RValSigma.red vpairM
          ; htFst = RValSigma.htFst vpairM ; cohW1 = RValSigma.cohW1 vpairM ; fmW1 = fmu'0
          ; valFst = v2FstM' ; valSnd = v2SndM'
          }
        vpairN' = record
          { domA = RValSigma.domA vpairN ; codB = RValSigma.codB vpairN ; red = RValSigma.red vpairN
          ; htFst = RValSigma.htFst vpairN ; cohW1 = RValSigma.cohW1 vpairN ; fmW1 = fmu'0
          ; valFst = v2FstN' ; valSnd = v2SndN'
          }
        eqp'  = record
          { domA    = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM  = REqValSigma.htFstM eqp
          ; cohW1   = cu'
          ; fmW1    = fmu'0
          ; valFstM = v2FstM-eq
          ; valSndM = v2SndM-eq
          ; htFstN  = REqValSigma.htFstN eqp
          ; valFstN = v2FstN-eq
          ; valSndN = v2SndN-eq
          ; eqFst   = eqFst'
          }
    in mkSigma vty' (mkSigma vpairM' (mkSigma vpairN' eqp'))
  -- PairCode: all EqVal2 = Top
  downEqVal2 G M N T Bot (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T UCode (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T PropCode (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (PiCode a' ff) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (SigmaCode a' ff) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le ()

  -- downValTy2 cases
  downValTy2 G M Bot          u1             le fmem cu1 src = tt
  downValTy2 G M UCode        Bot            ()
  downValTy2 G M UCode        UCode          le fmem cu1 src = src
  downValTy2 G M UCode        (FunEl h)      ()
  downValTy2 G M UCode        (PiCode b f)   ()
  downValTy2 G M UCode        (SigmaCode b f) ()
  downValTy2 G M UCode        (PairCode x y) ()
  downValTy2 G M PropCode      Bot            ()
  downValTy2 G M PropCode      UCode          ()
  downValTy2 G M PropCode      PropCode       le fmem cu1 src = src
  downValTy2 G M PropCode      (FunEl h)      ()
  downValTy2 G M PropCode      (PiCode b f)   ()
  downValTy2 G M PropCode      (SigmaCode b f) ()
  downValTy2 G M PropCode      (PairCode x y) ()
  downValTy2 G M (FunEl g)    u1             le ()
  downValTy2 G M (PiCode b0 f0) Bot          ()
  downValTy2 G M (PiCode b0 f0) UCode        ()
  downValTy2 G M (PiCode b0 f0) (FunEl h)    ()
  downValTy2 G M (PiCode b0 f0) (SigmaCode b1 f1) ()
  downValTy2 G M (PiCode b0 f0) (PairCode x y) ()
  downValTy2 G M (PiCode b0 f0) PropCode     ()
  downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
    let fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b1 = RValTyPi.valA src
        vtA-b0 = downValTy2 G (RValTyPi.domA src) b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        piEV0  = transportPiEdgeVal2-sel G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeV src)
        piEE0  = transportPiEdgeEq2-sel G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeE src)
    in record
      { domA   = RValTyPi.domA src
      ; codB   = RValTyPi.codB src
      ; red    = RValTyPi.red src
      ; cohF   = sat0
      ; fmAllU = fmemAll0
      ; htA    = RValTyPi.htA src
      ; htB    = RValTyPi.htB src
      ; valA   = vtA-b0
      ; edgeV  = piEV0
      ; edgeE  = piEE0
      }
  -- SigmaCode downValTy2
  downValTy2 G M (SigmaCode b0 f0) Bot          ()
  downValTy2 G M (SigmaCode b0 f0) UCode        ()
  downValTy2 G M (SigmaCode b0 f0) (FunEl h)    ()
  downValTy2 G M (SigmaCode b0 f0) (PiCode b1 f1) ()
  downValTy2 G M (SigmaCode b0 f0) (PairCode x y) ()
  downValTy2 G M (SigmaCode b0 f0) PropCode     ()
  downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
    let fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b1 = RValTySigma.valA src
        vtA-b0 = downValTy2 G (RValTySigma.domA src) b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        sigEV0 = transportPiEdgeVal2-sel G (RValTySigma.domA src) (RValTySigma.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTySigma.cohF src) (RValTySigma.fmAllU src) vtA-b1 (RValTySigma.edgeV src)
        sigEE0 = transportPiEdgeEq2-sel G (RValTySigma.domA src) (RValTySigma.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTySigma.cohF src) (RValTySigma.fmAllU src) vtA-b1 (RValTySigma.edgeE src)
    in record
      { domA   = RValTySigma.domA src
      ; codB   = RValTySigma.codB src
      ; red    = RValTySigma.red src
      ; cohF   = sat0
      ; fmAllU = fmemAll0
      ; fmBU   = fmem-b0
      ; htA    = RValTySigma.htA src
      ; htB    = RValTySigma.htB src
      ; valA   = vtA-b0
      ; edgeV  = sigEV0
      ; edgeE  = sigEE0
      }
  -- PairCode downValTy2
  downValTy2 G M (PairCode u v) u1 le ()

  -- downEqValTy2 cases
  downEqValTy2 G M N Bot          u1             le fmem cu1 src = tt
  downEqValTy2 G M N UCode        Bot            ()
  downEqValTy2 G M N UCode        UCode          le fmem cu1 src = src
  downEqValTy2 G M N UCode        (FunEl h)      ()
  downEqValTy2 G M N UCode        (PiCode b f)   ()
  downEqValTy2 G M N UCode        (SigmaCode b f) ()
  downEqValTy2 G M N UCode        (PairCode x y) ()
  downEqValTy2 G M N PropCode      Bot            ()
  downEqValTy2 G M N PropCode      UCode          ()
  downEqValTy2 G M N PropCode      PropCode       le fmem cu1 src = src
  downEqValTy2 G M N PropCode      (FunEl h)      ()
  downEqValTy2 G M N PropCode      (PiCode b f)   ()
  downEqValTy2 G M N PropCode      (SigmaCode b f) ()
  downEqValTy2 G M N PropCode      (PairCode x y) ()
  downEqValTy2 G M N (FunEl g)    u1             le ()
  downEqValTy2 G M N (PiCode b0 f0) Bot          ()
  downEqValTy2 G M N (PiCode b0 f0) UCode        ()
  downEqValTy2 G M N (PiCode b0 f0) (FunEl h)    ()
  downEqValTy2 G M N (PiCode b0 f0) (SigmaCode b1 f1) ()
  downEqValTy2 G M N (PiCode b0 f0) (PairCode x y) ()
  downEqValTy2 G M N (PiCode b0 f0) PropCode     ()
  downEqValTy2 G M N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
    let vtyM1  = fst src
        vtyN1  = fst (snd src)
        core   = snd (snd src)
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        -- vtA-b1 from vtyM1
        uniqM  = Red3-unique-Pi (RValTyPi.red vtyM1) (REqValTyPi.redM core)
        eqAMA  = fst uniqM
        vtA-b1 = Eq-transport (\ X -> ValTy2 G X b1) eqAMA (RValTyPi.valA vtyM1)
        eqvty0  = downEqValTy2 G (REqValTyPi.domA core) (REqValTyPi.domA' core) b0 b1 (fst le) fmem-b0 (fst cu1) (REqValTyPi.eqA core)
        piEEqT0 = transportPiEdgeEqTy2-sel G (REqValTyPi.domA core) (REqValTyPi.codB core) (REqValTyPi.codB' core) b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (REqValTyPi.cohF core) (REqValTyPi.fmAllU core) vtA-b1 (REqValTyPi.edgeET core)
        vtyM0  = downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
        core0  = record
          { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
          ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
          ; redM = REqValTyPi.redM core ; redN = REqValTyPi.redN core
          ; cohF = sat0 ; fmAllU = fmemAll0
          ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
          ; eqA = eqvty0 ; edgeET = piEEqT0
          }
    in mkSigma vtyM0 (mkSigma vtyN0 core0)
  -- SigmaCode downEqValTy2
  downEqValTy2 G M N (SigmaCode b0 f0) Bot          ()
  downEqValTy2 G M N (SigmaCode b0 f0) UCode        ()
  downEqValTy2 G M N (SigmaCode b0 f0) (FunEl h)    ()
  downEqValTy2 G M N (SigmaCode b0 f0) (PiCode b1 f1) ()
  downEqValTy2 G M N (SigmaCode b0 f0) (PairCode x y) ()
  downEqValTy2 G M N (SigmaCode b0 f0) PropCode     ()
  downEqValTy2 G M N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
    let vtyM1  = fst src
        vtyN1  = fst (snd src)
        core   = snd (snd src)
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        uniqM  = Red3-unique-Sigma (RValTySigma.red vtyM1) (REqValTySigma.redM core)
        eqAMA  = fst uniqM
        vtA-b1 = Eq-transport (\ X -> ValTy2 G X b1) eqAMA (RValTySigma.valA vtyM1)
        eqvty0  = downEqValTy2 G (REqValTySigma.domA core) (REqValTySigma.domA' core) b0 b1 (fst le) fmem-b0 (fst cu1) (REqValTySigma.eqA core)
        sigEEqT0 = transportPiEdgeEqTy2-sel G (REqValTySigma.domA core) (REqValTySigma.codB core) (REqValTySigma.codB' core) b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (REqValTySigma.cohF core) (REqValTySigma.fmAllU core) vtA-b1 (REqValTySigma.edgeET core)
        vtyM0  = downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyN1
        core0  = record
          { domA = REqValTySigma.domA core ; codB = REqValTySigma.codB core
          ; domA' = REqValTySigma.domA' core ; codB' = REqValTySigma.codB' core
          ; redM = REqValTySigma.redM core ; redN = REqValTySigma.redN core
          ; cohF = sat0 ; fmAllU = fmemAll0
          ; convA = REqValTySigma.convA core ; convB = REqValTySigma.convB core
          ; eqA = eqvty0 ; edgeET = sigEEqT0
          }
    in mkSigma vtyM0 (mkSigma vtyN0 core0)
  -- PairCode downEqValTy2
  downEqValTy2 G M N (PairCode u v) u1 le ()

  ------------------------------------------------------------------
  -- upVal2 / upEqVal2
  ------------------------------------------------------------------

  upVal2 G M T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode        Bot a1 le ()
  upVal2 G M T (FunEl g)    Bot a1 le ()
  upVal2 G M T (PiCode a f) Bot a1 le ()
  upVal2 G M T (SigmaCode a f) Bot a1 le ()
  upVal2 G M T (PairCode u' v') Bot a1 le ()
  upVal2 G M T PropCode     Bot a1 le ()
  upVal2 G M T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (FunEl g')     UCode UCode le ()
  upVal2 G M T PropCode        UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T u UCode Bot          ()
  upVal2 G M T u UCode PropCode     ()
  upVal2 G M T u UCode (FunEl h)    ()
  upVal2 G M T u UCode (PiCode b h) ()
  upVal2 G M T u UCode (SigmaCode b h) ()
  upVal2 G M T u UCode (PairCode x y) ()
  upVal2 G M T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (FunEl g) a1             le ()
  upVal2 G M T PropCode       (FunEl g) a1             le ()
  upVal2 G M T (FunEl g')     (FunEl g) a1             le ()
  upVal2 G M T (PiCode a' f') (FunEl g) a1             le ()
  upVal2 G M T (SigmaCode a' f') (FunEl g) a1          le ()
  upVal2 G M T (PairCode u' v') (FunEl g) a1           le ()
  upVal2 G M T UCode          PropCode a1             le ()
  upVal2 G M T PropCode       PropCode a1             le ()
  upVal2 G M T (FunEl g)      PropCode a1             le ()
  upVal2 G M T (SigmaCode a' f') PropCode a1          le ()
  upVal2 G M T (PairCode u' v') PropCode a1           le ()
  upVal2 G M T Bot            PropCode Bot             ()
  upVal2 G M T Bot            PropCode UCode           ()
  upVal2 G M T Bot            PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            PropCode (FunEl h)       ()
  upVal2 G M T Bot            PropCode (PiCode b1 f1)  ()
  upVal2 G M T Bot            PropCode (SigmaCode b1 f1) ()
  upVal2 G M T Bot            PropCode (PairCode x y)  ()
  upVal2 G M T (PiCode a' f') PropCode Bot             ()
  upVal2 G M T (PiCode a' f') PropCode UCode           ()
  upVal2 G M T (PiCode a' f') PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PiCode a' f') PropCode (FunEl h)       ()
  upVal2 G M T (PiCode a' f') PropCode (PiCode b1 f1)  ()
  upVal2 G M T (PiCode a' f') PropCode (SigmaCode b1 f1) ()
  upVal2 G M T (PiCode a' f') PropCode (PairCode x y)  ()
  upVal2 G M T u (PiCode b0 f0) Bot       ()
  upVal2 G M T u (PiCode b0 f0) UCode     ()
  upVal2 G M T u (PiCode b0 f0) PropCode  ()
  upVal2 G M T u (PiCode b0 f0) (FunEl h) ()
  upVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  upVal2 G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = snd src
        cf0  = snd ca0
        cf1  = snd ca1
        pf0  = snd (snd mem0)
        pf1  = snd (snd mem1)
        b0U  = fst pf0
        b1U  = fst pf1
        allU0 = fst (snd pf0)
        allU1 = fst (snd pf1)
        cb0  = coh-from-aU b0 b0U
        cb1  = coh-from-aU b1 b1U
        -- piEV1 from vta1 (RValTyPi G T b1 f1)
        uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vta1)
        piEV1 : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b1 f1
        piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
        vpi' = record
          { domA0 = RValPi.domA0 vpiM
          ; codB0 = RValPi.codB0 vpiM
          ; red   = RValPi.red vpiM
          ; cohG  = RValPi.cohG vpiM
          ; fmG   = fst mem1
          ; appV  = upPiAppVal2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (RValPi.appV vpiM)
          ; appE  = upPiAppEq2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (RValPi.appE vpiM)
          }
    in mkSigma vta1 vpi'
  upVal2 G M T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode upVal2
  upVal2 G M T u (SigmaCode b0 f0) Bot       ()
  upVal2 G M T u (SigmaCode b0 f0) UCode     ()
  upVal2 G M T u (SigmaCode b0 f0) PropCode  ()
  upVal2 G M T u (SigmaCode b0 f0) (FunEl h) ()
  upVal2 G M T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  upVal2 G M T u (SigmaCode b0 f0) (PairCode x y) ()
  upVal2 G M T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (PiCode a f)   (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (SigmaCode a f) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty   = fst src
        vpair = snd src
        cf0   = snd ca0
        cf1   = snd ca1
        pf0   = snd (snd mem0)
        pf1   = snd (snd mem1)
        b0U   = fst pf0
        b1U   = fst pf1
        cb0   = coh-from-aU b0 b0U
        cb1   = coh-from-aU b1 b1U
        fmu'0 = fst (fst mem0)
        fmu'1 = fst (fst mem1)
        uniq  = Red3-unique-Sigma (RValSigma.red vpair) (RValTySigma.red vta1)
        sigEV1 : SigmaEdgeVal2 G (RValSigma.domA vpair) (RValSigma.codB vpair) b1 f1
        sigEV1 = Eq-transport (\ Y -> SigmaEdgeVal2 G (RValSigma.domA vpair) Y b1 f1) (Eq-sym (snd uniq))
                   (Eq-transport (\ X -> SigmaEdgeVal2 G X (RValTySigma.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTySigma.edgeV vta1))
        ctf0  = snd ca0
        ctf1  = snd ca1
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 (RValSigma.cohW1 vpair) (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 (RValSigma.cohW1 vpair)
        ca1_ef = Coherent-EvalFun f1 u' ctf1 (RValSigma.cohW1 vpair)
        ef1U  = EvalFun-in-UCode f1 u' b1 ctf1 (RValSigma.cohW1 vpair) (fst (snd pf1))
        v2Fst' = upVal2 G (Fst _) (RValSigma.domA vpair) u' b0 b1 (fst le) fmu'0 fmu'1 cb0 cb1 (RValSigma.valFst vpair)
                   (Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst uniq)) (RValTySigma.valA vta1))
        v2Snd' = upVal2 G (Snd _) (subst1 (RValSigma.codB vpair) (Fst _)) v' (EvalFun f0 u') (EvalFun f1 u')
                   le_ef (snd (fst mem0)) (snd (fst mem1)) ca0_ef ca1_ef (RValSigma.valSnd vpair)
                   (let sb = selectionBelow f1 u' ctf1 (RValSigma.cohW1 vpair)
                        u1 = fst sb
                        v1 = fst (snd sb)
                        sel1 = fst (snd (snd sb))
                        le-u1 = fst (snd (snd (snd sb)))
                        eq-v1 = snd (snd (snd (snd sb)))
                        fmu1-b1 = FinMemAllU-Selection b1 sel1 (fst (snd pf1)) ctf1 cb1 b1U
                        fmu-b1 = finMem-upward u' b0 b1 (fst le) cb0 cb1 fmu'0 b1U
                        valFst-u1 = restrictVal2 _ _ (RValSigma.domA vpair) u' u1 b1 le-u1 fmu1-b1 fmu-b1 v2Fst'
                        vty-v1 = sigEV1 u1 v1 sel1 (Fst _) (RValSigma.htFst vpair) valFst-u1
                    in Eq-transport (\ x -> ValTy2 G (subst1 (RValSigma.codB vpair) (Fst _)) x) (Eq-sym eq-v1) vty-v1)
        vpair' = record
          { domA   = RValSigma.domA vpair
          ; codB   = RValSigma.codB vpair
          ; red    = RValSigma.red vpair
          ; htFst  = RValSigma.htFst vpair
          ; cohW1  = RValSigma.cohW1 vpair
          ; fmW1   = fmu'1
          ; valFst = v2Fst'
          ; valSnd = v2Snd'
          }
    in mkSigma vta1 vpair'
  -- PairCode upVal2: FinMem Bot (PairCode x y) = Empty
  upVal2 G M T Bot (PairCode x0 y0) a1 le ()
  upVal2 G M T UCode (PairCode x0 y0) a1 le ()
  upVal2 G M T PropCode (PairCode x0 y0) a1 le ()
  upVal2 G M T (FunEl g) (PairCode x0 y0) a1 le ()
  upVal2 G M T (PiCode a f) (PairCode x0 y0) a1 le ()
  upVal2 G M T (SigmaCode a f) (PairCode x0 y0) a1 le ()
  upVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le ()

  upEqVal2 G M N T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode        Bot a1 le ()
  upEqVal2 G M N T (FunEl g)    Bot a1 le ()
  upEqVal2 G M N T (PiCode a f) Bot a1 le ()
  upEqVal2 G M N T (SigmaCode a f) Bot a1 le ()
  upEqVal2 G M N T (PairCode u' v') Bot a1 le ()
  upEqVal2 G M N T PropCode     Bot a1 le ()
  upEqVal2 G M N T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (FunEl g')     UCode UCode le ()
  upEqVal2 G M N T PropCode        UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T u UCode Bot          ()
  upEqVal2 G M N T u UCode PropCode     ()
  upEqVal2 G M N T u UCode (FunEl h)    ()
  upEqVal2 G M N T u UCode (PiCode b h) ()
  upEqVal2 G M N T u UCode (SigmaCode b h) ()
  upEqVal2 G M N T u UCode (PairCode x y) ()
  upEqVal2 G M N T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (FunEl g) a1             le ()
  upEqVal2 G M N T PropCode       (FunEl g) a1             le ()
  upEqVal2 G M N T (FunEl g')     (FunEl g) a1             le ()
  upEqVal2 G M N T (PiCode a' f') (FunEl g) a1             le ()
  upEqVal2 G M N T (SigmaCode a' f') (FunEl g) a1          le ()
  upEqVal2 G M N T (PairCode u' v') (FunEl g) a1           le ()
  upEqVal2 G M N T UCode          PropCode a1             le ()
  upEqVal2 G M N T PropCode       PropCode a1             le ()
  upEqVal2 G M N T (FunEl g)      PropCode a1             le ()
  upEqVal2 G M N T (SigmaCode a' f') PropCode a1          le ()
  upEqVal2 G M N T (PairCode u' v') PropCode a1           le ()
  upEqVal2 G M N T Bot            PropCode Bot             ()
  upEqVal2 G M N T Bot            PropCode UCode           ()
  upEqVal2 G M N T Bot            PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            PropCode (FunEl h)       ()
  upEqVal2 G M N T Bot            PropCode (PiCode b1 f1)  ()
  upEqVal2 G M N T Bot            PropCode (SigmaCode b1 f1) ()
  upEqVal2 G M N T Bot            PropCode (PairCode x y)  ()
  upEqVal2 G M N T (PiCode a' f') PropCode Bot             ()
  upEqVal2 G M N T (PiCode a' f') PropCode UCode           ()
  upEqVal2 G M N T (PiCode a' f') PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PiCode a' f') PropCode (FunEl h)       ()
  upEqVal2 G M N T (PiCode a' f') PropCode (PiCode b1 f1)  ()
  upEqVal2 G M N T (PiCode a' f') PropCode (SigmaCode b1 f1) ()
  upEqVal2 G M N T (PiCode a' f') PropCode (PairCode x y)  ()
  upEqVal2 G M N T u (PiCode b0 f0) Bot       ()
  upEqVal2 G M N T u (PiCode b0 f0) UCode     ()
  upEqVal2 G M N T u (PiCode b0 f0) PropCode  ()
  upEqVal2 G M N T u (PiCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = fst (snd src)
        vpiN = fst (snd (snd src))
        epi  = snd (snd (snd src))
        cf0   = snd ca0
        cf1   = snd ca1
        pf0   = snd (snd mem0)
        pf1   = snd (snd mem1)
        b0U   = fst pf0
        b1U   = fst pf1
        allU0 = fst (snd pf0)
        allU1 = fst (snd pf1)
        cb0   = coh-from-aU b0 b0U
        cb1   = coh-from-aU b1 b1U
        uniq  = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vta1)
        piEV1 : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b1 f1
        piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
        valM   = mkSigma vty vpiM
        valN   = mkSigma vty vpiN
        valM'  = upVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
        valN'  = upVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
        epi'   = record
          { domA0 = REqValPi.domA0 epi
          ; codB0 = REqValPi.codB0 epi
          ; red   = REqValPi.red epi
          ; cohG  = REqValPi.cohG epi
          ; fmG   = fst mem1
          ; appEV = upPiAppEqVal2 G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 cf1 (REqValPi.cohG epi) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (REqValPi.appEV epi)
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  upEqVal2 G M N T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode upEqVal2
  upEqVal2 G M N T u (SigmaCode b0 f0) Bot       ()
  upEqVal2 G M N T u (SigmaCode b0 f0) UCode     ()
  upEqVal2 G M N T u (SigmaCode b0 f0) PropCode  ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (PiCode a f)   (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (SigmaCode a f) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vpairM = fst (snd src)
        vpairN = fst (snd (snd src))
        eqp    = snd (snd (snd src))
        fmu'0  = fst (fst mem0)
        fmu'1  = fst (fst mem1)
        valM   = mkSigma (fst src) vpairM
        valN   = mkSigma (fst src) vpairN
        valM'  = upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
        valN'  = upVal2 G N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
        -- Compute upVal2 separately for REqValSigma M-fields
        vpairM-eq : RValSigma G M T (PairCode u' v') b0 f0
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq' = upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 (mkSigma (fst src) vpairM-eq) vta1
        vpairN-eq : RValSigma G N T (PairCode u' v') b0 f0
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq' = upVal2 G N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 (mkSigma (fst src) vpairN-eq) vta1
        eqFst' = upEqVal2 G (Fst M) (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 fmu'1 (fst ca0) (fst ca1) (REqValSigma.eqFst eqp)
                   (Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Sigma (REqValSigma.red eqp) (RValTySigma.red vta1))))
                      (RValTySigma.valA vta1))
        eqp'   = record
          { domA    = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM  = RValSigma.htFst (snd valM-eq')
          ; cohW1   = REqValSigma.cohW1 eqp
          ; fmW1    = fmu'1
          ; valFstM = RValSigma.valFst (snd valM-eq')
          ; valSndM = RValSigma.valSnd (snd valM-eq')
          ; htFstN  = RValSigma.htFst (snd valN-eq')
          ; valFstN = RValSigma.valFst (snd valN-eq')
          ; valSndN = RValSigma.valSnd (snd valN-eq')
          ; eqFst   = eqFst'
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') eqp'))
  -- PairCode upEqVal2
  upEqVal2 G M N T Bot (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T UCode (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T PropCode (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (PiCode a f) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (SigmaCode a f) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le ()

  ------------------------------------------------------------------
  -- downPiAppVal2 / downPiAppEq2 / downPiAppEqVal2
  ------------------------------------------------------------------

  downPiAppVal2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppVal2 G M A0 B0 b1 f1 g ->
    PiAppVal2 G M A0 B0 b0 f0 g
  downPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pav
    = \ u v sel N htN valN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            lef0  = fst le
            lef1  = snd le
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
            val-b1 = upVal2 _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 valN vtAb1
            body  = pav u v sel N htN val-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  downPiAppEq2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppEq2 G M A0 B0 b1 f1 g ->
    PiAppEq2 G M A0 B0 b0 f0 g
  downPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pae
    = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            lef0  = fst le
            lef1  = snd le
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
            eqN-b1 = upEqVal2 _ _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 eqN vtAb1
            body  = pae u v sel N1 N2 htN1 htN2 cvN eqN-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  downPiAppEqVal2 : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppEqVal2 G M N A0 B0 b1 f1 g ->
    PiAppEqVal2 G M N A0 B0 b0 f0 g
  downPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 paev
    = \ u v sel P htP valP ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            lef0  = fst le
            lef1  = snd le
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
            valP-b1 = upVal2 _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 valP vtAb1
            body  = paev u v sel P htP valP-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  ------------------------------------------------------------------
  -- upPiAppVal2 / upPiAppEq2 / upPiAppEqVal2
  ------------------------------------------------------------------

  upPiAppVal2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppVal2 G M A0 B0 b0 f0 g ->
    PiAppVal2 G M A0 B0 b1 f1 g
  upPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pav
    = \ u v sel N htN valN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            valN-b0 = downVal2 _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U valN
            body  = pav u v sel N htN valN-b0
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            c-ef1 = Coherent-EvalFun f1 u cf1 cu
            fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            valN-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valN
            vty-v1  = piEV1 u1 v1 sel1 N htN valN-u1
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-v1) vty-v1
        in upVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  upPiAppEq2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppEq2 G M A0 B0 b0 f0 g ->
    PiAppEq2 G M A0 B0 b1 f1 g
  upPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pae
    = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            eqN-b0  = downEqVal2 _ _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U eqN
            body    = pae u v sel N1 N2 htN1 htN2 cvN eqN-b0
            le-f    = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0   = Coherent-EvalFun f0 u cf0 cu
            c-ef1   = Coherent-EvalFun f1 u cf1 cu
            fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
            ef1U    = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            valN1-b1 = Val2-from-EqVal2-first u b1 eqN
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            valN1-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valN1-b1
            vty-v1  = piEV1 u1 v1 sel1 N1 htN1 valN1-u1
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  upPiAppEqVal2 : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppEqVal2 G M N A0 B0 b0 f0 g ->
    PiAppEqVal2 G M N A0 B0 b1 f1 g
  upPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 paev
    = \ u v sel P htP valP ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            valP-b0 = downVal2 _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U valP
            body    = paev u v sel P htP valP-b0
            le-f    = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0   = Coherent-EvalFun f0 u cf0 cu
            c-ef1   = Coherent-EvalFun f1 u cf1 cu
            fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
            ef1U    = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            valP-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valP
            vty-v1  = piEV1 u1 v1 sel1 P htP valP-u1
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  ------------------------------------------------------------------
  -- transportPiEdgeVal2-sel / transportPiEdgeEq2-sel / transportPiEdgeEqTy2-sel
  ------------------------------------------------------------------

  transportPiEdgeVal2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeVal2 G A B b1 f1 ->
    PiEdgeVal2 G A B b0 f0
  transportPiEdgeVal2-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pev1
    = \ u v sel N htN valN ->
        let cu    = Coherent-Selection sel cf0
            fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
            fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
            valN-b1 = upVal2 _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 valN vtAb1
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            valN-u1 = restrictVal2 _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 valN-b1
            vt-v1   = pev1 u1 v1 sel1 N htN valN-u1
            vt-ef   = Eq-transport (\ x -> ValTy2 G (subst1 B N) x) (Eq-sym eq-v1) vt-v1
            le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downValTy2 G (subst1 B N) v v1 le-v-v1 fmem-v-U v1U vt-v1

  transportPiEdgeEq2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeEq2 G A B b1 f1 ->
    PiEdgeEq2 G A B b0 f0
  transportPiEdgeEq2-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pee1
    = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
        let cu    = Coherent-Selection sel cf0
            fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
            fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
            eqN-b1  = upEqVal2 _ _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 eqN vtAb1
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            eqN-u1  = restrictEqVal2 _ _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 eqN-b1
            eqt-v1  = pee1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqN-u1
            le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downEqValTy2 G (subst1 B N1) (subst1 B N2) v v1 le-v-v1 fmem-v-U v1U eqt-v1

  transportPiEdgeEqTy2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeEqTy2 G A B B' b1 f1 ->
    PiEdgeEqTy2 G A B B' b0 f0
  transportPiEdgeEqTy2-sel G A B B' b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pet1
    = \ u v sel P htP valP ->
        let cu    = Coherent-Selection sel cf0
            fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
            fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
            valP-b1 = upVal2 _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 valP vtAb1
            sb1   = selectionBelow f1 u cf1 cu
            u1    = fst sb1
            v1    = fst (snd sb1)
            sel1  = fst (snd (snd sb1))
            le-u1 = fst (snd (snd (snd sb1)))
            eq-v1 = snd (snd (snd (snd sb1)))
            fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
            valP-u1 = restrictVal2 _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 valP-b1
            eqt-v1  = pet1 u1 v1 sel1 P htP valP-u1
            le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downEqValTy2 G (subst1 B P) (subst1 B' P) v v1 le-v-v1 fmem-v-U v1U eqt-v1

  ------------------------------------------------------------------
  -- restrictVal2 / restrictEqVal2
  ------------------------------------------------------------------

  restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    Val2 G M T u a -> Val2 G M T u' a

  restrictVal2 G M T u u' Bot          le mem fmu src = src
  restrictVal2 G M T Bot Bot UCode        le mem fmu src = src
  restrictVal2 G M T Bot UCode UCode      ()
  restrictVal2 G M T Bot (FunEl _) UCode  ()
  restrictVal2 G M T Bot (PiCode _ _) UCode ()
  restrictVal2 G M T UCode Bot UCode        le mem fmu src = tt
  restrictVal2 G M T UCode UCode UCode      le mem fmu src = src
  restrictVal2 G M T UCode (FunEl _) UCode  ()
  restrictVal2 G M T UCode (PiCode _ _) UCode ()
  restrictVal2 G M T (FunEl g) Bot UCode    le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode UCode  ()
  restrictVal2 G M T (FunEl g) (FunEl g') UCode le mem fmu src =
    downValTy2 G M (FunEl g') (FunEl g) le mem fmu src
  restrictVal2 G M T (FunEl g) (PiCode _ _) UCode ()
  restrictVal2 G M T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a' f') UCode UCode ()
  restrictVal2 G M T (PiCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu src =
    mkSigma (fst src) (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu (snd src))
  restrictVal2 G M T PropCode Bot UCode le mem fmu src = tt
  restrictVal2 G M T PropCode UCode UCode ()
  restrictVal2 G M T PropCode PropCode UCode le mem fmu src = src
  restrictVal2 G M T PropCode (FunEl _) UCode ()
  restrictVal2 G M T PropCode (PiCode _ _) UCode ()
  restrictVal2 G M T Bot PropCode UCode ()
  restrictVal2 G M T UCode PropCode UCode ()
  restrictVal2 G M T (FunEl g) PropCode UCode ()
  restrictVal2 G M T (PiCode a' f') PropCode UCode ()
  restrictVal2 G M T Bot Bot PropCode le mem fmu src = src
  restrictVal2 G M T Bot UCode PropCode le ()
  restrictVal2 G M T Bot PropCode PropCode ()
  restrictVal2 G M T Bot (FunEl _) PropCode le ()
  restrictVal2 G M T Bot (PiCode _ _) PropCode ()
  restrictVal2 G M T UCode u' PropCode le mem ()
  restrictVal2 G M T PropCode u' PropCode le mem ()
  restrictVal2 G M T (FunEl _) u' PropCode le mem ()
  restrictVal2 G M T (PiCode a' f') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a' f') UCode PropCode le ()
  restrictVal2 G M T (PiCode a' f') PropCode PropCode ()
  restrictVal2 G M T (PiCode a' f') (FunEl _) PropCode le ()
  restrictVal2 G M T (PiCode a' f') (PiCode a2 f2) PropCode le mem fmu src =
    mkSigma (fst src) (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) (snd src))
  restrictVal2 G M T u u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T Bot UCode          (PiCode b f) le ()
  restrictVal2 G M T Bot (FunEl g')     (PiCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T UCode (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode          (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
    let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
    in mkSigma (fst src)
         (restrictVal2-PiCode G M T g g' b f (snd (snd aU)) (coh-from-aU b (fst aU))
           (fst (snd aU)) (fst aU) le (mkSigma (fst mem) (fst (snd mem))) (fst src) (snd src))
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  -- SigmaCode restrictVal2
  restrictVal2 G M T Bot PropCode (SigmaCode b f) ()
  restrictVal2 G M T UCode PropCode (SigmaCode b f) ()
  restrictVal2 G M T (FunEl g) PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a' f') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a' f') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u' v') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a' f') UCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (PiCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (SigmaCode a2 f2) UCode le mem fmu src =
    mkSigma (fst src) (downValTy2 G M (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu (snd src))
  restrictVal2 G M T (SigmaCode a' f') (PairCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') PropCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a' f') UCode PropCode le ()
  restrictVal2 G M T (SigmaCode a' f') PropCode PropCode ()
  restrictVal2 G M T (SigmaCode a' f') (FunEl _) PropCode le ()
  restrictVal2 G M T (SigmaCode a' f') (PiCode a2 f2) PropCode le mem ()
  restrictVal2 G M T (SigmaCode a' f') (SigmaCode a2 f2) PropCode le mem ()
  restrictVal2 G M T (SigmaCode a' f') (PairCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode UCode ()
  restrictVal2 G M T (PairCode u' v') (FunEl _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PiCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictVal2 G M T (PairCode u' v') PropCode UCode ()
  restrictVal2 G M T (PairCode u' v') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode PropCode le ()
  restrictVal2 G M T (PairCode u' v') PropCode PropCode ()
  restrictVal2 G M T (PairCode u' v') (FunEl _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (PiCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (PairCode _ _) PropCode le mem ()
  restrictVal2 G M T Bot Bot (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T Bot UCode (SigmaCode b f) le ()
  restrictVal2 G M T Bot (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T UCode Bot (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T UCode UCode (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T UCode (FunEl g') (SigmaCode b f) le mem ()
  restrictVal2 G M T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T UCode (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T UCode (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictVal2 G M T PropCode u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (FunEl g) Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (FunEl g') (SigmaCode b f) le mem ()
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (PairCode u' v') Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (FunEl g') (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let fmu2b = fst (fst mem)
        vpair = snd src
        cfSrc = RValTySigma.cohF (fst src)
        allU  = RValTySigma.fmAllU (fst src)
        cu2   = FinMem-Coherent u2 b fmu2b
        cu'   = RValSigma.cohW1 vpair
        -- Restrict Fst: u' -> u2 at b
        v2Fst' = restrictVal2 _ _ (RValSigma.domA vpair) u' u2 b (fst le) fmu2b (RValSigma.fmW1 vpair) (RValSigma.valFst vpair)
        le_ef = EvalFun-mon-arg f u2 u' (fst le) cfSrc cu2 cu'
        c_ef_u2 = Coherent-EvalFun f u2 cfSrc cu2
        c_ef_u' = Coherent-EvalFun f u' cfSrc cu'
        ef_u'_U = EvalFun-in-UCode f u' b cfSrc cu' allU
        ef_u2_U = EvalFun-in-UCode f u2 b cfSrc cu2 allU
        fmv'efu' = snd (fst fmu)
        fmv2efu2 = snd (fst mem)
        aU = snd (snd fmu)
        bU = fst aU
        fmv2efu' = finMem-upward v2 (EvalFun f u2) (EvalFun f u') le_ef c_ef_u2 c_ef_u' fmv2efu2 ef_u'_U
        -- Get ValTy2 at ef u' from the Sigma edge
        sb = selectionBelow f u' cfSrc cu'
        u1 = fst sb
        v1 = fst (snd sb)
        sel1 = fst (snd (snd sb))
        le-u1 = fst (snd (snd (snd sb)))
        eq-v1 = snd (snd (snd (snd sb)))
        fmu1-b = FinMemAllU-Selection b sel1 allU cfSrc (coh-from-aU b bU) bU
        uniqS = Red3-unique-Sigma (RValSigma.red vpair) (RValTySigma.red (fst src))
        eqAS = fst uniqS
        valFst-u1 = restrictVal2 _ _ (RValSigma.domA vpair) u' u1 b le-u1 fmu1-b (RValSigma.fmW1 vpair) (RValSigma.valFst vpair)
        htFst-S = Eq-transport (\ X -> HasType _ _ X) eqAS (RValSigma.htFst vpair)
        valFst-u1-S = Eq-transport (\ X -> Val2 _ _ X u1 b) eqAS valFst-u1
        vty-v1 = RValTySigma.edgeV (fst src) u1 v1 sel1 (Fst _) htFst-S valFst-u1-S
        vty-v1' = Eq-transport (\ X -> ValTy2 _ (subst1 X (Fst _)) v1) (Eq-sym (snd uniqS)) vty-v1
        vty-efu' = Eq-transport (\ x -> ValTy2 _ (subst1 (RValSigma.codB vpair) (Fst _)) x) (Eq-sym eq-v1) vty-v1'
        -- Step: restrict v'->v2 at ef u', then downVal2 to ef u2
        sndRestricted = restrictVal2 _ _ (subst1 (RValSigma.codB vpair) (Fst _)) v' v2 (EvalFun f u') (snd le)
                    fmv2efu' fmv'efu' (RValSigma.valSnd vpair)
        sndDown = downVal2 _ _ (subst1 (RValSigma.codB vpair) (Fst _)) v2 (EvalFun f u2) (EvalFun f u') le_ef fmv2efu2 c_ef_u2 ef_u'_U sndRestricted
        vpair' = record
          { domA = RValSigma.domA vpair ; codB = RValSigma.codB vpair ; red = RValSigma.red vpair
          ; htFst = RValSigma.htFst vpair ; cohW1 = cu2 ; fmW1 = fmu2b
          ; valFst = v2Fst' ; valSnd = sndDown
          }
    in mkSigma (fst src) vpair'
  -- PairCode restrictVal2
  restrictVal2 G M T u u' (PairCode x y) le mem fmu src = src

  restrictEqVal2 G M N T u u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T Bot Bot UCode        le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode UCode     ()
  restrictEqVal2 G M N T Bot (FunEl _) UCode ()
  restrictEqVal2 G M N T Bot (PiCode _ _) UCode ()
  restrictEqVal2 G M N T UCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T UCode UCode UCode le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl _) UCode ()
  restrictEqVal2 G M N T UCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (FunEl g) Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode UCode ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') UCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a' f') UCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu (mkSigma vtA (mkSigma vtM (mkSigma vtN eqvt))) =
    mkSigma vtA
      (mkSigma (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu vtM)
        (mkSigma (downValTy2 G N (PiCode a2 f2) (PiCode a' f') le mem fmu vtN)
          (downEqValTy2 G M N (PiCode a2 f2) (PiCode a' f') le mem fmu eqvt)))
  restrictEqVal2 G M N T PropCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T PropCode UCode UCode ()
  restrictEqVal2 G M N T PropCode PropCode UCode le mem fmu src = src
  restrictEqVal2 G M N T PropCode (FunEl _) UCode ()
  restrictEqVal2 G M N T PropCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T Bot PropCode UCode ()
  restrictEqVal2 G M N T UCode PropCode UCode ()
  restrictEqVal2 G M N T (FunEl g) PropCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') PropCode UCode ()
  restrictEqVal2 G M N T Bot Bot PropCode le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode PropCode le ()
  restrictEqVal2 G M N T Bot PropCode PropCode ()
  restrictEqVal2 G M N T Bot (FunEl _) PropCode ()
  restrictEqVal2 G M N T Bot (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T UCode u' PropCode le mem ()
  restrictEqVal2 G M N T PropCode u' PropCode le mem ()
  restrictEqVal2 G M N T (FunEl _) u' PropCode le mem ()
  restrictEqVal2 G M N T (PiCode a' f') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a' f') UCode PropCode le ()
  restrictEqVal2 G M N T (PiCode a' f') PropCode PropCode ()
  restrictEqVal2 G M N T (PiCode a' f') (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (PiCode a' f') (PiCode a2 f2) PropCode le mem fmu (mkSigma vtA (mkSigma vtM (mkSigma vtN eqvt))) =
    mkSigma vtA
      (mkSigma (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) vtM)
        (mkSigma (downValTy2 G N (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) vtN)
          (downEqValTy2 G M N (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) eqvt)))
  restrictEqVal2 G M N T u u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g')     (PiCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
    let aU    = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
        valM  = mkSigma (fst src) (fst (snd src))
        valN  = mkSigma (fst src) (fst (snd (snd src)))
        epi   = snd (snd (snd src))
        valM' = restrictVal2 G M T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valM
        valN' = restrictVal2 G N T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valN
        epi'  = restrictEqVal2-PiCode G M N T g g' b f (snd (snd aU)) (coh-from-aU b (fst aU))
                  (fst (snd aU)) (fst aU) le (mkSigma (fst mem) (fst (snd mem))) (fst src) epi
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  restrictEqVal2 G M N T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  -- SigmaCode restrictEqVal2
  restrictEqVal2 G M N T (SigmaCode a' f') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode a' f') UCode UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (FunEl _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (SigmaCode a2 f2) UCode le mem fmu (mkSigma vtA (mkSigma vtM (mkSigma vtN eqvt))) =
    mkSigma vtA
      (mkSigma (downValTy2 G M (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu vtM)
        (mkSigma (downValTy2 G N (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu vtN)
          (downEqValTy2 G M N (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu eqvt)))
  restrictEqVal2 G M N T (SigmaCode a' f') (PairCode _ _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') PropCode UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode a' f') UCode PropCode le ()
  restrictEqVal2 G M N T (SigmaCode a' f') PropCode PropCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PiCode a2 f2) PropCode le mem ()
  restrictEqVal2 G M N T (SigmaCode a' f') (SigmaCode a2 f2) PropCode le mem ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PairCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictEqVal2 G M N T (PairCode u' v') PropCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode PropCode le ()
  restrictEqVal2 G M N T (PairCode u' v') PropCode PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode _ _) PropCode le mem ()
  restrictEqVal2 G M N T Bot Bot (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode Bot (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode UCode (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl g') (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T PropCode u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (FunEl g) Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (PairCode u' v') Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl g') (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let valM  = Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b f) src
        valN  = Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b f) src
        valM' = restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu valM
        valN' = restrictVal2 G N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu valN
        eqp   = snd (snd (snd src))
        fmu'0 = fst (fst mem)
        eqFst' = restrictEqVal2 _ _ _ (REqValSigma.domA eqp) u' u2 b (fst le) fmu'0 (REqValSigma.fmW1 eqp) (REqValSigma.eqFst eqp)
        -- Compute restrictVal2 separately for REqValSigma M/N fields
        vpairM-eq : RValSigma G M T (PairCode u' v') b f
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq' = restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu (mkSigma (fst src) vpairM-eq)
        vpairN-eq : RValSigma G N T (PairCode u' v') b f
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq' = restrictVal2 G N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu (mkSigma (fst src) vpairN-eq)
        eqp'  = record
          { domA   = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM = RValSigma.htFst (snd valM-eq')
          ; cohW1  = FinMem-Coherent u2 b fmu'0
          ; fmW1   = fmu'0
          ; valFstM = RValSigma.valFst (snd valM-eq')
          ; valSndM = RValSigma.valSnd (snd valM-eq')
          ; htFstN = RValSigma.htFst (snd valN-eq')
          ; valFstN = RValSigma.valFst (snd valN-eq')
          ; valSndN = RValSigma.valSnd (snd valN-eq')
          ; eqFst  = eqFst'
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') eqp'))
  -- PairCode restrictEqVal2
  restrictEqVal2 G M N T u u' (PairCode x y) le mem fmu src = src

  ------------------------------------------------------------------
  -- restrictPiAppVal2-sel / restrictPiAppEq2-sel / restrictPiAppEqVal2-sel
  ------------------------------------------------------------------

  restrictPiAppVal2-sel : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppVal2 G M A0 B0 b f g -> PiAppVal2 G M A0 B0 b f g'
  restrictPiAppVal2-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pav
    u' v' sel' N htN valN =
    let ctg      = cft-from-cf g cg
        ctg'     = cft-from-cf g' cg'
        cu'      = Coherent-Selection sel' ctg'
        fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
        sb       = selectionBelow g u' ctg cu'
        u_g      = fst sb
        v_g      = fst (snd sb)
        sel_g    = fst (snd (snd sb))
        le-ug    = fst (snd (snd (snd sb)))
        eq-vg    = snd (snd (snd (snd sb)))
        cu_g     = Coherent-Selection sel_g ctg
        fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
        valN-ug  = restrictVal2 _ _ A0 u' u_g b le-ug fmu_g fmu'-b valN
        body     = pav u_g v_g sel_g N htN valN-ug
        le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
        c-efug   = Coherent-EvalFun f u_g cf cu_g
        c-efu'   = Coherent-EvalFun f u' cf cu'
        fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
        efuU'    = EvalFun-in-UCode f u' b cf cu' allU
        fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                          le-ef c-efug c-efu' fmem-vg-efug efuU'
        sb-f     = selectionBelow f u' cf cu'
        u_f      = fst sb-f
        v_f      = fst (snd sb-f)
        sel_f    = fst (snd (snd sb-f))
        le-uf    = fst (snd (snd (snd sb-f)))
        eq-ef    = snd (snd (snd (snd sb-f)))
        fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
        valN-uf  = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valN
        vty-vf   = piEV u_f v_f sel_f N htN valN-uf
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-ef) vty-vf
        body2    = upVal2 _ _ (subst1 B0 N) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictVal2 _ _ (subst1 B0 N) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  restrictPiAppEq2-sel : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppEq2 G M A0 B0 b f g -> PiAppEq2 G M A0 B0 b f g'
  restrictPiAppEq2-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pae
    u' v' sel' N1 N2 htN1 htN2 cvN eqN =
    let ctg      = cft-from-cf g cg
        ctg'     = cft-from-cf g' cg'
        cu'      = Coherent-Selection sel' ctg'
        fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
        sb       = selectionBelow g u' ctg cu'
        u_g      = fst sb
        v_g      = fst (snd sb)
        sel_g    = fst (snd (snd sb))
        le-ug    = fst (snd (snd (snd sb)))
        eq-vg    = snd (snd (snd (snd sb)))
        cu_g     = Coherent-Selection sel_g ctg
        fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
        eqN-ug   = restrictEqVal2 _ _ _ A0 u' u_g b le-ug fmu_g fmu'-b eqN
        body     = pae u_g v_g sel_g N1 N2 htN1 htN2 cvN eqN-ug
        le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
        c-efug   = Coherent-EvalFun f u_g cf cu_g
        c-efu'   = Coherent-EvalFun f u' cf cu'
        fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
        efuU'    = EvalFun-in-UCode f u' b cf cu' allU
        fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                          le-ef c-efug c-efu' fmem-vg-efug efuU'
        valN1-b  = Val2-from-EqVal2-first u' b eqN
        sb-f     = selectionBelow f u' cf cu'
        u_f      = fst sb-f
        v_f      = fst (snd sb-f)
        sel_f    = fst (snd (snd sb-f))
        le-uf    = fst (snd (snd (snd sb-f)))
        eq-ef    = snd (snd (snd (snd sb-f)))
        fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
        valN1-uf = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valN1-b
        vty-vf   = piEV u_f v_f sel_f N1 htN1 valN1-uf
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 N1) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictEqVal2 _ _ _ (subst1 B0 N1) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  restrictPiAppEqVal2-sel : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppEqVal2 G M N A0 B0 b f g -> PiAppEqVal2 G M N A0 B0 b f g'
  restrictPiAppEqVal2-sel G M N A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV paev
    u' v' sel' P htP valP =
    let ctg      = cft-from-cf g cg
        ctg'     = cft-from-cf g' cg'
        cu'      = Coherent-Selection sel' ctg'
        fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
        sb       = selectionBelow g u' ctg cu'
        u_g      = fst sb
        v_g      = fst (snd sb)
        sel_g    = fst (snd (snd sb))
        le-ug    = fst (snd (snd (snd sb)))
        eq-vg    = snd (snd (snd (snd sb)))
        cu_g     = Coherent-Selection sel_g ctg
        fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
        valP-ug  = restrictVal2 _ _ A0 u' u_g b le-ug fmu_g fmu'-b valP
        body     = paev u_g v_g sel_g P htP valP-ug
        le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
        c-efug   = Coherent-EvalFun f u_g cf cu_g
        c-efu'   = Coherent-EvalFun f u' cf cu'
        fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
        efuU'    = EvalFun-in-UCode f u' b cf cu' allU
        fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                          le-ef c-efug c-efu' fmem-vg-efug efuU'
        sb-f     = selectionBelow f u' cf cu'
        u_f      = fst sb-f
        v_f      = fst (snd sb-f)
        sel_f    = fst (snd (snd sb-f))
        le-uf    = fst (snd (snd (snd sb-f)))
        eq-ef    = snd (snd (snd (snd sb-f)))
        fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
        valP-uf  = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valP
        vty-vf   = piEV u_f v_f sel_f P htP valP-uf
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 P) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictEqVal2 _ _ _ (subst1 B0 P) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  ------------------------------------------------------------------
  -- restrictVal2-PiCode / restrictEqVal2-PiCode
  ------------------------------------------------------------------

  restrictVal2-PiCode : {n : Nat} (G : Ctx n) (M T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    RValPi G M T g b f ->
    RValPi G M T g' b f
  restrictVal2-PiCode G M T g g' b f cf cb allU bU le mem' vtyT vpiM =
    let cg'  = snd mem'
        fmg' = fst mem'
        -- Derive PiEdgeVal2 from vtyT (RValTyPi)
        uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vtyT)
        piEV : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
    in record
      { domA0 = RValPi.domA0 vpiM
      ; codB0 = RValPi.codB0 vpiM
      ; red   = RValPi.red vpiM
      ; cohG  = cg'
      ; fmG   = fmg'
      ; appV  = restrictPiAppVal2-sel G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                  bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appV vpiM)
      ; appE  = restrictPiAppEq2-sel G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                  bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appE vpiM)
      }

  restrictEqVal2-PiCode : {n : Nat} (G : Ctx n) (M N T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    REqValPi G M N T g b f ->
    REqValPi G M N T g' b f
  restrictEqVal2-PiCode G M N T g g' b f cf cb allU bU le mem' vtyT epi =
    let cg'  = snd mem'
        fmg' = fst mem'
        -- Derive PiEdgeVal2 from vtyT (RValTyPi)
        uniq = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vtyT)
        piEV : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
    in record
      { domA0 = REqValPi.domA0 epi
      ; codB0 = REqValPi.codB0 epi
      ; red   = REqValPi.red epi
      ; cohG  = cg'
      ; fmG   = fmg'
      ; appEV = restrictPiAppEqVal2-sel G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f g g' cf (REqValPi.cohG epi) cg' cb allU
                  bU le fmg' (REqValPi.fmG epi) piEV (REqValPi.appEV epi)
      }
