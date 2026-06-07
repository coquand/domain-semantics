{-# OPTIONS --without-K #-}
module SigmaProp.Validity5SymTrans where
open import SigmaProp.Validity5Fwd public

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
-- EqValTy2-sym, EqValTy2-trans, EqVal2-sym, EqVal2-trans
--
-- Mechanical port from Validity4.agda lines 626-1054.
-- Renames: RValPair → RValSigma, REqValPair → REqValSigma,
--          .cohU → .cohW1, .fmU → .fmW1
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  ------------------------------------------------------------------
  -- EqValTy2-trans
  ------------------------------------------------------------------

  EqValTy2-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
    (u : FinEl) -> Coherent u ->
    EqValTy2 G A B u -> EqValTy2 G B C u -> EqValTy2 G A C u
  EqValTy2-trans Bot cu tt tt = tt
  EqValTy2-trans UCode cu eqAB eqBC = mkSigma (fst eqAB) (snd eqBC)
  EqValTy2-trans PropCode cu eqAB eqBC = mkSigma (fst eqAB) (snd eqBC)
  EqValTy2-trans (FunEl g) cu tt tt = tt
  EqValTy2-trans (PairCode u v) cu tt tt = tt
  EqValTy2-trans (PiCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = REqValTyPi.domA coreAB
        B0    = REqValTyPi.codB coreAB
        A0'   = REqValTyPi.domA' coreAB
        B0'   = REqValTyPi.codB' coreAB
        rA    = REqValTyPi.redM coreAB
        rB1   = REqValTyPi.redN coreAB
        cf1   = REqValTyPi.cohF coreAB
        fmU1  = REqValTyPi.fmAllU coreAB
        convAA_AB = REqValTyPi.convA coreAB
        convBB_AB = REqValTyPi.convB coreAB
        eqDomAB = REqValTyPi.eqA coreAB
        petAB   = REqValTyPi.edgeET coreAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = REqValTyPi.domA coreBC
        B1    = REqValTyPi.codB coreBC
        A1'   = REqValTyPi.domA' coreBC
        B1'   = REqValTyPi.codB' coreBC
        rB2   = REqValTyPi.redM coreBC
        rC    = REqValTyPi.redN coreBC
        cf2   = REqValTyPi.cohF coreBC
        fmU2  = REqValTyPi.fmAllU coreBC
        convAA_BC = REqValTyPi.convA coreBC
        convBB_BC = REqValTyPi.convB coreBC
        eqDomBC = REqValTyPi.eqA coreBC
        petBC   = REqValTyPi.edgeET coreBC
        uniq = Red3-unique-Pi rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        -- htA0' needed early for petAC
        redB1-vty-e = RValTyPi.red vtyB1
        uniqB1-dom-e = Red3-unique-Pi redB1-vty-e rB1
        htA0'-raw-e = RValTyPi.htA vtyB1
        htA0'-e = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        petAC : PiEdgeEqTy2 _ A0 B0 B1' b f
        petAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = petAB u' v' sel P htP valP
              eqt2 = petBC u' v' sel P htP-A1 valP-A1
              eqt2' = Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        -- convAA_trans
        convAA_BC' = Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        -- convBB_trans
        convBB_BC-transported = Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = RValTyPi.red vtyA
        uniqA-dom = Red3-unique-Pi redA-vty rA
        htA0-raw = RValTyPi.htA vtyA
        htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = RValTyPi.red vtyB1
        uniqB1-dom = Red3-unique-Pi redB1-vty rB1
        htA0'-raw = RValTyPi.htA vtyB1
        htA0' = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = record
          { domA = A0 ; codB = B0 ; domA' = A1' ; codB' = B1'
          ; redM = rA ; redN = rC ; cohF = cf1 ; fmAllU = fmU1
          ; convA = convAA_AC ; convB = convBB_AC
          ; eqA = eqDomAC ; edgeET = petAC
          }
    in mkSigma vtyA (mkSigma vtyC resultCore)
  EqValTy2-trans (SigmaCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = REqValTySigma.domA coreAB
        B0    = REqValTySigma.codB coreAB
        A0'   = REqValTySigma.domA' coreAB
        B0'   = REqValTySigma.codB' coreAB
        rA    = REqValTySigma.redM coreAB
        rB1   = REqValTySigma.redN coreAB
        cf1   = REqValTySigma.cohF coreAB
        fmU1  = REqValTySigma.fmAllU coreAB
        convAA_AB = REqValTySigma.convA coreAB
        convBB_AB = REqValTySigma.convB coreAB
        eqDomAB = REqValTySigma.eqA coreAB
        petAB   = REqValTySigma.edgeET coreAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = REqValTySigma.domA coreBC
        B1    = REqValTySigma.codB coreBC
        A1'   = REqValTySigma.domA' coreBC
        B1'   = REqValTySigma.codB' coreBC
        rB2   = REqValTySigma.redM coreBC
        rC    = REqValTySigma.redN coreBC
        cf2   = REqValTySigma.cohF coreBC
        fmU2  = REqValTySigma.fmAllU coreBC
        convAA_BC = REqValTySigma.convA coreBC
        convBB_BC = REqValTySigma.convB coreBC
        eqDomBC = REqValTySigma.eqA coreBC
        petBC   = REqValTySigma.edgeET coreBC
        uniq = Red3-unique-Sigma rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        redB1-vty-e = RValTySigma.red vtyB1
        uniqB1-dom-e = Red3-unique-Sigma redB1-vty-e rB1
        htA0'-raw-e = RValTySigma.htA vtyB1
        htA0'-e = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        petAC : SigmaEdgeEqTy2 _ A0 B0 B1' b f
        petAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = petAB u' v' sel P htP valP
              eqt2 = petBC u' v' sel P htP-A1 valP-A1
              eqt2' = Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        convAA_BC' = Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        convBB_BC-transported = Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = RValTySigma.red vtyA
        uniqA-dom = Red3-unique-Sigma redA-vty rA
        htA0-raw = RValTySigma.htA vtyA
        htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = RValTySigma.red vtyB1
        uniqB1-dom = Red3-unique-Sigma redB1-vty rB1
        htA0'-raw = RValTySigma.htA vtyB1
        htA0' = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = record
          { domA = A0 ; codB = B0 ; domA' = A1' ; codB' = B1'
          ; redM = rA ; redN = rC ; cohF = cf1 ; fmAllU = fmU1
          ; convA = convAA_AC ; convB = convBB_AC
          ; eqA = eqDomAC ; edgeET = petAC
          }
    in mkSigma vtyA (mkSigma vtyC resultCore)

  ------------------------------------------------------------------
  -- EqVal2-sym
  ------------------------------------------------------------------

  EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M N A u a -> EqVal2 G N M A u a
  EqVal2-sym u Bot cu ca tt = tt
  EqVal2-sym Bot UCode cu ca tt = tt
  EqVal2-sym UCode UCode cu ca ev =
    mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (EqValTy2-sym UCode cu (snd (snd (snd ev))))))
  EqVal2-sym (FunEl g) UCode cu ca ev = tt
  EqVal2-sym (PiCode a' f') UCode cu ca ev =
    mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (EqValTy2-sym (PiCode a' f') cu (snd (snd (snd ev))))))
  EqVal2-sym (SigmaCode a' f') UCode cu ca ev =
    mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (EqValTy2-sym (SigmaCode a' f') cu (snd (snd (snd ev))))))
  EqVal2-sym (PairCode u' v') UCode cu ca tt = tt
  EqVal2-sym PropCode UCode cu ca ev =
    mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (EqValTy2-sym PropCode cu (snd (snd (snd ev))))))
  EqVal2-sym (PiCode a' f') PropCode cu ca ev =
    mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (EqValTy2-sym (PiCode a' f') cu (snd (snd (snd ev))))))
  EqVal2-sym Bot PropCode cu ca tt = tt
  EqVal2-sym UCode PropCode cu ca tt = tt
  EqVal2-sym PropCode PropCode cu ca tt = tt
  EqVal2-sym (FunEl g) PropCode cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') PropCode cu ca tt = tt
  EqVal2-sym (PairCode u' v') PropCode cu ca tt = tt
  EqVal2-sym u (FunEl h) cu ca tt = tt
  EqVal2-sym Bot (PiCode b f) cu ca tt = tt
  EqVal2-sym UCode (PiCode b f) cu ca tt = tt
  EqVal2-sym PropCode (PiCode b f) cu ca tt = tt
  EqVal2-sym (FunEl g) (PiCode b f) cu ca ev =
    let vty  = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        eqvp = snd (snd (snd ev))
        A0     = REqValPi.domA0 eqvp
        B0     = REqValPi.codB0 eqvp
        redA   = REqValPi.red eqvp
        cg     = REqValPi.cohG eqvp
        fmg    = REqValPi.fmG eqvp
        paev   = REqValPi.appEV eqvp
        cf     = snd ca
        paev'  : PiAppEqVal2 _ _ _ _ B0 b f g
        paev'  = \ u' v' sel P htP valP ->
          let body = paev u' v' sel P htP valP
              ctg  = cft-from-cf g cg
              cu'  = Coherent-Selection sel ctg
              cv'  = Coherent-Selection-val sel ctg
              cev  = Coherent-EvalFun f u' cf cu'
          in EqVal2-sym v' (EvalFun f u') cv' cev body
        eqvp' = record
          { domA0 = A0 ; codB0 = B0 ; red = redA
          ; cohG = cg ; fmG = fmg ; appEV = paev'
          }
    in mkSigma vty (mkSigma vpiN (mkSigma vpiM eqvp'))
  EqVal2-sym (PiCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (PiCode b f) cu ca tt = tt
  EqVal2-sym Bot (SigmaCode b f) cu ca tt = tt
  EqVal2-sym UCode (SigmaCode b f) cu ca tt = tt
  EqVal2-sym PropCode (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (FunEl g) (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (PiCode a' f') (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (SigmaCode b f) cu ca ev =
    let vty   = fst ev
        vpM   = fst (snd ev)
        vpN   = fst (snd (snd ev))
        eqp   = snd (snd (snd ev))
        A0    = REqValSigma.domA eqp
        B0    = REqValSigma.codB eqp
        redA  = REqValSigma.red eqp
        cf    = snd ca
        eqFst' = EqVal2-sym u' b (RValSigma.cohW1 vpM) (fst ca) (REqValSigma.eqFst eqp)
        eqp'  = record
          { domA    = A0 ; codB = B0 ; red = redA
          ; htFstM  = REqValSigma.htFstN eqp
          ; cohW1   = REqValSigma.cohW1 eqp
          ; fmW1    = REqValSigma.fmW1 eqp
          ; valFstM = REqValSigma.valFstN eqp
          ; valSndM = REqValSigma.valSndN eqp
          ; htFstN  = REqValSigma.htFstM eqp
          ; valFstN = REqValSigma.valFstM eqp
          ; valSndN = REqValSigma.valSndM eqp
          ; eqFst   = eqFst'
          }
    in mkSigma vty (mkSigma vpN (mkSigma vpM eqp'))
  EqVal2-sym u (PairCode x y) cu ca tt = tt

  ------------------------------------------------------------------
  -- EqVal2-trans
  ------------------------------------------------------------------

  EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a ->
    EqVal2 G M1 M3 A u a
  EqVal2-trans u Bot cu ca tt tt = tt
  EqVal2-trans Bot UCode cu ca tt tt = tt
  EqVal2-trans UCode UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2))) (EqValTy2-trans UCode cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
  EqVal2-trans (FunEl g) UCode cu ca ev1 ev2 = tt
  EqVal2-trans (PiCode a' f') UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
      (EqValTy2-trans (PiCode a' f') cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
  EqVal2-trans (SigmaCode a' f') UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
      (EqValTy2-trans (SigmaCode a' f') cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
  EqVal2-trans (PairCode u' v') UCode cu ca tt tt = tt
  EqVal2-trans PropCode UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
      (EqValTy2-trans PropCode cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
  EqVal2-trans (PiCode a' f') PropCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
      (EqValTy2-trans (PiCode a' f') cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
  EqVal2-trans Bot PropCode cu ca tt tt = tt
  EqVal2-trans UCode PropCode cu ca tt tt = tt
  EqVal2-trans PropCode PropCode cu ca tt tt = tt
  EqVal2-trans (FunEl g) PropCode cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') PropCode cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') PropCode cu ca tt tt = tt
  EqVal2-trans u (FunEl h) cu ca tt tt = tt
  EqVal2-trans Bot (PiCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans PropCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (PiCode b f) cu ca ev1 ev2 =
    let vty    = fst ev1
        vpiM1  = fst (snd ev1)
        vpiM3  = fst (snd (snd ev2))
        epi1   = snd (snd (snd ev1))
        epi2   = snd (snd (snd ev2))
        Ax     = REqValPi.domA0 epi1
        Bx     = REqValPi.codB0 epi1
        redAx  = REqValPi.red epi1
        cg     = REqValPi.cohG epi1
        fmg    = REqValPi.fmG epi1
        paev1  = REqValPi.appEV epi1
        Ay     = REqValPi.domA0 epi2
        By     = REqValPi.codB0 epi2
        redAy  = REqValPi.red epi2
        paev2  = REqValPi.appEV epi2
        uniq   = Red3-unique-Pi redAx redAy
        eqA0   = fst uniq
        eqB0   = snd uniq
        paev2' : PiAppEqVal2 _ _ _ Ax Bx b f g
        paev2' = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X Bx b f g) (Eq-sym eqA0)
                   (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ Ay Y b f g) (Eq-sym eqB0) paev2)
        cf     = snd ca
        paev'  : PiAppEqVal2 _ _ _ Ax Bx b f g
        paev'  = \ u' v' sel P htP valP ->
          let body1 = paev1 u' v' sel P htP valP
              body2 = paev2' u' v' sel P htP valP
              ctg  = cft-from-cf g cg
              cv'  = Coherent-Selection-val sel ctg
              cu'  = Coherent-Selection sel ctg
              cev  = Coherent-EvalFun f u' cf cu'
          in EqVal2-trans v' (EvalFun f u') cv' cev body1 body2
        epi' = record
          { domA0 = Ax ; codB0 = Bx ; red = redAx
          ; cohG = cg ; fmG = fmg ; appEV = paev'
          }
    in mkSigma vty (mkSigma vpiM1 (mkSigma vpiM3 epi'))
  EqVal2-trans (PiCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans Bot (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans PropCode (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (SigmaCode b f) cu ca ev1 ev2 =
    let vty     = fst ev1
        vpM1    = fst (snd ev1)
        vpM3    = fst (snd (snd ev2))
        eqp1    = snd (snd (snd ev1))
        eqp2    = snd (snd (snd ev2))
        Ax      = REqValSigma.domA eqp1
        Bx      = REqValSigma.codB eqp1
        redAx   = REqValSigma.red eqp1
        Ay      = REqValSigma.domA eqp2
        By      = REqValSigma.codB eqp2
        redAy   = REqValSigma.red eqp2
        uniq    = Red3-unique-Sigma redAx redAy
        eqA0    = fst uniq
        eqB0    = snd uniq
        eqFst1  = REqValSigma.eqFst eqp1
        eqFst2  = REqValSigma.eqFst eqp2
        eqFst2' = Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X u' b) (Eq-sym eqA0) eqFst2
        eqFst'  = EqVal2-trans u' b (RValSigma.cohW1 vpM1) (fst ca) eqFst1 eqFst2'
        eqp'    = record
          { domA    = Ax ; codB = Bx ; red = redAx
          ; htFstM  = REqValSigma.htFstM eqp1
          ; cohW1   = REqValSigma.cohW1 eqp1
          ; fmW1    = REqValSigma.fmW1 eqp1
          ; valFstM = REqValSigma.valFstM eqp1
          ; valSndM = REqValSigma.valSndM eqp1
          ; htFstN  = Eq-transport (\ X -> HasType _ _ X) (Eq-sym eqA0) (REqValSigma.htFstN eqp2)
          ; valFstN = Eq-transport (\ X -> Val2 _ _ X u' b) (Eq-sym eqA0) (REqValSigma.valFstN eqp2)
          ; valSndN = Eq-transport (\ X -> Val2 _ _ (subst1 X _) v' (EvalFun f u')) (Eq-sym eqB0)
                        (REqValSigma.valSndN eqp2)
          ; eqFst   = eqFst'
          }
    in mkSigma vty (mkSigma vpM1 (mkSigma vpM3 eqp'))
  EqVal2-trans u (PairCode x y) cu ca tt tt = tt
