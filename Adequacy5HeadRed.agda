{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Adequacy5HeadRed.agda
--
-- Headred transport for adequacy.
-- Val2-beta-expand delegates to Validity5Lemmas.
-- Val2-headred-contract and EqVal2-headred-expand in mutual block.
-- 0 postulates.
------------------------------------------------------------------------

module Adequacy5HeadRed where
open import Adequacy5Helpers public

import Validity5Lemmas as V5L

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ;
              codeFst ; codeSnd)
open import RawSyntaxSigma using (Expr ; U ; Prop ; Pi ; Fst ; Snd ; App ;
  Fin ; fzero ; fsuc ; subst1)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; extend ;
  HasType ; ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Prop-U ;
  conv-App-fun ; conv-Fst ; conv-Snd)
open import ReductionSigma using (HeadRed ; HeadRed1 ; HeadRed1-det ;
  headred-refl ; headred-step ; Red ; mkRed ; Red-hr ;
  HeadRed-trans ; HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma)
open import PaperSemanticsSigma using (EvalFun ; CoherentFun ; CoherentFunTail ;
  FinMemFun ; FinMemAllU ; Coherent ; FinMem ; coh-from-aU ; cft-from-cf)
open import SubstitutionLemmaSigma using (typing-ConvTm ; typing-type ;
  subst1-cong-ConvTm)
open import SelectionSigma using (selectionBelow ; FinMemAllU-Selection ;
  Coherent-Selection ; Coherent-Selection-val)

------------------------------------------------------------------------
-- HeadRed strip lemmas for U and Prop (normal forms)
------------------------------------------------------------------------

HeadRed1-not-U : {n : Nat} {N : Expr n} -> HeadRed1 U N -> Empty
HeadRed1-not-U ()

HeadRed1-not-Prop : {n : Nat} {N : Expr n} -> HeadRed1 Prop N -> Empty
HeadRed1-not-Prop ()

HeadRed-strip-U : {n : Nat} {M M' : Expr n} ->
  HeadRed M M' -> HeadRed M U -> HeadRed M' U
HeadRed-strip-U headred-refl hr2 = hr2
HeadRed-strip-U (headred-step s1 hr1) headred-refl with HeadRed1-not-U s1
... | ()
HeadRed-strip-U (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-U hr1
    (S.Eq-transport (\ x -> HeadRed x U) (S.Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Prop : {n : Nat} {M M' : Expr n} ->
  HeadRed M M' -> HeadRed M Prop -> HeadRed M' Prop
HeadRed-strip-Prop headred-refl hr2 = hr2
HeadRed-strip-Prop (headred-step s1 hr1) headred-refl with HeadRed1-not-Prop s1
... | ()
HeadRed-strip-Prop (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Prop hr1
    (S.Eq-transport (\ x -> HeadRed x Prop) (S.Eq-sym (HeadRed1-det s1 s2)) hr2)

------------------------------------------------------------------------
-- Val2-beta-expand: delegate to Validity5Lemmas
-- HeadRed M' M means M' reduces to M (expand from M to M')
------------------------------------------------------------------------

Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
  (u a : FinEl) -> HeadRed M' M -> ConvTm G M' M T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-beta-expand u a hr cv val =
  Val2-from-EqVal2-second u a (V5L.Val2-beta-expand u a hr cv val)

------------------------------------------------------------------------
-- Mutual block: contract and EqVal2-headred-expand/contract
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- ValTy2-headred-contract: HeadRed M M', ConvTm G M M' U
  ValTy2-headred-contract : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M M' -> ConvTm G M M' U ->
    ValTy2 G M u -> ValTy2 G M' u
  ValTy2-headred-contract Bot hr cv vt = tt
  ValTy2-headred-contract UCode hr cv vt =
    mkRed3 (HeadRed-strip-U hr (Red3.hr vt)) (conv-trans (conv-sym cv) (Red3.ct vt))
  ValTy2-headred-contract PropCode hr cv vt =
    mkRed3 (HeadRed-strip-Prop hr (Red3.hr vt)) (conv-trans (conv-sym cv) (Red3.ct vt))
  ValTy2-headred-contract (FunEl g) hr cv vt = tt
  ValTy2-headred-contract (PairCode _ _) hr cv vt = tt
  ValTy2-headred-contract (PiCode b f) hr cv vt =
    record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
           ; red = mkRed3 (HeadRed-strip-Pi hr (Red3.hr (RValTyPi.red vt)))
                          (conv-trans (conv-sym cv) (Red3.ct (RValTyPi.red vt)))
           ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
           ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
           ; valA = RValTyPi.valA vt
           ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }
  ValTy2-headred-contract (SigmaCode b f) hr cv vt =
    record { domA = RValTySigma.domA vt ; codB = RValTySigma.codB vt
           ; red = mkRed3 (HeadRed-strip-Sigma hr (Red3.hr (RValTySigma.red vt)))
                          (conv-trans (conv-sym cv) (Red3.ct (RValTySigma.red vt)))
           ; cohF = RValTySigma.cohF vt ; fmAllU = RValTySigma.fmAllU vt
           ; fmBU = RValTySigma.fmBU vt
           ; htA = RValTySigma.htA vt ; htB = RValTySigma.htB vt
           ; valA = RValTySigma.valA vt
           ; edgeV = RValTySigma.edgeV vt ; edgeE = RValTySigma.edgeE vt }

  -- EqValTy2-headred-contract
  EqValTy2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    ConvTm G M1 M1' U -> ConvTm G M2 M2' U ->
    EqValTy2 G M1 M2 u -> EqValTy2 G M1' M2' u
  EqValTy2-headred-contract Bot hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-contract UCode hr1 hr2 cv1 cv2 eqvt =
    mkSigma (mkRed3 (HeadRed-strip-U hr1 (Red3.hr (fst eqvt))) (conv-trans (conv-sym cv1) (Red3.ct (fst eqvt))))
            (mkRed3 (HeadRed-strip-U hr2 (Red3.hr (snd eqvt))) (conv-trans (conv-sym cv2) (Red3.ct (snd eqvt))))
  EqValTy2-headred-contract PropCode hr1 hr2 cv1 cv2 eqvt =
    mkSigma (mkRed3 (HeadRed-strip-Prop hr1 (Red3.hr (fst eqvt))) (conv-trans (conv-sym cv1) (Red3.ct (fst eqvt))))
            (mkRed3 (HeadRed-strip-Prop hr2 (Red3.hr (snd eqvt))) (conv-trans (conv-sym cv2) (Red3.ct (snd eqvt))))
  EqValTy2-headred-contract (FunEl g) hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-contract (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-contract (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
    let vt1  = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
    in mkSigma (ValTy2-headred-contract (PiCode b f) hr1 cv1 vt1)
         (mkSigma (ValTy2-headred-contract (PiCode b f) hr2 cv2 vt2)
           (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                   ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                   ; redM = mkRed3 (HeadRed-strip-Pi hr1 (Red3.hr (REqValTyPi.redM core)))
                                   (conv-trans (conv-sym cv1) (Red3.ct (REqValTyPi.redM core)))
                   ; redN = mkRed3 (HeadRed-strip-Pi hr2 (Red3.hr (REqValTyPi.redN core)))
                                   (conv-trans (conv-sym cv2) (Red3.ct (REqValTyPi.redN core)))
                   ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                   ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                   ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))
  EqValTy2-headred-contract (SigmaCode b f) hr1 hr2 cv1 cv2 eqvt =
    let vt1  = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
    in mkSigma (ValTy2-headred-contract (SigmaCode b f) hr1 cv1 vt1)
         (mkSigma (ValTy2-headred-contract (SigmaCode b f) hr2 cv2 vt2)
           (record { domA = REqValTySigma.domA core ; codB = REqValTySigma.codB core
                   ; domA' = REqValTySigma.domA' core ; codB' = REqValTySigma.codB' core
                   ; redM = mkRed3 (HeadRed-strip-Sigma hr1 (Red3.hr (REqValTySigma.redM core)))
                                   (conv-trans (conv-sym cv1) (Red3.ct (REqValTySigma.redM core)))
                   ; redN = mkRed3 (HeadRed-strip-Sigma hr2 (Red3.hr (REqValTySigma.redN core)))
                                   (conv-trans (conv-sym cv2) (Red3.ct (REqValTySigma.redN core)))
                   ; cohF = REqValTySigma.cohF core ; fmAllU = REqValTySigma.fmAllU core
                   ; convA = REqValTySigma.convA core ; convB = REqValTySigma.convB core
                   ; eqA = REqValTySigma.eqA core ; edgeET = REqValTySigma.edgeET core }))

  -- ValPi2-headred-contract
  ValPi2-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M M' -> ConvTm G M M' T -> RValTyPi G T b f ->
    RValPi G M T g0 b f -> RValPi G M' T g0 b f
  ValPi2-headred-contract g0 b f hr cv vty vpiM =
    let A0    = RValPi.domA0 vpiM
        B0    = RValPi.codB0 vpiM
        redT  = RValPi.red vpiM
        uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
        htPiU = snd (typing-ConvTm (Red3.ct redT))
        ctPi  = conv-conv cv (Red3.ct redT) htPiU
    in record { domA0 = A0 ; codB0 = B0 ; red = redT
              ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
              ; appV = \ u v sel N htN valN ->
                  Val2-headred-contract v (EvalFun f u) (HeadRed-App hr)
                    (conv-App-fun htA0 htB0 ctPi htN)
                    (RValPi.appV vpiM u v sel N htN valN)
              ; appE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
                  let cvApp1 = conv-App-fun htA0 htB0 ctPi htN1
                      cvApp2-raw = conv-App-fun htA0 htB0 ctPi htN2
                      cvBN = subst1-cong-ConvTm htA0 htB0 htN1 htN2 cvN
                      htB0N1 = fst (typing-ConvTm cvBN)
                      cvApp2 = conv-conv cvApp2-raw (conv-sym cvBN) htB0N1
                  in EqVal2-headred-contract v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                       cvApp1 cvApp2
                       (RValPi.appE vpiM u v sel N1 N2 htN1 htN2 cvN eqN) }

  EqValPi2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1 M1' -> HeadRed M2 M2' ->
    ConvTm G M1 M1' T -> ConvTm G M2 M2' T -> RValTyPi G T b f ->
    REqValPi G M1 M2 T g0 b f -> REqValPi G M1' M2' T g0 b f
  EqValPi2-headred-contract g0 b f hr1 hr2 cv1 cv2 vty epi =
    let A0    = REqValPi.domA0 epi
        B0    = REqValPi.codB0 epi
        redT  = REqValPi.red epi
        uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
        htPiU = snd (typing-ConvTm (Red3.ct redT))
        ctPi1 = conv-conv cv1 (Red3.ct redT) htPiU
        ctPi2 = conv-conv cv2 (Red3.ct redT) htPiU
    in record { domA0 = A0 ; codB0 = B0 ; red = redT
              ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
              ; appEV = \ u v sel P htP valP ->
                  EqVal2-headred-contract v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                    (conv-App-fun htA0 htB0 ctPi1 htP) (conv-App-fun htA0 htB0 ctPi2 htP)
                    (REqValPi.appEV epi u v sel P htP valP) }

  -- Sigma codomain transport: given EqVal2 for Fst M / Fst M',
  -- produce EqValTy2 for subst1 B0 (Fst M) / subst1 B0 (Fst M')
  sigma-codomain-eq : {n : Nat} {G : Ctx n} {M M' T A0 : Expr n} {B0 : Expr (suc n)}
    (u' : FinEl) (b0 : FinEl) (f0 : FinFun) ->
    (redT : Red3 G T (SigmaE A0 B0) U) ->
    ConvTm G (Fst M) (Fst M') A0 ->
    EqVal2 G (Fst M) (Fst M') A0 u' b0 ->
    (cu' : Coherent u') -> FinMem u' b0 ->
    (vty : RValTySigma G T b0 f0) ->
    EqValTy2 G (subst1 B0 (Fst M)) (subst1 B0 (Fst M')) (EvalFun f0 u')
  sigma-codomain-eq {G = G} {M} {M'} {T} {A0} {B0} u' b0 f0 redT cvFst eqFstMM' cu' fmu' vty =
    let uniq   = Red3-unique-Sigma (RValTySigma.red vty) redT
        cf-sig = RValTySigma.cohF vty
        bU-sig = RValTySigma.fmBU vty
        cb-sig = coh-from-aU b0 bU-sig
        sb     = selectionBelow f0 u' cf-sig cu'
        u-f    = fst sb ; v-f = fst (snd sb)
        sel-f  = fst (snd (snd sb))
        le-uf  = fst (snd (snd (snd sb)))
        eq-ef  = snd (snd (snd (snd sb)))
        fmu-f  = FinMemAllU-Selection b0 sel-f (RValTySigma.fmAllU vty) cf-sig cb-sig bU-sig
        -- Restrict eqFst
        eqFst-uf = restrictEqVal2 _ _ _ A0 u' u-f b0 le-uf fmu-f fmu' eqFstMM'
        -- Transport to vty coords
        eqA-to-vty   = S.Eq-sym (fst uniq)
        htFstM-vty   = S.Eq-transport (\ X -> HasType _ _ X) eqA-to-vty (fst (typing-ConvTm cvFst))
        htFstM'-vty  = S.Eq-transport (\ X -> HasType _ _ X) eqA-to-vty (snd (typing-ConvTm cvFst))
        cvFst-vty    = S.Eq-transport (\ X -> ConvTm _ _ _ X) eqA-to-vty cvFst
        eqFst-uf-vty = S.Eq-transport (\ X -> EqVal2 _ _ _ X u-f b0) eqA-to-vty eqFst-uf
        codB-vty     = RValTySigma.codB vty
        eqTyB-vf     = RValTySigma.edgeE vty u-f v-f sel-f
                          (Fst M) (Fst M') htFstM-vty htFstM'-vty cvFst-vty eqFst-uf-vty
        eqTyB-ef = S.Eq-transport (\ w -> EqValTy2 _ (subst1 codB-vty (Fst M)) (subst1 codB-vty (Fst M')) w)
                     (S.Eq-sym eq-ef) eqTyB-vf
        eqTyB    = S.Eq-transport (\ Y -> EqValTy2 _ (subst1 Y (Fst M)) (subst1 Y (Fst M')) (EvalFun f0 u'))
                     (snd uniq) eqTyB-ef
    in eqTyB

  -- Val2-headred-contract: HeadRed M M', ConvTm G M M' T
  Val2-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
    Val2 G M T u a -> Val2 G M' T u a
  Val2-headred-contract u Bot hr cv tt = tt
  Val2-headred-contract Bot UCode hr cv tt = tt
  Val2-headred-contract UCode UCode hr cv val =
    let vtA = fst val ; vtM = snd val
        ctU = conv-conv cv (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA (mkRed3 (HeadRed-strip-U hr (Red3.hr vtM)) (conv-trans (conv-sym ctU) (Red3.ct vtM)))
  Val2-headred-contract PropCode UCode hr cv val =
    let vtA = fst val ; vtP = snd val
        ctU = conv-conv cv (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA (mkRed3 (HeadRed-strip-Prop hr (Red3.hr vtP)) (conv-trans (conv-sym ctU) (Red3.ct vtP)))
  Val2-headred-contract (FunEl g) UCode hr cv tt = tt
  Val2-headred-contract (PiCode a' f') UCode hr cv val =
    let vtA = fst val ; vtPi = snd val
        ctU = conv-conv cv (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA (ValTy2-headred-contract (PiCode a' f') hr ctU vtPi)
  Val2-headred-contract (SigmaCode a' f') UCode hr cv val =
    let vtA = fst val ; vtSig = snd val
        ctU = conv-conv cv (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA (ValTy2-headred-contract (SigmaCode a' f') hr ctU vtSig)
  Val2-headred-contract (PairCode _ _) UCode hr cv tt = tt
  Val2-headred-contract (PiCode a' f') PropCode hr cv val =
    let vtA = fst val ; vtPi = snd val
        ctU = conv-Prop-U (conv-conv cv (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA (ValTy2-headred-contract (PiCode a' f') hr ctU vtPi)
  Val2-headred-contract Bot PropCode hr cv tt = tt
  Val2-headred-contract UCode PropCode hr cv tt = tt
  Val2-headred-contract PropCode PropCode hr cv tt = tt
  Val2-headred-contract (FunEl _) PropCode hr cv tt = tt
  Val2-headred-contract (SigmaCode _ _) PropCode hr cv tt = tt
  Val2-headred-contract (PairCode _ _) PropCode hr cv tt = tt
  Val2-headred-contract u (FunEl h) hr cv tt = tt
  Val2-headred-contract Bot (PiCode b f) hr cv tt = tt
  Val2-headred-contract UCode (PiCode b f) hr cv tt = tt
  Val2-headred-contract PropCode (PiCode b f) hr cv tt = tt
  Val2-headred-contract (FunEl g) (PiCode b f) hr cv val =
    mkSigma (fst val) (ValPi2-headred-contract g b f hr cv (fst val) (snd val))
  Val2-headred-contract (PiCode a' f') (PiCode b f) hr cv tt = tt
  Val2-headred-contract (SigmaCode _ _) (PiCode b f) hr cv tt = tt
  Val2-headred-contract (PairCode _ _) (PiCode b f) hr cv tt = tt
  Val2-headred-contract Bot (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract UCode (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract PropCode (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract (FunEl _) (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract (PiCode _ _) (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract (SigmaCode _ _) (SigmaCode _ _) hr cv tt = tt
  Val2-headred-contract (PairCode u' v') (SigmaCode b0 f0) hr cv val =
    let vty  = fst val ; vsig = snd val
        A0   = RValSigma.domA vsig ; B0 = RValSigma.codB vsig
        redT = RValSigma.red vsig
        uniq = Red3-unique-Sigma (RValTySigma.red vty) redT
        htA0 = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTySigma.htA vty)
        htB0 = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                 (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTySigma.htB vty))
        htSigU = snd (typing-ConvTm (Red3.ct redT))
        cvSig  = conv-conv cv (Red3.ct redT) htSigU
        -- Step 1: contract Fst
        cvFst  = conv-Fst htA0 htB0 cvSig
        valFstM' = Val2-headred-contract u' b0 (HeadRed-Fst hr) cvFst (RValSigma.valFst vsig)
        htFstM'  = snd (typing-ConvTm cvFst)
        -- Step 2: contract Snd (at type subst1 B0 (Fst M))
        cvSnd  = conv-Snd htA0 htB0 cvSig
        valSndM'-raw = Val2-headred-contract v' (EvalFun f0 u') (HeadRed-Snd hr) cvSnd (RValSigma.valSnd vsig)
        -- Step 3: transport snd type from subst1 B0 (Fst M) to subst1 B0 (Fst M')
        eqFstMM'-rev = V5L.Val2-beta-expand u' b0 (HeadRed-Fst hr) cvFst valFstM'
        -- V5L gives EqVal2 G (Fst M') (Fst M), need (Fst M) (Fst M')
        cb0  = coh-from-aU b0 (RValTySigma.fmBU vty)
        eqFstMM' = EqVal2-sym u' b0 (RValSigma.cohW1 vsig) cb0 eqFstMM'-rev
        eqTyB = sigma-codomain-eq u' b0 f0 redT cvFst eqFstMM'
                  (RValSigma.cohW1 vsig) (RValSigma.fmW1 vsig) vty
        valSndM' = Val2-type-transport v' (EvalFun f0 u') eqTyB valSndM'-raw
    in mkSigma vty (record { domA = A0 ; codB = B0 ; red = redT
                            ; htFst = htFstM'
                            ; cohW1 = RValSigma.cohW1 vsig ; fmW1 = RValSigma.fmW1 vsig
                            ; valFst = valFstM' ; valSnd = valSndM' })
  Val2-headred-contract Bot (PairCode _ _) hr cv tt = tt
  Val2-headred-contract UCode (PairCode _ _) hr cv tt = tt
  Val2-headred-contract PropCode (PairCode _ _) hr cv tt = tt
  Val2-headred-contract (FunEl _) (PairCode _ _) hr cv tt = tt
  Val2-headred-contract (PiCode _ _) (PairCode _ _) hr cv tt = tt
  Val2-headred-contract (SigmaCode _ _) (PairCode _ _) hr cv tt = tt
  Val2-headred-contract (PairCode _ _) (PairCode _ _) hr cv tt = tt

  -- EqVal2-headred-expand: HeadRed M' M, HeadRed N' N
  EqVal2-headred-expand : {n : Nat} {G : Ctx n} {M M' N N' T : Expr n}
    (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
    ConvTm G M' M T -> ConvTm G N' N T ->
    EqVal2 G M N T u a -> EqVal2 G M' N' T u a
  EqVal2-headred-expand u Bot hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand Bot UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand UCode UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
        vtM' = mkRed3 (HeadRed-trans hr1 (Red3.hr vtM)) (conv-trans ctU1 (Red3.ct vtM))
        vtN' = mkRed3 (HeadRed-trans hr2 (Red3.hr vtN)) (conv-trans ctU2 (Red3.ct vtN))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
  EqVal2-headred-expand PropCode UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
        vtM' = mkRed3 (HeadRed-trans hr1 (Red3.hr vtM)) (conv-trans ctU1 (Red3.ct vtM))
        vtN' = mkRed3 (HeadRed-trans hr2 (Red3.hr vtN)) (conv-trans ctU2 (Red3.ct vtN))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
  EqVal2-headred-expand (FunEl g) UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PiCode a' f') UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        expand1 = ValTy2-headred-expand (PiCode a' f') hr1 ctU1 (fst (snd ev))
        expand2 = ValTy2-headred-expand (PiCode a' f') hr2 ctU2 (fst (snd (snd ev)))
        eqexpand = EqValTy2-headred-expand (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev)))
    in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
  EqVal2-headred-expand (SigmaCode a' f') UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        expand1 = ValTy2-headred-expand (SigmaCode a' f') hr1 ctU1 (fst (snd ev))
        expand2 = ValTy2-headred-expand (SigmaCode a' f') hr2 ctU2 (fst (snd (snd ev)))
        eqexpand = EqValTy2-headred-expand (SigmaCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev)))
    in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
  EqVal2-headred-expand (PairCode _ _) UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PiCode a' f') PropCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-Prop-U (conv-conv cv1 (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-Prop-U (conv-conv cv2 (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
        expand1 = ValTy2-headred-expand (PiCode a' f') hr1 ctU1 (fst (snd ev))
        expand2 = ValTy2-headred-expand (PiCode a' f') hr2 ctU2 (fst (snd (snd ev)))
        eqexpand = EqValTy2-headred-expand (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev)))
    in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
  EqVal2-headred-expand Bot PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand UCode PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand PropCode PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (FunEl _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PairCode _ _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand UCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand PropCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
    let vty = fst ev
    in mkSigma vty
         (mkSigma (ValPi2-headred-expand g b f hr1 cv1 vty (fst (snd ev)))
           (mkSigma (ValPi2-headred-expand g b f hr2 cv2 vty (fst (snd (snd ev))))
             (EqValPi2-headred-expand g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
  EqVal2-headred-expand (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PairCode _ _) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand Bot (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand UCode (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand PropCode (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (FunEl _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PiCode _ _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PairCode u' v') (SigmaCode b0 f0) hr1 hr2 cv1 cv2 ev =
    let vty   = fst ev
        vsigM = fst (snd ev) ; vsigN = fst (snd (snd ev)) ; esig = snd (snd (snd ev))
        A0    = REqValSigma.domA esig ; B0 = REqValSigma.codB esig
        redT  = REqValSigma.red esig
        uniq  = Red3-unique-Sigma (RValTySigma.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTySigma.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTySigma.htB vty))
        htSigU = snd (typing-ConvTm (Red3.ct redT))
        cvSig1 = conv-conv cv1 (Red3.ct redT) htSigU
        cvSig2 = conv-conv cv2 (Red3.ct redT) htSigU
        cvFst1 = conv-Fst htA0 htB0 cvSig1
        cvFst2 = conv-Fst htA0 htB0 cvSig2
        cvSnd1 = conv-Snd htA0 htB0 cvSig1
        cvSnd2 = conv-Snd htA0 htB0 cvSig2
        -- Expand Fst
        valFstM' = Val2-beta-expand u' b0 (HeadRed-Fst hr1) cvFst1 (REqValSigma.valFstM esig)
        valFstN' = Val2-beta-expand u' b0 (HeadRed-Fst hr2) cvFst2 (REqValSigma.valFstN esig)
        eqFst'   = EqVal2-headred-expand u' b0 (HeadRed-Fst hr1) (HeadRed-Fst hr2)
                     cvFst1 cvFst2 (REqValSigma.eqFst esig)
        htFstM'  = fst (typing-ConvTm cvFst1)
        htFstN'  = fst (typing-ConvTm cvFst2)
        -- Type transport for Snd: subst1 B0 (Fst M) → subst1 B0 (Fst M')
        eqFstMM' = V5L.Val2-beta-expand u' b0 (HeadRed-Fst hr1) cvFst1 (REqValSigma.valFstM esig)
        eqFstNN' = V5L.Val2-beta-expand u' b0 (HeadRed-Fst hr2) cvFst2 (REqValSigma.valFstN esig)
        eqTyM = sigma-codomain-eq u' b0 f0 redT (conv-sym cvFst1) eqFstMM'
                  (REqValSigma.cohW1 esig) (REqValSigma.fmW1 esig) vty
        eqTyN = sigma-codomain-eq u' b0 f0 redT (conv-sym cvFst2) eqFstNN'
                  (REqValSigma.cohW1 esig) (REqValSigma.fmW1 esig) vty
        -- Step 1: transport valSnd type, Step 2: expand Snd term
        valSndM-typed = Val2-type-transport v' (EvalFun f0 u') eqTyM (REqValSigma.valSndM esig)
        valSndN-typed = Val2-type-transport v' (EvalFun f0 u') eqTyN (REqValSigma.valSndN esig)
        valSndM' = Val2-beta-expand v' (EvalFun f0 u') (HeadRed-Snd hr1) cvSnd1 valSndM-typed
        valSndN' = Val2-beta-expand v' (EvalFun f0 u') (HeadRed-Snd hr2) cvSnd2 valSndN-typed
    in mkSigma vty
         (mkSigma (record { domA = A0 ; codB = B0 ; red = redT ; htFst = htFstM'
                           ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                           ; valFst = valFstM' ; valSnd = valSndM' })
           (mkSigma (record { domA = A0 ; codB = B0 ; red = redT ; htFst = htFstN'
                             ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                             ; valFst = valFstN' ; valSnd = valSndN' })
             (record { domA = A0 ; codB = B0 ; red = redT
                     ; htFstM = htFstM' ; htFstN = htFstN'
                     ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                     ; valFstM = valFstM' ; valSndM = valSndM'
                     ; valFstN = valFstN' ; valSndN = valSndN'
                     ; eqFst = eqFst' })))
  EqVal2-headred-expand Bot (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand UCode (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand PropCode (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (FunEl _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PiCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-expand (PairCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt

  -- EqVal2-headred-contract
  EqVal2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    ConvTm G M1 M1' T -> ConvTm G M2 M2' T ->
    EqVal2 G M1 M2 T u a -> EqVal2 G M1' M2' T u a
  EqVal2-headred-contract u Bot hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract Bot UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract UCode UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
        vtM' = mkRed3 (HeadRed-strip-U hr1 (Red3.hr vtM)) (conv-trans (conv-sym ctU1) (Red3.ct vtM))
        vtN' = mkRed3 (HeadRed-strip-U hr2 (Red3.hr vtN)) (conv-trans (conv-sym ctU2) (Red3.ct vtN))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
  EqVal2-headred-contract PropCode UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
        vtM' = mkRed3 (HeadRed-strip-Prop hr1 (Red3.hr vtM)) (conv-trans (conv-sym ctU1) (Red3.ct vtM))
        vtN' = mkRed3 (HeadRed-strip-Prop hr2 (Red3.hr vtN)) (conv-trans (conv-sym ctU2) (Red3.ct vtN))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
  EqVal2-headred-contract (FunEl g) UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PiCode a' f') UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA
         (mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 ctU1 (fst (snd ev)))
           (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 ctU2 (fst (snd (snd ev))))
             (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev))))))
  EqVal2-headred-contract (SigmaCode a' f') UCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-conv cv1 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-conv cv2 (Red3.ct vtA) (typing-type (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA
         (mkSigma (ValTy2-headred-contract (SigmaCode a' f') hr1 ctU1 (fst (snd ev)))
           (mkSigma (ValTy2-headred-contract (SigmaCode a' f') hr2 ctU2 (fst (snd (snd ev))))
             (EqValTy2-headred-contract (SigmaCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev))))))
  EqVal2-headred-contract (PairCode _ _) UCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PiCode a' f') PropCode hr1 hr2 cv1 cv2 ev =
    let vtA = fst ev
        ctU1 = conv-Prop-U (conv-conv cv1 (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
        ctU2 = conv-Prop-U (conv-conv cv2 (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
    in mkSigma vtA
         (mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 ctU1 (fst (snd ev)))
           (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 ctU2 (fst (snd (snd ev))))
             (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev))))))
  EqVal2-headred-contract Bot PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract UCode PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract PropCode PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (FunEl _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PairCode _ _) PropCode hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract UCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract PropCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
    let vty = fst ev
    in mkSigma vty
         (mkSigma (ValPi2-headred-contract g b f hr1 cv1 vty (fst (snd ev)))
           (mkSigma (ValPi2-headred-contract g b f hr2 cv2 vty (fst (snd (snd ev))))
             (EqValPi2-headred-contract g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
  EqVal2-headred-contract (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PairCode _ _) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract Bot (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract UCode (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract PropCode (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (FunEl _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PiCode _ _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (SigmaCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PairCode u' v') (SigmaCode b0 f0) hr1 hr2 cv1 cv2 ev =
    let vty   = fst ev
        vsigM = fst (snd ev) ; vsigN = fst (snd (snd ev)) ; esig = snd (snd (snd ev))
        A0    = REqValSigma.domA esig ; B0 = REqValSigma.codB esig
        redT  = REqValSigma.red esig
        uniq  = Red3-unique-Sigma (RValTySigma.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTySigma.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTySigma.htB vty))
        htSigU = snd (typing-ConvTm (Red3.ct redT))
        cvSig1 = conv-conv cv1 (Red3.ct redT) htSigU
        cvSig2 = conv-conv cv2 (Red3.ct redT) htSigU
        cvFst1 = conv-Fst htA0 htB0 cvSig1
        cvFst2 = conv-Fst htA0 htB0 cvSig2
        cvSnd1 = conv-Snd htA0 htB0 cvSig1
        cvSnd2 = conv-Snd htA0 htB0 cvSig2
        -- Contract Fst
        valFstM' = Val2-headred-contract u' b0 (HeadRed-Fst hr1) cvFst1 (REqValSigma.valFstM esig)
        valFstN' = Val2-headred-contract u' b0 (HeadRed-Fst hr2) cvFst2 (REqValSigma.valFstN esig)
        eqFst'   = EqVal2-headred-contract u' b0 (HeadRed-Fst hr1) (HeadRed-Fst hr2)
                     cvFst1 cvFst2 (REqValSigma.eqFst esig)
        htFstM'  = snd (typing-ConvTm cvFst1)
        htFstN'  = snd (typing-ConvTm cvFst2)
        -- Contract Snd (term only)
        valSndM-raw = Val2-headred-contract v' (EvalFun f0 u') (HeadRed-Snd hr1) cvSnd1 (REqValSigma.valSndM esig)
        valSndN-raw = Val2-headred-contract v' (EvalFun f0 u') (HeadRed-Snd hr2) cvSnd2 (REqValSigma.valSndN esig)
        -- Type transport for Snd
        cb0 = coh-from-aU b0 (RValTySigma.fmBU vty)
        eqFstMM'-rev = V5L.Val2-beta-expand u' b0 (HeadRed-Fst hr1) cvFst1 valFstM'
        eqFstNN'-rev = V5L.Val2-beta-expand u' b0 (HeadRed-Fst hr2) cvFst2 valFstN'
        eqFstMM' = EqVal2-sym u' b0 (REqValSigma.cohW1 esig) cb0 eqFstMM'-rev
        eqFstNN' = EqVal2-sym u' b0 (REqValSigma.cohW1 esig) cb0 eqFstNN'-rev
        eqTyM = sigma-codomain-eq u' b0 f0 redT cvFst1 eqFstMM'
                  (REqValSigma.cohW1 esig) (REqValSigma.fmW1 esig) vty
        eqTyN = sigma-codomain-eq u' b0 f0 redT cvFst2 eqFstNN'
                  (REqValSigma.cohW1 esig) (REqValSigma.fmW1 esig) vty
        valSndM' = Val2-type-transport v' (EvalFun f0 u') eqTyM valSndM-raw
        valSndN' = Val2-type-transport v' (EvalFun f0 u') eqTyN valSndN-raw
    in mkSigma vty
         (mkSigma (record { domA = A0 ; codB = B0 ; red = redT ; htFst = htFstM'
                           ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                           ; valFst = valFstM' ; valSnd = valSndM' })
           (mkSigma (record { domA = A0 ; codB = B0 ; red = redT ; htFst = htFstN'
                             ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                             ; valFst = valFstN' ; valSnd = valSndN' })
             (record { domA = A0 ; codB = B0 ; red = redT
                     ; htFstM = htFstM' ; htFstN = htFstN'
                     ; cohW1 = REqValSigma.cohW1 esig ; fmW1 = REqValSigma.fmW1 esig
                     ; valFstM = valFstM' ; valSndM = valSndM'
                     ; valFstN = valFstN' ; valSndN = valSndN'
                     ; eqFst = eqFst' })))
  EqVal2-headred-contract Bot (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract UCode (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract PropCode (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (FunEl _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PiCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqVal2-headred-contract (PairCode _ _) (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt

  -- ValTy2-headred-expand and EqValTy2-headred-expand (needed by EqVal2-headred-expand)
  ValTy2-headred-expand : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M' M -> ConvTm G M' M U ->
    ValTy2 G M u -> ValTy2 G M' u
  ValTy2-headred-expand Bot hr cv vt = tt
  ValTy2-headred-expand UCode hr cv vt =
    mkRed3 (HeadRed-trans hr (Red3.hr vt)) (conv-trans cv (Red3.ct vt))
  ValTy2-headred-expand PropCode hr cv vt =
    mkRed3 (HeadRed-trans hr (Red3.hr vt)) (conv-trans cv (Red3.ct vt))
  ValTy2-headred-expand (FunEl g) hr cv vt = tt
  ValTy2-headred-expand (PairCode _ _) hr cv vt = tt
  ValTy2-headred-expand (PiCode b f) hr cv vt =
    record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
           ; red = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyPi.red vt)))
                          (conv-trans cv (Red3.ct (RValTyPi.red vt)))
           ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
           ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
           ; valA = RValTyPi.valA vt
           ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }
  ValTy2-headred-expand (SigmaCode b f) hr cv vt =
    record { domA = RValTySigma.domA vt ; codB = RValTySigma.codB vt
           ; red = mkRed3 (HeadRed-trans hr (Red3.hr (RValTySigma.red vt)))
                          (conv-trans cv (Red3.ct (RValTySigma.red vt)))
           ; cohF = RValTySigma.cohF vt ; fmAllU = RValTySigma.fmAllU vt
           ; fmBU = RValTySigma.fmBU vt
           ; htA = RValTySigma.htA vt ; htB = RValTySigma.htB vt
           ; valA = RValTySigma.valA vt
           ; edgeV = RValTySigma.edgeV vt ; edgeE = RValTySigma.edgeE vt }

  EqValTy2-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
    ConvTm G M1' M1 U -> ConvTm G M2' M2 U ->
    EqValTy2 G M1 M2 u -> EqValTy2 G M1' M2' u
  EqValTy2-headred-expand Bot hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-expand UCode hr1 hr2 cv1 cv2 eqvt =
    mkSigma (mkRed3 (HeadRed-trans hr1 (Red3.hr (fst eqvt))) (conv-trans cv1 (Red3.ct (fst eqvt))))
            (mkRed3 (HeadRed-trans hr2 (Red3.hr (snd eqvt))) (conv-trans cv2 (Red3.ct (snd eqvt))))
  EqValTy2-headred-expand PropCode hr1 hr2 cv1 cv2 eqvt =
    mkSigma (mkRed3 (HeadRed-trans hr1 (Red3.hr (fst eqvt))) (conv-trans cv1 (Red3.ct (fst eqvt))))
            (mkRed3 (HeadRed-trans hr2 (Red3.hr (snd eqvt))) (conv-trans cv2 (Red3.ct (snd eqvt))))
  EqValTy2-headred-expand (FunEl g) hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-expand (PairCode _ _) hr1 hr2 cv1 cv2 tt = tt
  EqValTy2-headred-expand (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
    let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
    in mkSigma (ValTy2-headred-expand (PiCode b f) hr1 cv1 vt1)
         (mkSigma (ValTy2-headred-expand (PiCode b f) hr2 cv2 vt2)
           (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                   ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                   ; redM = mkRed3 (HeadRed-trans hr1 (Red3.hr (REqValTyPi.redM core)))
                                   (conv-trans cv1 (Red3.ct (REqValTyPi.redM core)))
                   ; redN = mkRed3 (HeadRed-trans hr2 (Red3.hr (REqValTyPi.redN core)))
                                   (conv-trans cv2 (Red3.ct (REqValTyPi.redN core)))
                   ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                   ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                   ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))
  EqValTy2-headred-expand (SigmaCode b f) hr1 hr2 cv1 cv2 eqvt =
    let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
    in mkSigma (ValTy2-headred-expand (SigmaCode b f) hr1 cv1 vt1)
         (mkSigma (ValTy2-headred-expand (SigmaCode b f) hr2 cv2 vt2)
           (record { domA = REqValTySigma.domA core ; codB = REqValTySigma.codB core
                   ; domA' = REqValTySigma.domA' core ; codB' = REqValTySigma.codB' core
                   ; redM = mkRed3 (HeadRed-trans hr1 (Red3.hr (REqValTySigma.redM core)))
                                   (conv-trans cv1 (Red3.ct (REqValTySigma.redM core)))
                   ; redN = mkRed3 (HeadRed-trans hr2 (Red3.hr (REqValTySigma.redN core)))
                                   (conv-trans cv2 (Red3.ct (REqValTySigma.redN core)))
                   ; cohF = REqValTySigma.cohF core ; fmAllU = REqValTySigma.fmAllU core
                   ; convA = REqValTySigma.convA core ; convB = REqValTySigma.convB core
                   ; eqA = REqValTySigma.eqA core ; edgeET = REqValTySigma.edgeET core }))

  -- ValPi2-headred-expand (needed by EqVal2-headred-expand at FunEl/PiCode)
  ValPi2-headred-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M' M -> ConvTm G M' M T -> RValTyPi G T b f ->
    RValPi G M T g0 b f -> RValPi G M' T g0 b f
  ValPi2-headred-expand g0 b f hr cv vty vpiM =
    let A0    = RValPi.domA0 vpiM
        B0    = RValPi.codB0 vpiM
        redT  = RValPi.red vpiM
        uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
        htPiU = snd (typing-ConvTm (Red3.ct redT))
        ctPi  = conv-conv cv (Red3.ct redT) htPiU
    in record { domA0 = A0 ; codB0 = B0 ; red = redT
              ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
              ; appV = \ u v sel N htN valN ->
                  Val2-beta-expand v (EvalFun f u) (HeadRed-App hr)
                    (conv-App-fun htA0 htB0 ctPi htN)
                    (RValPi.appV vpiM u v sel N htN valN)
              ; appE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
                  let cvApp1 = conv-App-fun htA0 htB0 ctPi htN1
                      cvApp2-raw = conv-App-fun htA0 htB0 ctPi htN2
                      cvBN = subst1-cong-ConvTm htA0 htB0 htN1 htN2 cvN
                      htB0N1 = fst (typing-ConvTm cvBN)
                      cvApp2 = conv-conv cvApp2-raw (conv-sym cvBN) htB0N1
                  in EqVal2-headred-expand v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                       cvApp1 cvApp2
                       (RValPi.appE vpiM u v sel N1 N2 htN1 htN2 cvN eqN) }

  EqValPi2-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1' M1 -> HeadRed M2' M2 ->
    ConvTm G M1' M1 T -> ConvTm G M2' M2 T -> RValTyPi G T b f ->
    REqValPi G M1 M2 T g0 b f -> REqValPi G M1' M2' T g0 b f
  EqValPi2-headred-expand g0 b f hr1 hr2 cv1 cv2 vty epi =
    let A0    = REqValPi.domA0 epi
        B0    = REqValPi.codB0 epi
        redT  = REqValPi.red epi
        uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
        htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
        htPiU = snd (typing-ConvTm (Red3.ct redT))
        ctPi1 = conv-conv cv1 (Red3.ct redT) htPiU
        ctPi2 = conv-conv cv2 (Red3.ct redT) htPiU
    in record { domA0 = A0 ; codB0 = B0 ; red = redT
              ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
              ; appEV = \ u v sel P htP valP ->
                  EqVal2-headred-expand v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                    (conv-App-fun htA0 htB0 ctPi1 htP) (conv-App-fun htA0 htB0 ctPi2 htP)
                    (REqValPi.appEV epi u v sel P htP valP) }
