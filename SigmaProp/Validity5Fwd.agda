{-# OPTIONS --without-K #-}
module SigmaProp.Validity5Fwd where
open import SigmaProp.Validity5DownUpRestrict public

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
  HasType ; ConvTm ; WfCtx ;
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
  bU-from-cf-fmFun ; FinMem-Coherent)
open import SigmaProp.SubstitutionLemmaSigma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Val2-EqValTy2-fwd, EqVal2-EqValTy2-fwd, and EqValTy2-sym.
--
-- Mechanical port from Validity4.agda lines 2350-2700, with only
-- record/field name changes:
--   RValPair -> RValSigma, REqValPair -> REqValSigma
--   .cohU -> .cohW1, .fmU -> .fmW1
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
    (a : FinEl) -> Coherent a -> EqValTy2 G M N a -> EqValTy2 G N M a

  Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    Val2 G M C u b -> Val2 G M C' u b

  EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    EqVal2 G M N C u b -> EqVal2 G M N C' u b

  ------------------------------------------------------------------
  -- EqValTy2-sym
  ------------------------------------------------------------------

  EqValTy2-sym Bot ca ev = tt
  EqValTy2-sym UCode ca ev = mkSigma (snd ev) (fst ev)
  EqValTy2-sym PropCode ca ev = mkSigma (snd ev) (fst ev)
  EqValTy2-sym (FunEl g) ca ev = tt
  EqValTy2-sym (PairCode u v) ca ev = tt
  EqValTy2-sym (PiCode b f) ca (mkSigma vtyM (mkSigma vtyN core)) =
    mkSigma vtyN (mkSigma vtyM (record
      { domA = REqValTyPi.domA' core ; codB = REqValTyPi.codB' core
      ; domA' = REqValTyPi.domA core ; codB' = REqValTyPi.codB core
      ; redM = REqValTyPi.redN core ; redN = REqValTyPi.redM core
      ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
      ; convA = conv-sym (REqValTyPi.convA core)
      ; convB = let htA-e = Eq-transport (\ X -> HasType _ X _)
                             (fst (Red3-unique-Pi (RValTyPi.red vtyM) (REqValTyPi.redM core)))
                             (RValTyPi.htA vtyM)
                    htA'-e = Eq-transport (\ X -> HasType _ X _)
                              (fst (Red3-unique-Pi (RValTyPi.red vtyN) (REqValTyPi.redN core)))
                              (RValTyPi.htA vtyN)
                in ctx-conv-ConvTm htA-e htA'-e (REqValTyPi.convA core) (conv-sym (REqValTyPi.convB core))
      ; eqA = EqValTy2-sym b (fst ca) (REqValTyPi.eqA core)
      ; edgeET = \ u' v' sel P htP valP ->
          let htA'-e = Eq-transport (\ X -> HasType _ X _)
                         (fst (Red3-unique-Pi (RValTyPi.red vtyN) (REqValTyPi.redN core)))
                         (RValTyPi.htA vtyN)
              htA-e = Eq-transport (\ X -> HasType _ X _)
                        (fst (Red3-unique-Pi (RValTyPi.red vtyM) (REqValTyPi.redM core)))
                        (RValTyPi.htA vtyM)
              htP-A = ty-conv htP (conv-sym (REqValTyPi.convA core)) htA-e
              valP-A = Val2-EqValTy2-fwd u' b (fst ca) (EqValTy2-sym b (fst ca) (REqValTyPi.eqA core)) valP
          in EqValTy2-sym v' (Coherent-Selection-val sel (REqValTyPi.cohF core))
               (REqValTyPi.edgeET core u' v' sel P htP-A valP-A)
      }))
  EqValTy2-sym (SigmaCode b f) ca (mkSigma vtyM (mkSigma vtyN core)) =
    mkSigma vtyN (mkSigma vtyM (record
      { domA = REqValTySigma.domA' core ; codB = REqValTySigma.codB' core
      ; domA' = REqValTySigma.domA core ; codB' = REqValTySigma.codB core
      ; redM = REqValTySigma.redN core ; redN = REqValTySigma.redM core
      ; cohF = REqValTySigma.cohF core ; fmAllU = REqValTySigma.fmAllU core
      ; convA = conv-sym (REqValTySigma.convA core)
      ; convB = let htA-e = Eq-transport (\ X -> HasType _ X _)
                             (fst (Red3-unique-Sigma (RValTySigma.red vtyM) (REqValTySigma.redM core)))
                             (RValTySigma.htA vtyM)
                    htA'-e = Eq-transport (\ X -> HasType _ X _)
                              (fst (Red3-unique-Sigma (RValTySigma.red vtyN) (REqValTySigma.redN core)))
                              (RValTySigma.htA vtyN)
                in ctx-conv-ConvTm htA-e htA'-e (REqValTySigma.convA core) (conv-sym (REqValTySigma.convB core))
      ; eqA = EqValTy2-sym b (fst ca) (REqValTySigma.eqA core)
      ; edgeET = \ u' v' sel P htP valP ->
          let htA'-e = Eq-transport (\ X -> HasType _ X _)
                         (fst (Red3-unique-Sigma (RValTySigma.red vtyN) (REqValTySigma.redN core)))
                         (RValTySigma.htA vtyN)
              htA-e = Eq-transport (\ X -> HasType _ X _)
                        (fst (Red3-unique-Sigma (RValTySigma.red vtyM) (REqValTySigma.redM core)))
                        (RValTySigma.htA vtyM)
              htP-A = ty-conv htP (conv-sym (REqValTySigma.convA core)) htA-e
              valP-A = Val2-EqValTy2-fwd u' b (fst ca) (EqValTy2-sym b (fst ca) (REqValTySigma.eqA core)) valP
          in EqValTy2-sym v' (Coherent-Selection-val sel (REqValTySigma.cohF core))
               (REqValTySigma.edgeET core u' v' sel P htP-A valP-A)
      }))

  ------------------------------------------------------------------
  -- Val2-EqValTy2-fwd
  ------------------------------------------------------------------

  -- Leaf cases: Val2 = Top on both sides, return tt
  Val2-EqValTy2-fwd u Bot cb eqv val = tt
  Val2-EqValTy2-fwd Bot UCode cb eqv val = tt
  Val2-EqValTy2-fwd PropCode UCode cb eqv val = mkSigma (snd eqv) (snd val)
  Val2-EqValTy2-fwd (PairCode u' v') UCode cb eqv val = tt
  Val2-EqValTy2-fwd Bot PropCode cb eqv val = tt
  Val2-EqValTy2-fwd UCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd PropCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv val = mkSigma (snd eqv) (snd val)
  Val2-EqValTy2-fwd (SigmaCode a' f') PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') PropCode cb eqv val = tt
  Val2-EqValTy2-fwd u (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv val = tt
  -- UCode cases: Val2 = Pair (ValTy2 G C UCode) (ValTy2 G M u), transport first component via eqv
  Val2-EqValTy2-fwd UCode UCode cb eqv val = mkSigma (snd eqv) (snd val)
  Val2-EqValTy2-fwd (FunEl g) UCode cb eqv val = val
  Val2-EqValTy2-fwd (PiCode a' f') UCode cb eqv val = mkSigma (snd eqv) (snd val)
  Val2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv val = mkSigma (snd eqv) (snd val)
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        convEE' = REqValTyPi.convA core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        -- htE : HasType G E U from vtyC
        redCv = RValTyPi.red vtyC
        htAc  = RValTyPi.htA vtyC
        uniqC2 = Red3-unique-Pi redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        -- Extract from val : Val2 G M C (FunEl g) (PiCode b0 f0)
        vpiM = snd val
        A0   = RValPi.domA0 vpiM
        B0   = RValPi.codB0 vpiM
        redC = RValPi.red vpiM
        cg   = RValPi.cohG vpiM
        fmg  = RValPi.fmG vpiM
        pav  = RValPi.appV vpiM
        pae  = RValPi.appE vpiM
        uniq = Red3-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        pav-EF : PiAppVal2 _ _ E F b0 f0 g
        pav-EF = Eq-transport (\ X -> PiAppVal2 _ _ X F b0 f0 g) eqA0E
                   (Eq-transport (\ Y -> PiAppVal2 _ _ A0 Y b0 f0 g) eqB0F pav)
        pae-EF : PiAppEq2 _ _ E F b0 f0 g
        pae-EF = Eq-transport (\ X -> PiAppEq2 _ _ X F b0 f0 g) eqA0E
                   (Eq-transport (\ Y -> PiAppEq2 _ _ A0 Y b0 f0 g) eqB0F pae)
        cb0 = fst cb
        b0U = bU-from-cf-fmFun g b0 f0 cg fmg
        ctg  = cft-from-cf g cg
        pav-E'F' : PiAppVal2 _ _ E' F' b0 f0 g
        pav-E'F' = \ u' v' sel N htN valN ->
          let htN-E  = ty-conv htN (conv-sym convEE') htE
              valN-E = Val2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) valN
              body   = pav-EF u' v' sel N htN-E valN-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valN-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu' valN-E
              eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N) (subst1 F' N) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in Val2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        pae-E'F' : PiAppEq2 _ _ E' F' b0 f0 g
        pae-E'F' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
          let htN1-E = ty-conv htN1 (conv-sym convEE') htE
              htN2-E = ty-conv htN2 (conv-sym convEE') htE
              cvN-E  = conv-conv cvN (conv-sym convEE') htE
              eqN-E  = EqVal2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) eqN
              body   = pae-EF u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valN1-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu'
                           (Val2-from-EqVal2-first u' b0 eqN-E)
              eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N1) (subst1 F' N1) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        vpi' = record
          { domA0 = E' ; codB0 = F' ; red = rC'
          ; cohG = cg ; fmG = fmg
          ; appV = pav-E'F' ; appE = pae-E'F'
          }
    in mkSigma vtyC' vpi'
  -- SigmaCode cases for Val2-EqValTy2-fwd
  Val2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTySigma.domA core
        F     = REqValTySigma.codB core
        E'    = REqValTySigma.domA' core
        F'    = REqValTySigma.codB' core
        rC    = REqValTySigma.redM core
        rC'   = REqValTySigma.redN core
        cf0   = REqValTySigma.cohF core
        fmU   = REqValTySigma.fmAllU core
        convEE' = REqValTySigma.convA core
        eqE   = REqValTySigma.eqA core
        vpair = snd val
        redC  = RValSigma.red vpair
        uniq  = Red3-unique-Sigma redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        -- htE from vtyC
        redCv = RValTySigma.red vtyC
        htAc  = RValTySigma.htA vtyC
        uniqC2 = Red3-unique-Sigma redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        cb0   = fst cb
        ctg-dummy = cf0  -- using cohF from the core
        -- Transport Fst/Snd validity through the type equality
        valFst-E = RValSigma.valFst vpair
        valFst-E' = Eq-transport (\ X -> Val2 _ _ X u' b0) eqA0E valFst-E
        valFst-E'2 = Val2-EqValTy2-fwd u' b0 cb0 eqE valFst-E'
        redC'v = RValTySigma.red vtyC'
        htAc'  = RValTySigma.htA vtyC'
        uniqC2' = Red3-unique-Sigma redC'v rC'
        htE'   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2') htAc'
        htFst-E = RValSigma.htFst vpair
        htFst-E' = Eq-transport (\ X -> HasType _ _ X) eqA0E htFst-E
        htFst-E'2 = ty-conv htFst-E' convEE' htE'
        vpair' = record
          { domA   = E' ; codB = F'
          ; red    = rC'
          ; htFst  = htFst-E'2
          ; cohW1  = RValSigma.cohW1 vpair
          ; fmW1   = RValSigma.fmW1 vpair
          ; valFst = valFst-E'2
          ; valSnd = let valSnd-F = RValSigma.valSnd vpair
                         valSnd-F' = Eq-transport (\ X -> Val2 _ _ (subst1 X _) v' (EvalFun f0 u')) eqB0F valSnd-F
                         pet = REqValTySigma.edgeET core
                         cu' = RValSigma.cohW1 vpair
                         sb  = selectionBelow f0 u' cf0 cu'
                         u-f = fst sb
                         v-f = fst (snd sb)
                         sel-f = fst (snd (snd sb))
                         le-uf = fst (snd (snd (snd sb)))
                         eq-ef = snd (snd (snd (snd sb)))
                         b0U = RValTySigma.fmBU vtyC
                         b0U' = RValTySigma.fmBU vtyC
                         fmu-f = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U'
                         valFst-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f (RValSigma.fmW1 vpair) valFst-E'
                         eqt-vf = pet u-f v-f sel-f (Fst _) htFst-E' valFst-uf
                         eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F (Fst _)) (subst1 F' (Fst _)) w)
                                    (Eq-sym eq-ef) eqt-vf
                         cev = Coherent-EvalFun f0 u' cf0 cu'
                     in Val2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef valSnd-F'
          }
    in mkSigma vtyC' vpair'
  Val2-EqValTy2-fwd u (PairCode x y) cb eqv val = tt

  ------------------------------------------------------------------
  -- EqVal2-EqValTy2-fwd
  ------------------------------------------------------------------

  -- Leaf cases: EqVal2 = Top on both sides, return tt
  EqVal2-EqValTy2-fwd u Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
  EqVal2-EqValTy2-fwd (PairCode u' v') UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd UCode PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd PropCode PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (FunEl g) PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv ev = mkSigma (snd eqv) (snd ev)
  EqVal2-EqValTy2-fwd (SigmaCode a' f') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PairCode u' v') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd u (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv ev = tt
  -- UCode cases: transport ValTy2 G C UCode -> ValTy2 G C' UCode via eqv
  EqVal2-EqValTy2-fwd UCode UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
  EqVal2-EqValTy2-fwd (FunEl g) UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PiCode a' f') UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
  EqVal2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  EqVal2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv ev =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        convEE'-eq = REqValTyPi.convA core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        -- htE : HasType G E U from vtyC
        redCv-eq = RValTyPi.red vtyC
        htAc-eq = RValTyPi.htA vtyC
        uniqC2-eq = Red3-unique-Pi redCv-eq rC
        htE-eq  = Eq-transport (\ X -> HasType _ X _) (fst uniqC2-eq) htAc-eq
        -- ev : EqVal2 G M N C (FunEl g) (PiCode b0 f0)
        vtyC-ev = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        epi  = snd (snd (snd ev))
        A0    = REqValPi.domA0 epi
        B0    = REqValPi.codB0 epi
        redC  = REqValPi.red epi
        cg    = REqValPi.cohG epi
        fmg   = REqValPi.fmG epi
        paev  = REqValPi.appEV epi
        uniq = Red3-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        cb0 = fst cb
        b0U = bU-from-cf-fmFun g b0 f0 cg fmg
        paev-EF : PiAppEqVal2 _ _ _ E F b0 f0 g
        paev-EF = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X F b0 f0 g) eqA0E
                    (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ A0 Y b0 f0 g) eqB0F paev)
        ctg  = cft-from-cf g cg
        paev-E'F' : PiAppEqVal2 _ _ _ E' F' b0 f0 g
        paev-E'F' = \ u' v' sel P htP valP ->
          let htP-E  = ty-conv htP (conv-sym convEE'-eq) htE-eq
              valP-E = Val2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) valP
              body   = paev-EF u' v' sel P htP-E valP-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valP-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu' valP-E
              eqt-vf = pet u-f v-f sel-f P htP-E valP-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F P) (subst1 F' P) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        -- Build Val2 G M C' and Val2 G N C'
        valM-C  = Val2-from-EqVal2-first (FunEl g) (PiCode b0 f0) ev
        valN-C  = Val2-from-EqVal2-second (FunEl g) (PiCode b0 f0) ev
        valM-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valM-C
        valN-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valN-C
        eqvpi-C' = record
          { domA0 = E' ; codB0 = F' ; red = rC'
          ; cohG = cg ; fmG = fmg ; appEV = paev-E'F'
          }
    in mkSigma vtyC' (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqvpi-C'))
  -- SigmaCode EqVal2-EqValTy2-fwd
  EqVal2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv ev =
    let valM-C  = Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b0 f0) ev
        valN-C  = Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b0 f0) ev
        valM-C' = Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv valM-C
        valN-C' = Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv valN-C
        eqp    = snd (snd (snd ev))
        core   = snd (snd eqv)
        uniqE  = Red3-unique-Sigma (REqValSigma.red eqp) (REqValTySigma.redM core)
        eqFst' = EqVal2-EqValTy2-fwd u' b0 (fst cb) (REqValTySigma.eqA core)
                   (Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X u' b0) (fst uniqE)
                     (REqValSigma.eqFst eqp))
        -- htFstM needs to go from REqValSigma.domA to REqValTySigma.domA' via convA
        vtyC  = fst eqv
        htAc  = RValTySigma.htA vtyC
        uniqC = Red3-unique-Sigma (RValTySigma.red vtyC) (REqValTySigma.redM core)
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC) htAc
        vtyC' = fst (snd eqv)
        htAc' = RValTySigma.htA vtyC'
        uniqC' = Red3-unique-Sigma (RValTySigma.red vtyC') (REqValTySigma.redN core)
        htE'  = Eq-transport (\ X -> HasType _ X _) (fst uniqC') htAc'
        htFstM-E = Eq-transport (\ X -> HasType _ _ X) (fst uniqE) (REqValSigma.htFstM eqp)
        htFstM-E' = ty-conv htFstM-E (REqValTySigma.convA core) htE'
        htFstN-E = Eq-transport (\ X -> HasType _ _ X) (fst uniqE) (REqValSigma.htFstN eqp)
        htFstN-E' = ty-conv htFstN-E (REqValTySigma.convA core) htE'
        -- Compute Val2-EqValTy2-fwd separately for REqValSigma M/N fields
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq-C' = Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv (mkSigma (fst ev) vpairM-eq)
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq-C' = Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv (mkSigma (fst ev) vpairN-eq)
        eqp'   = record
          { domA    = REqValTySigma.domA' core ; codB = REqValTySigma.codB' core
          ; red     = REqValTySigma.redN core
          ; htFstM  = RValSigma.htFst (snd valM-eq-C')
          ; cohW1   = REqValSigma.cohW1 eqp
          ; fmW1    = REqValSigma.fmW1 eqp
          ; valFstM = RValSigma.valFst (snd valM-eq-C')
          ; valSndM = RValSigma.valSnd (snd valM-eq-C')
          ; htFstN  = RValSigma.htFst (snd valN-eq-C')
          ; valFstN = RValSigma.valFst (snd valN-eq-C')
          ; valSndN = RValSigma.valSnd (snd valN-eq-C')
          ; eqFst   = eqFst'
          }
    in mkSigma (fst valM-C') (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqp'))
  EqVal2-EqValTy2-fwd u (PairCode x y) cb eqv ev = tt
