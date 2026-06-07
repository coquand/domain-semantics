{-# OPTIONS --without-K #-}
module SigmaProp.Validity5Lemmas where
open import SigmaProp.Validity5Sup public

import SigmaProp.BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              codeFst ; codeSnd)
import SigmaProp.RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ; Fst ; Snd ; MkPair ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import SigmaProp.TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Prop-U ;
  conv-Pi ; conv-Sigma ; conv-Fst ; conv-Snd ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-Sigma ; ty-Fst ; ty-Snd ; ty-App)
open import SigmaProp.ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma ;
  HeadRed-unique-Pi ; HeadRed-unique-Sigma)
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
open import SigmaProp.SubstitutionLemmaSigma using (typing-ConvTm ; typing-type ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Lemma 1: Val2-type-transport
--
-- Transport Val2 along EqValTy2 in the type parameter C.
-- By induction on a, then case split on u where needed.
-- Note: Val2-EqValTy2-fwd in Validity5Fwd does the same job but
-- requires a Coherent argument. Val2-type-transport drops that
-- requirement since Coherent is only used for the recursive calls
-- through selectionBelow/restrictVal2 (which themselves supply it).
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  Val2-type-transport : {n : Nat} {G : Ctx n} {C C' N : Expr n}
    (u a : FinEl) -> EqValTy2 G C C' a -> Val2 G N C u a -> Val2 G N C' u a

  -- a = Bot: Val2 = Top for all u
  Val2-type-transport u Bot eqvt val = tt

  -- a = UCode: transport ValTy2 G C UCode -> ValTy2 G C' UCode via eqvt
  Val2-type-transport Bot UCode eqvt val = tt
  Val2-type-transport UCode UCode eqvt val = mkSigma (snd eqvt) (snd val)
  Val2-type-transport PropCode UCode eqvt val = mkSigma (snd eqvt) (snd val)
  Val2-type-transport (FunEl g) UCode eqvt val = tt
  Val2-type-transport (PiCode a' f') UCode eqvt val = mkSigma (snd eqvt) (snd val)
  Val2-type-transport (SigmaCode a' f') UCode eqvt val = mkSigma (snd eqvt) (snd val)
  Val2-type-transport (PairCode u' v') UCode eqvt val = tt

  -- a = PropCode: Val2 = Top for most u; ValTy2 for PiCode (independent of C)
  Val2-type-transport Bot PropCode eqvt val = tt
  Val2-type-transport UCode PropCode eqvt val = tt
  Val2-type-transport PropCode PropCode eqvt val = tt
  Val2-type-transport (FunEl g) PropCode eqvt val = tt
  Val2-type-transport (PiCode a' f') PropCode eqvt val = mkSigma (snd eqvt) (snd val)
  Val2-type-transport (SigmaCode a' f') PropCode eqvt val = tt
  Val2-type-transport (PairCode u' v') PropCode eqvt val = tt

  -- a = FunEl: Val2 = Top
  Val2-type-transport u (FunEl h) eqvt val = tt

  -- a = PiCode b f, u = FunEl g: non-trivial case
  Val2-type-transport (FunEl g) (PiCode b f) eqvt val =
    let vtyC  = fst eqvt
        vtyC' = fst (snd eqvt)
        core  = snd (snd eqvt)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        convEE' = REqValTyPi.convA core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        -- htE from vtyC
        redCv = RValTyPi.red vtyC
        htAc  = RValTyPi.htA vtyC
        uniqC2 = Red3-unique-Pi redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        -- Extract from val : Pair (ValTy2 G C (PiCode b f)) (RValPi G N C g b f)
        vpiN  = snd val
        A0    = RValPi.domA0 vpiN
        B0    = RValPi.codB0 vpiN
        redC  = RValPi.red vpiN
        cg    = RValPi.cohG vpiN
        fmg   = RValPi.fmG vpiN
        pav   = RValPi.appV vpiN
        pae   = RValPi.appE vpiN
        -- Pi-uniqueness between redC and rC
        uniq  = Red3-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        -- Transport appV/appE from (A0, B0) to (E, F)
        pav-EF : PiAppVal2 _ _ E F b f g
        pav-EF = Eq-transport (\ X -> PiAppVal2 _ _ X F b f g) eqA0E
                   (Eq-transport (\ Y -> PiAppVal2 _ _ A0 Y b f g) eqB0F pav)
        pae-EF : PiAppEq2 _ _ E F b f g
        pae-EF = Eq-transport (\ X -> PiAppEq2 _ _ X F b f g) eqA0E
                   (Eq-transport (\ Y -> PiAppEq2 _ _ A0 Y b f g) eqB0F pae)
        -- Build appV/appE for (E', F')
        ctg  = cft-from-cf g cg
        b0U  = bU-from-cf-fmFun g b f cg fmg
        pav-E'F' : PiAppVal2 _ _ E' F' b f g
        pav-E'F' = \ u' v' sel N htN valN ->
          let htN-E  = ty-conv htN (conv-sym convEE') htE
              cu'    = Coherent-Selection sel ctg
              cb0'   = coh-from-aU b b0U
              valN-E = Val2-type-transport u' b (EqValTy2-sym b cb0' eqE) valN
              body   = pav-EF u' v' sel N htN-E valN-E
              sb     = selectionBelow f u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
              fmu'   = FinMem-Selection b f sel fmg ctg cb0' b0U
              valN-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f fmu' valN-E
              eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N) (subst1 F' N) w)
                         (Eq-sym eq-ef) eqt-vf
          in Val2-type-transport v' (EvalFun f u') eqt-ef body
        pae-E'F' : PiAppEq2 _ _ E' F' b f g
        pae-E'F' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
          let htN1-E = ty-conv htN1 (conv-sym convEE') htE
              htN2-E = ty-conv htN2 (conv-sym convEE') htE
              cvN-E  = conv-conv cvN (conv-sym convEE') htE
              cu'    = Coherent-Selection sel ctg
              cb0'   = coh-from-aU b b0U
              eqN-E  = EqVal2-type-transport u' b (EqValTy2-sym b cb0' eqE) eqN
              body   = pae-EF u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
              sb     = selectionBelow f u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
              fmu'   = FinMem-Selection b f sel fmg ctg cb0' b0U
              valN1-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f fmu'
                           (Val2-from-EqVal2-first u' b eqN-E)
              eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N1) (subst1 F' N1) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f u' cf0 cu'
          in EqVal2-type-transport v' (EvalFun f u') eqt-ef body
        vpi' = record
          { domA0 = E' ; codB0 = F' ; red = rC'
          ; cohG = cg ; fmG = fmg
          ; appV = pav-E'F' ; appE = pae-E'F'
          }
    in mkSigma vtyC' vpi'

  -- a = PiCode b f, u /= FunEl: Val2 = Top
  Val2-type-transport Bot (PiCode b f) eqvt val = tt
  Val2-type-transport UCode (PiCode b f) eqvt val = tt
  Val2-type-transport PropCode (PiCode b f) eqvt val = tt
  Val2-type-transport (PiCode a' f') (PiCode b f) eqvt val = tt
  Val2-type-transport (SigmaCode a' f') (PiCode b f) eqvt val = tt
  Val2-type-transport (PairCode u' v') (PiCode b f) eqvt val = tt

  -- a = SigmaCode b f, u = PairCode u' v': non-trivial case
  Val2-type-transport (PairCode u' v') (SigmaCode b f) eqvt val =
    let vtyC  = fst eqvt
        vtyC' = fst (snd eqvt)
        core  = snd (snd eqvt)
        E     = REqValTySigma.domA core
        F     = REqValTySigma.codB core
        E'    = REqValTySigma.domA' core
        F'    = REqValTySigma.codB' core
        rC    = REqValTySigma.redM core
        rC'   = REqValTySigma.redN core
        convEE' = REqValTySigma.convA core
        eqE   = REqValTySigma.eqA core
        cf0   = REqValTySigma.cohF core
        fmU   = REqValTySigma.fmAllU core
        pet   = REqValTySigma.edgeET core
        -- Extract from val
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
        b0U   = RValTySigma.fmBU vtyC
        cb0   = coh-from-aU b b0U
        -- Transport valFst from old domA to E then to E'
        valFst-E = Eq-transport (\ X -> Val2 _ _ X u' b) eqA0E (RValSigma.valFst vpair)
        valFst-E' = Val2-type-transport u' b eqE valFst-E
        -- htFst transport
        htFst-E = Eq-transport (\ X -> HasType _ _ X) eqA0E (RValSigma.htFst vpair)
        redC'v = RValTySigma.red vtyC'
        htAc'  = RValTySigma.htA vtyC'
        uniqC2' = Red3-unique-Sigma redC'v rC'
        htE'   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2') htAc'
        htFst-E' = ty-conv htFst-E convEE' htE'
        -- Transport valSnd: need EqValTy2 for codomain at Fst N
        valSnd-F = Eq-transport (\ X -> Val2 _ _ (subst1 X _) v' (EvalFun f u'))
                     eqB0F (RValSigma.valSnd vpair)
        cu'  = RValSigma.cohW1 vpair
        sb   = selectionBelow f u' cf0 cu'
        u-f  = fst sb
        v-f  = fst (snd sb)
        sel-f = fst (snd (snd sb))
        le-uf = fst (snd (snd (snd sb)))
        eq-ef = snd (snd (snd (snd sb)))
        fmu-f = FinMemAllU-Selection b sel-f fmU cf0 cb0 b0U
        valFst-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f (RValSigma.fmW1 vpair) valFst-E
        eqt-vf = pet u-f v-f sel-f (Fst _) htFst-E valFst-uf
        eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F (Fst _)) (subst1 F' (Fst _)) w)
                   (Eq-sym eq-ef) eqt-vf
        cev = Coherent-EvalFun f u' cf0 cu'
        valSnd-F' = Val2-type-transport v' (EvalFun f u') eqt-ef valSnd-F
        vpair' = record
          { domA   = E' ; codB = F'
          ; red    = rC'
          ; htFst  = htFst-E'
          ; cohW1  = RValSigma.cohW1 vpair
          ; fmW1   = RValSigma.fmW1 vpair
          ; valFst = valFst-E'
          ; valSnd = valSnd-F'
          }
    in mkSigma vtyC' vpair'

  -- a = SigmaCode b f, u /= PairCode: Val2 = Top
  Val2-type-transport Bot (SigmaCode b f) eqvt val = tt
  Val2-type-transport UCode (SigmaCode b f) eqvt val = tt
  Val2-type-transport PropCode (SigmaCode b f) eqvt val = tt
  Val2-type-transport (FunEl g) (SigmaCode b f) eqvt val = tt
  Val2-type-transport (PiCode a' f') (SigmaCode b f) eqvt val = tt
  Val2-type-transport (SigmaCode a' f') (SigmaCode b f) eqvt val = tt

  -- a = PairCode: Val2 = Top
  Val2-type-transport u (PairCode x y) eqvt val = tt

  --------------------------------------------------------------------------
  -- EqVal2-type-transport: same lemma for EqVal2
  --------------------------------------------------------------------------

  EqVal2-type-transport : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (u a : FinEl) -> EqValTy2 G C C' a -> EqVal2 G M N C u a -> EqVal2 G M N C' u a

  -- a = Bot
  EqVal2-type-transport u Bot eqvt ev = tt

  -- a = UCode: transport ValTy2 G C UCode -> ValTy2 G C' UCode via eqvt
  EqVal2-type-transport Bot UCode eqvt ev = tt
  EqVal2-type-transport UCode UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
  EqVal2-type-transport PropCode UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
  EqVal2-type-transport (FunEl g) UCode eqvt ev = tt
  EqVal2-type-transport (PiCode a' f') UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
  EqVal2-type-transport (SigmaCode a' f') UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
  EqVal2-type-transport (PairCode u' v') UCode eqvt ev = tt

  -- a = PropCode
  EqVal2-type-transport Bot PropCode eqvt ev = tt
  EqVal2-type-transport UCode PropCode eqvt ev = tt
  EqVal2-type-transport PropCode PropCode eqvt ev = tt
  EqVal2-type-transport (FunEl g) PropCode eqvt ev = tt
  EqVal2-type-transport (PiCode a' f') PropCode eqvt ev = mkSigma (snd eqvt) (snd ev)
  EqVal2-type-transport (SigmaCode a' f') PropCode eqvt ev = tt
  EqVal2-type-transport (PairCode u' v') PropCode eqvt ev = tt

  -- a = FunEl
  EqVal2-type-transport u (FunEl h) eqvt ev = tt

  -- a = PiCode b f, u = FunEl g: non-trivial case
  EqVal2-type-transport (FunEl g) (PiCode b f) eqvt ev =
    let vtyC  = fst eqvt
        vtyC' = fst (snd eqvt)
        core  = snd (snd eqvt)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        convEE' = REqValTyPi.convA core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        -- htE from vtyC
        redCv = RValTyPi.red vtyC
        htAc  = RValTyPi.htA vtyC
        uniqC2 = Red3-unique-Pi redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        -- Extract from ev : Pair vty (Pair vpiM (Pair vpiN eqpi))
        vtyEV = fst ev
        vpiM  = fst (snd ev)
        vpiN  = fst (snd (snd ev))
        eqpi  = snd (snd (snd ev))
        -- Helper: transport a single RValPi from E/F to E'/F'
        transportRValPi : {M : _} -> RValPi _ M _ g b f -> RValPi _ M _ g b f
        transportRValPi vpi =
          let uniqX = Red3-unique-Pi (RValPi.red vpi) rC
              pavX  = Eq-transport (\ X -> PiAppVal2 _ _ X F b f g) (fst uniqX)
                        (Eq-transport (\ Y -> PiAppVal2 _ _ _ Y b f g) (snd uniqX)
                          (RValPi.appV vpi))
              paeX  = Eq-transport (\ X -> PiAppEq2 _ _ X F b f g) (fst uniqX)
                        (Eq-transport (\ Y -> PiAppEq2 _ _ _ Y b f g) (snd uniqX)
                          (RValPi.appE vpi))
              cgX   = RValPi.cohG vpi
              fmgX  = RValPi.fmG vpi
              ctgX  = cft-from-cf g cgX
              b0U   = bU-from-cf-fmFun g b f cgX fmgX
              pavX' : PiAppVal2 _ _ E' F' b f g
              pavX' = \ u' v' sel N htN valN ->
                let htN-E  = ty-conv htN (conv-sym convEE') htE
                    cu'    = Coherent-Selection sel ctgX
                    cb0'   = coh-from-aU b b0U
                    valN-E = Val2-type-transport u' b (EqValTy2-sym b cb0' eqE) valN
                    body   = pavX u' v' sel N htN-E valN-E
                    sb     = selectionBelow f u' cf0 cu'
                    u-f    = fst sb
                    v-f    = fst (snd sb)
                    sel-f  = fst (snd (snd sb))
                    le-uf  = fst (snd (snd (snd sb)))
                    eq-ef  = snd (snd (snd (snd sb)))
                    fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                    fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                    valN-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f fmu' valN-E
                    eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
                    eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N) (subst1 F' N) w)
                               (Eq-sym eq-ef) eqt-vf
                    cev    = Coherent-EvalFun f u' cf0 cu'
                in Val2-type-transport v' (EvalFun f u') eqt-ef body
              paeX' : PiAppEq2 _ _ E' F' b f g
              paeX' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
                let htN1-E = ty-conv htN1 (conv-sym convEE') htE
                    htN2-E = ty-conv htN2 (conv-sym convEE') htE
                    cvN-E  = conv-conv cvN (conv-sym convEE') htE
                    cu'    = Coherent-Selection sel ctgX
                    cb0'   = coh-from-aU b b0U
                    eqN-E  = EqVal2-type-transport u' b (EqValTy2-sym b cb0' eqE) eqN
                    body   = paeX u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
                    sb     = selectionBelow f u' cf0 cu'
                    u-f    = fst sb
                    v-f    = fst (snd sb)
                    sel-f  = fst (snd (snd sb))
                    le-uf  = fst (snd (snd (snd sb)))
                    eq-ef  = snd (snd (snd (snd sb)))
                    fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                    fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                    valN1-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f fmu'
                                 (Val2-from-EqVal2-first u' b eqN-E)
                    eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
                    eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N1) (subst1 F' N1) w)
                               (Eq-sym eq-ef) eqt-vf
                    cev    = Coherent-EvalFun f u' cf0 cu'
                in EqVal2-type-transport v' (EvalFun f u') eqt-ef body
          in record
            { domA0 = E' ; codB0 = F' ; red = rC'
            ; cohG = cgX ; fmG = fmgX
            ; appV = pavX' ; appE = paeX'
            }
        -- Transport REqValPi
        transportREqValPi : REqValPi _ _ _ _ g b f -> REqValPi _ _ _ _ g b f
        transportREqValPi eqp =
          let uniqEq = Red3-unique-Pi (REqValPi.red eqp) rC
              paevX  = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X F b f g) (fst uniqEq)
                         (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ _ Y b f g) (snd uniqEq)
                           (REqValPi.appEV eqp))
              cgX   = REqValPi.cohG eqp
              fmgX  = REqValPi.fmG eqp
              ctgX  = cft-from-cf g cgX
              b0U   = bU-from-cf-fmFun g b f cgX fmgX
              paevX' : PiAppEqVal2 _ _ _ E' F' b f g
              paevX' = \ u' v' sel P htP valP ->
                let htP-E  = ty-conv htP (conv-sym convEE') htE
                    cu'    = Coherent-Selection sel ctgX
                    cb0'   = coh-from-aU b b0U
                    valP-E = Val2-type-transport u' b (EqValTy2-sym b cb0' eqE) valP
                    body   = paevX u' v' sel P htP-E valP-E
                    sb     = selectionBelow f u' cf0 cu'
                    u-f    = fst sb
                    v-f    = fst (snd sb)
                    sel-f  = fst (snd (snd sb))
                    le-uf  = fst (snd (snd (snd sb)))
                    eq-ef  = snd (snd (snd (snd sb)))
                    fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                    fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                    valP-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f fmu' valP-E
                    eqt-vf = pet u-f v-f sel-f P htP-E valP-uf
                    eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F P) (subst1 F' P) w)
                               (Eq-sym eq-ef) eqt-vf
                    cev    = Coherent-EvalFun f u' cf0 cu'
                in EqVal2-type-transport v' (EvalFun f u') eqt-ef body
          in record
            { domA0 = E' ; codB0 = F' ; red = rC'
            ; cohG = cgX ; fmG = fmgX
            ; appEV = paevX'
            }
    in mkSigma vtyC' (mkSigma (transportRValPi vpiM)
         (mkSigma (transportRValPi vpiN) (transportREqValPi eqpi)))

  -- a = PiCode b f, u /= FunEl: Top
  EqVal2-type-transport Bot (PiCode b f) eqvt ev = tt
  EqVal2-type-transport UCode (PiCode b f) eqvt ev = tt
  EqVal2-type-transport PropCode (PiCode b f) eqvt ev = tt
  EqVal2-type-transport (PiCode a' f') (PiCode b f) eqvt ev = tt
  EqVal2-type-transport (SigmaCode a' f') (PiCode b f) eqvt ev = tt
  EqVal2-type-transport (PairCode u' v') (PiCode b f) eqvt ev = tt

  -- a = SigmaCode b f, u = PairCode u' v': non-trivial case
  EqVal2-type-transport (PairCode u' v') (SigmaCode b f) eqvt ev =
    let vtyC  = fst eqvt
        vtyC' = fst (snd eqvt)
        core  = snd (snd eqvt)
        E     = REqValTySigma.domA core
        F     = REqValTySigma.codB core
        E'    = REqValTySigma.domA' core
        F'    = REqValTySigma.codB' core
        rC    = REqValTySigma.redM core
        rC'   = REqValTySigma.redN core
        convEE' = REqValTySigma.convA core
        eqE   = REqValTySigma.eqA core
        cf0   = REqValTySigma.cohF core
        fmU   = REqValTySigma.fmAllU core
        pet   = REqValTySigma.edgeET core
        -- htE from vtyC
        redCv = RValTySigma.red vtyC
        htAc  = RValTySigma.htA vtyC
        uniqC2 = Red3-unique-Sigma redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        b0U   = RValTySigma.fmBU vtyC
        cb0   = coh-from-aU b b0U
        -- htE' from vtyC'
        redC'v = RValTySigma.red vtyC'
        htAc'  = RValTySigma.htA vtyC'
        uniqC2' = Red3-unique-Sigma redC'v rC'
        htE'   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2') htAc'
        -- Extract from ev
        vtyEV = fst ev
        vsigM = fst (snd ev)
        vsigN = fst (snd (snd ev))
        eqsig = snd (snd (snd ev))
        -- Helper: transport a single RValSigma from E/F to E'/F'
        transportRValSigma : {M : _} -> RValSigma _ M _ (PairCode u' v') b f ->
                             RValSigma _ M _ (PairCode u' v') b f
        transportRValSigma vs =
          let uniqX = Red3-unique-Sigma (RValSigma.red vs) rC
              valFst-E = Eq-transport (\ X -> Val2 _ _ X u' b) (fst uniqX) (RValSigma.valFst vs)
              valFst-E' = Val2-type-transport u' b eqE valFst-E
              htFst-E = Eq-transport (\ X -> HasType _ _ X) (fst uniqX) (RValSigma.htFst vs)
              htFst-E' = ty-conv htFst-E convEE' htE'
              valSnd-F = Eq-transport (\ X -> Val2 _ _ (subst1 X _) v' (EvalFun f u'))
                           (snd uniqX) (RValSigma.valSnd vs)
              cu'  = RValSigma.cohW1 vs
              sb   = selectionBelow f u' cf0 cu'
              u-f  = fst sb
              v-f  = fst (snd sb)
              sel-f = fst (snd (snd sb))
              le-uf = fst (snd (snd (snd sb)))
              eq-ef = snd (snd (snd (snd sb)))
              fmu-f = FinMemAllU-Selection b sel-f fmU cf0 cb0 b0U
              valFst-uf = restrictVal2 _ _ E u' u-f b le-uf fmu-f (RValSigma.fmW1 vs) valFst-E
              eqt-vf = pet u-f v-f sel-f (Fst _) htFst-E valFst-uf
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F (Fst _)) (subst1 F' (Fst _)) w)
                         (Eq-sym eq-ef) eqt-vf
              cev = Coherent-EvalFun f u' cf0 cu'
              valSnd-F' = Val2-type-transport v' (EvalFun f u') eqt-ef valSnd-F
          in record
            { domA   = E' ; codB = F'
            ; red    = rC'
            ; htFst  = htFst-E'
            ; cohW1  = RValSigma.cohW1 vs
            ; fmW1   = RValSigma.fmW1 vs
            ; valFst = valFst-E'
            ; valSnd = valSnd-F'
            }
        -- Transport REqValSigma
        uniqEq = Red3-unique-Sigma (REqValSigma.red eqsig) rC
        eqFst-E = Eq-transport (\ X -> EqVal2 _ _ _ X u' b) (fst uniqEq) (REqValSigma.eqFst eqsig)
        eqFst-E' = EqVal2-type-transport u' b eqE eqFst-E
        vsigM' = transportRValSigma vsigM
        vsigN' = transportRValSigma vsigN
        eqsig' = record
          { domA    = E' ; codB = F'
          ; red     = rC'
          ; htFstM  = RValSigma.htFst vsigM'
          ; htFstN  = RValSigma.htFst vsigN'
          ; cohW1   = REqValSigma.cohW1 eqsig
          ; fmW1    = REqValSigma.fmW1 eqsig
          ; valFstM = RValSigma.valFst vsigM'
          ; valSndM = RValSigma.valSnd vsigM'
          ; valFstN = RValSigma.valFst vsigN'
          ; valSndN = RValSigma.valSnd vsigN'
          ; eqFst   = eqFst-E'
          }
    in mkSigma vtyC' (mkSigma vsigM' (mkSigma vsigN' eqsig'))

  -- a = SigmaCode b f, u /= PairCode: Top
  EqVal2-type-transport Bot (SigmaCode b f) eqvt ev = tt
  EqVal2-type-transport UCode (SigmaCode b f) eqvt ev = tt
  EqVal2-type-transport PropCode (SigmaCode b f) eqvt ev = tt
  EqVal2-type-transport (FunEl g) (SigmaCode b f) eqvt ev = tt
  EqVal2-type-transport (PiCode a' f') (SigmaCode b f) eqvt ev = tt
  EqVal2-type-transport (SigmaCode a' f') (SigmaCode b f) eqvt ev = tt

  -- a = PairCode: Top
  EqVal2-type-transport u (PairCode x y) eqvt ev = tt

  --------------------------------------------------------------------------
  -- Lemma 2: Val2-beta-expand (head-reduction transport)
  --
  -- Given HeadRed M M', ConvTm G M M' T, and Val2 G M' T u a,
  -- produce EqVal2 G M' M T u a (which bundles Val2 for both M' and M).
  -- By induction on a.
  --------------------------------------------------------------------------

  Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
    Val2 G M' T u a -> EqVal2 G M' M T u a

  -- a = Bot: trivial
  Val2-beta-expand u Bot hr ct val = tt

  -- a = UCode: by u
  Val2-beta-expand Bot UCode hr ct val = tt
  Val2-beta-expand (FunEl g) UCode hr ct val = tt
  Val2-beta-expand (PairCode u' v') UCode hr ct val = tt
  Val2-beta-expand PropCode UCode hr ct val =
    let vtA = fst val ; vtM' = snd val
        ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
        vtM = mkRed3 (HeadRed-trans hr (Red3.hr vtM')) (conv-trans ctU (Red3.ct vtM'))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtM (mkSigma vtM' vtM)))
  Val2-beta-expand UCode UCode hr ct val =
    let vtA = fst val ; vtM' = snd val
        ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
        vtM = mkRed3 (HeadRed-trans hr (Red3.hr vtM')) (conv-trans ctU (Red3.ct vtM'))
    in mkSigma vtA (mkSigma vtM' (mkSigma vtM (mkSigma vtM' vtM)))
  Val2-beta-expand (PiCode a' f') UCode hr ct val =
    let vtA = fst val ; vtPi = snd val
        ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
        newRed = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyPi.red vtPi)))
                        (conv-trans ctU (Red3.ct (RValTyPi.red vtPi)))
        vtM = record
          { domA = RValTyPi.domA vtPi ; codB = RValTyPi.codB vtPi ; red = newRed
          ; cohF = RValTyPi.cohF vtPi ; fmAllU = RValTyPi.fmAllU vtPi
          ; htA = RValTyPi.htA vtPi ; htB = RValTyPi.htB vtPi
          ; valA = RValTyPi.valA vtPi
          ; edgeV = RValTyPi.edgeV vtPi ; edgeE = RValTyPi.edgeE vtPi }
        edgeEqTy : PiEdgeEqTy2 _ (RValTyPi.domA vtPi) (RValTyPi.codB vtPi) (RValTyPi.codB vtPi) a' f'
        edgeEqTy = \ u0 v0 sel P htP valP ->
          ValTy2-to-EqValTy2 v0 (RValTyPi.edgeV vtPi u0 v0 sel P htP valP)
        coreEq = record
          { domA = RValTyPi.domA vtPi ; codB = RValTyPi.codB vtPi
          ; domA' = RValTyPi.domA vtPi ; codB' = RValTyPi.codB vtPi
          ; redM = RValTyPi.red vtPi ; redN = newRed
          ; cohF = RValTyPi.cohF vtPi ; fmAllU = RValTyPi.fmAllU vtPi
          ; convA = conv-refl (RValTyPi.htA vtPi) ; convB = conv-refl (RValTyPi.htB vtPi)
          ; eqA = ValTy2-to-EqValTy2 a' (RValTyPi.valA vtPi) ; edgeET = edgeEqTy }
    in mkSigma vtA (mkSigma vtPi (mkSigma vtM (mkSigma vtPi (mkSigma vtM coreEq))))
  Val2-beta-expand (SigmaCode a' f') UCode hr ct val =
    let vtA = fst val ; vtSig = snd val
        ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
        newRed = mkRed3 (HeadRed-trans hr (Red3.hr (RValTySigma.red vtSig)))
                        (conv-trans ctU (Red3.ct (RValTySigma.red vtSig)))
        vtM = record
          { domA = RValTySigma.domA vtSig ; codB = RValTySigma.codB vtSig ; red = newRed
          ; cohF = RValTySigma.cohF vtSig ; fmAllU = RValTySigma.fmAllU vtSig
          ; fmBU = RValTySigma.fmBU vtSig
          ; htA = RValTySigma.htA vtSig ; htB = RValTySigma.htB vtSig
          ; valA = RValTySigma.valA vtSig
          ; edgeV = RValTySigma.edgeV vtSig ; edgeE = RValTySigma.edgeE vtSig }
        edgeEqTy : SigmaEdgeEqTy2 _ (RValTySigma.domA vtSig) (RValTySigma.codB vtSig) (RValTySigma.codB vtSig) a' f'
        edgeEqTy = \ u0 v0 sel P htP valP ->
          ValTy2-to-EqValTy2 v0 (RValTySigma.edgeV vtSig u0 v0 sel P htP valP)
        coreEq = record
          { domA = RValTySigma.domA vtSig ; codB = RValTySigma.codB vtSig
          ; domA' = RValTySigma.domA vtSig ; codB' = RValTySigma.codB vtSig
          ; redM = RValTySigma.red vtSig ; redN = newRed
          ; cohF = RValTySigma.cohF vtSig ; fmAllU = RValTySigma.fmAllU vtSig
          ; convA = conv-refl (RValTySigma.htA vtSig) ; convB = conv-refl (RValTySigma.htB vtSig)
          ; eqA = ValTy2-to-EqValTy2 a' (RValTySigma.valA vtSig) ; edgeET = edgeEqTy }
    in mkSigma vtA (mkSigma vtSig (mkSigma vtM (mkSigma vtSig (mkSigma vtM coreEq))))

  -- a = PropCode: same pattern via conv-Prop-U
  Val2-beta-expand Bot PropCode hr ct val = tt
  Val2-beta-expand UCode PropCode hr ct val = tt
  Val2-beta-expand PropCode PropCode hr ct val = tt
  Val2-beta-expand (FunEl g) PropCode hr ct val = tt
  Val2-beta-expand (SigmaCode a' f') PropCode hr ct val = tt
  Val2-beta-expand (PairCode u' v') PropCode hr ct val = tt
  Val2-beta-expand (PiCode a' f') PropCode hr ct val =
    let vtA = fst val ; vtPi = snd val
        ctU = conv-Prop-U (conv-conv ct (Red3.ct vtA) (snd (typing-ConvTm (Red3.ct vtA))))
        newRed = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyPi.red vtPi)))
                        (conv-trans ctU (Red3.ct (RValTyPi.red vtPi)))
        vtM = record
          { domA = RValTyPi.domA vtPi ; codB = RValTyPi.codB vtPi ; red = newRed
          ; cohF = RValTyPi.cohF vtPi ; fmAllU = RValTyPi.fmAllU vtPi
          ; htA = RValTyPi.htA vtPi ; htB = RValTyPi.htB vtPi
          ; valA = RValTyPi.valA vtPi
          ; edgeV = RValTyPi.edgeV vtPi ; edgeE = RValTyPi.edgeE vtPi }
        edgeEqTy : PiEdgeEqTy2 _ (RValTyPi.domA vtPi) (RValTyPi.codB vtPi) (RValTyPi.codB vtPi) a' f'
        edgeEqTy = \ u0 v0 sel P htP valP ->
          ValTy2-to-EqValTy2 v0 (RValTyPi.edgeV vtPi u0 v0 sel P htP valP)
        coreEq = record
          { domA = RValTyPi.domA vtPi ; codB = RValTyPi.codB vtPi
          ; domA' = RValTyPi.domA vtPi ; codB' = RValTyPi.codB vtPi
          ; redM = RValTyPi.red vtPi ; redN = newRed
          ; cohF = RValTyPi.cohF vtPi ; fmAllU = RValTyPi.fmAllU vtPi
          ; convA = conv-refl (RValTyPi.htA vtPi) ; convB = conv-refl (RValTyPi.htB vtPi)
          ; eqA = ValTy2-to-EqValTy2 a' (RValTyPi.valA vtPi) ; edgeET = edgeEqTy }
    in mkSigma vtA (mkSigma vtPi (mkSigma vtM (mkSigma vtPi (mkSigma vtM coreEq))))

  -- a = FunEl: trivial
  Val2-beta-expand u (FunEl h) hr ct val = tt

  -- a = PiCode b f: by u (PDF §6.1)
  Val2-beta-expand Bot (PiCode b f) hr ct val = tt
  Val2-beta-expand UCode (PiCode b f) hr ct val = tt
  Val2-beta-expand PropCode (PiCode b f) hr ct val = tt
  Val2-beta-expand (PiCode a' f') (PiCode b f) hr ct val = tt
  Val2-beta-expand (SigmaCode a' f') (PiCode b f) hr ct val = tt
  Val2-beta-expand (PairCode u' v') (PiCode b f) hr ct val = tt
  Val2-beta-expand (FunEl g) (PiCode b f) hr ct val =
    let vty   = fst val
        vpiM' = snd val
        A0    = RValPi.domA0 vpiM'
        B0    = RValPi.codB0 vpiM'
        redT  = RValPi.red vpiM'
        -- Get htA0 htB0 at A0 B0 (transport from vty coordinates)
        uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
        htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
        htB0  = Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                  (Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
        htPiU = snd (typing-ConvTm (Red3.ct redT))
        ctPi  = conv-conv ct (Red3.ct redT) htPiU
        -- appV for M: IH at each selection point
        appVM : PiAppVal2 _ _ A0 B0 b f g
        appVM = \ u0 v0 sel N htN valN ->
          Val2-from-EqVal2-second v0 (EvalFun f u0)
            (Val2-beta-expand v0 (EvalFun f u0) (HeadRed-App hr)
              (conv-App-fun htA0 htB0 ctPi htN)
              (RValPi.appV vpiM' u0 v0 sel N htN valN))
        -- appE for M
        cf-vty = RValTyPi.cohF vty
        cg-vpi = RValPi.cohG vpiM'
        ctg    = cft-from-cf g cg-vpi
        bU-pi  = bU-from-cf-fmFun g b f cg-vpi (RValPi.fmG vpiM')
        cb-pi  = coh-from-aU b bU-pi
        -- Transport edge from vty coords to A0/B0
        piEE-A0 : PiEdgeEq2 _ A0 B0 b f
        piEE-A0 = Eq-transport (\ Y -> PiEdgeEq2 _ A0 Y b f) (snd uniq)
                    (Eq-transport (\ X -> PiEdgeEq2 _ X (RValTyPi.codB vty) b f) (fst uniq) (RValTyPi.edgeE vty))
        appEM : PiAppEq2 _ _ A0 B0 b f g
        appEM = \ u0 v0 sel N1 N2 htN1 htN2 cvN eqN ->
          let eqApp1 = Val2-beta-expand v0 (EvalFun f u0) (HeadRed-App hr)
                         (conv-App-fun htA0 htB0 ctPi htN1)
                         (RValPi.appV vpiM' u0 v0 sel N1 htN1 (Val2-from-EqVal2-first u0 b eqN))
              eqApp2-raw = Val2-beta-expand v0 (EvalFun f u0) (HeadRed-App hr)
                             (conv-App-fun htA0 htB0 ctPi htN2)
                             (RValPi.appV vpiM' u0 v0 sel N2 htN2 (Val2-from-EqVal2-second u0 b eqN))
              -- Transport eqApp2 from subst1 B0 N2 to subst1 B0 N1 via edge+selectionBelow
              cu0 = Coherent-Selection sel ctg
              eqN-rev = EqVal2-sym u0 b cu0 cb-pi eqN
              sb  = selectionBelow f u0 cf-vty cu0
              u-f = fst sb ; v-f = fst (snd sb)
              sel-f = fst (snd (snd sb))
              le-uf = fst (snd (snd (snd sb)))
              eq-ef = snd (snd (snd (snd sb)))
              fmu-f = FinMemAllU-Selection b sel-f (RValTyPi.fmAllU vty) cf-vty cb-pi bU-pi
              fmu0  = FinMem-Selection b f sel (RValPi.fmG vpiM') ctg cb-pi bU-pi
              eqN-uf = restrictEqVal2 _ _ _ A0 u0 u-f b le-uf fmu-f fmu0 eqN-rev
              valN2-uf = Val2-from-EqVal2-first u-f b eqN-uf
              eqTyB-vf = piEE-A0 u-f v-f sel-f N2 N1 htN2 htN1 (conv-sym cvN) eqN-uf
              eqTyB-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 B0 N2) (subst1 B0 N1) w)
                           (Eq-sym eq-ef) eqTyB-vf
              eqApp2 = EqVal2-type-transport v0 (EvalFun f u0) eqTyB-ef eqApp2-raw
              eqAppM' = RValPi.appE vpiM' u0 v0 sel N1 N2 htN1 htN2 cvN eqN
              cv0 = Coherent-Selection-val sel ctg
              cev = Coherent-EvalFun f u0 cf-vty cu0
          in EqVal2-trans v0 (EvalFun f u0) cv0 cev
               (EqVal2-sym v0 (EvalFun f u0) cv0 cev eqApp1)
               (EqVal2-trans v0 (EvalFun f u0) cv0 cev eqAppM' eqApp2)
        vpiM = record
          { domA0 = A0 ; codB0 = B0 ; red = redT
          ; cohG = cg-vpi ; fmG = RValPi.fmG vpiM'
          ; appV = appVM ; appE = appEM
          }
        appEVM : PiAppEqVal2 _ _ _ A0 B0 b f g
        appEVM = \ u0 v0 sel P htP valP ->
          Val2-beta-expand v0 (EvalFun f u0) (HeadRed-App hr)
            (conv-App-fun htA0 htB0 ctPi htP)
            (RValPi.appV vpiM' u0 v0 sel P htP valP)
        eqpi = record
          { domA0 = A0 ; codB0 = B0 ; red = redT
          ; cohG = cg-vpi ; fmG = RValPi.fmG vpiM'
          ; appEV = appEVM
          }
    in mkSigma vty (mkSigma vpiM' (mkSigma vpiM eqpi))

  -- a = SigmaCode b f: by u (PDF §6.2, 4-step chain)
  Val2-beta-expand Bot (SigmaCode b f) hr ct val = tt
  Val2-beta-expand UCode (SigmaCode b f) hr ct val = tt
  Val2-beta-expand PropCode (SigmaCode b f) hr ct val = tt
  Val2-beta-expand (FunEl g) (SigmaCode b f) hr ct val = tt
  Val2-beta-expand (PiCode a' f') (SigmaCode b f) hr ct val = tt
  Val2-beta-expand (SigmaCode a' f') (SigmaCode b f) hr ct val = tt
  Val2-beta-expand (PairCode u' v') (SigmaCode b f) hr ct val =
    let vty    = fst val
        vsigM' = snd val
        A0     = RValSigma.domA vsigM'
        B0     = RValSigma.codB vsigM'
        redT   = RValSigma.red vsigM'
        -- Transport htA0/htB0 from vty coords to A0/B0
        uniq   = Red3-unique-Sigma (RValTySigma.red vty) redT
        htA0   = Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTySigma.htA vty)
        htB0   = Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                   (Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTySigma.htB vty))
        htSigU = snd (typing-ConvTm (Red3.ct redT))
        ctSig  = conv-conv ct (Red3.ct redT) htSigU
        -- Step 1: IH at fst
        ctFst  = conv-Fst htA0 htB0 ctSig
        eqFst  = Val2-beta-expand u' b (HeadRed-Fst hr) ctFst (RValSigma.valFst vsigM')
        valFstM = Val2-from-EqVal2-second u' b eqFst
        -- Step 2: edge → type equality (using selectionBelow)
        htFstM' = RValSigma.htFst vsigM'
        htFstM  = fst (typing-ConvTm ctFst)
        eqA-to-vty = Eq-sym (fst uniq)  -- Eq A0 domA_vty
        eqB-to-vty = Eq-sym (snd uniq)  -- Eq B0 codB_vty
        cf-sig  = RValTySigma.cohF vty
        cu'     = RValSigma.cohW1 vsigM'
        bU-sig  = RValTySigma.fmBU vty
        cb-sig  = coh-from-aU b bU-sig
        sb      = selectionBelow f u' cf-sig cu'
        u-f     = fst sb ; v-f = fst (snd sb)
        sel-f   = fst (snd (snd sb))
        le-uf   = fst (snd (snd (snd sb)))
        eq-ef   = snd (snd (snd (snd sb)))
        fmu-f   = FinMemAllU-Selection b sel-f (RValTySigma.fmAllU vty) cf-sig cb-sig bU-sig
        -- Restrict eqFst to u-f and transport to vty coords
        eqFst-uf = restrictEqVal2 _ _ _ A0 u' u-f b le-uf fmu-f (RValSigma.fmW1 vsigM') eqFst
        htFstM'-vty = Eq-transport (\ X -> HasType _ _ X) eqA-to-vty htFstM'
        htFstM-vty  = Eq-transport (\ X -> HasType _ _ X) eqA-to-vty htFstM
        eqFst-uf-vty = Eq-transport (\ X -> EqVal2 _ _ _ X u-f b) eqA-to-vty eqFst-uf
        ctFst-vty = Eq-transport (\ X -> ConvTm _ _ _ X) eqA-to-vty ctFst
        eqTyB-vf = RValTySigma.edgeE vty u-f v-f sel-f
                      (Fst _) (Fst _) htFstM'-vty htFstM-vty (conv-sym ctFst-vty) eqFst-uf-vty
        codB-vty = RValTySigma.codB vty
        eqTyB-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 codB-vty (Fst _)) (subst1 codB-vty (Fst _)) w) (Eq-sym eq-ef) eqTyB-vf
        eqTyB   = Eq-transport (\ Y -> EqValTy2 _ (subst1 Y (Fst _)) (subst1 Y (Fst _)) (EvalFun f u')) (snd uniq) eqTyB-ef
        -- Step 3: IH at snd (type = subst1 B0 (Fst M'))
        ctSnd-raw  = conv-Snd htA0 htB0 ctSig
        subst1Eq   = subst1-cong-ConvTm htA0 htB0 htFstM htFstM' ctFst
        htBFstM'   = snd (typing-ConvTm subst1Eq)
        ctSnd      = conv-conv ctSnd-raw subst1Eq htBFstM'
        eqSnd      = Val2-beta-expand v' (EvalFun f u') (HeadRed-Snd hr) ctSnd (RValSigma.valSnd vsigM')
        valSndM-BM' = Val2-from-EqVal2-second v' (EvalFun f u') eqSnd
        -- Step 4: transport snd from B0[Fst M'] to B0[Fst M]
        valSndM = Val2-type-transport v' (EvalFun f u') eqTyB valSndM-BM'
        -- Build result records
        vsigM  = record
          { domA = A0 ; codB = B0 ; red = redT
          ; htFst = htFstM ; cohW1 = RValSigma.cohW1 vsigM'
          ; fmW1 = RValSigma.fmW1 vsigM' ; valFst = valFstM ; valSnd = valSndM
          }
        eqsig  = record
          { domA = A0 ; codB = B0 ; red = redT
          ; htFstM = htFstM' ; htFstN = htFstM
          ; cohW1 = RValSigma.cohW1 vsigM' ; fmW1 = RValSigma.fmW1 vsigM'
          ; valFstM = RValSigma.valFst vsigM'
          ; valSndM = RValSigma.valSnd vsigM'
          ; valFstN = valFstM ; valSndN = valSndM ; eqFst = eqFst
          }
    in mkSigma vty (mkSigma vsigM' (mkSigma vsigM eqsig))

  -- a = PairCode: trivial
  Val2-beta-expand u (PairCode x y) hr ct val = tt
