{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityProps.agda  (MIN/ — Pi + U fragment)
--
-- Stratified ports of ValidityFwd / ValiditySymTrans / ValiditySup, the
-- same combinator+induction way as MIN.Validity.Mono:
--   FwdPack k / goodStageFwd        (consumes goodStage)
--   SymTransPack k / goodStageSymTrans (consumes goodStageFwd)
--   SupPack k / goodStageSup        (consumes goodStage)
--
-- Each goodStageX (suc n) ports the original case analysis; recursion into
-- a smaller code = the IH (goodStageX n), same-code = local, edge work uses
-- upstream packs (goodStage / goodStageFwd) at the needed stage.
--
-- No postulates.
------------------------------------------------------------------------

module MIN.Validity.Props where

open import MIN.Validity.Mono
open import MIN.Validity.Stratified using (Red3 ; mkRed3)

import MIN.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons )
import MIN.Syntax.Raw as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import MIN.Syntax.Typing using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-App)
open import MIN.Syntax.Reduction using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ;
  HeadRed-strip-Pi )
open import MIN.Domain.Kernel using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ; finMem-piU-dom ; finMem-piU-allU ;
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
  CFTcons ; CoherentFunTail ; CoherentWith )
open import MIN.Model.Selection using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import MIN.Validity.Core using (Red-unique-Pi ;
  bU-from-cf-fmFun ; FinMem-Coherent)
open import MIN.Syntax.Substitution using (typing-ConvTm ; typing-type ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- FwdPack: EqValTy2-sym + Val2-EqValTy2-fwd + EqVal2-EqValTy2-fwd at Stage k
------------------------------------------------------------------------

record FwdPack (k : Nat) : Set1 where
  field
    EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
      (a : FinEl) -> Coherent a -> EVTy k G M N a -> EVTy k G N M a
    Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
      (u b : FinEl) -> Coherent b -> EVTy k G C C' b -> Vl k G M C u b -> Vl k G M C' u b
    EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
      (u b : FinEl) -> Coherent b -> EVTy k G C C' b -> EVl k G M N C u b -> EVl k G M N C' u b

goodStageFwd : (k : Nat) -> FwdPack k
goodStageFwd zero = record
  { EqValTy2-sym        = \ a ca ev -> tt
  ; Val2-EqValTy2-fwd   = \ u b cb eqv val -> tt
  ; EqVal2-EqValTy2-fwd = \ u b cb eqv ev -> tt
  }
goodStageFwd (suc n) = record
  { EqValTy2-sym = Esym ; Val2-EqValTy2-fwd = Vfwd ; EqVal2-EqValTy2-fwd = EVfwd }
  where
    ihF : FwdPack n
    ihF = goodStageFwd n
    ihM : MonoPack n
    ihM = goodStage n
    ihMs : MonoPack (suc n)
    ihMs = goodStage (suc n)
    open SR n
    sym  = FwdPack.EqValTy2-sym ihF
    fwd  = FwdPack.Val2-EqValTy2-fwd ihF
    efwd = FwdPack.EqVal2-EqValTy2-fwd ihF
    rstr = MonoPack.restrictVal2 ihM
    vf1  = MonoPack.Val2-from-EqVal2-first ihM

    Esym : {m : Nat} {G : Ctx m} {M N : Expr m}
      (a : FinEl) -> Coherent a -> EVTy (suc n) G M N a -> EVTy (suc n) G N M a
    Vfwd : {m : Nat} {G : Ctx m} {C C' M : Expr m}
      (u b : FinEl) -> Coherent b -> EVTy (suc n) G C C' b -> Vl (suc n) G M C u b -> Vl (suc n) G M C' u b
    EVfwd : {m : Nat} {G : Ctx m} {C C' M N : Expr m}
      (u b : FinEl) -> Coherent b -> EVTy (suc n) G C C' b -> EVl (suc n) G M N C u b -> EVl (suc n) G M N C' u b

    Esym Bot ca ev = tt
    Esym UCode ca ev = mkSigma (snd ev) (fst ev)
    Esym (FunEl g) ca ev = tt
    Esym (PiCode b f) ca (mkSigma vtyM (mkSigma vtyN core)) =
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
        ; eqA = sym b (fst ca) (REqValTyPi.eqA core)
        ; edgeET = \ u' v' sel P htP valP ->
            let htA'-e = Eq-transport (\ X -> HasType _ X _)
                           (fst (Red3-unique-Pi (RValTyPi.red vtyN) (REqValTyPi.redN core)))
                           (RValTyPi.htA vtyN)
                htA-e = Eq-transport (\ X -> HasType _ X _)
                          (fst (Red3-unique-Pi (RValTyPi.red vtyM) (REqValTyPi.redM core)))
                          (RValTyPi.htA vtyM)
                htP-A = ty-conv htP (conv-sym (REqValTyPi.convA core)) htA-e
                valP-A = fwd u' b (fst ca) (sym b (fst ca) (REqValTyPi.eqA core)) valP
            in sym v' (Coherent-Selection-val sel (REqValTyPi.cohF core))
                 (REqValTyPi.edgeET core u' v' sel P htP-A valP-A)
        }))

    Vfwd u Bot cb eqv val = tt
    Vfwd Bot UCode cb eqv val = tt
    Vfwd u (FunEl h) cb eqv val = tt
    Vfwd Bot (PiCode b0 f0) cb eqv val = tt
    Vfwd UCode (PiCode b0 f0) cb eqv val = tt
    Vfwd (PiCode a' ff) (PiCode b0 f0) cb eqv val = tt
    Vfwd UCode UCode cb eqv val = mkSigma (snd eqv) (snd val)
    Vfwd (FunEl g) UCode cb eqv val = val
    Vfwd (PiCode a' f') UCode cb eqv val = mkSigma (snd eqv) (snd val)
    Vfwd (FunEl g) (PiCode b0 f0) cb eqv val =
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
          redCv = RValTyPi.red vtyC
          htAc  = RValTyPi.htA vtyC
          uniqC2 = Red3-unique-Pi redCv rC
          htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
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
                valN-E = fwd u' b0 cb0 (sym b0 cb0 eqE) valN
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
                valN-uf = rstr _ _ E u' u-f b0 le-uf fmu-f fmu' valN-E
                eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
                eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N) (subst1 F' N) w)
                           (Eq-sym eq-ef) eqt-vf
                cev    = Coherent-EvalFun f0 u' cf0 cu'
            in fwd v' (EvalFun f0 u') cev eqt-ef body
          pae-E'F' : PiAppEq2 _ _ E' F' b0 f0 g
          pae-E'F' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
            let htN1-E = ty-conv htN1 (conv-sym convEE') htE
                htN2-E = ty-conv htN2 (conv-sym convEE') htE
                cvN-E  = conv-conv cvN (conv-sym convEE') htE
                eqN-E  = efwd u' b0 cb0 (sym b0 cb0 eqE) eqN
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
                valN1-uf = rstr _ _ E u' u-f b0 le-uf fmu-f fmu'
                             (vf1 u' b0 eqN-E)
                eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
                eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N1) (subst1 F' N1) w)
                           (Eq-sym eq-ef) eqt-vf
                cev    = Coherent-EvalFun f0 u' cf0 cu'
            in efwd v' (EvalFun f0 u') cev eqt-ef body
          vpi' = record
            { domA0 = E' ; codB0 = F' ; red = rC'
            ; cohG = cg ; fmG = fmg
            ; appV = pav-E'F' ; appE = pae-E'F'
            }
      in mkSigma vtyC' vpi'

    EVfwd u Bot cb eqv ev = tt
    EVfwd Bot UCode cb eqv ev = tt
    EVfwd u (FunEl h) cb eqv ev = tt
    EVfwd Bot (PiCode b0 f0) cb eqv ev = tt
    EVfwd UCode (PiCode b0 f0) cb eqv ev = tt
    EVfwd (PiCode a' ff) (PiCode b0 f0) cb eqv ev = tt
    EVfwd UCode UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
    EVfwd (FunEl g) UCode cb eqv ev = ev
    EVfwd (PiCode a' f') UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
    EVfwd (FunEl g) (PiCode b0 f0) cb eqv ev =
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
          redCv-eq = RValTyPi.red vtyC
          htAc-eq = RValTyPi.htA vtyC
          uniqC2-eq = Red3-unique-Pi redCv-eq rC
          htE-eq  = Eq-transport (\ X -> HasType _ X _) (fst uniqC2-eq) htAc-eq
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
                valP-E = fwd u' b0 cb0 (sym b0 cb0 eqE) valP
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
                valP-uf = rstr _ _ E u' u-f b0 le-uf fmu-f fmu' valP-E
                eqt-vf = pet u-f v-f sel-f P htP-E valP-uf
                eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F P) (subst1 F' P) w)
                           (Eq-sym eq-ef) eqt-vf
                cev    = Coherent-EvalFun f0 u' cf0 cu'
            in efwd v' (EvalFun f0 u') cev eqt-ef body
          valM-C  = MonoPack.Val2-from-EqVal2-first ihMs (FunEl g) (PiCode b0 f0) ev
          valN-C  = MonoPack.Val2-from-EqVal2-second ihMs (FunEl g) (PiCode b0 f0) ev
          valM-C' = Vfwd (FunEl g) (PiCode b0 f0) cb eqv valM-C
          valN-C' = Vfwd (FunEl g) (PiCode b0 f0) cb eqv valN-C
          eqvpi-C' = record
            { domA0 = E' ; codB0 = F' ; red = rC'
            ; cohG = cg ; fmG = fmg ; appEV = paev-E'F'
            }
      in mkSigma vtyC' (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqvpi-C'))

------------------------------------------------------------------------
-- SymTransPack: EqValTy2-trans + EqVal2-sym + EqVal2-trans at Stage k
-- (consumes goodStageFwd)
------------------------------------------------------------------------

record SymTransPack (k : Nat) : Set1 where
  field
    EqValTy2-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
      (u : FinEl) -> Coherent u -> EVTy k G A B u -> EVTy k G B C u -> EVTy k G A C u
    EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> Coherent u -> Coherent a -> EVl k G M N A u a -> EVl k G N M A u a
    EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
      (u a : FinEl) -> Coherent u -> Coherent a ->
      EVl k G M1 M2 A u a -> EVl k G M2 M3 A u a -> EVl k G M1 M3 A u a

goodStageSymTrans : (k : Nat) -> SymTransPack k
goodStageSymTrans zero = record
  { EqValTy2-trans = \ u cu eqAB eqBC -> tt
  ; EqVal2-sym     = \ u a cu ca ev -> tt
  ; EqVal2-trans   = \ u a cu ca ev1 ev2 -> tt
  }
goodStageSymTrans (suc n) = record
  { EqValTy2-trans = ETrans ; EqVal2-sym = EVsym ; EqVal2-trans = EVtrans }
  where
    ihST : SymTransPack n
    ihST = goodStageSymTrans n
    ihF : FwdPack n
    ihF = goodStageFwd n
    ihFs : FwdPack (suc n)
    ihFs = goodStageFwd (suc n)
    open SR n
    etr  = SymTransPack.EqValTy2-trans ihST
    evs  = SymTransPack.EqVal2-sym ihST
    evt  = SymTransPack.EqVal2-trans ihST
    fwdn = FwdPack.Val2-EqValTy2-fwd ihF
    syms = FwdPack.EqValTy2-sym ihFs

    ETrans : {m : Nat} {G : Ctx m} {A B C : Expr m}
      (u : FinEl) -> Coherent u -> EVTy (suc n) G A B u -> EVTy (suc n) G B C u -> EVTy (suc n) G A C u
    EVsym : {m : Nat} {G : Ctx m} {M N A : Expr m}
      (u a : FinEl) -> Coherent u -> Coherent a -> EVl (suc n) G M N A u a -> EVl (suc n) G N M A u a
    EVtrans : {m : Nat} {G : Ctx m} {M1 M2 M3 A : Expr m}
      (u a : FinEl) -> Coherent u -> Coherent a ->
      EVl (suc n) G M1 M2 A u a -> EVl (suc n) G M2 M3 A u a -> EVl (suc n) G M1 M3 A u a

    ETrans Bot cu tt tt = tt
    ETrans UCode cu eqAB eqBC = mkSigma (fst eqAB) (snd eqBC)
    ETrans (FunEl g) cu tt tt = tt
    ETrans (PiCode b f) cu eqAB eqBC =
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
          eqDomBC' = Eq-transport (\ X -> EVTy n _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
          eqDomAC  = etr b cb eqDomAB eqDomBC'
          redB1-vty-e = RValTyPi.red vtyB1
          uniqB1-dom-e = Red3-unique-Pi redB1-vty-e rB1
          htA0'-raw-e = RValTyPi.htA vtyB1
          htA0'-e = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
          petAC : PiEdgeEqTy2 _ A0 B0 B1' b f
          petAC = \ u' v' sel P htP valP ->
            let valP-A0' = fwdn u' b cb eqDomAB valP
                valP-A1  = Eq-transport (\ X -> Vl n _ P X u' b) eqA0'A1 valP-A0'
                htP-A0'  = ty-conv htP convAA_AB htA0'-e
                htP-A1   = Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
                eqt1 = petAB u' v' sel P htP valP
                eqt2 = petBC u' v' sel P htP-A1 valP-A1
                eqt2' = Eq-transport (\ X -> EVTy n _ (subst1 X P) (subst1 B1' P) v')
                          (Eq-sym eqB0'B1) eqt2
                cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
            in etr v' cv' eqt1 eqt2'
          convAA_BC' = Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
          convAA_AC = conv-trans convAA_AB convAA_BC'
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

    EVsym u Bot cu ca tt = tt
    EVsym Bot UCode cu ca tt = tt
    EVsym UCode UCode cu ca ev =
      mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (syms UCode cu (snd (snd (snd ev))))))
    EVsym (FunEl g) UCode cu ca ev = tt
    EVsym (PiCode a' f') UCode cu ca ev =
      mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (syms (PiCode a' f') cu (snd (snd (snd ev))))))
    EVsym u (FunEl h) cu ca tt = tt
    EVsym Bot (PiCode b f) cu ca tt = tt
    EVsym UCode (PiCode b f) cu ca tt = tt
    EVsym (FunEl g) (PiCode b f) cu ca ev =
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
            in evs v' (EvalFun f u') cv' cev body
          eqvp' = record
            { domA0 = A0 ; codB0 = B0 ; red = redA
            ; cohG = cg ; fmG = fmg ; appEV = paev'
            }
      in mkSigma vty (mkSigma vpiN (mkSigma vpiM eqvp'))
    EVsym (PiCode a' f') (PiCode b f) cu ca tt = tt

    EVtrans u Bot cu ca tt tt = tt
    EVtrans Bot UCode cu ca tt tt = tt
    EVtrans UCode UCode cu ca ev1 ev2 =
      mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2))) (ETrans UCode cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
    EVtrans (FunEl g) UCode cu ca ev1 ev2 = tt
    EVtrans (PiCode a' f') UCode cu ca ev1 ev2 =
      mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
        (ETrans (PiCode a' f') cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
    EVtrans u (FunEl h) cu ca tt tt = tt
    EVtrans Bot (PiCode b f) cu ca tt tt = tt
    EVtrans UCode (PiCode b f) cu ca tt tt = tt
    EVtrans (FunEl g) (PiCode b f) cu ca ev1 ev2 =
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
            in evt v' (EvalFun f u') cv' cev body1 body2
          epi' = record
            { domA0 = Ax ; codB0 = Bx ; red = redAx
            ; cohG = cg ; fmG = fmg ; appEV = paev'
            }
      in mkSigma vty (mkSigma vpiM1 (mkSigma vpiM3 epi'))
    EVtrans (PiCode a' f') (PiCode b f) cu ca tt tt = tt

------------------------------------------------------------------------
-- SupPack: ValTy2-Sup + EqValTy2-Sup at Stage k  (consumes goodStage)
------------------------------------------------------------------------

record SupPack (k : Nat) : Set1 where
  field
    ValTy2-Sup : {n : Nat} (G : Ctx n) (T : Expr n) (a1 a2 : FinEl) ->
      Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
      VTy k G T a1 -> VTy k G T a2 -> VTy k G T (Sup a1 a2)
    EqValTy2-Sup : {n : Nat} (G : Ctx n) (M N : Expr n) (u1 u2 : FinEl) ->
      Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
      EVTy k G M N u1 -> EVTy k G M N u2 -> EVTy k G M N (Sup u1 u2)

goodStageSup : (k : Nat) -> SupPack k
goodStageSup zero = record
  { ValTy2-Sup   = \ G T a1 a2 comp fm1 fm2 vt1 vt2 -> tt
  ; EqValTy2-Sup = \ G M N u1 u2 comp fm1 fm2 eq1 eq2 -> tt
  }
goodStageSup (suc n) = record
  { ValTy2-Sup = VSup ; EqValTy2-Sup = EVSup }
  where
    ihSup : SupPack n
    ihSup = goodStageSup n
    ihM : MonoPack n
    ihM = goodStage n
    open SR n
    vsup  = SupPack.ValTy2-Sup ihSup
    evsup = SupPack.EqValTy2-Sup ihSup
    rstr  = MonoPack.restrictVal2 ihM
    rstrE = MonoPack.restrictEqVal2 ihM
    dV    = MonoPack.downVal2 ihM
    dEV   = MonoPack.downEqVal2 ihM
    dVT   = MonoPack.downValTy2 ihM
    dEVT  = MonoPack.downEqValTy2 ihM

    VSup : {m : Nat} (G : Ctx m) (T : Expr m) (a1 a2 : FinEl) ->
      Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
      VTy (suc n) G T a1 -> VTy (suc n) G T a2 -> VTy (suc n) G T (Sup a1 a2)
    EVSup : {m : Nat} (G : Ctx m) (M N : Expr m) (u1 u2 : FinEl) ->
      Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
      EVTy (suc n) G M N u1 -> EVTy (suc n) G M N u2 -> EVTy (suc n) G M N (Sup u1 u2)

    VSup G T Bot a2 comp fm1 fm2 vt1 vt2 = vt2
    VSup G T UCode Bot comp fm1 fm2 vt1 vt2 = vt1
    VSup G T UCode UCode comp fm1 fm2 vt1 vt2 = vt1
    VSup G T UCode (FunEl g) ()
    VSup G T UCode (PiCode b g) ()
    VSup G T (FunEl g) Bot comp fm1 fm2 vt1 vt2 = vt1
    VSup G T (FunEl g) UCode ()
    VSup G T (FunEl g) (FunEl h) comp fm1 fm2 vt1 vt2 = vt1
    VSup G T (FunEl g) (PiCode b h) ()
    VSup G T (PiCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
    VSup G T (PiCode b1 f1) UCode ()
    VSup G T (PiCode b1 f1) (FunEl h) ()
    VSup G T (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vt1 vt2 =
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
          vtAb2' : VTy n G A1 b2
          vtAb2' = Eq-transport (\ X -> VTy n G X b2) (Eq-sym eqA) vtAb2
          piEV2' : PiEdgeVal2 G A1 B1 b2 f2
          piEV2' = Eq-transport (\ Y -> PiEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                     (Eq-transport (\ X -> PiEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) piEV2)
          piEE2' : PiEdgeEq2 G A1 B1 b2 f2
          piEE2' = Eq-transport (\ Y -> PiEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                     (Eq-transport (\ X -> PiEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) piEE2)
          comp-b = fst comp
          comp-f = snd comp
          b1U    = finMem-piU-dom b1 f1 fm1
          allU1' = finMem-piU-allU b1 f1 fm1
          b2U    = finMem-piU-dom b2 f2 fm2
          allU2' = finMem-piU-allU b2 f2 fm2
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
          vtA-sup = vsup G A1 b1 b2 comp-b b1U b2U vtAb1 vtAb2'
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
                val-u1-sup = rstr _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valN
                val-u1-b1  = dV _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
                val-u2-sup = rstr _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valN
                val-u2-b2  = dV _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
                vt-v1  = piEV1 u1 v1 sel1 N htN val-u1-b1
                vt-v2  = piEV2' u2 v2 sel2 N htN val-u2-b2
                vt-ef1 = Eq-transport (\ x -> VTy n G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
                vt-ef2 = Eq-transport (\ x -> VTy n G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
                comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
                fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
                fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
                vt-sup  = vsup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                            comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
                eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
                vt-ef-app = Eq-transport (\ x -> VTy n G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
                fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
                ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
                lf-refl = LeFunCode-refl (append f1 f2) ctf-app
                le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
            in dVT _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
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
                eqv-u1-sup = rstrE _ _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup eqN
                eqv-u1-b1  = dEV _ _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU eqv-u1-sup
                eqv-u2-sup = rstrE _ _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup eqN
                eqv-u2-b2  = dEV _ _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU eqv-u2-sup
                eqt-v1 = piEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
                eqt-v2 = piEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
                eqt-ef1 = Eq-transport (\ x -> EVTy n G (subst1 B1 N1) (subst1 B1 N2) x)
                            (Eq-sym eq-v1) eqt-v1
                eqt-ef2 = Eq-transport (\ x -> EVTy n G (subst1 B1 N1) (subst1 B1 N2) x)
                            (Eq-sym eq-v2) eqt-v2
                comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
                fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
                fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
                eqt-sup = evsup G (subst1 B1 N1) (subst1 B1 N2)
                            (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
                eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
                eqt-ef-app = Eq-transport (\ x -> EVTy n G (subst1 B1 N1) (subst1 B1 N2) x)
                               (Eq-sym eq-app) eqt-sup
                fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
                ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
                lf-refl = LeFunCode-refl (append f1 f2) ctf-app
                le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
            in dEVT G (subst1 B1 N1) (subst1 B1 N2)
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

    EVSup G M N Bot u2 comp fm1 fm2 eq1 eq2 = eq2
    EVSup G M N UCode Bot comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N UCode UCode comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N UCode (FunEl g) ()
    EVSup G M N UCode (PiCode b g) ()
    EVSup G M N (FunEl g) Bot comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N (FunEl g) UCode ()
    EVSup G M N (FunEl g) (FunEl h) comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N (FunEl g) (PiCode b h) ()
    EVSup G M N (PiCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N (PiCode b1 f1) UCode ()
    EVSup G M N (PiCode b1 f1) (FunEl h) ()
    EVSup G M N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 eq1 eq2 =
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
          eqvtA2' : EVTy n G AM AN b2
          eqvtA2' = Eq-transport (\ X -> EVTy n G X AN b2) (Eq-sym eqAM)
                      (Eq-transport (\ X -> EVTy n G AM2 X b2) (Eq-sym eqAN) eqvtA2)
          piEET2' : PiEdgeEqTy2 G AM BM BN b2 f2
          piEET2' = Eq-transport (\ X -> PiEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                      (Eq-transport (\ X -> PiEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                        (Eq-transport (\ X -> PiEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) piEET2))
          comp-b  = fst comp
          comp-f  = snd comp
          b1U     = finMem-piU-dom b1 f1 fm1
          allU1'  = finMem-piU-allU b1 f1 fm1
          b2U     = finMem-piU-dom b2 f2 fm2
          allU2'  = finMem-piU-allU b2 f2 fm2
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
          eqvtA-sup = evsup G AM AN b1 b2 comp-b b1U b2U eqvtA1 eqvtA2'
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
                val-u1-sup = rstr _ _ AM u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valP
                val-u1-b1  = dV _ _ AM u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
                val-u2-sup = rstr _ _ AM u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valP
                val-u2-b2  = dV _ _ AM u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
                eqt-v1  = piEET1 u1 v1 sel1 P htP val-u1-b1
                eqt-v2  = piEET2' u2 v2 sel2 P htP val-u2-b2
                eqt-ef1 = Eq-transport (\ x -> EVTy n G (subst1 BM P) (subst1 BN P) x)
                            (Eq-sym eq-v1) eqt-v1
                eqt-ef2 = Eq-transport (\ x -> EVTy n G (subst1 BM P) (subst1 BN P) x)
                            (Eq-sym eq-v2) eqt-v2
                comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
                fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
                fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
                eqt-sup = evsup G (subst1 BM P) (subst1 BN P)
                            (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
                eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
                eqt-ef-app = Eq-transport (\ x -> EVTy n G (subst1 BM P) (subst1 BN P) x)
                               (Eq-sym eq-app) eqt-sup
                fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
                ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
                lf-refl = LeFunCode-refl (append f1 f2) ctf-app
                le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
            in dEVT G (subst1 BM P) (subst1 BN P)
                 v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
          vtM-sup = VSup G M (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtM1-eq1 vtM2-eq2
          vtN-sup = VSup G N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtN1-eq1 vtN2-eq2
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

------------------------------------------------------------------------
-- ReflPack: reflexivity at Stage k
--   Val2-Bot / EqVal2-Bot (trivial), Val2-to-EqVal2, ValTy2-to-EqValTy2.
-- Recurses into codes (the IH); consumes only conv-refl.  ValPi2-to-
-- EqValPi2 is a non-recursive combinator over a ReflPack k.
------------------------------------------------------------------------

record ReflPack (k : Nat) : Set1 where
  field
    Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n}
      (a : FinEl) -> Vl k G M A Bot a
    EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (a : FinEl) -> EVl k G M N A Bot a
    Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n}
      (u a : FinEl) -> Vl k G M A u a -> EVl k G M M A u a
    ValTy2-to-EqValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
      (a : FinEl) -> VTy k G M a -> EVTy k G M M a

valPi2ToEqValPi2 : (k : Nat) (rp : ReflPack k) {n : Nat} (G : Ctx n) (M A : Expr n)
  (g : FinFun) (b : FinEl) (f : FinFun) ->
  SR.RValPi k G M A g b f -> SR.REqValPi k G M M A g b f
valPi2ToEqValPi2 k rp G M A g b f vpi = record
  { domA0 = RValPi.domA0 vpi
  ; codB0 = RValPi.codB0 vpi
  ; red   = RValPi.red vpi
  ; cohG  = RValPi.cohG vpi
  ; fmG   = RValPi.fmG vpi
  ; appEV = \ u v sel P htP valP ->
      ReflPack.Val2-to-EqVal2 rp v (EvalFun f u) (RValPi.appV vpi u v sel P htP valP)
  }
  where open SR k

goodStageRefl : (k : Nat) -> ReflPack k
goodStageRefl zero = record
  { Val2-Bot           = \ a -> tt
  ; EqVal2-Bot         = \ a -> tt
  ; Val2-to-EqVal2     = \ u a v -> tt
  ; ValTy2-to-EqValTy2 = \ a vt -> tt
  }
goodStageRefl (suc n) = record
  { Val2-Bot = V2B ; EqVal2-Bot = EV2B ; Val2-to-EqVal2 = V2E ; ValTy2-to-EqValTy2 = VT2E }
  where
    ih : ReflPack n
    ih = goodStageRefl n
    open SR n
    vt2e = ReflPack.ValTy2-to-EqValTy2 ih

    V2B : {m : Nat} {G : Ctx m} {M A : Expr m} (a : FinEl) -> Vl (suc n) G M A Bot a
    V2B Bot          = tt
    V2B UCode        = tt
    V2B (FunEl h)    = tt
    V2B (PiCode b f) = tt

    EV2B : {m : Nat} {G : Ctx m} {M N A : Expr m} (a : FinEl) -> EVl (suc n) G M N A Bot a
    EV2B Bot          = tt
    EV2B UCode        = tt
    EV2B (FunEl h)    = tt
    EV2B (PiCode b f) = tt

    VT2E : {m : Nat} {G : Ctx m} {M : Expr m} (a : FinEl) -> VTy (suc n) G M a -> EVTy (suc n) G M M a
    VT2E Bot v = tt
    VT2E UCode v = mkSigma v v
    VT2E (FunEl g) v = tt
    VT2E (PiCode b f) vtyM =
      let eqVtA = vt2e b (RValTyPi.valA vtyM)
          A0 = RValTyPi.domA vtyM
          B0 = RValTyPi.codB vtyM
          edgeEqTy : PiEdgeEqTy2 _ A0 B0 B0 b f
          edgeEqTy = \ u' v' sel P htP valP ->
            vt2e v' (RValTyPi.edgeV vtyM u' v' sel P htP valP)
          coreEq : REqValTyPi _ _ _ b f
          coreEq = record
            { domA   = RValTyPi.domA vtyM
            ; codB   = RValTyPi.codB vtyM
            ; domA'  = RValTyPi.domA vtyM
            ; codB'  = RValTyPi.codB vtyM
            ; redM   = RValTyPi.red vtyM
            ; redN   = RValTyPi.red vtyM
            ; cohF   = RValTyPi.cohF vtyM
            ; fmAllU = RValTyPi.fmAllU vtyM
            ; convA  = conv-refl (RValTyPi.htA vtyM)
            ; convB  = conv-refl (RValTyPi.htB vtyM)
            ; eqA    = eqVtA
            ; edgeET = edgeEqTy
            }
      in mkSigma vtyM (mkSigma vtyM coreEq)

    V2E : {m : Nat} {G : Ctx m} {M A : Expr m} (u a : FinEl) -> Vl (suc n) G M A u a -> EVl (suc n) G M M A u a
    V2E u Bot v = tt
    V2E Bot UCode v = tt
    V2E Bot (FunEl h) v = tt
    V2E Bot (PiCode b f) v = tt
    V2E UCode UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (mkSigma (snd v) (snd v))))
    V2E (FunEl g) UCode v = tt
    V2E (PiCode a f) UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (VT2E (PiCode a f) (snd v))))
    V2E UCode (FunEl h) v = tt
    V2E (FunEl g) (FunEl h) v = tt
    V2E (PiCode a f) (FunEl h) v = tt
    V2E UCode (PiCode b f) v = tt
    V2E (PiCode a' f') (PiCode b f) v = tt
    V2E (FunEl g) (PiCode b f) (mkSigma vty vpi) =
      mkSigma vty (mkSigma vpi (mkSigma vpi (valPi2ToEqValPi2 n ih _ _ _ g b f vpi)))

------------------------------------------------------------------------
-- TransportPack: Val2-type-transport / EqVal2-type-transport at Stage k.
-- Transport Val2/EqVal2 along EqValTy2 in the type slot (no Coherent arg;
-- coherence derived internally from the record).  fwd-family; recurses
-- into codes (the IH); consumes goodStageFwd (EqValTy2-sym) + goodStage
-- (restrictVal2, Val2-from-EqVal2-first).
------------------------------------------------------------------------

record TransportPack (k : Nat) : Set1 where
  field
    Val2-type-transport : {n : Nat} {G : Ctx n} {C C' N : Expr n}
      (u a : FinEl) -> EVTy k G C C' a -> Vl k G N C u a -> Vl k G N C' u a
    EqVal2-type-transport : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
      (u a : FinEl) -> EVTy k G C C' a -> EVl k G M N C u a -> EVl k G M N C' u a

goodStageTransport : (k : Nat) -> TransportPack k
goodStageTransport zero = record
  { Val2-type-transport   = \ u a eqvt val -> tt
  ; EqVal2-type-transport = \ u a eqvt ev -> tt
  }
goodStageTransport (suc n) = record { Val2-type-transport = VTT ; EqVal2-type-transport = EVTT }
  where
    ihT : TransportPack n
    ihT = goodStageTransport n
    open SR n
    v2t  = TransportPack.Val2-type-transport ihT
    ev2t = TransportPack.EqVal2-type-transport ihT
    syms = FwdPack.EqValTy2-sym (goodStageFwd n)
    rstr = MonoPack.restrictVal2 (goodStage n)
    vf1  = MonoPack.Val2-from-EqVal2-first (goodStage n)

    VTT : {m : Nat} {G : Ctx m} {C C' N : Expr m}
      (u a : FinEl) -> EVTy (suc n) G C C' a -> Vl (suc n) G N C u a -> Vl (suc n) G N C' u a
    VTT u Bot eqvt val = tt
    VTT Bot UCode eqvt val = tt
    VTT UCode UCode eqvt val = mkSigma (snd eqvt) (snd val)
    VTT (FunEl g) UCode eqvt val = tt
    VTT (PiCode a' f') UCode eqvt val = mkSigma (snd eqvt) (snd val)
    VTT u (FunEl h) eqvt val = tt
    VTT Bot (PiCode b f) eqvt val = tt
    VTT UCode (PiCode b f) eqvt val = tt
    VTT (PiCode a' f') (PiCode b f) eqvt val = tt
    VTT (FunEl g) (PiCode b f) eqvt val =
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
          redCv = RValTyPi.red vtyC
          htAc  = RValTyPi.htA vtyC
          uniqC2 = Red3-unique-Pi redCv rC
          htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
          vpiN = snd val
          A0   = RValPi.domA0 vpiN
          B0   = RValPi.codB0 vpiN
          redC = RValPi.red vpiN
          cg   = RValPi.cohG vpiN
          fmg  = RValPi.fmG vpiN
          pav  = RValPi.appV vpiN
          pae  = RValPi.appE vpiN
          uniq = Red3-unique-Pi redC rC
          eqA0E = fst uniq
          eqB0F = snd uniq
          pav-EF : PiAppVal2 _ _ E F b f g
          pav-EF = Eq-transport (\ X -> PiAppVal2 _ _ X F b f g) eqA0E
                     (Eq-transport (\ Y -> PiAppVal2 _ _ A0 Y b f g) eqB0F pav)
          pae-EF : PiAppEq2 _ _ E F b f g
          pae-EF = Eq-transport (\ X -> PiAppEq2 _ _ X F b f g) eqA0E
                     (Eq-transport (\ Y -> PiAppEq2 _ _ A0 Y b f g) eqB0F pae)
          ctg  = cft-from-cf g cg
          b0U  = bU-from-cf-fmFun g b f cg fmg
          pav-E'F' : PiAppVal2 _ _ E' F' b f g
          pav-E'F' = \ u' v' sel N htN valN ->
            let htN-E  = ty-conv htN (conv-sym convEE') htE
                cu'    = Coherent-Selection sel ctg
                cb0'   = coh-from-aU b b0U
                valN-E = v2t u' b (syms b cb0' eqE) valN
                body   = pav-EF u' v' sel N htN-E valN-E
                sb     = selectionBelow f u' cf0 cu'
                u-f    = fst sb
                v-f    = fst (snd sb)
                sel-f  = fst (snd (snd sb))
                le-uf  = fst (snd (snd (snd sb)))
                eq-ef  = snd (snd (snd (snd sb)))
                fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                fmu'   = FinMem-Selection b f sel fmg ctg cb0' b0U
                valN-uf = rstr _ _ E u' u-f b le-uf fmu-f fmu' valN-E
                eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
                eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N) (subst1 F' N) w)
                           (Eq-sym eq-ef) eqt-vf
                cev    = Coherent-EvalFun f u' cf0 cu'
            in v2t v' (EvalFun f u') eqt-ef body
          pae-E'F' : PiAppEq2 _ _ E' F' b f g
          pae-E'F' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
            let htN1-E = ty-conv htN1 (conv-sym convEE') htE
                htN2-E = ty-conv htN2 (conv-sym convEE') htE
                cvN-E  = conv-conv cvN (conv-sym convEE') htE
                cu'    = Coherent-Selection sel ctg
                cb0'   = coh-from-aU b b0U
                eqN-E  = ev2t u' b (syms b cb0' eqE) eqN
                body   = pae-EF u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
                sb     = selectionBelow f u' cf0 cu'
                u-f    = fst sb
                v-f    = fst (snd sb)
                sel-f  = fst (snd (snd sb))
                le-uf  = fst (snd (snd (snd sb)))
                eq-ef  = snd (snd (snd (snd sb)))
                fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                fmu'   = FinMem-Selection b f sel fmg ctg cb0' b0U
                valN1-uf = rstr _ _ E u' u-f b le-uf fmu-f fmu' (vf1 u' b eqN-E)
                eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
                eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N1) (subst1 F' N1) w)
                           (Eq-sym eq-ef) eqt-vf
                cev    = Coherent-EvalFun f u' cf0 cu'
            in ev2t v' (EvalFun f u') eqt-ef body
          vpi' = record
            { domA0 = E' ; codB0 = F' ; red = rC'
            ; cohG = cg ; fmG = fmg
            ; appV = pav-E'F' ; appE = pae-E'F'
            }
      in mkSigma vtyC' vpi'

    EVTT : {m : Nat} {G : Ctx m} {C C' M N : Expr m}
      (u a : FinEl) -> EVTy (suc n) G C C' a -> EVl (suc n) G M N C u a -> EVl (suc n) G M N C' u a
    EVTT u Bot eqvt ev = tt
    EVTT Bot UCode eqvt ev = tt
    EVTT UCode UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
    EVTT (FunEl g) UCode eqvt ev = tt
    EVTT (PiCode a' f') UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
    EVTT u (FunEl h) eqvt ev = tt
    EVTT Bot (PiCode b f) eqvt ev = tt
    EVTT UCode (PiCode b f) eqvt ev = tt
    EVTT (PiCode a' f') (PiCode b f) eqvt ev = tt
    EVTT (FunEl g) (PiCode b f) eqvt ev =
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
          redCv = RValTyPi.red vtyC
          htAc  = RValTyPi.htA vtyC
          uniqC2 = Red3-unique-Pi redCv rC
          htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
          vpiM  = fst (snd ev)
          vpiN  = fst (snd (snd ev))
          eqpi  = snd (snd (snd ev))
          transportRValPi : {Mx : Expr _} -> RValPi _ Mx _ g b f -> RValPi _ Mx _ g b f
          transportRValPi vpi =
            let uniqX = Red3-unique-Pi (RValPi.red vpi) rC
                pavX  = Eq-transport (\ X -> PiAppVal2 _ _ X F b f g) (fst uniqX)
                          (Eq-transport (\ Y -> PiAppVal2 _ _ _ Y b f g) (snd uniqX) (RValPi.appV vpi))
                paeX  = Eq-transport (\ X -> PiAppEq2 _ _ X F b f g) (fst uniqX)
                          (Eq-transport (\ Y -> PiAppEq2 _ _ _ Y b f g) (snd uniqX) (RValPi.appE vpi))
                cgX   = RValPi.cohG vpi
                fmgX  = RValPi.fmG vpi
                ctgX  = cft-from-cf g cgX
                b0U   = bU-from-cf-fmFun g b f cgX fmgX
                pavX' : PiAppVal2 _ _ E' F' b f g
                pavX' = \ u' v' sel N htN valN ->
                  let htN-E  = ty-conv htN (conv-sym convEE') htE
                      cu'    = Coherent-Selection sel ctgX
                      cb0'   = coh-from-aU b b0U
                      valN-E = v2t u' b (syms b cb0' eqE) valN
                      body   = pavX u' v' sel N htN-E valN-E
                      sb     = selectionBelow f u' cf0 cu'
                      u-f    = fst sb
                      v-f    = fst (snd sb)
                      sel-f  = fst (snd (snd sb))
                      le-uf  = fst (snd (snd (snd sb)))
                      eq-ef  = snd (snd (snd (snd sb)))
                      fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                      fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                      valN-uf = rstr _ _ E u' u-f b le-uf fmu-f fmu' valN-E
                      eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
                      eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N) (subst1 F' N) w)
                                 (Eq-sym eq-ef) eqt-vf
                      cev    = Coherent-EvalFun f u' cf0 cu'
                  in v2t v' (EvalFun f u') eqt-ef body
                paeX' : PiAppEq2 _ _ E' F' b f g
                paeX' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
                  let htN1-E = ty-conv htN1 (conv-sym convEE') htE
                      htN2-E = ty-conv htN2 (conv-sym convEE') htE
                      cvN-E  = conv-conv cvN (conv-sym convEE') htE
                      cu'    = Coherent-Selection sel ctgX
                      cb0'   = coh-from-aU b b0U
                      eqN-E  = ev2t u' b (syms b cb0' eqE) eqN
                      body   = paeX u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
                      sb     = selectionBelow f u' cf0 cu'
                      u-f    = fst sb
                      v-f    = fst (snd sb)
                      sel-f  = fst (snd (snd sb))
                      le-uf  = fst (snd (snd (snd sb)))
                      eq-ef  = snd (snd (snd (snd sb)))
                      fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                      fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                      valN1-uf = rstr _ _ E u' u-f b le-uf fmu-f fmu' (vf1 u' b eqN-E)
                      eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
                      eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F N1) (subst1 F' N1) w)
                                 (Eq-sym eq-ef) eqt-vf
                      cev    = Coherent-EvalFun f u' cf0 cu'
                  in ev2t v' (EvalFun f u') eqt-ef body
            in record
              { domA0 = E' ; codB0 = F' ; red = rC' ; cohG = cgX ; fmG = fmgX
              ; appV = pavX' ; appE = paeX' }
          transportREqValPi : REqValPi _ _ _ _ g b f -> REqValPi _ _ _ _ g b f
          transportREqValPi eqp =
            let uniqEq = Red3-unique-Pi (REqValPi.red eqp) rC
                paevX  = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X F b f g) (fst uniqEq)
                           (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ _ Y b f g) (snd uniqEq) (REqValPi.appEV eqp))
                cgX   = REqValPi.cohG eqp
                fmgX  = REqValPi.fmG eqp
                ctgX  = cft-from-cf g cgX
                b0U   = bU-from-cf-fmFun g b f cgX fmgX
                paevX' : PiAppEqVal2 _ _ _ E' F' b f g
                paevX' = \ u' v' sel P htP valP ->
                  let htP-E  = ty-conv htP (conv-sym convEE') htE
                      cu'    = Coherent-Selection sel ctgX
                      cb0'   = coh-from-aU b b0U
                      valP-E = v2t u' b (syms b cb0' eqE) valP
                      body   = paevX u' v' sel P htP-E valP-E
                      sb     = selectionBelow f u' cf0 cu'
                      u-f    = fst sb
                      v-f    = fst (snd sb)
                      sel-f  = fst (snd (snd sb))
                      le-uf  = fst (snd (snd (snd sb)))
                      eq-ef  = snd (snd (snd (snd sb)))
                      fmu-f  = FinMemAllU-Selection b sel-f fmU cf0 cb0' b0U
                      fmu'   = FinMem-Selection b f sel fmgX ctgX cb0' b0U
                      valP-uf = rstr _ _ E u' u-f b le-uf fmu-f fmu' valP-E
                      eqt-vf = pet u-f v-f sel-f P htP-E valP-uf
                      eqt-ef = Eq-transport (\ w -> EVTy n _ (subst1 F P) (subst1 F' P) w)
                                 (Eq-sym eq-ef) eqt-vf
                      cev    = Coherent-EvalFun f u' cf0 cu'
                  in ev2t v' (EvalFun f u') eqt-ef body
            in record
              { domA0 = E' ; codB0 = F' ; red = rC' ; cohG = cgX ; fmG = fmgX
              ; appEV = paevX' }
      in mkSigma vtyC' (mkSigma (transportRValPi vpiM)
           (mkSigma (transportRValPi vpiN) (transportREqValPi eqpi)))

------------------------------------------------------------------------
-- BetaPack: Val2-beta-expand (head-reduction transport) at Stage k.
-- Given HeadRed M M', ConvTm G M M' T, Val2 G M' T u a, produce
-- EqVal2 G M' M T u a.  Recurses into codes (IH at EvalFun); consumes
-- goodStageRefl (ValTy2-to-EqValTy2), goodStage (Val2-from-EqVal2-*,
-- restrictEqVal2), goodStageSymTrans (EqVal2-sym/trans), goodStageTransport
-- (EqVal2-type-transport).
------------------------------------------------------------------------

record BetaPack (k : Nat) : Set1 where
  field
    Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
      (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
      Vl k G M' T u a -> EVl k G M' M T u a

goodStageBeta : (k : Nat) -> BetaPack k
goodStageBeta zero = record { Val2-beta-expand = \ u a hr ct val -> tt }
goodStageBeta (suc n) = record { Val2-beta-expand = Beta }
  where
    ihB : BetaPack n
    ihB = goodStageBeta n
    open SR n
    beta    = BetaPack.Val2-beta-expand ihB
    vt2e    = ReflPack.ValTy2-to-EqValTy2 (goodStageRefl n)
    vf1     = MonoPack.Val2-from-EqVal2-first (goodStage n)
    vf2     = MonoPack.Val2-from-EqVal2-second (goodStage n)
    rstrE   = MonoPack.restrictEqVal2 (goodStage n)
    evsym   = SymTransPack.EqVal2-sym (goodStageSymTrans n)
    evtrans = SymTransPack.EqVal2-trans (goodStageSymTrans n)
    ev2t    = TransportPack.EqVal2-type-transport (goodStageTransport n)

    Beta : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
      Vl (suc n) G M' T u a -> EVl (suc n) G M' M T u a
    Beta u Bot hr ct val = tt
    Beta Bot UCode hr ct val = tt
    Beta (FunEl g) UCode hr ct val = tt
    Beta UCode UCode hr ct val =
      let vtA = fst val ; vtM' = snd val
          ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
          vtM = mkRed3 (HeadRed-trans hr (Red3.hr vtM')) (conv-trans ctU (Red3.ct vtM'))
      in mkSigma vtA (mkSigma vtM' (mkSigma vtM (mkSigma vtM' vtM)))
    Beta (PiCode a' f') UCode hr ct val =
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
            vt2e v0 (RValTyPi.edgeV vtPi u0 v0 sel P htP valP)
          coreEq = record
            { domA = RValTyPi.domA vtPi ; codB = RValTyPi.codB vtPi
            ; domA' = RValTyPi.domA vtPi ; codB' = RValTyPi.codB vtPi
            ; redM = RValTyPi.red vtPi ; redN = newRed
            ; cohF = RValTyPi.cohF vtPi ; fmAllU = RValTyPi.fmAllU vtPi
            ; convA = conv-refl (RValTyPi.htA vtPi) ; convB = conv-refl (RValTyPi.htB vtPi)
            ; eqA = vt2e a' (RValTyPi.valA vtPi) ; edgeET = edgeEqTy }
      in mkSigma vtA (mkSigma vtPi (mkSigma vtM (mkSigma vtPi (mkSigma vtM coreEq))))
    Beta u (FunEl h) hr ct val = tt
    Beta Bot (PiCode b f) hr ct val = tt
    Beta UCode (PiCode b f) hr ct val = tt
    Beta (PiCode a' f') (PiCode b f) hr ct val = tt
    Beta (FunEl g) (PiCode b f) hr ct val =
      let vty   = fst val
          vpiM' = snd val
          A0    = RValPi.domA0 vpiM'
          B0    = RValPi.codB0 vpiM'
          redT  = RValPi.red vpiM'
          uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
          htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
          htB0  = Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                    (Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
          htPiU = snd (typing-ConvTm (Red3.ct redT))
          ctPi  = conv-conv ct (Red3.ct redT) htPiU
          appVM : PiAppVal2 _ _ A0 B0 b f g
          appVM = \ u0 v0 sel N htN valN ->
            vf2 v0 (EvalFun f u0)
              (beta v0 (EvalFun f u0) (HeadRed-App hr)
                (conv-App-fun htA0 htB0 ctPi htN)
                (RValPi.appV vpiM' u0 v0 sel N htN valN))
          cf-vty = RValTyPi.cohF vty
          cg-vpi = RValPi.cohG vpiM'
          ctg    = cft-from-cf g cg-vpi
          bU-pi  = bU-from-cf-fmFun g b f cg-vpi (RValPi.fmG vpiM')
          cb-pi  = coh-from-aU b bU-pi
          piEE-A0 : PiEdgeEq2 _ A0 B0 b f
          piEE-A0 = Eq-transport (\ Y -> PiEdgeEq2 _ A0 Y b f) (snd uniq)
                      (Eq-transport (\ X -> PiEdgeEq2 _ X (RValTyPi.codB vty) b f) (fst uniq) (RValTyPi.edgeE vty))
          appEM : PiAppEq2 _ _ A0 B0 b f g
          appEM = \ u0 v0 sel N1 N2 htN1 htN2 cvN eqN ->
            let eqApp1 = beta v0 (EvalFun f u0) (HeadRed-App hr)
                           (conv-App-fun htA0 htB0 ctPi htN1)
                           (RValPi.appV vpiM' u0 v0 sel N1 htN1 (vf1 u0 b eqN))
                eqApp2-raw = beta v0 (EvalFun f u0) (HeadRed-App hr)
                               (conv-App-fun htA0 htB0 ctPi htN2)
                               (RValPi.appV vpiM' u0 v0 sel N2 htN2 (vf2 u0 b eqN))
                cu0 = Coherent-Selection sel ctg
                eqN-rev = evsym u0 b cu0 cb-pi eqN
                sb  = selectionBelow f u0 cf-vty cu0
                u-f = fst sb ; v-f = fst (snd sb)
                sel-f = fst (snd (snd sb))
                le-uf = fst (snd (snd (snd sb)))
                eq-ef = snd (snd (snd (snd sb)))
                fmu-f = FinMemAllU-Selection b sel-f (RValTyPi.fmAllU vty) cf-vty cb-pi bU-pi
                fmu0  = FinMem-Selection b f sel (RValPi.fmG vpiM') ctg cb-pi bU-pi
                eqN-uf = rstrE _ _ _ A0 u0 u-f b le-uf fmu-f fmu0 eqN-rev
                valN2-uf = vf1 u-f b eqN-uf
                eqTyB-vf = piEE-A0 u-f v-f sel-f N2 N1 htN2 htN1 (conv-sym cvN) eqN-uf
                eqTyB-ef = Eq-transport (\ w -> EVTy n _ (subst1 B0 N2) (subst1 B0 N1) w)
                             (Eq-sym eq-ef) eqTyB-vf
                eqApp2 = ev2t v0 (EvalFun f u0) eqTyB-ef eqApp2-raw
                eqAppM' = RValPi.appE vpiM' u0 v0 sel N1 N2 htN1 htN2 cvN eqN
                cv0 = Coherent-Selection-val sel ctg
                cev = Coherent-EvalFun f u0 cf-vty cu0
            in evtrans v0 (EvalFun f u0) cv0 cev
                 (evsym v0 (EvalFun f u0) cv0 cev eqApp1)
                 (evtrans v0 (EvalFun f u0) cv0 cev eqAppM' eqApp2)
          vpiM = record
            { domA0 = A0 ; codB0 = B0 ; red = redT
            ; cohG = cg-vpi ; fmG = RValPi.fmG vpiM'
            ; appV = appVM ; appE = appEM }
          appEVM : PiAppEqVal2 _ _ _ A0 B0 b f g
          appEVM = \ u0 v0 sel P htP valP ->
            beta v0 (EvalFun f u0) (HeadRed-App hr)
              (conv-App-fun htA0 htB0 ctPi htP)
              (RValPi.appV vpiM' u0 v0 sel P htP valP)
          eqpi = record
            { domA0 = A0 ; codB0 = B0 ; red = redT
            ; cohG = cg-vpi ; fmG = RValPi.fmG vpiM'
            ; appEV = appEVM }
      in mkSigma vty (mkSigma vpiM' (mkSigma vpiM eqpi))
