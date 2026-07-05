{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityProps.agda  (MIN/ — Pi + U fragment)
--
-- Stratified ports of ValidityFwd / ValiditySymTrans / ValiditySup, the
-- same combinator+induction way as ID.Validity.Mono:
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

module ID.Validity.Props where

open import ID.Validity.Mono
open import ID.Validity.Stratified using (Red3 ; mkRed3)

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ;
              List ; nil ; cons )
import ID.Syntax.Raw as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ; Ref ; Id ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import ID.Syntax.Typing using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; conv-Id ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-App)
open import ID.Syntax.Reduction using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; headred-step ; HeadRed-trans ;
  HeadRed-App ;
  HeadRed-strip-Pi ; HeadRed-strip-Ref ; HeadRed1-not-Ref )
open import ID.Domain.Kernel using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ; finMem-piU-dom ; finMem-piU-allU ;
  finMem-idU-dom ; finMem-idU-lhs ; finMem-idU-rhs ;
  LeCode ; LeCode-trans ; LeCode-Bot ;
  Comp-down ; finMem-upward ;
  finMem-Sup-left ; finMem-Sup-right ; finMem-Sup-both ;
  finMemUCode-Sup ; FinMem-Sup-element ;
  EvalFun-in-UCode ; EvalFun-mon ; EvalFun-mon-arg ;
  comp-EvalFun ; EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMemAllU-append-Sup ;
  LeFunCode-refl ; LeFunCode ; append ;
  Comp-refl ; comp-Sup ; comp-Bot-r ;
  Comp-value-EvalFun ; coherentWith-to-compStepFun ;
  CFTcons ; CoherentFunTail ; CoherentWith )
open import ID.Domain.Membership using
  (finMem-ref-le1 ; finMem-ref-le2 ; finMem-ref-wit ; finMem-ref-uT ; finMem-ref-vT ; finMem-ref-coh ;
   FinMemFun-append)
open import ID.Model.Selection using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import ID.Validity.Core using (Red-unique-Pi ;
  bU-from-cf-fmFun ; FinMem-Coherent)
open import ID.Syntax.Substitution using (typing-ConvTm ; typing-type ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Transport a proof-term reduction (Red3 M (Ref W) C) across a type
-- conversion C ~ C' : U.  Used when forwarding an Id VALUE across a type
-- equality (the redTm field of RValId is typed at the Id type).  Stage-
-- independent (Red3/ConvTm/HasType are not stratified).
------------------------------------------------------------------------

redTm-type-transport : {m : Nat} {G : Ctx m} {M W C C' : Expr m} ->
  ConvTm G C C' U -> HasType G C' U -> Red3 G M (Ref W) C -> Red3 G M (Ref W) C'
redTm-type-transport cCC' htC' rt =
  mkRed3 (Red3.hr rt) (conv-conv (Red3.ct rt) cCC' htC')

-- Two head-reductions of the same term M to a `Ref` value have equal witnesses
-- (HeadRed to a value is deterministic).  Used to align the two witnesses'
-- endEq at a compatible binary sup of Id-proof values.
Ref-wit-unique : {m : Nat} {M W1 W2 : Expr m} ->
  HeadRed M (Ref W1) -> HeadRed M (Ref W2) -> Eq W1 W2
Ref-wit-unique hr1 hr2 with HeadRed-strip-Ref hr1 hr2
... | headred-refl = refl
... | headred-step s _ with HeadRed1-not-Ref s
...   | ()

------------------------------------------------------------------------
-- FwdPack: EqValTy2-sym + Val2-EqValTy2-fwd + EqVal2-EqValTy2-fwd at Stage k
------------------------------------------------------------------------

-- MERGED Fwd + SymTrans: Vfwd/EVfwd (fwd) need value-level EqVal2-sym/-trans to
-- transport a proof value's endpoint equality (endEq) across an Id-type conversion,
-- and ETrans/EVtrans need same-stage EqValTy2-sym (Esym) — a genuine mutual
-- dependency (cf. graded-type-theory Conversion.agda:63-65 "mutual with symEq").
-- One package, one structural recursion on the stage index.
record FwdPack (k : Nat) : Set1 where
  field
    EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
      (a : FinEl) -> Coherent a -> EVTy k G M N a -> EVTy k G N M a
    Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
      (u b : FinEl) -> Coherent b -> EVTy k G C C' b -> Vl k G M C u b -> Vl k G M C' u b
    EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
      (u b : FinEl) -> Coherent b -> EVTy k G C C' b -> EVl k G M N C u b -> EVl k G M N C' u b
    EqValTy2-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
      (u : FinEl) -> Coherent u -> EVTy k G A B u -> EVTy k G B C u -> EVTy k G A C u
    EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> Coherent u -> Coherent a -> EVl k G M N A u a -> EVl k G N M A u a
    EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
      (u a : FinEl) -> Coherent u -> Coherent a ->
      EVl k G M1 M2 A u a -> EVl k G M2 M3 A u a -> EVl k G M1 M3 A u a

goodStageFwd : (k : Nat) -> FwdPack k
goodStageFwd zero = record
  { EqValTy2-sym        = \ a ca ev -> tt
  ; Val2-EqValTy2-fwd   = \ u b cb eqv val -> tt
  ; EqVal2-EqValTy2-fwd = \ u b cb eqv ev -> tt
  ; EqValTy2-trans      = \ u cu eqAB eqBC -> tt
  ; EqVal2-sym          = \ u a cu ca ev -> tt
  ; EqVal2-trans        = \ u a cu ca ev1 ev2 -> tt
  }
goodStageFwd (suc n) = record
  { EqValTy2-sym = Esym ; Val2-EqValTy2-fwd = Vfwd ; EqVal2-EqValTy2-fwd = EVfwd
  ; EqValTy2-trans = ETrans ; EqVal2-sym = EVsym ; EqVal2-trans = EVtrans }
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
    -- SymTrans ops at stage n (from the merged IH) + same-stage Esym (local):
    etr  = FwdPack.EqValTy2-trans ihF
    evs  = FwdPack.EqVal2-sym ihF
    evt  = FwdPack.EqVal2-trans ihF
    fwdn = fwd
    rstrE = MonoPack.restrictEqVal2 ihM

    Esym : {m : Nat} {G : Ctx m} {M N : Expr m}
      (a : FinEl) -> Coherent a -> EVTy (suc n) G M N a -> EVTy (suc n) G N M a
    Vfwd : {m : Nat} {G : Ctx m} {C C' M : Expr m}
      (u b : FinEl) -> Coherent b -> EVTy (suc n) G C C' b -> Vl (suc n) G M C u b -> Vl (suc n) G M C' u b
    EVfwd : {m : Nat} {G : Ctx m} {C C' M N : Expr m}
      (u b : FinEl) -> Coherent b -> EVTy (suc n) G C C' b -> EVl (suc n) G M N C u b -> EVl (suc n) G M N C' u b

    -- From an Id-type equality (C ~ C'), reconstruct the syntactic type
    -- conversion ConvTm C C' U + HasType C' U, used to retype the redTm of a
    -- forwarded Id proof value.  Aligns the C-side RValTyId with the eq-record
    -- core via Red3-unique-Id.
    idTyConvC : {m : Nat} {G : Ctx m} {C C' : Expr m} {t u v : FinEl} ->
      RValTyId G C t u v -> REqValTyId G C C' t u v -> Pair (ConvTm G C C' U) (HasType G C' U)
    idTyConvC vtC core =
      let uC  = Red3-unique-Id (RValTyId.red vtC) (REqValTyId.redM core)
          lC  = RValTyId.lhs vtC ; rC = RValTyId.rhs vtC
          hA  = Eq-transport (\ X -> HasType _ X U) (fst uC) (RValTyId.htA vtC)
          hL  = Eq-transport (\ X -> HasType _ X _) (fst (snd uC))
                  (Eq-transport (\ Y -> HasType _ lC Y) (fst uC) (RValTyId.htL vtC))
          hR  = Eq-transport (\ X -> HasType _ X _) (snd (snd uC))
                  (Eq-transport (\ Y -> HasType _ rC Y) (fst uC) (RValTyId.htR vtC))
          cId = conv-Id hA hL hR (REqValTyId.convA core) (REqValTyId.convL core) (REqValTyId.convR core)
          cCC' = conv-trans (Red3.ct (REqValTyId.redM core))
                   (conv-trans cId (conv-sym (Red3.ct (REqValTyId.redN core))))
      in mkSigma cCC' (fst (typing-ConvTm (Red3.ct (REqValTyId.redN core))))

    -- Transport a proof value's endpoint conversions (wit0 ~ lhs0/rhs0 : domA0)
    -- across an Id-type equality C ~ C', to the C'-reduced endpoints.
    refConvsFwd : {m : Nat} {G : Ctx m} {M C C' : Expr m} {w t u v : FinEl} ->
      (rid : RValId G M C w t u v) (core : REqValTyId G C C' t u v) ->
      Pair (ConvTm G (RValId.wit0 rid) (REqValTyId.lhs' core) (REqValTyId.domA' core))
           (ConvTm G (RValId.wit0 rid) (REqValTyId.rhs' core) (REqValTyId.domA' core))
    refConvsFwd rid core =
      let al   = Red3-unique-Id (RValId.red rid) (REqValTyId.redM core)
          w0   = RValId.wit0 rid
          d0   = RValId.domA0 rid
          rcL0 = Eq-transport (\ X -> ConvTm _ w0 X d0) (fst (snd al)) (RValId.refConvL rid)
          rcL  = Eq-transport (\ X -> ConvTm _ w0 (REqValTyId.lhs core) X) (fst al) rcL0
          rcR0 = Eq-transport (\ X -> ConvTm _ w0 X d0) (snd (snd al)) (RValId.refConvR rid)
          rcR  = Eq-transport (\ X -> ConvTm _ w0 (REqValTyId.rhs core) X) (fst al) rcR0
          cA   = REqValTyId.convA core
          htDomA' = snd (typing-ConvTm cA)
          rcL' = conv-conv (conv-trans rcL (REqValTyId.convL core)) cA htDomA'
          rcR' = conv-conv (conv-trans rcR (REqValTyId.convR core)) cA htDomA'
      in mkSigma rcL' rcR'

    -- Semantic analog of refConvsFwd: forward a raw value-record endEq pair
    -- (wit0 ~ lhs0/rhs0) across an Id-type equality C ~ C' to the C'-reduced
    -- endpoints.  Align to core's M-side, restrict core.eqL/eqR down to the
    -- witness value-code w, PER-compose, then efwd the domain domA -> domA'.
    endEqFwdRaw : {m : Nat} {G : Ctx m} {A C' : Expr m} {wit0 domA0 lhs0 rhs0 : Expr m} {w t u v : FinEl} ->
      Red3 G A (Id domA0 lhs0 rhs0) U -> FinMem (RefEl w) (IdCode t u v) ->
      EVl n G wit0 lhs0 domA0 w t -> EVl n G wit0 rhs0 domA0 w t ->
      (core : REqValTyId G A C' t u v) ->
      Pair (EVl n G wit0 (REqValTyId.lhs' core) (REqValTyId.domA' core) w t)
           (EVl n G wit0 (REqValTyId.rhs' core) (REqValTyId.domA' core) w t)
    endEqFwdRaw {G = G} {wit0 = w0} {domA0 = d0} {w = w} {t = t} {u = u} {v = v} red refMem eL eR core =
      let al = Red3-unique-Id red (REqValTyId.redM core)
          eL0 = Eq-transport (\ X -> EVl n G w0 X d0 w t) (fst (snd al)) eL
          eL1 = Eq-transport (\ X -> EVl n G w0 (REqValTyId.lhs core) X w t) (fst al) eL0
          eR0 = Eq-transport (\ X -> EVl n G w0 X d0 w t) (snd (snd al)) eR
          eR1 = Eq-transport (\ X -> EVl n G w0 (REqValTyId.rhs core) X w t) (fst al) eR0
          le_wu = finMem-ref-le1 w t u v refMem
          le_wv = finMem-ref-le2 w t u v refMem
          fm_w_t = finMem-ref-wit w t u v refMem
          fmemIdU = FinMem-a-in-U (RefEl w) (IdCode t u v) refMem
          t_U = finMem-idU-dom t u v fmemIdU
          fm_u_t = finMem-idU-lhs t u v fmemIdU
          fm_v_t = finMem-idU-rhs t u v fmemIdU
          coh_w = FinMem-coh-u w t fm_w_t
          coh_t = coh-from-aU t t_U
          eqL_w = rstrE G (REqValTyId.lhs core) (REqValTyId.lhs' core) (REqValTyId.domA core) u w t le_wu fm_w_t fm_u_t (REqValTyId.eqL core)
          eqR_w = rstrE G (REqValTyId.rhs core) (REqValTyId.rhs' core) (REqValTyId.domA core) v w t le_wv fm_w_t fm_v_t (REqValTyId.eqR core)
          composedL = evt w t coh_w coh_t eL1 eqL_w
          composedR = evt w t coh_w coh_t eR1 eqR_w
          eL' = efwd w t coh_t (REqValTyId.eqA core) composedL
          eR' = efwd w t coh_t (REqValTyId.eqA core) composedR
      in mkSigma eL' eR'

    endEqFwd : {m : Nat} {G : Ctx m} {M C C' : Expr m} {w t u v : FinEl} ->
      (rid : RValId G M C w t u v) (core : REqValTyId G C C' t u v) ->
      Pair (EVl n G (RValId.wit0 rid) (REqValTyId.lhs' core) (REqValTyId.domA' core) w t)
           (EVl n G (RValId.wit0 rid) (REqValTyId.rhs' core) (REqValTyId.domA' core) w t)
    endEqFwd rid core =
      endEqFwdRaw (RValId.red rid) (RValId.refMem rid) (RValId.endEqL rid) (RValId.endEqR rid) core

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
    Esym (IdCode t u v) ca (mkSigma vtyM (mkSigma vtyN core)) =
      let ct    = fst ca
          uniqN = Red3-unique-Id (RValTyId.red vtyN) (REqValTyId.redN core)
          htA'  = Eq-transport (\ X -> HasType _ X _) (fst uniqN) (RValTyId.htA vtyN)
      in mkSigma vtyN (mkSigma vtyM (record
           { domA = REqValTyId.domA' core ; lhs = REqValTyId.lhs' core ; rhs = REqValTyId.rhs' core
           ; domA' = REqValTyId.domA core ; lhs' = REqValTyId.lhs core ; rhs' = REqValTyId.rhs core
           ; redM = REqValTyId.redN core ; redN = REqValTyId.redM core
           ; convA = conv-sym (REqValTyId.convA core)
           ; convL = conv-conv (conv-sym (REqValTyId.convL core)) (REqValTyId.convA core) htA'
           ; convR = conv-conv (conv-sym (REqValTyId.convR core)) (REqValTyId.convA core) htA'
           ; eqA = sym t ct (REqValTyId.eqA core)
           ; eqL = efwd u t ct (REqValTyId.eqA core) (evs u t (fst (snd ca)) ct (REqValTyId.eqL core))
           ; eqR = efwd v t ct (REqValTyId.eqA core) (evs v t (snd (snd ca)) ct (REqValTyId.eqR core))
           }))
    Esym (RefEl w) ca ev = tt

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
    Vfwd (IdCode u u1 u2) UCode cb eqv val = mkSigma (snd eqv) (snd val)
    Vfwd (RefEl u) UCode cb eqv val = tt
    Vfwd (IdCode u u1 u2) (PiCode b0 f0) cb eqv val = tt
    Vfwd (RefEl u) (PiCode b0 f0) cb eqv val = tt
    Vfwd u (RefEl a) cb eqv val = tt
    Vfwd Bot (IdCode t u v) cb eqv val = tt
    Vfwd UCode (IdCode t u v) cb eqv val = tt
    Vfwd (FunEl g) (IdCode t u v) cb eqv val = tt
    Vfwd (PiCode a' f') (IdCode t u v) cb eqv val = tt
    Vfwd (IdCode s0 s1 s2) (IdCode t u v) cb eqv val = tt
    Vfwd (RefEl w) (IdCode t u v) cb eqv val =
      let core = snd (snd eqv)
          cc   = idTyConvC (fst eqv) core ; cCC' = fst cc ; htC' = snd cc
          rid  = snd val
          rcs  = refConvsFwd rid core
          ees  = endEqFwd rid core
      in mkSigma (fst (snd eqv)) (record
        { domA0 = REqValTyId.domA' core ; lhs0 = REqValTyId.lhs' core ; rhs0 = REqValTyId.rhs' core
        ; red = REqValTyId.redN core ; wit0 = RValId.wit0 rid
        ; redTm = redTm-type-transport cCC' htC' (RValId.redTm rid)
        ; refConvL = fst rcs ; refConvR = snd rcs
        ; refMem = RValId.refMem rid
        ; endEqL = fst ees ; endEqR = snd ees })

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
    EVfwd (IdCode u u1 u2) UCode cb eqv ev = mkSigma (snd eqv) (snd ev)
    EVfwd (RefEl u) UCode cb eqv ev = tt
    EVfwd (IdCode u u1 u2) (PiCode b0 f0) cb eqv ev = tt
    EVfwd (RefEl u) (PiCode b0 f0) cb eqv ev = tt
    EVfwd u (RefEl a) cb eqv ev = tt
    EVfwd Bot (IdCode t u v) cb eqv ev = tt
    EVfwd UCode (IdCode t u v) cb eqv ev = tt
    EVfwd (FunEl g) (IdCode t u v) cb eqv ev = tt
    EVfwd (PiCode a' f') (IdCode t u v) cb eqv ev = tt
    EVfwd (IdCode s0 s1 s2) (IdCode t u v) cb eqv ev = tt
    EVfwd (RefEl w) (IdCode t u v) cb eqv ev =
      let core = snd (snd eqv)
          cc   = idTyConvC (fst eqv) core ; cCC' = fst cc ; htC' = snd cc
          ridM = fst (snd ev) ; ridN = fst (snd (snd ev)) ; reid = snd (snd (snd ev))
          dA0 = REqValTyId.domA' core ; l0 = REqValTyId.lhs' core ; r0 = REqValTyId.rhs' core ; rN = REqValTyId.redN core
          rcsM = refConvsFwd ridM core ; rcsN = refConvsFwd ridN core
          eesM = endEqFwd ridM core ; eesN = endEqFwd ridN core
          eesLM = endEqFwdRaw (REqValId.red reid) (REqValId.refMem reid) (REqValId.endEqLM reid) (REqValId.endEqRM reid) core
          eesLN = endEqFwdRaw (REqValId.red reid) (REqValId.refMem reid) (REqValId.endEqLN reid) (REqValId.endEqRN reid) core
      in mkSigma (fst (snd eqv))
        (mkSigma (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                         ; wit0 = RValId.wit0 ridM ; redTm = redTm-type-transport cCC' htC' (RValId.redTm ridM)
                         ; refConvL = fst rcsM ; refConvR = snd rcsM
                         ; refMem = RValId.refMem ridM
                         ; endEqL = fst eesM ; endEqR = snd eesM })
          (mkSigma (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                           ; wit0 = RValId.wit0 ridN ; redTm = redTm-type-transport cCC' htC' (RValId.redTm ridN)
                           ; refConvL = fst rcsN ; refConvR = snd rcsN
                           ; refMem = RValId.refMem ridN
                           ; endEqL = fst eesN ; endEqR = snd eesN })
                   (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                           ; wit0M = REqValId.wit0M reid ; wit0N = REqValId.wit0N reid
                           ; redTmM = redTm-type-transport cCC' htC' (REqValId.redTmM reid)
                           ; redTmN = redTm-type-transport cCC' htC' (REqValId.redTmN reid)
                           ; refMem = REqValId.refMem reid
                           ; endEqLM = fst eesLM ; endEqRM = snd eesLM
                           ; endEqLN = fst eesLN ; endEqRN = snd eesLN })))

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
    ETrans (IdCode t u v) cu eqAB eqBC =
      let vtyA   = fst eqAB
          coreAB = snd (snd eqAB)
          vtyC   = fst (snd eqBC)
          coreBC = snd (snd eqBC)
          ct = fst cu
          A0 = REqValTyId.domA coreAB
          lA = REqValTyId.lhs coreAB
          rA = REqValTyId.rhs coreAB
          B0' = REqValTyId.domA' coreAB
          lB' = REqValTyId.lhs' coreAB
          rB' = REqValTyId.rhs' coreAB
          rMA = REqValTyId.redM coreAB
          rNB = REqValTyId.redN coreAB
          convA_AB = REqValTyId.convA coreAB
          convL_AB = REqValTyId.convL coreAB
          convR_AB = REqValTyId.convR coreAB
          eqA_AB = REqValTyId.eqA coreAB
          B1 = REqValTyId.domA coreBC
          rMB = REqValTyId.redM coreBC
          rNC = REqValTyId.redN coreBC
          C0' = REqValTyId.domA' coreBC
          lC' = REqValTyId.lhs' coreBC
          rC' = REqValTyId.rhs' coreBC
          convA_BC = REqValTyId.convA coreBC
          convL_BC = REqValTyId.convL coreBC
          convR_BC = REqValTyId.convR coreBC
          eqA_BC = REqValTyId.eqA coreBC
          uniqB = Red3-unique-Id rNB rMB
          eqDom = fst uniqB
          eqLhs = fst (snd uniqB)
          eqRhs = snd (snd uniqB)
          uniqA = Red3-unique-Id (RValTyId.red vtyA) rMA
          htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniqA) (RValTyId.htA vtyA)
          convA_BC' = Eq-transport (\ X -> ConvTm _ X C0' _) (Eq-sym eqDom) convA_BC
          convA_AC  = conv-trans convA_AB convA_BC'
          eqA_BC'   = Eq-transport (\ X -> EVTy n _ X C0' t) (Eq-sym eqDom) eqA_BC
          eqA_AC    = etr t ct eqA_AB eqA_BC'
          convL_BC1 = Eq-transport (\ X -> ConvTm _ lB' lC' X) (Eq-sym eqDom)
                        (Eq-transport (\ X -> ConvTm _ X lC' B1) (Eq-sym eqLhs) convL_BC)
          convL_AC  = conv-trans convL_AB (conv-conv convL_BC1 (conv-sym convA_AB) htA0)
          convR_BC1 = Eq-transport (\ X -> ConvTm _ rB' rC' X) (Eq-sym eqDom)
                        (Eq-transport (\ X -> ConvTm _ X rC' B1) (Eq-sym eqRhs) convR_BC)
          convR_AC  = conv-trans convR_AB (conv-conv convR_BC1 (conv-sym convA_AB) htA0)
          eqL_BC0 = Eq-transport (\ X -> EVl n _ (REqValTyId.lhs coreBC) lC' X u t) (Eq-sym eqDom) (REqValTyId.eqL coreBC)
          eqL_BC1 = Eq-transport (\ X -> EVl n _ X lC' B0' u t) (Eq-sym eqLhs) eqL_BC0
          eqL_BCm = efwd u t ct (sym t ct eqA_AB) eqL_BC1
          eqL_AC  = evt u t (fst (snd cu)) ct (REqValTyId.eqL coreAB) eqL_BCm
          eqR_BC0 = Eq-transport (\ X -> EVl n _ (REqValTyId.rhs coreBC) rC' X v t) (Eq-sym eqDom) (REqValTyId.eqR coreBC)
          eqR_BC1 = Eq-transport (\ X -> EVl n _ X rC' B0' v t) (Eq-sym eqRhs) eqR_BC0
          eqR_BCm = efwd v t ct (sym t ct eqA_AB) eqR_BC1
          eqR_AC  = evt v t (snd (snd cu)) ct (REqValTyId.eqR coreAB) eqR_BCm
      in mkSigma vtyA (mkSigma vtyC (record
           { domA = A0 ; lhs = lA ; rhs = rA
           ; domA' = C0' ; lhs' = lC' ; rhs' = rC'
           ; redM = rMA ; redN = rNC
           ; convA = convA_AC ; convL = convL_AC ; convR = convR_AC
           ; eqA = eqA_AC ; eqL = eqL_AC ; eqR = eqR_AC
           }))
    ETrans (RefEl w) cu eqAB eqBC = tt

    EVsym u Bot cu ca tt = tt
    EVsym Bot UCode cu ca tt = tt
    EVsym UCode UCode cu ca ev =
      mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (Esym UCode cu (snd (snd (snd ev))))))
    EVsym (FunEl g) UCode cu ca ev = tt
    EVsym (PiCode a' f') UCode cu ca ev =
      mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (Esym (PiCode a' f') cu (snd (snd (snd ev))))))
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
    EVsym (IdCode t1 t2 t3) UCode cu ca ev =
      mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev))
        (Esym (IdCode t1 t2 t3) cu (snd (snd (snd ev))))))
    EVsym (RefEl w) UCode cu ca ev = tt
    EVsym (IdCode t1 t2 t3) (PiCode b f) cu ca ev = tt
    EVsym (RefEl w) (PiCode b f) cu ca ev = tt
    EVsym (RefEl w) (IdCode t' u' v') cu ca ev =
      let e = snd (snd (snd ev))
      in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev))
           (record { domA0 = REqValId.domA0 e ; lhs0 = REqValId.lhs0 e
                   ; rhs0 = REqValId.rhs0 e ; red = REqValId.red e ; wit0M = REqValId.wit0N e ; wit0N = REqValId.wit0M e ; redTmM = REqValId.redTmN e ; redTmN = REqValId.redTmM e ; refMem = REqValId.refMem e
                   ; endEqLM = REqValId.endEqLN e ; endEqRM = REqValId.endEqRN e ; endEqLN = REqValId.endEqLM e ; endEqRN = REqValId.endEqRM e })))
    EVsym Bot (IdCode a a1 a2) cu ca ev = tt
    EVsym UCode (IdCode a a1 a2) cu ca ev = tt
    EVsym (FunEl g) (IdCode a a1 a2) cu ca ev = tt
    EVsym (PiCode b f) (IdCode a a1 a2) cu ca ev = tt
    EVsym (IdCode s0 s1 s2) (IdCode a a1 a2) cu ca ev = tt
    EVsym u (RefEl a) cu ca ev = tt

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
    EVtrans (IdCode t1 t2 t3) UCode cu ca ev1 ev2 =
      mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
        (ETrans (IdCode t1 t2 t3) cu (snd (snd (snd ev1))) (snd (snd (snd ev2))))))
    EVtrans (RefEl w) UCode cu ca ev1 ev2 = tt
    EVtrans (IdCode t1 t2 t3) (PiCode b f) cu ca ev1 ev2 = tt
    EVtrans (RefEl w) (PiCode b f) cu ca ev1 ev2 = tt
    EVtrans (RefEl w) (IdCode t' u' v') cu ca ev1 ev2 =
      let e = snd (snd (snd ev1)) ; e2 = snd (snd (snd ev2))
          alE = Red3-unique-Id (REqValId.red e2) (REqValId.red e)
          endEqLN' = Eq-transport (\ X -> EVl n _ (REqValId.wit0N e2) (REqValId.lhs0 e) X w t') (fst alE)
                       (Eq-transport (\ X -> EVl n _ (REqValId.wit0N e2) X (REqValId.domA0 e2) w t') (fst (snd alE)) (REqValId.endEqLN e2))
          endEqRN' = Eq-transport (\ X -> EVl n _ (REqValId.wit0N e2) (REqValId.rhs0 e) X w t') (fst alE)
                       (Eq-transport (\ X -> EVl n _ (REqValId.wit0N e2) X (REqValId.domA0 e2) w t') (snd (snd alE)) (REqValId.endEqRN e2))
      in mkSigma (fst ev1) (mkSigma (fst (snd ev1)) (mkSigma (fst (snd (snd ev2)))
           (record { domA0 = REqValId.domA0 e ; lhs0 = REqValId.lhs0 e
                   ; rhs0 = REqValId.rhs0 e ; red = REqValId.red e ; wit0M = REqValId.wit0M e ; wit0N = REqValId.wit0N e2 ; redTmM = REqValId.redTmM e ; redTmN = REqValId.redTmN e2 ; refMem = REqValId.refMem e
                   ; endEqLM = REqValId.endEqLM e ; endEqRM = REqValId.endEqRM e ; endEqLN = endEqLN' ; endEqRN = endEqRN' })))
    EVtrans Bot (IdCode a a1 a2) cu ca ev1 ev2 = tt
    EVtrans UCode (IdCode a a1 a2) cu ca ev1 ev2 = tt
    EVtrans (FunEl g) (IdCode a a1 a2) cu ca ev1 ev2 = tt
    EVtrans (PiCode b f) (IdCode a a1 a2) cu ca ev1 ev2 = tt
    EVtrans (IdCode s0 s1 s2) (IdCode a a1 a2) cu ca ev1 ev2 = tt
    EVtrans u (RefEl a) cu ca ev1 ev2 = tt

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
    -- Value-level compatible-sup closure at a FIXED type-code a (Coquand): the
    -- logical mirror of the kernel's FinMem-Sup-element (sup the value-code, keep
    -- the type-code fixed).  The general two-code form is derivable from this plus
    -- type-code monotonicity (upVal2), so only the fixed-code form is proved here.
    Val2-Sup : {n : Nat} (G : Ctx n) (M A : Expr n) (u1 u2 a : FinEl) ->
      Comp u1 u2 -> Coherent a -> FinMem a UCode -> FinMem u1 a -> FinMem u2 a ->
      Vl k G M A u1 a -> Vl k G M A u2 a -> Vl k G M A (Sup u1 u2) a
    EqVal2-Sup : {n : Nat} (G : Ctx n) (M N A : Expr n) (u1 u2 a : FinEl) ->
      Comp u1 u2 -> Coherent a -> FinMem a UCode -> FinMem u1 a -> FinMem u2 a ->
      EVl k G M N A u1 a -> EVl k G M N A u2 a -> EVl k G M N A (Sup u1 u2) a

goodStageSup : (k : Nat) -> SupPack k
goodStageSup zero = record
  { ValTy2-Sup   = \ G T a1 a2 comp fm1 fm2 vt1 vt2 -> tt
  ; EqValTy2-Sup = \ G M N u1 u2 comp fm1 fm2 eq1 eq2 -> tt
  ; Val2-Sup     = \ G M A u1 u2 a comp ca fma fm1 fm2 vt1 vt2 -> tt
  ; EqVal2-Sup   = \ G M N A u1 u2 a comp ca fma fm1 fm2 eq1 eq2 -> tt
  }
goodStageSup (suc n) = record
  { ValTy2-Sup = VSup ; EqValTy2-Sup = EVSup
  ; Val2-Sup = VLSup ; EqVal2-Sup = EVLSup }
  where
    ihSup : SupPack n
    ihSup = goodStageSup n
    ihM : MonoPack n
    ihM = goodStage n
    open SR n
    vsup  = SupPack.ValTy2-Sup ihSup
    evsup = SupPack.EqValTy2-Sup ihSup
    vlsup  = SupPack.Val2-Sup ihSup
    evlsup = SupPack.EqVal2-Sup ihSup
    rstr  = MonoPack.restrictVal2 ihM
    rstrE = MonoPack.restrictEqVal2 ihM
    dV    = MonoPack.downVal2 ihM
    dEV   = MonoPack.downEqVal2 ihM
    dVT   = MonoPack.downValTy2 ihM
    dEVT  = MonoPack.downEqValTy2 ihM
    uV    = MonoPack.upVal2 ihM
    uEV   = MonoPack.upEqVal2 ihM
    v1st  = MonoPack.Val2-from-EqVal2-first ihM

    -- Join two Id-proof endpoint equalities at compatible witness codes w1, w2
    -- (fixed type-code t): align the second (via witness/endpoint/domain Eqs)
    -- to the first's terms, then EqVal2-Sup the value codes.
    joinE : {m : Nat} {G : Ctx m} {wit1 e1 d1 wit2 e2 d2 : Expr m} (w1 w2 t : FinEl) ->
      Comp w1 w2 -> Coherent t -> FinMem t UCode -> FinMem w1 t -> FinMem w2 t ->
      Eq wit2 wit1 -> Eq e2 e1 -> Eq d2 d1 ->
      EVl n G wit1 e1 d1 w1 t -> EVl n G wit2 e2 d2 w2 t ->
      EVl n G wit1 e1 d1 (Sup w1 w2) t
    joinE {G = G} {wit1 = wit1} {e1 = e1} {d1 = d1} {wit2 = wit2} {e2 = e2} {d2 = d2} w1 w2 t comp coh_t t_U fmw1 fmw2 weq eeq deq ee1 ee2 =
      evlsup G wit1 e1 d1 w1 w2 t comp coh_t t_U fmw1 fmw2 ee1
        (Eq-transport (\ X -> EVl n G X e1 d1 w2 t) weq
          (Eq-transport (\ X -> EVl n G wit2 X d1 w2 t) eeq
            (Eq-transport (\ X -> EVl n G wit2 e2 X w2 t) deq ee2)))

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
    VSup G T (IdCode a1 a3 a4) Bot comp fm1 fm2 vt1 vt2 = vt1
    VSup G T (IdCode a1 a3 a4) UCode ()
    VSup G T (IdCode a1 a3 a4) (FunEl h) ()
    VSup G T (IdCode a1 a3 a4) (PiCode b g) ()
    VSup G T (IdCode a1 a3 a4) (RefEl w) ()
    VSup G T (IdCode a1 a3 a4) (IdCode b1 b3 b4) comp fm1 fm2 vt1 vt2 =
      let comp-t = fst comp
          A1 = RValTyId.domA vt1 ; l1 = RValTyId.lhs vt1 ; r1 = RValTyId.rhs vt1
          uniq = Red3-unique-Id (RValTyId.red vt1) (RValTyId.red vt2)
          eqDom = fst uniq ; eqLhs = fst (snd uniq) ; eqRhs = snd (snd uniq)
          comp-l = fst (snd comp) ; comp-r = snd (snd comp)
          a1U = finMem-idU-dom a1 a3 a4 fm1
          b1U = finMem-idU-dom b1 b3 b4 fm2
          valA2 = Eq-transport (\ X -> VTy n G X b1) (Eq-sym eqDom) (RValTyId.valA vt2)
          valA-sup = vsup G A1 a1 b1 comp-t a1U b1U (RValTyId.valA vt1) valA2
          -- endpoints: paper Lemma 2 (finMem-Sup-both) closes membership under
          -- compatible binary sup, uniformly (functions included).
          valL-sup = finMem-Sup-both a3 b3 a1 b1
                       (finMem-idU-lhs a1 a3 a4 fm1) (finMem-idU-lhs b1 b3 b4 fm2) comp-t comp-l
          valR-sup = finMem-Sup-both a4 b4 a1 b1
                       (finMem-idU-rhs a1 a3 a4 fm1) (finMem-idU-rhs b1 b3 b4 fm2) comp-t comp-r
          ca1 = coh-from-aU a1 a1U ; cb1 = coh-from-aU b1 b1U
          sup1U = finMemUCode-Sup a1 b1 comp-t a1U b1U
          csup1 = Coherent-Sup a1 b1 comp-t ca1 cb1
          le-a1 = LeCode-Sup-left a1 b1 comp-t ca1 cb1
          le-b1 = LeCode-Sup-right a1 b1 comp-t ca1 cb1
          fm-a3-a1 = finMem-idU-lhs a1 a3 a4 fm1 ; fm-b3-b1 = finMem-idU-lhs b1 b3 b4 fm2
          fm-a4-a1 = finMem-idU-rhs a1 a3 a4 fm1 ; fm-b4-b1 = finMem-idU-rhs b1 b3 b4 fm2
          fm-a3-sup = finMem-upward a3 a1 (Sup a1 b1) le-a1 ca1 csup1 fm-a3-a1 sup1U
          fm-b3-sup = finMem-upward b3 b1 (Sup a1 b1) le-b1 cb1 csup1 fm-b3-b1 sup1U
          fm-a4-sup = finMem-upward a4 a1 (Sup a1 b1) le-a1 ca1 csup1 fm-a4-a1 sup1U
          fm-b4-sup = finMem-upward b4 b1 (Sup a1 b1) le-b1 cb1 csup1 fm-b4-b1 sup1U
          vll2-al = Eq-transport (\ X -> Vl n G X A1 b3 b1) (Eq-sym eqLhs)
                      (Eq-transport (\ X -> Vl n G (RValTyId.lhs vt2) X b3 b1) (Eq-sym eqDom) (RValTyId.valLlog vt2))
          vlr2-al = Eq-transport (\ X -> Vl n G X A1 b4 b1) (Eq-sym eqRhs)
                      (Eq-transport (\ X -> Vl n G (RValTyId.rhs vt2) X b4 b1) (Eq-sym eqDom) (RValTyId.valRlog vt2))
          vll1-up = uV G l1 A1 a3 a1 (Sup a1 b1) le-a1 fm-a3-a1 fm-a3-sup ca1 csup1 (RValTyId.valLlog vt1) valA-sup
          vll2-up = uV G l1 A1 b3 b1 (Sup a1 b1) le-b1 fm-b3-b1 fm-b3-sup cb1 csup1 vll2-al valA-sup
          valLlog-sup = vlsup G l1 A1 a3 b3 (Sup a1 b1) comp-l csup1 sup1U fm-a3-sup fm-b3-sup vll1-up vll2-up
          vlr1-up = uV G r1 A1 a4 a1 (Sup a1 b1) le-a1 fm-a4-a1 fm-a4-sup ca1 csup1 (RValTyId.valRlog vt1) valA-sup
          vlr2-up = uV G r1 A1 b4 b1 (Sup a1 b1) le-b1 fm-b4-b1 fm-b4-sup cb1 csup1 vlr2-al valA-sup
          valRlog-sup = vlsup G r1 A1 a4 b4 (Sup a1 b1) comp-r csup1 sup1U fm-a4-sup fm-b4-sup vlr1-up vlr2-up
      in record
           { domA = A1 ; lhs = l1 ; rhs = r1
           ; red = RValTyId.red vt1
           ; htA = RValTyId.htA vt1 ; htL = RValTyId.htL vt1 ; htR = RValTyId.htR vt1
           ; valA = valA-sup
           ; valL = valL-sup
           ; valR = valR-sup
           ; valLlog = valLlog-sup
           ; valRlog = valRlog-sup
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
    EVSup G M N (IdCode u1 u3 u4) Bot comp fm1 fm2 eq1 eq2 = eq1
    EVSup G M N (IdCode u1 u3 u4) UCode ()
    EVSup G M N (IdCode u1 u3 u4) (FunEl h) ()
    EVSup G M N (IdCode u1 u3 u4) (PiCode b g) ()
    EVSup G M N (IdCode u1 u3 u4) (RefEl w) ()
    EVSup G M N (IdCode u1 u3 u4) (IdCode v1 v3 v4) comp fm1 fm2 eq1 eq2 =
      let eqId1 = snd (snd eq1) ; eqId2 = snd (snd eq2)
          AM = REqValTyId.domA eqId1 ; lM = REqValTyId.lhs eqId1 ; rM = REqValTyId.rhs eqId1
          AN = REqValTyId.domA' eqId1 ; lN = REqValTyId.lhs' eqId1 ; rN = REqValTyId.rhs' eqId1
          redM1 = REqValTyId.redM eqId1 ; redN1 = REqValTyId.redN eqId1
          AM2 = REqValTyId.domA eqId2 ; AN2 = REqValTyId.domA' eqId2
          redM2 = REqValTyId.redM eqId2 ; redN2 = REqValTyId.redN eqId2
          uniqM = Red3-unique-Id redM1 redM2 ; eqAM = fst uniqM
          uniqN = Red3-unique-Id redN1 redN2 ; eqAN = fst uniqN
          eqvtA2' = Eq-transport (\ X -> EVTy n G X AN v1) (Eq-sym eqAM)
                      (Eq-transport (\ X -> EVTy n G AM2 X v1) (Eq-sym eqAN) (REqValTyId.eqA eqId2))
          comp-t = fst comp
          a1U = finMem-idU-dom u1 u3 u4 fm1
          b1U = finMem-idU-dom v1 v3 v4 fm2
          eqvtA-sup = evsup G AM AN u1 v1 comp-t a1U b1U (REqValTyId.eqA eqId1) eqvtA2'
          vtM-sup = VSup G M (IdCode u1 u3 u4) (IdCode v1 v3 v4) comp fm1 fm2 (fst eq1) (fst eq2)
          vtN-sup = VSup G N (IdCode u1 u3 u4) (IdCode v1 v3 v4) comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2))
          cu1 = coh-from-aU u1 a1U ; cv1 = coh-from-aU v1 b1U
          sup1U = finMemUCode-Sup u1 v1 comp-t a1U b1U
          csup1 = Coherent-Sup u1 v1 comp-t cu1 cv1
          le-u1 = LeCode-Sup-left u1 v1 comp-t cu1 cv1
          le-v1 = LeCode-Sup-right u1 v1 comp-t cu1 cv1
          comp-l = fst (snd comp) ; comp-r = snd (snd comp)
          fm-u3-u1 = finMem-idU-lhs u1 u3 u4 fm1 ; fm-v3-v1 = finMem-idU-lhs v1 v3 v4 fm2
          fm-u4-u1 = finMem-idU-rhs u1 u3 u4 fm1 ; fm-v4-v1 = finMem-idU-rhs v1 v3 v4 fm2
          fm-u3-sup = finMem-upward u3 u1 (Sup u1 v1) le-u1 cu1 csup1 fm-u3-u1 sup1U
          fm-v3-sup = finMem-upward v3 v1 (Sup u1 v1) le-v1 cv1 csup1 fm-v3-v1 sup1U
          fm-u4-sup = finMem-upward u4 u1 (Sup u1 v1) le-u1 cu1 csup1 fm-u4-u1 sup1U
          fm-v4-sup = finMem-upward v4 v1 (Sup u1 v1) le-v1 cv1 csup1 fm-v4-v1 sup1U
          vtM-supA = Eq-transport (\ X -> VTy n G X (Sup u1 v1)) (fst (Red3-unique-Id (RValTyId.red vtM-sup) redM1)) (RValTyId.valA vtM-sup)
          eqL2-al = Eq-transport (\ X -> EVl n G X lN AM v3 v1) (Eq-sym (fst (snd uniqM)))
                      (Eq-transport (\ X -> EVl n G (REqValTyId.lhs eqId2) X AM v3 v1) (Eq-sym (fst (snd uniqN)))
                        (Eq-transport (\ X -> EVl n G (REqValTyId.lhs eqId2) (REqValTyId.lhs' eqId2) X v3 v1) (Eq-sym eqAM) (REqValTyId.eqL eqId2)))
          eqR2-al = Eq-transport (\ X -> EVl n G X rN AM v4 v1) (Eq-sym (snd (snd uniqM)))
                      (Eq-transport (\ X -> EVl n G (REqValTyId.rhs eqId2) X AM v4 v1) (Eq-sym (snd (snd uniqN)))
                        (Eq-transport (\ X -> EVl n G (REqValTyId.rhs eqId2) (REqValTyId.rhs' eqId2) X v4 v1) (Eq-sym eqAM) (REqValTyId.eqR eqId2)))
          eqL1-up = uEV G lM lN AM u3 u1 (Sup u1 v1) le-u1 fm-u3-u1 fm-u3-sup cu1 csup1 (REqValTyId.eqL eqId1) vtM-supA
          eqL2-up = uEV G lM lN AM v3 v1 (Sup u1 v1) le-v1 fm-v3-v1 fm-v3-sup cv1 csup1 eqL2-al vtM-supA
          eqL-sup = evlsup G lM lN AM u3 v3 (Sup u1 v1) comp-l csup1 sup1U fm-u3-sup fm-v3-sup eqL1-up eqL2-up
          eqR1-up = uEV G rM rN AM u4 u1 (Sup u1 v1) le-u1 fm-u4-u1 fm-u4-sup cu1 csup1 (REqValTyId.eqR eqId1) vtM-supA
          eqR2-up = uEV G rM rN AM v4 v1 (Sup u1 v1) le-v1 fm-v4-v1 fm-v4-sup cv1 csup1 eqR2-al vtM-supA
          eqR-sup = evlsup G rM rN AM u4 v4 (Sup u1 v1) comp-r csup1 sup1U fm-u4-sup fm-v4-sup eqR1-up eqR2-up
          core = record
            { domA = AM ; lhs = lM ; rhs = rM
            ; domA' = AN ; lhs' = lN ; rhs' = rN
            ; redM = redM1 ; redN = redN1
            ; convA = REqValTyId.convA eqId1
            ; convL = REqValTyId.convL eqId1
            ; convR = REqValTyId.convR eqId1
            ; eqA = eqvtA-sup ; eqL = eqL-sup ; eqR = eqR-sup }
      in mkSigma vtM-sup (mkSigma vtN-sup core)

    ------------------------------------------------------------------------
    -- Value-level compatible sup at a FIXED Pi type-code (PiCode b f): the
    -- appended value-graph (append g1 g2).  appVSup / appESup / appEVSup build
    -- the PiAppVal2 / PiAppEq2 / PiAppEqVal2 edges; the recursion into the
    -- codomain value-code is `vlsup`/`evlsup` (the IH from ihSup).  Modelled on
    -- ID/Model/Eval.agda EvalRel-Sup (FunEl case) and VSup's PiCode edge.
    ------------------------------------------------------------------------

    appVSup : {m : Nat} (G : Ctx m) (M A : Expr m) (g1 g2 : FinFun) (b : FinEl) (f : FinFun) ->
      Comp (FunEl g1) (FunEl g2) -> Coherent (PiCode b f) -> FinMem (PiCode b f) UCode ->
      RValTyPi G A b f ->
      (rv1 : RValPi G M A g1 b f) (rv2 : RValPi G M A g2 b f) ->
      PiAppVal2 G M (RValPi.domA0 rv1) (RValPi.codB0 rv1) b f (append g1 g2)
    appVSup G M A g1 g2 b f comp ca fma vtCod rv1 rv2 = \ u v sel N htN valN ->
      let cb    = fst ca
          ctf   = snd ca
          bU    = finMem-piU-dom b f fma
          allUf = finMem-piU-allU b f fma
          cg1   = RValPi.cohG rv1
          cg2   = RValPi.cohG rv2
          ctg1  = cft-from-cf g1 cg1
          ctg2  = cft-from-cf g2 cg2
          A0    = RValPi.domA0 rv1
          B0    = RValPi.codB0 rv1
          uniq  = Red3-unique-Pi (RValPi.red rv1) (RValPi.red rv2)
          eqA   = fst uniq
          eqB   = snd uniq
          appV2' : PiAppVal2 G M A0 B0 b f g2
          appV2' = Eq-transport (\ Y -> PiAppVal2 G M A0 Y b f g2) (Eq-sym eqB)
                     (Eq-transport (\ X -> PiAppVal2 G M X (RValPi.codB0 rv2) b f g2) (Eq-sym eqA)
                       (RValPi.appV rv2))
          fmG-app  = FinMemFun-append g1 g2 b f (RValPi.fmG rv1) (RValPi.fmG rv2)
          cohG-app = CoherentFun-append g1 g2 cg1 cg2 comp
          ctg-app  = cft-from-cf (append g1 g2) cohG-app
          uniqC = Red3-unique-Pi (RValTyPi.red vtCod) (RValPi.red rv1)
          eqCA  = fst uniqC
          eqCB  = snd uniqC
          edgeV' : PiEdgeVal2 G A0 B0 b f
          edgeV' = Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b f) eqCB
                     (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtCod) b f) eqCA
                       (RValTyPi.edgeV vtCod))
          cu    = Coherent-Selection sel ctg-app
          sb1   = selectionBelow g1 u ctg1 cu
          ug1   = fst sb1
          vg1   = fst (snd sb1)
          selg1 = fst (snd (snd sb1))
          le-ug1 = fst (snd (snd (snd sb1)))
          eq-vg1 = snd (snd (snd (snd sb1)))
          sb2   = selectionBelow g2 u ctg2 cu
          ug2   = fst sb2
          vg2   = fst (snd sb2)
          selg2 = fst (snd (snd sb2))
          le-ug2 = fst (snd (snd (snd sb2)))
          eq-vg2 = snd (snd (snd (snd sb2)))
          cug1  = Coherent-Selection selg1 ctg1
          cug2  = Coherent-Selection selg2 ctg2
          fmug1-b = FinMem-Selection b f selg1 (RValPi.fmG rv1) ctg1 cb bU
          fmug2-b = FinMem-Selection b f selg2 (RValPi.fmG rv2) ctg2 cb bU
          fmu-b   = FinMem-Selection b f sel fmG-app ctg-app cb bU
          valN1 = rstr G N A0 u ug1 b le-ug1 fmug1-b fmu-b valN
          valN2 = rstr G N A0 u ug2 b le-ug2 fmug2-b fmu-b valN
          r1 = RValPi.appV rv1 ug1 vg1 selg1 N htN valN1
          r2 = appV2' ug2 vg2 selg2 N htN valN2
          selff  = selectionBelow f u ctf cu
          uf     = fst selff
          vf     = fst (snd selff)
          self   = fst (snd (snd selff))
          le-uf  = fst (snd (snd (snd selff)))
          eq-vf  = snd (snd (snd (snd selff)))
          fmuf-b = FinMemAllU-Selection b self allUf ctf cb bU
          valNuf = rstr G N A0 u uf b le-uf fmuf-b fmu-b valN
          vt-vf  = edgeV' uf vf self N htN valNuf
          vtyCod = Eq-transport (\ x -> VTy n G (subst1 B0 N) x) (Eq-sym eq-vf) vt-vf
          c-ef-ug1 = Coherent-EvalFun f ug1 ctf cug1
          c-ef-ug2 = Coherent-EvalFun f ug2 ctf cug2
          c-ef-u   = Coherent-EvalFun f u ctf cu
          ef-u-U   = EvalFun-in-UCode f u b ctf cu allUf
          le-ef1 = EvalFun-mon-arg f ug1 u le-ug1 ctf cug1 cu
          le-ef2 = EvalFun-mon-arg f ug2 u le-ug2 ctf cug2 cu
          fmVg1-ef-ug1 = FinMem-Selection-codomain b f selg1 (RValPi.fmG rv1) ctg1 ctf allUf
          fmVg2-ef-ug2 = FinMem-Selection-codomain b f selg2 (RValPi.fmG rv2) ctg2 ctf allUf
          fmVg1-ef-u = finMem-upward vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 c-ef-ug1 c-ef-u fmVg1-ef-ug1 ef-u-U
          fmVg2-ef-u = finMem-upward vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 c-ef-ug2 c-ef-u fmVg2-ef-ug2 ef-u-U
          r1' = uV G (App M N) (subst1 B0 N) vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 fmVg1-ef-ug1 fmVg1-ef-u c-ef-ug1 c-ef-u r1 vtyCod
          r2' = uV G (App M N) (subst1 B0 N) vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 fmVg2-ef-ug2 fmVg2-ef-u c-ef-ug2 c-ef-u r2 vtyCod
          comp-vg-ef = comp-EvalFun g1 g2 u comp ctg1 cu
          comp-v = Eq-transport (\ y -> Comp vg1 y) eq-vg2
                     (Eq-transport (\ x -> Comp x (EvalFun g2 u)) eq-vg1 comp-vg-ef)
          fmSup-ef = FinMem-Sup-element vg1 vg2 (EvalFun f u) comp-v c-ef-u fmVg1-ef-u fmVg2-ef-u
          supr = vlsup G (App M N) (subst1 B0 N) vg1 vg2 (EvalFun f u) comp-v c-ef-u ef-u-U fmVg1-ef-u fmVg2-ef-u r1' r2'
          eq-app = EvalFun-append-eq g1 g2 u comp ctg1 cu
          lf-refl = LeFunCode-refl (append g1 g2) ctg-app
          le-v-appf = Selection-le-EvalFun (append g1 g2) sel lf-refl ctg-app ctg-app cu
          le-v-supEf = Eq-transport (\ x -> LeCode v x) eq-app le-v-appf
          le-v-supv = Eq-transport (\ y -> LeCode v (Sup vg1 y)) eq-vg2
                        (Eq-transport (\ x -> LeCode v (Sup x (EvalFun g2 u))) eq-vg1 le-v-supEf)
          fmv-ef = FinMem-Selection-codomain b f sel fmG-app ctg-app ctf allUf
      in rstr G (App M N) (subst1 B0 N) (Sup vg1 vg2) v (EvalFun f u) le-v-supv fmv-ef fmSup-ef supr

    appESup : {m : Nat} (G : Ctx m) (M A : Expr m) (g1 g2 : FinFun) (b : FinEl) (f : FinFun) ->
      Comp (FunEl g1) (FunEl g2) -> Coherent (PiCode b f) -> FinMem (PiCode b f) UCode ->
      RValTyPi G A b f ->
      (rv1 : RValPi G M A g1 b f) (rv2 : RValPi G M A g2 b f) ->
      PiAppEq2 G M (RValPi.domA0 rv1) (RValPi.codB0 rv1) b f (append g1 g2)
    appESup G M A g1 g2 b f comp ca fma vtCod rv1 rv2 = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let cb    = fst ca
          ctf   = snd ca
          bU    = finMem-piU-dom b f fma
          allUf = finMem-piU-allU b f fma
          cg1   = RValPi.cohG rv1
          cg2   = RValPi.cohG rv2
          ctg1  = cft-from-cf g1 cg1
          ctg2  = cft-from-cf g2 cg2
          A0    = RValPi.domA0 rv1
          B0    = RValPi.codB0 rv1
          uniq  = Red3-unique-Pi (RValPi.red rv1) (RValPi.red rv2)
          eqA   = fst uniq
          eqB   = snd uniq
          appE2' : PiAppEq2 G M A0 B0 b f g2
          appE2' = Eq-transport (\ Y -> PiAppEq2 G M A0 Y b f g2) (Eq-sym eqB)
                     (Eq-transport (\ X -> PiAppEq2 G M X (RValPi.codB0 rv2) b f g2) (Eq-sym eqA)
                       (RValPi.appE rv2))
          fmG-app  = FinMemFun-append g1 g2 b f (RValPi.fmG rv1) (RValPi.fmG rv2)
          cohG-app = CoherentFun-append g1 g2 cg1 cg2 comp
          ctg-app  = cft-from-cf (append g1 g2) cohG-app
          uniqC = Red3-unique-Pi (RValTyPi.red vtCod) (RValPi.red rv1)
          eqCA  = fst uniqC
          eqCB  = snd uniqC
          edgeV' : PiEdgeVal2 G A0 B0 b f
          edgeV' = Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b f) eqCB
                     (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtCod) b f) eqCA
                       (RValTyPi.edgeV vtCod))
          cu    = Coherent-Selection sel ctg-app
          sb1   = selectionBelow g1 u ctg1 cu
          ug1   = fst sb1
          vg1   = fst (snd sb1)
          selg1 = fst (snd (snd sb1))
          le-ug1 = fst (snd (snd (snd sb1)))
          eq-vg1 = snd (snd (snd (snd sb1)))
          sb2   = selectionBelow g2 u ctg2 cu
          ug2   = fst sb2
          vg2   = fst (snd sb2)
          selg2 = fst (snd (snd sb2))
          le-ug2 = fst (snd (snd (snd sb2)))
          eq-vg2 = snd (snd (snd (snd sb2)))
          cug1  = Coherent-Selection selg1 ctg1
          cug2  = Coherent-Selection selg2 ctg2
          fmug1-b = FinMem-Selection b f selg1 (RValPi.fmG rv1) ctg1 cb bU
          fmug2-b = FinMem-Selection b f selg2 (RValPi.fmG rv2) ctg2 cb bU
          fmu-b   = FinMem-Selection b f sel fmG-app ctg-app cb bU
          eqN1 = rstrE G N1 N2 A0 u ug1 b le-ug1 fmug1-b fmu-b eqN
          eqN2 = rstrE G N1 N2 A0 u ug2 b le-ug2 fmug2-b fmu-b eqN
          r1 = RValPi.appE rv1 ug1 vg1 selg1 N1 N2 htN1 htN2 cvN eqN1
          r2 = appE2' ug2 vg2 selg2 N1 N2 htN1 htN2 cvN eqN2
          selff  = selectionBelow f u ctf cu
          uf     = fst selff
          vf     = fst (snd selff)
          self   = fst (snd (snd selff))
          le-uf  = fst (snd (snd (snd selff)))
          eq-vf  = snd (snd (snd (snd selff)))
          valN-u = v1st u b eqN
          fmuf-b = FinMemAllU-Selection b self allUf ctf cb bU
          valNuf = rstr G N1 A0 u uf b le-uf fmuf-b fmu-b valN-u
          vt-vf  = edgeV' uf vf self N1 htN1 valNuf
          vtyCod = Eq-transport (\ x -> VTy n G (subst1 B0 N1) x) (Eq-sym eq-vf) vt-vf
          c-ef-ug1 = Coherent-EvalFun f ug1 ctf cug1
          c-ef-ug2 = Coherent-EvalFun f ug2 ctf cug2
          c-ef-u   = Coherent-EvalFun f u ctf cu
          ef-u-U   = EvalFun-in-UCode f u b ctf cu allUf
          le-ef1 = EvalFun-mon-arg f ug1 u le-ug1 ctf cug1 cu
          le-ef2 = EvalFun-mon-arg f ug2 u le-ug2 ctf cug2 cu
          fmVg1-ef-ug1 = FinMem-Selection-codomain b f selg1 (RValPi.fmG rv1) ctg1 ctf allUf
          fmVg2-ef-ug2 = FinMem-Selection-codomain b f selg2 (RValPi.fmG rv2) ctg2 ctf allUf
          fmVg1-ef-u = finMem-upward vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 c-ef-ug1 c-ef-u fmVg1-ef-ug1 ef-u-U
          fmVg2-ef-u = finMem-upward vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 c-ef-ug2 c-ef-u fmVg2-ef-ug2 ef-u-U
          r1' = uEV G (App M N1) (App M N2) (subst1 B0 N1) vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 fmVg1-ef-ug1 fmVg1-ef-u c-ef-ug1 c-ef-u r1 vtyCod
          r2' = uEV G (App M N1) (App M N2) (subst1 B0 N1) vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 fmVg2-ef-ug2 fmVg2-ef-u c-ef-ug2 c-ef-u r2 vtyCod
          comp-vg-ef = comp-EvalFun g1 g2 u comp ctg1 cu
          comp-v = Eq-transport (\ y -> Comp vg1 y) eq-vg2
                     (Eq-transport (\ x -> Comp x (EvalFun g2 u)) eq-vg1 comp-vg-ef)
          fmSup-ef = FinMem-Sup-element vg1 vg2 (EvalFun f u) comp-v c-ef-u fmVg1-ef-u fmVg2-ef-u
          supr = evlsup G (App M N1) (App M N2) (subst1 B0 N1) vg1 vg2 (EvalFun f u) comp-v c-ef-u ef-u-U fmVg1-ef-u fmVg2-ef-u r1' r2'
          eq-app = EvalFun-append-eq g1 g2 u comp ctg1 cu
          lf-refl = LeFunCode-refl (append g1 g2) ctg-app
          le-v-appf = Selection-le-EvalFun (append g1 g2) sel lf-refl ctg-app ctg-app cu
          le-v-supEf = Eq-transport (\ x -> LeCode v x) eq-app le-v-appf
          le-v-supv = Eq-transport (\ y -> LeCode v (Sup vg1 y)) eq-vg2
                        (Eq-transport (\ x -> LeCode v (Sup x (EvalFun g2 u))) eq-vg1 le-v-supEf)
          fmv-ef = FinMem-Selection-codomain b f sel fmG-app ctg-app ctf allUf
      in rstrE G (App M N1) (App M N2) (subst1 B0 N1) (Sup vg1 vg2) v (EvalFun f u) le-v-supv fmv-ef fmSup-ef supr

    appEVSup : {m : Nat} (G : Ctx m) (M N A : Expr m) (g1 g2 : FinFun) (b : FinEl) (f : FinFun) ->
      Comp (FunEl g1) (FunEl g2) -> Coherent (PiCode b f) -> FinMem (PiCode b f) UCode ->
      RValTyPi G A b f ->
      (rveq1 : REqValPi G M N A g1 b f) (rveq2 : REqValPi G M N A g2 b f) ->
      PiAppEqVal2 G M N (REqValPi.domA0 rveq1) (REqValPi.codB0 rveq1) b f (append g1 g2)
    appEVSup G M N A g1 g2 b f comp ca fma vtCod rveq1 rveq2 = \ u v sel P htP valP ->
      let cb    = fst ca
          ctf   = snd ca
          bU    = finMem-piU-dom b f fma
          allUf = finMem-piU-allU b f fma
          cg1   = REqValPi.cohG rveq1
          cg2   = REqValPi.cohG rveq2
          ctg1  = cft-from-cf g1 cg1
          ctg2  = cft-from-cf g2 cg2
          A0    = REqValPi.domA0 rveq1
          B0    = REqValPi.codB0 rveq1
          uniq  = Red3-unique-Pi (REqValPi.red rveq1) (REqValPi.red rveq2)
          eqA   = fst uniq
          eqB   = snd uniq
          appEV2' : PiAppEqVal2 G M N A0 B0 b f g2
          appEV2' = Eq-transport (\ Y -> PiAppEqVal2 G M N A0 Y b f g2) (Eq-sym eqB)
                     (Eq-transport (\ X -> PiAppEqVal2 G M N X (REqValPi.codB0 rveq2) b f g2) (Eq-sym eqA)
                       (REqValPi.appEV rveq2))
          fmG-app  = FinMemFun-append g1 g2 b f (REqValPi.fmG rveq1) (REqValPi.fmG rveq2)
          cohG-app = CoherentFun-append g1 g2 cg1 cg2 comp
          ctg-app  = cft-from-cf (append g1 g2) cohG-app
          uniqC = Red3-unique-Pi (RValTyPi.red vtCod) (REqValPi.red rveq1)
          eqCA  = fst uniqC
          eqCB  = snd uniqC
          edgeV' : PiEdgeVal2 G A0 B0 b f
          edgeV' = Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b f) eqCB
                     (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtCod) b f) eqCA
                       (RValTyPi.edgeV vtCod))
          cu    = Coherent-Selection sel ctg-app
          sb1   = selectionBelow g1 u ctg1 cu
          ug1   = fst sb1
          vg1   = fst (snd sb1)
          selg1 = fst (snd (snd sb1))
          le-ug1 = fst (snd (snd (snd sb1)))
          eq-vg1 = snd (snd (snd (snd sb1)))
          sb2   = selectionBelow g2 u ctg2 cu
          ug2   = fst sb2
          vg2   = fst (snd sb2)
          selg2 = fst (snd (snd sb2))
          le-ug2 = fst (snd (snd (snd sb2)))
          eq-vg2 = snd (snd (snd (snd sb2)))
          cug1  = Coherent-Selection selg1 ctg1
          cug2  = Coherent-Selection selg2 ctg2
          fmug1-b = FinMem-Selection b f selg1 (REqValPi.fmG rveq1) ctg1 cb bU
          fmug2-b = FinMem-Selection b f selg2 (REqValPi.fmG rveq2) ctg2 cb bU
          fmu-b   = FinMem-Selection b f sel fmG-app ctg-app cb bU
          valP1 = rstr G P A0 u ug1 b le-ug1 fmug1-b fmu-b valP
          valP2 = rstr G P A0 u ug2 b le-ug2 fmug2-b fmu-b valP
          r1 = REqValPi.appEV rveq1 ug1 vg1 selg1 P htP valP1
          r2 = appEV2' ug2 vg2 selg2 P htP valP2
          selff  = selectionBelow f u ctf cu
          uf     = fst selff
          vf     = fst (snd selff)
          self   = fst (snd (snd selff))
          le-uf  = fst (snd (snd (snd selff)))
          eq-vf  = snd (snd (snd (snd selff)))
          fmuf-b = FinMemAllU-Selection b self allUf ctf cb bU
          valPuf = rstr G P A0 u uf b le-uf fmuf-b fmu-b valP
          vt-vf  = edgeV' uf vf self P htP valPuf
          vtyCod = Eq-transport (\ x -> VTy n G (subst1 B0 P) x) (Eq-sym eq-vf) vt-vf
          c-ef-ug1 = Coherent-EvalFun f ug1 ctf cug1
          c-ef-ug2 = Coherent-EvalFun f ug2 ctf cug2
          c-ef-u   = Coherent-EvalFun f u ctf cu
          ef-u-U   = EvalFun-in-UCode f u b ctf cu allUf
          le-ef1 = EvalFun-mon-arg f ug1 u le-ug1 ctf cug1 cu
          le-ef2 = EvalFun-mon-arg f ug2 u le-ug2 ctf cug2 cu
          fmVg1-ef-ug1 = FinMem-Selection-codomain b f selg1 (REqValPi.fmG rveq1) ctg1 ctf allUf
          fmVg2-ef-ug2 = FinMem-Selection-codomain b f selg2 (REqValPi.fmG rveq2) ctg2 ctf allUf
          fmVg1-ef-u = finMem-upward vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 c-ef-ug1 c-ef-u fmVg1-ef-ug1 ef-u-U
          fmVg2-ef-u = finMem-upward vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 c-ef-ug2 c-ef-u fmVg2-ef-ug2 ef-u-U
          r1' = uEV G (App M P) (App N P) (subst1 B0 P) vg1 (EvalFun f ug1) (EvalFun f u) le-ef1 fmVg1-ef-ug1 fmVg1-ef-u c-ef-ug1 c-ef-u r1 vtyCod
          r2' = uEV G (App M P) (App N P) (subst1 B0 P) vg2 (EvalFun f ug2) (EvalFun f u) le-ef2 fmVg2-ef-ug2 fmVg2-ef-u c-ef-ug2 c-ef-u r2 vtyCod
          comp-vg-ef = comp-EvalFun g1 g2 u comp ctg1 cu
          comp-v = Eq-transport (\ y -> Comp vg1 y) eq-vg2
                     (Eq-transport (\ x -> Comp x (EvalFun g2 u)) eq-vg1 comp-vg-ef)
          fmSup-ef = FinMem-Sup-element vg1 vg2 (EvalFun f u) comp-v c-ef-u fmVg1-ef-u fmVg2-ef-u
          supr = evlsup G (App M P) (App N P) (subst1 B0 P) vg1 vg2 (EvalFun f u) comp-v c-ef-u ef-u-U fmVg1-ef-u fmVg2-ef-u r1' r2'
          eq-app = EvalFun-append-eq g1 g2 u comp ctg1 cu
          lf-refl = LeFunCode-refl (append g1 g2) ctg-app
          le-v-appf = Selection-le-EvalFun (append g1 g2) sel lf-refl ctg-app ctg-app cu
          le-v-supEf = Eq-transport (\ x -> LeCode v x) eq-app le-v-appf
          le-v-supv = Eq-transport (\ y -> LeCode v (Sup vg1 y)) eq-vg2
                        (Eq-transport (\ x -> LeCode v (Sup x (EvalFun g2 u))) eq-vg1 le-v-supEf)
          fmv-ef = FinMem-Selection-codomain b f sel fmG-app ctg-app ctf allUf
      in rstrE G (App M P) (App N P) (subst1 B0 P) (Sup vg1 vg2) v (EvalFun f u) le-v-supv fmv-ef fmSup-ef supr

    ------------------------------------------------------------------------
    -- VLSup / EVLSup : value-level compatible sup at a fixed type-code a.
    -- Dispatch on a (Bot/FunEl/RefEl -> Vl = Top = tt); UCode delegates to
    -- VSup (type-of-M), PiCode to the appended-graph builders, IdCode is
    -- purely syntactic (RValId copy + FinMem-Sup-element on refMem).
    ------------------------------------------------------------------------

    vlSupU : {m : Nat} (G : Ctx m) (M A : Expr m) (u1 u2 : FinEl) ->
      Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
      Vl (suc n) G M A u1 UCode -> Vl (suc n) G M A u2 UCode -> Vl (suc n) G M A (Sup u1 u2) UCode
    vlSupU G M A Bot u2 comp fm1 fm2 vt1 vt2 = vt2
    vlSupU G M A UCode Bot comp fm1 fm2 vt1 vt2 = vt1
    vlSupU G M A (FunEl g1) Bot comp fm1 fm2 vt1 vt2 = vt1
    vlSupU G M A (PiCode a1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
    vlSupU G M A (IdCode t1 u1 v1) Bot comp fm1 fm2 vt1 vt2 = vt1
    vlSupU G M A (RefEl w1) Bot comp fm1 fm2 vt1 vt2 = vt1
    vlSupU G M A UCode UCode comp fm1 fm2 vt1 vt2 =
      mkSigma (fst vt1) (VSup G M UCode UCode comp fm1 fm2 (snd vt1) (snd vt2))
    vlSupU G M A UCode (FunEl g2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A UCode (PiCode c h) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A UCode (IdCode t2 u2 v2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A UCode (RefEl w2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (FunEl g1) UCode comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (FunEl g1) (FunEl g2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (FunEl g1) (PiCode c h) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (FunEl g1) (IdCode t2 u2 v2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (FunEl g1) (RefEl w2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (PiCode a1 f1) UCode comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (PiCode a1 f1) (FunEl g2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (PiCode a1 f1) (PiCode c h) comp fm1 fm2 vt1 vt2 =
      mkSigma (fst vt1) (VSup G M (PiCode a1 f1) (PiCode c h) comp fm1 fm2 (snd vt1) (snd vt2))
    vlSupU G M A (PiCode a1 f1) (IdCode t2 u2 v2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (PiCode a1 f1) (RefEl w2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (IdCode t1 u1 v1) UCode comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (IdCode t1 u1 v1) (FunEl g2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (IdCode t1 u1 v1) (PiCode c h) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 vt1 vt2 =
      mkSigma (fst vt1) (VSup G M (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 (snd vt1) (snd vt2))
    vlSupU G M A (IdCode t1 u1 v1) (RefEl w2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (RefEl w1) UCode comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (RefEl w1) (FunEl g2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (RefEl w1) (PiCode c h) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (RefEl w1) (IdCode t2 u2 v2) comp fm1 fm2 vt1 vt2 = tt
    vlSupU G M A (RefEl w1) (RefEl w2) comp fm1 fm2 vt1 vt2 = tt

    vlSupId : {m : Nat} (G : Ctx m) (M A : Expr m) (u1 u2 : FinEl) (t u v : FinEl) ->
      Comp u1 u2 -> Coherent (IdCode t u v) -> FinMem (IdCode t u v) UCode ->
      FinMem u1 (IdCode t u v) -> FinMem u2 (IdCode t u v) ->
      Vl (suc n) G M A u1 (IdCode t u v) -> Vl (suc n) G M A u2 (IdCode t u v) ->
      Vl (suc n) G M A (Sup u1 u2) (IdCode t u v)
    vlSupId G M A Bot u2 t u v comp ca fma fm1 fm2 vt1 vt2 = vt2
    vlSupId G M A UCode Bot t u v comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupId G M A (FunEl g1) Bot t u v comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupId G M A (PiCode a1 f1) Bot t u v comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupId G M A (IdCode t1 u1 v1) Bot t u v comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupId G M A (RefEl w1) Bot t u v comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupId G M A (RefEl w1) (RefEl w2) t u v comp ca fma fm1 fm2 vt1 vt2 =
      let rid1 = snd vt1 ; rid2 = snd vt2
          witEq = Ref-wit-unique (Red3.hr (RValId.redTm rid2)) (Red3.hr (RValId.redTm rid1))
          alR = Red3-unique-Id (RValId.red rid2) (RValId.red rid1)
          t_U = finMem-idU-dom t u v fma
          coh_t = coh-from-aU t t_U
          fm-w1-t = finMem-ref-wit w1 t u v (RValId.refMem rid1)
          fm-w2-t = finMem-ref-wit w2 t u v (RValId.refMem rid2)
          eL2-al = Eq-transport (\ X -> EVl n G X (RValId.lhs0 rid1) (RValId.domA0 rid1) w2 t) witEq
                     (Eq-transport (\ X -> EVl n G (RValId.wit0 rid2) X (RValId.domA0 rid1) w2 t) (fst (snd alR))
                       (Eq-transport (\ X -> EVl n G (RValId.wit0 rid2) (RValId.lhs0 rid2) X w2 t) (fst alR) (RValId.endEqL rid2)))
          eR2-al = Eq-transport (\ X -> EVl n G X (RValId.rhs0 rid1) (RValId.domA0 rid1) w2 t) witEq
                     (Eq-transport (\ X -> EVl n G (RValId.wit0 rid2) X (RValId.domA0 rid1) w2 t) (snd (snd alR))
                       (Eq-transport (\ X -> EVl n G (RValId.wit0 rid2) (RValId.rhs0 rid2) X w2 t) (fst alR) (RValId.endEqR rid2)))
          endEqL-sup = evlsup G (RValId.wit0 rid1) (RValId.lhs0 rid1) (RValId.domA0 rid1) w1 w2 t comp coh_t t_U fm-w1-t fm-w2-t (RValId.endEqL rid1) eL2-al
          endEqR-sup = evlsup G (RValId.wit0 rid1) (RValId.rhs0 rid1) (RValId.domA0 rid1) w1 w2 t comp coh_t t_U fm-w1-t fm-w2-t (RValId.endEqR rid1) eR2-al
      in mkSigma (fst vt1)
        (record { domA0 = RValId.domA0 rid1 ; lhs0 = RValId.lhs0 rid1 ; rhs0 = RValId.rhs0 rid1
                ; red = RValId.red rid1 ; wit0 = RValId.wit0 rid1 ; redTm = RValId.redTm rid1
                ; refConvL = RValId.refConvL rid1 ; refConvR = RValId.refConvR rid1
                ; refMem = FinMem-Sup-element (RefEl w1) (RefEl w2) (IdCode t u v) comp ca
                             (RValId.refMem rid1) (RValId.refMem rid2)
                ; endEqL = endEqL-sup ; endEqR = endEqR-sup })
    vlSupId G M A UCode UCode t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A UCode (FunEl g2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A UCode (PiCode c h) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A UCode (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A UCode (RefEl w2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (FunEl g1) UCode t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (FunEl g1) (FunEl g2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (FunEl g1) (PiCode c h) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (FunEl g1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (FunEl g1) (RefEl w2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (PiCode a1 f1) UCode t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (PiCode a1 f1) (FunEl g2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (PiCode a1 f1) (PiCode c h) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (PiCode a1 f1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (PiCode a1 f1) (RefEl w2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (IdCode t1 u1 v1) UCode t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (IdCode t1 u1 v1) (FunEl g2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (IdCode t1 u1 v1) (PiCode c h) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (IdCode t1 u1 v1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (IdCode t1 u1 v1) (RefEl w2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (RefEl w1) UCode t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (RefEl w1) (FunEl g2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (RefEl w1) (PiCode c h) t u v comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupId G M A (RefEl w1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 vt1 vt2 = tt

    vlSupPi : {m : Nat} (G : Ctx m) (M A : Expr m) (u1 u2 : FinEl) (b : FinEl) (f : FinFun) ->
      Comp u1 u2 -> Coherent (PiCode b f) -> FinMem (PiCode b f) UCode ->
      FinMem u1 (PiCode b f) -> FinMem u2 (PiCode b f) ->
      Vl (suc n) G M A u1 (PiCode b f) -> Vl (suc n) G M A u2 (PiCode b f) ->
      Vl (suc n) G M A (Sup u1 u2) (PiCode b f)
    vlSupPi G M A Bot u2 b f comp ca fma fm1 fm2 vt1 vt2 = vt2
    vlSupPi G M A UCode Bot b f comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupPi G M A (FunEl g1) Bot b f comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupPi G M A (PiCode a1 f1) Bot b f comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupPi G M A (IdCode t1 u1 v1) Bot b f comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupPi G M A (RefEl w1) Bot b f comp ca fma fm1 fm2 vt1 vt2 = vt1
    vlSupPi G M A (FunEl g1) (FunEl g2) b f comp ca fma fm1 fm2 vt1 vt2 =
      mkSigma (fst vt1)
        (record { domA0 = RValPi.domA0 (snd vt1) ; codB0 = RValPi.codB0 (snd vt1)
                ; red = RValPi.red (snd vt1)
                ; cohG = CoherentFun-append g1 g2 (RValPi.cohG (snd vt1)) (RValPi.cohG (snd vt2)) comp
                ; fmG = FinMemFun-append g1 g2 b f (RValPi.fmG (snd vt1)) (RValPi.fmG (snd vt2))
                ; appV = appVSup G M A g1 g2 b f comp ca fma (fst vt1) (snd vt1) (snd vt2)
                ; appE = appESup G M A g1 g2 b f comp ca fma (fst vt1) (snd vt1) (snd vt2) })
    vlSupPi G M A UCode UCode b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A UCode (FunEl g2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A UCode (PiCode c h) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A UCode (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A UCode (RefEl w2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (FunEl g1) UCode b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (FunEl g1) (PiCode c h) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (FunEl g1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (FunEl g1) (RefEl w2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (PiCode a1 f1) UCode b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (PiCode a1 f1) (FunEl g2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (PiCode a1 f1) (PiCode c h) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (PiCode a1 f1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (PiCode a1 f1) (RefEl w2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (IdCode t1 u1 v1) UCode b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (IdCode t1 u1 v1) (FunEl g2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (IdCode t1 u1 v1) (PiCode c h) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (IdCode t1 u1 v1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (IdCode t1 u1 v1) (RefEl w2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (RefEl w1) UCode b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (RefEl w1) (FunEl g2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (RefEl w1) (PiCode c h) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (RefEl w1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 vt1 vt2 = tt
    vlSupPi G M A (RefEl w1) (RefEl w2) b f comp ca fma fm1 fm2 vt1 vt2 = tt

    VLSup : {m : Nat} (G : Ctx m) (M A : Expr m) (u1 u2 a : FinEl) ->
      Comp u1 u2 -> Coherent a -> FinMem a UCode -> FinMem u1 a -> FinMem u2 a ->
      Vl (suc n) G M A u1 a -> Vl (suc n) G M A u2 a -> Vl (suc n) G M A (Sup u1 u2) a
    VLSup G M A u1 u2 Bot comp ca fma fm1 fm2 vt1 vt2 = tt
    VLSup G M A u1 u2 UCode comp ca fma fm1 fm2 vt1 vt2 =
      vlSupU G M A u1 u2 comp fm1 fm2 vt1 vt2
    VLSup G M A u1 u2 (FunEl h) comp ca fma fm1 fm2 vt1 vt2 = tt
    VLSup G M A u1 u2 (PiCode b f) comp ca fma fm1 fm2 vt1 vt2 =
      vlSupPi G M A u1 u2 b f comp ca fma fm1 fm2 vt1 vt2
    VLSup G M A u1 u2 (IdCode t u v) comp ca fma fm1 fm2 vt1 vt2 =
      vlSupId G M A u1 u2 t u v comp ca fma fm1 fm2 vt1 vt2
    VLSup G M A u1 u2 (RefEl w) comp ca fma fm1 fm2 vt1 vt2 = tt

    ------------------------------------------------------------------------
    -- EVLSup : the equality mirror.
    ------------------------------------------------------------------------

    evlSupU : {m : Nat} (G : Ctx m) (M N A : Expr m) (u1 u2 : FinEl) ->
      Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
      EVl (suc n) G M N A u1 UCode -> EVl (suc n) G M N A u2 UCode -> EVl (suc n) G M N A (Sup u1 u2) UCode
    evlSupU G M N A Bot u2 comp fm1 fm2 eq1 eq2 = eq2
    evlSupU G M N A UCode Bot comp fm1 fm2 eq1 eq2 = eq1
    evlSupU G M N A (FunEl g1) Bot comp fm1 fm2 eq1 eq2 = eq1
    evlSupU G M N A (PiCode a1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
    evlSupU G M N A (IdCode t1 u1 v1) Bot comp fm1 fm2 eq1 eq2 = eq1
    evlSupU G M N A (RefEl w1) Bot comp fm1 fm2 eq1 eq2 = eq1
    evlSupU G M N A UCode UCode comp fm1 fm2 eq1 eq2 =
      mkSigma (fst eq1)
        (mkSigma (VSup G M UCode UCode comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2)))
          (mkSigma (VSup G N UCode UCode comp fm1 fm2 (fst (snd (snd eq1))) (fst (snd (snd eq2))))
            (EVSup G M N UCode UCode comp fm1 fm2 (snd (snd (snd eq1))) (snd (snd (snd eq2))))))
    evlSupU G M N A UCode (FunEl g2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A UCode (PiCode c h) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A UCode (IdCode t2 u2 v2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A UCode (RefEl w2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (FunEl g1) UCode comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (FunEl g1) (FunEl g2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (FunEl g1) (PiCode c h) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (FunEl g1) (IdCode t2 u2 v2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (FunEl g1) (RefEl w2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (PiCode a1 f1) UCode comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (PiCode a1 f1) (FunEl g2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (PiCode a1 f1) (PiCode c h) comp fm1 fm2 eq1 eq2 =
      mkSigma (fst eq1)
        (mkSigma (VSup G M (PiCode a1 f1) (PiCode c h) comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2)))
          (mkSigma (VSup G N (PiCode a1 f1) (PiCode c h) comp fm1 fm2 (fst (snd (snd eq1))) (fst (snd (snd eq2))))
            (EVSup G M N (PiCode a1 f1) (PiCode c h) comp fm1 fm2 (snd (snd (snd eq1))) (snd (snd (snd eq2))))))
    evlSupU G M N A (PiCode a1 f1) (IdCode t2 u2 v2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (PiCode a1 f1) (RefEl w2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (IdCode t1 u1 v1) UCode comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (IdCode t1 u1 v1) (FunEl g2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (IdCode t1 u1 v1) (PiCode c h) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 eq1 eq2 =
      mkSigma (fst eq1)
        (mkSigma (VSup G M (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2)))
          (mkSigma (VSup G N (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 (fst (snd (snd eq1))) (fst (snd (snd eq2))))
            (EVSup G M N (IdCode t1 u1 v1) (IdCode t2 u2 v2) comp fm1 fm2 (snd (snd (snd eq1))) (snd (snd (snd eq2))))))
    evlSupU G M N A (IdCode t1 u1 v1) (RefEl w2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (RefEl w1) UCode comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (RefEl w1) (FunEl g2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (RefEl w1) (PiCode c h) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (RefEl w1) (IdCode t2 u2 v2) comp fm1 fm2 eq1 eq2 = tt
    evlSupU G M N A (RefEl w1) (RefEl w2) comp fm1 fm2 eq1 eq2 = tt

    evlSupId : {m : Nat} (G : Ctx m) (M N A : Expr m) (u1 u2 : FinEl) (t u v : FinEl) ->
      Comp u1 u2 -> Coherent (IdCode t u v) -> FinMem (IdCode t u v) UCode ->
      FinMem u1 (IdCode t u v) -> FinMem u2 (IdCode t u v) ->
      EVl (suc n) G M N A u1 (IdCode t u v) -> EVl (suc n) G M N A u2 (IdCode t u v) ->
      EVl (suc n) G M N A (Sup u1 u2) (IdCode t u v)
    evlSupId G M N A Bot u2 t u v comp ca fma fm1 fm2 eq1 eq2 = eq2
    evlSupId G M N A UCode Bot t u v comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupId G M N A (FunEl g1) Bot t u v comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupId G M N A (PiCode a1 f1) Bot t u v comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupId G M N A (IdCode t1 u1 v1) Bot t u v comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupId G M N A (RefEl w1) Bot t u v comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupId G M N A (RefEl w1) (RefEl w2) t u v comp ca fma fm1 fm2 eq1 eq2 =
      let rid1M = fst (snd eq1) ; rid2M = fst (snd eq2)
          rid1N = fst (snd (snd eq1)) ; rid2N = fst (snd (snd eq2))
          reid1 = snd (snd (snd eq1)) ; reid2 = snd (snd (snd eq2))
          t_U = finMem-idU-dom t u v fma
          coh_t = coh-from-aU t t_U
          fw1 = \ rm -> finMem-ref-wit w1 t u v rm
          fw2 = \ rm -> finMem-ref-wit w2 t u v rm
          -- M-value record
          alM = Red3-unique-Id (RValId.red rid2M) (RValId.red rid1M)
          weM = Ref-wit-unique (Red3.hr (RValId.redTm rid2M)) (Red3.hr (RValId.redTm rid1M))
          eLM = joinE w1 w2 t comp coh_t t_U (fw1 (RValId.refMem rid1M)) (fw2 (RValId.refMem rid2M)) weM (fst (snd alM)) (fst alM) (RValId.endEqL rid1M) (RValId.endEqL rid2M)
          eRM = joinE w1 w2 t comp coh_t t_U (fw1 (RValId.refMem rid1M)) (fw2 (RValId.refMem rid2M)) weM (snd (snd alM)) (fst alM) (RValId.endEqR rid1M) (RValId.endEqR rid2M)
          -- N-value record
          alN = Red3-unique-Id (RValId.red rid2N) (RValId.red rid1N)
          weN = Ref-wit-unique (Red3.hr (RValId.redTm rid2N)) (Red3.hr (RValId.redTm rid1N))
          eLN = joinE w1 w2 t comp coh_t t_U (fw1 (RValId.refMem rid1N)) (fw2 (RValId.refMem rid2N)) weN (fst (snd alN)) (fst alN) (RValId.endEqL rid1N) (RValId.endEqL rid2N)
          eRN = joinE w1 w2 t comp coh_t t_U (fw1 (RValId.refMem rid1N)) (fw2 (RValId.refMem rid2N)) weN (snd (snd alN)) (fst alN) (RValId.endEqR rid1N) (RValId.endEqR rid2N)
          -- equality record
          alE = Red3-unique-Id (REqValId.red reid2) (REqValId.red reid1)
          weEM = Ref-wit-unique (Red3.hr (REqValId.redTmM reid2)) (Red3.hr (REqValId.redTmM reid1))
          weEN = Ref-wit-unique (Red3.hr (REqValId.redTmN reid2)) (Red3.hr (REqValId.redTmN reid1))
          fw1E = fw1 (REqValId.refMem reid1) ; fw2E = fw2 (REqValId.refMem reid2)
          eLME = joinE w1 w2 t comp coh_t t_U fw1E fw2E weEM (fst (snd alE)) (fst alE) (REqValId.endEqLM reid1) (REqValId.endEqLM reid2)
          eRME = joinE w1 w2 t comp coh_t t_U fw1E fw2E weEM (snd (snd alE)) (fst alE) (REqValId.endEqRM reid1) (REqValId.endEqRM reid2)
          eLNE = joinE w1 w2 t comp coh_t t_U fw1E fw2E weEN (fst (snd alE)) (fst alE) (REqValId.endEqLN reid1) (REqValId.endEqLN reid2)
          eRNE = joinE w1 w2 t comp coh_t t_U fw1E fw2E weEN (snd (snd alE)) (fst alE) (REqValId.endEqRN reid1) (REqValId.endEqRN reid2)
      in mkSigma (fst eq1)
        (mkSigma
           (record { domA0 = RValId.domA0 rid1M ; lhs0 = RValId.lhs0 rid1M ; rhs0 = RValId.rhs0 rid1M
                   ; red = RValId.red rid1M ; wit0 = RValId.wit0 rid1M ; redTm = RValId.redTm rid1M
                   ; refConvL = RValId.refConvL rid1M ; refConvR = RValId.refConvR rid1M
                   ; refMem = FinMem-Sup-element (RefEl w1) (RefEl w2) (IdCode t u v) comp ca
                                (RValId.refMem rid1M) (RValId.refMem rid2M)
                   ; endEqL = eLM ; endEqR = eRM })
           (mkSigma
              (record { domA0 = RValId.domA0 rid1N ; lhs0 = RValId.lhs0 rid1N ; rhs0 = RValId.rhs0 rid1N
                      ; red = RValId.red rid1N ; wit0 = RValId.wit0 rid1N ; redTm = RValId.redTm rid1N
                      ; refConvL = RValId.refConvL rid1N ; refConvR = RValId.refConvR rid1N
                      ; refMem = FinMem-Sup-element (RefEl w1) (RefEl w2) (IdCode t u v) comp ca
                                   (RValId.refMem rid1N) (RValId.refMem rid2N)
                      ; endEqL = eLN ; endEqR = eRN })
              (record { domA0 = REqValId.domA0 reid1 ; lhs0 = REqValId.lhs0 reid1 ; rhs0 = REqValId.rhs0 reid1
                      ; red = REqValId.red reid1
                      ; wit0M = REqValId.wit0M reid1 ; wit0N = REqValId.wit0N reid1
                      ; redTmM = REqValId.redTmM reid1 ; redTmN = REqValId.redTmN reid1
                      ; refMem = FinMem-Sup-element (RefEl w1) (RefEl w2) (IdCode t u v) comp ca
                                   (REqValId.refMem reid1) (REqValId.refMem reid2)
                      ; endEqLM = eLME ; endEqRM = eRME ; endEqLN = eLNE ; endEqRN = eRNE })))
    evlSupId G M N A UCode UCode t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A UCode (FunEl g2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A UCode (PiCode c h) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A UCode (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A UCode (RefEl w2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (FunEl g1) UCode t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (FunEl g1) (FunEl g2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (FunEl g1) (PiCode c h) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (FunEl g1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (FunEl g1) (RefEl w2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (PiCode a1 f1) UCode t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (PiCode a1 f1) (FunEl g2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (PiCode a1 f1) (PiCode c h) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (PiCode a1 f1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (PiCode a1 f1) (RefEl w2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (IdCode t1 u1 v1) UCode t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (IdCode t1 u1 v1) (FunEl g2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (IdCode t1 u1 v1) (PiCode c h) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (IdCode t1 u1 v1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (IdCode t1 u1 v1) (RefEl w2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (RefEl w1) UCode t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (RefEl w1) (FunEl g2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (RefEl w1) (PiCode c h) t u v comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupId G M N A (RefEl w1) (IdCode t2 u2 v2) t u v comp ca fma fm1 fm2 eq1 eq2 = tt

    evlSupPi : {m : Nat} (G : Ctx m) (M N A : Expr m) (u1 u2 : FinEl) (b : FinEl) (f : FinFun) ->
      Comp u1 u2 -> Coherent (PiCode b f) -> FinMem (PiCode b f) UCode ->
      FinMem u1 (PiCode b f) -> FinMem u2 (PiCode b f) ->
      EVl (suc n) G M N A u1 (PiCode b f) -> EVl (suc n) G M N A u2 (PiCode b f) ->
      EVl (suc n) G M N A (Sup u1 u2) (PiCode b f)
    evlSupPi G M N A Bot u2 b f comp ca fma fm1 fm2 eq1 eq2 = eq2
    evlSupPi G M N A UCode Bot b f comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupPi G M N A (FunEl g1) Bot b f comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupPi G M N A (PiCode a1 f1) Bot b f comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupPi G M N A (IdCode t1 u1 v1) Bot b f comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupPi G M N A (RefEl w1) Bot b f comp ca fma fm1 fm2 eq1 eq2 = eq1
    evlSupPi G M N A (FunEl g1) (FunEl g2) b f comp ca fma fm1 fm2 eq1 eq2 =
      let vtCod = fst eq1
          rvM1 = fst (snd eq1) ; rvM2 = fst (snd eq2)
          rvN1 = fst (snd (snd eq1)) ; rvN2 = fst (snd (snd eq2))
          rveq1 = snd (snd (snd eq1)) ; rveq2 = snd (snd (snd eq2))
      in mkSigma vtCod
           (mkSigma
              (record { domA0 = RValPi.domA0 rvM1 ; codB0 = RValPi.codB0 rvM1 ; red = RValPi.red rvM1
                      ; cohG = CoherentFun-append g1 g2 (RValPi.cohG rvM1) (RValPi.cohG rvM2) comp
                      ; fmG = FinMemFun-append g1 g2 b f (RValPi.fmG rvM1) (RValPi.fmG rvM2)
                      ; appV = appVSup G M A g1 g2 b f comp ca fma vtCod rvM1 rvM2
                      ; appE = appESup G M A g1 g2 b f comp ca fma vtCod rvM1 rvM2 })
              (mkSigma
                 (record { domA0 = RValPi.domA0 rvN1 ; codB0 = RValPi.codB0 rvN1 ; red = RValPi.red rvN1
                         ; cohG = CoherentFun-append g1 g2 (RValPi.cohG rvN1) (RValPi.cohG rvN2) comp
                         ; fmG = FinMemFun-append g1 g2 b f (RValPi.fmG rvN1) (RValPi.fmG rvN2)
                         ; appV = appVSup G N A g1 g2 b f comp ca fma vtCod rvN1 rvN2
                         ; appE = appESup G N A g1 g2 b f comp ca fma vtCod rvN1 rvN2 })
                 (record { domA0 = REqValPi.domA0 rveq1 ; codB0 = REqValPi.codB0 rveq1 ; red = REqValPi.red rveq1
                         ; cohG = CoherentFun-append g1 g2 (REqValPi.cohG rveq1) (REqValPi.cohG rveq2) comp
                         ; fmG = FinMemFun-append g1 g2 b f (REqValPi.fmG rveq1) (REqValPi.fmG rveq2)
                         ; appEV = appEVSup G M N A g1 g2 b f comp ca fma vtCod rveq1 rveq2 })))
    evlSupPi G M N A UCode UCode b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A UCode (FunEl g2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A UCode (PiCode c h) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A UCode (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A UCode (RefEl w2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (FunEl g1) UCode b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (FunEl g1) (PiCode c h) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (FunEl g1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (FunEl g1) (RefEl w2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (PiCode a1 f1) UCode b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (PiCode a1 f1) (FunEl g2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (PiCode a1 f1) (PiCode c h) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (PiCode a1 f1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (PiCode a1 f1) (RefEl w2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (IdCode t1 u1 v1) UCode b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (IdCode t1 u1 v1) (FunEl g2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (IdCode t1 u1 v1) (PiCode c h) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (IdCode t1 u1 v1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (IdCode t1 u1 v1) (RefEl w2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (RefEl w1) UCode b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (RefEl w1) (FunEl g2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (RefEl w1) (PiCode c h) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (RefEl w1) (IdCode t2 u2 v2) b f comp ca fma fm1 fm2 eq1 eq2 = tt
    evlSupPi G M N A (RefEl w1) (RefEl w2) b f comp ca fma fm1 fm2 eq1 eq2 = tt

    EVLSup : {m : Nat} (G : Ctx m) (M N A : Expr m) (u1 u2 a : FinEl) ->
      Comp u1 u2 -> Coherent a -> FinMem a UCode -> FinMem u1 a -> FinMem u2 a ->
      EVl (suc n) G M N A u1 a -> EVl (suc n) G M N A u2 a -> EVl (suc n) G M N A (Sup u1 u2) a
    EVLSup G M N A u1 u2 Bot comp ca fma fm1 fm2 eq1 eq2 = tt
    EVLSup G M N A u1 u2 UCode comp ca fma fm1 fm2 eq1 eq2 =
      evlSupU G M N A u1 u2 comp fm1 fm2 eq1 eq2
    EVLSup G M N A u1 u2 (FunEl h) comp ca fma fm1 fm2 eq1 eq2 = tt
    EVLSup G M N A u1 u2 (PiCode b f) comp ca fma fm1 fm2 eq1 eq2 =
      evlSupPi G M N A u1 u2 b f comp ca fma fm1 fm2 eq1 eq2
    EVLSup G M N A u1 u2 (IdCode t u v) comp ca fma fm1 fm2 eq1 eq2 =
      evlSupId G M N A u1 u2 t u v comp ca fma fm1 fm2 eq1 eq2
    EVLSup G M N A u1 u2 (RefEl w) comp ca fma fm1 fm2 eq1 eq2 = tt

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
    v2e  = ReflPack.Val2-to-EqVal2 ih

    V2B : {m : Nat} {G : Ctx m} {M A : Expr m} (a : FinEl) -> Vl (suc n) G M A Bot a
    V2B Bot          = tt
    V2B UCode        = tt
    V2B (FunEl h)    = tt
    V2B (PiCode b f) = tt
    V2B (IdCode t u v) = tt
    V2B (RefEl w)    = tt

    EV2B : {m : Nat} {G : Ctx m} {M N A : Expr m} (a : FinEl) -> EVl (suc n) G M N A Bot a
    EV2B Bot          = tt
    EV2B UCode        = tt
    EV2B (FunEl h)    = tt
    EV2B (PiCode b f) = tt
    EV2B (IdCode t u v) = tt
    EV2B (RefEl w)    = tt

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
    VT2E (IdCode t u v) vtyM =
      let A0 = RValTyId.domA vtyM ; l0 = RValTyId.lhs vtyM ; r0 = RValTyId.rhs vtyM
      in mkSigma vtyM (mkSigma vtyM (record
           { domA = A0 ; lhs = l0 ; rhs = r0
           ; domA' = A0 ; lhs' = l0 ; rhs' = r0
           ; redM = RValTyId.red vtyM ; redN = RValTyId.red vtyM
           ; convA = conv-refl (RValTyId.htA vtyM)
           ; convL = conv-refl (RValTyId.htL vtyM)
           ; convR = conv-refl (RValTyId.htR vtyM)
           ; eqA = vt2e t (RValTyId.valA vtyM)
           ; eqL = v2e u t (RValTyId.valLlog vtyM)
           ; eqR = v2e v t (RValTyId.valRlog vtyM)
           }))
    VT2E (RefEl w) vtyM = tt

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
    V2E (IdCode t1 t2 t3) UCode v =
      mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (VT2E (IdCode t1 t2 t3) (snd v))))
    V2E (RefEl w) UCode v = tt
    V2E (IdCode t1 t2 t3) (FunEl h) v = tt
    V2E (RefEl w) (FunEl h) v = tt
    V2E (IdCode t1 t2 t3) (PiCode b f) v = tt
    V2E (RefEl w) (PiCode b f) v = tt
    V2E (RefEl w) (IdCode t' u' v') v =
      let rid = snd v
      in mkSigma (fst v) (mkSigma rid (mkSigma
           (record { domA0 = RValId.domA0 rid ; lhs0 = RValId.lhs0 rid ; rhs0 = RValId.rhs0 rid ; red = RValId.red rid ; wit0 = RValId.wit0 rid ; redTm = RValId.redTm rid ; refConvL = RValId.refConvL rid ; refConvR = RValId.refConvR rid ; refMem = RValId.refMem rid ; endEqL = RValId.endEqL rid ; endEqR = RValId.endEqR rid })
           (record { domA0 = RValId.domA0 rid ; lhs0 = RValId.lhs0 rid ; rhs0 = RValId.rhs0 rid ; red = RValId.red rid ; wit0M = RValId.wit0 rid ; wit0N = RValId.wit0 rid ; redTmM = RValId.redTm rid ; redTmN = RValId.redTm rid ; refMem = RValId.refMem rid ; endEqLM = RValId.endEqL rid ; endEqRM = RValId.endEqR rid ; endEqLN = RValId.endEqL rid ; endEqRN = RValId.endEqR rid })))
    V2E Bot (IdCode a a1 a2) v = tt
    V2E UCode (IdCode a a1 a2) v = tt
    V2E (FunEl g) (IdCode a a1 a2) v = tt
    V2E (PiCode b f) (IdCode a a1 a2) v = tt
    V2E (IdCode s0 s1 s2) (IdCode a a1 a2) v = tt
    V2E u (RefEl a) v = tt

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
    efwdT = FwdPack.EqVal2-EqValTy2-fwd (goodStageFwd n)
    evtT  = FwdPack.EqVal2-trans (goodStageFwd n)
    rstrET = MonoPack.restrictEqVal2 (goodStage n)

    idTyConvC : {m : Nat} {G : Ctx m} {C C' : Expr m} {t u v : FinEl} ->
      RValTyId G C t u v -> REqValTyId G C C' t u v -> Pair (ConvTm G C C' U) (HasType G C' U)
    idTyConvC vtC core =
      let uC  = Red3-unique-Id (RValTyId.red vtC) (REqValTyId.redM core)
          lC  = RValTyId.lhs vtC ; rC = RValTyId.rhs vtC
          hA  = Eq-transport (\ X -> HasType _ X U) (fst uC) (RValTyId.htA vtC)
          hL  = Eq-transport (\ X -> HasType _ X _) (fst (snd uC))
                  (Eq-transport (\ Y -> HasType _ lC Y) (fst uC) (RValTyId.htL vtC))
          hR  = Eq-transport (\ X -> HasType _ X _) (snd (snd uC))
                  (Eq-transport (\ Y -> HasType _ rC Y) (fst uC) (RValTyId.htR vtC))
          cId = conv-Id hA hL hR (REqValTyId.convA core) (REqValTyId.convL core) (REqValTyId.convR core)
          cCC' = conv-trans (Red3.ct (REqValTyId.redM core))
                   (conv-trans cId (conv-sym (Red3.ct (REqValTyId.redN core))))
      in mkSigma cCC' (fst (typing-ConvTm (Red3.ct (REqValTyId.redN core))))

    refConvsFwd : {m : Nat} {G : Ctx m} {M C C' : Expr m} {w t u v : FinEl} ->
      (rid : RValId G M C w t u v) (core : REqValTyId G C C' t u v) ->
      Pair (ConvTm G (RValId.wit0 rid) (REqValTyId.lhs' core) (REqValTyId.domA' core))
           (ConvTm G (RValId.wit0 rid) (REqValTyId.rhs' core) (REqValTyId.domA' core))
    refConvsFwd rid core =
      let al   = Red3-unique-Id (RValId.red rid) (REqValTyId.redM core)
          w0   = RValId.wit0 rid ; d0 = RValId.domA0 rid
          rcL0 = Eq-transport (\ X -> ConvTm _ w0 X d0) (fst (snd al)) (RValId.refConvL rid)
          rcL  = Eq-transport (\ X -> ConvTm _ w0 (REqValTyId.lhs core) X) (fst al) rcL0
          rcR0 = Eq-transport (\ X -> ConvTm _ w0 X d0) (snd (snd al)) (RValId.refConvR rid)
          rcR  = Eq-transport (\ X -> ConvTm _ w0 (REqValTyId.rhs core) X) (fst al) rcR0
          cA   = REqValTyId.convA core ; htDomA' = snd (typing-ConvTm cA)
          rcL' = conv-conv (conv-trans rcL (REqValTyId.convL core)) cA htDomA'
          rcR' = conv-conv (conv-trans rcR (REqValTyId.convR core)) cA htDomA'
      in mkSigma rcL' rcR'

    endEqFwdRaw : {m : Nat} {G : Ctx m} {A C' : Expr m} {wit0 domA0 lhs0 rhs0 : Expr m} {w t u v : FinEl} ->
      Red3 G A (Id domA0 lhs0 rhs0) U -> FinMem (RefEl w) (IdCode t u v) ->
      EVl n G wit0 lhs0 domA0 w t -> EVl n G wit0 rhs0 domA0 w t ->
      (core : REqValTyId G A C' t u v) ->
      Pair (EVl n G wit0 (REqValTyId.lhs' core) (REqValTyId.domA' core) w t)
           (EVl n G wit0 (REqValTyId.rhs' core) (REqValTyId.domA' core) w t)
    endEqFwdRaw {G = G} {wit0 = w0} {domA0 = d0} {w = w} {t = t} {u = u} {v = v} red refMem eL eR core =
      let al = Red3-unique-Id red (REqValTyId.redM core)
          eL0 = Eq-transport (\ X -> EVl n G w0 X d0 w t) (fst (snd al)) eL
          eL1 = Eq-transport (\ X -> EVl n G w0 (REqValTyId.lhs core) X w t) (fst al) eL0
          eR0 = Eq-transport (\ X -> EVl n G w0 X d0 w t) (snd (snd al)) eR
          eR1 = Eq-transport (\ X -> EVl n G w0 (REqValTyId.rhs core) X w t) (fst al) eR0
          le_wu = finMem-ref-le1 w t u v refMem
          le_wv = finMem-ref-le2 w t u v refMem
          fm_w_t = finMem-ref-wit w t u v refMem
          fmemIdU = FinMem-a-in-U (RefEl w) (IdCode t u v) refMem
          t_U = finMem-idU-dom t u v fmemIdU
          fm_u_t = finMem-idU-lhs t u v fmemIdU
          fm_v_t = finMem-idU-rhs t u v fmemIdU
          coh_w = FinMem-coh-u w t fm_w_t
          coh_t = coh-from-aU t t_U
          eqL_w = rstrET G (REqValTyId.lhs core) (REqValTyId.lhs' core) (REqValTyId.domA core) u w t le_wu fm_w_t fm_u_t (REqValTyId.eqL core)
          eqR_w = rstrET G (REqValTyId.rhs core) (REqValTyId.rhs' core) (REqValTyId.domA core) v w t le_wv fm_w_t fm_v_t (REqValTyId.eqR core)
          composedL = evtT w t coh_w coh_t eL1 eqL_w
          composedR = evtT w t coh_w coh_t eR1 eqR_w
          eL' = efwdT w t coh_t (REqValTyId.eqA core) composedL
          eR' = efwdT w t coh_t (REqValTyId.eqA core) composedR
      in mkSigma eL' eR'

    endEqFwd : {m : Nat} {G : Ctx m} {M C C' : Expr m} {w t u v : FinEl} ->
      (rid : RValId G M C w t u v) (core : REqValTyId G C C' t u v) ->
      Pair (EVl n G (RValId.wit0 rid) (REqValTyId.lhs' core) (REqValTyId.domA' core) w t)
           (EVl n G (RValId.wit0 rid) (REqValTyId.rhs' core) (REqValTyId.domA' core) w t)
    endEqFwd rid core =
      endEqFwdRaw (RValId.red rid) (RValId.refMem rid) (RValId.endEqL rid) (RValId.endEqR rid) core

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
    VTT (IdCode t1 t2 t3) UCode eqvt val = mkSigma (snd eqvt) (snd val)
    VTT (RefEl w) UCode eqvt val = tt
    VTT (IdCode t1 t2 t3) (PiCode b f) eqvt val = tt
    VTT (RefEl w) (PiCode b f) eqvt val = tt
    VTT (RefEl w) (IdCode t' u' v') eqvt val =
      let core = snd (snd eqvt)
          cc   = idTyConvC (fst eqvt) core ; cCC' = fst cc ; htC' = snd cc
          rid  = snd val ; rcs = refConvsFwd rid core ; ees = endEqFwd rid core
      in mkSigma (fst (snd eqvt))
           (record { domA0 = REqValTyId.domA' core ; lhs0 = REqValTyId.lhs' core
                   ; rhs0 = REqValTyId.rhs' core ; red = REqValTyId.redN core
                   ; wit0 = RValId.wit0 rid ; redTm = redTm-type-transport cCC' htC' (RValId.redTm rid)
                   ; refConvL = fst rcs ; refConvR = snd rcs ; refMem = RValId.refMem rid
                   ; endEqL = fst ees ; endEqR = snd ees })
    VTT Bot (IdCode a a1 a2) eqvt val = tt
    VTT UCode (IdCode a a1 a2) eqvt val = tt
    VTT (FunEl g) (IdCode a a1 a2) eqvt val = tt
    VTT (PiCode b f) (IdCode a a1 a2) eqvt val = tt
    VTT (IdCode s0 s1 s2) (IdCode a a1 a2) eqvt val = tt
    VTT u (RefEl a) eqvt val = tt

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
    EVTT (IdCode t1 t2 t3) UCode eqvt ev = mkSigma (snd eqvt) (snd ev)
    EVTT (RefEl w) UCode eqvt ev = tt
    EVTT (IdCode t1 t2 t3) (PiCode b f) eqvt ev = tt
    EVTT (RefEl w) (PiCode b f) eqvt ev = tt
    EVTT (RefEl w) (IdCode t' u' v') eqvt ev =
      let core = snd (snd eqvt)
          cc   = idTyConvC (fst eqvt) core ; cCC' = fst cc ; htC' = snd cc
          ridM = fst (snd ev) ; ridN = fst (snd (snd ev)) ; reid = snd (snd (snd ev))
          dA0 = REqValTyId.domA' core ; l0 = REqValTyId.lhs' core ; r0 = REqValTyId.rhs' core ; rN = REqValTyId.redN core
          rcsM = refConvsFwd ridM core ; rcsN = refConvsFwd ridN core
          eesM = endEqFwd ridM core ; eesN = endEqFwd ridN core
          eesLM = endEqFwdRaw (REqValId.red reid) (REqValId.refMem reid) (REqValId.endEqLM reid) (REqValId.endEqRM reid) core
          eesLN = endEqFwdRaw (REqValId.red reid) (REqValId.refMem reid) (REqValId.endEqLN reid) (REqValId.endEqRN reid) core
      in mkSigma (fst (snd eqvt))
           (mkSigma (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                            ; wit0 = RValId.wit0 ridM ; redTm = redTm-type-transport cCC' htC' (RValId.redTm ridM)
                            ; refConvL = fst rcsM ; refConvR = snd rcsM ; refMem = RValId.refMem ridM
                            ; endEqL = fst eesM ; endEqR = snd eesM })
             (mkSigma (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                              ; wit0 = RValId.wit0 ridN ; redTm = redTm-type-transport cCC' htC' (RValId.redTm ridN)
                              ; refConvL = fst rcsN ; refConvR = snd rcsN ; refMem = RValId.refMem ridN
                              ; endEqL = fst eesN ; endEqR = snd eesN })
                      (record { domA0 = dA0 ; lhs0 = l0 ; rhs0 = r0 ; red = rN
                              ; wit0M = REqValId.wit0M reid ; wit0N = REqValId.wit0N reid
                              ; redTmM = redTm-type-transport cCC' htC' (REqValId.redTmM reid)
                              ; redTmN = redTm-type-transport cCC' htC' (REqValId.redTmN reid) ; refMem = REqValId.refMem reid
                              ; endEqLM = fst eesLM ; endEqRM = snd eesLM ; endEqLN = fst eesLN ; endEqRN = snd eesLN })))
    EVTT Bot (IdCode a a1 a2) eqvt ev = tt
    EVTT UCode (IdCode a a1 a2) eqvt ev = tt
    EVTT (FunEl g) (IdCode a a1 a2) eqvt ev = tt
    EVTT (PiCode b f) (IdCode a a1 a2) eqvt ev = tt
    EVTT (IdCode s0 s1 s2) (IdCode a a1 a2) eqvt ev = tt
    EVTT u (RefEl a) eqvt ev = tt

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
    v2eB    = ReflPack.Val2-to-EqVal2 (goodStageRefl n)
    vf1     = MonoPack.Val2-from-EqVal2-first (goodStage n)
    vf2     = MonoPack.Val2-from-EqVal2-second (goodStage n)
    rstrE   = MonoPack.restrictEqVal2 (goodStage n)
    evsym   = FwdPack.EqVal2-sym (goodStageFwd n)
    evtrans = FwdPack.EqVal2-trans (goodStageFwd n)
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
    Beta (IdCode t1 t2 t3) UCode hr ct val =
      let vtA = fst val ; vtId' = snd val
          ctU = conv-conv ct (Red3.ct vtA) (typing-type (typing-type (fst (typing-ConvTm ct))))
          newRed = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyId.red vtId')))
                          (conv-trans ctU (Red3.ct (RValTyId.red vtId')))
          A0 = RValTyId.domA vtId' ; l0 = RValTyId.lhs vtId' ; r0 = RValTyId.rhs vtId'
          vtId = record
            { domA = A0 ; lhs = l0 ; rhs = r0 ; red = newRed
            ; htA = RValTyId.htA vtId' ; htL = RValTyId.htL vtId' ; htR = RValTyId.htR vtId'
            ; valA = RValTyId.valA vtId' ; valL = RValTyId.valL vtId' ; valR = RValTyId.valR vtId'
            ; valLlog = RValTyId.valLlog vtId' ; valRlog = RValTyId.valRlog vtId' }
          coreEq = record
            { domA = A0 ; lhs = l0 ; rhs = r0
            ; domA' = A0 ; lhs' = l0 ; rhs' = r0
            ; redM = RValTyId.red vtId' ; redN = newRed
            ; convA = conv-refl (RValTyId.htA vtId')
            ; convL = conv-refl (RValTyId.htL vtId')
            ; convR = conv-refl (RValTyId.htR vtId')
            ; eqA = vt2e t1 (RValTyId.valA vtId')
            ; eqL = v2eB t2 t1 (RValTyId.valLlog vtId') ; eqR = v2eB t3 t1 (RValTyId.valRlog vtId') }
      in mkSigma vtA (mkSigma vtId' (mkSigma vtId (mkSigma vtId' (mkSigma vtId coreEq))))
    Beta (RefEl w) UCode hr ct val = tt
    Beta (IdCode t1 t2 t3) (PiCode b f) hr ct val = tt
    Beta (RefEl w) (PiCode b f) hr ct val = tt
    Beta (RefEl w) (IdCode t' u' v') hr ct val =
      let rid = snd val
          redTmM' = mkRed3 (HeadRed-trans hr (Red3.hr (RValId.redTm rid)))
                          (conv-trans ct (Red3.ct (RValId.redTm rid)))
      in mkSigma (fst val) (mkSigma rid (mkSigma
           (record { domA0 = RValId.domA0 rid ; lhs0 = RValId.lhs0 rid ; rhs0 = RValId.rhs0 rid ; red = RValId.red rid ; wit0 = RValId.wit0 rid ; redTm = redTmM' ; refConvL = RValId.refConvL rid ; refConvR = RValId.refConvR rid ; refMem = RValId.refMem rid ; endEqL = RValId.endEqL rid ; endEqR = RValId.endEqR rid })
           (record { domA0 = RValId.domA0 rid ; lhs0 = RValId.lhs0 rid ; rhs0 = RValId.rhs0 rid ; red = RValId.red rid ; wit0M = RValId.wit0 rid ; wit0N = RValId.wit0 rid ; redTmM = RValId.redTm rid ; redTmN = redTmM' ; refMem = RValId.refMem rid ; endEqLM = RValId.endEqL rid ; endEqRM = RValId.endEqR rid ; endEqLN = RValId.endEqL rid ; endEqRN = RValId.endEqR rid })))
    Beta Bot (IdCode a a1 a2) hr ct val = tt
    Beta UCode (IdCode a a1 a2) hr ct val = tt
    Beta (FunEl g) (IdCode a a1 a2) hr ct val = tt
    Beta (PiCode b f) (IdCode a a1 a2) hr ct val = tt
    Beta (IdCode s0 s1 s2) (IdCode a a1 a2) hr ct val = tt
    Beta u (RefEl a) hr ct val = tt
