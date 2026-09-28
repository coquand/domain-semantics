{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityHeadRed.agda  (MIN/ — Pi + U fragment)
--
-- Stratified head-expansion / head-contraction transport, replacing the
-- mutual block that used to live in AdequacyHeadRed.
--
-- These functions keep the codes (u,a) FIXED and only rewrite the
-- expressions; the only recursion descends a Pi edge to the strictly
-- smaller code (v, EvalFun f u).  That is a RANK decrease, so — exactly
-- like the MonoPack/FwdPack/BetaPack families — we package the functions
-- as `HeadRedPack k` and prove `goodStageHeadRed : (k) -> HeadRedPack k`
-- by structural recursion on the stage index k.  Within `goodStageHeadRed
-- (suc n)` the Pi-edge recursion lands at stage n = the IH pack, so there
-- is no cycle.
--
-- Public (canonical-level) wrappers at the end: since the transport is
-- code-fixed, input and output sit at the SAME canonical level, so no
-- `shift*` is needed (unlike the rank-changing lemmas in ValidityLevels).
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Valid.HeadRed (D : LDecAll) where

open import BCDE4.Levels using (LExpr ; Valid ; v-sym)

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)
open import BCDE4.Valid.Core using (U-tr)
open import BCDE4.Valid.Stratified D using (Ann ; mkAnn ; Ann-back)
open import BCDE4.Valid.AnnLemmas D

open import BCDE4.Valid.Mono D
open import BCDE4.Valid.Props D using (BetaPack ; goodStageBeta ; HeadRed-LApp)
open import BCDE4.Valid.Stratified D using (Red3 ; mkRed3 ; Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ; codeL)

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              max ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              LevTy ; LevEl ; LPiCode)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; App ; subst1 ; LPi ; LApp ; lsub1)
open import BCDE4.RussellTyping
open import BCDE4.RussellReduction
open import BCDE4.Dom.Kernel using (EvalFun ; Coherent-EvalFun ; cft-from-cf ; LeCode ; Coherent)
open import BCDE4.Model.Selection using (Selection ; Coherent-Selection ; Coherent-Selection-val)
open import BCDE4.RussellMeta
open import BCDE4.RussellMetaCong using (subst1-cong-Ty)
open import BCDE4.RussellLeq using (lsub1-cong)
open import BCDE4.Dom.Rank using (RANK)
open import BCDE4.Valid.Stratified D using (RValU ; mkRValU ; ulv ; ured ; ucode)

-- the universe clause along head reduction
rvu-contract : {m : Nat} {G : Ctx m} {M M' : Expr m} {k : Nat} ->
  HeadRed M M' -> ConvTy G M M' -> RValU G M k -> RValU G M' k
rvu-contract hr cv (mkRValU l r e) =
  mkRValU l (mkRed3 (HeadRed-strip-U hr (Red3.hr r)) (conv-Ty-trans (conv-Ty-sym cv) (Red3.ct r))) e

rvu-expand : {m : Nat} {G : Ctx m} {M M' : Expr m} {k : Nat} ->
  HeadRed M' M -> ConvTy G M' M -> RValU G M k -> RValU G M' k
rvu-expand hr cv (mkRValU l r e) =
  mkRValU l (mkRed3 (HeadRed-trans hr (Red3.hr r)) (conv-Ty-trans cv (Red3.ct r))) e



------------------------------------------------------------------------
-- HeadRedPack: the head-expansion/contraction transports at Stage k.
-- The three entry points reachable across stages (via the Pi-edge IH).
------------------------------------------------------------------------

record HeadRedPack (k : Nat) : Set1 where
  field
    Val2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
      Vl k G M T u a -> Vl k G M' T u a
    EqVal2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' T -> ConvTm G M2 M2' T ->
      EVl k G M1 M2 T u a -> EVl k G M1' M2' T u a
    EqVal2-headred-expand : {m : Nat} {G : Ctx m} {M M' N N' T : Expr m}
      (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
      ConvTm G M' M T -> ConvTm G N' N T ->
      EVl k G M N T u a -> EVl k G M' N' T u a
    ValTy2-headred-expand : {m : Nat} {G : Ctx m} {M M' : Expr m}
      (u : FinEl) -> HeadRed M' M -> ConvTy G M' M ->
      VTy k G M u -> VTy k G M' u
    EqValTy2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
      (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
      ConvTy G M1' M1 -> ConvTy G M2' M2 ->
      EVTy k G M1 M2 u -> EVTy k G M1' M2' u

goodStageHeadRed : (k : Nat) -> HeadRedPack k
goodStageHeadRed zero = record
  { Val2-headred-contract   = \ u a hr cv val -> tt
  ; EqVal2-headred-contract = \ u a hr1 hr2 cv1 cv2 ev -> tt
  ; EqVal2-headred-expand   = \ u a hr1 hr2 cv1 cv2 ev -> tt
  ; ValTy2-headred-expand   = \ u hr cv vt -> tt
  ; EqValTy2-headred-expand = \ u hr1 hr2 cv1 cv2 ev -> tt
  }
goodStageHeadRed (suc n) = record
  { Val2-headred-contract   = Val2-headred-contract
  ; EqVal2-headred-contract = EqVal2-headred-contract
  ; EqVal2-headred-expand   = EqVal2-headred-expand
  ; ValTy2-headred-expand   = ValTy2-headred-expand
  ; EqValTy2-headred-expand = EqValTy2-headred-expand
  }
  where
    ihH : HeadRedPack n
    ihH = goodStageHeadRed n
    hrc-n = HeadRedPack.Val2-headred-contract ihH
    ehc-n = HeadRedPack.EqVal2-headred-contract ihH
    ehe-n = HeadRedPack.EqVal2-headred-expand ihH
    open SR n
    betaB = BetaPack.Val2-beta-expand (goodStageBeta n)
    vf2   = MonoPack.Val2-from-EqVal2-second (goodStage n)

    -- local Val2->Val2 beta-expansion at stage n (HeadRed M' M)
    betaExp : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (u a : FinEl) -> HeadRed M' M -> ConvTm G M' M T ->
      Vl n G M T u a -> Vl n G M' T u a
    betaExp u a hr cv val = vf2 u a (betaB u a hr cv val)

    -- ValTy2-headred-contract: HeadRed M M', ConvTy G M M'
    ValTy2-headred-contract : {m : Nat} {G : Ctx m} {M M' : Expr m}
      (u : FinEl) -> HeadRed M M' -> ConvTy G M M' ->
      VTy (suc n) G M u -> VTy (suc n) G M' u
    ValTy2-headred-contract Bot hr cv vt = tt
    ValTy2-headred-contract (UCode lu) hr cv vt = rvu-contract hr cv vt
    ValTy2-headred-contract (FunEl g) hr cv vt = tt
    ValTy2-headred-contract (PiCode b f) hr cv vt =
      record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
             ; red = mkRed3 (HeadRed-strip-Pi hr (Red3.hr (RValTyPi.red vt)))
                            (conv-Ty-trans (conv-Ty-sym cv) (Red3.ct (RValTyPi.red vt)))
             ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
             ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
             ; valA = RValTyPi.valA vt
             ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }

    ValTy2-headred-contract LevTy hr cv vt = tt
    ValTy2-headred-contract (LevEl k) hr cv vt = tt
    ValTy2-headred-contract (LPiCode f) hr cv vt =
      record { domA = RValTyLPi.domA vt
             ; red = mkRed3 (HeadRed-strip-LPi hr (Red3.hr (RValTyLPi.red vt))) (conv-Ty-trans (conv-Ty-sym cv) (Red3.ct (RValTyLPi.red vt)))
             ; cohF = RValTyLPi.cohF vt ; fmAllU = RValTyLPi.fmAllU vt
             ; htA = RValTyLPi.htA vt
             ; edgeV = RValTyLPi.edgeV vt ; edgeLE = RValTyLPi.edgeLE vt }
    -- ValTy2-headred-expand: HeadRed M' M, ConvTy G M' M
    ValTy2-headred-expand : {m : Nat} {G : Ctx m} {M M' : Expr m}
      (u : FinEl) -> HeadRed M' M -> ConvTy G M' M ->
      VTy (suc n) G M u -> VTy (suc n) G M' u
    ValTy2-headred-expand Bot hr cv vt = tt
    ValTy2-headred-expand (UCode lu) hr cv vt = rvu-expand hr cv vt
    ValTy2-headred-expand (FunEl g) hr cv vt = tt
    ValTy2-headred-expand (PiCode b f) hr cv vt =
      record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
             ; red = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyPi.red vt)))
                            (conv-Ty-trans cv (Red3.ct (RValTyPi.red vt)))
             ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
             ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
             ; valA = RValTyPi.valA vt
             ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }

    ValTy2-headred-expand LevTy hr cv vt = tt
    ValTy2-headred-expand (LevEl k) hr cv vt = tt
    ValTy2-headred-expand (LPiCode f) hr cv vt =
      record { domA = RValTyLPi.domA vt
             ; red = mkRed3 (HeadRed-trans hr (Red3.hr (RValTyLPi.red vt))) (conv-Ty-trans cv (Red3.ct (RValTyLPi.red vt)))
             ; cohF = RValTyLPi.cohF vt ; fmAllU = RValTyLPi.fmAllU vt
             ; htA = RValTyLPi.htA vt
             ; edgeV = RValTyLPi.edgeV vt ; edgeLE = RValTyLPi.edgeLE vt }
    -- EqValTy2-headred-contract
    EqValTy2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
      (u : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTy G M1 M1' -> ConvTy G M2 M2' ->
      EVTy (suc n) G M1 M2 u -> EVTy (suc n) G M1' M2' u
    EqValTy2-headred-contract Bot hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-contract (UCode lu) hr1 hr2 cv1 cv2 eqvt =
      mkSigma (rvu-contract hr1 cv1 (fst eqvt)) (rvu-contract hr2 cv2 (snd eqvt))
    EqValTy2-headred-contract (FunEl g) hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-contract (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-contract (PiCode b f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-contract (PiCode b f) hr2 cv2 vt2)
             (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                     ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                     ; redM = mkRed3 (HeadRed-strip-Pi hr1 (Red3.hr (REqValTyPi.redM core)))
                                     (conv-Ty-trans (conv-Ty-sym cv1) (Red3.ct (REqValTyPi.redM core)))
                     ; redN = mkRed3 (HeadRed-strip-Pi hr2 (Red3.hr (REqValTyPi.redN core)))
                                     (conv-Ty-trans (conv-Ty-sym cv2) (Red3.ct (REqValTyPi.redN core)))
                     ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                     ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                     ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))

    EqValTy2-headred-contract LevTy hr1 hr2 cv1 cv2 eqvt = tt
    EqValTy2-headred-contract (LevEl k) hr1 hr2 cv1 cv2 eqvt = tt
    EqValTy2-headred-contract (LPiCode f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-contract (LPiCode f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-contract (LPiCode f) hr2 cv2 vt2)
             (record { domA = REqValTyLPi.domA core ; domA' = REqValTyLPi.domA' core
                     ; redM = mkRed3 (HeadRed-strip-LPi hr1 (Red3.hr (REqValTyLPi.redM core))) (conv-Ty-trans (conv-Ty-sym cv1) (Red3.ct (REqValTyLPi.redM core)))
                     ; redN = mkRed3 (HeadRed-strip-LPi hr2 (Red3.hr (REqValTyLPi.redN core))) (conv-Ty-trans (conv-Ty-sym cv2) (Red3.ct (REqValTyLPi.redN core)))
                     ; cohF = REqValTyLPi.cohF core ; fmAllU = REqValTyLPi.fmAllU core
                     ; convA = REqValTyLPi.convA core ; edgeET = REqValTyLPi.edgeET core }))
    -- EqValTy2-headred-expand
    EqValTy2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
      (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
      ConvTy G M1' M1 -> ConvTy G M2' M2 ->
      EVTy (suc n) G M1 M2 u -> EVTy (suc n) G M1' M2' u
    EqValTy2-headred-expand Bot hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-expand (UCode lu) hr1 hr2 cv1 cv2 eqvt =
      mkSigma (rvu-expand hr1 cv1 (fst eqvt)) (rvu-expand hr2 cv2 (snd eqvt))
    EqValTy2-headred-expand (FunEl g) hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-expand (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-expand (PiCode b f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-expand (PiCode b f) hr2 cv2 vt2)
             (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                     ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                     ; redM = mkRed3 (HeadRed-trans hr1 (Red3.hr (REqValTyPi.redM core)))
                                     (conv-Ty-trans cv1 (Red3.ct (REqValTyPi.redM core)))
                     ; redN = mkRed3 (HeadRed-trans hr2 (Red3.hr (REqValTyPi.redN core)))
                                     (conv-Ty-trans cv2 (Red3.ct (REqValTyPi.redN core)))
                     ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                     ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                     ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))

    EqValTy2-headred-expand LevTy hr1 hr2 cv1 cv2 eqvt = tt
    EqValTy2-headred-expand (LevEl k) hr1 hr2 cv1 cv2 eqvt = tt
    EqValTy2-headred-expand (LPiCode f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-expand (LPiCode f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-expand (LPiCode f) hr2 cv2 vt2)
             (record { domA = REqValTyLPi.domA core ; domA' = REqValTyLPi.domA' core
                     ; redM = mkRed3 (HeadRed-trans hr1 (Red3.hr (REqValTyLPi.redM core))) (conv-Ty-trans cv1 (Red3.ct (REqValTyLPi.redM core)))
                     ; redN = mkRed3 (HeadRed-trans hr2 (Red3.hr (REqValTyLPi.redN core))) (conv-Ty-trans cv2 (Red3.ct (REqValTyLPi.redN core)))
                     ; cohF = REqValTyLPi.cohF core ; fmAllU = REqValTyLPi.fmAllU core
                     ; convA = REqValTyLPi.convA core ; edgeET = REqValTyLPi.edgeET core }))
    -- ValPi2-headred-contract: edge recursion lands at stage n (ihH)
    ValPi2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (g0 : FinFun) (b : FinEl) (f : FinFun) ->
      HeadRed M M' -> ConvTm G M M' T -> RValTyPi G T b f ->
      RValPi G M T g0 b f -> RValPi G M' T g0 b f
    ValPi2-headred-contract g0 b f hr cv vty vpiM =
      let A0    = RValPi.domA0 vpiM
          B0    = RValPi.codB0 vpiM
          redT  = RValPi.red vpiM
          uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType _ X) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> IsType (extend _ A0) Y) (snd uniq)
                    (S.Eq-transport (\ X -> IsType (extend _ X) _) (fst uniq) (RValTyPi.htB vty))
          ctPi  = conv-conv cv (Red3.ct redT)
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
                ; appV = \ u v sel {A1} {B1} an N htN valN ->
                    hrc-n v (EvalFun f u) (HeadRed-App hr)
                      (ann-App-fun htA0 an ctPi htN)
                      (RValPi.appV vpiM u v sel an N htN valN)
                ; appE = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN ->
                    let cvApp1 = ann-App-fun htA0 an1 ctPi htN1
                        cvApp2-raw = ann-App-fun htA0 an2 ctPi htN2
                        cvBN = subst1-cong-Ty cvN htA0 htB0
                        cvApp2 = conv-conv cvApp2-raw (conv-Ty-sym cvBN)
                    in ehc-n v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                         cvApp1 cvApp2
                         (RValPi.appE vpiM u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN) }

    EqValPi2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (g0 : FinFun) (b : FinEl) (f : FinFun) ->
      HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' T -> ConvTm G M2 M2' T -> RValTyPi G T b f ->
      REqValPi G M1 M2 T g0 b f -> REqValPi G M1' M2' T g0 b f
    EqValPi2-headred-contract g0 b f hr1 hr2 cv1 cv2 vty epi =
      let A0    = REqValPi.domA0 epi
          B0    = REqValPi.codB0 epi
          redT  = REqValPi.red epi
          uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType _ X) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> IsType (extend _ A0) Y) (snd uniq)
                    (S.Eq-transport (\ X -> IsType (extend _ X) _) (fst uniq) (RValTyPi.htB vty))
          ctPi1 = conv-conv cv1 (Red3.ct redT)
          ctPi2 = conv-conv cv2 (Red3.ct redT)
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
                ; appEV = \ u v sel {A1} {A2} {B1} {B2} an1 an2 P htP valP ->
                    ehc-n v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                      (ann-App-fun htA0 an1 ctPi1 htP) (ann-App-fun htA0 an2 ctPi2 htP)
                      (REqValPi.appEV epi u v sel an1 an2 P htP valP) }

    -- ValPi2-headred-expand: edge appV via betaExp (stage n), appE via ehe-n
    ValPi2-headred-expand : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (g0 : FinFun) (b : FinEl) (f : FinFun) ->
      HeadRed M' M -> ConvTm G M' M T -> RValTyPi G T b f ->
      RValPi G M T g0 b f -> RValPi G M' T g0 b f
    ValPi2-headred-expand g0 b f hr cv vty vpiM =
      let A0    = RValPi.domA0 vpiM
          B0    = RValPi.codB0 vpiM
          redT  = RValPi.red vpiM
          uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType _ X) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> IsType (extend _ A0) Y) (snd uniq)
                    (S.Eq-transport (\ X -> IsType (extend _ X) _) (fst uniq) (RValTyPi.htB vty))
          ctPi  = conv-conv cv (Red3.ct redT)
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
                ; appV = \ u v sel {A1} {B1} an N htN valN ->
                    betaExp v (EvalFun f u) (HeadRed-App hr)
                      (ann-App-fun htA0 an ctPi htN)
                      (RValPi.appV vpiM u v sel an N htN valN)
                ; appE = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN ->
                    let cvApp1 = ann-App-fun htA0 an1 ctPi htN1
                        cvApp2-raw = ann-App-fun htA0 an2 ctPi htN2
                        cvBN = subst1-cong-Ty cvN htA0 htB0
                        cvApp2 = conv-conv cvApp2-raw (conv-Ty-sym cvBN)
                    in ehe-n v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                         cvApp1 cvApp2
                         (RValPi.appE vpiM u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN) }

    EqValPi2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (g0 : FinFun) (b : FinEl) (f : FinFun) ->
      HeadRed M1' M1 -> HeadRed M2' M2 ->
      ConvTm G M1' M1 T -> ConvTm G M2' M2 T -> RValTyPi G T b f ->
      REqValPi G M1 M2 T g0 b f -> REqValPi G M1' M2' T g0 b f
    EqValPi2-headred-expand g0 b f hr1 hr2 cv1 cv2 vty epi =
      let A0    = REqValPi.domA0 epi
          B0    = REqValPi.codB0 epi
          redT  = REqValPi.red epi
          uniq  = Red3-unique-Pi (RValTyPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType _ X) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> IsType (extend _ A0) Y) (snd uniq)
                    (S.Eq-transport (\ X -> IsType (extend _ X) _) (fst uniq) (RValTyPi.htB vty))
          ctPi1 = conv-conv cv1 (Red3.ct redT)
          ctPi2 = conv-conv cv2 (Red3.ct redT)
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
                ; appEV = \ u v sel {A1} {A2} {B1} {B2} an1 an2 P htP valP ->
                    ehe-n v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                      (ann-App-fun htA0 an1 ctPi1 htP) (ann-App-fun htA0 an2 ctPi2 htP)
                      (REqValPi.appEV epi u v sel an1 an2 P htP valP) }

    -- level products: the transports of RValLPi / REqValLPi.
    ValLPi2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (g0 : FinFun) (f : FinFun) ->
      HeadRed M M' -> ConvTm G M M' T -> RValTyLPi G T f ->
      RValLPi G M T g0 f -> RValLPi G M' T g0 f
    ValLPi2-headred-contract {G = G} g0 f hr cv vty vpiM =
      let A0    = RValLPi.domA0 vpiM
          redT  = RValLPi.red vpiM
          uniq  = Red3-unique-LPi (RValTyLPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType (addL G) X) uniq (RValTyLPi.htA vty)
          ctPi  = conv-conv cv (Red3.ct redT)
          ctg   = cft-from-cf g0 (RValLPi.cohG vpiM)
          cf    = RValTyLPi.cohF vty
      in record { domA0 = A0 ; red = redT
                ; cohG = RValLPi.cohG vpiM ; fmG = RValLPi.fmG vpiM
                ; appV = \ u v sel an l lel ->
                    hrc-n v (EvalFun f u) (HeadRed-LApp hr) (lann-LApp-fun htA0 an ctPi)
                      (RValLPi.appV vpiM u v sel an l lel)
                ; appLE = \ u v sel an1 an2 l l' e lel ->
                    ehc-n v (EvalFun f u) (HeadRed-LApp hr) (HeadRed-LApp hr)
                      (lann-LApp-fun htA0 an1 ctPi)
                      (conv-conv (lann-LApp-fun htA0 an2 ctPi) (lsub1-cong htA0 (v-sym e)))
                      (RValLPi.appLE vpiM u v sel an1 an2 l l' e lel) }

    EqValLPi2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (g0 : FinFun) (f : FinFun) ->
      HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' T -> ConvTm G M2 M2' T -> RValTyLPi G T f ->
      REqValLPi G M1 M2 T g0 f -> REqValLPi G M1' M2' T g0 f
    EqValLPi2-headred-contract {G = G} g0 f hr1 hr2 cv1 cv2 vty epi =
      let A0    = REqValLPi.domA0 epi
          redT  = REqValLPi.red epi
          uniq  = Red3-unique-LPi (RValTyLPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType (addL G) X) uniq (RValTyLPi.htA vty)
          ctPi1 = conv-conv cv1 (Red3.ct redT)
          ctPi2 = conv-conv cv2 (Red3.ct redT)
      in record { domA0 = A0 ; red = redT
                ; cohG = REqValLPi.cohG epi ; fmG = REqValLPi.fmG epi
                ; appEV = \ u v sel an1 an2 l lel ->
                    ehc-n v (EvalFun f u) (HeadRed-LApp hr1) (HeadRed-LApp hr2)
                      (lann-LApp-fun htA0 an1 ctPi1) (lann-LApp-fun htA0 an2 ctPi2)
                      (REqValLPi.appEV epi u v sel an1 an2 l lel) }

    ValLPi2-headred-expand : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (g0 : FinFun) (f : FinFun) ->
      HeadRed M' M -> ConvTm G M' M T -> RValTyLPi G T f ->
      RValLPi G M T g0 f -> RValLPi G M' T g0 f
    ValLPi2-headred-expand {G = G} g0 f hr cv vty vpiM =
      let A0    = RValLPi.domA0 vpiM
          redT  = RValLPi.red vpiM
          uniq  = Red3-unique-LPi (RValTyLPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType (addL G) X) uniq (RValTyLPi.htA vty)
          ctPi  = conv-conv cv (Red3.ct redT)
          ctg   = cft-from-cf g0 (RValLPi.cohG vpiM)
          cf    = RValTyLPi.cohF vty
      in record { domA0 = A0 ; red = redT
                ; cohG = RValLPi.cohG vpiM ; fmG = RValLPi.fmG vpiM
                ; appV = \ u v sel an l lel ->
                    betaExp v (EvalFun f u) (HeadRed-LApp hr) (lann-LApp-fun htA0 an ctPi)
                      (RValLPi.appV vpiM u v sel an l lel)
                ; appLE = \ u v sel an1 an2 l l' e lel ->
                    ehe-n v (EvalFun f u) (HeadRed-LApp hr) (HeadRed-LApp hr)
                      (lann-LApp-fun htA0 an1 ctPi)
                      (conv-conv (lann-LApp-fun htA0 an2 ctPi) (lsub1-cong htA0 (v-sym e)))
                      (RValLPi.appLE vpiM u v sel an1 an2 l l' e lel) }

    EqValLPi2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (g0 : FinFun) (f : FinFun) ->
      HeadRed M1' M1 -> HeadRed M2' M2 ->
      ConvTm G M1' M1 T -> ConvTm G M2' M2 T -> RValTyLPi G T f ->
      REqValLPi G M1 M2 T g0 f -> REqValLPi G M1' M2' T g0 f
    EqValLPi2-headred-expand {G = G} g0 f hr1 hr2 cv1 cv2 vty epi =
      let A0    = REqValLPi.domA0 epi
          redT  = REqValLPi.red epi
          uniq  = Red3-unique-LPi (RValTyLPi.red vty) redT
          htA0  = S.Eq-transport (\ X -> IsType (addL G) X) uniq (RValTyLPi.htA vty)
          ctPi1 = conv-conv cv1 (Red3.ct redT)
          ctPi2 = conv-conv cv2 (Red3.ct redT)
      in record { domA0 = A0 ; red = redT
                ; cohG = REqValLPi.cohG epi ; fmG = REqValLPi.fmG epi
                ; appEV = \ u v sel an1 an2 l lel ->
                    ehe-n v (EvalFun f u) (HeadRed-LApp hr1) (HeadRed-LApp hr2)
                      (lann-LApp-fun htA0 an1 ctPi1) (lann-LApp-fun htA0 an2 ctPi2)
                      (REqValLPi.appEV epi u v sel an1 an2 l lel) }

    -- Val2-headred-contract (entry point at stage suc n)
    Val2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
      Vl (suc n) G M T u a -> Vl (suc n) G M' T u a
    Val2-headred-contract u Bot hr cv tt = tt
    Val2-headred-contract Bot (UCode lu) hr cv tt = tt
    Val2-headred-contract (UCode lu) (UCode lv) hr cv val =
      let vtA = fst val ; vtM = snd val
          ctU = conv-conv cv (Red3.ct (ured vtA))
      in mkSigma vtA (rvu-contract hr (conv-Ty-from-U ctU) vtM)
    Val2-headred-contract (FunEl g) (UCode lu) hr cv tt = tt
    Val2-headred-contract (PiCode a' f') (UCode lu) hr cv val =
      let vtA = fst val ; vtPi = snd val
          ctU = conv-conv cv (Red3.ct (ured vtA))
      in mkSigma vtA (ValTy2-headred-contract (PiCode a' f') hr (conv-Ty-from-U ctU) vtPi)
    Val2-headred-contract u (FunEl h) hr cv tt = tt
    Val2-headred-contract Bot (PiCode b f) hr cv tt = tt
    Val2-headred-contract (UCode lu) (PiCode b f) hr cv tt = tt
    Val2-headred-contract (FunEl g) (PiCode b f) hr cv val =
      mkSigma (fst val) (ValPi2-headred-contract g b f hr cv (fst val) (snd val))
    Val2-headred-contract (PiCode a' f') (PiCode b f) hr cv tt = tt
    Val2-headred-contract LevTy (UCode lu) hr cv val = tt
    Val2-headred-contract (LevEl k) (UCode lu) hr cv val = tt
    Val2-headred-contract (LPiCode f') (UCode lu) hr cv val =
      let vtA = fst val ; vtPi = snd val
          ctU = conv-conv cv (Red3.ct (ured vtA))
      in mkSigma vtA (ValTy2-headred-contract (LPiCode f') hr (conv-Ty-from-U ctU) vtPi)
    Val2-headred-contract u LevTy hr cv val = tt
    Val2-headred-contract u (LevEl k) hr cv val = tt
    Val2-headred-contract LevTy (PiCode b f) hr cv val = tt
    Val2-headred-contract (LevEl k) (PiCode b f) hr cv val = tt
    Val2-headred-contract (LPiCode f') (PiCode b f) hr cv val = tt
    Val2-headred-contract Bot (LPiCode f) hr cv val = tt
    Val2-headred-contract (UCode lu) (LPiCode f) hr cv val = tt
    Val2-headred-contract LevTy (LPiCode f) hr cv val = tt
    Val2-headred-contract (LevEl k) (LPiCode f) hr cv val = tt
    Val2-headred-contract (PiCode a' f') (LPiCode f) hr cv val = tt
    Val2-headred-contract (LPiCode f') (LPiCode f) hr cv val = tt
    Val2-headred-contract (FunEl g) (LPiCode f) hr cv val =
      mkSigma (fst val) (ValLPi2-headred-contract g f hr cv (fst val) (snd val))

    -- EqVal2-headred-expand (entry point)
    EqVal2-headred-expand : {m : Nat} {G : Ctx m} {M M' N N' T : Expr m}
      (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
      ConvTm G M' M T -> ConvTm G N' N T ->
      EVl (suc n) G M N T u a -> EVl (suc n) G M' N' T u a
    EqVal2-headred-expand u Bot hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand Bot (UCode lu) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (UCode lu) (UCode lv) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
          vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
          vtM' = rvu-expand hr1 (conv-Ty-from-U ctU1) vtM
          vtN' = rvu-expand hr2 (conv-Ty-from-U ctU2) vtN
      in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
    EqVal2-headred-expand (FunEl g) (UCode lu) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (PiCode a' f') (UCode lu) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
          expand1 = ValTy2-headred-expand (PiCode a' f') hr1 (conv-Ty-from-U ctU1) (fst (snd ev))
          expand2 = ValTy2-headred-expand (PiCode a' f') hr2 (conv-Ty-from-U ctU2) (fst (snd (snd ev)))
          eqexpand = EqValTy2-headred-expand (PiCode a' f') hr1 hr2 (conv-Ty-from-U ctU1) (conv-Ty-from-U ctU2) (snd (snd (snd ev)))
      in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
    EqVal2-headred-expand u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (UCode lu) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValPi2-headred-expand g b f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValPi2-headred-expand g b f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValPi2-headred-expand g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
    EqVal2-headred-expand (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand LevTy (UCode lu) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LevEl k) (UCode lu) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LPiCode f') (UCode lu) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
          expand1 = ValTy2-headred-expand (LPiCode f') hr1 (conv-Ty-from-U ctU1) (fst (snd ev))
          expand2 = ValTy2-headred-expand (LPiCode f') hr2 (conv-Ty-from-U ctU2) (fst (snd (snd ev)))
          eqexpand = EqValTy2-headred-expand (LPiCode f') hr1 hr2 (conv-Ty-from-U ctU1) (conv-Ty-from-U ctU2) (snd (snd (snd ev)))
      in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
    EqVal2-headred-expand u LevTy hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand u (LevEl k) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand LevTy (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LevEl k) (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LPiCode f') (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand Bot (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (UCode lu) (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand LevTy (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LevEl k) (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (PiCode a' f') (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (LPiCode f') (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (FunEl g) (LPiCode f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValLPi2-headred-expand g f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValLPi2-headred-expand g f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValLPi2-headred-expand g f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))

    -- EqVal2-headred-contract (entry point)
    EqVal2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' T -> ConvTm G M2 M2' T ->
      EVl (suc n) G M1 M2 T u a -> EVl (suc n) G M1' M2' T u a
    EqVal2-headred-contract u Bot hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract Bot (UCode lu) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (UCode lu) (UCode lv) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
          vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
          vtM' = rvu-contract hr1 (conv-Ty-from-U ctU1) vtM
          vtN' = rvu-contract hr2 (conv-Ty-from-U ctU2) vtN
      in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
    EqVal2-headred-contract (FunEl g) (UCode lu) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (PiCode a' f') (UCode lu) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
      in mkSigma vtA
           (mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 (conv-Ty-from-U ctU1) (fst (snd ev)))
             (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 (conv-Ty-from-U ctU2) (fst (snd (snd ev))))
               (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 (conv-Ty-from-U ctU1) (conv-Ty-from-U ctU2) (snd (snd (snd ev))))))
    EqVal2-headred-contract u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (UCode lu) (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValPi2-headred-contract g b f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValPi2-headred-contract g b f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValPi2-headred-contract g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
    EqVal2-headred-contract (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract LevTy (UCode lu) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LevEl k) (UCode lu) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LPiCode f') (UCode lu) hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3.ct (ured vtA))
          ctU2 = conv-conv cv2 (Red3.ct (ured vtA))
      in mkSigma vtA
           (mkSigma (ValTy2-headred-contract (LPiCode f') hr1 (conv-Ty-from-U ctU1) (fst (snd ev)))
             (mkSigma (ValTy2-headred-contract (LPiCode f') hr2 (conv-Ty-from-U ctU2) (fst (snd (snd ev))))
               (EqValTy2-headred-contract (LPiCode f') hr1 hr2 (conv-Ty-from-U ctU1) (conv-Ty-from-U ctU2) (snd (snd (snd ev))))))
    EqVal2-headred-contract u LevTy hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract u (LevEl k) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract LevTy (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LevEl k) (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LPiCode f') (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract Bot (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (UCode lu) (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract LevTy (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LevEl k) (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (PiCode a' f') (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (LPiCode f') (LPiCode f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (FunEl g) (LPiCode f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValLPi2-headred-contract g f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValLPi2-headred-contract g f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValLPi2-headred-contract g f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))

------------------------------------------------------------------------
-- Public (canonical-level) wrappers.  Transport is code-fixed, so input
-- and output share the canonical level suc (max (RANK u) (RANK a)); no
-- shift is needed.
------------------------------------------------------------------------

Val2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
  (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-headred-contract u a hr cv val =
  HeadRedPack.Val2-headred-contract (goodStageHeadRed (suc (max (RANK u) (RANK a)))) u a hr cv val

EqVal2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
  (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
  ConvTm G M1 M1' T -> ConvTm G M2 M2' T ->
  EqVal2 G M1 M2 T u a -> EqVal2 G M1' M2' T u a
EqVal2-headred-contract u a hr1 hr2 cv1 cv2 ev =
  HeadRedPack.EqVal2-headred-contract (goodStageHeadRed (suc (max (RANK u) (RANK a)))) u a hr1 hr2 cv1 cv2 ev

EqVal2-headred-expand : {m : Nat} {G : Ctx m} {M M' N N' T : Expr m}
  (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
  ConvTm G M' M T -> ConvTm G N' N T ->
  EqVal2 G M N T u a -> EqVal2 G M' N' T u a
EqVal2-headred-expand u a hr1 hr2 cv1 cv2 ev =
  HeadRedPack.EqVal2-headred-expand (goodStageHeadRed (suc (max (RANK u) (RANK a)))) u a hr1 hr2 cv1 cv2 ev

ValTy2-headred-expand : {m : Nat} {G : Ctx m} {M M' : Expr m}
  (u : FinEl) -> HeadRed M' M -> ConvTy G M' M -> ValTy2 G M u -> ValTy2 G M' u
ValTy2-headred-expand u hr cv vt =
  HeadRedPack.ValTy2-headred-expand (goodStageHeadRed (suc (RANK u))) u hr cv vt

EqValTy2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
  (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 -> ConvTy G M1' M1 -> ConvTy G M2' M2 ->
  EqValTy2 G M1 M2 u -> EqValTy2 G M1' M2' u
EqValTy2-headred-expand u hr1 hr2 cv1 cv2 ev =
  HeadRedPack.EqValTy2-headred-expand (goodStageHeadRed (suc (RANK u))) u hr1 hr2 cv1 cv2 ev
