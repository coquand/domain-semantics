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

module CAST.ValidityHeadRed where

open import CAST.ValidityMono
open import CAST.ValidityProps using (BetaPack ; goodStageBeta)
open import CAST.ValidityStratified using (Red3 ; mkRed3 ; Red3-ct ; Red3-trans ;
  Red3-strip-U ; Red3-strip-Pi ; Val2 ; EqVal2)

import CAST.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              max ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun)
open import CAST.RawSyntax using (Expr ; U ; Pi ; App ; subst1)
open import CAST.TypingRules using (Ctx ; extend ; HasType ; ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-App-fun)
open import CAST.Reduction using (HeadRed ; HeadRed1 ; HeadRed1-det ;
  headred-refl ; headred-step ; HeadRed-trans ; HeadRed-App ; HeadRed-strip-Pi)
open import CAST.PaperSemantics using (EvalFun)
open import CAST.SubstitutionLemma using (typing-ConvTm ; typing-type ; subst1-cong-ConvTm)
open import CAST.Rank using (RANK)

------------------------------------------------------------------------
-- HeadRed strip lemma for U (normal form)
------------------------------------------------------------------------

HeadRed1-not-U : {n : Nat} {N : Expr n} -> HeadRed1 U N -> Empty
HeadRed1-not-U ()

HeadRed-strip-U : {n : Nat} {M M' : Expr n} ->
  HeadRed M M' -> HeadRed M U -> HeadRed M' U
HeadRed-strip-U headred-refl hr2 = hr2
HeadRed-strip-U (headred-step s1 hr1) headred-refl with HeadRed1-not-U s1
... | ()
HeadRed-strip-U (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-U hr1
    (S.Eq-transport (\ x -> HeadRed x U) (S.Eq-sym (HeadRed1-det s1 s2)) hr2)

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

goodStageHeadRed : (k : Nat) -> HeadRedPack k
goodStageHeadRed zero = record
  { Val2-headred-contract   = \ u a hr cv val -> tt
  ; EqVal2-headred-contract = \ u a hr1 hr2 cv1 cv2 ev -> tt
  ; EqVal2-headred-expand   = \ u a hr1 hr2 cv1 cv2 ev -> tt
  }
goodStageHeadRed (suc n) = record
  { Val2-headred-contract   = Val2-headred-contract
  ; EqVal2-headred-contract = EqVal2-headred-contract
  ; EqVal2-headred-expand   = EqVal2-headred-expand
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

    -- ValTy2-headred-contract: HeadRed M M', ConvTm G M M' U
    ValTy2-headred-contract : {m : Nat} {G : Ctx m} {M M' : Expr m}
      (u : FinEl) -> HeadRed M M' -> ConvTm G M M' U ->
      VTy (suc n) G M u -> VTy (suc n) G M' u
    ValTy2-headred-contract Bot hr cv vt = tt
    ValTy2-headred-contract UCode hr cv vt = Red3-strip-U hr cv vt
    ValTy2-headred-contract (FunEl g) hr cv vt = tt
    ValTy2-headred-contract (PiCode b f) hr cv vt =
      record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
             ; red = Red3-strip-Pi hr cv (RValTyPi.red vt)
             ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
             ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
             ; valA = RValTyPi.valA vt
             ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }
    ValTy2-headred-contract (IdCode a b) hr cv vt = tt

    -- ValTy2-headred-expand: HeadRed M' M, ConvTm G M' M U
    ValTy2-headred-expand : {m : Nat} {G : Ctx m} {M M' : Expr m}
      (u : FinEl) -> HeadRed M' M -> ConvTm G M' M U ->
      VTy (suc n) G M u -> VTy (suc n) G M' u
    ValTy2-headred-expand Bot hr cv vt = tt
    ValTy2-headred-expand UCode hr cv vt = Red3-trans (mkRed3 hr cv) vt
    ValTy2-headred-expand (FunEl g) hr cv vt = tt
    ValTy2-headred-expand (PiCode b f) hr cv vt =
      record { domA = RValTyPi.domA vt ; codB = RValTyPi.codB vt
             ; red = Red3-trans (mkRed3 hr cv) (RValTyPi.red vt)
             ; cohF = RValTyPi.cohF vt ; fmAllU = RValTyPi.fmAllU vt
             ; htA = RValTyPi.htA vt ; htB = RValTyPi.htB vt
             ; valA = RValTyPi.valA vt
             ; edgeV = RValTyPi.edgeV vt ; edgeE = RValTyPi.edgeE vt }
    ValTy2-headred-expand (IdCode a b) hr cv vt = tt

    -- EqValTy2-headred-contract
    EqValTy2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
      (u : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' U -> ConvTm G M2 M2' U ->
      EVTy (suc n) G M1 M2 u -> EVTy (suc n) G M1' M2' u
    EqValTy2-headred-contract Bot hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-contract UCode hr1 hr2 cv1 cv2 eqvt =
      mkSigma (Red3-strip-U hr1 cv1 (fst eqvt)) (Red3-strip-U hr2 cv2 (snd eqvt))
    EqValTy2-headred-contract (FunEl g) hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-contract (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-contract (PiCode b f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-contract (PiCode b f) hr2 cv2 vt2)
             (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                     ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                     ; redM = Red3-strip-Pi hr1 cv1 (REqValTyPi.redM core)
                     ; redN = Red3-strip-Pi hr2 cv2 (REqValTyPi.redN core)
                     ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                     ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                     ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))
    EqValTy2-headred-contract (IdCode a b) hr1 hr2 cv1 cv2 eqvt = tt

    -- EqValTy2-headred-expand
    EqValTy2-headred-expand : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' : Expr m}
      (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
      ConvTm G M1' M1 U -> ConvTm G M2' M2 U ->
      EVTy (suc n) G M1 M2 u -> EVTy (suc n) G M1' M2' u
    EqValTy2-headred-expand Bot hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-expand UCode hr1 hr2 cv1 cv2 eqvt =
      mkSigma (Red3-trans (mkRed3 hr1 cv1) (fst eqvt)) (Red3-trans (mkRed3 hr2 cv2) (snd eqvt))
    EqValTy2-headred-expand (FunEl g) hr1 hr2 cv1 cv2 tt = tt
    EqValTy2-headred-expand (PiCode b f) hr1 hr2 cv1 cv2 eqvt =
      let vt1 = fst eqvt ; vt2 = fst (snd eqvt) ; core = snd (snd eqvt)
      in mkSigma (ValTy2-headred-expand (PiCode b f) hr1 cv1 vt1)
           (mkSigma (ValTy2-headred-expand (PiCode b f) hr2 cv2 vt2)
             (record { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
                     ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
                     ; redM = Red3-trans (mkRed3 hr1 cv1) (REqValTyPi.redM core)
                     ; redN = Red3-trans (mkRed3 hr2 cv2) (REqValTyPi.redN core)
                     ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
                     ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
                     ; eqA = REqValTyPi.eqA core ; edgeET = REqValTyPi.edgeET core }))
    EqValTy2-headred-expand (IdCode a b) hr1 hr2 cv1 cv2 eqvt = tt

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
          htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                    (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
          htPiU = snd (typing-ConvTm (Red3-ct redT))
          ctPi  = conv-conv cv (Red3-ct redT) htPiU
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
                ; appV = \ u v sel N htN valN ->
                    hrc-n v (EvalFun f u) (HeadRed-App hr)
                      (conv-App-fun htA0 htB0 ctPi htN)
                      (RValPi.appV vpiM u v sel N htN valN)
                ; appE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
                    let cvApp1 = conv-App-fun htA0 htB0 ctPi htN1
                        cvApp2-raw = conv-App-fun htA0 htB0 ctPi htN2
                        cvBN = subst1-cong-ConvTm htA0 htB0 htN1 htN2 cvN
                        htB0N1 = fst (typing-ConvTm cvBN)
                        cvApp2 = conv-conv cvApp2-raw (conv-sym cvBN) htB0N1
                    in ehc-n v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                         cvApp1 cvApp2
                         (RValPi.appE vpiM u v sel N1 N2 htN1 htN2 cvN eqN) }

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
          htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                    (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
          htPiU = snd (typing-ConvTm (Red3-ct redT))
          ctPi1 = conv-conv cv1 (Red3-ct redT) htPiU
          ctPi2 = conv-conv cv2 (Red3-ct redT) htPiU
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
                ; appEV = \ u v sel P htP valP ->
                    ehc-n v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                      (conv-App-fun htA0 htB0 ctPi1 htP) (conv-App-fun htA0 htB0 ctPi2 htP)
                      (REqValPi.appEV epi u v sel P htP valP) }

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
          htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                    (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
          htPiU = snd (typing-ConvTm (Red3-ct redT))
          ctPi  = conv-conv cv (Red3-ct redT) htPiU
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = RValPi.cohG vpiM ; fmG = RValPi.fmG vpiM
                ; appV = \ u v sel N htN valN ->
                    betaExp v (EvalFun f u) (HeadRed-App hr)
                      (conv-App-fun htA0 htB0 ctPi htN)
                      (RValPi.appV vpiM u v sel N htN valN)
                ; appE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
                    let cvApp1 = conv-App-fun htA0 htB0 ctPi htN1
                        cvApp2-raw = conv-App-fun htA0 htB0 ctPi htN2
                        cvBN = subst1-cong-ConvTm htA0 htB0 htN1 htN2 cvN
                        htB0N1 = fst (typing-ConvTm cvBN)
                        cvApp2 = conv-conv cvApp2-raw (conv-sym cvBN) htB0N1
                    in ehe-n v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
                         cvApp1 cvApp2
                         (RValPi.appE vpiM u v sel N1 N2 htN1 htN2 cvN eqN) }

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
          htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniq) (RValTyPi.htA vty)
          htB0  = S.Eq-transport (\ Y -> HasType (extend _ A0) Y _) (snd uniq)
                    (S.Eq-transport (\ X -> HasType (extend _ X) _ _) (fst uniq) (RValTyPi.htB vty))
          htPiU = snd (typing-ConvTm (Red3-ct redT))
          ctPi1 = conv-conv cv1 (Red3-ct redT) htPiU
          ctPi2 = conv-conv cv2 (Red3-ct redT) htPiU
      in record { domA0 = A0 ; codB0 = B0 ; red = redT
                ; cohG = REqValPi.cohG epi ; fmG = REqValPi.fmG epi
                ; appEV = \ u v sel P htP valP ->
                    ehe-n v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
                      (conv-App-fun htA0 htB0 ctPi1 htP) (conv-App-fun htA0 htB0 ctPi2 htP)
                      (REqValPi.appEV epi u v sel P htP valP) }

    -- Val2-headred-contract (entry point at stage suc n)
    Val2-headred-contract : {m : Nat} {G : Ctx m} {M M' T : Expr m}
      (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
      Vl (suc n) G M T u a -> Vl (suc n) G M' T u a
    Val2-headred-contract u Bot hr cv tt = tt
    Val2-headred-contract Bot UCode hr cv tt = tt
    Val2-headred-contract UCode UCode hr cv val =
      let vtA = fst val ; vtM = snd val
          ctU = conv-conv cv (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
      in mkSigma vtA (Red3-strip-U hr ctU vtM)
    Val2-headred-contract (FunEl g) UCode hr cv tt = tt
    Val2-headred-contract (PiCode a' f') UCode hr cv val =
      let vtA = fst val ; vtPi = snd val
          ctU = conv-conv cv (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
      in mkSigma vtA (ValTy2-headred-contract (PiCode a' f') hr ctU vtPi)
    Val2-headred-contract u (FunEl h) hr cv tt = tt
    Val2-headred-contract Bot (PiCode b f) hr cv tt = tt
    Val2-headred-contract UCode (PiCode b f) hr cv tt = tt
    Val2-headred-contract (FunEl g) (PiCode b f) hr cv val =
      mkSigma (fst val) (ValPi2-headred-contract g b f hr cv (fst val) (snd val))
    Val2-headred-contract (PiCode a' f') (PiCode b f) hr cv tt = tt
    Val2-headred-contract (IdCode u u₁) UCode hr cv val = tt
    Val2-headred-contract (IdCode u u₁) (PiCode b f) hr cv val = tt
    Val2-headred-contract u (IdCode a a₁) hr cv val = tt

    -- EqVal2-headred-expand (entry point)
    EqVal2-headred-expand : {m : Nat} {G : Ctx m} {M M' N N' T : Expr m}
      (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
      ConvTm G M' M T -> ConvTm G N' N T ->
      EVl (suc n) G M N T u a -> EVl (suc n) G M' N' T u a
    EqVal2-headred-expand u Bot hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand Bot UCode hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand UCode UCode hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          ctU2 = conv-conv cv2 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
          vtM' = Red3-trans (mkRed3 hr1 ctU1) vtM
          vtN' = Red3-trans (mkRed3 hr2 ctU2) vtN
      in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
    EqVal2-headred-expand (FunEl g) UCode hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (PiCode a' f') UCode hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          ctU2 = conv-conv cv2 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          expand1 = ValTy2-headred-expand (PiCode a' f') hr1 ctU1 (fst (snd ev))
          expand2 = ValTy2-headred-expand (PiCode a' f') hr2 ctU2 (fst (snd (snd ev)))
          eqexpand = EqValTy2-headred-expand (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev)))
      in mkSigma vtA (mkSigma expand1 (mkSigma expand2 eqexpand))
    EqVal2-headred-expand u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand UCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValPi2-headred-expand g b f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValPi2-headred-expand g b f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValPi2-headred-expand g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
    EqVal2-headred-expand (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-expand (IdCode u u₁) UCode hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand (IdCode u u₁) (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-expand u (IdCode a a₁) hr1 hr2 cv1 cv2 ev = tt

    -- EqVal2-headred-contract (entry point)
    EqVal2-headred-contract : {m : Nat} {G : Ctx m} {M1 M2 M1' M2' T : Expr m}
      (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
      ConvTm G M1 M1' T -> ConvTm G M2 M2' T ->
      EVl (suc n) G M1 M2 T u a -> EVl (suc n) G M1' M2' T u a
    EqVal2-headred-contract u Bot hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract Bot UCode hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract UCode UCode hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          ctU2 = conv-conv cv2 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          vtM = fst (snd ev) ; vtN = fst (snd (snd ev))
          vtM' = Red3-strip-U hr1 ctU1 vtM
          vtN' = Red3-strip-U hr2 ctU2 vtN
      in mkSigma vtA (mkSigma vtM' (mkSigma vtN' (mkSigma vtM' vtN')))
    EqVal2-headred-contract (FunEl g) UCode hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (PiCode a' f') UCode hr1 hr2 cv1 cv2 ev =
      let vtA = fst ev
          ctU1 = conv-conv cv1 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
          ctU2 = conv-conv cv2 (Red3-ct vtA) (typing-type (snd (typing-ConvTm (Red3-ct vtA))))
      in mkSigma vtA
           (mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 ctU1 (fst (snd ev)))
             (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 ctU2 (fst (snd (snd ev))))
               (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 ctU1 ctU2 (snd (snd (snd ev))))))
    EqVal2-headred-contract u (FunEl h) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract Bot (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract UCode (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (FunEl g) (PiCode b f) hr1 hr2 cv1 cv2 ev =
      let vty = fst ev
      in mkSigma vty
           (mkSigma (ValPi2-headred-contract g b f hr1 cv1 vty (fst (snd ev)))
             (mkSigma (ValPi2-headred-contract g b f hr2 cv2 vty (fst (snd (snd ev))))
               (EqValPi2-headred-contract g b f hr1 hr2 cv1 cv2 vty (snd (snd (snd ev))))))
    EqVal2-headred-contract (PiCode a' f') (PiCode b f) hr1 hr2 cv1 cv2 tt = tt
    EqVal2-headred-contract (IdCode u u₁) UCode hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract (IdCode u u₁) (PiCode b f) hr1 hr2 cv1 cv2 ev = tt
    EqVal2-headred-contract u (IdCode a a₁) hr1 hr2 cv1 cv2 ev = tt

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
