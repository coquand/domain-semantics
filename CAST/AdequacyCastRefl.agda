{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.AdequacyCastRefl.agda
--
-- CastReflPack: a coercion between VALIDITY-equal types is the identity,
--   cast A B q M  ~  M  : B    (EqVal2),  given EqValTy2 A B and  M : A.
-- (The proof q is irrelevant: A=B at the validity level already makes the
--  coercion the identity, so this covers conv-cast-refl as the q=refl case.)
--
-- Proven by stage induction, reusing goodStageCast.castVal for the cast's
-- own RValPi; only REqValPi.appEV (the coe relating cast to M) is new, and
-- its Pi-edge recursion lands at the predecessor stage on the smaller
-- domain/codomain types -- exactly like cast-fun-Pi's appV.
--
-- 0 postulates.
------------------------------------------------------------------------

module CAST.AdequacyCastRefl where

open import CAST.ValidityMono
open import CAST.ValidityStratified using (Red3 ; mkRed3 ; red3-conv ;
  Red3-trans ; Red3-ct ; Red3-hr)
open import CAST.ValidityProps using (goodStageBeta ; BetaPack ;
  ReflPack ; goodStageRefl ; SymTransPack ; goodStageSymTrans ;
  TransportPack ; goodStageTransport ; FwdPack ; goodStageFwd)
open import CAST.AdequacyCast using (CastPack ; goodStageCast)
open import CAST.ValidityHeadRed using (HeadRedPack ; goodStageHeadRed)
import CAST.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun)
open import CAST.RawSyntax using (Expr ; U ; Pi ; App ; Id ; cast ; sym ; pi1 ; pi2 ; subst1)
open import CAST.TypingRules using (Ctx ; extend ; HasType ; ConvTm ;
  ty-U ; ty-Pi ; ty-App ; ty-cast ; ty-Id ; ty-refl ; ty-sym ; ty-pi1 ; ty-pi2 ; ty-conv ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Id ; conv-cast-refl ; conv-cast-cong ;
  conv-App-fun ; conv-cast-Pi)
open import CAST.Reduction using (HeadRed ; HeadRed1 ; headred-refl ; headred-step ; HeadRed-trans ;
  HeadRed-App ; HeadRed-cast-src ; HeadRed-cast-tgt ; HeadRed-cast-tgt-U ; headred-cast-U ;
  headred-cast-src ; headred-cast-tgt ; headred-cast-tgt-U ; headred-cast-Pi)
open import CAST.SubstitutionLemma using (typing-ConvTm ; typing-WfCtx ; subst-HasType ; subst1-WtSub)
open import CAST.Selection using (Selection ; selectionBelow ; Selection-le-EvalFun ;
  Coherent-Selection ; Coherent-Selection-val ;
  FinMem-Selection ; FinMem-Selection-codomain ; FinMemAllU-Selection)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; LeFunCode ;
  FinMem ; Coherent ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ;
  cft-from-cf ; coh-from-aU ; FinMem-coh-u ; FinMem-a-in-U ; finMem-upward ;
  EvalFun ; Coherent-EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; EvalFun-in-UCode ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft)

------------------------------------------------------------------------
-- CastReflPack: cast-is-identity at Stage k.
------------------------------------------------------------------------

le-UCode-eq : (v : FinEl) -> LeCode UCode v -> Eq v UCode
le-UCode-eq Bot ()
le-UCode-eq UCode le = refl
le-UCode-eq (FunEl _) ()
le-UCode-eq (PiCode _ _) ()
le-UCode-eq (IdCode _ _) ()

finMem-UCode-eq : (c : FinEl) -> FinMem UCode c -> Eq c UCode
finMem-UCode-eq Bot ()
finMem-UCode-eq UCode fm = refl
finMem-UCode-eq (FunEl _) ()
finMem-UCode-eq (PiCode _ _) ()
finMem-UCode-eq (IdCode _ _) ()

-- a type-code (PiCode) lives only in UCode
finMem-pi-UCode : (b1 : FinEl) (g1 : FinFun) (c : FinEl) -> FinMem (PiCode b1 g1) c -> Eq c UCode
finMem-pi-UCode b1 g1 Bot ()
finMem-pi-UCode b1 g1 UCode fm = refl
finMem-pi-UCode b1 g1 (FunEl _) ()
finMem-pi-UCode b1 g1 (PiCode _ _) ()
finMem-pi-UCode b1 g1 (IdCode _ _) ()

record CastReflPack (k : Nat) : Set1 where
  field
    -- cast between validity-equal types is the identity.  Source code c, result
    -- code a, with c <= a (holds in the Pi-edge recursion: EvalFun f ua <= EvalFun f u0).
    castId : {n : Nat} {G : Ctx n} (A B q M : Expr n) (u v c a : FinEl) ->
      LeCode u v -> LeCode c a -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G A U -> HasType G B U -> HasType G q (Id A B) -> HasType G M A ->
      EVTy k G A B c -> VTy k G B a -> Vl k G M A v c ->
      EVl k G (cast A B q M) M B u a

goodStageCastRefl : (k : Nat) -> CastReflPack k
goodStageCastRefl zero = record
  { castId = \ A B q M u v c a _ _ _ _ _ _ _ _ _ _ _ _ -> tt }
goodStageCastRefl (suc n) = record { castId = CId }
  where
    ihR : CastReflPack n
    ihR = goodStageCastRefl n

    open SR n

    -- shared head-expansion for the type-code-UCode cases: A,B -> U so
    -- cast A B q M -->* M is a genuine head reduction.
    idCastUCode : {m : Nat} {G : Ctx m} (A B q M : Expr m) (u v c : FinEl) ->
      LeCode u v -> LeCode c UCode -> FinMem u UCode -> FinMem v c ->
      HasType G A U -> HasType G B U -> HasType G q (Id A B) -> HasType G M A ->
      EVTy (suc n) G A B UCode -> Vl (suc n) G M A v c ->
      EVl (suc n) G (cast A B q M) M B u UCode
    idCastUCode {G = G} A B q M u v c le lec fmu fmv dA dB dq dM eqAB vlM =
      HeadRedPack.EqVal2-headred-expand (goodStageHeadRed (suc n)) u UCode
        hr headred-refl cv (conv-refl dMB) diag
      where
        rA = fst eqAB ; rB = snd eqAB
        convAB = conv-trans (Red3-ct rA) (conv-sym (Red3-ct rB))
        dMB = ty-conv dM convAB dB
        drefl = ty-conv (ty-refl dA) (conv-Id dA dA dA dB (conv-refl dA) convAB) (ty-Id dA dB)
        cv = conv-trans
               (conv-cast-cong dA dB dq dM dA dB drefl dM (conv-refl dA) (conv-refl dB) (conv-refl dM))
               (conv-cast-refl dA dB dM convAB)
        hr = HeadRed-trans (HeadRed-cast-src (Red3-hr rA))
               (HeadRed-trans (HeadRed-cast-tgt-U (Red3-hr rB))
                              (headred-step headred-cast-U headred-refl))
        ccoh = coh-from-aU c (FinMem-a-in-U v c fmv)
        fmv-U = finMem-upward v c UCode lec ccoh tt fmv tt
        vlM-U = MonoPack.upVal2 (goodStage (suc n)) G M A v c UCode lec fmv fmv-U ccoh tt vlM rA
        vlM-B-v = TransportPack.Val2-type-transport (goodStageTransport (suc n)) v UCode eqAB vlM-U
        vlM-B-u = MonoPack.restrictVal2 (goodStage (suc n)) G M B v u UCode le fmu fmv-U vlM-B-v
        diag = ReflPack.Val2-to-EqVal2 (goodStageRefl (suc n)) u UCode vlM-B-u

    CId : {m : Nat} {G : Ctx m} (A B q M : Expr m) (u v c a : FinEl) ->
      LeCode u v -> LeCode c a -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G A U -> HasType G B U -> HasType G q (Id A B) -> HasType G M A ->
      EVTy (suc n) G A B c -> VTy (suc n) G B a -> Vl (suc n) G M A v c ->
      EVl (suc n) G (cast A B q M) M B u a
    -- trivial type-codes
    CId A B q M u v c Bot          le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M u v c (FunEl _)    le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M u v c (IdCode _ _) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    -- type-code UCode: informative for value UCode / PiCode (then c = UCode)
    CId A B q M Bot          v c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M (FunEl _)    v c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M (IdCode _ _) v c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId {G = G} A B q M UCode v c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM =
      idCastUCode A B q M UCode v c le lec fmu fmv dA dB dq dM
        (Eq-transport (\ x -> EVTy (suc n) G A B x) (finMem-UCode-eq c (Eq-transport (\ y -> FinMem y c) (le-UCode-eq v le) fmv)) eqAB) vlM
    CId {G = G} A B q M (PiCode a' f') Bot          c UCode () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId {G = G} A B q M (PiCode a' f') UCode        c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM =
      idCastUCode A B q M (PiCode a' f') UCode c le lec fmu fmv dA dB dq dM
        (Eq-transport (\ x -> EVTy (suc n) G A B x) (finMem-UCode-eq c fmv) eqAB) vlM
    CId {G = G} A B q M (PiCode a' f') (FunEl _)    c UCode () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId {G = G} A B q M (PiCode a' f') (PiCode b1 g1) c UCode le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM =
      idCastUCode A B q M (PiCode a' f') (PiCode b1 g1) c le lec fmu fmv dA dB dq dM
        (Eq-transport (\ x -> EVTy (suc n) G A B x) (finMem-pi-UCode b1 g1 c fmv) eqAB) vlM
    CId {G = G} A B q M (PiCode a' f') (IdCode _ _) c UCode () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    -- type-code PiCode: informative for value FunEl
    CId A B q M Bot          v c (PiCode b f) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M UCode        v c (PiCode b f) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M (PiCode _ _) v c (PiCode b f) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M (IdCode _ _) v c (PiCode b f) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM = tt
    CId A B q M (FunEl g) Bot          c (PiCode b f) () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) UCode        c (PiCode b f) () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (PiCode _ _) c (PiCode b f) () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (IdCode _ _) c (PiCode b f) () lec fmu fmv cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (FunEl gv) Bot          (PiCode b f) le lec fmu () cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (FunEl gv) UCode        (PiCode b f) le lec fmu () cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (FunEl gv) (FunEl _)    (PiCode b f) le lec fmu () cv dA dB dq dM eqAB vtBa vlM
    CId A B q M (FunEl g) (FunEl gv) (IdCode _ _) (PiCode b f) le lec fmu () cv dA dB dq dM eqAB vtBa vlM
    CId {G = G} A B q M (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b f) le lec fmu fmv cv dA dB dq dM eqAB vtBa vlM =
      mkSigma vtBa (mkSigma (snd castvl) (mkSigma (snd vlM-B-g) reqpi))
      where
        vtAc = fst eqAB
        vtBc = fst (snd eqAB)
        reqABc = snd (snd eqAB)
        cU = FinMem-a-in-U (FunEl gv) (PiCode bc fc) fmv
        aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
        ccoh = coh-from-aU (PiCode bc fc) cU
        acoh = coh-from-aU (PiCode b f) aU
        castvl = CastPack.castVal (goodStageCast (suc n)) A B q M (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b f)
                   le fmu fmv cv dA dB dq dM vtAc vtBa vlM
        vlM-Bc = TransportPack.Val2-type-transport (goodStageTransport (suc n)) (FunEl gv) (PiCode bc fc) eqAB vlM
        fmv-a  = finMem-upward (FunEl gv) (PiCode bc fc) (PiCode b f) lec ccoh acoh fmv aU
        vlM-Ba = MonoPack.upVal2 (goodStage (suc n)) G M B (FunEl gv) (PiCode bc fc) (PiCode b f) lec fmv fmv-a ccoh acoh vlM-Bc vtBa
        vlM-B-g = MonoPack.restrictVal2 (goodStage (suc n)) G M B (FunEl gv) (FunEl g) (PiCode b f) le fmu fmv-a vlM-Ba
        C0 = RValTyPi.domA vtBa ; D0 = RValTyPi.codB vtBa
        A1 = RValTyPi.domA vtAc ; A2 = RValTyPi.codB vtAc
        htA1 = RValTyPi.htA vtAc ; htA2 = RValTyPi.htB vtAc
        htC0 = RValTyPi.htA vtBa ; htD0 = RValTyPi.htB vtBa
        cAPi = Red3-ct (RValTyPi.red vtAc) ; cBPi = Red3-ct (RValTyPi.red vtBa)
        htPiAB = ty-Pi htA1 htA2 ; htPiCD = ty-Pi htC0 htD0
        qPi = ty-conv dq (conv-Id dA dB htPiAB htPiCD cAPi cBPi) (ty-Id htPiAB htPiCD)
        htP-Pi = ty-conv dM cAPi htPiAB
        pi1symq = ty-pi1 htC0 htD0 htA1 htA2 (ty-sym htPiAB htPiCD qPi)
        cccong = conv-cast-cong dA dB dq dM htPiAB htPiCD qPi htP-Pi cAPi cBPi (conv-refl dM)
        cccongPi = conv-conv cccong cBPi htPiCD
        rvalpiCast = snd castvl
        vlMpi = snd vlM   -- RValPi M A gv bc fc  (M's NATURAL codes)
        uniqM = Red3-unique-Pi (RValTyPi.red vtAc) (RValPi.red vlMpi)
        M-appV : PiAppVal2 G M A1 A2 bc fc gv
        M-appV = Eq-transport (\ Y -> PiAppVal2 G M A1 Y bc fc gv) (Eq-sym (snd uniqM))
                   (Eq-transport (\ X -> PiAppVal2 G M X (RValPi.codB0 vlMpi) bc fc gv) (Eq-sym (fst uniqM)) (RValPi.appV vlMpi))
        M-appE : PiAppEq2 G M A1 A2 bc fc gv
        M-appE = Eq-transport (\ Y -> PiAppEq2 G M A1 Y bc fc gv) (Eq-sym (snd uniqM))
                   (Eq-transport (\ X -> PiAppEq2 G M X (RValPi.codB0 vlMpi) bc fc gv) (Eq-sym (fst uniqM)) (RValPi.appE vlMpi))
        -- domain equality C0 ~ A1 at code b (B's domain) vs bc (A's): from reqABc (at c) -- A1,C0 at code bc
        uniqAd = Red3-unique-Pi (RValTyPi.red vtAc) (REqValTyPi.redM reqABc)
        uniqBd = Red3-unique-Pi (RValTyPi.red vtBc) (REqValTyPi.redN reqABc)
        bcU = finMem-piU-dom bc fc cU ; cbc = coh-from-aU bc bcU
        bU  = finMem-piU-dom b f aU  ; cb  = coh-from-aU b bU
        eqA1C0c : EVTy n G A1 (RValTyPi.domA vtBc) bc
        eqA1C0c = Eq-transport (\ Y -> EVTy n G A1 Y bc) (Eq-sym (fst uniqBd))
                    (Eq-transport (\ X -> EVTy n G X (REqValTyPi.domA' reqABc) bc) (Eq-sym (fst uniqAd)) (REqValTyPi.eqA reqABc))
        convA1C0c : ConvTm G A1 (RValTyPi.domA vtBc) U
        convA1C0c = Eq-transport (\ Y -> ConvTm G A1 Y U) (Eq-sym (fst uniqBd))
                      (Eq-transport (\ X -> ConvTm G X (REqValTyPi.domA' reqABc) U) (Eq-sym (fst uniqAd)) (REqValTyPi.convA reqABc))
        reqpi : REqValPi G (cast A B q M) M B g b f
        reqpi = record
          { domA0 = C0 ; codB0 = D0 ; red = RValTyPi.red vtBa
          ; cohG = finMem-funel-coh g b f fmu ; fmG = finMem-funel-fun g b f fmu
          ; appEV = appEV }
          where
            appEV : PiAppEqVal2 G (cast A B q M) M C0 D0 b f g
            appEV u0 v0 selg Q htQ valQ =
              EqVal2-trans v0 (EvalFun f u0) cv0 cef
                (EqVal2-sym v0 (EvalFun f u0) cv0 cef betaA)
                (EqVal2-trans v0 (EvalFun f u0) cv0 cef eqR-MQ' eqMQ'-MQ)
              where
                EqVal2-trans   = SymTransPack.EqVal2-trans (goodStageSymTrans n)
                EqVal2-sym     = SymTransPack.EqVal2-sym (goodStageSymTrans n)
                EqValTy2-trans = SymTransPack.EqValTy2-trans (goodStageSymTrans n)

                wfH = typing-WfCtx dA

                -- code data for the two graphs g (cast side) and gv (M side)
                fmFun-g  = finMem-funel-fun g b f fmu
                cf-g     = finMem-funel-coh g b f fmu
                ctg-g    = cft-from-cf g cf-g
                fmFun-gv = finMem-funel-fun gv bc fc fmv
                cf-gv    = finMem-funel-coh gv bc fc fmv
                ctg-gv   = cft-from-cf gv cf-gv
                cft-fc   = RValTyPi.cohF vtAc
                allU-fc  = RValTyPi.fmAllU vtAc
                cft-f    = RValTyPi.cohF vtBa
                allU-f   = RValTyPi.fmAllU vtBa

                -- selection of the cast-side argument and the back-cast Qp : A1
                coh-u0   = Coherent-Selection selg ctg-g
                fmu0-b   = FinMem-Selection b f selg fmFun-g ctg-g cb bU
                sbgv     = selectionBelow gv u0 ctg-gv coh-u0
                ua       = fst sbgv
                vP       = fst (snd sbgv)
                selgv    = fst (snd (snd sbgv))
                le-ua-u0 = fst (snd (snd (snd sbgv)))
                eq-vP    = snd (snd (snd (snd sbgv)))
                coh-ua   = Coherent-Selection selgv ctg-gv
                fmua-bc  = FinMem-Selection bc fc selgv fmFun-gv ctg-gv cbc bcU

                -- codomain codes / coherences
                coh-EFfcua = Coherent-EvalFun fc ua cft-fc coh-ua
                cef        = Coherent-EvalFun f u0 cft-f coh-u0
                fmv0       = FinMem-Selection-codomain b f selg fmFun-g ctg-g cft-f allU-f
                fmvP       = FinMem-Selection-codomain bc fc selgv fmFun-gv ctg-gv cft-fc allU-fc
                coh-vP     = Coherent-Selection-val selgv ctg-gv
                cv0        = FinMem-coh-u v0 (EvalFun f u0) fmv0
                le-v0-vP   = Eq-transport (LeCode v0) eq-vP
                               (Selection-le-EvalFun gv selg le ctg-g ctg-gv coh-u0)
                -- EvalFun fc ua <= EvalFun f u0  (codomain graph fc<=f, arg ua<=u0)
                le-EFfcua-EFfu0 : LeCode (EvalFun fc ua) (EvalFun f u0)
                le-EFfcua-EFfu0 = LeCode-trans (EvalFun fc ua) (EvalFun fc u0) (EvalFun f u0)
                                    coh-EFfcua (Coherent-EvalFun fc u0 cft-fc coh-u0) cef
                                    (EvalFun-mon-arg fc ua u0 le-ua-u0 cft-fc coh-ua coh-u0)
                                    (EvalFun-mon fc f u0 cft-fc cft-f coh-u0 (snd lec))
                fmvP-EFfu0 = finMem-upward vP (EvalFun fc ua) (EvalFun f u0) le-EFfcua-EFfu0
                               coh-EFfcua cef fmvP (EvalFun-in-UCode f u0 b cft-f coh-u0 allU-f)

                -- the back-cast Qp = cast C0 A1 (pi1 (sym q)) Q : A1, and its value
                Qp   = cast C0 A1 (pi1 (sym q)) Q
                htQp = ty-cast htC0 htA1 pi1symq htQ
                fmua-b = finMem-upward ua bc b (fst lec) cbc cb fmua-bc bU
                valQ-ua-b = MonoPack.restrictVal2 (goodStage n) G Q C0 u0 ua b
                              le-ua-u0 fmua-b fmu0-b valQ
                valQ-at-bc = MonoPack.downVal2 (goodStage n) G Q C0 ua bc b
                               (fst lec) fmua-bc cbc bU valQ-ua-b
                valQp-A1 = CastPack.castVal (goodStageCast n) C0 A1 (pi1 (sym q)) Q ua u0 b bc
                             le-ua-u0 fmua-bc fmu0-b coh-u0
                             htC0 htA1 pi1symq htQ
                             (RValTyPi.valA vtBa) (RValTyPi.valA vtAc) valQ

                -- domain type equality  C0 ~ A1  (from eqA1C0c / convA1C0c, aligned)
                uniqBac  = Red3-unique-Pi (RValTyPi.red vtBa) (RValTyPi.red vtBc)
                eqA1C0'  : EVTy n G A1 C0 bc
                eqA1C0'  = Eq-transport (\ X -> EVTy n G A1 X bc) (Eq-sym (fst uniqBac)) eqA1C0c
                eqC0A1   : EVTy n G C0 A1 bc
                eqC0A1   = FwdPack.EqValTy2-sym (goodStageFwd n) bc cbc eqA1C0'
                convA1C0' : ConvTm G A1 C0 U
                convA1C0' = Eq-transport (\ X -> ConvTm G A1 X U) (Eq-sym (fst uniqBac)) convA1C0c
                convC0A1  : ConvTm G C0 A1 U
                convC0A1  = conv-sym convA1C0'

                -- Qp ~ Q : A1  (proof swapped to refl, then conv-cast-refl)
                drefl-CA = ty-conv (ty-refl htC0)
                             (conv-Id htC0 htC0 htC0 htA1 (conv-refl htC0) convC0A1)
                             (ty-Id htC0 htA1)
                cvQ'Q : ConvTm G Qp Q A1
                cvQ'Q = conv-trans
                          (conv-cast-cong htC0 htA1 pi1symq htQ htC0 htA1 drefl-CA htQ
                            (conv-refl htC0) (conv-refl htA1) (conv-refl htQ))
                          (conv-cast-refl htC0 htA1 htQ convC0A1)
                eqQ'Q : EVl n G Qp Q A1 ua bc
                eqQ'Q = CastReflPack.castId ihR C0 A1 (pi1 (sym q)) Q ua ua bc bc
                          (LeCode-refl ua coh-ua) (LeCode-refl bc cbc)
                          fmua-bc fmua-bc coh-ua
                          htC0 htA1 pi1symq htQ
                          eqC0A1 (RValTyPi.valA vtAc) valQ-at-bc
                valQ-A1 = MonoPack.Val2-from-EqVal2-second (goodStage n) ua bc eqQ'Q
                htQ-A1  = ty-conv htQ convC0A1 htA1

                -- codomain target type value  VTy (subst1 D0 Q) (EvalFun f u0)
                sbf'     = selectionBelow f u0 cft-f coh-u0
                wf2      = fst sbf'
                vvf2     = fst (snd sbf')
                self'    = fst (snd (snd sbf'))
                le-wf2   = fst (snd (snd (snd sbf')))
                eq-f'    = snd (snd (snd (snd sbf')))
                fmwf2-b  = FinMemAllU-Selection b self' allU-f cft-f cb bU
                valQ-wf2 = MonoPack.restrictVal2 (goodStage n) G Q C0 u0 wf2 b
                             le-wf2 fmwf2-b fmu0-b valQ
                vtTgt : VTy n G (subst1 D0 Q) (EvalFun f u0)
                vtTgt = Eq-transport (\ x -> VTy n G (subst1 D0 Q) x) (Eq-sym eq-f')
                          (RValTyPi.edgeV vtBa wf2 vvf2 self' Q htQ valQ-wf2)

                -- source type equality  subst1 A2 Qp ~ subst1 D0 Q  (EvalFun fc ua)
                sbfc     = selectionBelow fc ua cft-fc coh-ua
                wf1      = fst sbfc
                vvf1     = fst (snd sbfc)
                selfc    = fst (snd (snd sbfc))
                le-wf1   = fst (snd (snd (snd sbfc)))
                eq-fc    = snd (snd (snd (snd sbfc)))
                fmwf1-bc = FinMemAllU-Selection bc selfc allU-fc cft-fc cbc bcU
                eqQ'Q-wf1   = MonoPack.restrictEqVal2 (goodStage n) G Qp Q A1 ua wf1 bc
                                le-wf1 fmwf1-bc fmua-bc eqQ'Q
                valQ-A1-wf1 = MonoPack.restrictVal2 (goodStage n) G Q A1 ua wf1 bc
                                le-wf1 fmwf1-bc fmua-bc valQ-A1
                -- the A2 -> D0 type-equality edge (from reqABc.edgeET, code-aligned)
                edgeET-A2D0 : PiEdgeEqTy2 G A1 A2 D0 bc fc
                edgeET-A2D0 =
                  Eq-transport (\ Z -> PiEdgeEqTy2 G A1 A2 Z bc fc) (Eq-sym (snd uniqBac))
                    (Eq-transport (\ Z -> PiEdgeEqTy2 G A1 A2 Z bc fc) (Eq-sym (snd uniqBd))
                      (Eq-transport (\ Y -> PiEdgeEqTy2 G A1 Y (REqValTyPi.codB' reqABc) bc fc) (Eq-sym (snd uniqAd))
                        (Eq-transport (\ X -> PiEdgeEqTy2 G X (REqValTyPi.codB reqABc) (REqValTyPi.codB' reqABc) bc fc) (Eq-sym (fst uniqAd))
                          (REqValTyPi.edgeET reqABc))))
                eqSrc1 : EVTy n G (subst1 A2 Qp) (subst1 A2 Q) (EvalFun fc ua)
                eqSrc1 = Eq-transport (\ x -> EVTy n G (subst1 A2 Qp) (subst1 A2 Q) x) (Eq-sym eq-fc)
                           (RValTyPi.edgeE vtAc wf1 vvf1 selfc Qp Q htQp htQ-A1 cvQ'Q eqQ'Q-wf1)
                eqSrc2 : EVTy n G (subst1 A2 Q) (subst1 D0 Q) (EvalFun fc ua)
                eqSrc2 = Eq-transport (\ x -> EVTy n G (subst1 A2 Q) (subst1 D0 Q) x) (Eq-sym eq-fc)
                           (edgeET-A2D0 wf1 vvf1 selfc Q htQ-A1 valQ-A1-wf1)
                eqSrc : EVTy n G (subst1 A2 Qp) (subst1 D0 Q) (EvalFun fc ua)
                eqSrc = EqValTy2-trans (EvalFun fc ua) coh-EFfcua eqSrc1 eqSrc2

                -- typings for the codomain coe and its inner value App M Qp
                symq    = ty-sym htPiAB htPiCD qPi
                htSrc'  = subst-HasType (subst1-WtSub htA1 htQp) wfH htA2
                htTgt'  = subst-HasType (subst1-WtSub htC0 htQ) wfH htD0
                pi2symqQ = ty-pi2 htC0 htD0 htA1 htA2 symq htQ
                htQpr'  = ty-sym htTgt' htSrc' pi2symqQ
                htMQp   = ty-App htA1 htA2 htP-Pi htQp
                vlMQp   = M-appV ua vP selgv Qp htQp valQp-A1

                -- eqR-MQ' :  reduct R  ~  App M Qp   (codomain recursion, UP)
                eqR-MQ' : EVl n G (cast (subst1 A2 Qp) (subst1 D0 Q) (sym (pi2 (sym q) Q)) (App M Qp))
                                  (App M Qp) (subst1 D0 Q) v0 (EvalFun f u0)
                eqR-MQ' = CastReflPack.castId ihR (subst1 A2 Qp) (subst1 D0 Q) (sym (pi2 (sym q) Q)) (App M Qp)
                            v0 vP (EvalFun fc ua) (EvalFun f u0)
                            le-v0-vP le-EFfcua-EFfu0 fmv0 fmvP coh-vP
                            htSrc' htTgt' htQpr' htMQp
                            eqSrc vtTgt vlMQp

                -- eqMQ'-MQ :  App M Qp  ~  App M Q   (M.appE, then transport/up/restrict)
                appE-M    = M-appE ua vP selgv Qp Q htQp htQ-A1 cvQ'Q eqQ'Q
                appE-M-D0 = TransportPack.EqVal2-type-transport (goodStageTransport n)
                              vP (EvalFun fc ua) eqSrc appE-M
                appE-M-up = MonoPack.upEqVal2 (goodStage n) G (App M Qp) (App M Q) (subst1 D0 Q)
                              vP (EvalFun fc ua) (EvalFun f u0) le-EFfcua-EFfu0
                              fmvP fmvP-EFfu0 coh-EFfcua cef appE-M-D0 vtTgt
                eqMQ'-MQ : EVl n G (App M Qp) (App M Q) (subst1 D0 Q) v0 (EvalFun f u0)
                eqMQ'-MQ = MonoPack.restrictEqVal2 (goodStage n) G (App M Qp) (App M Q) (subst1 D0 Q)
                             vP v0 (EvalFun f u0) le-v0-vP fmv0 fmvP-EFfu0 appE-M-up

                -- betaA :  reduct R  ~  App (cast A B q M) Q   (head-expansion, cast side)
                hr-app = HeadRed-trans
                           (HeadRed-App (HeadRed-trans (HeadRed-cast-src (Red3-hr (RValTyPi.red vtAc)))
                                                       (HeadRed-cast-tgt (Red3-hr (RValTyPi.red vtBa)))))
                           (headred-step headred-cast-Pi headred-refl)
                cv-app = conv-trans
                           (conv-App-fun htC0 htD0 cccongPi htQ)
                           (conv-cast-Pi htA1 htA2 htC0 htD0 qPi htP-Pi htQ)
                valCast = RValPi.appV rvalpiCast u0 v0 selg Q htQ valQ
                valR    = HeadRedPack.Val2-headred-contract (goodStageHeadRed n)
                            v0 (EvalFun f u0) hr-app cv-app valCast
                betaA   = BetaPack.Val2-beta-expand (goodStageBeta n)
                            v0 (EvalFun f u0) hr-app cv-app valR
