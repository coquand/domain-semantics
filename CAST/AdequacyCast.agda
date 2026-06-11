{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyCast.agda
--
-- Cast-coercion adequacy as a stage-stratified property, in the same
-- `goodStage`-pack style as MonoPack / BetaPack / HeadRedPack.
--
--   CastPack k  :  given a valid source P at T1 (Vl k at value v : c) and a
--                  valid target type T2 (VTy k at a), the guarded coercion
--                  cast T1 T2 q P is valid at T2 (Vl k at u <= v, u : a).
--
-- goodStageCast : (k) -> CastPack k, by induction on the stage index k.
-- In the (FunEl g, PiCode b' f') case the cast's RValPi.appV
--   (a) casts the argument back to T1's domain via the predecessor pack,
--   (b) applies P (its own appV) to that argument,
--   (c) casts the result forward to T2's codomain via the predecessor pack,
-- both recursive calls landing at stage n, so the induction is structural.
------------------------------------------------------------------------

module CAST.AdequacyCast where

open import CAST.ValidityMono
open import CAST.ValidityStratified using (Red3 ; mkRed3 ; red3-conv ;
  Red3-trans ; Red3-ct ; Red3-hr ; collapse-conv)
open import CAST.ValidityProps using (goodStageBeta ; BetaPack ;
  ReflPack ; goodStageRefl ; SymTransPack ; goodStageSymTrans ;
  TransportPack ; goodStageTransport ; FwdPack ; goodStageFwd)
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
  headred-cast-src ; headred-cast-tgt ; headred-cast-tgt-U ; headred-cast-Pi ; HeadRed1-not-U)
open import CAST.SubstitutionLemma using (typing-ConvTm ; typing-WfCtx ; subst-HasType ; subst1-WtSub)
open import CAST.Selection using (Selection ; selectionBelow ; Selection-le-EvalFun ;
  Coherent-Selection ; Coherent-Selection-val ;
  FinMem-Selection ; FinMem-Selection-codomain ; FinMemAllU-Selection)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; LeFunCode ;
  FinMem ; Coherent ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ;
  cft-from-cf ; coh-from-aU ; FinMem-coh-u ; FinMem-a-in-U ; finMem-upward ;
  EvalFun ; Coherent-EvalFun ; EvalFun-mon-arg ; EvalFun-in-UCode ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft)

------------------------------------------------------------------------
-- CastPack: cast-coercion validity at Stage k
------------------------------------------------------------------------

-- UCode is the top code: a value below/at it, or a type containing it, is UCode.
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

------------------------------------------------------------------------
-- castToP / castUTgToP : the coercion  cast T1 T2 q P  head-reduces to its
-- argument P, as a TYPED reduction Red3 (T1, T2, P all reduce to U).
--
-- The cast collapse  cast U U q P -> P  is UNTYPED (headred-cast-U), so when
-- T1, T2 reduce to U via untyped steps (the only case that actually occurs --
-- Red3-at-U is always a mkRed3 by construction), the result is a plain mkRed3.
-- The red3-collapse branches (a source/target stuck at a non-U cast that is
-- only convertible to U) are dead but must type-check; they route through an
-- outer red3-collapse re-indexed by red3-conv.
------------------------------------------------------------------------

-- target phase:  cast U Tg q P -> P   (Tg reduces to U; source already U).
-- Input type index S is general so a red3-conv (nested-cast bookkeeping) can be
-- stripped; cSU : S conv U re-indexes the carried conversions to U.
castUTgToP : {n : Nat} {G : Ctx n} {Tg q P S : Expr n} ->
  HasType G Tg U -> HasType G q (Id U Tg) -> HasType G P U -> ConvTm G S U U ->
  Red3 G Tg U S -> Red3 G (cast U Tg q P) P Tg
castUTgToP {G = G} {Tg} {q} {P} dTg dq dP cSU (mkRed3 hrTg ctTg) =
  mkRed3 (HeadRed-trans (HeadRed-cast-tgt-U hrTg) (headred-step headred-cast-U headred-refl))
         (collapse-conv (ty-U wf) dTg dq dP (conv-sym cTgU))
  where wf   = typing-WfCtx dTg
        cTgU = conv-conv ctTg cSU (ty-U wf)
castUTgToP {G = G} {Tg} {q} {P} dTg dq dP cSU (red3-conv c r) =
  castUTgToP dTg dq dP (conv-trans c cSU) r

-- full coercion:  cast T1 T2 q P -> P   (T1, T2 reduce to U).  S1 generalises
-- T1's reduction type (so a red3-conv source can be stripped via cS1U).
castToP : {n : Nat} {G : Ctx n} {T1 T2 q P S1 : Expr n} ->
  HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 -> ConvTm G S1 U U ->
  Red3 G T1 U S1 -> Red3 G T2 U U -> Red3 G (cast T1 T2 q P) P T2
castToP {G = G} {T1} {T2} {q} {P} dT1 dT2 dq dP cS1U (mkRed3 hrT1 ctT1) vtT2 =
  Red3-trans (mkRed3 (HeadRed-cast-src hrT1) ctSrc)
             (castUTgToP dT2 dqU dPU (conv-refl (ty-U wf)) vtT2)
  where
    wf = typing-WfCtx dT1
    cT1U : ConvTm G T1 U U
    cT1U = conv-conv ctT1 cS1U (ty-U wf)
    dPU : HasType G P U
    dPU = ty-conv dP cT1U (ty-U wf)
    dqU : HasType G q (Id U T2)
    dqU = ty-conv dq (conv-Id dT1 dT2 (ty-U wf) dT2 cT1U (conv-refl dT2)) (ty-Id (ty-U wf) dT2)
    ctSrc : ConvTm G (cast T1 T2 q P) (cast U T2 q P) T2
    ctSrc = conv-cast-cong dT1 dT2 dq dP (ty-U wf) dT2 dqU dPU cT1U (conv-refl dT2) (conv-refl dP)
castToP {G = G} {T1} {T2} {q} {P} dT1 dT2 dq dP cS1U (red3-conv c r) vtT2 =
  castToP dT1 dT2 dq dP (conv-trans c cS1U) r vtT2

record CastPack (k : Nat) : Set1 where
  field
    castVal : {n : Nat} {G : Ctx n} (T1 T2 q P : Expr n) (u v c a : FinEl) ->
      LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
      VTy k G T1 c -> VTy k G T2 a ->
      Vl k G P T1 v c ->
      Vl k G (cast T1 T2 q P) T2 u a
    -- cast congruence at EqVal: two casts whose source types, target types and
    -- inner terms are pairwise related are themselves related.  The second cast
    -- is "viewed at" the first cast's target type T2 (T2 ~ T2').
    castEqVal : {n : Nat} {G : Ctx n}
      (T1 T2 q P T1' T2' q' P' : Expr n) (u v c a : FinEl) ->
      LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
      HasType G T1' U -> HasType G T2' U -> HasType G q' (Id T1' T2') -> HasType G P' T1' ->
      EVTy k G T1 T1' c -> EVTy k G T2 T2' a ->
      EVl k G P P' T1 v c ->
      EVl k G (cast T1 T2 q P) (cast T1' T2' q' P') T2 u a

------------------------------------------------------------------------
-- goodStageCast : (k) -> CastPack k, by induction on the stage index.
------------------------------------------------------------------------

goodStageCast : (k : Nat) -> CastPack k
goodStageCast zero = record
  { castVal   = \ T1 T2 q P u v c a _ _ _ _ _ _ _ _ _ _ _ -> tt
  ; castEqVal = \ T1 T2 q P T1' T2' q' P' u v c a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> tt }
goodStageCast (suc n) = record { castVal = Cast ; castEqVal = CastEq }
  where
    ihC : CastPack n
    ihC = goodStageCast n

    open SR n

    ------------------------------------------------------------------
    -- coeFull : the coe-Pi construction for ONE cast applied to one
    -- argument, packaged as a record so it can be reused (Cast's appV/appE
    -- keep their own inline copy; CastEq's appEV calls this for M and M').
    ------------------------------------------------------------------
    record CF {m : Nat} (G : Ctx m) (T1 T2 q P : Expr m)
              (g gv : FinFun) (bc : FinEl) (fc : FinFun) (b' : FinEl) (f' : FinFun)
              (u0 v0 : FinEl) (N : Expr m) : Set where
      field
        A0 C0    : Expr m
        B0 D0    : Expr (suc m)
        htA0     : HasType G A0 U
        htB0     : HasType (extend G A0) B0 U
        htC0     : HasType G C0 U
        htD0     : HasType (extend G C0) D0 U
        valA0    : VTy n G A0 bc
        valC0    : VTy n G C0 b'
        edgeEAB  : PiEdgeEq2 G A0 B0 bc fc
        edgeECD  : PiEdgeEq2 G C0 D0 b' f'
        pi1symq  : HasType G (pi1 (sym q)) (Id C0 A0)
        cbc      : Coherent bc
        bcU      : FinMem bc UCode
        cb'      : Coherent b'
        b'U      : FinMem b' UCode
        cftfc    : CoherentFunTail fc
        allUfc   : FinMemAllU fc bc
        cftf'    : CoherentFunTail f'
        allUf'   : FinMemAllU f' b'
        ctgg     : CoherentFunTail g
        ctggv    : CoherentFunTail gv
        fmFung   : FinMemFun g b' f'
        fmFungv  : FinMemFun gv bc fc
        ua vP    : FinEl
        selgv    : Selection gv ua vP
        cohua    : Coherent ua
        fmuabc   : FinMem ua bc
        Npr reduct : Expr m
        valNpr   : Vl n G Npr A0 ua bc
        htNpr    : HasType G Npr A0
        htSrc    : HasType G (subst1 B0 Npr) U
        htTgt    : HasType G (subst1 D0 N) U
        htQpr    : HasType G (sym (pi2 (sym q) N)) (Id (subst1 B0 Npr) (subst1 D0 N))
        htPNpr   : HasType G (App P Npr) (subst1 B0 Npr)
        vlPNpr   : Vl n G (App P Npr) (subst1 B0 Npr) vP (EvalFun fc ua)
        cohu0    : Coherent u0
        fmu0b'   : FinMem u0 b'
        leuau0   : LeCode ua u0
        fmv0     : FinMem v0 (EvalFun f' u0)
        lev0vP   : LeCode v0 vP
        cohvP    : Coherent vP
        fmvP     : FinMem vP (EvalFun fc ua)
        hr       : HeadRed (App (cast T1 T2 q P) N) reduct
        ct       : ConvTm G (App (cast T1 T2 q P) N) reduct (subst1 D0 N)
        reductVal : Vl n G reduct (subst1 D0 N) v0 (EvalFun f' u0)

    coeFull : {m : Nat} {G : Ctx m} (T1 T2 q P : Expr m)
      (g gv : FinFun) (bc : FinEl) (fc : FinFun) (b' : FinEl) (f' : FinFun) ->
      LeCode (FunEl g) (FunEl gv) -> FinMem (FunEl g) (PiCode b' f') -> FinMem (FunEl gv) (PiCode bc fc) ->
      HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
      (vtT1 : RValTyPi G T1 bc fc) (vtT2 : RValTyPi G T2 b' f') (vlPpi : RValPi G P T1 gv bc fc) ->
      (u0 v0 : FinEl) -> Selection g u0 v0 -> (N : Expr m) ->
      HasType G N (RValTyPi.domA vtT2) -> Vl n G N (RValTyPi.domA vtT2) u0 b' ->
      CF G T1 T2 q P g gv bc fc b' f' u0 v0 N
    coeFull {G = G} T1 T2 q P g gv bc fc b' f' le fmu fmv dT1 dT2 dq dP vtT1 vtT2 vlPpi u0 v0 sel N htN valN =
      record
        { A0 = A0 ; C0 = C0 ; B0 = B0 ; D0 = D0
        ; htA0 = htA0 ; htB0 = htB0 ; htC0 = RValTyPi.htA vtT2 ; htD0 = RValTyPi.htB vtT2
        ; valA0 = valA0 ; valC0 = RValTyPi.valA vtT2 ; edgeEAB = edgeE-A0B0 ; edgeECD = RValTyPi.edgeE vtT2
        ; pi1symq = pi1symq ; cbc = cbc ; bcU = bcU ; cb' = cb' ; b'U = b'U
        ; cftfc = cft-fc ; allUfc = allU-fc ; cftf' = cft-f' ; allUf' = allU-f'
        ; ctgg = ctg-g ; ctggv = ctg-gv ; fmFung = fmFun-g ; fmFungv = fmFun-gv
        ; ua = ua ; vP = vP ; selgv = selgv ; cohua = coh-ua ; fmuabc = fmua-bc
        ; cohu0 = coh-u0 ; fmu0b' = fmu0-b' ; leuau0 = le-ua-u0
        ; Npr = Npr ; reduct = reduct ; valNpr = valNpr ; htNpr = htNpr
        ; htSrc = ht-srcBNpr ; htTgt = ht-tgtDN ; htQpr = ht-qpr ; htPNpr = ht-PNpr ; vlPNpr = vlPNpr
        ; fmv0 = fm-v0 ; lev0vP = le-v0-vP ; cohvP = coh-vP ; fmvP = fm-vP
        ; hr = hr-full ; ct = ct-full ; reductVal = reductVal }
      where
        wfH  = typing-WfCtx dT1
        A0 = RValPi.domA0 vlPpi
        B0 = RValPi.codB0 vlPpi
        redT1 = RValPi.red vlPpi
        C0 = RValTyPi.domA vtT2
        D0 = RValTyPi.codB vtT2
        redT2 = RValTyPi.red vtT2
        uniqT1 = Red3-unique-Pi (RValTyPi.red vtT1) redT1
        htA0 : HasType G A0 U
        htA0 = Eq-transport (\ X -> HasType G X U) (fst uniqT1) (RValTyPi.htA vtT1)
        htB0 : HasType (extend G A0) B0 U
        htB0 = Eq-transport (\ Y -> HasType (extend G A0) Y U) (snd uniqT1)
                 (Eq-transport (\ X -> HasType (extend G X) (RValTyPi.codB vtT1) U) (fst uniqT1)
                   (RValTyPi.htB vtT1))
        valA0 : VTy n G A0 bc
        valA0 = Eq-transport (\ X -> VTy n G X bc) (fst uniqT1) (RValTyPi.valA vtT1)
        edgeE-A0B0 : PiEdgeEq2 G A0 B0 bc fc
        edgeE-A0B0 = Eq-transport (\ Y -> PiEdgeEq2 G A0 Y bc fc) (snd uniqT1)
                       (Eq-transport (\ X -> PiEdgeEq2 G X (RValTyPi.codB vtT1) bc fc) (fst uniqT1)
                         (RValTyPi.edgeE vtT1))
        edgeV-A0B0 : PiEdgeVal2 G A0 B0 bc fc
        edgeV-A0B0 = Eq-transport (\ Y -> PiEdgeVal2 G A0 Y bc fc) (snd uniqT1)
                       (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtT1) bc fc) (fst uniqT1)
                         (RValTyPi.edgeV vtT1))
        fmFun-gv = finMem-funel-fun gv bc fc fmv
        cf-gv    = finMem-funel-coh gv bc fc fmv
        ctg-gv   = cft-from-cf gv cf-gv
        piU-gv   = finMem-funel-wf gv bc fc fmv
        bcU      = finMem-piU-dom bc fc piU-gv
        cbc      = coh-from-aU bc bcU
        cft-fc   = RValTyPi.cohF vtT1
        allU-fc  = RValTyPi.fmAllU vtT1
        fmFun-g  = finMem-funel-fun g b' f' fmu
        cf-g     = finMem-funel-coh g b' f' fmu
        ctg-g    = cft-from-cf g cf-g
        piU-g    = finMem-funel-wf g b' f' fmu
        b'U      = finMem-piU-dom b' f' piU-g
        cb'      = coh-from-aU b' b'U
        cft-f'   = RValTyPi.cohF vtT2
        allU-f'  = RValTyPi.fmAllU vtT2
        htPiAB = ty-Pi htA0 htB0
        htPiCD = ty-Pi (RValTyPi.htA vtT2) (RValTyPi.htB vtT2)
        cT1Pi  = Red3-ct redT1
        cT2Pi  = Red3-ct redT2
        qPi    = ty-conv dq (conv-Id dT1 dT2 htPiAB htPiCD cT1Pi cT2Pi) (ty-Id htPiAB htPiCD)
        symq   = ty-sym htPiAB htPiCD qPi
        pi1symq = ty-pi1 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) htA0 htB0 symq
        htP-Pi = ty-conv dP cT1Pi htPiAB
        cccong = conv-cast-cong dT1 dT2 dq dP htPiAB htPiCD qPi htP-Pi cT1Pi cT2Pi (conv-refl dP)
        cccongPi = conv-conv cccong cT2Pi htPiCD

        Npr = cast C0 A0 (pi1 (sym q)) N
        qpr = sym (pi2 (sym q) N)
        reduct = cast (subst1 B0 Npr) (subst1 D0 N) qpr (App P Npr)
        coh-u0 = Coherent-Selection sel ctg-g
        fmu0-b' = FinMem-Selection b' f' sel fmFun-g ctg-g cb' b'U
        sbgv  = selectionBelow gv u0 ctg-gv coh-u0
        ua    = fst sbgv
        vP    = fst (snd sbgv)
        selgv = fst (snd (snd sbgv))
        le-ua-u0 = fst (snd (snd (snd sbgv)))
        eq-vP    = snd (snd (snd (snd sbgv)))
        coh-ua   = Coherent-Selection selgv ctg-gv
        fmua-bc  = FinMem-Selection bc fc selgv fmFun-gv ctg-gv cbc bcU
        htNpr : HasType G Npr A0
        htNpr = ty-cast (RValTyPi.htA vtT2) htA0 pi1symq htN
        ht-srcBNpr = subst-HasType (subst1-WtSub htA0 htNpr) wfH htB0
        ht-tgtDN = subst-HasType (subst1-WtSub (RValTyPi.htA vtT2) htN) wfH (RValTyPi.htB vtT2)
        pi2symqN = ty-pi2 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) htA0 htB0 symq htN
        ht-qpr = ty-sym ht-tgtDN ht-srcBNpr pi2symqN
        ht-PNpr = ty-App htA0 htB0 htP-Pi htNpr
        valNpr : Vl n G Npr A0 ua bc
        valNpr = CastPack.castVal ihC C0 A0 (pi1 (sym q)) N ua u0 b' bc
                   le-ua-u0 fmua-bc fmu0-b' coh-u0
                   (RValTyPi.htA vtT2) htA0 pi1symq htN
                   (RValTyPi.valA vtT2) valA0 valN
        vlPNpr : Vl n G (App P Npr) (subst1 B0 Npr) vP (EvalFun fc ua)
        vlPNpr = RValPi.appV vlPpi ua vP selgv Npr htNpr valNpr
        sbfc   = selectionBelow fc ua cft-fc coh-ua
        w1     = fst sbfc
        vv1    = fst (snd sbfc)
        selfc  = fst (snd (snd sbfc))
        le-w1-ua = fst (snd (snd (snd sbfc)))
        eq-fc    = snd (snd (snd (snd sbfc)))
        fmw1-bc  = FinMemAllU-Selection bc selfc allU-fc cft-fc cbc bcU
        valNpr-w1 = MonoPack.restrictVal2 (goodStage n) G Npr A0 ua w1 bc le-w1-ua fmw1-bc fmua-bc valNpr
        vt-srcBNpr : VTy n G (subst1 B0 Npr) (EvalFun fc ua)
        vt-srcBNpr = Eq-transport (\ x -> VTy n G (subst1 B0 Npr) x) (Eq-sym eq-fc)
                       (edgeV-A0B0 w1 vv1 selfc Npr htNpr valNpr-w1)
        sbf'   = selectionBelow f' u0 cft-f' coh-u0
        w2     = fst sbf'
        vv2    = fst (snd sbf')
        self'  = fst (snd (snd sbf'))
        le-w2-u0 = fst (snd (snd (snd sbf')))
        eq-f'    = snd (snd (snd (snd sbf')))
        fmw2-b'  = FinMemAllU-Selection b' self' allU-f' cft-f' cb' b'U
        valN-w2  = MonoPack.restrictVal2 (goodStage n) G N C0 u0 w2 b' le-w2-u0 fmw2-b' fmu0-b' valN
        vt-tgtDN : VTy n G (subst1 D0 N) (EvalFun f' u0)
        vt-tgtDN = Eq-transport (\ x -> VTy n G (subst1 D0 N) x) (Eq-sym eq-f')
                     (RValTyPi.edgeV vtT2 w2 vv2 self' N htN valN-w2)
        fm-v0 = FinMem-Selection-codomain b' f' sel fmFun-g ctg-g cft-f' allU-f'
        fm-vP = FinMem-Selection-codomain bc fc selgv fmFun-gv ctg-gv cft-fc allU-fc
        coh-vP = Coherent-Selection-val selgv ctg-gv
        le-v0-vP : LeCode v0 vP
        le-v0-vP = Eq-transport (LeCode v0) eq-vP (Selection-le-EvalFun gv sel le ctg-g ctg-gv coh-u0)
        reductVal : Vl n G reduct (subst1 D0 N) v0 (EvalFun f' u0)
        reductVal = CastPack.castVal ihC (subst1 B0 Npr) (subst1 D0 N) qpr (App P Npr)
                      v0 vP (EvalFun fc ua) (EvalFun f' u0)
                      le-v0-vP fm-v0 fm-vP coh-vP ht-srcBNpr ht-tgtDN ht-qpr ht-PNpr
                      vt-srcBNpr vt-tgtDN vlPNpr
        hr-full : HeadRed (App (cast T1 T2 q P) N) reduct
        hr-full = HeadRed-trans
                    (HeadRed-App (HeadRed-trans (HeadRed-cast-src (Red3-hr redT1))
                                                (HeadRed-cast-tgt (Red3-hr redT2))))
                    (headred-step headred-cast-Pi headred-refl)
        ct-full : ConvTm G (App (cast T1 T2 q P) N) reduct (subst1 D0 N)
        ct-full = conv-trans
                    (conv-App-fun (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) cccongPi htN)
                    (conv-cast-Pi htA0 htB0 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) qPi htP-Pi htN)

    Cast : {m : Nat} {G : Ctx m} (T1 T2 q P : Expr m) (u v c a : FinEl) ->
      LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
      VTy (suc n) G T1 c -> VTy (suc n) G T2 a ->
      Vl (suc n) G P T1 v c ->
      Vl (suc n) G (cast T1 T2 q P) T2 u a
    -- trivial target codes: Vl is Top
    Cast T1 T2 q P u v c Bot          le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P u v c (FunEl _)    le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P u v c (IdCode _ _) le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    -- target UCode: informative only when the value is a type-code
    Cast T1 T2 q P Bot          v c UCode le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P (FunEl _)    v c UCode le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P (IdCode _ _) v c UCode le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast {G = G} T1 T2 q P UCode v c UCode le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP =
      mkSigma vtT2 castToU
      where
        eqv = le-UCode-eq v le
        eqc = finMem-UCode-eq c (Eq-transport (\ x -> FinMem x c) eqv fmv)
        vtT1' : Red3 G T1 U U
        vtT1' = Eq-transport (\ x -> VTy (suc n) G T1 x) eqc vtT1
        vlP' : Vl (suc n) G P T1 UCode UCode
        vlP' = Eq-transport (\ x -> Vl (suc n) G P T1 x UCode) eqv
                 (Eq-transport (\ y -> Vl (suc n) G P T1 v y) eqc vlP)
        vtPU : Red3 G P U U
        vtPU = snd vlP'
        wfH = typing-WfCtx dT1
        cT2U = Red3-ct vtT2
        -- cast T1 T2 q P -->* P -->* U, all at type U (re-indexed off T2)
        castToPval : Red3 G (cast T1 T2 q P) P T2
        castToPval = castToP dT1 dT2 dq dP (conv-refl (ty-U wfH)) vtT1' vtT2
        castToU : Red3 G (cast T1 T2 q P) U U
        castToU = red3-conv cT2U
                    (Red3-trans castToPval (red3-conv (conv-sym cT2U) vtPU))
    Cast {G = G} T1 T2 q P (PiCode a' f') (PiCode b1 g1) UCode UCode le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP =
      mkSigma vtT2 newVtPpi
      where
        wfH = typing-WfCtx dT1
        vtPpi : VTy (suc n) G P (PiCode a' f')
        vtPpi = MonoPack.downValTy2 (goodStage (suc n)) G P (PiCode a' f') (PiCode b1 g1)
                  le fmu fmv (snd vlP)
        cT2U = Red3-ct vtT2
        -- cast T1 T2 q P -->* P -->* (Pi domA codB), at type U
        castToPval : Red3 G (cast T1 T2 q P) P T2
        castToPval = castToP dT1 dT2 dq dP (conv-refl (ty-U wfH)) vtT1 vtT2
        newRed : Red3 G (cast T1 T2 q P) (Pi (RValTyPi.domA vtPpi) (RValTyPi.codB vtPpi)) U
        newRed = Red3-trans (red3-conv cT2U castToPval) (RValTyPi.red vtPpi)
        -- only `red` mentions the head term; copy the rest from vtPpi
        newVtPpi : VTy (suc n) G (cast T1 T2 q P) (PiCode a' f')
        newVtPpi = record
          { domA   = RValTyPi.domA vtPpi
          ; codB   = RValTyPi.codB vtPpi
          ; red    = newRed
          ; cohF   = RValTyPi.cohF vtPpi
          ; fmAllU = RValTyPi.fmAllU vtPpi
          ; htA    = RValTyPi.htA vtPpi
          ; htB    = RValTyPi.htB vtPpi
          ; valA   = RValTyPi.valA vtPpi
          ; edgeV  = RValTyPi.edgeV vtPpi
          ; edgeE  = RValTyPi.edgeE vtPpi
          }
    -- target PiCode: informative only when the value is a function
    Cast T1 T2 q P Bot          v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P UCode        v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P (PiCode _ _) v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    Cast T1 T2 q P (IdCode _ _) v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP = tt
    -- value-code v of P forced to FunEl by le : LeCode (FunEl g) v
    Cast T1 T2 q P (FunEl g) Bot          c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) UCode        c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) (PiCode _ _) c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) (IdCode _ _) c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP
    -- type-code c of P forced to PiCode by fmv : FinMem (FunEl gv) c
    Cast T1 T2 q P (FunEl g) (FunEl gv) Bot          (PiCode b' f') le fmu () cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) (FunEl gv) UCode        (PiCode b' f') le fmu () cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) (FunEl gv) (FunEl _)    (PiCode b' f') le fmu () cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast T1 T2 q P (FunEl g) (FunEl gv) (IdCode _ _) (PiCode b' f') le fmu () cv dT1 dT2 dq dP vtT1 vtT2 vlP
    Cast {m} {G = G} T1 T2 q P (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP =
      mkSigma vtT2 (record
        { domA0 = C0
        ; codB0 = D0
        ; red   = RValTyPi.red vtT2
        ; cohG  = finMem-funel-coh g b' f' fmu
        ; fmG   = finMem-funel-fun g b' f' fmu
        ; appV  = appV
        ; appE  = appE })
      where
        wfH  = typing-WfCtx dT1

        ----------------------------------------------------------------
        -- P's RValPi (gv) and the literal Pi forms of T1, T2.
        ----------------------------------------------------------------
        vlPpi : RValPi G P T1 gv bc fc
        vlPpi = snd vlP

        A0 = RValPi.domA0 vlPpi
        B0 = RValPi.codB0 vlPpi
        redT1 : Red3 G T1 (Pi A0 B0) U
        redT1 = RValPi.red vlPpi
        redT2 : Red3 G T2 (Pi (RValTyPi.domA vtT2) (RValTyPi.codB vtT2)) U
        redT2 = RValTyPi.red vtT2
        C0 = RValTyPi.domA vtT2
        D0 = RValTyPi.codB vtT2

        -- T1's domain/codomain typing+edge, transported to (A0, B0).
        uniqT1 = Red3-unique-Pi (RValTyPi.red vtT1) redT1
        htA0 : HasType G A0 U
        htA0 = Eq-transport (\ X -> HasType G X U) (fst uniqT1) (RValTyPi.htA vtT1)
        htB0 : HasType (extend G A0) B0 U
        htB0 = Eq-transport (\ Y -> HasType (extend G A0) Y U) (snd uniqT1)
                 (Eq-transport (\ X -> HasType (extend G X) (RValTyPi.codB vtT1) U) (fst uniqT1)
                   (RValTyPi.htB vtT1))
        valA0 : VTy n G A0 bc
        valA0 = Eq-transport (\ X -> VTy n G X bc) (fst uniqT1) (RValTyPi.valA vtT1)
        edgeV-A0B0 : PiEdgeVal2 G A0 B0 bc fc
        edgeV-A0B0 = Eq-transport (\ Y -> PiEdgeVal2 G A0 Y bc fc) (snd uniqT1)
                       (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtT1) bc fc) (fst uniqT1)
                         (RValTyPi.edgeV vtT1))
        edgeE-A0B0 : PiEdgeEq2 G A0 B0 bc fc
        edgeE-A0B0 = Eq-transport (\ Y -> PiEdgeEq2 G A0 Y bc fc) (snd uniqT1)
                       (Eq-transport (\ X -> PiEdgeEq2 G X (RValTyPi.codB vtT1) bc fc) (fst uniqT1)
                         (RValTyPi.edgeE vtT1))

        ----------------------------------------------------------------
        -- Code data for gv / bc / fc (P side) and g / b' / f' (cast side).
        ----------------------------------------------------------------
        fmFun-gv = finMem-funel-fun gv bc fc fmv
        cf-gv    = finMem-funel-coh gv bc fc fmv
        ctg-gv   = cft-from-cf gv cf-gv
        piU-gv   = finMem-funel-wf gv bc fc fmv
        bcU      = finMem-piU-dom bc fc piU-gv
        cbc      = coh-from-aU bc bcU
        cft-fc   = RValTyPi.cohF vtT1
        allU-fc  = RValTyPi.fmAllU vtT1

        fmFun-g  = finMem-funel-fun g b' f' fmu
        cf-g     = finMem-funel-coh g b' f' fmu
        ctg-g    = cft-from-cf g cf-g
        piU-g    = finMem-funel-wf g b' f' fmu
        b'U      = finMem-piU-dom b' f' piU-g
        cb'      = coh-from-aU b' b'U
        cft-f'   = RValTyPi.cohF vtT2
        allU-f'  = RValTyPi.fmAllU vtT2

        ----------------------------------------------------------------
        -- Shared typings of the literal-Pi cast and its proof.
        ----------------------------------------------------------------
        htPiAB = ty-Pi htA0 htB0
        htPiCD = ty-Pi (RValTyPi.htA vtT2) (RValTyPi.htB vtT2)
        cT1Pi  = Red3-ct redT1                  -- ConvTm G T1 (Pi A0 B0) U
        cT2Pi  = Red3-ct redT2                  -- ConvTm G T2 (Pi C0 D0) U
        qPi    = ty-conv dq (conv-Id dT1 dT2 htPiAB htPiCD cT1Pi cT2Pi) (ty-Id htPiAB htPiCD)
        symq   = ty-sym htPiAB htPiCD qPi       -- HasType G (sym q) (Id (Pi C0 D0) (Pi A0 B0))
        pi1symq = ty-pi1 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) htA0 htB0 symq
        htP-Pi = ty-conv dP cT1Pi htPiAB        -- HasType G P (Pi A0 B0)
        -- cast T1 T2 q P --conv-cast-cong--> cast (Pi A0 B0)(Pi C0 D0) q P : T2, then : Pi C0 D0
        cccong = conv-cast-cong dT1 dT2 dq dP htPiAB htPiCD qPi htP-Pi cT1Pi cT2Pi (conv-refl dP)
        cccongPi = conv-conv cccong cT2Pi htPiCD

        -- Per-argument coe unit: applying the cast to N head-reduces to `reduct`,
        -- whose Vl is built by coercing the argument, applying P, re-casting.
        record Unit (u0 v0 : FinEl) (N : Expr m) : Set where
          field
            ua vP : FinEl
            selgv : Selection gv ua vP
            coh-ua : Coherent ua
            fmua-bc : FinMem ua bc
            Npr : Expr m
            htNpr : HasType G Npr A0
            ht-srcBNpr : HasType G (subst1 B0 Npr) U
            ht-tgtDN : HasType G (subst1 D0 N) U
            ht-qpr : HasType G (sym (pi2 (sym q) N)) (Id (subst1 B0 Npr) (subst1 D0 N))
            ht-PNpr : HasType G (App P Npr) (subst1 B0 Npr)
            vlPNpr : Vl n G (App P Npr) (subst1 B0 Npr) vP (EvalFun fc ua)
            fm-v0 : FinMem v0 (EvalFun f' u0)
            le-v0-vP : LeCode v0 vP
            coh-vP : Coherent vP
            fm-vP : FinMem vP (EvalFun fc ua)
            reduct : Expr m
            hr : HeadRed (App (cast T1 T2 q P) N) reduct
            ct : ConvTm G (App (cast T1 T2 q P) N) reduct (subst1 D0 N)
            reductVal : Vl n G reduct (subst1 D0 N) v0 (EvalFun f' u0)

        unit : (u0 v0 : FinEl) -> Selection g u0 v0 -> (N : Expr m) ->
          HasType G N C0 -> Vl n G N C0 u0 b' -> Unit u0 v0 N
        unit u0 v0 sel N htN valN = record
          { ua = ua ; vP = vP ; selgv = selgv ; coh-ua = coh-ua ; fmua-bc = fmua-bc
          ; Npr = Npr ; htNpr = htNpr ; ht-srcBNpr = ht-srcBNpr ; ht-tgtDN = ht-tgtDN
          ; ht-qpr = ht-qpr ; ht-PNpr = ht-PNpr ; vlPNpr = vlPNpr
          ; fm-v0 = fm-v0 ; le-v0-vP = le-v0-vP ; coh-vP = coh-vP ; fm-vP = fm-vP
          ; reduct = reduct ; hr = hr-full ; ct = ct-full ; reductVal = reductVal }
          where
            Npr = cast C0 A0 (pi1 (sym q)) N
            qpr = sym (pi2 (sym q) N)
            reduct = cast (subst1 B0 Npr) (subst1 D0 N) qpr (App P Npr)

            coh-u0 = Coherent-Selection sel ctg-g
            fmu0-b' = FinMem-Selection b' f' sel fmFun-g ctg-g cb' b'U

            sbgv  = selectionBelow gv u0 ctg-gv coh-u0
            ua    = fst sbgv
            vP    = fst (snd sbgv)
            selgv = fst (snd (snd sbgv))
            le-ua-u0 = fst (snd (snd (snd sbgv)))
            eq-vP    = snd (snd (snd (snd sbgv)))
            coh-ua   = Coherent-Selection selgv ctg-gv
            fmua-bc  = FinMem-Selection bc fc selgv fmFun-gv ctg-gv cbc bcU

            htNpr : HasType G Npr A0
            htNpr = ty-cast (RValTyPi.htA vtT2) htA0 pi1symq htN
            ht-srcBNpr : HasType G (subst1 B0 Npr) U
            ht-srcBNpr = subst-HasType (subst1-WtSub htA0 htNpr) wfH htB0
            ht-tgtDN : HasType G (subst1 D0 N) U
            ht-tgtDN = subst-HasType (subst1-WtSub (RValTyPi.htA vtT2) htN) wfH (RValTyPi.htB vtT2)
            pi2symqN = ty-pi2 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) htA0 htB0 symq htN
            ht-qpr : HasType G qpr (Id (subst1 B0 Npr) (subst1 D0 N))
            ht-qpr = ty-sym ht-tgtDN ht-srcBNpr pi2symqN
            ht-PNpr : HasType G (App P Npr) (subst1 B0 Npr)
            ht-PNpr = ty-App htA0 htB0 htP-Pi htNpr

            valNpr : Vl n G Npr A0 ua bc
            valNpr = CastPack.castVal ihC C0 A0 (pi1 (sym q)) N ua u0 b' bc
                       le-ua-u0 fmua-bc fmu0-b' coh-u0
                       (RValTyPi.htA vtT2) htA0 pi1symq htN
                       (RValTyPi.valA vtT2) valA0 valN
            vlPNpr : Vl n G (App P Npr) (subst1 B0 Npr) vP (EvalFun fc ua)
            vlPNpr = RValPi.appV vlPpi ua vP selgv Npr htNpr valNpr

            sbfc   = selectionBelow fc ua cft-fc coh-ua
            w1     = fst sbfc
            vv1    = fst (snd sbfc)
            selfc  = fst (snd (snd sbfc))
            le-w1-ua = fst (snd (snd (snd sbfc)))
            eq-fc    = snd (snd (snd (snd sbfc)))
            fmw1-bc  = FinMemAllU-Selection bc selfc allU-fc cft-fc cbc bcU
            valNpr-w1 = MonoPack.restrictVal2 (goodStage n) G Npr A0 ua w1 bc
                          le-w1-ua fmw1-bc fmua-bc valNpr
            vt-srcBNpr : VTy n G (subst1 B0 Npr) (EvalFun fc ua)
            vt-srcBNpr = Eq-transport (\ x -> VTy n G (subst1 B0 Npr) x) (Eq-sym eq-fc)
                           (edgeV-A0B0 w1 vv1 selfc Npr htNpr valNpr-w1)

            sbf'   = selectionBelow f' u0 cft-f' coh-u0
            w2     = fst sbf'
            vv2    = fst (snd sbf')
            self'  = fst (snd (snd sbf'))
            le-w2-u0 = fst (snd (snd (snd sbf')))
            eq-f'    = snd (snd (snd (snd sbf')))
            fmw2-b'  = FinMemAllU-Selection b' self' allU-f' cft-f' cb' b'U
            valN-w2  = MonoPack.restrictVal2 (goodStage n) G N C0 u0 w2 b'
                         le-w2-u0 fmw2-b' fmu0-b' valN
            vt-tgtDN : VTy n G (subst1 D0 N) (EvalFun f' u0)
            vt-tgtDN = Eq-transport (\ x -> VTy n G (subst1 D0 N) x) (Eq-sym eq-f')
                         (RValTyPi.edgeV vtT2 w2 vv2 self' N htN valN-w2)

            fm-v0 : FinMem v0 (EvalFun f' u0)
            fm-v0 = FinMem-Selection-codomain b' f' sel fmFun-g ctg-g cft-f' allU-f'
            fm-vP : FinMem vP (EvalFun fc ua)
            fm-vP = FinMem-Selection-codomain bc fc selgv fmFun-gv ctg-gv cft-fc allU-fc
            coh-vP = Coherent-Selection-val selgv ctg-gv
            le-v0-vP : LeCode v0 vP
            le-v0-vP = Eq-transport (LeCode v0) eq-vP
                         (Selection-le-EvalFun gv sel le ctg-g ctg-gv coh-u0)

            reductVal : Vl n G reduct (subst1 D0 N) v0 (EvalFun f' u0)
            reductVal = CastPack.castVal ihC (subst1 B0 Npr) (subst1 D0 N) qpr (App P Npr)
                          v0 vP (EvalFun fc ua) (EvalFun f' u0)
                          le-v0-vP fm-v0 fm-vP coh-vP
                          ht-srcBNpr ht-tgtDN ht-qpr ht-PNpr
                          vt-srcBNpr vt-tgtDN vlPNpr

            hr-full : HeadRed (App (cast T1 T2 q P) N) reduct
            hr-full = HeadRed-trans
                        (HeadRed-App (HeadRed-trans (HeadRed-cast-src (Red3-hr redT1))
                                                    (HeadRed-cast-tgt (Red3-hr redT2))))
                        (headred-step headred-cast-Pi headred-refl)
            ct-full : ConvTm G (App (cast T1 T2 q P) N) reduct (subst1 D0 N)
            ct-full = conv-trans
                        (conv-App-fun (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) cccongPi htN)
                        (conv-cast-Pi htA0 htB0 (RValTyPi.htA vtT2) (RValTyPi.htB vtT2) qPi htP-Pi htN)

        appV : PiAppVal2 G (cast T1 T2 q P) C0 D0 b' f' g
        appV u0 v0 sel N htN valN =
          let U = unit u0 v0 sel N htN valN in
          MonoPack.Val2-from-EqVal2-second (goodStage n) v0 (EvalFun f' u0)
            (BetaPack.Val2-beta-expand (goodStageBeta n) v0 (EvalFun f' u0)
              (Unit.hr U) (Unit.ct U) (Unit.reductVal U))

        appE : PiAppEq2 G (cast T1 T2 q P) C0 D0 b' f' g
        appE u0 v0 sel N1 N2 htN1 htN2 cvN eqN =
          EqVal2-trans v0 (EvalFun f' u0) cv0 cef
            (EqVal2-sym v0 (EvalFun f' u0) cv0 cef betaA)
            (EqVal2-trans v0 (EvalFun f' u0) cv0 cef outerEq betaB)
          where
            EqVal2-trans = SymTransPack.EqVal2-trans (goodStageSymTrans n)
            EqVal2-sym   = SymTransPack.EqVal2-sym (goodStageSymTrans n)
            beta         = BetaPack.Val2-beta-expand (goodStageBeta n)
            U1 = unit u0 v0 sel N1 htN1 (MonoPack.Val2-from-EqVal2-first (goodStage n) u0 b' eqN)
            U2 = unit u0 v0 sel N2 htN2 (MonoPack.Val2-from-EqVal2-second (goodStage n) u0 b' eqN)
            coh-u0  = Coherent-Selection sel ctg-g
            fmu0-b' = FinMem-Selection b' f' sel fmFun-g ctg-g cb' b'U
            cv0 = FinMem-coh-u v0 (EvalFun f' u0) (Unit.fm-v0 U1)
            cef = Coherent-EvalFun f' u0 cft-f' coh-u0
            ua  = Unit.ua U1
            vP  = Unit.vP U1
            coh-ua = Unit.coh-ua U1
            -- selectionBelow gv u0 : reproduce ua <= u0
            sbgv = selectionBelow gv u0 ctg-gv coh-u0
            le-ua-u0 = fst (snd (snd (snd sbgv)))
            cvNpr : ConvTm G (Unit.Npr U1) (Unit.Npr U2) A0
            cvNpr = conv-cast-cong (RValTyPi.htA vtT2) htA0 pi1symq htN1
                      (RValTyPi.htA vtT2) htA0 pi1symq htN2
                      (conv-refl (RValTyPi.htA vtT2)) (conv-refl htA0) cvN
            innerArgEq : EVl n G (Unit.Npr U1) (Unit.Npr U2) A0 ua bc
            innerArgEq = CastPack.castEqVal ihC C0 A0 (pi1 (sym q)) N1 C0 A0 (pi1 (sym q)) N2
                           ua u0 b' bc le-ua-u0 (Unit.fmua-bc U1) fmu0-b' coh-u0
                           (RValTyPi.htA vtT2) htA0 pi1symq htN1
                           (RValTyPi.htA vtT2) htA0 pi1symq htN2
                           (ReflPack.ValTy2-to-EqValTy2 (goodStageRefl n) b' (RValTyPi.valA vtT2))
                           (ReflPack.ValTy2-to-EqValTy2 (goodStageRefl n) bc valA0)
                           eqN
            -- inner value equality via P.appE
            innerValEq : EVl n G (App P (Unit.Npr U1)) (App P (Unit.Npr U2)) (subst1 B0 (Unit.Npr U1)) vP (EvalFun fc ua)
            innerValEq = RValPi.appE vlPpi ua vP (Unit.selgv U1) (Unit.Npr U1) (Unit.Npr U2)
                           (Unit.htNpr U1) (Unit.htNpr U2) cvNpr innerArgEq
            -- source-type equality EVTy (subst1 B0 Npr1)(subst1 B0 Npr2)(EvalFun fc ua)
            sbfc   = selectionBelow fc ua cft-fc coh-ua
            w1     = fst sbfc
            vv1    = fst (snd sbfc)
            selfc  = fst (snd (snd sbfc))
            le-w1-ua = fst (snd (snd (snd sbfc)))
            eq-fc    = snd (snd (snd (snd sbfc)))
            fmw1-bc  = FinMemAllU-Selection bc selfc allU-fc cft-fc cbc bcU
            innerArgEq-w1 = MonoPack.restrictEqVal2 (goodStage n) G (Unit.Npr U1) (Unit.Npr U2) A0 ua w1 bc
                              le-w1-ua fmw1-bc (Unit.fmua-bc U1) innerArgEq
            eqSrc : EVTy n G (subst1 B0 (Unit.Npr U1)) (subst1 B0 (Unit.Npr U2)) (EvalFun fc ua)
            eqSrc = Eq-transport (\ x -> EVTy n G (subst1 B0 (Unit.Npr U1)) (subst1 B0 (Unit.Npr U2)) x) (Eq-sym eq-fc)
                      (edgeE-A0B0 w1 vv1 selfc (Unit.Npr U1) (Unit.Npr U2) (Unit.htNpr U1) (Unit.htNpr U2) cvNpr innerArgEq-w1)
            -- target-type equality EVTy (subst1 D0 N1)(subst1 D0 N2)(EvalFun f' u0)
            sbf'   = selectionBelow f' u0 cft-f' coh-u0
            w2     = fst sbf'
            vv2    = fst (snd sbf')
            self'  = fst (snd (snd sbf'))
            le-w2-u0 = fst (snd (snd (snd sbf')))
            eq-f'    = snd (snd (snd (snd sbf')))
            fmw2-b'  = FinMemAllU-Selection b' self' allU-f' cft-f' cb' b'U
            eqN-w2   = MonoPack.restrictEqVal2 (goodStage n) G N1 N2 C0 u0 w2 b'
                         le-w2-u0 fmw2-b' fmu0-b' eqN
            eqTgt : EVTy n G (subst1 D0 N1) (subst1 D0 N2) (EvalFun f' u0)
            eqTgt = Eq-transport (\ x -> EVTy n G (subst1 D0 N1) (subst1 D0 N2) x) (Eq-sym eq-f')
                      (RValTyPi.edgeE vtT2 w2 vv2 self' N1 N2 htN1 htN2 cvN eqN-w2)
            eqTgt-sym : EVTy n G (subst1 D0 N2) (subst1 D0 N1) (EvalFun f' u0)
            eqTgt-sym = FwdPack.EqValTy2-sym (goodStageFwd n) (EvalFun f' u0) cef eqTgt
            outerEq : EVl n G (Unit.reduct U1) (Unit.reduct U2) (subst1 D0 N1) v0 (EvalFun f' u0)
            outerEq = CastPack.castEqVal ihC
                        (subst1 B0 (Unit.Npr U1)) (subst1 D0 N1) (sym (pi2 (sym q) N1)) (App P (Unit.Npr U1))
                        (subst1 B0 (Unit.Npr U2)) (subst1 D0 N2) (sym (pi2 (sym q) N2)) (App P (Unit.Npr U2))
                        v0 vP (EvalFun fc ua) (EvalFun f' u0)
                        (Unit.le-v0-vP U1) (Unit.fm-v0 U1) (Unit.fm-vP U1) (Unit.coh-vP U1)
                        (Unit.ht-srcBNpr U1) (Unit.ht-tgtDN U1) (Unit.ht-qpr U1) (Unit.ht-PNpr U1)
                        (Unit.ht-srcBNpr U2) (Unit.ht-tgtDN U2) (Unit.ht-qpr U2) (Unit.ht-PNpr U2)
                        eqSrc eqTgt innerValEq
            betaA : EVl n G (Unit.reduct U1) (App (cast T1 T2 q P) N1) (subst1 D0 N1) v0 (EvalFun f' u0)
            betaA = beta v0 (EvalFun f' u0) (Unit.hr U1) (Unit.ct U1) (Unit.reductVal U1)
            betaB-nat : EVl n G (Unit.reduct U2) (App (cast T1 T2 q P) N2) (subst1 D0 N2) v0 (EvalFun f' u0)
            betaB-nat = beta v0 (EvalFun f' u0) (Unit.hr U2) (Unit.ct U2) (Unit.reductVal U2)
            betaB : EVl n G (Unit.reduct U2) (App (cast T1 T2 q P) N2) (subst1 D0 N1) v0 (EvalFun f' u0)
            betaB = TransportPack.EqVal2-type-transport (goodStageTransport n) v0 (EvalFun f' u0) eqTgt-sym betaB-nat

    ------------------------------------------------------------------
    -- CastEq : cast congruence at EqVal, Stage (suc n).  Same case split
    -- as Cast; informative only when the target type-code a is UCode/PiCode.
    ------------------------------------------------------------------
    CastEq : {m : Nat} {G : Ctx m}
      (T1 T2 q P T1' T2' q' P' : Expr m) (u v c a : FinEl) ->
      LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
      HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
      HasType G T1' U -> HasType G T2' U -> HasType G q' (Id T1' T2') -> HasType G P' T1' ->
      EVTy (suc n) G T1 T1' c -> EVTy (suc n) G T2 T2' a ->
      EVl (suc n) G P P' T1 v c ->
      EVl (suc n) G (cast T1 T2 q P) (cast T1' T2' q' P') T2 u a
    -- trivial target codes
    CastEq T1 T2 q P T1' T2' q' P' u v c Bot          le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' u v c (FunEl _)    le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' u v c (IdCode _ _) le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    -- target UCode
    CastEq T1 T2 q P T1' T2' q' P' Bot          v c UCode le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' (FunEl _)    v c UCode le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' (IdCode _ _) v c UCode le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq {G = G} T1 T2 q P T1' T2' q' P' UCode v c UCode le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP =
      mkSigma redT2 (mkSigma castToU-M (mkSigma castToU-M' (mkSigma castToU-M castToU-M')))
      where
        eqv = le-UCode-eq v le
        eqc = finMem-UCode-eq c (Eq-transport (\ x -> FinMem x c) eqv fmv)
        wfH = typing-WfCtx dT1
        redT2 : Red3 G T2 U U
        redT2 = fst eqT2
        redT2'U : Red3 G T2' U U
        redT2'U = snd eqT2
        cT2U  = Red3-ct redT2
        cT2'U = Red3-ct redT2'U
        eqT1' = Eq-transport (\ x -> EVTy (suc n) G T1 T1' x) eqc eqT1
        redT1U  : Red3 G T1 U U
        redT1U  = fst eqT1'
        redT1'U : Red3 G T1' U U
        redT1'U = snd eqT1'
        eqP' = Eq-transport (\ x -> EVl (suc n) G P P' T1 x UCode) eqv
                 (Eq-transport (\ y -> EVl (suc n) G P P' T1 v y) eqc eqP)
        redPU  : Red3 G P U U
        redPU  = fst (snd eqP')
        redP'U : Red3 G P' U U
        redP'U = fst (snd (snd eqP'))
        castToU-M : Red3 G (cast T1 T2 q P) U U
        castToU-M = red3-conv cT2U
                      (Red3-trans (castToP dT1 dT2 dq dP (conv-refl (ty-U wfH)) redT1U redT2)
                                  (red3-conv (conv-sym cT2U) redPU))
        castToU-M' : Red3 G (cast T1' T2' q' P') U U
        castToU-M' = red3-conv cT2'U
                       (Red3-trans (castToP dT1' dT2' dq' dP' (conv-refl (ty-U wfH)) redT1'U redT2'U)
                                   (red3-conv (conv-sym cT2'U) redP'U))
    CastEq {G = G} T1 T2 q P T1' T2' q' P' (PiCode a' f') (PiCode b1 g1) UCode UCode le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP =
      mkSigma redT2 (mkSigma newVtM (mkSigma newVtM' (mkSigma newVtM (mkSigma newVtM' newEqMM'))))
      where
        wfH = typing-WfCtx dT1
        redT2  : Red3 G T2 U U
        redT2  = fst eqT2
        redT2'U : Red3 G T2' U U
        redT2'U = snd eqT2
        cT2U  = Red3-ct redT2
        cT2'U = Red3-ct redT2'U
        redT1U  : Red3 G T1 U U
        redT1U  = fst eqT1
        redT1'U : Red3 G T1' U U
        redT1'U = snd eqT1
        -- P / P' / their equality as RValTyPi / REqValTyPi at (a', f')
        vtP-b1g1   = fst (snd eqP)
        vtP'-b1g1  = fst (snd (snd eqP))
        eqvtPP'-b1g1 = snd (snd (snd eqP))
        vtPpi : VTy (suc n) G P (PiCode a' f')
        vtPpi = MonoPack.downValTy2 (goodStage (suc n)) G P (PiCode a' f') (PiCode b1 g1) le fmu fmv vtP-b1g1
        vtP'pi : VTy (suc n) G P' (PiCode a' f')
        vtP'pi = MonoPack.downValTy2 (goodStage (suc n)) G P' (PiCode a' f') (PiCode b1 g1) le fmu fmv vtP'-b1g1
        eqvtPP' : EVTy (suc n) G P P' (PiCode a' f')
        eqvtPP' = MonoPack.downEqValTy2 (goodStage (suc n)) G P P' (PiCode a' f') (PiCode b1 g1) le fmu fmv eqvtPP'-b1g1
        eqvtPP'R : REqValTyPi G P P' a' f'
        eqvtPP'R = snd (snd eqvtPP')
        -- the cast -->* P reductions
        castToPval-M  = castToP dT1 dT2 dq dP (conv-refl (ty-U wfH)) redT1U redT2
        castToPval-M' = castToP dT1' dT2' dq' dP' (conv-refl (ty-U wfH)) redT1'U redT2'U
        redCM  = red3-conv cT2U  castToPval-M    -- Red3 G (cast T1 T2 q P)  P  U
        redCM' = red3-conv cT2'U castToPval-M'   -- Red3 G (cast T1' T2' q' P') P' U
        newVtM : VTy (suc n) G (cast T1 T2 q P) (PiCode a' f')
        newVtM = record
          { domA = RValTyPi.domA vtPpi ; codB = RValTyPi.codB vtPpi
          ; red = Red3-trans redCM (RValTyPi.red vtPpi)
          ; cohF = RValTyPi.cohF vtPpi ; fmAllU = RValTyPi.fmAllU vtPpi
          ; htA = RValTyPi.htA vtPpi ; htB = RValTyPi.htB vtPpi
          ; valA = RValTyPi.valA vtPpi
          ; edgeV = RValTyPi.edgeV vtPpi ; edgeE = RValTyPi.edgeE vtPpi }
        newVtM' : VTy (suc n) G (cast T1' T2' q' P') (PiCode a' f')
        newVtM' = record
          { domA = RValTyPi.domA vtP'pi ; codB = RValTyPi.codB vtP'pi
          ; red = Red3-trans redCM' (RValTyPi.red vtP'pi)
          ; cohF = RValTyPi.cohF vtP'pi ; fmAllU = RValTyPi.fmAllU vtP'pi
          ; htA = RValTyPi.htA vtP'pi ; htB = RValTyPi.htB vtP'pi
          ; valA = RValTyPi.valA vtP'pi
          ; edgeV = RValTyPi.edgeV vtP'pi ; edgeE = RValTyPi.edgeE vtP'pi }
        newEqMM' : REqValTyPi G (cast T1 T2 q P) (cast T1' T2' q' P') a' f'
        newEqMM' = record
          { domA = REqValTyPi.domA eqvtPP'R ; codB = REqValTyPi.codB eqvtPP'R
          ; domA' = REqValTyPi.domA' eqvtPP'R ; codB' = REqValTyPi.codB' eqvtPP'R
          ; redM = Red3-trans redCM (REqValTyPi.redM eqvtPP'R)
          ; redN = Red3-trans redCM' (REqValTyPi.redN eqvtPP'R)
          ; cohF = REqValTyPi.cohF eqvtPP'R ; fmAllU = REqValTyPi.fmAllU eqvtPP'R
          ; convA = REqValTyPi.convA eqvtPP'R ; convB = REqValTyPi.convB eqvtPP'R
          ; eqA = REqValTyPi.eqA eqvtPP'R ; edgeET = REqValTyPi.edgeET eqvtPP'R }
    -- target PiCode
    CastEq T1 T2 q P T1' T2' q' P' Bot          v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' UCode        v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' (PiCode _ _) v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    CastEq T1 T2 q P T1' T2' q' P' (IdCode _ _) v c (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP = tt
    -- value-code v forced to FunEl by le
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) Bot          c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) UCode        c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (PiCode _ _) c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (IdCode _ _) c (PiCode b' f') () fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    -- type-code c forced to PiCode by fmv
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (FunEl gv) Bot          (PiCode b' f') le fmu () cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (FunEl gv) UCode        (PiCode b' f') le fmu () cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (FunEl gv) (FunEl _)    (PiCode b' f') le fmu () cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq T1 T2 q P T1' T2' q' P' (FunEl g) (FunEl gv) (IdCode _ _) (PiCode b' f') le fmu () cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP
    CastEq {G = G} T1 T2 q P T1' T2' q' P' (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b' f') le fmu fmv cv dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP =
      mkSigma vtT2 (mkSigma (snd castM) (mkSigma (snd castM'-T2) reqpi))
      where
        vtT1  = fst eqT1
        vtT1' = fst (snd eqT1)
        reqT1 = snd (snd eqT1)
        vtT2  = fst eqT2
        vtT2' = fst (snd eqT2)
        reqT2 = snd (snd eqT2)
        reqP  = snd (snd (snd eqP))
        vlP-full = MonoPack.Val2-from-EqVal2-first (goodStage (suc n)) (FunEl gv) (PiCode bc fc) eqP
        vlPpi = snd vlP-full
        C0 = RValTyPi.domA vtT2 ;  D0 = RValTyPi.codB vtT2
        C0' = RValTyPi.domA vtT2' ; D0' = RValTyPi.codB vtT2'
        A0 = RValPi.domA0 vlPpi ;  B0 = RValPi.codB0 vlPpi
        cv-pi = coh-from-aU (PiCode b' f') (finMem-funel-wf g b' f' fmu)
        -- P' relocated from T1 to T1'
        vlP'-T1  = MonoPack.Val2-from-EqVal2-second (goodStage (suc n)) (FunEl gv) (PiCode bc fc) eqP
        vlP'-T1' = TransportPack.Val2-type-transport (goodStageTransport (suc n)) (FunEl gv) (PiCode bc fc) eqT1 vlP'-T1
        vlP'pi   = snd vlP'-T1'
        -- uniqueness alignments with the REqValTyPi component names
        uniqT2M = Red3-unique-Pi (RValTyPi.red vtT2)  (REqValTyPi.redM reqT2)
        uniqT2N = Red3-unique-Pi (RValTyPi.red vtT2') (REqValTyPi.redN reqT2)
        convC0C0' : ConvTm G C0 C0' U
        convC0C0' = Eq-transport (\ y -> ConvTm G C0 y U) (Eq-sym (fst uniqT2N))
                      (Eq-transport (\ x -> ConvTm G x (REqValTyPi.domA' reqT2) U) (Eq-sym (fst uniqT2M))
                        (REqValTyPi.convA reqT2))
        eqC0C0' : EVTy n G C0 C0' b'
        eqC0C0' = Eq-transport (\ y -> EVTy n G C0 y b') (Eq-sym (fst uniqT2N))
                    (Eq-transport (\ x -> EVTy n G x (REqValTyPi.domA' reqT2) b') (Eq-sym (fst uniqT2M))
                      (REqValTyPi.eqA reqT2))
        A0' = RValPi.domA0 vlP'pi ; B0' = RValPi.codB0 vlP'pi
        uniqT1M = Red3-unique-Pi (RValPi.red vlPpi)  (REqValTyPi.redM reqT1)
        uniqT1N = Red3-unique-Pi (RValPi.red vlP'pi) (REqValTyPi.redN reqT1)
        eqA0A0' : EVTy n G A0 A0' bc
        eqA0A0' = Eq-transport (\ y -> EVTy n G A0 y bc) (Eq-sym (fst uniqT1N))
                    (Eq-transport (\ x -> EVTy n G x (REqValTyPi.domA' reqT1) bc) (Eq-sym (fst uniqT1M))
                      (REqValTyPi.eqA reqT1))
        convA0A0' : ConvTm G A0 A0' U
        convA0A0' = Eq-transport (\ y -> ConvTm G A0 y U) (Eq-sym (fst uniqT1N))
                      (Eq-transport (\ x -> ConvTm G x (REqValTyPi.domA' reqT1) U) (Eq-sym (fst uniqT1M))
                        (REqValTyPi.convA reqT1))
        edgeET-C0D0 : PiEdgeEqTy2 G C0 D0 D0' b' f'
        edgeET-C0D0 = Eq-transport (\ Z -> PiEdgeEqTy2 G C0 D0 Z b' f') (Eq-sym (snd uniqT2N))
                        (Eq-transport (\ Y -> PiEdgeEqTy2 G C0 Y (REqValTyPi.codB' reqT2) b' f') (Eq-sym (snd uniqT2M))
                          (Eq-transport (\ X -> PiEdgeEqTy2 G X (REqValTyPi.codB reqT2) (REqValTyPi.codB' reqT2) b' f') (Eq-sym (fst uniqT2M))
                            (REqValTyPi.edgeET reqT2)))
        edgeET-A0BB' : PiEdgeEqTy2 G A0 B0 B0' bc fc
        edgeET-A0BB' = Eq-transport (\ Z -> PiEdgeEqTy2 G A0 B0 Z bc fc) (Eq-sym (snd uniqT1N))
                         (Eq-transport (\ Y -> PiEdgeEqTy2 G A0 Y (REqValTyPi.codB' reqT1) bc fc) (Eq-sym (snd uniqT1M))
                           (Eq-transport (\ X -> PiEdgeEqTy2 G X (REqValTyPi.codB reqT1) (REqValTyPi.codB' reqT1) bc fc) (Eq-sym (fst uniqT1M))
                             (REqValTyPi.edgeET reqT1)))
        -- RValPi for the two casts (M' relocated to type T2)
        castM = Cast T1 T2 q P (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b' f')
                  le fmu fmv cv dT1 dT2 dq dP vtT1 vtT2 vlP-full
        castM'-T2' = Cast T1' T2' q' P' (FunEl g) (FunEl gv) (PiCode bc fc) (PiCode b' f')
                       le fmu fmv cv dT1' dT2' dq' dP' vtT1' vtT2' vlP'-T1'
        eqT2-sym : EVTy (suc n) G T2' T2 (PiCode b' f')
        eqT2-sym = FwdPack.EqValTy2-sym (goodStageFwd (suc n)) (PiCode b' f') cv-pi eqT2
        castM'-T2 = TransportPack.Val2-type-transport (goodStageTransport (suc n)) (FunEl g) (PiCode b' f') eqT2-sym castM'-T2'

        reqpi : REqValPi G (cast T1 T2 q P) (cast T1' T2' q' P') T2 g b' f'
        reqpi = record
          { domA0 = C0 ; codB0 = D0 ; red = RValTyPi.red vtT2
          ; cohG = finMem-funel-coh g b' f' fmu ; fmG = finMem-funel-fun g b' f' fmu
          ; appEV = appEV }
          where
            appEV : PiAppEqVal2 G (cast T1 T2 q P) (cast T1' T2' q' P') C0 D0 b' f' g
            appEV u0 v0 selg Q htQ valQ =
              EqVal2-trans v0 (EvalFun f' u0) cv0 cef
                (EqVal2-sym v0 (EvalFun f' u0) cv0 cef betaA)
                (EqVal2-trans v0 (EvalFun f' u0) cv0 cef outerEq betaB)
              where
                EqVal2-trans = SymTransPack.EqVal2-trans (goodStageSymTrans n)
                EqVal2-sym   = SymTransPack.EqVal2-sym (goodStageSymTrans n)
                beta         = BetaPack.Val2-beta-expand (goodStageBeta n)
                cf-M = coeFull T1 T2 q P g gv bc fc b' f' le fmu fmv dT1 dT2 dq dP vtT1 vtT2 vlPpi u0 v0 selg Q htQ valQ
                htQ' : HasType G Q C0'
                htQ' = ty-conv htQ convC0C0' (RValTyPi.htA vtT2')
                valQ' : Vl n G Q C0' u0 b'
                valQ' = TransportPack.Val2-type-transport (goodStageTransport n) u0 b' eqC0C0' valQ
                cf-M' = coeFull T1' T2' q' P' g gv bc fc b' f' le fmu fmv dT1' dT2' dq' dP' vtT1' vtT2' vlP'pi u0 v0 selg Q htQ' valQ'
                cv0 = FinMem-coh-u v0 (EvalFun f' u0) (CF.fmv0 cf-M)
                cef = Coherent-EvalFun f' u0 (CF.cftf' cf-M) (CF.cohu0 cf-M)
                -- shorthands
                ua = CF.ua cf-M ;  vP = CF.vP cf-M
                QA = CF.Npr cf-M ; QB = CF.Npr cf-M'
                cft-fc = RValTyPi.cohF vtT1 ; allU-fc = RValTyPi.fmAllU vtT1
                cft-f' = RValTyPi.cohF vtT2 ; allU-f' = RValTyPi.fmAllU vtT2
                cef-fc = Coherent-EvalFun fc ua cft-fc (CF.cohua cf-M)
                EqValTy2-trans = SymTransPack.EqValTy2-trans (goodStageSymTrans n)
                -- argument equality QA = QB : A0
                cvQAQB : ConvTm G QA QB A0
                cvQAQB = conv-cast-cong (RValTyPi.htA vtT2) (CF.htA0 cf-M) (CF.pi1symq cf-M) htQ
                           (RValTyPi.htA vtT2') (CF.htA0 cf-M') (CF.pi1symq cf-M') htQ'
                           convC0C0' convA0A0' (conv-refl htQ)
                argEq : EVl n G QA QB A0 ua bc
                argEq = CastPack.castEqVal ihC C0 A0 (pi1 (sym q)) Q  C0' A0' (pi1 (sym q')) Q
                          ua u0 b' bc (CF.leuau0 cf-M) (CF.fmuabc cf-M) (CF.fmu0b' cf-M) (CF.cohu0 cf-M)
                          (RValTyPi.htA vtT2) (CF.htA0 cf-M) (CF.pi1symq cf-M) htQ
                          (RValTyPi.htA vtT2') (CF.htA0 cf-M') (CF.pi1symq cf-M') htQ'
                          eqC0C0' eqA0A0' (ReflPack.Val2-to-EqVal2 (goodStageRefl n) u0 b' valQ)
                htQB-A0 : HasType G QB A0
                htQB-A0 = ty-conv (CF.htNpr cf-M') (conv-sym convA0A0') (CF.htA0 cf-M)
                valQB : Vl n G QB A0 ua bc
                valQB = MonoPack.Val2-from-EqVal2-second (goodStage n) ua bc argEq
                -- selectionBelow fc ua : value-edge equalities at code (EvalFun fc ua)
                sbfc = selectionBelow fc ua cft-fc (CF.cohua cf-M)
                wf1 = fst sbfc ; vvf1 = fst (snd sbfc) ; selfc = fst (snd (snd sbfc))
                le-wf1 = fst (snd (snd (snd sbfc))) ; eqfc = snd (snd (snd (snd sbfc)))
                fmwf1-bc = FinMemAllU-Selection bc selfc allU-fc cft-fc (CF.cbc cf-M) (CF.bcU cf-M)
                argEq-wf1 = MonoPack.restrictEqVal2 (goodStage n) G QA QB A0 ua wf1 bc le-wf1 fmwf1-bc (CF.fmuabc cf-M) argEq
                valQB-wf1 = MonoPack.restrictVal2 (goodStage n) G QB A0 ua wf1 bc le-wf1 fmwf1-bc (CF.fmuabc cf-M) valQB
                -- innerValEq : App P QA = App P' QB
                appEP : EVl n G (App P QA) (App P QB) (subst1 (CF.B0 cf-M) QA) vP (EvalFun fc ua)
                appEP = RValPi.appE vlPpi ua vP (CF.selgv cf-M) QA QB (CF.htNpr cf-M) htQB-A0 cvQAQB argEq
                uniqP = Red3-unique-Pi (RValPi.red vlPpi) (REqValPi.red reqP)
                htQB-reqP = Eq-transport (\ X -> HasType G QB X) (fst uniqP) htQB-A0
                valQB-reqP = Eq-transport (\ X -> Vl n G QB X ua bc) (fst uniqP) valQB
                appEVP' : EVl n G (App P QB) (App P' QB) (subst1 (CF.B0 cf-M) QB) vP (EvalFun fc ua)
                appEVP' = Eq-transport (\ Y -> EVl n G (App P QB) (App P' QB) (subst1 Y QB) vP (EvalFun fc ua)) (Eq-sym (snd uniqP))
                            (REqValPi.appEV reqP ua vP (CF.selgv cf-M) QB htQB-reqP valQB-reqP)
                eqBQBA : EVTy n G (subst1 (CF.B0 cf-M) QB) (subst1 (CF.B0 cf-M) QA) (EvalFun fc ua)
                eqBQBA = Eq-transport (\ x -> EVTy n G (subst1 (CF.B0 cf-M) QB) (subst1 (CF.B0 cf-M) QA) x) (Eq-sym eqfc)
                           (CF.edgeEAB cf-M wf1 vvf1 selfc QB QA htQB-A0 (CF.htNpr cf-M) (conv-sym cvQAQB)
                             (SymTransPack.EqVal2-sym (goodStageSymTrans n) wf1 bc (Coherent-Selection selfc cft-fc) (CF.cbc cf-M) argEq-wf1))
                innerValEq : EVl n G (App P QA) (App P' QB) (subst1 (CF.B0 cf-M) QA) vP (EvalFun fc ua)
                innerValEq = SymTransPack.EqVal2-trans (goodStageSymTrans n) vP (EvalFun fc ua) (CF.cohvP cf-M) cef-fc
                               appEP (TransportPack.EqVal2-type-transport (goodStageTransport n) vP (EvalFun fc ua) eqBQBA appEVP')
                -- eqSrcO : subst1 B0 QA = subst1 B0' QB (codomain code EvalFun fc ua)
                eqSrc1 : EVTy n G (subst1 (CF.B0 cf-M) QA) (subst1 (CF.B0 cf-M) QB) (EvalFun fc ua)
                eqSrc1 = Eq-transport (\ x -> EVTy n G (subst1 (CF.B0 cf-M) QA) (subst1 (CF.B0 cf-M) QB) x) (Eq-sym eqfc)
                           (CF.edgeEAB cf-M wf1 vvf1 selfc QA QB (CF.htNpr cf-M) htQB-A0 cvQAQB argEq-wf1)
                eqSrc2 : EVTy n G (subst1 (CF.B0 cf-M) QB) (subst1 (CF.B0 cf-M') QB) (EvalFun fc ua)
                eqSrc2 = Eq-transport (\ x -> EVTy n G (subst1 (CF.B0 cf-M) QB) (subst1 (CF.B0 cf-M') QB) x) (Eq-sym eqfc)
                           (edgeET-A0BB' wf1 vvf1 selfc QB htQB-A0 valQB-wf1)
                eqSrcO : EVTy n G (subst1 (CF.B0 cf-M) QA) (subst1 (CF.B0 cf-M') QB) (EvalFun fc ua)
                eqSrcO = EqValTy2-trans (EvalFun fc ua) cef-fc eqSrc1 eqSrc2
                -- eqTgtO : subst1 D0 Q = subst1 D0' Q (codomain code EvalFun f' u0)
                sbf' = selectionBelow f' u0 cft-f' (CF.cohu0 cf-M)
                wf2 = fst sbf' ; vvf2 = fst (snd sbf') ; self' = fst (snd (snd sbf'))
                le-wf2 = fst (snd (snd (snd sbf'))) ; eqf' = snd (snd (snd (snd sbf')))
                fmwf2-b' = FinMemAllU-Selection b' self' allU-f' cft-f' (CF.cb' cf-M) (CF.b'U cf-M)
                valQ-wf2 = MonoPack.restrictVal2 (goodStage n) G Q C0 u0 wf2 b' le-wf2 fmwf2-b' (CF.fmu0b' cf-M) valQ
                eqTgtO : EVTy n G (subst1 D0 Q) (subst1 D0' Q) (EvalFun f' u0)
                eqTgtO = Eq-transport (\ x -> EVTy n G (subst1 D0 Q) (subst1 D0' Q) x) (Eq-sym eqf')
                           (edgeET-C0D0 wf2 vvf2 self' Q htQ valQ-wf2)
                eqTgtO-sym : EVTy n G (subst1 D0' Q) (subst1 D0 Q) (EvalFun f' u0)
                eqTgtO-sym = FwdPack.EqValTy2-sym (goodStageFwd n) (EvalFun f' u0) cef eqTgtO
                outerEq : EVl n G (CF.reduct cf-M) (CF.reduct cf-M') (subst1 D0 Q) v0 (EvalFun f' u0)
                outerEq = CastPack.castEqVal ihC
                            (subst1 (CF.B0 cf-M) (CF.Npr cf-M)) (subst1 D0 Q) (sym (pi2 (sym q) Q)) (App P (CF.Npr cf-M))
                            (subst1 (CF.B0 cf-M') (CF.Npr cf-M')) (subst1 D0' Q) (sym (pi2 (sym q') Q)) (App P' (CF.Npr cf-M'))
                            v0 (CF.vP cf-M) (EvalFun fc (CF.ua cf-M)) (EvalFun f' u0)
                            (CF.lev0vP cf-M) (CF.fmv0 cf-M) (CF.fmvP cf-M) (CF.cohvP cf-M)
                            (CF.htSrc cf-M) (CF.htTgt cf-M) (CF.htQpr cf-M) (CF.htPNpr cf-M)
                            (CF.htSrc cf-M') (CF.htTgt cf-M') (CF.htQpr cf-M') (CF.htPNpr cf-M')
                            eqSrcO eqTgtO innerValEq
                betaA : EVl n G (CF.reduct cf-M) (App (cast T1 T2 q P) Q) (subst1 D0 Q) v0 (EvalFun f' u0)
                betaA = beta v0 (EvalFun f' u0) (CF.hr cf-M) (CF.ct cf-M) (CF.reductVal cf-M)
                betaB-nat : EVl n G (CF.reduct cf-M') (App (cast T1' T2' q' P') Q) (subst1 D0' Q) v0 (EvalFun f' u0)
                betaB-nat = beta v0 (EvalFun f' u0) (CF.hr cf-M') (CF.ct cf-M') (CF.reductVal cf-M')
                betaB : EVl n G (CF.reduct cf-M') (App (cast T1' T2' q' P') Q) (subst1 D0 Q) v0 (EvalFun f' u0)
                betaB = TransportPack.EqVal2-type-transport (goodStageTransport n) v0 (EvalFun f' u0) eqTgtO-sym betaB-nat
