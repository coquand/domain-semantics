{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.CastAgreement.agda
--
-- Semantic soundness of the coe-Pi reduction rule (headred-cast-Pi):
--
--   App (cast (Pi A B) (Pi C D) p M) N
--     reduces to
--   cast (B[N']) (D[N]) (sym (pi2 (sym p) N)) (App M N')   ,  N' = cast C A (pi1 (sym p)) N
--
-- We prove `InvConv-cast-Pi`, the EvalRel bidirectional agreement plus the
-- two InvTyp enlargements, which is exactly what `convSound'` needs for the
-- `conv-cast-Pi` constructor.  Built only from the existing EvalRel companions
-- and the InvTyp-App / selection machinery in LemmaForTS / RawSemantics.
--
-- 0 postulates.
------------------------------------------------------------------------

module CAST.CastAgreement where

import CAST.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; mkCFT ; cft-from-cf ;
  NotBot ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  finMem-bot-from ; finMem-piU-mk ; finMem-funel-mk ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  finMem-upward ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon-arg ; Coherent-EvalFun ;
  LeFunCode ; LeFunCode-refl ;
  EvalFun-in-UCode)
open import CAST.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMem-Selection ; FinMem-Selection-codomain)
open import CAST.RawSyntax using (Expr ; U ; Pi ; Lam ; App ; Id ; cast ; sym ; pi1 ; pi2 ;
  subst1)
open import CAST.RawSemantics
open import CAST.EvalSubstitution using (EvalRel-subst1-forward)
open import CAST.TypingRules using (Ctx ; extend ; HasType ; ConvTm)
open import CAST.PaperSemantics using (comp-Bot-r ; EvalFun-in-UCode)
open import CAST.LemmaForTS using (Fits ; Typed ; InvTyp ; InvConv ;
  Fits-CoherentEnv ; InvTyp-App ; NotBot-from-Le ; NotBot-from-FinMem ; EvalFun-edge-le)

------------------------------------------------------------------------
-- InvTyp-cast : a cast value is its own typed enlargement at the target.
-- Uniform in the code u: the guarded semantics already carries a target
-- witness (v : b with b an approximant of the target type).
------------------------------------------------------------------------

InvTyp-cast : {n : Nat} {G : Ctx n} (T1 T2 q P : Expr n) (rho : EnvApprox n) ->
  InvTyp G (cast T1 T2 q P) T2 rho
InvTyp-cast T1 T2 q P rho u ev =
  let cu     = fst ev
      v      = fst (snd ev)
      le-u-v = fst (snd (snd ev))
      evP-v  = fst (snd (snd (snd ev)))
      b      = fst (snd (snd (snd (snd ev))))
      evT2-b = fst (snd (snd (snd (snd (snd ev)))))
      fm-v-b = snd (snd (snd (snd (snd (snd ev)))))
      cv     = FinMem-coh-u v b fm-v-b
      evCast-v : EvalRel (cast T1 T2 q P) rho v
      evCast-v = mkSigma cv (mkSigma v (mkSigma (LeCode-refl v cv)
                   (mkSigma evP-v (mkSigma b (mkSigma evT2-b fm-v-b)))))
  in mkSigma v (mkSigma b (mkSigma le-u-v (mkSigma evCast-v (mkSigma fm-v-b evT2-b))))

------------------------------------------------------------------------
-- single-edge-PiCD : a single C-typed/D-typed edge is a Pi C D member.
--
-- Given a domain value vstar : cstar (a C-approximant) and an output w that
-- is D-typed at vstar (w : b2, EvalRel D (rho,vstar) b2), the singleton
-- function {vstar |-> w} is a member of the Pi-code (PiCode cstar {vstar|->b2}),
-- which is itself a value of Pi C D.  This is the ONLY synthesis the backward
-- direction needs.
------------------------------------------------------------------------

single-edge-PiCD : {n : Nat} (C : Expr n) (D : Expr (suc n))
  (rho : EnvApprox n) (vstar w cstar b2 : FinEl) -> NotBot w ->
  Coherent vstar -> Coherent w ->
  FinMem vstar cstar -> EvalRel C rho cstar ->
  EvalRel D (extendEnv rho vstar) b2 -> FinMem w b2 ->
  Sigma FinEl (\ b -> Pair (EvalRel (Pi C D) rho b)
                           (FinMem (FunEl (cons (mkSigma vstar w) nil)) b))
single-edge-PiCD C D rho vstar w cstar b2 nbw cvstar cw fm-vstar-cstar evC-cstar evD-b2 fm-w-b2 =
  mkSigma (PiCode cstar fc) (mkSigma evPi fm-funel)
  where
    fc : FinFun
    fc = cons (mkSigma vstar b2) nil
    c-cstar = EvalRel-coh C rho cstar evC-cstar
    cb2     = EvalRel-coh D (extendEnv rho vstar) b2 evD-b2
    nb-b2   = NotBot-from-FinMem w b2 nbw fm-w-b2
    cstarU  = FinMem-a-in-U vstar cstar fm-vstar-cstar
    b2U     = FinMem-a-in-U w b2 fm-w-b2
    cft-fc  : CoherentFunTail fc
    cft-fc  = mkCFT cvstar cb2 nb-b2 tt tt
    fmBot   = finMem-bot-from cstar cstarU
    selbody : (u' v' : FinEl) -> Selection fc u' v' ->
      Sigma FinEl (\ x -> Pair (LeCode x u')
        (Pair (FinMem x cstar) (EvalRel D (extendEnv rho x) v')))
    selbody .Bot .Bot (sel-skip sel-nil) =
      mkSigma Bot (mkSigma (LeCode-Bot Bot)
        (mkSigma fmBot (EvalRel-Bot D (extendEnv rho Bot))))
    selbody .(Sup vstar Bot) .(Sup b2 Bot) (sel-take {._} {.Bot} {.Bot} ck cv0 sel-nil) =
      mkSigma vstar (mkSigma
        (Eq-transport (LeCode vstar) (Eq-sym (Sup-Bot-r vstar)) (LeCode-refl vstar cvstar))
        (mkSigma fm-vstar-cstar
          (Eq-transport (EvalRel D (extendEnv rho vstar)) (Eq-sym (Sup-Bot-r b2)) evD-b2)))
    evPi : EvalRel (Pi C D) rho (PiCode cstar fc)
    evPi = mkSigma (mkSigma c-cstar cft-fc)
             (mkSigma evC-cstar (mkSigma cstar (mkSigma evC-cstar selbody)))
    -- FinMem of the singleton {vstar |-> w}
    fmAllU : FinMemAllU fc cstar
    fmAllU = mkSigma (mkSigma fm-vstar-cstar b2U) tt
    fm-pi-U : FinMem (PiCode cstar fc) UCode
    fm-pi-U = finMem-piU-mk cstar fc cstarU fmAllU cft-fc
    le-b2-Ef : LeCode b2 (EvalFun fc vstar)
    le-b2-Ef = EvalFun-edge-le (mkSigma vstar b2) fc vstar cft-fc here cvstar
                 (LeCode-refl vstar cvstar)
    c-Ef    = Coherent-EvalFun fc vstar cft-fc cvstar
    Ef-U    = EvalFun-in-UCode fc vstar cstar cft-fc cvstar fmAllU
    fm-w-Ef : FinMem w (EvalFun fc vstar)
    fm-w-Ef = finMem-upward w b2 (EvalFun fc vstar) le-b2-Ef cb2 c-Ef fm-w-b2 Ef-U
    fmFun   : FinMemFun (cons (mkSigma vstar w) nil) cstar fc
    fmFun   = mkSigma (mkSigma fm-vstar-cstar fm-w-Ef) tt
    cf-edge : CoherentFun (cons (mkSigma vstar w) nil)
    cf-edge = mkCFT cvstar cw nbw tt tt
    fm-funel : FinMem (FunEl (cons (mkSigma vstar w) nil)) (PiCode cstar fc)
    fm-funel = finMem-funel-mk (cons (mkSigma vstar w) nil) cstar fc fmFun cf-edge fm-pi-U

------------------------------------------------------------------------
-- InvConv-cast-Pi : the coe-Pi reduction is EvalRel-sound.
--
--   LHS    = App (cast (Pi A B) (Pi C D) p M) N
--   N'     = cast C A (pi1 (sym p)) N
--   reduct = cast (subst1 B N') (subst1 D N) (sym (pi2 (sym p) N)) (App M N')
--   type   = subst1 D N
------------------------------------------------------------------------

InvConv-cast-Pi : {n : Nat} {G : Ctx n}
  (A C : Expr n) (B D : Expr (suc n)) (p M N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G M (Pi A B) rho ->
  InvTyp G N C rho ->
  InvConv G (App (cast (Pi A B) (Pi C D) p M) N)
            (cast (subst1 B (cast C A (pi1 (sym p)) N)) (subst1 D N)
                  (sym (pi2 (sym p) N))
                  (App M (cast C A (pi1 (sym p)) N)))
            (subst1 D N) rho
InvConv-cast-Pi {G = G} A C B D p M N rho fits invM invN =
  mkSigma invTyp-LHS (mkSigma invTyp-reduct (mkSigma fwd bwd))
  where
    crho = Fits-CoherentEnv rho fits
    Npr  = cast C A (pi1 (sym p)) N
    qpr  = sym (pi2 (sym p) N)
    Fcast = cast (Pi A B) (Pi C D) p M

    invTyp-LHS : InvTyp G (App Fcast N) (subst1 D N) rho
    invTyp-LHS = InvTyp-App C D Fcast N rho fits (InvTyp-cast {G = G} (Pi A B) (Pi C D) p M rho) invN

    invTyp-reduct : InvTyp G (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) (subst1 D N) rho
    invTyp-reduct = InvTyp-cast {G = G} (subst1 B Npr) (subst1 D N) qpr (App M Npr) rho

    -- App M Npr at the edge output: arg = the A-typed selection u0 of warg,
    -- M-edge {u0 |-> vout} <= g' because EvalFun g' u0 = EvalFun g' warg >= vout.
    mkEvalAppNpr : (vout : FinEl) -> NotBot vout -> (arg : FinEl) ->
      EvalRel Npr rho arg ->
      EvalRel M rho (FunEl (cons (mkSigma arg vout) nil)) ->
      EvalRel (App M Npr) rho vout
    mkEvalAppNpr Bot () arg eA eM
    mkEvalAppNpr UCode nb arg eA eM = mkSigma arg (mkSigma eA eM)
    mkEvalAppNpr (FunEl g) nb arg eA eM = mkSigma arg (mkSigma eA eM)
    mkEvalAppNpr (PiCode a0 f0) nb arg eA eM = mkSigma arg (mkSigma eA eM)
    mkEvalAppNpr (IdCode a0 b0) nb arg eA eM = mkSigma arg (mkSigma eA eM)

    fwd-core-h : (warg vout : FinEl) -> NotBot vout -> Coherent vout ->
      EvalRel N rho warg ->
      EvalRel M rho (FunEl (cons (mkSigma warg vout) nil)) ->
      (h piaf : FinEl) ->
      LeCode (FunEl (cons (mkSigma warg vout) nil)) h ->
      EvalRel M rho h -> FinMem h piaf -> EvalRel (Pi A B) rho piaf ->
      EvalRel (App M Npr) rho vout
    fwd-core-h warg vout nbv cv evN evMsing Bot piaf () evM-h fm-h evPi
    fwd-core-h warg vout nbv cv evN evMsing UCode piaf () evM-h fm-h evPi
    fwd-core-h warg vout nbv cv evN evMsing (PiCode _ _) piaf () evM-h fm-h evPi
    fwd-core-h warg vout nbv cv evN evMsing (IdCode _ _) piaf () evM-h fm-h evPi
    fwd-core-h warg vout nbv cv evN evMsing (FunEl g') Bot le evM-g' () evPi
    fwd-core-h warg vout nbv cv evN evMsing (FunEl g') UCode le evM-g' () evPi
    fwd-core-h warg vout nbv cv evN evMsing (FunEl g') (FunEl _) le evM-g' () evPi
    fwd-core-h warg vout nbv cv evN evMsing (FunEl g') (IdCode _ _) le evM-g' fm-g' ()
    fwd-core-h warg vout nbv cv evN evMsing (FunEl g') (PiCode a f) le evM-g' fm-g' evPi =
      let fmFun-g' = finMem-funel-fun g' a f fm-g'
          cf-g'    = finMem-funel-coh g' a f fm-g'
          piU      = finMem-funel-wf g' a f fm-g'
          aU       = finMem-piU-dom a f piU
          ca       = coh-from-aU a aU
          le-v-ef  = fst le                       -- LeCode vout (EvalFun g' warg)
          cw       = EvalRel-coh N rho warg evN
          ctg'     = cft-from-cf g' cf-g'
          sb       = selectionBelow g' warg ctg' cw
          u0       = fst sb
          vsel     = fst (snd sb)                 -- = EvalFun g' warg
          sel-g'   = fst (snd (snd sb))           -- Selection g' u0 vsel
          le-u0-w  = fst (snd (snd (snd sb)))     -- LeCode u0 warg
          eq-vsel  = snd (snd (snd (snd sb)))     -- Eq (EvalFun g' warg) vsel
          cu0      = Coherent-Selection sel-g' ctg'
          cvsel    = Coherent-Selection-val sel-g' ctg'
          fm-u0-a  = FinMem-Selection a f sel-g' fmFun-g' ctg' ca aU
          evA-a    = fst (snd evPi)
          evN-u0   = EvalRel-down N rho warg u0 crho cu0 evN le-u0-w
          evNpr-u0 : EvalRel Npr rho u0
          evNpr-u0 = mkSigma cu0 (mkSigma u0 (mkSigma (LeCode-refl u0 cu0)
                       (mkSigma evN-u0 (mkSigma a (mkSigma evA-a fm-u0-a)))))
          le-vsel-efu0 = Selection-le-EvalFun g' sel-g' (LeFunCode-refl g' ctg') ctg' ctg' cu0
                                                    -- LeCode vsel (EvalFun g' u0)
          c-efu0   = Coherent-EvalFun g' u0 ctg' cu0
          le-vout-vsel = Eq-transport (LeCode vout) eq-vsel le-v-ef  -- LeCode vout vsel
          le-vout-efu0 = LeCode-trans vout vsel (EvalFun g' u0) cv cvsel c-efu0
                           le-vout-vsel le-vsel-efu0
          lf-sing : LeFunCode (cons (mkSigma u0 vout) nil) g'
          lf-sing = mkSigma le-vout-efu0 tt
          cf-sing : Coherent (FunEl (cons (mkSigma u0 vout) nil))
          cf-sing = mkCFT cu0 cv nbv tt tt
          evM-sing-u0 = EvalRel-down M rho (FunEl g') (FunEl (cons (mkSigma u0 vout) nil))
                          crho cf-sing evM-g' lf-sing
      in mkEvalAppNpr vout nbv u0 evNpr-u0 evM-sing-u0

    fwd-core : (warg vout : FinEl) -> NotBot vout -> Coherent vout ->
      EvalRel N rho warg ->
      EvalRel M rho (FunEl (cons (mkSigma warg vout) nil)) ->
      EvalRel (App M Npr) rho vout
    fwd-core warg vout nbv cv evN evMsing =
      let im = invM (FunEl (cons (mkSigma warg vout) nil)) evMsing
          h    = fst im
          piaf = fst (snd im)
          le-sing-h = fst (snd (snd im))
          evM-h = fst (snd (snd (snd im)))
          fm-h  = fst (snd (snd (snd (snd im))))
          evPi  = snd (snd (snd (snd (snd im))))
      in fwd-core-h warg vout nbv cv evN evMsing h piaf le-sing-h evM-h fm-h evPi

    fwd-non-bot : (u : FinEl) -> NotBot u -> EvalRel (App Fcast N) rho u ->
      EvalRel (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) rho u
    fwd-non-bot u nbu ev =
      let cu       = EvalRel-coh (App Fcast N) rho u ev
          typed    = invTyp-LHS u ev
          u'       = fst typed
          a'       = fst (snd typed)
          le-u-u'  = fst (snd (snd typed))
          ev-LHS-u' = fst (snd (snd (snd typed)))
          fm-u'-a' = fst (snd (snd (snd (snd typed))))
          ev-DN-a' = snd (snd (snd (snd (snd typed))))
          cu'      = FinMem-coh-u u' a' fm-u'-a'
          nbu'     = NotBot-from-Le u u' cu nbu le-u-u'
          dec      = App-decompose Fcast N rho u' nbu' ev-LHS-u'
          v'       = fst dec
          evN-v'   = fst (snd dec)
          evFcast  = snd (snd dec)             -- EvalRel Fcast rho (FunEl(cons(v',u')nil))
          W        = FunEl (cons (mkSigma v' u') nil)
          cW       = fst evFcast
          vv       = fst (snd evFcast)
          le-W-vv  = fst (snd (snd evFcast))
          evM-vv   = fst (snd (snd (snd evFcast)))
          evMW     = EvalRel-down M rho vv W crho cW evM-vv le-W-vv
          evApp    = fwd-core v' u' nbu' cu' evN-v' evMW
      in mkSigma cu (mkSigma u' (mkSigma le-u-u'
           (mkSigma evApp (mkSigma a' (mkSigma ev-DN-a' fm-u'-a')))))

    fwd : (u : FinEl) -> EvalRel (App Fcast N) rho u ->
      EvalRel (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) rho u
    fwd Bot ev =
      EvalRel-Bot (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) rho
    fwd UCode ev = fwd-non-bot UCode tt ev
    fwd (FunEl g) ev = fwd-non-bot (FunEl g) tt ev
    fwd (PiCode a0 f0) ev = fwd-non-bot (PiCode a0 f0) tt ev
    fwd (IdCode a0 b0) ev = fwd-non-bot (IdCode a0 b0) tt ev

    mkEvalAppFcast : (u : FinEl) -> NotBot u -> (arg : FinEl) ->
      EvalRel N rho arg ->
      EvalRel Fcast rho (FunEl (cons (mkSigma arg u) nil)) ->
      EvalRel (App Fcast N) rho u
    mkEvalAppFcast Bot () arg eN eF
    mkEvalAppFcast UCode nb arg eN eF = mkSigma arg (mkSigma eN eF)
    mkEvalAppFcast (FunEl g) nb arg eN eF = mkSigma arg (mkSigma eN eF)
    mkEvalAppFcast (PiCode a0 f0) nb arg eN eF = mkSigma arg (mkSigma eN eF)
    mkEvalAppFcast (IdCode a0 b0) nb arg eN eF = mkSigma arg (mkSigma eN eF)

    bwd-non-bot : (u : FinEl) -> NotBot u ->
      EvalRel (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) rho u ->
      EvalRel (App Fcast N) rho u
    bwd-non-bot u nbu ev =
      let cu        = fst ev
          w         = fst (snd ev)
          le-u-w    = fst (snd (snd ev))
          evApp-w   = fst (snd (snd (snd ev)))
          b2        = fst (snd (snd (snd (snd ev))))
          evDN-b2   = fst (snd (snd (snd (snd (snd ev)))))
          fm-w-b2   = snd (snd (snd (snd (snd (snd ev)))))
          cw        = FinMem-coh-u w b2 fm-w-b2
          nbw       = NotBot-from-Le u w cu nbu le-u-w
          dec       = App-decompose M Npr rho w nbw evApp-w
          vN'       = fst dec
          evNpr-vN' = fst (snd dec)
          evM-vN'w  = snd (snd dec)           -- EvalRel M rho (FunEl(cons(vN',w)nil))
          cvN'      = fst evNpr-vN'
          vc        = fst (snd evNpr-vN')
          le-vN'-vc = fst (snd (snd evNpr-vN'))
          evN-vc    = fst (snd (snd (snd evNpr-vN')))
          sf        = EvalRel-subst1-forward D N rho b2 crho evDN-b2
          vn        = fst sf
          evN-vn    = fst (snd sf)
          evD-vn-b2 = snd (snd sf)
          cvc       = EvalRel-coh N rho vc evN-vc
          cvn       = EvalRel-coh N rho vn evN-vn
          comp      = EvalRel-Comp N rho crho vc vn evN-vc evN-vn
          vsup      = Sup vc vn
          cvsup     = Coherent-Sup vc vn comp cvc cvn
          evN-vsup  = EvalRel-Sup N rho vc vn crho cvc cvn comp evN-vc evN-vn
          tn        = invN vsup evN-vsup
          vstar     = fst tn
          cstar     = fst (snd tn)
          le-vsup-vstar = fst (snd (snd tn))
          evN-vstar = fst (snd (snd (snd tn)))
          fm-vstar-cstar = fst (snd (snd (snd (snd tn))))
          evC-cstar = snd (snd (snd (snd (snd tn))))
          cvstar    = FinMem-coh-u vstar cstar fm-vstar-cstar
          le-vc-vsup = LeCode-Sup-left vc vn comp cvc cvn
          le-vn-vsup = LeCode-Sup-right vc vn comp cvc cvn
          le-vN'-vsup = LeCode-trans vN' vc vsup cvN' cvc cvsup le-vN'-vc le-vc-vsup
          le-vN'-vstar = LeCode-trans vN' vsup vstar cvN' cvsup cvstar le-vN'-vsup le-vsup-vstar
          le-vn-vstar = LeCode-trans vn vsup vstar cvn cvsup cvstar le-vn-vsup le-vsup-vstar
          envle     = mkSigma (EnvLe-refl rho crho) (mkSigma cvn (mkSigma cvstar le-vn-vstar))
          evD-vstar-b2 = EvalRel-mon-env D (extendEnv rho vn) (extendEnv rho vstar) b2 evD-vn-b2 envle
          -- M-edge vstar |-> w  (down-close the input from vN' to vstar)
          cft-vN'w  = mkCFT cvN' cw nbw tt tt
          le-w-Ef-vN' = EvalFun-edge-le (mkSigma vN' w) (cons (mkSigma vN' w) nil) vstar
                          cft-vN'w here cvstar le-vN'-vstar
          cf-vstarw : Coherent (FunEl (cons (mkSigma vstar w) nil))
          cf-vstarw = mkCFT cvstar cw nbw tt tt
          lf-edge   : LeFunCode (cons (mkSigma vstar w) nil) (cons (mkSigma vN' w) nil)
          lf-edge   = mkSigma le-w-Ef-vN' tt
          evM-vstarw = EvalRel-down M rho (FunEl (cons (mkSigma vN' w) nil))
                         (FunEl (cons (mkSigma vstar w) nil)) crho cf-vstarw evM-vN'w lf-edge
          -- the Pi C D membership for {vstar |-> w}
          piCD      = single-edge-PiCD C D rho vstar w cstar b2 nbw cvstar cw
                        fm-vstar-cstar evC-cstar evD-vstar-b2 fm-w-b2
          bcode     = fst piCD
          evPiCD    = fst (snd piCD)
          fm-vv-b   = snd (snd piCD)
          -- the Fcast edge value {vstar |-> u}
          cft-vstarw = mkCFT cvstar cw nbw tt tt
          c-Ef-vstarw = Coherent-EvalFun (cons (mkSigma vstar w) nil) vstar cft-vstarw cvstar
          le-w-Ef-vstar = EvalFun-edge-le (mkSigma vstar w) (cons (mkSigma vstar w) nil) vstar
                            cft-vstarw here cvstar (LeCode-refl vstar cvstar)
          le-u-Ef   = LeCode-trans u w (EvalFun (cons (mkSigma vstar w) nil) vstar)
                        cu cw c-Ef-vstarw le-u-w le-w-Ef-vstar
          lf-u      : LeFunCode (cons (mkSigma vstar u) nil) (cons (mkSigma vstar w) nil)
          lf-u      = mkSigma le-u-Ef tt
          coh-edge-u : Coherent (FunEl (cons (mkSigma vstar u) nil))
          coh-edge-u = mkCFT cvstar cu nbu tt tt
          evFcast-edge : EvalRel Fcast rho (FunEl (cons (mkSigma vstar u) nil))
          evFcast-edge = mkSigma coh-edge-u (mkSigma (FunEl (cons (mkSigma vstar w) nil))
                           (mkSigma lf-u (mkSigma evM-vstarw
                             (mkSigma bcode (mkSigma evPiCD fm-vv-b)))))
      in mkEvalAppFcast u nbu vstar evN-vstar evFcast-edge

    bwd : (u : FinEl) ->
      EvalRel (cast (subst1 B Npr) (subst1 D N) qpr (App M Npr)) rho u ->
      EvalRel (App Fcast N) rho u
    bwd Bot ev = EvalRel-Bot (App Fcast N) rho
    bwd UCode ev = bwd-non-bot UCode tt ev
    bwd (FunEl g) ev = bwd-non-bot (FunEl g) tt ev
    bwd (PiCode a0 f0) ev = bwd-non-bot (PiCode a0 f0) tt ev
    bwd (IdCode a0 b0) ev = bwd-non-bot (IdCode a0 b0) tt ev
