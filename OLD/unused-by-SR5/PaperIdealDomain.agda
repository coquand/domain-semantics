{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperIdealDomain.agda
--
-- General domain elements as ideals of COHERENT finite elements,
-- built over the paper-faithful finite semantics from
-- PaperSemantics.agda.
--
-- A domain element is an ideal of coherent finite elements:
-- downward closed, pairwise compatible, sup-closed, with all
-- members coherent.
--
-- 0 postulates.
------------------------------------------------------------------------

module PaperIdealDomain where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; List ; nil ; cons ; Eq ; refl ;
              Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun)
open import PaperSemantics hiding (LeCode-refl ; LeCode-trans)
open import PaperSemantics using (LeCode-refl ; LeCode-trans)

------------------------------------------------------------------------
-- Section 1: Ideal record and order
------------------------------------------------------------------------

record Dom : Set₁ where
  field
    holds : FinEl -> Set
    botH  : holds Bot
    downH : (u v : FinEl) -> Coherent u -> LeCode u v -> holds v ->
             holds u
    compH : (u v : FinEl) -> holds u -> holds v -> Comp u v
    supH  : (u v : FinEl) -> Comp u v -> holds u -> holds v ->
             holds (Sup u v)
    cohH  : (u : FinEl) -> holds u -> Coherent u

open Dom public

LeDom : Dom -> Dom -> Set
LeDom X Y = (u : FinEl) -> holds X u -> holds Y u

LeDom-refl : (X : Dom) -> LeDom X X
LeDom-refl X u h = h

LeDom-trans : (X Y Z : Dom) -> LeDom X Y -> LeDom Y Z -> LeDom X Z
LeDom-trans X Y Z xy yz u h = yz u (xy u h)

------------------------------------------------------------------------
-- Section 2: Principal ideals
------------------------------------------------------------------------

Principal-comp : (a : FinEl) -> Coherent a ->
  (u v : FinEl) -> Pair (Coherent u) (LeCode u a) ->
  Pair (Coherent v) (LeCode v a) -> Comp u v
Principal-comp a ca u v hu hv = LeCode-Comp u v a ca (snd hu) (snd hv)

Principal-sup-closed : (a u v : FinEl) ->
  LeCode u a -> LeCode v a -> LeCode (Sup u v) a
Principal-sup-closed a u v = LeCode-Sup-lub u v a

Principal : (a : FinEl) -> Coherent a -> Dom
holds (Principal a ca) u = Pair (Coherent u) (LeCode u a)
botH  (Principal a ca) = mkSigma tt (LeCode-Bot a)
downH (Principal a ca) u v cu le (mkSigma cv hv) =
  mkSigma cu (LeCode-trans u v a cu cv ca le hv)
compH (Principal a ca) u v hu hv = Principal-comp a ca u v hu hv
supH  (Principal a ca) u v comp (mkSigma cu hu) (mkSigma cv hv) =
  mkSigma (Coherent-Sup u v comp cu cv)
          (Principal-sup-closed a u v hu hv)
cohH  (Principal a ca) u (mkSigma cu _) = cu

------------------------------------------------------------------------
-- Section 3: Application of ideals
------------------------------------------------------------------------

Coherent-applyEl : (f a : FinEl) -> Coherent f -> Coherent a ->
  Coherent (applyEl f a)
Coherent-applyEl Bot          a cf ca = tt
Coherent-applyEl UCode        a cf ca = tt
Coherent-applyEl PropCode     a cf ca = tt
Coherent-applyEl (FunEl g)    a cf ca = Coherent-EvalFun g a (cft-from-cf g cf) ca
Coherent-applyEl (PiCode b h) a cf ca = tt

applyEl-le-Sup-left : (f1 f2 a1 a2 : FinEl) ->
  Coherent f1 -> Coherent f2 -> Coherent a1 -> Coherent a2 ->
  Comp f1 f2 -> Comp a1 a2 ->
  LeCode (applyEl f1 a1) (applyEl (Sup f1 f2) (Sup a1 a2))
applyEl-le-Sup-left Bot          f2           a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left UCode        Bot          a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left UCode        UCode        a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left UCode        PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left UCode        (FunEl g2)   a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left UCode        (PiCode b h) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left PropCode     Bot          a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left PropCode     UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left PropCode     PropCode     a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left PropCode     (FunEl g2)   a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left PropCode     (PiCode b h) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (PiCode b h) Bot          a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left (PiCode b h) UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (PiCode b h) PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (PiCode b h) (FunEl g2)   a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (PiCode b h) (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-left (FunEl g1) Bot a1 a2 cf1 cf2 ca1 ca2 compf compa =
  EvalFun-mon-arg g1 a1 (Sup a1 a2)
    (LeCode-Sup-left a1 a2 compa ca1 ca2)
    (cft-from-cf g1 cf1) ca1 (Coherent-Sup a1 a2 compa ca1 ca2)
applyEl-le-Sup-left (FunEl g1) UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (FunEl g1) PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (FunEl g1) (PiCode b h) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-left (FunEl g1) (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 compf compa =
  let cgh  = CoherentFun-append g1 g2 cf1 cf2 compf
      cght = cft-from-cf (append g1 g2) cgh
      cf1t = cft-from-cf g1 cf1
      ca12 = Coherent-Sup a1 a2 compa ca1 ca2
      le-g = LeFunCode-append-left g1 g2 compf cf1t (cft-from-cf g2 cf2)
      le-a = LeCode-Sup-left a1 a2 compa ca1 ca2
      step1 = EvalFun-mon g1 (append g1 g2) a1 cf1t cght ca1 le-g
      step2 = EvalFun-mon-arg (append g1 g2) a1 (Sup a1 a2) le-a
                cght ca1 ca12
  in LeCode-trans (EvalFun g1 a1) (EvalFun (append g1 g2) a1)
       (EvalFun (append g1 g2) (Sup a1 a2))
       (Coherent-EvalFun g1 a1 cf1t ca1)
       (Coherent-EvalFun (append g1 g2) a1 cght ca1)
       (Coherent-EvalFun (append g1 g2) (Sup a1 a2) cght ca12)
       step1 step2

applyEl-le-Sup-right : (f1 f2 a1 a2 : FinEl) ->
  Coherent f1 -> Coherent f2 -> Coherent a1 -> Coherent a2 ->
  Comp f1 f2 -> Comp a1 a2 ->
  LeCode (applyEl f2 a2) (applyEl (Sup f1 f2) (Sup a1 a2))
applyEl-le-Sup-right f1           Bot          a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right Bot          UCode        a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right UCode        UCode        a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right PropCode     UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (FunEl g1)   UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (PiCode b h) UCode        a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right Bot          PropCode     a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right UCode        PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right PropCode     PropCode     a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right (FunEl g1)   PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (PiCode b h) PropCode     a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right Bot          (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right UCode        (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right PropCode     (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (FunEl g1)   (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (PiCode b h) (PiCode c k) a1 a2 cf1 cf2 ca1 ca2 compf compa = tt
applyEl-le-Sup-right Bot (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 compf compa =
  EvalFun-mon-arg g2 a2 (Sup a1 a2)
    (LeCode-Sup-right a1 a2 compa ca1 ca2)
    (cft-from-cf g2 cf2) ca2 (Coherent-Sup a1 a2 compa ca1 ca2)
applyEl-le-Sup-right UCode        (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right PropCode     (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (PiCode b h) (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 ()
applyEl-le-Sup-right (FunEl g1) (FunEl g2) a1 a2 cf1 cf2 ca1 ca2 compf compa =
  let cgh  = CoherentFun-append g1 g2 cf1 cf2 compf
      cght = cft-from-cf (append g1 g2) cgh
      cf2t = cft-from-cf g2 cf2
      ca12 = Coherent-Sup a1 a2 compa ca1 ca2
      le-g = LeFunCode-append-right g1 g2 compf (cft-from-cf g1 cf1) cf2t
      le-a = LeCode-Sup-right a1 a2 compa ca1 ca2
      step1 = EvalFun-mon g2 (append g1 g2) a2 cf2t cght ca2 le-g
      step2 = EvalFun-mon-arg (append g1 g2) a2 (Sup a1 a2) le-a
                cght ca2 ca12
  in LeCode-trans (EvalFun g2 a2) (EvalFun (append g1 g2) a2)
       (EvalFun (append g1 g2) (Sup a1 a2))
       (Coherent-EvalFun g2 a2 cf2t ca2)
       (Coherent-EvalFun (append g1 g2) a2 cght ca2)
       (Coherent-EvalFun (append g1 g2) (Sup a1 a2) cght ca12)
       step1 step2

record AppWitness (X Y : Dom) (w : FinEl) : Set where
  constructor mkAppWitness
  field
    app-coh       : Coherent w
    app-fun       : FinEl
    app-arg       : FinEl
    app-fun-holds : holds X app-fun
    app-arg-holds : holds Y app-arg
    app-le        : LeCode w (applyEl app-fun app-arg)

AppDom-comp : (X Y : Dom) (u v : FinEl) ->
  AppWitness X Y u -> AppWitness X Y v -> Comp u v
AppDom-comp X Y u v
  (mkAppWitness cu f1 a1 hf1 ha1 hle1)
  (mkAppWitness cv f2 a2 hf2 ha2 hle2) =
  let cf1 = cohH X f1 hf1
      cf2 = cohH X f2 hf2
      ca1 = cohH Y a1 ha1
      ca2 = cohH Y a2 ha2
      compf = compH X f1 f2 hf1 hf2
      compa = compH Y a1 a2 ha1 ha2
      c-sup-f = Coherent-Sup f1 f2 compf cf1 cf2
      c-sup-a = Coherent-Sup a1 a2 compa ca1 ca2
      c-apply-sup = Coherent-applyEl (Sup f1 f2) (Sup a1 a2) c-sup-f c-sup-a
      le1 = applyEl-le-Sup-left  f1 f2 a1 a2 cf1 cf2 ca1 ca2 compf compa
      le2 = applyEl-le-Sup-right f1 f2 a1 a2 cf1 cf2 ca1 ca2 compf compa
      comp-apply = LeCode-Comp
        (applyEl f1 a1) (applyEl f2 a2)
        (applyEl (Sup f1 f2) (Sup a1 a2))
        c-apply-sup le1 le2
  in Comp-down u (applyEl f1 a1) v hle1
       (Comp-sym v (applyEl f1 a1)
         (Comp-down v (applyEl f2 a2) (applyEl f1 a1) hle2
           (Comp-sym (applyEl f1 a1) (applyEl f2 a2) comp-apply)))

AppDom-sup : (X Y : Dom) (u v : FinEl) -> Comp u v ->
  AppWitness X Y u -> AppWitness X Y v ->
  AppWitness X Y (Sup u v)
AppDom-sup X Y u v comp
  (mkAppWitness cu f1 a1 hf1 ha1 hle1)
  (mkAppWitness cv f2 a2 hf2 ha2 hle2) =
  let cf1 = cohH X f1 hf1
      cf2 = cohH X f2 hf2
      ca1 = cohH Y a1 ha1
      ca2 = cohH Y a2 ha2
      compf = compH X f1 f2 hf1 hf2
      compa = compH Y a1 a2 ha1 ha2
      c-sup-f = Coherent-Sup f1 f2 compf cf1 cf2
      c-sup-a = Coherent-Sup a1 a2 compa ca1 ca2
      sf = Sup f1 f2
      sa = Sup a1 a2
      hf-sup = supH X f1 f2 compf hf1 hf2
      ha-sup = supH Y a1 a2 compa ha1 ha2
      le1 = applyEl-le-Sup-left  f1 f2 a1 a2 cf1 cf2 ca1 ca2 compf compa
      le2 = applyEl-le-Sup-right f1 f2 a1 a2 cf1 cf2 ca1 ca2 compf compa
      capply1 = Coherent-applyEl f1 a1 cf1 ca1
      capply2 = Coherent-applyEl f2 a2 cf2 ca2
      c-apply-sup = Coherent-applyEl sf sa c-sup-f c-sup-a
      chain1 = LeCode-trans u (applyEl f1 a1) (applyEl sf sa)
                 cu capply1 c-apply-sup hle1 le1
      chain2 = LeCode-trans v (applyEl f2 a2) (applyEl sf sa)
                 cv capply2 c-apply-sup hle2 le2
  in mkAppWitness (Coherent-Sup u v comp cu cv)
       sf sa hf-sup ha-sup
       (LeCode-Sup-lub u v (applyEl sf sa) chain1 chain2)

AppDom : Dom -> Dom -> Dom
holds (AppDom X Y) w = AppWitness X Y w
botH  (AppDom X Y) =
  mkAppWitness tt Bot Bot (botH X) (botH Y) tt
downH (AppDom X Y) u v cu le (mkAppWitness cv f a hf ha hle) =
  mkAppWitness cu f a hf ha
    (LeCode-trans u v (applyEl f a) cu cv
      (Coherent-applyEl f a (cohH X f hf) (cohH Y a ha)) le hle)
compH (AppDom X Y) u v hu hv = AppDom-comp X Y u v hu hv
supH  (AppDom X Y) u v comp hu hv = AppDom-sup X Y u v comp hu hv
cohH  (AppDom X Y) u (mkAppWitness cw _ _ _ _ _) = cw

------------------------------------------------------------------------
-- Section 4: Monotonicity lemmas
------------------------------------------------------------------------

AppDom-monotone-left : (X X' Y : Dom) -> LeDom X X' ->
  LeDom (AppDom X Y) (AppDom X' Y)
AppDom-monotone-left X X' Y le u (mkAppWitness cw f a hf ha hle) =
  mkAppWitness cw f a (le f hf) ha hle

AppDom-monotone-right : (X Y Y' : Dom) -> LeDom Y Y' ->
  LeDom (AppDom X Y) (AppDom X Y')
AppDom-monotone-right X Y Y' le u (mkAppWitness cw f a hf ha hle) =
  mkAppWitness cw f a hf (le a ha) hle
