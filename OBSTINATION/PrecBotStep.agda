{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotStep
--
-- Primitive recursion at an INCOMPLETE finite first argument:
--   f = prec g h  satisfies ultimate obstination at  cons (bot n) Y,
-- for every n and Y  (min1.pdf p.2: "le cas ou x est fini est une
-- recurrence directe sur x").
--
-- The step (c -> suc c) dispatches h's obstination case at the inner
-- point  B = cons (bot c) (cons v1 Y)  (v1 = the extension value of the
-- recursion restriction Fc at Y) and routes each case to a witness
-- builder:
--
--   h Case1                      -> f Case1                (PrecBotCase1)
--   h Case2 at coord 0           -> f Case2 at coord 0     (hval-coord0)
--   h Case2 at coord 1           -> f Case2 at coord 0     (base-const flattens Fc)
--   h Case2 at a Y-coord         -> f Case2 at that coord  (hval-Ycoord-Case2)
--   h Case3 at coord 0           -> impossible (bot c /= inf)
--   h Case3 at coord 1           -> impossible (base-const vs Fc-increasing)
--   h Case3 at a Y-coord         -> f Case3 at that coord  (hval-Ycoord-Case3)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotStep where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (embed-inj)
open import OBSTINATION.CompCase3Helpers using (bot-not-inf)
open import OBSTINATION.PrecBot using (prop1-prec-bot)
open import OBSTINATION.PrecBotEngine using (FcFun ; FcConst ; unshift-bot)
open import OBSTINATION.PrecBotReach using (fc-v1 ; fc-reach)
open import OBSTINATION.PrecBotCase1 using (prec-bot-Case1)
open import OBSTINATION.PrecBotCase23 using (prec-bot-Case2-coord0)
open import OBSTINATION.PrecBotHval using
  (hval-coord0 ; hval-Ycoord-Case2 ; hval-Ycoord-Case3)
open import OBSTINATION.PrecBotCoord1 using (hval-coord1-Case2)
open import OBSTINATION.PrecBotCoord1C using (coord1-Case3-absurd)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

------------------------------------------------------------------------
-- Extracting the target incomplete value from IncompleteFinite.
------------------------------------------------------------------------

inc-fin-bot : (d : D) -> IncompleteFinite d -> Sigma Nat (\ m -> Eq d (bot m))
inc-fin-bot (bot m) _  = mkSigma m refl
inc-fin-bot (cpl m) ()
inc-fin-bot inf     ()

------------------------------------------------------------------------
-- Routing h's Case 2 at the inner point.
------------------------------------------------------------------------

module _ (rd : RecData) (c : Nat) (Y : Tup)
  (o : Or (UO (FcFun rd c) Y) (FcConst rd c Y)) where

  open RecData rd

  private
    v1 = fc-v1 rd c Y o
    reach = fc-reach rd c Y o

  route-uo2 : (A0H : FTup) -> Below A0H (cons (bot c) (cons v1 Y)) ->
    (mh i : Nat) -> LeN (suc i) (length A0H) -> IncompleteFinite (get i (cons (bot c) (cons v1 Y))) ->
    Eq (embed (getF i A0H)) (get i (cons (bot c) (cons v1 Y))) ->
    ((X : FTup) -> Eq (length X) (length A0H) -> Eq (getF i X) (getF i A0H) ->
       LeFTup (del i A0H) (del i X) -> Eq (H X) (fbot mh)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  route-uo2 nil                       () mh i irange incompl eqinv univH
  route-uo2 (cons a0 nil)             belA0H mh i irange incompl eqinv univH =
    Empty-elim (snd belA0H)
  -- coordinate 0
  route-uo2 (cons a0 (cons a1 A0Ht)) belA0H mh zero irange incompl eqinv univH =
    let hc = hval-coord0 rd c mh Y v1 reach (cons a0 (cons a1 A0Ht)) belA0H eqinv univH
    in prec-bot-Case2-coord0 rd c mh Y (fst hc) (fst (snd hc)) (snd (snd hc))
  -- coordinate 1 (recursion result) -> base-const flattens Fc -> Case 2 at coord 0
  route-uo2 (cons a0 (cons a1 A0Ht)) belA0H mh (suc zero) irange incompl eqinv univH =
    hval-coord1-Case2 rd c mh m' Y o veq a0 A0Ht (fst belA0H) (snd (snd belA0H)) univH'
    where
      ifb = inc-fin-bot v1 incompl
      m'  = fst ifb
      veq : Eq v1 (bot m')
      veq = snd ifb
      a1eq : Eq a1 (fbot m')
      a1eq = embed-inj {a1} {fbot m'} (Eq-trans eqinv veq)
      univH' : (Z : FTup) -> Eq (length Z) (suc (suc (length A0Ht))) ->
               Eq (getF (suc zero) Z) (fbot m') ->
               LeFTup (cons a0 A0Ht) (del (suc zero) Z) -> Eq (H Z) (fbot mh)
      univH' Z lenZ coordZ delZ = univH Z lenZ (Eq-trans coordZ (Eq-sym a1eq)) delZ
  -- a Y-coordinate
  route-uo2 (cons a0 (cons a1 B0t)) belA0H mh (suc (suc j)) irange incompl eqinv univH =
    hval-Ycoord-Case2 rd c mh j Y v1 reach a0 a1 B0t
      (fst belA0H) (fst (snd belA0H)) (snd (snd belA0H))
      irange incompl eqinv univH

  route-uo3 : (A0H : FTup) -> Below A0H (cons (bot c) (cons v1 Y)) ->
    (i : Nat) -> Eq (get i (cons (bot c) (cons v1 Y))) inf ->
    (k : Nat) -> Eq (getF i A0H) (fbot k) -> (phi : Nat -> Nat) -> PhiOK k phi ->
    ((X : FTup) (m : Nat) -> Eq (length X) (length A0H) -> LeN k m ->
       Eq (getF i X) (fbot m) -> LeFTup (del i A0H) (del i X) -> Eq (H X) (fbot (phi m))) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  route-uo3 nil                       () i eqinf k eqA0 phi phiok univH
  route-uo3 (cons a0 nil)             belA0H i eqinf k eqA0 phi phiok univH =
    Empty-elim (snd belA0H)
  -- coordinate 0 : bot c /= inf
  route-uo3 (cons a0 (cons a1 A0Ht)) belA0H zero eqinf k eqA0 phi phiok univH =
    Empty-elim (bot-not-inf eqinf)
  -- coordinate 1 : impossible (base-const vs Fc increasing)
  route-uo3 (cons a0 (cons a1 A0Ht)) belA0H (suc zero) eqinf k eqA0 phi phiok univH =
    Empty-elim (coord1-Case3-absurd rd c k Y o eqinf a0 k phi A0Ht
      (fst belA0H) (snd (snd belA0H)) univH)
  -- a Y-coordinate
  route-uo3 (cons a0 (cons a1 B0t)) belA0H (suc (suc j)) eqinf k eqA0 phi phiok univH =
    hval-Ycoord-Case3 rd c j k phi Y v1 reach a0 a1 B0t
      (fst belA0H) (fst (snd belA0H)) (snd (snd belA0H))
      eqinf eqA0 phiok univH

------------------------------------------------------------------------
-- The step, and the full incomplete-finite-argument theorem.
------------------------------------------------------------------------

module _ (rd : RecData) where
  open RecData rd

  prec-bot-step : (c : Nat) (Y : Tup) ->
    UO (PF G H) (cons (bot c) Y) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  prec-bot-step c Y ih with unshift-bot rd c Y ih
  ... | o with uoh (cons (bot c) (cons (fc-v1 rd c Y o) Y))
  ...        | uo1 (mkSigma B0 (mkSigma belB0 (mkSigma m univG))) =
               prec-bot-Case1 rd c Y (fc-v1 rd c Y o) (fc-reach rd c Y o) B0 belB0 m univG
  ...        | uo2 (mkSigma A0H (mkSigma belA0H (mkSigma mh (mkSigma i
               (mkSigma irange (mkSigma incompl (mkSigma eqinv univH))))))) =
               route-uo2 rd c Y o A0H belA0H mh i irange incompl eqinv univH
  ...        | uo3 (mkSigma A0H (mkSigma belA0H (mkSigma i (mkSigma eqinf
               (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univH)))))))) =
               route-uo3 rd c Y o A0H belA0H i eqinf k eqA0 phi phiok univH

  prop1-prec-bot-all : (n : Nat) (Y : Tup) -> UO (PF G H) (cons (bot n) Y)
  prop1-prec-bot-all zero    Y = prop1-prec-bot rd Y
  prop1-prec-bot-all (suc c) Y =
    prec-bot-step c Y (prop1-prec-bot-all c Y)
