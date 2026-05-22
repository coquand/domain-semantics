{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityMono.agda  (MIN/ — Pi + U fragment)
--
-- Phase 1 of the goodStage plan (NEXT_SESSION_GOODSTAGE.md): the
-- *monotonicity* property package, re-indexed by the stage n.
--
-- Structure (cleaner than "bundle everything and re-derive per stage"):
--   * MonoPack k : the 8 top-level monotonicity functions at Stage k.
--   * The Pi helper functions (downPiApp*, upPiApp*, transportPiEdge*,
--     restrictPiApp*, restrict*-PiCode) are NON-recursive combinators over
--     a MonoPack k, defined once.
--   * goodStage : (k) -> MonoPack k by induction on k.  goodStage (suc n)
--     builds the Stage-(suc n) functions: every recursion-into-a-smaller-
--     code becomes a projection of the IH (goodStage n), because at
--     Stage (suc n) the records (SR n) expose Stage-n relations.
--
-- No NO_POSITIVITY_CHECK, no postulates.
------------------------------------------------------------------------

module MIN.ValidityMono where

open import MIN.ValidityStratified

import MIN.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons )
import MIN.RawSyntax as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import MIN.TypingRules using (Ctx ; empty ; extend ;
  HasType ; ConvTm ;
  WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-App)
open import MIN.Reduction using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ;
  HeadRed-strip-Pi )
open import MIN.PaperSemantics using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-wf ; finMem-funel-coh ;
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
open import MIN.Selection using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import MIN.Validity using (Red-unique-Pi ;
  bU-from-cf-fmFun ;
  FinMem-Coherent)
open import MIN.SubstitutionLemma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Records at "Stage k level": OpenRecords instantiated at the Stage-k
-- relations.  These are exactly the records appearing inside Stage (suc k).
------------------------------------------------------------------------

module SR (k : Nat) = OpenRecords
  (Bundle.val (Stage k)) (Bundle.eqval (Stage k))
  (Bundle.valty (Stage k)) (Bundle.eqvalty (Stage k))

------------------------------------------------------------------------
-- Stage-level relation abbreviations
------------------------------------------------------------------------

Vl : (k : Nat) {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Vl k = Bundle.val (Stage k)

EVl : (k : Nat) {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EVl k = Bundle.eqval (Stage k)

VTy : (k : Nat) {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
VTy k = Bundle.valty (Stage k)

EVTy : (k : Nat) {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
EVTy k = Bundle.eqvalty (Stage k)

------------------------------------------------------------------------
-- Red3-unique-Pi (for ValidityStratified.Red3)
------------------------------------------------------------------------

Red3-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red3 G A (Pi B F) U -> Red3 G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red3-unique-Pi {G = G} {A} r1 r2 =
  Red-unique-Pi {G = G} {A} (mkRed (Red3.hr r1)) (mkRed (Red3.hr r2))

------------------------------------------------------------------------
-- MonoPack k: the 8 top-level monotonicity functions at Stage k
------------------------------------------------------------------------

record MonoPack (k : Nat) : Set1 where
  field
    downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
      Vl k G M T u a1 -> Vl k G M T u a0
    downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
      EVl k G M N T u a1 -> EVl k G M N T u a0
    downValTy2 : {n : Nat} (G : Ctx n) (M : Expr n) (u0 u1 : FinEl) ->
      LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
      VTy k G M u1 -> VTy k G M u0
    downEqValTy2 : {n : Nat} (G : Ctx n) (M N : Expr n) (u0 u1 : FinEl) ->
      LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
      EVTy k G M N u1 -> EVTy k G M N u0
    upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
      Vl k G M T u a0 -> VTy k G T a1 -> Vl k G M T u a1
    upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
      EVl k G M N T u a0 -> VTy k G T a1 -> EVl k G M N T u a1
    restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
      LeCode u' u -> FinMem u' a -> FinMem u a ->
      Vl k G M T u a -> Vl k G M T u' a
    restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
      LeCode u' u -> FinMem u' a -> FinMem u a ->
      EVl k G M N T u a -> EVl k G M N T u' a
    -- Non-recursive projection (cannot be defined uniformly in k because
    -- Stage k does not reduce for a variable k); supplied here so the Pi
    -- helpers can use it via `open MonoPack`.
    Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> EVl k G M N A u a -> Vl k G M A u a
    Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> EVl k G M N A u a -> Vl k G N A u a

------------------------------------------------------------------------
-- Pi helper combinators over a MonoPack k (all NON-recursive).
------------------------------------------------------------------------

downPiAppVal2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b1 f1 ->
  VTy k G A0 b1 ->
  SR.PiAppVal2 k G M A0 B0 b1 f1 g ->
  SR.PiAppVal2 k G M A0 B0 b0 f0 g
downPiAppVal2 k mp G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pav
  = \ u v sel N htN valN ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          lef0  = fst le
          lef1  = snd le
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
          val-b1 = upVal2 _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 valN vtAb1
          body  = pav u v sel N htN val-b1
          le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
          c-ef0 = Coherent-EvalFun f0 u cf0 cu
          ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
      in downVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body
  where open MonoPack mp

downPiAppEq2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b1 f1 ->
  VTy k G A0 b1 ->
  SR.PiAppEq2 k G M A0 B0 b1 f1 g ->
  SR.PiAppEq2 k G M A0 B0 b0 f0 g
downPiAppEq2 k mp G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pae
  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          lef0  = fst le
          lef1  = snd le
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
          eqN-b1 = upEqVal2 _ _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 eqN vtAb1
          body  = pae u v sel N1 N2 htN1 htN2 cvN eqN-b1
          le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
          c-ef0 = Coherent-EvalFun f0 u cf0 cu
          ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
      in downEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body
  where open MonoPack mp

downPiAppEqVal2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b1 f1 ->
  VTy k G A0 b1 ->
  SR.PiAppEqVal2 k G M N A0 B0 b1 f1 g ->
  SR.PiAppEqVal2 k G M N A0 B0 b0 f0 g
downPiAppEqVal2 k mp G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 paev
  = \ u v sel P htP valP ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          lef0  = fst le
          lef1  = snd le
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          fmu1  = finMem-upward u b0 b1 lef0 cb0 cb1 fmu0 b1U
          valP-b1 = upVal2 _ _ A0 u b0 b1 lef0 fmu0 fmu1 cb0 cb1 valP vtAb1
          body  = paev u v sel P htP valP-b1
          le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu lef1
          c-ef0 = Coherent-EvalFun f0 u cf0 cu
          ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
      in downEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body
  where open MonoPack mp

upPiAppVal2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  SR.PiEdgeVal2 k G A0 B0 b1 f1 ->
  SR.PiAppVal2 k G M A0 B0 b0 f0 g ->
  SR.PiAppVal2 k G M A0 B0 b1 f1 g
upPiAppVal2 k mp G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pav
  = \ u v sel N htN valN ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          valN-b0 = downVal2 _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U valN
          body  = pav u v sel N htN valN-b0
          le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
          c-ef0 = Coherent-EvalFun f0 u cf0 cu
          c-ef1 = Coherent-EvalFun f1 u cf1 cu
          fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
          ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
          valN-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valN
          vty-v1  = piEV1 u1 v1 sel1 N htN valN-u1
          vty-ef1 = Eq-transport (\ x -> VTy k G (subst1 B0 N) x) (Eq-sym eq-v1) vty-v1
      in upVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
           (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
           c-ef0 c-ef1 body vty-ef1
  where open MonoPack mp

upPiAppEq2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  SR.PiEdgeVal2 k G A0 B0 b1 f1 ->
  SR.PiAppEq2 k G M A0 B0 b0 f0 g ->
  SR.PiAppEq2 k G M A0 B0 b1 f1 g
upPiAppEq2 k mp G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pae
  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          eqN-b0  = downEqVal2 _ _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U eqN
          body    = pae u v sel N1 N2 htN1 htN2 cvN eqN-b0
          le-f    = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
          c-ef0   = Coherent-EvalFun f0 u cf0 cu
          c-ef1   = Coherent-EvalFun f1 u cf1 cu
          fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
          ef1U    = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          valN1-b1 = Val2-from-EqVal2-first u b1 eqN
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
          valN1-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valN1-b1
          vty-v1  = piEV1 u1 v1 sel1 N1 htN1 valN1-u1
          vty-ef1 = Eq-transport (\ x -> VTy k G (subst1 B0 N1) x) (Eq-sym eq-v1) vty-v1
      in upEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
           (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
           c-ef0 c-ef1 body vty-ef1
  where open MonoPack mp

upPiAppEqVal2 : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  SR.PiEdgeVal2 k G A0 B0 b1 f1 ->
  SR.PiAppEqVal2 k G M N A0 B0 b0 f0 g ->
  SR.PiAppEqVal2 k G M N A0 B0 b1 f1 g
upPiAppEqVal2 k mp G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 paev
  = \ u v sel P htP valP ->
      let ctg   = cft-from-cf g cg
          cu    = Coherent-Selection sel ctg
          fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
          valP-b0 = downVal2 _ _ A0 u b0 b1 (fst le) fmu0 cb0 b1U valP
          body    = paev u v sel P htP valP-b0
          le-f    = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
          c-ef0   = Coherent-EvalFun f0 u cf0 cu
          c-ef1   = Coherent-EvalFun f1 u cf1 cu
          fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
          ef1U    = EvalFun-in-UCode f1 u b1 cf1 cu allU1
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          fmu-b1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
          valP-u1 = restrictVal2 _ _ A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 valP
          vty-v1  = piEV1 u1 v1 sel1 P htP valP-u1
          vty-ef1 = Eq-transport (\ x -> VTy k G (subst1 B0 P) x) (Eq-sym eq-v1) vty-v1
      in upEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
           (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
           c-ef0 c-ef1 body vty-ef1
  where open MonoPack mp

transportPiEdgeVal2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
  FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
  FinMemAllU f1 b1 ->
  VTy k G A b1 ->
  SR.PiEdgeVal2 k G A B b1 f1 ->
  SR.PiEdgeVal2 k G A B b0 f0
transportPiEdgeVal2-sel k mp G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pev1
  = \ u v sel N htN valN ->
      let cu    = Coherent-Selection sel cf0
          fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
          fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
          valN-b1 = upVal2 _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 valN vtAb1
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          valN-u1 = restrictVal2 _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 valN-b1
          vt-v1   = pev1 u1 v1 sel1 N htN valN-u1
          vt-ef   = Eq-transport (\ x -> VTy k G (subst1 B N) x) (Eq-sym eq-v1) vt-v1
          le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
          le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
          fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
          v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                  (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
      in downValTy2 G (subst1 B N) v v1 le-v-v1 fmem-v-U v1U vt-v1
  where open MonoPack mp

transportPiEdgeEq2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
  FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
  FinMemAllU f1 b1 ->
  VTy k G A b1 ->
  SR.PiEdgeEq2 k G A B b1 f1 ->
  SR.PiEdgeEq2 k G A B b0 f0
transportPiEdgeEq2-sel k mp G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pee1
  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let cu    = Coherent-Selection sel cf0
          fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
          fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
          eqN-b1  = upEqVal2 _ _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 eqN vtAb1
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          eqN-u1  = restrictEqVal2 _ _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 eqN-b1
          eqt-v1  = pee1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqN-u1
          le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
          le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
          fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
          v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                  (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
      in downEqValTy2 G (subst1 B N1) (subst1 B N2) v v1 le-v-v1 fmem-v-U v1U eqt-v1
  where open MonoPack mp

transportPiEdgeEqTy2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
  FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
  FinMemAllU f1 b1 ->
  VTy k G A b1 ->
  SR.PiEdgeEqTy2 k G A B B' b1 f1 ->
  SR.PiEdgeEqTy2 k G A B B' b0 f0
transportPiEdgeEqTy2-sel k mp G A B B' b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pet1
  = \ u v sel P htP valP ->
      let cu    = Coherent-Selection sel cf0
          fmu0-b0 = FinMemAllU-Selection b0 sel allU0 cf0 cb0 b0U
          fmu0-b1 = finMem-upward u b0 b1 leb cb0 cb1 fmu0-b0 b1U
          valP-b1 = upVal2 _ _ A u b0 b1 leb fmu0-b0 fmu0-b1 cb0 cb1 valP vtAb1
          sb1   = selectionBelow f1 u cf1 cu
          u1    = fst sb1
          v1    = fst (snd sb1)
          sel1  = fst (snd (snd sb1))
          le-u1 = fst (snd (snd (snd sb1)))
          eq-v1 = snd (snd (snd (snd sb1)))
          fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
          valP-u1 = restrictVal2 _ _ A u u1 b1 le-u1 fmu1-b1 fmu0-b1 valP-b1
          eqt-v1  = pet1 u1 v1 sel1 P htP valP-u1
          le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
          le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
          fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
          v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                  (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
      in downEqValTy2 G (subst1 B P) (subst1 B' P) v v1 le-v-v1 fmem-v-U v1U eqt-v1
  where open MonoPack mp

restrictPiAppVal2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b : FinEl) (f g g' : FinFun) ->
  CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
  FinMemAllU f b -> FinMem b UCode ->
  LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
  SR.PiEdgeVal2 k G A0 B0 b f ->
  SR.PiAppVal2 k G M A0 B0 b f g -> SR.PiAppVal2 k G M A0 B0 b f g'
restrictPiAppVal2-sel k mp G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pav
  u' v' sel' N htN valN =
  let ctg      = cft-from-cf g cg
      ctg'     = cft-from-cf g' cg'
      cu'      = Coherent-Selection sel' ctg'
      fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
      sb       = selectionBelow g u' ctg cu'
      u_g      = fst sb
      v_g      = fst (snd sb)
      sel_g    = fst (snd (snd sb))
      le-ug    = fst (snd (snd (snd sb)))
      eq-vg    = snd (snd (snd (snd sb)))
      cu_g     = Coherent-Selection sel_g ctg
      fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
      valN-ug  = restrictVal2 _ _ A0 u' u_g b le-ug fmu_g fmu'-b valN
      body     = pav u_g v_g sel_g N htN valN-ug
      le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug   = Coherent-EvalFun f u_g cf cu_g
      c-efu'   = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
      efuU'    = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      sb-f     = selectionBelow f u' cf cu'
      u_f      = fst sb-f
      v_f      = fst (snd sb-f)
      sel_f    = fst (snd (snd sb-f))
      le-uf    = fst (snd (snd (snd sb-f)))
      eq-ef    = snd (snd (snd (snd sb-f)))
      fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
      valN-uf  = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valN
      vty-vf   = piEV u_f v_f sel_f N htN valN-uf
      vty-efu' = Eq-transport (\ x -> VTy k G (subst1 B0 N) x) (Eq-sym eq-ef) vty-vf
      body2    = upVal2 _ _ (subst1 B0 N) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                   fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
  in restrictVal2 _ _ (subst1 B0 N) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2
  where open MonoPack mp

restrictPiAppEq2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b : FinEl) (f g g' : FinFun) ->
  CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
  FinMemAllU f b -> FinMem b UCode ->
  LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
  SR.PiEdgeVal2 k G A0 B0 b f ->
  SR.PiAppEq2 k G M A0 B0 b f g -> SR.PiAppEq2 k G M A0 B0 b f g'
restrictPiAppEq2-sel k mp G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pae
  u' v' sel' N1 N2 htN1 htN2 cvN eqN =
  let ctg      = cft-from-cf g cg
      ctg'     = cft-from-cf g' cg'
      cu'      = Coherent-Selection sel' ctg'
      fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
      sb       = selectionBelow g u' ctg cu'
      u_g      = fst sb
      v_g      = fst (snd sb)
      sel_g    = fst (snd (snd sb))
      le-ug    = fst (snd (snd (snd sb)))
      eq-vg    = snd (snd (snd (snd sb)))
      cu_g     = Coherent-Selection sel_g ctg
      fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
      eqN-ug   = restrictEqVal2 _ _ _ A0 u' u_g b le-ug fmu_g fmu'-b eqN
      body     = pae u_g v_g sel_g N1 N2 htN1 htN2 cvN eqN-ug
      le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug   = Coherent-EvalFun f u_g cf cu_g
      c-efu'   = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
      efuU'    = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      valN1-b  = Val2-from-EqVal2-first u' b eqN
      sb-f     = selectionBelow f u' cf cu'
      u_f      = fst sb-f
      v_f      = fst (snd sb-f)
      sel_f    = fst (snd (snd sb-f))
      le-uf    = fst (snd (snd (snd sb-f)))
      eq-ef    = snd (snd (snd (snd sb-f)))
      fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
      valN1-uf = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valN1-b
      vty-vf   = piEV u_f v_f sel_f N1 htN1 valN1-uf
      vty-efu' = Eq-transport (\ x -> VTy k G (subst1 B0 N1) x) (Eq-sym eq-ef) vty-vf
      body2    = upEqVal2 _ _ _ (subst1 B0 N1) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                   fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
  in restrictEqVal2 _ _ _ (subst1 B0 N1) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2
  where open MonoPack mp

restrictPiAppEqVal2-sel : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b : FinEl) (f g g' : FinFun) ->
  CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
  FinMemAllU f b -> FinMem b UCode ->
  LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
  SR.PiEdgeVal2 k G A0 B0 b f ->
  SR.PiAppEqVal2 k G M N A0 B0 b f g -> SR.PiAppEqVal2 k G M N A0 B0 b f g'
restrictPiAppEqVal2-sel k mp G M N A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV paev
  u' v' sel' P htP valP =
  let ctg      = cft-from-cf g cg
      ctg'     = cft-from-cf g' cg'
      cu'      = Coherent-Selection sel' ctg'
      fmu'-b   = FinMem-Selection b f sel' fmg' ctg' cb bU
      sb       = selectionBelow g u' ctg cu'
      u_g      = fst sb
      v_g      = fst (snd sb)
      sel_g    = fst (snd (snd sb))
      le-ug    = fst (snd (snd (snd sb)))
      eq-vg    = snd (snd (snd (snd sb)))
      cu_g     = Coherent-Selection sel_g ctg
      fmu_g    = FinMem-Selection b f sel_g fmg ctg cb bU
      valP-ug  = restrictVal2 _ _ A0 u' u_g b le-ug fmu_g fmu'-b valP
      body     = paev u_g v_g sel_g P htP valP-ug
      le-ef    = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug   = Coherent-EvalFun f u_g cf cu_g
      c-efu'   = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg ctg cf allU
      efuU'    = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      sb-f     = selectionBelow f u' cf cu'
      u_f      = fst sb-f
      v_f      = fst (snd sb-f)
      sel_f    = fst (snd (snd sb-f))
      le-uf    = fst (snd (snd (snd sb-f)))
      eq-ef    = snd (snd (snd (snd sb-f)))
      fmu_f-b  = FinMemAllU-Selection b sel_f allU cf cb bU
      valP-uf  = restrictVal2 _ _ A0 u' u_f b le-uf fmu_f-b fmu'-b valP
      vty-vf   = piEV u_f v_f sel_f P htP valP-uf
      vty-efu' = Eq-transport (\ x -> VTy k G (subst1 B0 P) x) (Eq-sym eq-ef) vty-vf
      body2    = upEqVal2 _ _ _ (subst1 B0 P) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                   fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
  in restrictEqVal2 _ _ _ (subst1 B0 P) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2
  where open MonoPack mp

restrictVal2-PiCode : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M T : Expr n) (g g' : FinFun)
  (b : FinEl) (f : FinFun) ->
  CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
  LeFunCode g' g ->
  Pair (FinMemFun g' b f) (CoherentFun g') ->
  SR.RValTyPi k G T b f ->
  SR.RValPi k G M T g b f ->
  SR.RValPi k G M T g' b f
restrictVal2-PiCode k mp G M T g g' b f cf cb allU bU le mem' vtyT vpiM =
  let cg'  = snd mem'
      fmg' = fst mem'
      uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vtyT)
      piEV : SR.PiEdgeVal2 k G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f
      piEV = Eq-transport (\ Y -> SR.PiEdgeVal2 k G (RValPi.domA0 vpiM) Y b f) (Eq-sym (snd uniq))
               (Eq-transport (\ X -> SR.PiEdgeVal2 k G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
  in record
    { domA0 = RValPi.domA0 vpiM
    ; codB0 = RValPi.codB0 vpiM
    ; red   = RValPi.red vpiM
    ; cohG  = cg'
    ; fmG   = fmg'
    ; appV  = restrictPiAppVal2-sel k mp G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appV vpiM)
    ; appE  = restrictPiAppEq2-sel k mp G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appE vpiM)
    }
  where open SR k

restrictEqVal2-PiCode : (k : Nat) (mp : MonoPack k) {n : Nat} (G : Ctx n) (M N T : Expr n) (g g' : FinFun)
  (b : FinEl) (f : FinFun) ->
  CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
  LeFunCode g' g ->
  Pair (FinMemFun g' b f) (CoherentFun g') ->
  SR.RValTyPi k G T b f ->
  SR.REqValPi k G M N T g b f ->
  SR.REqValPi k G M N T g' b f
restrictEqVal2-PiCode k mp G M N T g g' b f cf cb allU bU le mem' vtyT epi =
  let cg'  = snd mem'
      fmg' = fst mem'
      uniq = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vtyT)
      piEV : SR.PiEdgeVal2 k G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f
      piEV = Eq-transport (\ Y -> SR.PiEdgeVal2 k G (REqValPi.domA0 epi) Y b f) (Eq-sym (snd uniq))
               (Eq-transport (\ X -> SR.PiEdgeVal2 k G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
  in record
    { domA0 = REqValPi.domA0 epi
    ; codB0 = REqValPi.codB0 epi
    ; red   = REqValPi.red epi
    ; cohG  = cg'
    ; fmG   = fmg'
    ; appEV = restrictPiAppEqVal2-sel k mp G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f g g' cf (REqValPi.cohG epi) cg' cb allU
                bU le fmg' (REqValPi.fmG epi) piEV (REqValPi.appEV epi)
    }
  where open SR k

------------------------------------------------------------------------
-- goodStage : the property package at every stage, by induction on k.
------------------------------------------------------------------------

goodStage : (k : Nat) -> MonoPack k
goodStage zero = record
  { downVal2       = \ G M T u a0 a1 le mem ca0 ca1 src -> tt
  ; downEqVal2     = \ G M N T u a0 a1 le mem ca0 ca1 src -> tt
  ; downValTy2     = \ G M u0 u1 le fm0 fm1 src -> tt
  ; downEqValTy2   = \ G M N u0 u1 le fm0 fm1 src -> tt
  ; upVal2         = \ G M T u a0 a1 le m0 m1 c0 c1 src vt -> tt
  ; upEqVal2       = \ G M N T u a0 a1 le m0 m1 c0 c1 src vt -> tt
  ; restrictVal2   = \ G M T u u' a le m fm src -> tt
  ; restrictEqVal2 = \ G M N T u u' a le m fm src -> tt
  ; Val2-from-EqVal2-first = \ u a ev -> tt
  ; Val2-from-EqVal2-second = \ u a ev -> tt
  }
goodStage (suc n) = record
  { downVal2 = dV ; downEqVal2 = dEV ; downValTy2 = dVT ; downEqValTy2 = dEVT
  ; upVal2 = uV ; upEqVal2 = uEV ; restrictVal2 = rV ; restrictEqVal2 = rEV
  ; Val2-from-EqVal2-first = vfe1 ; Val2-from-EqVal2-second = vfe2
  }
  where
    ih : MonoPack n
    ih = goodStage n
    open SR n
    ihdVT  = MonoPack.downValTy2 ih
    ihdEVT = MonoPack.downEqValTy2 ih

    dV : {m : Nat} (G : Ctx m) (M T : Expr m) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
      Vl (suc n) G M T u a1 -> Vl (suc n) G M T u a0
    dEV : {m : Nat} (G : Ctx m) (M N T : Expr m) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
      EVl (suc n) G M N T u a1 -> EVl (suc n) G M N T u a0
    dVT : {m : Nat} (G : Ctx m) (M : Expr m) (u0 u1 : FinEl) ->
      LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
      VTy (suc n) G M u1 -> VTy (suc n) G M u0
    dEVT : {m : Nat} (G : Ctx m) (M N : Expr m) (u0 u1 : FinEl) ->
      LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
      EVTy (suc n) G M N u1 -> EVTy (suc n) G M N u0
    uV : {m : Nat} (G : Ctx m) (M T : Expr m) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
      Vl (suc n) G M T u a0 -> VTy (suc n) G T a1 -> Vl (suc n) G M T u a1
    uEV : {m : Nat} (G : Ctx m) (M N T : Expr m) (u a0 a1 : FinEl) ->
      LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
      EVl (suc n) G M N T u a0 -> VTy (suc n) G T a1 -> EVl (suc n) G M N T u a1
    rV : {m : Nat} (G : Ctx m) (M T : Expr m) (u u' a : FinEl) ->
      LeCode u' u -> FinMem u' a -> FinMem u a ->
      Vl (suc n) G M T u a -> Vl (suc n) G M T u' a
    rEV : {m : Nat} (G : Ctx m) (M N T : Expr m) (u u' a : FinEl) ->
      LeCode u' u -> FinMem u' a -> FinMem u a ->
      EVl (suc n) G M N T u a -> EVl (suc n) G M N T u' a
    vfe1 : {m : Nat} {G : Ctx m} {M N A : Expr m}
      (u a : FinEl) -> EVl (suc n) G M N A u a -> Vl (suc n) G M A u a
    vfe2 : {m : Nat} {G : Ctx m} {M N A : Expr m}
      (u a : FinEl) -> EVl (suc n) G M N A u a -> Vl (suc n) G N A u a

    -- downVal2
    dV G M T u Bot          a1             le mem ca0 ca1 src = tt
    dV G M T u UCode        Bot            ()
    dV G M T u UCode        UCode          le mem ca0 ca1 src = src
    dV G M T u UCode        (FunEl h)      ()
    dV G M T u UCode        (PiCode b f)   ()
    dV G M T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
    dV G M T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
    dV G M T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
    dV G M T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
    dV G M T u (PiCode b0 f0) Bot          ()
    dV G M T u (PiCode b0 f0) UCode        ()
    dV G M T u (PiCode b0 f0) (FunEl h)    ()
    dV G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
    dV G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
    dV G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
      let vty  = fst src
          vpiM = snd src
          fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
          cf0   = snd ca0
          cb0   = fst ca0
          b1U   = finMem-piU-dom b1 f1 ca1
          cb1   = coh-from-aU b1 b1U
          allU1 = finMem-piU-allU b1 f1 ca1
          b0U   = finMem-piU-dom b0 f0 fmem-pf
          allU0 = finMem-piU-allU b0 f0 fmem-pf
          vty'  = dVT G T (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
          vtAb1 : VTy n G (RValPi.domA0 vpiM) b1
          vtAb1 = Eq-transport (\ X -> VTy n G X b1) (Eq-sym (fst (Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vty))))
                     (RValTyPi.valA vty)
          vpi' = record
            { domA0 = RValPi.domA0 vpiM
            ; codB0 = RValPi.codB0 vpiM
            ; red   = RValPi.red vpiM
            ; cohG  = RValPi.cohG vpiM
            ; fmG   = finMem-funel-fun g b0 f0 mem
            ; appV  = downPiAppVal2 n ih G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (finMem-funel-fun g b0 f0 mem)
                        cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appV vpiM)
            ; appE  = downPiAppEq2 n ih G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (finMem-funel-fun g b0 f0 mem)
                        cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appE vpiM)
            }
      in mkSigma vty' vpi'
    dV G M T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()

    -- downEqVal2
    dEV G M N T u Bot          a1             le mem ca0 ca1 src = tt
    dEV G M N T u UCode        Bot            ()
    dEV G M N T u UCode        UCode          le mem ca0 ca1 src = src
    dEV G M N T u UCode        (FunEl h)      ()
    dEV G M N T u UCode        (PiCode b f)   ()
    dEV G M N T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
    dEV G M N T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
    dEV G M N T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
    dEV G M N T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
    dEV G M N T u (PiCode b0 f0) Bot          ()
    dEV G M N T u (PiCode b0 f0) UCode        ()
    dEV G M N T u (PiCode b0 f0) (FunEl h)    ()
    dEV G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
    dEV G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
    dEV G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
      let vty   = fst src
          vpiM  = fst (snd src)
          vpiN  = fst (snd (snd src))
          epi   = snd (snd (snd src))
          fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
          cf0   = snd ca0
          cb0   = fst ca0
          b1U   = finMem-piU-dom b1 f1 ca1
          cb1   = coh-from-aU b1 b1U
          allU1 = finMem-piU-allU b1 f1 ca1
          b0U   = finMem-piU-dom b0 f0 fmem-pf
          allU0 = finMem-piU-allU b0 f0 fmem-pf
          vtAb1 : VTy n G (REqValPi.domA0 epi) b1
          vtAb1 = Eq-transport (\ X -> VTy n G X b1) (Eq-sym (fst (Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vty))))
                     (RValTyPi.valA vty)
          valM  = mkSigma vty vpiM
          valN  = mkSigma vty vpiN
          valM' = dV G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
          valN' = dV G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
          epi'  = record
            { domA0 = REqValPi.domA0 epi
            ; codB0 = REqValPi.codB0 epi
            ; red   = REqValPi.red epi
            ; cohG  = REqValPi.cohG epi
            ; fmG   = finMem-funel-fun g b0 f0 mem
            ; appEV = downPiAppEqVal2 n ih G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (REqValPi.cohG epi) (finMem-funel-fun g b0 f0 mem)
                        cb0 cb1 b1U b0U allU0 allU1 le (REqValPi.fmG epi) vtAb1 (REqValPi.appEV epi)
            }
      in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
    dEV G M N T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()

    -- downValTy2
    dVT G M Bot          u1             le fmem cu1 src = tt
    dVT G M UCode        Bot            ()
    dVT G M UCode        UCode          le fmem cu1 src = src
    dVT G M UCode        (FunEl h)      ()
    dVT G M UCode        (PiCode b f)   ()
    dVT G M (FunEl g)    u1             le ()
    dVT G M (PiCode b0 f0) Bot          ()
    dVT G M (PiCode b0 f0) UCode        ()
    dVT G M (PiCode b0 f0) (FunEl h)    ()
    dVT G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
      let fmem-b0  = finMem-piU-dom b0 f0 fmem
          fmemAll0 = finMem-piU-allU b0 f0 fmem
          sat0     = finMem-piU-cft b0 f0 fmem
          cu1-b1   = finMem-piU-dom b1 f1 cu1
          cb1   = coh-from-aU b1 cu1-b1
          cb0   = coh-from-aU b0 fmem-b0
          vtA-b1 = RValTyPi.valA src
          vtA-b0 = ihdVT G (RValTyPi.domA src) b0 b1 (fst le) fmem-b0 cu1-b1 vtA-b1
          piEV0  = transportPiEdgeVal2-sel n ih G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                     cb0 cb1 cu1-b1 fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeV src)
          piEE0  = transportPiEdgeEq2-sel n ih G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                     cb0 cb1 cu1-b1 fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeE src)
      in record
        { domA   = RValTyPi.domA src
        ; codB   = RValTyPi.codB src
        ; red    = RValTyPi.red src
        ; cohF   = sat0
        ; fmAllU = fmemAll0
        ; htA    = RValTyPi.htA src
        ; htB    = RValTyPi.htB src
        ; valA   = vtA-b0
        ; edgeV  = piEV0
        ; edgeE  = piEE0
        }

    -- downEqValTy2
    dEVT G M N Bot          u1             le fmem cu1 src = tt
    dEVT G M N UCode        Bot            ()
    dEVT G M N UCode        UCode          le fmem cu1 src = src
    dEVT G M N UCode        (FunEl h)      ()
    dEVT G M N UCode        (PiCode b f)   ()
    dEVT G M N (FunEl g)    u1             le ()
    dEVT G M N (PiCode b0 f0) Bot          ()
    dEVT G M N (PiCode b0 f0) UCode        ()
    dEVT G M N (PiCode b0 f0) (FunEl h)    ()
    dEVT G M N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
      let vtyM1  = fst src
          vtyN1  = fst (snd src)
          core   = snd (snd src)
          fmem-b0  = finMem-piU-dom b0 f0 fmem
          fmemAll0 = finMem-piU-allU b0 f0 fmem
          sat0     = finMem-piU-cft b0 f0 fmem
          cu1-b1   = finMem-piU-dom b1 f1 cu1
          cb1   = coh-from-aU b1 cu1-b1
          cb0   = coh-from-aU b0 fmem-b0
          uniqM  = Red3-unique-Pi (RValTyPi.red vtyM1) (REqValTyPi.redM core)
          eqAMA  = fst uniqM
          vtA-b1 = Eq-transport (\ X -> VTy n G X b1) eqAMA (RValTyPi.valA vtyM1)
          eqvty0  = ihdEVT G (REqValTyPi.domA core) (REqValTyPi.domA' core) b0 b1 (fst le) fmem-b0 cu1-b1 (REqValTyPi.eqA core)
          piEEqT0 = transportPiEdgeEqTy2-sel n ih G (REqValTyPi.domA core) (REqValTyPi.codB core) (REqValTyPi.codB' core) b0 f0 b1 f1
                      cb0 cb1 cu1-b1 fmem-b0 (fst le) (snd le) fmemAll0 sat0 (REqValTyPi.cohF core) (REqValTyPi.fmAllU core) vtA-b1 (REqValTyPi.edgeET core)
          vtyM0  = dVT G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
          vtyN0  = dVT G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
          core0  = record
            { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
            ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
            ; redM = REqValTyPi.redM core ; redN = REqValTyPi.redN core
            ; cohF = sat0 ; fmAllU = fmemAll0
            ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
            ; eqA = eqvty0 ; edgeET = piEEqT0
            }
      in mkSigma vtyM0 (mkSigma vtyN0 core0)

    -- upVal2
    uV G M T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T UCode        Bot a1 le ()
    uV G M T (FunEl g)    Bot a1 le ()
    uV G M T (PiCode a f) Bot a1 le ()
    uV G M T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T (FunEl g')     UCode UCode le ()
    uV G M T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T u UCode Bot          ()
    uV G M T u UCode (FunEl h)    ()
    uV G M T u UCode (PiCode b h) ()
    uV G M T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T UCode          (FunEl g) a1             le ()
    uV G M T (FunEl g')     (FunEl g) a1             le ()
    uV G M T (PiCode a' f') (FunEl g) a1             le ()
    uV G M T u (PiCode b0 f0) Bot       ()
    uV G M T u (PiCode b0 f0) UCode     ()
    uV G M T u (PiCode b0 f0) (FunEl h) ()
    uV G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
    uV G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
    uV G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
      let vty  = fst src
          vpiM = snd src
          cf0  = snd ca0
          cf1  = snd ca1
          pf0  = finMem-funel-wf g b0 f0 mem0
          pf1  = finMem-funel-wf g b1 f1 mem1
          b0U  = finMem-piU-dom b0 f0 pf0
          b1U  = finMem-piU-dom b1 f1 pf1
          allU0 = finMem-piU-allU b0 f0 pf0
          allU1 = finMem-piU-allU b1 f1 pf1
          cb0  = coh-from-aU b0 b0U
          cb1  = coh-from-aU b1 b1U
          uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vta1)
          piEV1 : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b1 f1
          piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b1 f1) (Eq-sym (snd uniq))
                    (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
          vpi' = record
            { domA0 = RValPi.domA0 vpiM
            ; codB0 = RValPi.codB0 vpiM
            ; red   = RValPi.red vpiM
            ; cohG  = RValPi.cohG vpiM
            ; fmG   = finMem-funel-fun g b1 f1 mem1
            ; appV  = upPiAppVal2 n ih G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                        (finMem-funel-fun g b0 f0 mem0) piEV1 (RValPi.appV vpiM)
            ; appE  = upPiAppEq2 n ih G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                        (finMem-funel-fun g b0 f0 mem0) piEV1 (RValPi.appE vpiM)
            }
      in mkSigma vta1 vpi'
    uV G M T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()

    -- upEqVal2
    uEV G M N T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T UCode        Bot a1 le ()
    uEV G M N T (FunEl g)    Bot a1 le ()
    uEV G M N T (PiCode a f) Bot a1 le ()
    uEV G M N T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T (FunEl g')     UCode UCode le ()
    uEV G M N T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T u UCode Bot          ()
    uEV G M N T u UCode (FunEl h)    ()
    uEV G M N T u UCode (PiCode b h) ()
    uEV G M N T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T UCode          (FunEl g) a1             le ()
    uEV G M N T (FunEl g')     (FunEl g) a1             le ()
    uEV G M N T (PiCode a' f') (FunEl g) a1             le ()
    uEV G M N T u (PiCode b0 f0) Bot       ()
    uEV G M N T u (PiCode b0 f0) UCode     ()
    uEV G M N T u (PiCode b0 f0) (FunEl h) ()
    uEV G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
    uEV G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
    uEV G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
      let vty  = fst src
          vpiM = fst (snd src)
          vpiN = fst (snd (snd src))
          epi  = snd (snd (snd src))
          cf0   = snd ca0
          cf1   = snd ca1
          pf0   = finMem-funel-wf g b0 f0 mem0
          pf1   = finMem-funel-wf g b1 f1 mem1
          b0U   = finMem-piU-dom b0 f0 pf0
          b1U   = finMem-piU-dom b1 f1 pf1
          allU0 = finMem-piU-allU b0 f0 pf0
          allU1 = finMem-piU-allU b1 f1 pf1
          cb0   = coh-from-aU b0 b0U
          cb1   = coh-from-aU b1 b1U
          uniq  = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vta1)
          piEV1 : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b1 f1
          piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b1 f1) (Eq-sym (snd uniq))
                    (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
          valM   = mkSigma vty vpiM
          valN   = mkSigma vty vpiN
          valM'  = uV G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
          valN'  = uV G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
          epi'   = record
            { domA0 = REqValPi.domA0 epi
            ; codB0 = REqValPi.codB0 epi
            ; red   = REqValPi.red epi
            ; cohG  = REqValPi.cohG epi
            ; fmG   = finMem-funel-fun g b1 f1 mem1
            ; appEV = upPiAppEqVal2 n ih G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 cf1 (REqValPi.cohG epi) cb0 cb1 b1U allU1 b0U allU0 le
                        (finMem-funel-fun g b0 f0 mem0) piEV1 (REqValPi.appEV epi)
            }
      in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
    uEV G M N T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()

    -- restrictVal2
    rV G M T u u' Bot          le mem fmu src = src
    rV G M T Bot Bot UCode        le mem fmu src = src
    rV G M T Bot UCode UCode      ()
    rV G M T Bot (FunEl _) UCode  ()
    rV G M T Bot (PiCode _ _) UCode ()
    rV G M T UCode Bot UCode        le mem fmu src = tt
    rV G M T UCode UCode UCode      le mem fmu src = src
    rV G M T UCode (FunEl _) UCode  ()
    rV G M T UCode (PiCode _ _) UCode ()
    rV G M T (FunEl g) Bot UCode    le mem fmu src = tt
    rV G M T (FunEl g) UCode UCode  ()
    rV G M T (FunEl g) (FunEl g') UCode le mem fmu src =
      dVT G M (FunEl g') (FunEl g) le mem fmu src
    rV G M T (FunEl g) (PiCode _ _) UCode ()
    rV G M T (PiCode a' f') Bot UCode le mem fmu src = tt
    rV G M T (PiCode a' f') UCode UCode ()
    rV G M T (PiCode a' f') (FunEl _) UCode ()
    rV G M T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu src =
      mkSigma (fst src) (dVT G M (PiCode a2 f2) (PiCode a' f') le mem fmu (snd src))
    rV G M T u u' (FunEl h)    le mem fmu src = src
    rV G M T Bot Bot            (PiCode b f) le mem fmu src = src
    rV G M T Bot UCode          (PiCode b f) le ()
    rV G M T Bot (FunEl g')     (PiCode b f) ()
    rV G M T Bot (PiCode a2 f2) (PiCode b f) le ()
    rV G M T UCode Bot            (PiCode b f) le mem fmu src = src
    rV G M T UCode UCode          (PiCode b f) le mem fmu src = src
    rV G M T UCode (FunEl g')     (PiCode b f) le mem ()
    rV G M T UCode (PiCode a2 f2) (PiCode b f) le ()
    rV G M T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
    rV G M T (FunEl g) UCode          (PiCode b f) le ()
    rV G M T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
      let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
      in mkSigma (fst src)
           (restrictVal2-PiCode n ih G M T g g' b f (finMem-piU-cft b f aU) (coh-from-aU b (finMem-piU-dom b f aU))
             (finMem-piU-allU b f aU) (finMem-piU-dom b f aU) le (mkSigma (finMem-funel-fun g' b f mem) (finMem-funel-coh g' b f mem)) (fst src) (snd src))
    rV G M T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
    rV G M T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
    rV G M T (PiCode a1 f1) UCode          (PiCode b f) le ()
    rV G M T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
    rV G M T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src

    -- restrictEqVal2
    rEV G M N T u u' Bot          le mem fmu src = src
    rEV G M N T Bot Bot UCode        le mem fmu src = src
    rEV G M N T Bot UCode UCode     ()
    rEV G M N T Bot (FunEl _) UCode ()
    rEV G M N T Bot (PiCode _ _) UCode ()
    rEV G M N T UCode Bot UCode le mem fmu src = tt
    rEV G M N T UCode UCode UCode le mem fmu src = src
    rEV G M N T UCode (FunEl _) UCode ()
    rEV G M N T UCode (PiCode _ _) UCode ()
    rEV G M N T (FunEl g) Bot UCode le mem fmu src = tt
    rEV G M N T (FunEl g) UCode UCode ()
    rEV G M N T (FunEl g) (FunEl g') UCode le mem fmu src = tt
    rEV G M N T (FunEl g) (PiCode _ _) UCode ()
    rEV G M N T (PiCode a' f') Bot UCode le mem fmu src = tt
    rEV G M N T (PiCode a' f') UCode UCode ()
    rEV G M N T (PiCode a' f') (FunEl _) UCode ()
    rEV G M N T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu (mkSigma vtA (mkSigma vtM (mkSigma vtN eqvt))) =
      mkSigma vtA
        (mkSigma (dVT G M (PiCode a2 f2) (PiCode a' f') le mem fmu vtM)
          (mkSigma (dVT G N (PiCode a2 f2) (PiCode a' f') le mem fmu vtN)
            (dEVT G M N (PiCode a2 f2) (PiCode a' f') le mem fmu eqvt)))
    rEV G M N T u u' (FunEl h)    le mem fmu src = src
    rEV G M N T Bot Bot            (PiCode b f) le mem fmu src = src
    rEV G M N T Bot UCode          (PiCode b f) le ()
    rEV G M N T Bot (FunEl g')     (PiCode b f) ()
    rEV G M N T Bot (PiCode a2 f2) (PiCode b f) le ()
    rEV G M N T UCode Bot            (PiCode b f) le mem fmu src = src
    rEV G M N T UCode UCode          (PiCode b f) le mem fmu src = src
    rEV G M N T UCode (FunEl g')     (PiCode b f) le mem ()
    rEV G M N T UCode (PiCode a2 f2) (PiCode b f) le ()
    rEV G M N T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
    rEV G M N T (FunEl g) UCode          (PiCode b f) le ()
    rEV G M N T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
      let aU    = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
          valM  = mkSigma (fst src) (fst (snd src))
          valN  = mkSigma (fst src) (fst (snd (snd src)))
          epi   = snd (snd (snd src))
          valM' = rV G M T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valM
          valN' = rV G N T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valN
          epi'  = restrictEqVal2-PiCode n ih G M N T g g' b f (finMem-piU-cft b f aU) (coh-from-aU b (finMem-piU-dom b f aU))
                    (finMem-piU-allU b f aU) (finMem-piU-dom b f aU) le (mkSigma (finMem-funel-fun g' b f mem) (finMem-funel-coh g' b f mem)) (fst src) epi
      in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
    rEV G M N T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
    rEV G M N T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
    rEV G M N T (PiCode a1 f1) UCode          (PiCode b f) le ()
    rEV G M N T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
    rEV G M N T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src

    -- Val2-from-EqVal2-first
    vfe1 u Bot ev = tt
    vfe1 Bot UCode ev = tt
    vfe1 Bot (FunEl h) ev = tt
    vfe1 Bot (PiCode b f) ev = tt
    vfe1 UCode UCode ev = mkSigma (fst ev) (fst (snd ev))
    vfe1 (FunEl g) UCode ev = tt
    vfe1 (PiCode a f) UCode ev = mkSigma (fst ev) (fst (snd ev))
    vfe1 UCode (FunEl h) ev = tt
    vfe1 (FunEl g) (FunEl h) ev = tt
    vfe1 (PiCode a f) (FunEl h) ev = tt
    vfe1 UCode (PiCode b f) ev = tt
    vfe1 (PiCode a' f') (PiCode b f) ev = tt
    vfe1 (FunEl g) (PiCode b f) ev = mkSigma (fst ev) (fst (snd ev))

    vfe2 u Bot ev = tt
    vfe2 Bot UCode ev = tt
    vfe2 Bot (FunEl h) ev = tt
    vfe2 Bot (PiCode b f) ev = tt
    vfe2 UCode UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
    vfe2 (FunEl g) UCode ev = tt
    vfe2 (PiCode a f) UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
    vfe2 UCode (FunEl h) ev = tt
    vfe2 (FunEl g) (FunEl h) ev = tt
    vfe2 (PiCode a f) (FunEl h) ev = tt
    vfe2 UCode (PiCode b f) ev = tt
    vfe2 (PiCode a' f') (PiCode b f) ev = tt
    vfe2 (FunEl g) (PiCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
