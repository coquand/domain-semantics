{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3Sigma.agda
--
-- Full paper bundling:
--   Val2 G M A u a = Sigma (HasType G M A) (Sigma (ValTy2 G A a) (V2.Val2 ...))
--   EqVal2 G M N A u a = Sigma (ConvTm G M N A) (Sigma (ValTy2 G A a) (V2.EqVal2 ...))
--
-- ValTy2 G A a gives type validity at the type level — crucially,
-- at (SigmaCode b f) it provides SigmaEdgeEq2 needed for EqVal2-sym.
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity3Sigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ;
              FinFun)
open import RawSyntaxSigma using (Expr ; U ; Pi ; subst1 ; Fst ; Snd)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; extend ;
  HasType ; ConvTm ;
  ty-conv ; ty-Fst ; ty-Snd ; ty-Sigma ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Fst)
open import SubstitutionLemmaSigma using (typing-ConvTm ; typing-WfCtx ;
  subst1-cong-ConvTm ; subst-HasType ; subst1-WtSub)
open import ReductionSigma using (HeadRed ; HeadRed-Fst ; HeadRed-Snd ;
  headred-refl)
open import PaperSemanticsSigma using (Coherent ; EvalFun ;
  FinMem ; LeCode ; Comp ; Sup ;
  Coherent-EvalFun ; coh-from-aU)

import Validity2Sigma as V2

-- Re-export inner types
open V2 public using (
  ValTy2 ; EqValTy2 ;
  ValTyPi2 ; EqValTyPi2 ; ValPi2 ; EqValPi2 ;
  PiEdgeVal2 ; PiEdgeEq2 ; PiEdgeEqTy2 ;
  PiAppVal2 ; PiAppEq2 ; PiAppEqVal2 ;
  ValTySigma2 ; EqValTySigma2 ;
  SigmaEdgeVal2 ; SigmaEdgeEq2 ; SigmaEdgeEqTy2 ;
  ValPair2 ; EqValPair2 ;
  ValTy2-Sup ; EqValTy2-sym ;
  FinMem-Coherent)

------------------------------------------------------------------------
-- Outer layer: Val2 = HasType × ValTy2 × V2.Val2
------------------------------------------------------------------------

Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Val2 G M A u a = Sigma (HasType G M A) \ _ -> Sigma (ValTy2 G A a) \ _ -> V2.Val2 G M A u a

EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EqVal2 G M N A u a = Sigma (ConvTm G M N A) \ _ -> Sigma (ValTy2 G A a) \ _ -> V2.EqVal2 G M N A u a

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

Val2-ht : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} -> Val2 G M A u a -> HasType G M A
Val2-ht v = fst v

Val2-vty : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} -> Val2 G M A u a -> ValTy2 G A a
Val2-vty v = fst (snd v)

Val2-inner : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} -> Val2 G M A u a -> V2.Val2 G M A u a
Val2-inner v = snd (snd v)

EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} -> EqVal2 G M N A u a -> ConvTm G M N A
EqVal2-ct v = fst v

EqVal2-vty : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} -> EqVal2 G M N A u a -> ValTy2 G A a
EqVal2-vty v = fst (snd v)

EqVal2-inner : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} -> EqVal2 G M N A u a -> V2.EqVal2 G M N A u a
EqVal2-inner v = snd (snd v)

------------------------------------------------------------------------
-- Transport: delegate to V2, wrap HasType/ConvTm/ValTy2
------------------------------------------------------------------------

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  HasType G M A -> (a : FinEl) -> ValTy2 G A a -> Val2 G M A Bot a
Val2-Bot ht a vty = mkSigma ht (mkSigma vty (V2.Val2-Bot a))

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  ConvTm G M N A -> (a : FinEl) -> ValTy2 G A a -> EqVal2 G M N A Bot a
EqVal2-Bot ct a vty = mkSigma ct (mkSigma vty (V2.EqVal2-Bot a))

Val2-transport-M : {n : Nat} {G : Ctx n} {M M' A : Expr n} {u a : FinEl} ->
  Eq M M' -> Val2 G M A u a -> Val2 G M' A u a
Val2-transport-M refl v = v

Val2-transport-A : {n : Nat} {G : Ctx n} {M A A' : Expr n} {u a : FinEl} ->
  Eq A A' -> Val2 G M A u a -> Val2 G M A' u a
Val2-transport-A refl v = v

EqVal2-transport-A : {n : Nat} {G : Ctx n} {M N A A' : Expr n} {u a : FinEl} ->
  Eq A A' -> EqVal2 G M N A u a -> EqVal2 G M N A' u a
EqVal2-transport-A refl v = v

Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n} (u a : FinEl) ->
  Val2 G M A u a -> EqVal2 G M M A u a
Val2-to-EqVal2 u a (mkSigma ht (mkSigma vty i)) =
  mkSigma (conv-refl ht) (mkSigma vty (V2.Val2-to-EqVal2 u a i))

Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) ->
  EqVal2 G M N A u a -> Val2 G M A u a
Val2-from-EqVal2-first u a (mkSigma ct (mkSigma vty i)) =
  mkSigma (fst (typing-ConvTm ct)) (mkSigma vty (V2.Val2-from-EqVal2-first u a i))

Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) ->
  EqVal2 G M N A u a -> Val2 G N A u a
Val2-from-EqVal2-second u a (mkSigma ct (mkSigma vty i)) =
  mkSigma (snd (typing-ConvTm ct)) (mkSigma vty (V2.Val2-from-EqVal2-second u a i))

EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) ->
  Coherent u -> Coherent a ->
  EqVal2 G M N A u a -> EqVal2 G N M A u a
EqVal2-sym u a cu ca (mkSigma ct (mkSigma vty i)) =
  mkSigma (conv-sym ct) (mkSigma vty (V2.EqVal2-sym u a cu ca i))

EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n} (u a : FinEl) ->
  Coherent u -> Coherent a ->
  EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a -> EqVal2 G M1 M3 A u a
EqVal2-trans u a cu ca (mkSigma c1 (mkSigma v1 i1)) (mkSigma c2 (mkSigma v2 i2)) =
  mkSigma (conv-trans c1 c2) (mkSigma v1 (V2.EqVal2-trans u a cu ca i1 i2))

Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n} (u b : FinEl) ->
  Coherent b -> EqValTy2 G C C' b ->
  ConvTm G C C' U -> HasType G C' U -> ValTy2 G C' b ->
  Val2 G M C u b -> Val2 G M C' u b
Val2-EqValTy2-fwd u b cb eqv cc hc vty' (mkSigma ht (mkSigma vty i)) =
  mkSigma (ty-conv ht cc hc) (mkSigma vty' (V2.Val2-EqValTy2-fwd u b cb eqv i))

EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n} (u b : FinEl) ->
  Coherent b -> EqValTy2 G C C' b ->
  ConvTm G C C' U -> HasType G C' U -> ValTy2 G C' b ->
  EqVal2 G M N C u b -> EqVal2 G M N C' u b
EqVal2-EqValTy2-fwd u b cb eqv cc hc vty' (mkSigma ct (mkSigma vty i)) =
  mkSigma (conv-conv ct cc hc) (mkSigma vty' (V2.EqVal2-EqValTy2-fwd u b cb eqv i))

upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
  Val2 G M T u a0 -> ValTy2 G T a1 -> Val2 G M T u a1
upVal2 G M T u a0 a1 le m0 m1 c0 c1 (mkSigma ht (mkSigma vty0 i)) vty1 =
  mkSigma ht (mkSigma vty1 (V2.upVal2 G M T u a0 a1 le m0 m1 c0 c1 i vty1))

downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  ValTy2 G T a0 ->
  Val2 G M T u a1 -> Val2 G M T u a0
downVal2 G M T u a0 a1 le m0 c0 aU vty0 (mkSigma ht (mkSigma vty1 i)) =
  mkSigma ht (mkSigma vty0 (V2.downVal2 G M T u a0 a1 le m0 c0 aU i))

restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  Val2 G M T u a -> Val2 G M T u' a
restrictVal2 G M T u u' a le m' m (mkSigma ht (mkSigma vty i)) =
  mkSigma ht (mkSigma vty (V2.restrictVal2 G M T u u' a le m' m i))

upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
  EqVal2 G M N T u a0 -> ValTy2 G T a1 -> EqVal2 G M N T u a1
upEqVal2 G M N T u a0 a1 le m0 m1 c0 c1 (mkSigma ct (mkSigma vty0 i)) vty1 =
  mkSigma ct (mkSigma vty1 (V2.upEqVal2 G M N T u a0 a1 le m0 m1 c0 c1 i vty1))

downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  ValTy2 G T a0 ->
  EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
downEqVal2 G M N T u a0 a1 le m0 c0 aU vty0 (mkSigma ct (mkSigma vty1 i)) =
  mkSigma ct (mkSigma vty0 (V2.downEqVal2 G M N T u a0 a1 le m0 c0 aU i))

restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  EqVal2 G M N T u a -> EqVal2 G M N T u' a
restrictEqVal2 G M N T u u' a le m' m (mkSigma ct (mkSigma vty i)) =
  mkSigma ct (mkSigma vty (V2.restrictEqVal2 G M N T u u' a le m' m i))
