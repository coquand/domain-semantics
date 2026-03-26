{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3Sigma.agda
--
-- Modular bundled validity: Val2 = HasType × Val2-Pi × Val2-Sigma.
-- Each type former contributes one independent component.
-- Transport functions compose per-component.
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity3Sigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ;
              FinFun ; List ; nil ; cons)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  Fst ; Snd ; MkPair ; subst1 ; wkExpr)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-conv ; ty-Fst ; ty-Snd ; ty-Sigma ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Fst)
open import SubstitutionLemmaSigma using (typing-ConvTm ; typing-WfCtx ;
  subst1-cong-ConvTm ; subst-HasType ; subst1-WtSub)
open import ReductionSigma using (Red ; mkRed ; HeadRed ; HeadRed-trans ;
  HeadRed-Fst ; HeadRed-Snd ; HeadRed-unique-Pi ;
  headred-refl ; headred-step)
open import PaperSemanticsSigma using (Coherent ; EvalFun ;
  CoherentFun ; CoherentFunTail ; cft-from-cf ;
  FinMem ; FinMemFun ; FinMemAllU ; FinMem-coh-u ;
  FinMem-a-in-U ; coh-from-aU ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  LeCode ; LeCode-refl ; Comp ; Sup ;
  finMem-upward ; finMemUCode-Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup)
open import ValiditySigma using (
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ;
  Red-unique-Pi ; Red-unique-Sigma ;
  bU-from-cf-fmU)

-- Import Validity2Sigma as the Pi+Sigma inner layer (Top at leaves)
import Validity2Sigma as V2

-- Re-export inner types for Pi (they use V2.Val2 in edges —
-- but we'll re-wrap at the Val2 level)
open V2 public using (
  ValTy2 ; EqValTy2 ;
  ValTyPi2 ; EqValTyPi2 ;
  ValPi2 ; EqValPi2 ;
  PiEdgeVal2 ; PiEdgeEq2 ; PiEdgeEqTy2 ;
  PiAppVal2 ; PiAppEq2 ; PiAppEqVal2 ;
  ValTySigma2 ; EqValTySigma2 ;
  SigmaEdgeVal2 ; SigmaEdgeEq2 ; SigmaEdgeEqTy2 ;
  ValPair2 ; EqValPair2 ;
  ValTy2-Sup ; EqValTy2-sym ;
  FinMem-Coherent)

------------------------------------------------------------------------
-- Outer layer: Val2 = Pair HasType V2.Val2
------------------------------------------------------------------------

Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Val2 G M A u a = Pair (HasType G M A) (V2.Val2 G M A u a)

EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EqVal2 G M N A u a = Pair (ConvTm G M N A) (V2.EqVal2 G M N A u a)

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

Val2-ht : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} -> Val2 G M A u a -> HasType G M A
Val2-ht = fst

EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} -> EqVal2 G M N A u a -> ConvTm G M N A
EqVal2-ct = fst

------------------------------------------------------------------------
-- Transport functions: delegate to V2, wrap HasType/ConvTm
------------------------------------------------------------------------

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} -> HasType G M A -> (a : FinEl) -> Val2 G M A Bot a
Val2-Bot ht a = mkSigma ht (V2.Val2-Bot a)

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} -> ConvTm G M N A -> (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot ct a = mkSigma ct (V2.EqVal2-Bot a)

Val2-transport-M : {n : Nat} {G : Ctx n} {M M' A : Expr n} {u a : FinEl} -> Eq M M' -> Val2 G M A u a -> Val2 G M' A u a
Val2-transport-M refl v = v

Val2-transport-A : {n : Nat} {G : Ctx n} {M A A' : Expr n} {u a : FinEl} -> Eq A A' -> Val2 G M A u a -> Val2 G M A' u a
Val2-transport-A refl v = v

EqVal2-transport-A : {n : Nat} {G : Ctx n} {M N A A' : Expr n} {u a : FinEl} -> Eq A A' -> EqVal2 G M N A u a -> EqVal2 G M N A' u a
EqVal2-transport-A refl v = v

Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n} (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
Val2-to-EqVal2 u a (mkSigma ht i) = mkSigma (conv-refl ht) (V2.Val2-to-EqVal2 u a i)

Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
Val2-from-EqVal2-first u a (mkSigma ct i) = mkSigma (fst (typing-ConvTm ct)) (V2.Val2-from-EqVal2-first u a i)

Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
Val2-from-EqVal2-second u a (mkSigma ct i) = mkSigma (snd (typing-ConvTm ct)) (V2.Val2-from-EqVal2-second u a i)

EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n} (u a : FinEl) -> Coherent u -> Coherent a -> EqVal2 G M N A u a -> EqVal2 G N M A u a
EqVal2-sym u a cu ca (mkSigma ct i) = mkSigma (conv-sym ct) (V2.EqVal2-sym u a cu ca i)

EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n} (u a : FinEl) -> Coherent u -> Coherent a -> EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a -> EqVal2 G M1 M3 A u a
EqVal2-trans u a cu ca (mkSigma c1 i1) (mkSigma c2 i2) = mkSigma (conv-trans c1 c2) (V2.EqVal2-trans u a cu ca i1 i2)

Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n} (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b -> ConvTm G C C' U -> HasType G C' U -> Val2 G M C u b -> Val2 G M C' u b
Val2-EqValTy2-fwd u b cb eqv cc hc (mkSigma ht i) = mkSigma (ty-conv ht cc hc) (V2.Val2-EqValTy2-fwd u b cb eqv i)

EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n} (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b -> ConvTm G C C' U -> HasType G C' U -> EqVal2 G M N C u b -> EqVal2 G M N C' u b
EqVal2-EqValTy2-fwd u b cb eqv cc hc (mkSigma ct i) = mkSigma (conv-conv ct cc hc) (V2.EqVal2-EqValTy2-fwd u b cb eqv i)

-- Val2-beta-expand, Val2-headred-contract, EqVal2-headred-expand:
-- These are defined in the Adequacy mutual block (Adequacy2Sigma/Adequacy3Sigma),
-- not in the Validity file. They will wrap V2's versions with HasType/ConvTm.

upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) -> LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 -> Val2 G M T u a0 -> ValTy2 G T a1 -> Val2 G M T u a1
upVal2 G M T u a0 a1 le m0 m1 c0 c1 (mkSigma ht i) vt = mkSigma ht (V2.upVal2 G M T u a0 a1 le m0 m1 c0 c1 i vt)

downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) -> LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode -> Val2 G M T u a1 -> Val2 G M T u a0
downVal2 G M T u a0 a1 le m0 c0 aU (mkSigma ht i) = mkSigma ht (V2.downVal2 G M T u a0 a1 le m0 c0 aU i)

restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) -> LeCode u' u -> FinMem u' a -> FinMem u a -> Val2 G M T u a -> Val2 G M T u' a
restrictVal2 G M T u u' a le m' m (mkSigma ht i) = mkSigma ht (V2.restrictVal2 G M T u u' a le m' m i)

upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) -> LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 -> EqVal2 G M N T u a0 -> ValTy2 G T a1 -> EqVal2 G M N T u a1
upEqVal2 G M N T u a0 a1 le m0 m1 c0 c1 (mkSigma ct i) vt = mkSigma ct (V2.upEqVal2 G M N T u a0 a1 le m0 m1 c0 c1 i vt)

downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) -> LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode -> EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
downEqVal2 G M N T u a0 a1 le m0 c0 aU (mkSigma ct i) = mkSigma ct (V2.downEqVal2 G M N T u a0 a1 le m0 c0 aU i)

restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) -> LeCode u' u -> FinMem u' a -> FinMem u a -> EqVal2 G M N T u a -> EqVal2 G M N T u' a
restrictEqVal2 G M N T u u' a le m' m (mkSigma ct i) = mkSigma ct (V2.restrictEqVal2 G M N T u u' a le m' m i)

-- ValTy2-Sup and EqValTy2-sym re-exported from V2 via public open
