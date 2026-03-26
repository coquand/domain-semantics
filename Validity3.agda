{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3.agda
--
-- Two-layer bundled validity: Val2 = Pair HasType Val2c
-- where Val2c = Validity2.Val2 (structural content, Top at leaves).
--
-- No Prop, no Sigma. Minimal test for the modular design.
-- 0 postulates.
------------------------------------------------------------------------

module Validity3 where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun)
open import RawSyntax using (Expr ; U ; Pi ; subst1)
open import TypingRules using (Ctx ; extend ;
  HasType ; ConvTm ;
  ty-conv ; conv-refl ; conv-sym ; conv-trans ; conv-conv)
open import Reduction using (HeadRed ; headred-refl)
open import SubstitutionLemma using (typing-ConvTm)
open import PaperSemantics using (Coherent ; EvalFun ; FinMem ;
  LeCode ; coh-from-aU ; FinMem-a-in-U ; Coherent-EvalFun ;
  Comp ; Sup ; finMemUCode-Sup ; Coherent-Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  finMem-upward ; FinMem-coh-u ;
  CoherentFunTail ; cft-from-cf)

-- Import Validity2 as the inner layer
import Validity2 as V2
open V2 using () renaming (
  Val2 to Val2c ; EqVal2 to EqVal2c ;
  ValTy2 to ValTy2c ; EqValTy2 to EqValTy2c ;
  Val2-Bot to Val2c-Bot ; EqVal2-Bot to EqVal2c-Bot ;
  Val2-to-EqVal2 to Val2c-to-EqVal2c ;
  Val2-from-EqVal2-first to Val2c-from-first ;
  Val2-from-EqVal2-second to Val2c-from-second ;
  EqVal2-sym to EqVal2c-sym ;
  EqVal2-trans to EqVal2c-trans ;
  Val2-transport-M to Val2c-transport-M ;
  Val2-transport-A to Val2c-transport-A ;
  EqVal2-transport-A to EqVal2c-transport-A ;
  Val2-EqValTy2-fwd to Val2c-EqValTy2-fwd ;
  EqVal2-EqValTy2-fwd to EqVal2c-EqValTy2-fwd ;
  Val2-beta-expand to Val2c-beta-expand ;
  Val2-headred-contract to Val2c-headred-contract ;
  EqVal2-headred-expand to EqVal2c-headred-expand ;
  upVal2 to upVal2c ; downVal2 to downVal2c ; restrictVal2 to restrictVal2c ;
  upEqVal2 to upEqVal2c ; downEqVal2 to downEqVal2c ; restrictEqVal2 to restrictEqVal2c ;
  ValTy2-Sup to ValTy2c-Sup ; EqValTy2-sym to EqValTy2c-sym)

-- Re-export inner types unchanged
open V2 public using (
  ValTy2 ; EqValTy2 ;
  ValTyPi2 ; EqValTyPi2 ;
  ValPi2 ; EqValPi2 ;
  PiEdgeVal2 ; PiEdgeEq2 ; PiEdgeEqTy2 ;
  PiAppVal2 ; PiAppEq2 ; PiAppEqVal2)

------------------------------------------------------------------------
-- Outer layer: Val2 = Pair HasType Val2c
------------------------------------------------------------------------

Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Val2 G M A u a = Pair (HasType G M A) (Val2c G M A u a)

EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EqVal2 G M N A u a = Pair (ConvTm G M N A) (EqVal2c G M N A u a)

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

Val2-ht : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} ->
  Val2 G M A u a -> HasType G M A
Val2-ht = fst

EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
  EqVal2 G M N A u a -> ConvTm G M N A
EqVal2-ct = fst

------------------------------------------------------------------------
-- Bot
------------------------------------------------------------------------

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  HasType G M A -> (a : FinEl) -> Val2 G M A Bot a
Val2-Bot ht a = mkSigma ht (Val2c-Bot a)

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  ConvTm G M N A -> (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot ct a = mkSigma ct (EqVal2c-Bot a)

------------------------------------------------------------------------
-- Diagonal embedding
------------------------------------------------------------------------

Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
Val2-to-EqVal2 u a (mkSigma ht inner) =
  mkSigma (conv-refl ht) (Val2c-to-EqVal2c u a inner)

------------------------------------------------------------------------
-- Extraction from EqVal2
------------------------------------------------------------------------

Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
Val2-from-EqVal2-first u a (mkSigma ct inner) =
  mkSigma (fst (typing-ConvTm ct)) (Val2c-from-first u a inner)

Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
Val2-from-EqVal2-second u a (mkSigma ct inner) =
  mkSigma (snd (typing-ConvTm ct)) (Val2c-from-second u a inner)

------------------------------------------------------------------------
-- Symmetry / Transitivity
------------------------------------------------------------------------

EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal2 G M N A u a -> EqVal2 G N M A u a
EqVal2-sym u a cu ca (mkSigma ct inner) =
  mkSigma (conv-sym ct) (EqVal2c-sym u a cu ca inner)

EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a -> EqVal2 G M1 M3 A u a
EqVal2-trans u a cu ca (mkSigma ct1 i1) (mkSigma ct2 i2) =
  mkSigma (conv-trans ct1 ct2) (EqVal2c-trans u a cu ca i1 i2)

------------------------------------------------------------------------
-- Transport
------------------------------------------------------------------------

Val2-transport-M : {n : Nat} {G : Ctx n} {M M' A : Expr n}
  {u a : FinEl} -> Eq M M' -> Val2 G M A u a -> Val2 G M' A u a
Val2-transport-M refl v = v

Val2-transport-A : {n : Nat} {G : Ctx n} {M A A' : Expr n}
  {u a : FinEl} -> Eq A A' -> Val2 G M A u a -> Val2 G M A' u a
Val2-transport-A refl v = v

EqVal2-transport-A : {n : Nat} {G : Ctx n} {M N A A' : Expr n}
  {u a : FinEl} -> Eq A A' -> EqVal2 G M N A u a -> EqVal2 G M N A' u a
EqVal2-transport-A refl v = v

------------------------------------------------------------------------
-- Type conversion
------------------------------------------------------------------------

Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
  ConvTm G C C' U -> HasType G C' U ->
  Val2 G M C u b -> Val2 G M C' u b
Val2-EqValTy2-fwd u b cb eqv convCC' htC' (mkSigma ht inner) =
  mkSigma (ty-conv ht convCC' htC') (Val2c-EqValTy2-fwd u b cb eqv inner)

EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
  ConvTm G C C' U -> HasType G C' U ->
  EqVal2 G M N C u b -> EqVal2 G M N C' u b
EqVal2-EqValTy2-fwd u b cb eqv convCC' htC' (mkSigma ct inner) =
  mkSigma (conv-conv ct convCC' htC') (EqVal2c-EqValTy2-fwd u b cb eqv inner)

------------------------------------------------------------------------
-- Beta-expand / headred-contract
------------------------------------------------------------------------

Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
  (u a : FinEl) -> HeadRed M' M -> ConvTm G M' M T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-beta-expand u a hr ct (mkSigma ht inner) =
  mkSigma (fst (typing-ConvTm ct)) (Val2c-beta-expand u a hr inner)

Val2-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
  (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-headred-contract u a hr ct (mkSigma ht inner) =
  mkSigma (snd (typing-ConvTm ct)) (Val2c-headred-contract u a hr inner)

EqVal2-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
  (u a : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
  ConvTm G M1' M1 T -> ConvTm G M2' M2 T ->
  EqVal2 G M1 M2 T u a -> EqVal2 G M1' M2' T u a
EqVal2-headred-expand u a hr1 hr2 ct1 ct2 (mkSigma ct inner) =
  mkSigma (conv-trans ct1 (conv-trans ct (conv-sym ct2)))
          (EqVal2c-headred-expand u a hr1 hr2 inner)

------------------------------------------------------------------------
-- Monotonicity (up/down/restrict) — delegate to inner layer
------------------------------------------------------------------------

upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
  Coherent a0 -> Coherent a1 ->
  Val2 G M T u a0 -> ValTy2 G T a1 -> Val2 G M T u a1
upVal2 G M T u a0 a1 le fm0 fm1 ca0 ca1 (mkSigma ht inner) vty =
  mkSigma ht (upVal2c G M T u a0 a1 le fm0 fm1 ca0 ca1 inner vty)

downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  Val2 G M T u a1 -> Val2 G M T u a0
downVal2 G M T u a0 a1 le fm0 ca0 a1U (mkSigma ht inner) =
  mkSigma ht (downVal2c G M T u a0 a1 le fm0 ca0 a1U inner)

restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  Val2 G M T u a -> Val2 G M T u' a
restrictVal2 G M T u u' a le fm' fm (mkSigma ht inner) =
  mkSigma ht (restrictVal2c G M T u u' a le fm' fm inner)

upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
  Coherent a0 -> Coherent a1 ->
  EqVal2 G M N T u a0 -> ValTy2 G T a1 -> EqVal2 G M N T u a1
upEqVal2 G M N T u a0 a1 le fm0 fm1 ca0 ca1 (mkSigma ct inner) vty =
  mkSigma ct (upEqVal2c G M N T u a0 a1 le fm0 fm1 ca0 ca1 inner vty)

downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u : FinEl) (a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
downEqVal2 G M N T u a0 a1 le fm0 ca0 a1U (mkSigma ct inner) =
  mkSigma ct (downEqVal2c G M N T u a0 a1 le fm0 ca0 a1U inner)

restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  EqVal2 G M N T u a -> EqVal2 G M N T u' a
restrictEqVal2 G M N T u u' a le fm' fm (mkSigma ct inner) =
  mkSigma ct (restrictEqVal2c G M N T u u' a le fm' fm inner)

------------------------------------------------------------------------
-- ValTy2-Sup / EqValTy2-sym — pass through from inner layer
------------------------------------------------------------------------

ValTy2-Sup : {n : Nat} (G : Ctx n) (T : Expr n)
  (a0 a1 : FinEl) -> Comp a0 a1 ->
  FinMem a0 UCode -> FinMem a1 UCode ->
  ValTy2 G T a0 -> ValTy2 G T a1 ->
  ValTy2 G T (Sup a0 a1)
ValTy2-Sup = ValTy2c-Sup

EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
  (u : FinEl) -> Coherent u ->
  EqValTy2 G M N u -> EqValTy2 G N M u
EqValTy2-sym = EqValTy2c-sym
