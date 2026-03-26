{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3.agda
--
-- Test: bundled validity with full paper bundling.
-- Val2 bundles HasType, EqVal2 bundles ConvTm.
-- No Prop, no Sigma — minimal test for the design.
--
-- Based on Validity2.agda but with:
--   Val2 at leaf codes = HasType G M A (not Top)
--   EqVal2 at leaf codes = ConvTm G M N A (not Top)
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity3 where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons)
open import PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; Comp ; EvalFun ;
  FinMem ; FinMemFun ; FinMemAllU ;
  CoherentFunTail ; coh-from-aU ;
  Coherent-EvalFun)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1)
open import TypingRules using (Ctx ; empty ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-conv ; conv-refl ; conv-sym ; conv-trans ; conv-conv)
open import Reduction using (Red ; mkRed ; Red-hr ; HeadRed ;
  headred-refl ; headred-step)
open import Validity using (
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ;
  Red-unique-Pi)

------------------------------------------------------------------------
-- Mutual definitions
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Val2: HasType at leaves, structured at UCode / FunEl+PiCode
  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set

  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

  ValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

  EqValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinFun -> Set

  ValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  EqValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    Expr (suc n) -> FinEl -> FinFun -> Set

  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  --------------------------------------------------------------------
  -- Val2: HasType G M A at leaves
  --------------------------------------------------------------------

  Val2 G M A u Bot              = HasType G M A
  Val2 G M A Bot UCode          = HasType G M A
  Val2 G M A UCode UCode        = Pair (HasType G M A) (ValTy2 G M UCode)
  Val2 G M A (FunEl g) UCode    = Pair (HasType G M A) (ValTy2 G M (FunEl g))
  Val2 G M A (PiCode a' f') UCode = Pair (HasType G M A) (ValTy2 G M (PiCode a' f'))
  Val2 G M A PropCode UCode     = HasType G M A
  Val2 G M A (PiCode a' f') PropCode = Pair (HasType G M A) (ValTy2 G M (PiCode a' f'))
  Val2 G M A Bot PropCode       = HasType G M A
  Val2 G M A UCode PropCode     = HasType G M A
  Val2 G M A PropCode PropCode  = HasType G M A
  Val2 G M A (FunEl g) PropCode = HasType G M A
  Val2 G M A u (FunEl h)        = HasType G M A
  Val2 G M A Bot            (PiCode b f) = HasType G M A
  Val2 G M A UCode          (PiCode b f) = HasType G M A
  Val2 G M A PropCode       (PiCode b f) = HasType G M A
  Val2 G M A (FunEl g)      (PiCode b f) =
    Pair (HasType G M A)
         (Pair (ValTy2 G A (PiCode b f)) (ValPi2 G M A g b f))
  Val2 G M A (PiCode a' f') (PiCode b f) = HasType G M A

  --------------------------------------------------------------------
  -- EqVal2: ConvTm G M N A at leaves
  --------------------------------------------------------------------

  EqVal2 G M N A u Bot              = ConvTm G M N A
  EqVal2 G M N A Bot UCode          = ConvTm G M N A
  EqVal2 G M N A UCode UCode        =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode)))
  EqVal2 G M N A (FunEl g) UCode    =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (FunEl g)) (Pair (ValTy2 G N (FunEl g)) (EqValTy2 G M N (FunEl g))))
  EqVal2 G M N A (PiCode a' f') UCode =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A PropCode UCode    = ConvTm G M N A
  EqVal2 G M N A (PiCode a' f') PropCode =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A Bot PropCode      = ConvTm G M N A
  EqVal2 G M N A UCode PropCode    = ConvTm G M N A
  EqVal2 G M N A PropCode PropCode = ConvTm G M N A
  EqVal2 G M N A (FunEl g) PropCode = ConvTm G M N A
  EqVal2 G M N A u (FunEl h)       = ConvTm G M N A
  EqVal2 G M N A Bot            (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A UCode          (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A PropCode       (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A (FunEl g)      (PiCode b f) =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G A (PiCode b f))
               (Pair (ValPi2 G M A g b f)
                     (Pair (ValPi2 G N A g b f)
                           (EqValPi2 G M N A g b f))))
  EqVal2 G M N A (PiCode a' f') (PiCode b f) = ConvTm G M N A

  --------------------------------------------------------------------
  -- ValTy2 / EqValTy2: unchanged
  --------------------------------------------------------------------

  ValTy2 G M Bot          = Top
  ValTy2 G M UCode        = Top
  ValTy2 G M PropCode     = Top
  ValTy2 G M (FunEl g)    = Top
  ValTy2 G M (PiCode b f) = ValTyPi2 G M b f

  EqValTy2 G M N Bot          = Top
  EqValTy2 G M N UCode        = Top
  EqValTy2 G M N PropCode     = Top
  EqValTy2 G M N (FunEl g)    = Top
  EqValTy2 G M N (PiCode b f) =
    Pair (ValTyPi2 G M b f)
         (Pair (ValTyPi2 G N b f)
               (EqValTyPi2 G M N b f))

  --------------------------------------------------------------------
  -- Pi structures: unchanged from Validity2
  --------------------------------------------------------------------

  ValTyPi2 {n} G M b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red G M (Pi A B) U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (HasType G A U) \ _ ->
    Sigma (HasType (extend G A) B U) \ _ ->
    Pair (ValTy2 G A b)
         (Pair (PiEdgeVal2 G A B b f)
               (PiEdgeEq2 G A B b f))

  EqValTyPi2 {n} G M N b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Expr n) \ A' ->
    Sigma (Expr (suc n)) \ B' ->
    Sigma (Red G M (Pi A B) U) \ _ ->
    Sigma (Red G N (Pi A' B') U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (ConvTm G A A' U) \ _ ->
    Sigma (ConvTm (extend G A) B B' U) \ _ ->
    Pair (EqValTy2 G A A' b)
         (PiEdgeEqTy2 G A B B' b f)

  ValPi2 {n} G M A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    Pair (PiAppVal2 G M A0 B0 b f g)
         (PiAppEq2 G M A0 B0 b f g)

  EqValPi2 {n} G M N A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    PiAppEqVal2 G M N A0 B0 b f g

  PiEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
    ValTy2 G (subst1 B N) v

  PiEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
    EqValTy2 G (subst1 B N1) (subst1 B N2) v

  PiEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> Val2 G P A u b ->
    EqValTy2 G (subst1 B P) (subst1 B' P) v

  PiAppVal2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N : Expr n) -> HasType G N A0 -> Val2 G N A0 u b ->
    Val2 G (App M N) (subst1 B0 N) v (EvalFun f u)

  PiAppEq2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
    ConvTm G N1 N2 A0 -> EqVal2 G N1 N2 A0 u b ->
    EqVal2 G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)

  PiAppEqVal2 {n} G M N A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (P : Expr n) -> HasType G P A0 -> Val2 G P A0 u b ->
    EqVal2 G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)

------------------------------------------------------------------------
-- Test: Val2-Bot
------------------------------------------------------------------------

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  HasType G M A -> (a : FinEl) -> Val2 G M A Bot a
Val2-Bot ht Bot          = ht
Val2-Bot ht UCode        = ht
Val2-Bot ht PropCode     = ht
Val2-Bot ht (FunEl h)    = ht
Val2-Bot ht (PiCode b f) = ht

------------------------------------------------------------------------
-- Test: EqVal2-Bot
------------------------------------------------------------------------

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  ConvTm G M N A -> (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot ct Bot          = ct
EqVal2-Bot ct UCode        = ct
EqVal2-Bot ct PropCode     = ct
EqVal2-Bot ct (FunEl h)    = ct
EqVal2-Bot ct (PiCode b f) = ct

------------------------------------------------------------------------
-- Design validated: Val2 bundles HasType, EqVal2 bundles ConvTm.
-- The core mutual definitions compile.
-- Full transport functions (Val2-to-EqVal2, EqVal2-sym, etc.) to be added.
------------------------------------------------------------------------
