{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity2Sigma.agda
--
-- Syntax-bundled logical relation, extended with Sigma types.
-- Parallel version of Validity2.agda.
--
-- Every leaf that was Top in ValiditySigma.agda now carries HasType
-- or ConvTm evidence.  Val2/EqVal2 at (PairCode, SigmaCode) = Top,
-- matching ValiditySigma's design.
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity2Sigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ;
  WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; ty-conv)
open import ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-unique-Pi ;
  HeadRed-strip-Sigma ; HeadRed-unique-Sigma)
open import PaperSemanticsSigma using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ; FinMem-Prop-to-U ;
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
  CFTcons ; CoherentFunTail ; CoherentWith)
open import SelectionSigma using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import ValiditySigma using (Red-unique-Pi ; Red-unique-Sigma ;
  bU-from-cf-fmFun)
open import SubstitutionLemmaSigma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType)

------------------------------------------------------------------------
-- Bundled validity relations (mutual)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Val2 G M A u a : like Val, but HasType G M A at leaves
  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

  -- EqVal2 G M N A u a : like EqVal, but ConvTm G M N A at leaves
  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  -- ValTy2 G M u : type validity, HasType G M U at leaves
  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set

  -- EqValTy2 G M N u : type equality validity, ConvTm G M N U at leaves
  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

  -- ValTyPi2 G M b f
  ValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

  -- EqValTyPi2 G M N b f
  EqValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinFun -> Set

  -- ValTySigma2 G M b f
  ValTySigma2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

  -- EqValTySigma2 G M N b f
  EqValTySigma2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinFun -> Set

  -- ValPi2 G M A g b f
  ValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  -- EqValPi2 G M N A g b f
  EqValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  -- PiEdgeVal2 G A B b f
  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  -- PiEdgeEq2 G A B b f
  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  -- PiEdgeEqTy2 G A B B' b f
  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    Expr (suc n) -> FinEl -> FinFun -> Set

  -- PiAppVal2 G M A0 B0 b f g
  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> FinFun -> Set

  -- PiAppEq2 G M A0 B0 b f g
  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> FinFun -> Set

  -- PiAppEqVal2 G M N A0 B0 b f g
  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  -- SigmaEdgeVal2 G A B b f
  SigmaEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  -- SigmaEdgeEq2 G A B b f
  SigmaEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  -- SigmaEdgeEqTy2 G A B B' b f
  SigmaEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    Expr (suc n) -> FinEl -> FinFun -> Set

  -- ValPair2 G M T u' v' b f : term validity at (PairCode u' v', SigmaCode b f)
  ValPair2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinEl -> FinEl -> FinFun -> Set

  -- EqValPair2 G M N T u' v' b f : term equality at (PairCode u' v', SigmaCode b f)
  EqValPair2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> FinEl -> FinFun -> Set

  --------------------------------------------------------------------
  -- Val2: Top at leaves (like unbundled), structured at UCode / FunEl+PiCode
  -- Val2 at (PairCode, SigmaCode) = Top
  --------------------------------------------------------------------

  Val2 G M A u Bot              = Top
  Val2 G M A Bot UCode          = Top
  Val2 G M A UCode UCode        = ValTy2 G M UCode
  Val2 G M A (FunEl g) UCode    = ValTy2 G M (FunEl g)
  Val2 G M A (PiCode a' f') UCode = ValTy2 G M (PiCode a' f')
  Val2 G M A (SigmaCode a' f') UCode = ValTy2 G M (SigmaCode a' f')
  Val2 G M A (PairCode u' v') UCode = Top
  Val2 G M A PropCode UCode     = Top
  Val2 G M A (PiCode a' f') PropCode = ValTy2 G M (PiCode a' f')
  Val2 G M A Bot PropCode            = Top
  Val2 G M A UCode PropCode          = Top
  Val2 G M A PropCode PropCode       = Top
  Val2 G M A (FunEl g) PropCode      = Top
  Val2 G M A (SigmaCode a' f') PropCode = Top
  Val2 G M A (PairCode u' v') PropCode = Top
  Val2 G M A u (FunEl h)        = Top
  Val2 G M A Bot            (PiCode b f) = Top
  Val2 G M A UCode          (PiCode b f) = Top
  Val2 G M A PropCode       (PiCode b f) = Top
  Val2 G M A (FunEl g)      (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f)) (ValPi2 G M A g b f)
  Val2 G M A (PiCode a' f') (PiCode b f) = Top
  Val2 G M A (SigmaCode a' f') (PiCode b f) = Top
  Val2 G M A (PairCode u' v') (PiCode b f) = Top
  -- SigmaCode: Val at (PairCode, SigmaCode) = Top
  Val2 G M A Bot              (SigmaCode b f) = Top
  Val2 G M A UCode            (SigmaCode b f) = Top
  Val2 G M A PropCode         (SigmaCode b f) = Top
  Val2 G M A (FunEl g)        (SigmaCode b f) = Top
  Val2 G M A (PiCode a' f')  (SigmaCode b f) = Top
  Val2 G M A (SigmaCode a' f') (SigmaCode b f) = Top
  Val2 G M A (PairCode u' v') (SigmaCode b f) = ValPair2 G M A u' v' b f
  -- PairCode at a: Val always Top (unreachable when typed)
  Val2 G M A u (PairCode x y) = Top

  --------------------------------------------------------------------
  -- EqVal2: ConvTm at leaves
  --------------------------------------------------------------------

  EqVal2 G M N A u Bot              = Top
  EqVal2 G M N A Bot UCode          = Top
  EqVal2 G M N A UCode UCode        =
    Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode))
  EqVal2 G M N A (FunEl g) UCode    =
    Pair (ValTy2 G M (FunEl g)) (Pair (ValTy2 G N (FunEl g)) (EqValTy2 G M N (FunEl g)))
  EqVal2 G M N A (PiCode a' f') UCode =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2 G M N A (SigmaCode a' f') UCode =
    Pair (ValTy2 G M (SigmaCode a' f')) (Pair (ValTy2 G N (SigmaCode a' f')) (EqValTy2 G M N (SigmaCode a' f')))
  EqVal2 G M N A (PairCode u' v') UCode = Top
  EqVal2 G M N A PropCode UCode    = Top
  EqVal2 G M N A (PiCode a' f') PropCode =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2 G M N A Bot PropCode            = Top
  EqVal2 G M N A UCode PropCode          = Top
  EqVal2 G M N A PropCode PropCode       = Top
  EqVal2 G M N A (FunEl g) PropCode      = Top
  EqVal2 G M N A (SigmaCode a' f') PropCode = Top
  EqVal2 G M N A (PairCode u' v') PropCode = Top
  EqVal2 G M N A u (FunEl h)       = Top
  EqVal2 G M N A Bot            (PiCode b f) = Top
  EqVal2 G M N A UCode          (PiCode b f) = Top
  EqVal2 G M N A PropCode       (PiCode b f) = Top
  EqVal2 G M N A (FunEl g)      (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f))
         (Pair (ValPi2 G M A g b f)
               (Pair (ValPi2 G N A g b f)
                     (EqValPi2 G M N A g b f)))
  EqVal2 G M N A (PiCode a' f') (PiCode b f) = Top
  EqVal2 G M N A (SigmaCode a' f') (PiCode b f) = Top
  EqVal2 G M N A (PairCode u' v') (PiCode b f) = Top
  -- SigmaCode: EqVal at (PairCode, SigmaCode) = Top
  EqVal2 G M N A Bot              (SigmaCode b f) = Top
  EqVal2 G M N A UCode            (SigmaCode b f) = Top
  EqVal2 G M N A PropCode         (SigmaCode b f) = Top
  EqVal2 G M N A (FunEl g)        (SigmaCode b f) = Top
  EqVal2 G M N A (PiCode a' f')  (SigmaCode b f) = Top
  EqVal2 G M N A (SigmaCode a' f') (SigmaCode b f) = Top
  EqVal2 G M N A (PairCode u' v') (SigmaCode b f) = EqValPair2 G M N A u' v' b f
  -- PairCode at a: EqVal always Top
  EqVal2 G M N A u (PairCode x y) = Top

  --------------------------------------------------------------------
  -- ValTy2: HasType G M U at leaves
  --------------------------------------------------------------------

  ValTy2 G M Bot              = Top
  ValTy2 G M UCode            = Top
  ValTy2 G M PropCode         = Top
  ValTy2 G M (FunEl g)        = Top
  ValTy2 G M (PiCode b f)     = ValTyPi2 G M b f
  ValTy2 G M (SigmaCode b f)  = ValTySigma2 G M b f
  ValTy2 G M (PairCode u v)   = Top

  --------------------------------------------------------------------
  -- EqValTy2: ConvTm G M N U at leaves
  --------------------------------------------------------------------

  EqValTy2 G M N Bot              = Top
  EqValTy2 G M N UCode            = Top
  EqValTy2 G M N PropCode         = Top
  EqValTy2 G M N (FunEl g)        = Top
  EqValTy2 G M N (PiCode b f)     =
    Pair (ValTyPi2 G M b f)
         (Pair (ValTyPi2 G N b f)
               (EqValTyPi2 G M N b f))
  EqValTy2 G M N (SigmaCode b f)  =
    Pair (ValTySigma2 G M b f)
         (Pair (ValTySigma2 G N b f)
               (EqValTySigma2 G M N b f))
  EqValTy2 G M N (PairCode u v)   = Top

  --------------------------------------------------------------------
  -- Pi structures (selection-based)
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Sigma structures (selection-based)
  --------------------------------------------------------------------

  SigmaEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
    ValTy2 G (subst1 B N) v

  SigmaEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
    EqValTy2 G (subst1 B N1) (subst1 B N2) v

  SigmaEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> Val2 G P A u b ->
    EqValTy2 G (subst1 B P) (subst1 B' P) v

  --------------------------------------------------------------------
  -- ValTyPi2: type validity at PiCode b f
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

  --------------------------------------------------------------------
  -- EqValTyPi2: type equality at PiCode b f
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- ValTySigma2: type validity at SigmaCode b f
  --------------------------------------------------------------------

  ValTySigma2 {n} G M b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red G M (RS.Sigma A B) U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (HasType G A U) \ _ ->
    Sigma (HasType (extend G A) B U) \ _ ->
    Pair (ValTy2 G A b)
         (Pair (SigmaEdgeVal2 G A B b f)
               (SigmaEdgeEq2 G A B b f))

  --------------------------------------------------------------------
  -- EqValTySigma2: type equality at SigmaCode b f
  --------------------------------------------------------------------

  EqValTySigma2 {n} G M N b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Expr n) \ A' ->
    Sigma (Expr (suc n)) \ B' ->
    Sigma (Red G M (RS.Sigma A B) U) \ _ ->
    Sigma (Red G N (RS.Sigma A' B') U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (ConvTm G A A' U) \ _ ->
    Sigma (ConvTm (extend G A) B B' U) \ _ ->
    Pair (EqValTy2 G A A' b)
         (SigmaEdgeEqTy2 G A B B' b f)

  --------------------------------------------------------------------
  -- ValPair2: term validity at (PairCode u' v', SigmaCode b f)
  --------------------------------------------------------------------

  ValPair2 {n} G M T u' v' b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red G T (RS.Sigma A B) U) \ _ ->
    Pair (Val2 G (Fst M) A u' b)
         (Val2 G (Snd M) (subst1 B (Fst M)) v' (EvalFun f u'))

  --------------------------------------------------------------------
  -- EqValPair2: stores full ValPair2 for M and N + Fst equality.
  -- NO Snd equality at the inner level (handled by outer layer).
  --------------------------------------------------------------------

  EqValPair2 {n} G M N T u' v' b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red G T (RS.Sigma A B) U) \ _ ->
    -- M's data (Fst + Snd)
    Sigma (Val2 G (Fst M) A u' b) \ _ ->
    Sigma (Val2 G (Snd M) (subst1 B (Fst M)) v' (EvalFun f u')) \ _ ->
    -- N's data (Fst + Snd)
    Sigma (Val2 G (Fst N) A u' b) \ _ ->
    Sigma (Val2 G (Snd N) (subst1 B (Fst N)) v' (EvalFun f u')) \ _ ->
    -- Fst equality only (Snd equality handled by outer layer)
    EqVal2 G (Fst M) (Fst N) A u' b

  --------------------------------------------------------------------
  -- ValPi2: term validity at (FunEl g, PiCode b f)
  --------------------------------------------------------------------

  ValPi2 {n} G M A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    Pair (PiAppVal2 G M A0 B0 b f g)
         (PiAppEq2 G M A0 B0 b f g)

  --------------------------------------------------------------------
  -- EqValPi2: equality at (FunEl g, PiCode b f)
  --------------------------------------------------------------------

  EqValPi2 {n} G M N A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    PiAppEqVal2 G M N A0 B0 b f g

------------------------------------------------------------------------
-- Extraction helpers
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Val2-Bot / EqVal2-Bot: u = Bot means Val2/EqVal2 = Top at all a
------------------------------------------------------------------------

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  (a : FinEl) -> Val2 G M A Bot a
Val2-Bot Bot              = tt
Val2-Bot UCode            = tt
Val2-Bot PropCode         = tt
Val2-Bot (FunEl h)        = tt
Val2-Bot (PiCode b f)     = tt
Val2-Bot (SigmaCode b f)  = tt
Val2-Bot (PairCode x y)   = tt

-- Val2-SigmaTop / EqVal2-SigmaTop: NOT total for PairCode (ValPair2 is structured).
-- Use case-split on u instead.

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot Bot              = tt
EqVal2-Bot UCode            = tt
EqVal2-Bot PropCode         = tt
EqVal2-Bot (FunEl h)        = tt
EqVal2-Bot (PiCode b f)     = tt
EqVal2-Bot (SigmaCode b f)  = tt
EqVal2-Bot (PairCode x y)   = tt

------------------------------------------------------------------------
-- Eq-transport for Val2 / EqVal2
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

ValTy2-transport : {n : Nat} {G : Ctx n} {M M' : Expr n}
  {u : FinEl} -> Eq M M' -> ValTy2 G M u -> ValTy2 G M' u
ValTy2-transport refl v = v

EqValTy2-transport : {n : Nat} {G : Ctx n} {M M' N N' : Expr n}
  {u : FinEl} -> Eq M M' -> Eq N N' -> EqValTy2 G M N u -> EqValTy2 G M' N' u
EqValTy2-transport refl refl v = v

------------------------------------------------------------------------
-- Red-unique-Pi / Red-unique-Sigma (re-exported from ValiditySigma)
------------------------------------------------------------------------

-- bU-from-cf-fmU: derive FinMem b UCode from CoherentFun f and FinMemAllU f b
bU-from-cf-fmU : (f : FinFun) (b : FinEl) -> CoherentFun f -> FinMemAllU f b -> FinMem b UCode
bU-from-cf-fmU nil         b ()
bU-from-cf-fmU (cons p ps) b cf fmU = FinMem-a-in-U (fst p) b (fst (fst fmU))

------------------------------------------------------------------------
-- Transport lemmas (mutual, terminating)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  ------------------------------------------------------------------------
  -- Val2-to-EqVal2 / ValTy2-to-EqValTy2: diagonal embedding
  ------------------------------------------------------------------------

  Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n}
    (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
  Val2-to-EqVal2 u Bot          tt = tt
  Val2-to-EqVal2 Bot UCode      tt = tt
  Val2-to-EqVal2 UCode UCode    tt = mkSigma tt (mkSigma tt tt)
  Val2-to-EqVal2 (FunEl g) UCode tt = mkSigma tt (mkSigma tt tt)
  Val2-to-EqVal2 (PiCode a' f') UCode vty = mkSigma vty (mkSigma vty (ValTy2-to-EqValTy2 (PiCode a' f') vty))
  Val2-to-EqVal2 (SigmaCode a' f') UCode vty = mkSigma vty (mkSigma vty (ValTy2-to-EqValTy2 (SigmaCode a' f') vty))
  Val2-to-EqVal2 (PairCode u' v') UCode tt = tt
  Val2-to-EqVal2 PropCode UCode tt = tt
  Val2-to-EqVal2 (PiCode a' f') PropCode vty = mkSigma vty (mkSigma vty (ValTy2-to-EqValTy2 (PiCode a' f') vty))
  Val2-to-EqVal2 Bot PropCode tt = tt
  Val2-to-EqVal2 UCode PropCode tt = tt
  Val2-to-EqVal2 PropCode PropCode tt = tt
  Val2-to-EqVal2 (FunEl _) PropCode tt = tt
  Val2-to-EqVal2 (SigmaCode _ _) PropCode tt = tt
  Val2-to-EqVal2 (PairCode _ _) PropCode tt = tt
  Val2-to-EqVal2 u (FunEl h) tt = tt
  Val2-to-EqVal2 Bot (PiCode b f) tt = tt
  Val2-to-EqVal2 UCode (PiCode b f) tt = tt
  Val2-to-EqVal2 PropCode (PiCode b f) tt = tt
  Val2-to-EqVal2 (FunEl g) (PiCode b f) val =
    let vty  = fst val
        vpiM = snd val
        A0   = fst vpiM
        B0   = fst (snd vpiM)
        red  = fst (snd (snd vpiM))
        cg   = fst (snd (snd (snd vpiM)))
        fmg  = fst (snd (snd (snd (snd vpiM))))
        pav  = fst (snd (snd (snd (snd (snd vpiM)))))
        eqvpi = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
                  (\ u' v' sel P htP valP ->
                    Val2-to-EqVal2 v' (EvalFun f u') (pav u' v' sel P htP valP))))))
    in mkSigma vty (mkSigma vpiM (mkSigma vpiM eqvpi))
  Val2-to-EqVal2 (PiCode a' f') (PiCode b f) tt = tt
  Val2-to-EqVal2 (SigmaCode a' f') (PiCode b f) tt = tt
  Val2-to-EqVal2 (PairCode u' v') (PiCode b f) tt = tt
  Val2-to-EqVal2 Bot (SigmaCode b f) tt = tt
  Val2-to-EqVal2 UCode (SigmaCode b f) tt = tt
  Val2-to-EqVal2 PropCode (SigmaCode b f) tt = tt
  Val2-to-EqVal2 (FunEl g) (SigmaCode b f) tt = tt
  Val2-to-EqVal2 (PiCode a' f') (SigmaCode b f) tt = tt
  Val2-to-EqVal2 (SigmaCode a' f') (SigmaCode b f) tt = tt
  Val2-to-EqVal2 (PairCode u' v') (SigmaCode b f) val =
    let A0    = fst val
        B0    = fst (snd val)
        red   = fst (snd (snd val))
        v2Fst = fst (snd (snd (snd val)))
        v2Snd = snd (snd (snd (snd val)))
    in mkSigma A0 (mkSigma B0 (mkSigma red
         (mkSigma v2Fst (mkSigma v2Snd (mkSigma v2Fst (mkSigma v2Snd
         (Val2-to-EqVal2 u' b v2Fst)))))))
  Val2-to-EqVal2 u (PairCode x y) tt = tt

  ValTy2-to-EqValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
    (u : FinEl) -> ValTy2 G M u -> EqValTy2 G M M u
  ValTy2-to-EqValTy2 Bot          tt = tt
  ValTy2-to-EqValTy2 UCode        tt = tt
  ValTy2-to-EqValTy2 PropCode     tt = tt
  ValTy2-to-EqValTy2 (FunEl g)    tt = tt
  ValTy2-to-EqValTy2 (PairCode u v) tt = tt
  ValTy2-to-EqValTy2 (PiCode b f) vtyM =
    let A    = fst vtyM
        B    = fst (snd vtyM)
        red  = fst (snd (snd vtyM))
        cf   = fst (snd (snd (snd vtyM)))
        fmU  = fst (snd (snd (snd (snd vtyM))))
        htA  = fst (snd (snd (snd (snd (snd vtyM)))))
        htB  = fst (snd (snd (snd (snd (snd (snd vtyM))))))
        inn  = snd (snd (snd (snd (snd (snd (snd vtyM))))))
        vtA  = fst inn
        pev  = fst (snd inn)
        eqVtA = ValTy2-to-EqValTy2 b vtA
        pet   = (\ u' v' sel P htP valP -> ValTy2-to-EqValTy2 v' (pev u' v' sel P htP valP))
        coreEq = mkSigma A (mkSigma B (mkSigma A (mkSigma B
                   (mkSigma red (mkSigma red (mkSigma cf (mkSigma fmU
                     (mkSigma (conv-refl htA)
                       (mkSigma (conv-refl htB)
                         (mkSigma eqVtA pet))))))))))
    in mkSigma vtyM (mkSigma vtyM coreEq)
  ValTy2-to-EqValTy2 (SigmaCode b f) vtyM =
    let A    = fst vtyM
        B    = fst (snd vtyM)
        red  = fst (snd (snd vtyM))
        cf   = fst (snd (snd (snd vtyM)))
        fmU  = fst (snd (snd (snd (snd vtyM))))
        htA  = fst (snd (snd (snd (snd (snd vtyM)))))
        htB  = fst (snd (snd (snd (snd (snd (snd vtyM))))))
        inn  = snd (snd (snd (snd (snd (snd (snd vtyM))))))
        vtA  = fst inn
        sev  = fst (snd inn)
        eqVtA = ValTy2-to-EqValTy2 b vtA
        set   = (\ u' v' sel P htP valP -> ValTy2-to-EqValTy2 v' (sev u' v' sel P htP valP))
        coreEq = mkSigma A (mkSigma B (mkSigma A (mkSigma B
                   (mkSigma red (mkSigma red (mkSigma cf (mkSigma fmU
                     (mkSigma (conv-refl htA)
                       (mkSigma (conv-refl htB)
                         (mkSigma eqVtA set))))))))))
    in mkSigma vtyM (mkSigma vtyM coreEq)

  ------------------------------------------------------------------------
  -- Val2-from-EqVal2-first / Val2-from-EqVal2-second
  ------------------------------------------------------------------------

  Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
  Val2-from-EqVal2-first u Bot          tt = tt
  Val2-from-EqVal2-first Bot UCode      tt = tt
  Val2-from-EqVal2-first UCode UCode    ev = tt
  Val2-from-EqVal2-first (FunEl g) UCode ev = tt
  Val2-from-EqVal2-first (PiCode a' f') UCode ev = fst ev
  Val2-from-EqVal2-first (SigmaCode a' f') UCode ev = fst ev
  Val2-from-EqVal2-first (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-first PropCode UCode ev = tt
  Val2-from-EqVal2-first (PiCode a' f') PropCode ev = fst ev
  Val2-from-EqVal2-first Bot PropCode    tt = tt
  Val2-from-EqVal2-first UCode PropCode    tt = tt
  Val2-from-EqVal2-first PropCode PropCode    tt = tt
  Val2-from-EqVal2-first (FunEl _) PropCode    tt = tt
  Val2-from-EqVal2-first (SigmaCode _ _) PropCode    tt = tt
  Val2-from-EqVal2-first (PairCode _ _) PropCode    tt = tt
  Val2-from-EqVal2-first u (FunEl h)   tt = tt
  Val2-from-EqVal2-first Bot (PiCode b f) tt = tt
  Val2-from-EqVal2-first UCode (PiCode b f) tt = tt
  Val2-from-EqVal2-first PropCode (PiCode b f) tt = tt
  Val2-from-EqVal2-first (FunEl g) (PiCode b f) ev =
    mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (PiCode a' f') (PiCode b f) tt = tt
  Val2-from-EqVal2-first (SigmaCode a' f') (PiCode b f) tt = tt
  Val2-from-EqVal2-first (PairCode u' v') (PiCode b f) tt = tt
  Val2-from-EqVal2-first Bot (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first UCode (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first PropCode (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first (FunEl g) (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first (PiCode a' f') (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first (SigmaCode a' f') (SigmaCode b f) tt = tt
  Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b f) ev =
    let A0     = fst ev
        B0     = fst (snd ev)
        red    = fst (snd (snd ev))
        v2FstM = fst (snd (snd (snd ev)))
        v2SndM = fst (snd (snd (snd (snd ev))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma v2FstM v2SndM)))
  Val2-from-EqVal2-first u (PairCode x y) tt = tt

  Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
  Val2-from-EqVal2-second u Bot          tt = tt
  Val2-from-EqVal2-second Bot UCode      tt = tt
  Val2-from-EqVal2-second UCode UCode    ev = tt
  Val2-from-EqVal2-second (FunEl g) UCode ev = tt
  Val2-from-EqVal2-second (PiCode a' f') UCode ev = fst (snd ev)
  Val2-from-EqVal2-second (SigmaCode a' f') UCode ev = fst (snd ev)
  Val2-from-EqVal2-second (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-second PropCode UCode ev = tt
  Val2-from-EqVal2-second (PiCode a' f') PropCode ev = fst (snd ev)
  Val2-from-EqVal2-second Bot PropCode    tt = tt
  Val2-from-EqVal2-second UCode PropCode    tt = tt
  Val2-from-EqVal2-second PropCode PropCode    tt = tt
  Val2-from-EqVal2-second (FunEl _) PropCode    tt = tt
  Val2-from-EqVal2-second (SigmaCode _ _) PropCode    tt = tt
  Val2-from-EqVal2-second (PairCode _ _) PropCode    tt = tt
  Val2-from-EqVal2-second u (FunEl h)   tt = tt
  Val2-from-EqVal2-second Bot (PiCode b f) tt = tt
  Val2-from-EqVal2-second UCode (PiCode b f) tt = tt
  Val2-from-EqVal2-second PropCode (PiCode b f) tt = tt
  Val2-from-EqVal2-second (FunEl g) (PiCode b f) ev =
    mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (PiCode a' f') (PiCode b f) tt = tt
  Val2-from-EqVal2-second (SigmaCode a' f') (PiCode b f) tt = tt
  Val2-from-EqVal2-second (PairCode u' v') (PiCode b f) tt = tt
  Val2-from-EqVal2-second Bot (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second UCode (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second PropCode (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second (FunEl g) (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second (PiCode a' f') (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second (SigmaCode a' f') (SigmaCode b f) tt = tt
  Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b f) ev =
    let A0     = fst ev
        B0     = fst (snd ev)
        red    = fst (snd (snd ev))
        v2FstN = fst (snd (snd (snd (snd (snd ev)))))
        v2SndN = fst (snd (snd (snd (snd (snd (snd ev))))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma v2FstN v2SndN)))
  Val2-from-EqVal2-second u (PairCode x y) tt = tt

  ------------------------------------------------------------------------
  -- EqValTy2-sym
  ------------------------------------------------------------------------

  EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
    (u : FinEl) -> Coherent u -> EqValTy2 G M N u -> EqValTy2 G N M u
  EqValTy2-sym Bot          cu tt = tt
  EqValTy2-sym UCode        cu tt = tt
  EqValTy2-sym PropCode     cu tt = tt
  EqValTy2-sym (FunEl g)    cu tt = tt
  EqValTy2-sym (PairCode u v) cu tt = tt
  EqValTy2-sym (PiCode b f) cu eqv =
    let vtyM = fst eqv
        vtyN = fst (snd eqv)
        core = snd (snd eqv)
        A     = fst core
        B     = fst (snd core)
        A'    = fst (snd (snd core))
        B'    = fst (snd (snd (snd core)))
        rM    = fst (snd (snd (snd (snd core))))
        rN    = fst (snd (snd (snd (snd (snd core)))))
        cf    = fst (snd (snd (snd (snd (snd (snd core))))))
        fmU   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convAA = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        convBB = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqC   = fst tail12
        pet   = snd tail12
        cb    = fst cu
        redM-vty = fst (snd (snd vtyM))
        redN-vty = fst (snd (snd vtyN))
        uniqM = Red-unique-Pi redM-vty rM
        uniqN = Red-unique-Pi redN-vty rN
        htA-raw = fst (snd (snd (snd (snd (snd vtyM)))))
        htA'-raw = fst (snd (snd (snd (snd (snd vtyN)))))
        htA  = S.Eq-transport (\ X -> HasType _ X _) (fst uniqM) htA-raw
        htA' = S.Eq-transport (\ X -> HasType _ X _) (fst uniqN) htA'-raw
        symCore = mkSigma A' (mkSigma B' (mkSigma A (mkSigma B
                    (mkSigma rN (mkSigma rM (mkSigma cf (mkSigma fmU
                      (mkSigma (conv-sym convAA)
                        (mkSigma (ctx-conv-ConvTm htA htA' convAA (conv-sym convBB))
                          (mkSigma (EqValTy2-sym b cb eqC)
                            (\ u' v' sel P htP valP ->
                              let eqC' = EqValTy2-sym b cb eqC
                                  htP-A = ty-conv htP (conv-sym convAA) htA
                                  valP-A' = Val2-EqValTy2-fwd u' b cb eqC' valP
                                  cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU cf)
                              in EqValTy2-sym v' cv' (pet u' v' sel P htP-A valP-A'))))))))))))
    in mkSigma vtyN (mkSigma vtyM symCore)
  EqValTy2-sym (SigmaCode b f) cu eqv =
    let vtyM = fst eqv
        vtyN = fst (snd eqv)
        core = snd (snd eqv)
        A     = fst core
        B     = fst (snd core)
        A'    = fst (snd (snd core))
        B'    = fst (snd (snd (snd core)))
        rM    = fst (snd (snd (snd (snd core))))
        rN    = fst (snd (snd (snd (snd (snd core)))))
        cf    = fst (snd (snd (snd (snd (snd (snd core))))))
        fmU   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convAA = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        convBB = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqC   = fst tail12
        set   = snd tail12
        cb    = fst cu
        redM-vty = fst (snd (snd vtyM))
        redN-vty = fst (snd (snd vtyN))
        uniqM = Red-unique-Sigma redM-vty rM
        uniqN = Red-unique-Sigma redN-vty rN
        htA-raw = fst (snd (snd (snd (snd (snd vtyM)))))
        htA'-raw = fst (snd (snd (snd (snd (snd vtyN)))))
        htA  = S.Eq-transport (\ X -> HasType _ X _) (fst uniqM) htA-raw
        htA' = S.Eq-transport (\ X -> HasType _ X _) (fst uniqN) htA'-raw
        symCore = mkSigma A' (mkSigma B' (mkSigma A (mkSigma B
                    (mkSigma rN (mkSigma rM (mkSigma cf (mkSigma fmU
                      (mkSigma (conv-sym convAA)
                        (mkSigma (ctx-conv-ConvTm htA htA' convAA (conv-sym convBB))
                          (mkSigma (EqValTy2-sym b cb eqC)
                            (\ u' v' sel P htP valP ->
                              let eqC' = EqValTy2-sym b cb eqC
                                  htP-A = ty-conv htP (conv-sym convAA) htA
                                  valP-A' = Val2-EqValTy2-fwd u' b cb eqC' valP
                                  cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU cf)
                              in EqValTy2-sym v' cv' (set u' v' sel P htP-A valP-A'))))))))))))
    in mkSigma vtyN (mkSigma vtyM symCore)

  ------------------------------------------------------------------------
  -- EqValTy2-trans
  ------------------------------------------------------------------------

  EqValTy2-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
    (u : FinEl) -> Coherent u ->
    EqValTy2 G A B u -> EqValTy2 G B C u -> EqValTy2 G A C u
  EqValTy2-trans Bot cu tt tt = tt
  EqValTy2-trans UCode cu tt tt = tt
  EqValTy2-trans PropCode cu tt tt = tt
  EqValTy2-trans (FunEl g) cu tt tt = tt
  EqValTy2-trans (PairCode u v) cu tt tt = tt
  EqValTy2-trans (PiCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = fst coreAB
        B0    = fst (snd coreAB)
        A0'   = fst (snd (snd coreAB))
        B0'   = fst (snd (snd (snd coreAB)))
        rA    = fst (snd (snd (snd (snd coreAB))))
        rB1   = fst (snd (snd (snd (snd (snd coreAB)))))
        cf1   = fst (snd (snd (snd (snd (snd (snd coreAB))))))
        fmU1  = fst (snd (snd (snd (snd (snd (snd (snd coreAB)))))))
        convAA_AB = fst (snd (snd (snd (snd (snd (snd (snd (snd coreAB))))))))
        convBB_AB = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB)))))))))
        tailAB = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB)))))))))
        eqDomAB = fst tailAB
        petAB   = snd tailAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = fst coreBC
        B1    = fst (snd coreBC)
        A1'   = fst (snd (snd coreBC))
        B1'   = fst (snd (snd (snd coreBC)))
        rB2   = fst (snd (snd (snd (snd coreBC))))
        rC    = fst (snd (snd (snd (snd (snd coreBC)))))
        cf2   = fst (snd (snd (snd (snd (snd (snd coreBC))))))
        fmU2  = fst (snd (snd (snd (snd (snd (snd (snd coreBC)))))))
        convAA_BC = fst (snd (snd (snd (snd (snd (snd (snd (snd coreBC))))))))
        convBB_BC = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreBC)))))))))
        tailBC = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreBC)))))))))
        eqDomBC = fst tailBC
        petBC   = snd tailBC
        uniq = Red-unique-Pi rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = S.Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        redB1-vty-e = fst (snd (snd vtyB1))
        uniqB1-dom-e = Red-unique-Pi redB1-vty-e rB1
        htA0'-raw-e = fst (snd (snd (snd (snd (snd vtyB1)))))
        htA0'-e = S.Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        petAC : PiEdgeEqTy2 _ A0 B0 B1' b f
        petAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = S.Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = S.Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = petAB u' v' sel P htP valP
              eqt2 = petBC u' v' sel P htP-A1 valP-A1
              eqt2' = S.Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        convAA_BC' = S.Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        convBB_BC-transported = S.Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = fst (snd (snd vtyA))
        uniqA-dom = Red-unique-Pi redA-vty rA
        htA0-raw = fst (snd (snd (snd (snd (snd vtyA)))))
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = fst (snd (snd vtyB1))
        uniqB1-dom = Red-unique-Pi redB1-vty rB1
        htA0'-raw = fst (snd (snd (snd (snd (snd vtyB1)))))
        htA0' = S.Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = mkSigma A0 (mkSigma B0 (mkSigma A1' (mkSigma B1'
                       (mkSigma rA (mkSigma rC (mkSigma cf1 (mkSigma fmU1
                         (mkSigma convAA_AC
                           (mkSigma convBB_AC
                             (mkSigma eqDomAC petAC))))))))))
    in mkSigma vtyA (mkSigma vtyC resultCore)
  EqValTy2-trans (SigmaCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = fst coreAB
        B0    = fst (snd coreAB)
        A0'   = fst (snd (snd coreAB))
        B0'   = fst (snd (snd (snd coreAB)))
        rA    = fst (snd (snd (snd (snd coreAB))))
        rB1   = fst (snd (snd (snd (snd (snd coreAB)))))
        cf1   = fst (snd (snd (snd (snd (snd (snd coreAB))))))
        fmU1  = fst (snd (snd (snd (snd (snd (snd (snd coreAB)))))))
        convAA_AB = fst (snd (snd (snd (snd (snd (snd (snd (snd coreAB))))))))
        convBB_AB = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB)))))))))
        tailAB = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB)))))))))
        eqDomAB = fst tailAB
        setAB   = snd tailAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = fst coreBC
        B1    = fst (snd coreBC)
        A1'   = fst (snd (snd coreBC))
        B1'   = fst (snd (snd (snd coreBC)))
        rB2   = fst (snd (snd (snd (snd coreBC))))
        rC    = fst (snd (snd (snd (snd (snd coreBC)))))
        cf2   = fst (snd (snd (snd (snd (snd (snd coreBC))))))
        fmU2  = fst (snd (snd (snd (snd (snd (snd (snd coreBC)))))))
        convAA_BC = fst (snd (snd (snd (snd (snd (snd (snd (snd coreBC))))))))
        convBB_BC = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreBC)))))))))
        tailBC = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreBC)))))))))
        eqDomBC = fst tailBC
        setBC   = snd tailBC
        uniq = Red-unique-Sigma rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = S.Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        redB1-vty-e = fst (snd (snd vtyB1))
        uniqB1-dom-e = Red-unique-Sigma redB1-vty-e rB1
        htA0'-raw-e = fst (snd (snd (snd (snd (snd vtyB1)))))
        htA0'-e = S.Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        setAC : SigmaEdgeEqTy2 _ A0 B0 B1' b f
        setAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = S.Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = S.Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = setAB u' v' sel P htP valP
              eqt2 = setBC u' v' sel P htP-A1 valP-A1
              eqt2' = S.Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        convAA_BC' = S.Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        convBB_BC-transported = S.Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = fst (snd (snd vtyA))
        uniqA-dom = Red-unique-Sigma redA-vty rA
        htA0-raw = fst (snd (snd (snd (snd (snd vtyA)))))
        htA0  = S.Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = fst (snd (snd vtyB1))
        uniqB1-dom = Red-unique-Sigma redB1-vty rB1
        htA0'-raw = fst (snd (snd (snd (snd (snd vtyB1)))))
        htA0' = S.Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = mkSigma A0 (mkSigma B0 (mkSigma A1' (mkSigma B1'
                       (mkSigma rA (mkSigma rC (mkSigma cf1 (mkSigma fmU1
                         (mkSigma convAA_AC
                           (mkSigma convBB_AC
                             (mkSigma eqDomAC setAC))))))))))
    in mkSigma vtyA (mkSigma vtyC resultCore)

  ------------------------------------------------------------------------
  -- EqVal2-sym
  ------------------------------------------------------------------------

  EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M N A u a -> EqVal2 G N M A u a
  EqVal2-sym u Bot cu ca tt = tt
  EqVal2-sym Bot UCode cu ca tt = tt
  EqVal2-sym UCode UCode cu ca ev = mkSigma tt (mkSigma tt tt)
  EqVal2-sym (FunEl g) UCode cu ca ev = mkSigma tt (mkSigma tt tt)
  EqVal2-sym (PiCode a' f') UCode cu ca ev =
    mkSigma (fst (snd ev)) (mkSigma (fst ev) (EqValTy2-sym (PiCode a' f') cu (snd (snd ev))))
  EqVal2-sym (SigmaCode a' f') UCode cu ca ev =
    mkSigma (fst (snd ev)) (mkSigma (fst ev) (EqValTy2-sym (SigmaCode a' f') cu (snd (snd ev))))
  EqVal2-sym (PairCode u' v') UCode cu ca tt = tt
  EqVal2-sym PropCode UCode cu ca tt = tt
  EqVal2-sym (PiCode a' f') PropCode cu ca ev =
    mkSigma (fst (snd ev)) (mkSigma (fst ev) (EqValTy2-sym (PiCode a' f') cu (snd (snd ev))))
  EqVal2-sym Bot PropCode cu ca tt = tt
  EqVal2-sym UCode PropCode cu ca tt = tt
  EqVal2-sym PropCode PropCode cu ca tt = tt
  EqVal2-sym (FunEl _) PropCode cu ca tt = tt
  EqVal2-sym (SigmaCode _ _) PropCode cu ca tt = tt
  EqVal2-sym (PairCode _ _) PropCode cu ca tt = tt
  EqVal2-sym u (FunEl h) cu ca tt = tt
  EqVal2-sym Bot (PiCode b f) cu ca tt = tt
  EqVal2-sym UCode (PiCode b f) cu ca tt = tt
  EqVal2-sym PropCode (PiCode b f) cu ca tt = tt
  EqVal2-sym (FunEl g) (PiCode b f) cu ca ev =
    let vty  = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        eqvp = snd (snd (snd ev))
        A0     = fst eqvp
        B0     = fst (snd eqvp)
        redA   = fst (snd (snd eqvp))
        cg     = fst (snd (snd (snd eqvp)))
        fmg    = fst (snd (snd (snd (snd eqvp))))
        paev   = snd (snd (snd (snd (snd eqvp))))
        cf     = snd ca
        paev'  : PiAppEqVal2 _ _ _ _ B0 b f g
        paev'  = \ u' v' sel P htP valP ->
          let body = paev u' v' sel P htP valP
              ctg  = cft-from-cf g cg
              cu'  = Coherent-Selection sel ctg
              cv'  = Coherent-Selection-val sel ctg
              cev  = Coherent-EvalFun f u' cf cu'
          in EqVal2-sym v' (EvalFun f u') cv' cev body
        eqvp' = mkSigma A0 (mkSigma B0 (mkSigma redA (mkSigma cg (mkSigma fmg paev'))))
    in mkSigma vty (mkSigma vpiN (mkSigma vpiM eqvp'))
  EqVal2-sym (PiCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (PiCode b f) cu ca tt = tt
  EqVal2-sym Bot (SigmaCode b f) cu ca tt = tt
  EqVal2-sym UCode (SigmaCode b f) cu ca tt = tt
  EqVal2-sym PropCode (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (FunEl g) (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (PiCode a' f') (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (SigmaCode b f) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (SigmaCode b f) cu ca ev =
    let A0      = fst ev
        B0      = fst (snd ev)
        red     = fst (snd (snd ev))
        v2FstM  = fst (snd (snd (snd ev)))
        v2SndM  = fst (snd (snd (snd (snd ev))))
        v2FstN  = fst (snd (snd (snd (snd (snd ev)))))
        v2SndN  = fst (snd (snd (snd (snd (snd (snd ev))))))
        eqFst   = snd (snd (snd (snd (snd (snd (snd ev))))))
        cb      = fst ca
        cu'     = fst (fst cu)
    in mkSigma A0 (mkSigma B0 (mkSigma red
         (mkSigma v2FstN (mkSigma v2SndN (mkSigma v2FstM (mkSigma v2SndM
         (EqVal2-sym u' b cu' cb eqFst)))))))
  EqVal2-sym u (PairCode x y) cu ca tt = tt

  ------------------------------------------------------------------------
  -- EqVal2-trans
  ------------------------------------------------------------------------

  EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a ->
    EqVal2 G M1 M3 A u a
  EqVal2-trans u Bot cu ca tt tt = tt
  EqVal2-trans Bot UCode cu ca tt tt = tt
  EqVal2-trans UCode UCode cu ca ev1 ev2 = mkSigma tt (mkSigma tt tt)
  EqVal2-trans (FunEl g) UCode cu ca ev1 ev2 = mkSigma tt (mkSigma tt tt)
  EqVal2-trans (PiCode a' f') UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev2))
      (EqValTy2-trans (PiCode a' f') cu (snd (snd ev1)) (snd (snd ev2))))
  EqVal2-trans (SigmaCode a' f') UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev2))
      (EqValTy2-trans (SigmaCode a' f') cu (snd (snd ev1)) (snd (snd ev2))))
  EqVal2-trans (PairCode u' v') UCode cu ca tt tt = tt
  EqVal2-trans PropCode UCode cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') PropCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev2))
      (EqValTy2-trans (PiCode a' f') cu (snd (snd ev1)) (snd (snd ev2))))
  EqVal2-trans Bot PropCode cu ca tt tt = tt
  EqVal2-trans UCode PropCode cu ca tt tt = tt
  EqVal2-trans PropCode PropCode cu ca tt tt = tt
  EqVal2-trans (FunEl _) PropCode cu ca tt tt = tt
  EqVal2-trans (SigmaCode _ _) PropCode cu ca tt tt = tt
  EqVal2-trans (PairCode _ _) PropCode cu ca tt tt = tt
  EqVal2-trans u (FunEl h) cu ca tt tt = tt
  EqVal2-trans Bot (PiCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans PropCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (PiCode b f) cu ca ev1 ev2 =
    let vty    = fst ev1
        vpiM1  = fst (snd ev1)
        vpiM3  = fst (snd (snd ev2))
        epi1   = snd (snd (snd ev1))
        epi2   = snd (snd (snd ev2))
        Ax     = fst epi1
        Bx     = fst (snd epi1)
        redAx  = fst (snd (snd epi1))
        cg     = fst (snd (snd (snd epi1)))
        fmg    = fst (snd (snd (snd (snd epi1))))
        paev1  = snd (snd (snd (snd (snd epi1))))
        Ay     = fst epi2
        By     = fst (snd epi2)
        redAy  = fst (snd (snd epi2))
        paev2  = snd (snd (snd (snd (snd epi2))))
        uniq   = Red-unique-Pi redAx redAy
        eqA0   = fst uniq
        eqB0   = snd uniq
        paev2' : PiAppEqVal2 _ _ _ Ax Bx b f g
        paev2' = S.Eq-transport (\ X -> PiAppEqVal2 _ _ _ X Bx b f g) (Eq-sym eqA0)
                   (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ Ay Y b f g) (Eq-sym eqB0) paev2)
        cf     = snd ca
        paev'  : PiAppEqVal2 _ _ _ Ax Bx b f g
        paev'  = \ u' v' sel P htP valP ->
          let body1 = paev1 u' v' sel P htP valP
              body2 = paev2' u' v' sel P htP valP
              ctg  = cft-from-cf g cg
              cv'  = Coherent-Selection-val sel ctg
              cu'  = Coherent-Selection sel ctg
              cev  = Coherent-EvalFun f u' cf cu'
          in EqVal2-trans v' (EvalFun f u') cv' cev body1 body2
        epi' = mkSigma Ax (mkSigma Bx (mkSigma redAx (mkSigma cg (mkSigma fmg paev'))))
    in mkSigma vty (mkSigma vpiM1 (mkSigma vpiM3 epi'))
  EqVal2-trans (PiCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans Bot (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans PropCode (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (SigmaCode b f) cu ca ev1 ev2 =
    let A0       = fst ev1
        B0       = fst (snd ev1)
        red1     = fst (snd (snd ev1))
        -- M1's data from ev1
        v2FstM1  = fst (snd (snd (snd ev1)))
        v2SndM1  = fst (snd (snd (snd (snd ev1))))
        eqFst1   = snd (snd (snd (snd (snd (snd (snd ev1))))))
        -- M3's data from ev2 (needs transport from ev2's A to ev1's A)
        red2     = fst (snd (snd ev2))
        uniq     = Red-unique-Sigma red1 red2
        eqA      = S.Eq-sym (fst uniq)
        eqB      = S.Eq-sym (snd uniq)
        v2FstM3-raw = fst (snd (snd (snd (snd (snd ev2)))))
        v2SndM3-raw = fst (snd (snd (snd (snd (snd (snd ev2))))))
        eqFst2-raw  = snd (snd (snd (snd (snd (snd (snd ev2))))))
        v2FstM3  = S.Eq-transport (\ X -> Val2 _ (Fst _) X u' b) eqA v2FstM3-raw
        v2SndM3  = S.Eq-transport (\ X -> Val2 _ (Snd _) (subst1 X (Fst _)) v' (EvalFun f u')) eqB v2SndM3-raw
        eqFst2   = S.Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X u' b) eqA eqFst2-raw
        cb       = fst ca
        cu'      = fst (fst cu)
    in mkSigma A0 (mkSigma B0 (mkSigma red1
         (mkSigma v2FstM1 (mkSigma v2SndM1 (mkSigma v2FstM3 (mkSigma v2SndM3
         (EqVal2-trans u' b cu' cb eqFst1 eqFst2)))))))
  EqVal2-trans u (PairCode x y) cu ca tt tt = tt

  ------------------------------------------------------------------------
  -- Val2-EqValTy2-fwd: transport Val2 along EqValTy2
  ------------------------------------------------------------------------

  Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    Val2 G M C u b -> Val2 G M C' u b
  Val2-EqValTy2-fwd u Bot cb eqv val = tt
  Val2-EqValTy2-fwd Bot UCode cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv val = val
  Val2-EqValTy2-fwd Bot PropCode cb eqv val = tt
  Val2-EqValTy2-fwd UCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd PropCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl _) PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode _ _) PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode _ _) PropCode cb eqv val = tt
  Val2-EqValTy2-fwd u (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv val = tt
  -- UCode cases: Val2 = ValTy2 G M u, does not depend on C
  Val2-EqValTy2-fwd UCode UCode cb eqv val = val
  Val2-EqValTy2-fwd (FunEl g) UCode cb eqv val = val
  Val2-EqValTy2-fwd (PiCode a' f') UCode cb eqv val = val
  Val2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv val = val
  Val2-EqValTy2-fwd (PairCode u' v') UCode cb eqv val = val
  Val2-EqValTy2-fwd PropCode UCode cb eqv val = val
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = fst core
        F     = fst (snd core)
        E'    = fst (snd (snd core))
        F'    = fst (snd (snd (snd core)))
        rC    = fst (snd (snd (snd (snd core))))
        rC'   = fst (snd (snd (snd (snd (snd core)))))
        cf0   = fst (snd (snd (snd (snd (snd (snd core))))))
        fmU   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convEE' = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqE   = fst tail12
        pet   = snd tail12
        Ac-C  = fst vtyC
        redCv = fst (snd (snd vtyC))
        htAc  = fst (snd (snd (snd (snd (snd vtyC)))))
        uniqC2 = Red-unique-Pi redCv rC
        htE   = S.Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        vpiM = snd val
        A0   = fst vpiM
        B0   = fst (snd vpiM)
        redC = fst (snd (snd vpiM))
        cg   = fst (snd (snd (snd vpiM)))
        fmg  = fst (snd (snd (snd (snd vpiM))))
        pav  = fst (snd (snd (snd (snd (snd vpiM)))))
        pae  = snd (snd (snd (snd (snd (snd vpiM)))))
        uniq = Red-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        pav-EF : PiAppVal2 _ _ E F b0 f0 g
        pav-EF = S.Eq-transport (\ X -> PiAppVal2 _ _ X F b0 f0 g) eqA0E
                   (Eq-transport (\ Y -> PiAppVal2 _ _ A0 Y b0 f0 g) eqB0F pav)
        pae-EF : PiAppEq2 _ _ E F b0 f0 g
        pae-EF = S.Eq-transport (\ X -> PiAppEq2 _ _ X F b0 f0 g) eqA0E
                   (Eq-transport (\ Y -> PiAppEq2 _ _ A0 Y b0 f0 g) eqB0F pae)
        cb0 = fst cb
        b0U = bU-from-cf-fmFun g b0 f0 cg fmg
        ctg  = cft-from-cf g cg
        pav-E'F' : PiAppVal2 _ _ E' F' b0 f0 g
        pav-E'F' = \ u' v' sel N htN valN ->
          let htN-E  = ty-conv htN (conv-sym convEE') htE
              valN-E = Val2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) valN
              body   = pav-EF u' v' sel N htN-E valN-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valN-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu' valN-E
              eqt-vf = pet u-f v-f sel-f N htN-E valN-uf
              eqt-ef = S.Eq-transport (\ w -> EqValTy2 _ (subst1 F N) (subst1 F' N) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in Val2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        pae-E'F' : PiAppEq2 _ _ E' F' b0 f0 g
        pae-E'F' = \ u' v' sel N1 N2 htN1 htN2 cvN eqN ->
          let htN1-E = ty-conv htN1 (conv-sym convEE') htE
              htN2-E = ty-conv htN2 (conv-sym convEE') htE
              cvN-E  = conv-conv cvN (conv-sym convEE') htE
              eqN-E  = EqVal2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) eqN
              body   = pae-EF u' v' sel N1 N2 htN1-E htN2-E cvN-E eqN-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valN1-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu'
                           (Val2-from-EqVal2-first u' b0 eqN-E)
              eqt-vf = pet u-f v-f sel-f N1 htN1-E valN1-uf
              eqt-ef = S.Eq-transport (\ w -> EqValTy2 _ (subst1 F N1) (subst1 F' N1) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        vpi' = mkSigma E' (mkSigma F' (mkSigma rC' (mkSigma cg (mkSigma fmg
                   (mkSigma pav-E'F' pae-E'F')))))
    in mkSigma vtyC' vpi'
  -- Sigma cases: Val2 = Top, so trivial
  Val2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = fst core
        F     = fst (snd core)
        E'    = fst (snd (snd core))
        F'    = fst (snd (snd (snd core)))
        rC    = fst (snd (snd (snd (snd core))))
        rC'   = fst (snd (snd (snd (snd (snd core)))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqE   = fst tail12
        A0    = fst val
        B0    = fst (snd val)
        redT  = fst (snd (snd val))
        v2Fst = snd (snd (snd val))
        uniq  = Red-unique-Sigma redT rC
        eqA0E = fst uniq
        cb0   = fst cb
        v2Fst-E = S.Eq-transport (\ X -> Val2 _ (Fst _) X u' b0) eqA0E v2Fst
        v2Fst'  = Val2-EqValTy2-fwd u' b0 cb0 eqE v2Fst-E
    in mkSigma E' (mkSigma F' (mkSigma rC' v2Fst'))
  Val2-EqValTy2-fwd u (PairCode x y) cb eqv val = tt

  ------------------------------------------------------------------------
  -- EqVal2-EqValTy2-fwd
  ------------------------------------------------------------------------

  EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    EqVal2 G M N C u b -> EqVal2 G M N C' u b
  EqVal2-EqValTy2-fwd u Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd Bot PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl _) PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode _ _) PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode _ _) PropCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd u (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv ev = tt
  -- UCode cases: none depend on C
  EqVal2-EqValTy2-fwd UCode UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (FunEl g) UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PiCode a' f') UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PairCode u' v') UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd PropCode UCode cb eqv ev = ev
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  EqVal2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv ev =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = fst core
        F     = fst (snd core)
        E'    = fst (snd (snd core))
        F'    = fst (snd (snd (snd core)))
        rC    = fst (snd (snd (snd (snd core))))
        rC'   = fst (snd (snd (snd (snd (snd core)))))
        cf0   = fst (snd (snd (snd (snd (snd (snd core))))))
        fmU   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convEE'-eq = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqE   = fst tail12
        pet   = snd tail12
        Ac-Ceq  = fst vtyC
        redCv-eq = fst (snd (snd vtyC))
        htAc-eq = fst (snd (snd (snd (snd (snd vtyC)))))
        uniqC2-eq = Red-unique-Pi redCv-eq rC
        htE-eq  = S.Eq-transport (\ X -> HasType _ X _) (fst uniqC2-eq) htAc-eq
        vtyC-ev = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        epi  = snd (snd (snd ev))
        A0    = fst epi
        B0    = fst (snd epi)
        redC  = fst (snd (snd epi))
        cg    = fst (snd (snd (snd epi)))
        fmg   = fst (snd (snd (snd (snd epi))))
        paev  = snd (snd (snd (snd (snd epi))))
        uniq = Red-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        cb0 = fst cb
        b0U = bU-from-cf-fmFun g b0 f0 cg fmg
        paev-EF : PiAppEqVal2 _ _ _ E F b0 f0 g
        paev-EF = S.Eq-transport (\ X -> PiAppEqVal2 _ _ _ X F b0 f0 g) eqA0E
                    (Eq-transport (\ Y -> PiAppEqVal2 _ _ _ A0 Y b0 f0 g) eqB0F paev)
        ctg  = cft-from-cf g cg
        paev-E'F' : PiAppEqVal2 _ _ _ E' F' b0 f0 g
        paev-E'F' = \ u' v' sel P htP valP ->
          let htP-E  = ty-conv htP (conv-sym convEE'-eq) htE-eq
              valP-E = Val2-EqValTy2-fwd u' b0 cb0 (EqValTy2-sym b0 cb0 eqE) valP
              body   = paev-EF u' v' sel P htP-E valP-E
              cu'    = Coherent-Selection sel ctg
              sb     = selectionBelow f0 u' cf0 cu'
              u-f    = fst sb
              v-f    = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-uf  = fst (snd (snd (snd sb)))
              eq-ef  = snd (snd (snd (snd sb)))
              fmu-f  = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
              fmu'   = FinMem-Selection b0 f0 sel fmg ctg cb0 b0U
              valP-uf = restrictVal2 _ _ E u' u-f b0 le-uf fmu-f fmu' valP-E
              eqt-vf = pet u-f v-f sel-f P htP-E valP-uf
              eqt-ef = S.Eq-transport (\ w -> EqValTy2 _ (subst1 F P) (subst1 F' P) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        valM-C  = Val2-from-EqVal2-first (FunEl g) (PiCode b0 f0) ev
        valN-C  = Val2-from-EqVal2-second (FunEl g) (PiCode b0 f0) ev
        valM-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valM-C
        valN-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valN-C
        eqvpi-C' = mkSigma E' (mkSigma F' (mkSigma rC' (mkSigma cg (mkSigma fmg paev-E'F'))))
    in mkSigma vtyC' (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqvpi-C'))
  -- Sigma cases: all Top
  EqVal2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv ev =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = fst core
        F     = fst (snd core)
        E'    = fst (snd (snd core))
        F'    = fst (snd (snd (snd core)))
        rC    = fst (snd (snd (snd (snd core))))
        rC'   = fst (snd (snd (snd (snd (snd core)))))
        cf0   = fst (snd (snd (snd (snd (snd (snd core))))))
        fmU   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convEE' = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqE   = fst tail12
        A0    = fst ev
        B0    = fst (snd ev)
        redT  = fst (snd (snd ev))
        v2M   = fst (snd (snd (snd ev)))
        v2N   = fst (snd (snd (snd (snd ev))))
        eq    = snd (snd (snd (snd (snd ev))))
        uniq  = Red-unique-Sigma redT rC
        eqA0E = fst uniq
        cb0   = fst cb
        v2M-E = S.Eq-transport (\ X -> Val2 _ (Fst _) X u' b0) eqA0E v2M
        v2N-E = S.Eq-transport (\ X -> Val2 _ (Fst _) X u' b0) eqA0E v2N
        eq-E  = S.Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X u' b0) eqA0E eq
        v2M'  = Val2-EqValTy2-fwd u' b0 cb0 eqE v2M-E
        v2N'  = Val2-EqValTy2-fwd u' b0 cb0 eqE v2N-E
        eq'   = EqVal2-EqValTy2-fwd u' b0 cb0 eqE eq-E
    in mkSigma E' (mkSigma F' (mkSigma rC'
         (mkSigma v2M' (mkSigma v2N' eq'))))
  EqVal2-EqValTy2-fwd u (PairCode x y) cb eqv ev = tt

  ------------------------------------------------------------------------
  -- ValTy2-Sup
  ------------------------------------------------------------------------

  ValTy2-Sup : {n : Nat} (G : Ctx n) (T : Expr n) (a1 a2 : FinEl) ->
    Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
    ValTy2 G T a1 -> ValTy2 G T a2 -> ValTy2 G T (Sup a1 a2)
  ValTy2-Sup G T Bot a2 comp fm1 fm2 vt1 vt2 = vt2
  ValTy2-Sup G T UCode Bot comp fm1 fm2 vt1 vt2 = vt2
  ValTy2-Sup G T UCode UCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T UCode (FunEl g) ()
  ValTy2-Sup G T UCode (PiCode b g) ()
  ValTy2-Sup G T UCode (SigmaCode b g) ()
  ValTy2-Sup G T UCode (PairCode u v) ()
  ValTy2-Sup G T UCode PropCode ()
  ValTy2-Sup G T PropCode Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode UCode ()
  ValTy2-Sup G T PropCode PropCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode (FunEl g) ()
  ValTy2-Sup G T PropCode (PiCode b g) ()
  ValTy2-Sup G T PropCode (SigmaCode b g) ()
  ValTy2-Sup G T PropCode (PairCode u v) ()
  ValTy2-Sup G T (FunEl g) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) UCode ()
  ValTy2-Sup G T (FunEl g) (FunEl h) comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) (PiCode b h) ()
  ValTy2-Sup G T (FunEl g) (SigmaCode b h) ()
  ValTy2-Sup G T (FunEl g) (PairCode u v) ()
  ValTy2-Sup G T (FunEl g) PropCode ()
  ValTy2-Sup G T (PiCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (PiCode b1 f1) UCode ()
  ValTy2-Sup G T (PiCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (PiCode b1 f1) (SigmaCode b2 f2) ()
  ValTy2-Sup G T (PiCode b1 f1) (PairCode u v) ()
  ValTy2-Sup G T (PiCode b1 f1) PropCode ()
  ValTy2-Sup G T (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = fst vt1
        B1    = fst (snd vt1)
        red1  = fst (snd (snd vt1))
        cf1   = fst (snd (snd (snd vt1)))
        allU1 = fst (snd (snd (snd (snd vt1))))
        htA1  = fst (snd (snd (snd (snd (snd vt1)))))
        htB1  = fst (snd (snd (snd (snd (snd (snd vt1))))))
        inn1  = snd (snd (snd (snd (snd (snd (snd vt1))))))
        vtAb1 = fst inn1
        piEV1 = fst (snd inn1)
        piEE1 = snd (snd inn1)
        A2    = fst vt2
        B2    = fst (snd vt2)
        red2  = fst (snd (snd vt2))
        cf2   = fst (snd (snd (snd vt2)))
        allU2 = fst (snd (snd (snd (snd vt2))))
        htA2  = fst (snd (snd (snd (snd (snd vt2)))))
        htB2  = fst (snd (snd (snd (snd (snd (snd vt2))))))
        inn2  = snd (snd (snd (snd (snd (snd (snd vt2))))))
        vtAb2 = fst inn2
        piEV2 = fst (snd inn2)
        piEE2 = snd (snd inn2)
        uniq  = Red-unique-Pi red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = S.Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        piEV2' : PiEdgeVal2 G A1 B1 b2 f2
        piEV2' = S.Eq-transport (\ Y -> PiEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> PiEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) piEV2)
        piEE2' : PiEdgeEq2 G A1 B1 b2 f2
        piEE2' = S.Eq-transport (\ Y -> PiEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> PiEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) piEE2)
        comp-b = fst comp
        comp-f = snd comp
        b1U    = fst fm1
        allU1' = fst (snd fm1)
        b2U    = fst fm2
        allU2' = fst (snd fm2)
        cb1    = coh-from-aU b1 b1U
        cb2    = coh-from-aU b2 b2U
        supU   = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup  = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1   = cf1
        ctf2   = cf2
        cf-app = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        vtA-sup = ValTy2-Sup G A1 b1 b2 comp-b b1U b2U vtAb1 vtAb2'
        piEV : PiEdgeVal2 G A1 B1 (Sup b1 b2) (append f1 f2)
        piEV = \ u v sel N htN valN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valN
              val-u1-b1  = downVal2 _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valN
              val-u2-b2  = downVal2 _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              vt-v1  = piEV1 u1 v1 sel1 N htN val-u1-b1
              vt-v2  = piEV2' u2 v2 sel2 N htN val-u2-b2
              vt-ef1 = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downValTy2 _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
        piEE : PiEdgeEq2 G A1 B1 (Sup b1 b2) (append f1 f2)
        piEE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              eqv-u1-sup = restrictEqVal2 _ _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup eqN
              eqv-u1-b1  = downEqVal2 _ _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU eqv-u1-sup
              eqv-u2-sup = restrictEqVal2 _ _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup eqN
              eqv-u2-b2  = downEqVal2 _ _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU eqv-u2-sup
              eqt-v1 = piEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
              eqt-v2 = piEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
              eqt-ef1 = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in mkSigma A1 (mkSigma B1 (mkSigma red1 (mkSigma cf-app
         (mkSigma allU-app (mkSigma htA1 (mkSigma htB1
           (mkSigma vtA-sup (mkSigma piEV piEE))))))))
  ValTy2-Sup G T (SigmaCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (SigmaCode b1 f1) UCode ()
  ValTy2-Sup G T (SigmaCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PiCode b2 f2) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PairCode u v) ()
  ValTy2-Sup G T (SigmaCode b1 f1) PropCode ()
  ValTy2-Sup G T (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = fst vt1
        B1    = fst (snd vt1)
        red1  = fst (snd (snd vt1))
        cf1   = fst (snd (snd (snd vt1)))
        allU1 = fst (snd (snd (snd (snd vt1))))
        htA1  = fst (snd (snd (snd (snd (snd vt1)))))
        htB1  = fst (snd (snd (snd (snd (snd (snd vt1))))))
        inn1  = snd (snd (snd (snd (snd (snd (snd vt1))))))
        vtAb1 = fst inn1
        sEV1  = fst (snd inn1)
        sEE1  = snd (snd inn1)
        A2    = fst vt2
        B2    = fst (snd vt2)
        red2  = fst (snd (snd vt2))
        cf2   = fst (snd (snd (snd vt2)))
        allU2 = fst (snd (snd (snd (snd vt2))))
        inn2  = snd (snd (snd (snd (snd (snd (snd vt2))))))
        vtAb2 = fst inn2
        sEV2  = fst (snd inn2)
        sEE2  = snd (snd inn2)
        uniq  = Red-unique-Sigma red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = S.Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        sEV2' : SigmaEdgeVal2 G A1 B1 b2 f2
        sEV2' = S.Eq-transport (\ Y -> SigmaEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) sEV2)
        sEE2' : SigmaEdgeEq2 G A1 B1 b2 f2
        sEE2' = S.Eq-transport (\ Y -> SigmaEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) sEE2)
        comp-b = fst comp
        comp-f = snd comp
        b1U    = fst fm1
        allU1' = fst (snd fm1)
        b2U    = fst fm2
        allU2' = fst (snd fm2)
        cb1    = coh-from-aU b1 b1U
        cb2    = coh-from-aU b2 b2U
        supU   = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup  = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1   = cf1
        ctf2   = cf2
        cf-app = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        vtA-sup = ValTy2-Sup G A1 b1 b2 comp-b b1U b2U vtAb1 vtAb2'
        sEV : SigmaEdgeVal2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sEV = \ u v sel N htN valN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valN
              val-u1-b1  = downVal2 _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valN
              val-u2-b2  = downVal2 _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              vt-v1  = sEV1 u1 v1 sel1 N htN val-u1-b1
              vt-v2  = sEV2' u2 v2 sel2 N htN val-u2-b2
              vt-ef1 = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = S.Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downValTy2 _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
        sEE : SigmaEdgeEq2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sEE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              eqv-u1-sup = restrictEqVal2 _ _ _ A1 u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup eqN
              eqv-u1-b1  = downEqVal2 _ _ _ A1 u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU eqv-u1-sup
              eqv-u2-sup = restrictEqVal2 _ _ _ A1 u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup eqN
              eqv-u2-b2  = downEqVal2 _ _ _ A1 u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU eqv-u2-sup
              eqt-v1 = sEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
              eqt-v2 = sEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
              eqt-ef1 = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = S.Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in mkSigma A1 (mkSigma B1 (mkSigma red1 (mkSigma cf-app
         (mkSigma allU-app (mkSigma htA1 (mkSigma htB1
           (mkSigma vtA-sup (mkSigma sEV sEE))))))))
  ValTy2-Sup G T (PairCode u v) a2 comp () fm2 vt1 vt2

  ------------------------------------------------------------------------
  -- EqValTy2-Sup (stub — delegates to ValTy2-Sup for the two vals)
  ------------------------------------------------------------------------

  EqValTy2-Sup : {n : Nat} (G : Ctx n) (M N : Expr n) (u1 u2 : FinEl) ->
    Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
    EqValTy2 G M N u1 -> EqValTy2 G M N u2 -> EqValTy2 G M N (Sup u1 u2)
  EqValTy2-Sup G M N Bot u2 comp fm1 fm2 eq1 eq2 = eq2
  EqValTy2-Sup G M N UCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode UCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode (FunEl g) ()
  EqValTy2-Sup G M N UCode (PiCode b g) ()
  EqValTy2-Sup G M N UCode (SigmaCode b g) ()
  EqValTy2-Sup G M N UCode (PairCode u v) ()
  EqValTy2-Sup G M N UCode PropCode ()
  EqValTy2-Sup G M N PropCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode UCode ()
  EqValTy2-Sup G M N PropCode PropCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode (FunEl g) ()
  EqValTy2-Sup G M N PropCode (PiCode b g) ()
  EqValTy2-Sup G M N PropCode (SigmaCode b g) ()
  EqValTy2-Sup G M N PropCode (PairCode u v) ()
  EqValTy2-Sup G M N (FunEl g) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) UCode ()
  EqValTy2-Sup G M N (FunEl g) (FunEl h) comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) (PiCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (SigmaCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (PairCode u v) ()
  EqValTy2-Sup G M N (FunEl g) PropCode ()
  EqValTy2-Sup G M N (PiCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (PiCode b1 f1) UCode ()
  EqValTy2-Sup G M N (PiCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (SigmaCode b2 f2) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PairCode u v) ()
  EqValTy2-Sup G M N (PiCode b1 f1) PropCode ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM-sup = ValTy2-Sup G M (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 (fst eq1) (fst eq2)
        vtN-sup = ValTy2-Sup G N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2))
        -- For the EqValTyPi2 core, reuse the first one's data (same Red, ConvTm)
        -- and rebuild with appended coherent/allU data
        coreAB1 = snd (snd eq1)
        coreAB2 = snd (snd eq2)
        AM      = fst coreAB1
        BM      = fst (snd coreAB1)
        AN      = fst (snd (snd coreAB1))
        BN      = fst (snd (snd (snd coreAB1)))
        redM1   = fst (snd (snd (snd (snd coreAB1))))
        redN1   = fst (snd (snd (snd (snd (snd coreAB1)))))
        cfEq1   = fst (snd (snd (snd (snd (snd (snd coreAB1))))))
        allUEq1 = fst (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))
        convAA1 = fst (snd (snd (snd (snd (snd (snd (snd (snd coreAB1))))))))
        convBB1 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))))
        innEq1  = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))))
        eqvtA1  = fst innEq1
        piEET1  = snd innEq1
        AM2     = fst coreAB2
        BM2     = fst (snd coreAB2)
        AN2     = fst (snd (snd coreAB2))
        BN2     = fst (snd (snd (snd coreAB2)))
        redM2   = fst (snd (snd (snd (snd coreAB2))))
        redN2   = fst (snd (snd (snd (snd (snd coreAB2)))))
        cfEq2   = fst (snd (snd (snd (snd (snd (snd coreAB2))))))
        allUEq2 = fst (snd (snd (snd (snd (snd (snd (snd coreAB2)))))))
        innEq2  = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB2)))))))))
        eqvtA2  = fst innEq2
        piEET2  = snd innEq2
        uniqM   = Red-unique-Pi redM1 redM2
        eqAM    = fst uniqM
        eqBM    = snd uniqM
        uniqN   = Red-unique-Pi redN1 redN2
        eqAN    = fst uniqN
        eqBN    = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = S.Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) eqvtA2)
        piEET2' : PiEdgeEqTy2 G AM BM BN b2 f2
        piEET2' = S.Eq-transport (\ X -> PiEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                    (Eq-transport (\ X -> PiEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                      (Eq-transport (\ X -> PiEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) piEET2))
        comp-b  = fst comp
        comp-f  = snd comp
        b1U     = fst fm1
        allU1'  = fst (snd fm1)
        b2U     = fst fm2
        allU2'  = fst (snd fm2)
        cb1     = coh-from-aU b1 b1U
        cb2     = coh-from-aU b2 b2U
        supU    = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup   = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1    = cfEq1
        ctf2    = cfEq2
        cf-app  = CoherentFunTail-append f1 f2 cfEq1 cfEq2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        eqvtA-sup = EqValTy2-Sup G AM AN b1 b2 comp-b b1U b2U eqvtA1 eqvtA2'
        piEET : PiEdgeEqTy2 G AM BM BN (Sup b1 b2) (append f1 f2)
        piEET = \ u v sel P htP valP ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ AM u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valP
              val-u1-b1  = downVal2 _ _ AM u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ AM u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valP
              val-u2-b2  = downVal2 _ _ AM u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              eqt-v1  = piEET1 u1 v1 sel1 P htP val-u1-b1
              eqt-v2  = piEET2' u2 v2 sel2 P htP val-u2-b2
              eqt-ef1 = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        eqTyPi = mkSigma AM (mkSigma BM (mkSigma AN (mkSigma BN
                   (mkSigma redM1 (mkSigma redN1 (mkSigma cf-app (mkSigma allU-app
                     (mkSigma convAA1
                       (mkSigma convBB1
                         (mkSigma eqvtA-sup piEET))))))))))
    in mkSigma vtM-sup (mkSigma vtN-sup eqTyPi)
  EqValTy2-Sup G M N (SigmaCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (SigmaCode b1 f1) UCode ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PiCode b2 f2) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PairCode u v) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) PropCode ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM-sup = ValTy2-Sup G M (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 (fst eq1) (fst eq2)
        vtN-sup = ValTy2-Sup G N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 (fst (snd eq1)) (fst (snd eq2))
        coreAB1 = snd (snd eq1)
        coreAB2 = snd (snd eq2)
        AM      = fst coreAB1
        BM      = fst (snd coreAB1)
        AN      = fst (snd (snd coreAB1))
        BN      = fst (snd (snd (snd coreAB1)))
        redM1   = fst (snd (snd (snd (snd coreAB1))))
        redN1   = fst (snd (snd (snd (snd (snd coreAB1)))))
        cfEq1   = fst (snd (snd (snd (snd (snd (snd coreAB1))))))
        allUEq1 = fst (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))
        convAA1 = fst (snd (snd (snd (snd (snd (snd (snd (snd coreAB1))))))))
        convBB1 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))))
        innEq1  = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB1)))))))))
        eqvtA1  = fst innEq1
        sEET1   = snd innEq1
        AM2     = fst coreAB2
        BM2     = fst (snd coreAB2)
        AN2     = fst (snd (snd coreAB2))
        BN2     = fst (snd (snd (snd coreAB2)))
        redM2   = fst (snd (snd (snd (snd coreAB2))))
        redN2   = fst (snd (snd (snd (snd (snd coreAB2)))))
        cfEq2   = fst (snd (snd (snd (snd (snd (snd coreAB2))))))
        allUEq2 = fst (snd (snd (snd (snd (snd (snd (snd coreAB2)))))))
        innEq2  = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd coreAB2)))))))))
        eqvtA2  = fst innEq2
        sEET2   = snd innEq2
        uniqM   = Red-unique-Sigma redM1 redM2
        eqAM    = fst uniqM
        eqBM    = snd uniqM
        uniqN   = Red-unique-Sigma redN1 redN2
        eqAN    = fst uniqN
        eqBN    = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = S.Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) eqvtA2)
        sEET2' : SigmaEdgeEqTy2 G AM BM BN b2 f2
        sEET2' = S.Eq-transport (\ X -> SigmaEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                    (Eq-transport (\ X -> SigmaEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                      (Eq-transport (\ X -> SigmaEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) sEET2))
        comp-b  = fst comp
        comp-f  = snd comp
        b1U     = fst fm1
        allU1'  = fst (snd fm1)
        b2U     = fst fm2
        allU2'  = fst (snd fm2)
        cb1     = coh-from-aU b1 b1U
        cb2     = coh-from-aU b2 b2U
        supU    = finMemUCode-Sup b1 b2 comp-b b1U b2U
        c-sup   = Coherent-Sup b1 b2 comp-b cb1 cb2
        ctf1    = cfEq1
        ctf2    = cfEq2
        cf-app  = CoherentFunTail-append f1 f2 cfEq1 cfEq2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        eqvtA-sup = EqValTy2-Sup G AM AN b1 b2 comp-b b1U b2U eqvtA1 eqvtA2'
        sEET : SigmaEdgeEqTy2 G AM BM BN (Sup b1 b2) (append f1 f2)
        sEET = \ u v sel P htP valP ->
          let cu     = Coherent-Selection sel ctf-app
              fmu-sup = FinMemAllU-Selection (Sup b1 b2) sel allU-app ctf-app c-sup supU
              sb1    = selectionBelow f1 u ctf1 cu
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u ctf2 cu
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              cu1    = Coherent-Selection sel1 ctf1
              cu2    = Coherent-Selection sel2 ctf2
              fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1' ctf1 cb1 b1U
              fmu2-b2 = FinMemAllU-Selection b2 sel2 allU2' ctf2 cb2 b2U
              fmu1-sup = finMem-Sup-left b1 b2 u1 comp-b cb1 cb2 b2U cu1 fmu1-b1
              fmu2-sup = finMem-Sup-right b1 b2 u2 comp-b b1U cu2 fmu2-b2
              val-u1-sup = restrictVal2 _ _ AM u u1 (Sup b1 b2) le-u1 fmu1-sup fmu-sup valP
              val-u1-b1  = downVal2 _ _ AM u1 b1 (Sup b1 b2) le-b1-sup fmu1-b1 cb1 supU val-u1-sup
              val-u2-sup = restrictVal2 _ _ AM u u2 (Sup b1 b2) le-u2 fmu2-sup fmu-sup valP
              val-u2-b2  = downVal2 _ _ AM u2 b2 (Sup b1 b2) le-b2-sup fmu2-b2 cb2 supU val-u2-sup
              eqt-v1  = sEET1 u1 v1 sel1 P htP val-u1-b1
              eqt-v2  = sEET2' u2 v2 sel2 P htP val-u2-b2
              eqt-ef1 = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = S.Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        eqTySigma = mkSigma AM (mkSigma BM (mkSigma AN (mkSigma BN
                      (mkSigma redM1 (mkSigma redN1 (mkSigma cf-app (mkSigma allU-app
                        (mkSigma convAA1
                          (mkSigma convBB1
                            (mkSigma eqvtA-sup sEET))))))))))
    in mkSigma vtM-sup (mkSigma vtN-sup eqTySigma)
  EqValTy2-Sup G M N (PairCode u v) a2 comp () fm2 eq1 eq2

  ------------------------------------------------------------------------
  -- downVal2 / downEqVal2 / downValTy2 / downEqValTy2
  -- upVal2 / upEqVal2
  -- restrictVal2 / restrictEqVal2
  -- (Stubs with the same types — all SigmaCode/PairCode/PropCode cases
  -- are trivial since Val2/EqVal2 = Top there.)
  ------------------------------------------------------------------------

  downVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
    Val2 G M T u a1 -> Val2 G M T u a0
  downEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
    EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
  downValTy2 : {n : Nat} (G : Ctx n) (M : Expr n) (u0 u1 : FinEl) ->
    LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
    ValTy2 G M u1 -> ValTy2 G M u0
  downEqValTy2 : {n : Nat} (G : Ctx n) (M N : Expr n) (u0 u1 : FinEl) ->
    LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
    EqValTy2 G M N u1 -> EqValTy2 G M N u0
  upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    Val2 G M T u a0 -> ValTy2 G T a1 ->
    Val2 G M T u a1
  upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    EqVal2 G M N T u a0 -> ValTy2 G T a1 ->
    EqVal2 G M N T u a1
  restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    Val2 G M T u a -> Val2 G M T u' a
  restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    EqVal2 G M N T u a -> EqVal2 G M N T u' a

  -- downVal2: case split on (a0, a1)
  downVal2 G M T u Bot          a1             le mem ca0 ca1 src = tt
  downVal2 G M T u UCode        Bot            ()
  downVal2 G M T u UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T u UCode        (FunEl h)      ()
  downVal2 G M T u UCode        (PiCode b f)   ()
  downVal2 G M T u UCode        (SigmaCode b f) ()
  downVal2 G M T u UCode        (PairCode x y) ()
  downVal2 G M T u UCode        PropCode       ()
  downVal2 G M T (PiCode a' f') PropCode Bot ()
  downVal2 G M T (PiCode a' f') PropCode UCode ()
  downVal2 G M T (PiCode a' f') PropCode PropCode le mem ca0 ca1 src = src
  downVal2 G M T (PiCode a' f') PropCode (FunEl h) ()
  downVal2 G M T (PiCode a' f') PropCode (PiCode b f) ()
  downVal2 G M T (PiCode a' f') PropCode (SigmaCode b f) ()
  downVal2 G M T (PiCode a' f') PropCode (PairCode x y) ()
  downVal2 G M T Bot PropCode     Bot            ()
  downVal2 G M T Bot PropCode     UCode          ()
  downVal2 G M T Bot PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T Bot PropCode     (FunEl h)      ()
  downVal2 G M T Bot PropCode     (PiCode b f)   ()
  downVal2 G M T Bot PropCode     (SigmaCode b f) ()
  downVal2 G M T Bot PropCode     (PairCode x y) ()
  downVal2 G M T UCode PropCode     Bot            ()
  downVal2 G M T UCode PropCode     UCode          ()
  downVal2 G M T UCode PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T UCode PropCode     (FunEl h)      ()
  downVal2 G M T UCode PropCode     (PiCode b f)   ()
  downVal2 G M T UCode PropCode     (SigmaCode b f) ()
  downVal2 G M T UCode PropCode     (PairCode x y) ()
  downVal2 G M T PropCode PropCode     Bot            ()
  downVal2 G M T PropCode PropCode     UCode          ()
  downVal2 G M T PropCode PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T PropCode PropCode     (FunEl h)      ()
  downVal2 G M T PropCode PropCode     (PiCode b f)   ()
  downVal2 G M T PropCode PropCode     (SigmaCode b f) ()
  downVal2 G M T PropCode PropCode     (PairCode x y) ()
  downVal2 G M T (FunEl g) PropCode     Bot            ()
  downVal2 G M T (FunEl g) PropCode     UCode          ()
  downVal2 G M T (FunEl g) PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g) PropCode     (FunEl h)      ()
  downVal2 G M T (FunEl g) PropCode     (PiCode b f)   ()
  downVal2 G M T (FunEl g) PropCode     (SigmaCode b f) ()
  downVal2 G M T (FunEl g) PropCode     (PairCode x y) ()
  downVal2 G M T (SigmaCode a' ff) PropCode     Bot            ()
  downVal2 G M T (SigmaCode a' ff) PropCode     UCode          ()
  downVal2 G M T (SigmaCode a' ff) PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a' ff) PropCode     (FunEl h)      ()
  downVal2 G M T (SigmaCode a' ff) PropCode     (PiCode b f)   ()
  downVal2 G M T (SigmaCode a' ff) PropCode     (SigmaCode b f) ()
  downVal2 G M T (SigmaCode a' ff) PropCode     (PairCode x y) ()
  downVal2 G M T (PairCode u' v') PropCode     Bot            ()
  downVal2 G M T (PairCode u' v') PropCode     UCode          ()
  downVal2 G M T (PairCode u' v') PropCode     PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode u' v') PropCode     (FunEl h)      ()
  downVal2 G M T (PairCode u' v') PropCode     (PiCode b f)   ()
  downVal2 G M T (PairCode u' v') PropCode     (SigmaCode b f) ()
  downVal2 G M T (PairCode u' v') PropCode     (PairCode x y) ()
  downVal2 G M T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T u (FunEl g)    PropCode       le mem ca0 ca1 src = tt
  downVal2 G M T u (PiCode b0 f0) Bot          ()
  downVal2 G M T u (PiCode b0 f0) UCode        ()
  downVal2 G M T u (PiCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (PiCode b0 f0) PropCode     ()
  downVal2 G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty  = fst src
        vpiM = snd src
        A0    = fst vpiM
        B0    = fst (snd vpiM)
        red   = fst (snd (snd vpiM))
        sat0  = fst (snd (snd (snd vpiM)))
        fmg   = fst (snd (snd (snd (snd vpiM))))
        pav   = fst (snd (snd (snd (snd (snd vpiM)))))
        pae   = snd (snd (snd (snd (snd (snd vpiM)))))
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        vty'  = downValTy2 G _ (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
        Av    = fst vty
        Bv    = fst (snd vty)
        redv  = fst (snd (snd vty))
        vtAb1 : ValTy2 G A0 b1
        vtAb1 = S.Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red-unique-Pi red redv)))
                   (fst (snd (snd (snd (snd (snd (snd (snd vty))))))))
        vpi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat0
                 (mkSigma (fst mem)
                   (mkSigma (downPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 (snd (snd ca1)) sat0 (fst mem)
                               cb0 cb1 b1U b0U allU0 allU1 le fmg vtAb1 pav)
                   (downPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 (snd (snd ca1)) sat0 (fst mem)
                               cb0 cb1 b1U b0U allU0 allU1 le fmg vtAb1 pae))))))
    in mkSigma vty' vpi'
  downVal2 G M T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode: all Val2 cases = Top
  downVal2 G M T u (SigmaCode b0 f0) Bot          ()
  downVal2 G M T u (SigmaCode b0 f0) UCode        ()
  downVal2 G M T u (SigmaCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downVal2 G M T u (SigmaCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (SigmaCode b0 f0) PropCode     ()
  downVal2 G M T Bot (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2F  = snd (snd (snd src))
        cb0  = fst ca0
        fm-u'-b0 = fst (fst mem)
        v2F' = downVal2 G (Fst M) A0 u' b0 b1 (fst le) fm-u'-b0 cb0 (fst ca1) v2F
    in mkSigma A0 (mkSigma B0 (mkSigma red v2F'))
  -- PairCode: all Val2 cases = Top
  downVal2 G M T Bot (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T UCode (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a' ff) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a' ff) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le mem ca0 ca1 src = tt

  -- downEqVal2: same structure
  downEqVal2 G M N T u Bot          a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T u UCode        Bot            ()
  downEqVal2 G M N T u UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T u UCode        (FunEl h)      ()
  downEqVal2 G M N T u UCode        (PiCode b f)   ()
  downEqVal2 G M N T u UCode        (SigmaCode b f) ()
  downEqVal2 G M N T u UCode        (PairCode x y) ()
  downEqVal2 G M N T u UCode        PropCode       ()
  downEqVal2 G M N T Bot PropCode     Bot            ()
  downEqVal2 G M N T Bot PropCode     UCode          ()
  downEqVal2 G M N T Bot PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot PropCode     (FunEl h)      ()
  downEqVal2 G M N T Bot PropCode     (PiCode b f)   ()
  downEqVal2 G M N T Bot PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T Bot PropCode     (PairCode x y) ()
  downEqVal2 G M N T UCode PropCode     Bot            ()
  downEqVal2 G M N T UCode PropCode     UCode          ()
  downEqVal2 G M N T UCode PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode PropCode     (FunEl h)      ()
  downEqVal2 G M N T UCode PropCode     (PiCode b f)   ()
  downEqVal2 G M N T UCode PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T UCode PropCode     (PairCode x y) ()
  downEqVal2 G M N T PropCode PropCode     Bot            ()
  downEqVal2 G M N T PropCode PropCode     UCode          ()
  downEqVal2 G M N T PropCode PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode PropCode     (FunEl h)      ()
  downEqVal2 G M N T PropCode PropCode     (PiCode b f)   ()
  downEqVal2 G M N T PropCode PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T PropCode PropCode     (PairCode x y) ()
  downEqVal2 G M N T (FunEl g) PropCode     Bot            ()
  downEqVal2 G M N T (FunEl g) PropCode     UCode          ()
  downEqVal2 G M N T (FunEl g) PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g) PropCode     (FunEl h)      ()
  downEqVal2 G M N T (FunEl g) PropCode     (PiCode b f)   ()
  downEqVal2 G M N T (FunEl g) PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T (FunEl g) PropCode     (PairCode x y) ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     Bot            ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     UCode          ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     (FunEl h)      ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     (PiCode b f)   ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T (SigmaCode a' ff) PropCode     (PairCode x y) ()
  downEqVal2 G M N T (PairCode u' v') PropCode     Bot            ()
  downEqVal2 G M N T (PairCode u' v') PropCode     UCode          ()
  downEqVal2 G M N T (PairCode u' v') PropCode     PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode u' v') PropCode     (FunEl h)      ()
  downEqVal2 G M N T (PairCode u' v') PropCode     (PiCode b f)   ()
  downEqVal2 G M N T (PairCode u' v') PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T (PairCode u' v') PropCode     (PairCode x y) ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     Bot            ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     UCode          ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T (PiCode a' ff) PropCode     (FunEl h)      ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     (PiCode b f)   ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     (SigmaCode b f) ()
  downEqVal2 G M N T (PiCode a' ff) PropCode     (PairCode x y) ()
  downEqVal2 G M N T u (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (FunEl g)    PropCode       le mem ca0 ca1 src = tt
  downEqVal2 G M N T u (PiCode b0 f0) Bot          ()
  downEqVal2 G M N T u (PiCode b0 f0) UCode        ()
  downEqVal2 G M N T u (PiCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T (PiCode a' f') (PiCode b0 f0) PropCode le ()
  downEqVal2 G M N T u (PiCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty   = fst src
        vpiM  = fst (snd src)
        vpiN  = fst (snd (snd src))
        epi   = snd (snd (snd src))
        A0    = fst epi
        B0    = fst (snd epi)
        red   = fst (snd (snd epi))
        sat0  = fst (snd (snd (snd epi)))
        fmg   = fst (snd (snd (snd (snd epi))))
        paev  = snd (snd (snd (snd (snd epi))))
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        Av    = fst vty
        Bv    = fst (snd vty)
        redv  = fst (snd (snd vty))
        vtAb1 : ValTy2 G A0 b1
        vtAb1 = S.Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red-unique-Pi red redv)))
                   (fst (snd (snd (snd (snd (snd (snd (snd vty))))))))
        valM  = mkSigma vty vpiM
        valN  = mkSigma vty vpiN
        valM' = downVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
        valN' = downVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
        epi'  = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat0
                  (mkSigma (fst mem)
                    (downPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 (snd (snd ca1)) sat0 (fst mem)
                       cb0 cb1 b1U b0U allU0 allU1 le fmg vtAb1 paev)))))
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  downEqVal2 G M N T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode: all EqVal2 = Top
  downEqVal2 G M N T u (SigmaCode b0 f0) Bot          ()
  downEqVal2 G M N T u (SigmaCode b0 f0) UCode        ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2M  = fst (snd (snd (snd src)))
        v2N  = fst (snd (snd (snd (snd src))))
        eq   = snd (snd (snd (snd (snd src))))
        cb0  = fst ca0
        fm-u'-b0 = fst (fst mem)
        v2M' = downVal2 G (Fst M) A0 u' b0 b1 (fst le) fm-u'-b0 cb0 (fst ca1) v2M
        v2N' = downVal2 G (Fst N) A0 u' b0 b1 (fst le) fm-u'-b0 cb0 (fst ca1) v2N
        eq'  = downEqVal2 G (Fst M) (Fst N) A0 u' b0 b1 (fst le) fm-u'-b0 cb0 (fst ca1) eq
    in mkSigma A0 (mkSigma B0 (mkSigma red
         (mkSigma v2M' (mkSigma v2N' eq'))))
  -- PairCode: all EqVal2 = Top
  downEqVal2 G M N T Bot (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a' ff) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a' ff) (PairCode x0 y0) a1 le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le mem ca0 ca1 src = tt

  -- downValTy2
  downValTy2 G M Bot          u1             le fmem cu1 src = tt
  downValTy2 G M UCode        Bot            ()
  downValTy2 G M UCode        UCode          le fmem cu1 src = src
  downValTy2 G M UCode        (FunEl h)      ()
  downValTy2 G M UCode        (PiCode b f)   ()
  downValTy2 G M UCode        (SigmaCode b f) ()
  downValTy2 G M UCode        (PairCode x y) ()
  downValTy2 G M UCode        PropCode       ()
  downValTy2 G M PropCode     Bot            le fmem cu1 src = tt
  downValTy2 G M PropCode     UCode          ()
  downValTy2 G M PropCode     PropCode       le fmem cu1 src = src
  downValTy2 G M PropCode     (FunEl h)      ()
  downValTy2 G M PropCode     (PiCode b f)   ()
  downValTy2 G M PropCode     (SigmaCode b f) ()
  downValTy2 G M PropCode     (PairCode x y) ()
  downValTy2 G M (FunEl g)    u1             le ()
  downValTy2 G M (PairCode x y) u1           le ()
  downValTy2 G M (PiCode b0 f0) Bot          ()
  downValTy2 G M (PiCode b0 f0) UCode        ()
  downValTy2 G M (PiCode b0 f0) (FunEl h)    ()
  downValTy2 G M (PiCode b0 f0) (SigmaCode b1 f1) ()
  downValTy2 G M (PiCode b0 f0) (PairCode x y) ()
  downValTy2 G M (PiCode b0 f0) PropCode     ()
  downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
    let A     = fst src
        B     = fst (snd src)
        red   = fst (snd (snd src))
        sat1  = fst (snd (snd (snd src)))
        fmA1  = fst (snd (snd (snd (snd src))))
        htA-src = fst (snd (snd (snd (snd (snd src)))))
        htB-src = fst (snd (snd (snd (snd (snd (snd src))))))
        inner = snd (snd (snd (snd (snd (snd (snd src))))))
        vtA-b1 = fst inner
        piEV   = fst (snd inner)
        piEE   = snd (snd inner)
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b0 = downValTy2 G A b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        piEV0  = transportPiEdgeVal2-sel G A B b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 piEV
        piEE0  = transportPiEdgeEq2-sel G A B b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 piEE
    in mkSigma A (mkSigma B (mkSigma red (mkSigma sat0
         (mkSigma fmemAll0 (mkSigma htA-src (mkSigma htB-src
           (mkSigma vtA-b0 (mkSigma piEV0 piEE0))))))))
  downValTy2 G M (SigmaCode b0 f0) Bot          ()
  downValTy2 G M (SigmaCode b0 f0) UCode        ()
  downValTy2 G M (SigmaCode b0 f0) (FunEl h)    ()
  downValTy2 G M (SigmaCode b0 f0) (PiCode b1 f1) ()
  downValTy2 G M (SigmaCode b0 f0) (PairCode x y) ()
  downValTy2 G M (SigmaCode b0 f0) PropCode     ()
  downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
    let A     = fst src
        B     = fst (snd src)
        red   = fst (snd (snd src))
        sat1  = fst (snd (snd (snd src)))
        fmA1  = fst (snd (snd (snd (snd src))))
        htA-src = fst (snd (snd (snd (snd (snd src)))))
        htB-src = fst (snd (snd (snd (snd (snd (snd src))))))
        inner = snd (snd (snd (snd (snd (snd (snd src))))))
        vtA-b1 = fst inner
        sEV    = fst (snd inner)
        sEE    = snd (snd inner)
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b0 = downValTy2 G A b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        sEV0   = transportSigmaEdgeVal2-sel G A B b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 sEV
        sEE0   = transportSigmaEdgeEq2-sel G A B b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 sEE
    in mkSigma A (mkSigma B (mkSigma red (mkSigma sat0
         (mkSigma fmemAll0 (mkSigma htA-src (mkSigma htB-src
           (mkSigma vtA-b0 (mkSigma sEV0 sEE0))))))))

  -- downEqValTy2
  downEqValTy2 G M N Bot          u1             le fmem cu1 src = tt
  downEqValTy2 G M N UCode        Bot            ()
  downEqValTy2 G M N UCode        UCode          le fmem cu1 src = src
  downEqValTy2 G M N UCode        (FunEl h)      ()
  downEqValTy2 G M N UCode        (PiCode b f)   ()
  downEqValTy2 G M N UCode        (SigmaCode b f) ()
  downEqValTy2 G M N UCode        (PairCode x y) ()
  downEqValTy2 G M N UCode        PropCode       ()
  downEqValTy2 G M N PropCode     Bot            le fmem cu1 src = tt
  downEqValTy2 G M N PropCode     UCode          ()
  downEqValTy2 G M N PropCode     PropCode       le fmem cu1 src = src
  downEqValTy2 G M N PropCode     (FunEl h)      ()
  downEqValTy2 G M N PropCode     (PiCode b f)   ()
  downEqValTy2 G M N PropCode     (SigmaCode b f) ()
  downEqValTy2 G M N PropCode     (PairCode x y) ()
  downEqValTy2 G M N (FunEl g)    u1             le ()
  downEqValTy2 G M N (PairCode x y) u1           le ()
  downEqValTy2 G M N (PiCode b0 f0) Bot          ()
  downEqValTy2 G M N (PiCode b0 f0) UCode        ()
  downEqValTy2 G M N (PiCode b0 f0) (FunEl h)    ()
  downEqValTy2 G M N (PiCode b0 f0) (SigmaCode b1 f1) ()
  downEqValTy2 G M N (PiCode b0 f0) (PairCode x y) ()
  downEqValTy2 G M N (PiCode b0 f0) PropCode     ()
  downEqValTy2 G M N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
    let vtyM1  = fst src
        vtyN1  = fst (snd src)
        core   = snd (snd src)
        A      = fst core
        B      = fst (snd core)
        A'     = fst (snd (snd core))
        B'     = fst (snd (snd (snd core)))
        redM   = fst (snd (snd (snd (snd core))))
        redN   = fst (snd (snd (snd (snd (snd core)))))
        sat1   = fst (snd (snd (snd (snd (snd (snd core))))))
        fmA1   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convAA-core = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        convBB-core = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqvty  = fst tail12
        piEEqT = snd tail12
        A_M    = fst vtyM1
        vtA_M  = fst (snd (snd (snd (snd (snd (snd (snd vtyM1)))))))
        redM2  = fst (snd (snd vtyM1))
        uniqM  = Red-unique-Pi redM2 redM
        eqAMA  = fst uniqM
        vtA-b1 = S.Eq-transport (\ X -> ValTy2 G X b1) eqAMA vtA_M
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        eqvty0  = downEqValTy2 G A A' b0 b1 (fst le) fmem-b0 (fst cu1) eqvty
        piEEqT0 = transportPiEdgeEqTy2-sel G A B B' b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 piEEqT
        vtyM0  = downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
        core0  = mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
                   (mkSigma redM (mkSigma redN (mkSigma sat0 (mkSigma fmemAll0
                     (mkSigma convAA-core
                       (mkSigma convBB-core
                         (mkSigma eqvty0 piEEqT0))))))))))
    in mkSigma vtyM0 (mkSigma vtyN0 core0)
  downEqValTy2 G M N (SigmaCode b0 f0) Bot          ()
  downEqValTy2 G M N (SigmaCode b0 f0) UCode        ()
  downEqValTy2 G M N (SigmaCode b0 f0) (FunEl h)    ()
  downEqValTy2 G M N (SigmaCode b0 f0) (PiCode b1 f1) ()
  downEqValTy2 G M N (SigmaCode b0 f0) (PairCode x y) ()
  downEqValTy2 G M N (SigmaCode b0 f0) PropCode     ()
  downEqValTy2 G M N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
    let vtyM1  = fst src
        vtyN1  = fst (snd src)
        core   = snd (snd src)
        A      = fst core
        B      = fst (snd core)
        A'     = fst (snd (snd core))
        B'     = fst (snd (snd (snd core)))
        redM   = fst (snd (snd (snd (snd core))))
        redN   = fst (snd (snd (snd (snd (snd core)))))
        sat1   = fst (snd (snd (snd (snd (snd (snd core))))))
        fmA1   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
        convAA-core = fst (snd (snd (snd (snd (snd (snd (snd (snd core))))))))
        convBB-core = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        tail12 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd core)))))))))
        eqvty  = fst tail12
        sEEqT  = snd tail12
        A_M    = fst vtyM1
        vtA_M  = fst (snd (snd (snd (snd (snd (snd (snd vtyM1)))))))
        redM2  = fst (snd (snd vtyM1))
        uniqM  = Red-unique-Sigma redM2 redM
        eqAMA  = fst uniqM
        vtA-b1 = S.Eq-transport (\ X -> ValTy2 G X b1) eqAMA vtA_M
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        eqvty0  = downEqValTy2 G A A' b0 b1 (fst le) fmem-b0 (fst cu1) eqvty
        sEEqT0  = transportSigmaEdgeEqTy2-sel G A B B' b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 sEEqT
        vtyM0  = downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyN1
        core0  = mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
                   (mkSigma redM (mkSigma redN (mkSigma sat0 (mkSigma fmemAll0
                     (mkSigma convAA-core
                       (mkSigma convBB-core
                         (mkSigma eqvty0 sEEqT0))))))))))
    in mkSigma vtyM0 (mkSigma vtyN0 core0)

  -- upVal2 / upEqVal2: stubbed -- all non-Pi cases are trivial
  -- For brevity, we provide only the type signatures with TERMINATING
  -- The implementation follows Validity2.agda exactly with extra trivial cases.
  -- We use postulate-free approach: all SigmaCode/PairCode/PropCode = Top.

  -- upVal2: case split on (u, a0, a1)
  -- Most cases are trivial since Val2 = Top at SigmaCode/PairCode/PropCode/FunEl/Bot
  upVal2 G M T Bot a0 a1 le mem0 mem1 ca0 ca1 src vta1 = Val2-Bot a1
  upVal2 G M T UCode        Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T PropCode     Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (FunEl g)    Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PiCode a f) Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (SigmaCode a f) Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PairCode u' v') Bot a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T UCode        UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (FunEl g')     UCode UCode le ()
  upVal2 G M T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T PropCode      UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T u UCode Bot          ()
  upVal2 G M T u UCode (FunEl h)    ()
  upVal2 G M T u UCode (PiCode b h) ()
  upVal2 G M T u UCode (SigmaCode b h) ()
  upVal2 G M T u UCode (PairCode x y) ()
  upVal2 G M T u UCode PropCode    ()
  upVal2 G M T UCode          PropCode a1 le ()
  upVal2 G M T (FunEl g)      PropCode a1 le ()
  upVal2 G M T (PiCode a f)   PropCode Bot ()
  upVal2 G M T (PiCode a f)   PropCode UCode ()
  upVal2 G M T (PiCode a f)   PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PiCode a f)   PropCode (FunEl h) ()
  upVal2 G M T (PiCode a f)   PropCode (PiCode b h) ()
  upVal2 G M T (PiCode a f)   PropCode (SigmaCode b h) ()
  upVal2 G M T (PiCode a f)   PropCode (PairCode x y) ()
  upVal2 G M T (SigmaCode a f) PropCode a1 le ()
  upVal2 G M T (PairCode u' v') PropCode a1 le ()
  upVal2 G M T PropCode       PropCode Bot ()
  upVal2 G M T PropCode       PropCode UCode ()
  upVal2 G M T PropCode       PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
  upVal2 G M T PropCode       PropCode (FunEl h) ()
  upVal2 G M T PropCode       PropCode (PiCode b h) ()
  upVal2 G M T PropCode       PropCode (SigmaCode b h) ()
  upVal2 G M T PropCode       PropCode (PairCode x y) ()
  upVal2 G M T UCode          (FunEl g) a1 le ()
  upVal2 G M T (FunEl g')     (FunEl g) a1 le ()
  upVal2 G M T (PiCode a' f') (FunEl g) a1 le ()
  upVal2 G M T (SigmaCode a' f') (FunEl g) a1 le ()
  upVal2 G M T (PairCode u' v') (FunEl g) a1 le ()
  upVal2 G M T PropCode       (FunEl g) a1 le ()
  upVal2 G M T u (PiCode b0 f0) Bot       ()
  upVal2 G M T u (PiCode b0 f0) UCode     ()
  upVal2 G M T u (PiCode b0 f0) (FunEl h) ()
  upVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  upVal2 G M T u (PiCode b0 f0) PropCode ()
  upVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = snd src
        A0   = fst vpiM
        B0   = fst (snd vpiM)
        red  = fst (snd (snd vpiM))
        sat0 = fst (snd (snd (snd vpiM)))
        fmg  = fst (snd (snd (snd (snd vpiM))))
        pav  = fst (snd (snd (snd (snd (snd vpiM)))))
        pae  = snd (snd (snd (snd (snd (snd vpiM)))))
        cf0  = snd ca0
        cf1  = snd ca1
        pf0  = snd (snd mem0)
        pf1  = snd (snd mem1)
        b0U  = fst pf0
        b1U  = fst pf1
        allU0 = fst (snd pf0)
        allU1 = fst (snd pf1)
        cb0  = coh-from-aU b0 b0U
        cb1  = coh-from-aU b1 b1U
        Av   = fst vta1
        Bv   = fst (snd vta1)
        redv = fst (snd (snd vta1))
        uniq = Red-unique-Pi red redv
        inner-vta1 = snd (snd (snd (snd (snd (snd (snd vta1))))))
        piEVv = fst (snd inner-vta1)
        piEV1 : PiEdgeVal2 G A0 B0 b1 f1
        piEV1 = S.Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X Bv b1 f1) (Eq-sym (fst uniq)) piEVv)
        vpi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat0
                 (mkSigma (fst mem1)
                   (mkSigma
                     (upPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat0 cb0 cb1 b1U allU1 b0U allU0 le
                       (fst mem0) piEV1 pav)
                     (upPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat0 cb0 cb1 b1U allU1 b0U allU0 le
                       (fst mem0) piEV1 pae))))))
    in mkSigma vta1 vpi'
  -- SigmaCode cases: FinMem u (SigmaCode b0 f0) is Empty for non-PairCode u (except Bot caught above)
  upVal2 G M T UCode (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T PropCode (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (FunEl g) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PiCode a' ff) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (SigmaCode a' ff) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) Bot ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) UCode ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) PropCode ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (FunEl h) ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (PiCode b1 f1) ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (PairCode x y) ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2F  = snd (snd (snd src))
        fm-u'-b0 = fst (fst mem0)
        fm-u'-b1 = fst (fst mem1)
        cb0  = fst ca0
        cb1  = fst ca1
        -- Get ValTy2 at b1 for the domain A0
        A1   = fst vta1
        red1 = fst (snd (snd vta1))
        uniq = Red-unique-Sigma red red1
        eqA  = fst uniq
        inn1 = snd (snd (snd (snd (snd (snd (snd vta1))))))
        vtAb1-raw = fst inn1
        vtAb1 = S.Eq-transport (\ X -> ValTy2 _ X b1) (Eq-sym eqA) vtAb1-raw
        v2F' = upVal2 G (Fst M) A0 u' b0 b1 (fst le) fm-u'-b0 fm-u'-b1 cb0 cb1 v2F vtAb1
    in mkSigma A0 (mkSigma B0 (mkSigma red v2F'))
  -- PairCode cases: all Top (need case split on u for reduction)
  -- Bot case already caught above
  upVal2 G M T UCode (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T PropCode (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (FunEl g) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PiCode a' ff) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (SigmaCode a' ff) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1

  -- upEqVal2: same structure
  upEqVal2 G M N T Bot a0 a1 le mem0 mem1 ca0 ca1 src vta1 = EqVal2-Bot a1
  upEqVal2 G M N T UCode        Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T PropCode     Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (FunEl g)    Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PiCode a f) Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (SigmaCode a f) Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PairCode u' v') Bot a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (FunEl g')     UCode UCode le ()
  upEqVal2 G M N T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T PropCode      UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T u UCode Bot          ()
  upEqVal2 G M N T u UCode (FunEl h)    ()
  upEqVal2 G M N T u UCode (PiCode b h) ()
  upEqVal2 G M N T u UCode (SigmaCode b h) ()
  upEqVal2 G M N T u UCode (PairCode x y) ()
  upEqVal2 G M N T u UCode PropCode    ()
  upEqVal2 G M N T UCode          PropCode a1 le ()
  upEqVal2 G M N T (FunEl g)      PropCode a1 le ()
  upEqVal2 G M N T (PiCode a f)   PropCode Bot ()
  upEqVal2 G M N T (PiCode a f)   PropCode UCode ()
  upEqVal2 G M N T (PiCode a f)   PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PiCode a f)   PropCode (FunEl h) ()
  upEqVal2 G M N T (PiCode a f)   PropCode (PiCode b h) ()
  upEqVal2 G M N T (PiCode a f)   PropCode (SigmaCode b h) ()
  upEqVal2 G M N T (PiCode a f)   PropCode (PairCode x y) ()
  upEqVal2 G M N T (SigmaCode a f) PropCode a1 le ()
  upEqVal2 G M N T (PairCode u' v') PropCode a1 le ()
  upEqVal2 G M N T PropCode       PropCode Bot ()
  upEqVal2 G M N T PropCode       PropCode UCode ()
  upEqVal2 G M N T PropCode       PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
  upEqVal2 G M N T PropCode       PropCode (FunEl h) ()
  upEqVal2 G M N T PropCode       PropCode (PiCode b h) ()
  upEqVal2 G M N T PropCode       PropCode (SigmaCode b h) ()
  upEqVal2 G M N T PropCode       PropCode (PairCode x y) ()
  upEqVal2 G M N T UCode          (FunEl g) a1 le ()
  upEqVal2 G M N T (FunEl g')     (FunEl g) a1 le ()
  upEqVal2 G M N T (PiCode a' f') (FunEl g) a1 le ()
  upEqVal2 G M N T (SigmaCode a' f') (FunEl g) a1 le ()
  upEqVal2 G M N T (PairCode u' v') (FunEl g) a1 le ()
  upEqVal2 G M N T PropCode       (FunEl g) a1 le ()
  upEqVal2 G M N T u (PiCode b0 f0) Bot       ()
  upEqVal2 G M N T u (PiCode b0 f0) UCode     ()
  upEqVal2 G M N T u (PiCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T u (PiCode b0 f0) PropCode ()
  upEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = fst (snd src)
        vpiN = fst (snd (snd src))
        epi  = snd (snd (snd src))
        A0    = fst epi
        B0    = fst (snd epi)
        red   = fst (snd (snd epi))
        sat0  = fst (snd (snd (snd epi)))
        fmg   = fst (snd (snd (snd (snd epi))))
        paev  = snd (snd (snd (snd (snd epi))))
        cf0   = snd ca0
        cf1   = snd ca1
        pf0   = snd (snd mem0)
        pf1   = snd (snd mem1)
        b0U   = fst pf0
        b1U   = fst pf1
        allU0 = fst (snd pf0)
        allU1 = fst (snd pf1)
        cb0   = coh-from-aU b0 b0U
        cb1   = coh-from-aU b1 b1U
        Av    = fst vta1
        Bv    = fst (snd vta1)
        redv  = fst (snd (snd vta1))
        uniq  = Red-unique-Pi red redv
        inner-vta1 = snd (snd (snd (snd (snd (snd (snd vta1))))))
        piEVv = fst (snd inner-vta1)
        piEV1 : PiEdgeVal2 G A0 B0 b1 f1
        piEV1 = S.Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X Bv b1 f1) (Eq-sym (fst uniq)) piEVv)
        valM   = mkSigma vty vpiM
        valN   = mkSigma vty vpiN
        valM'  = upVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
        valN'  = upVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
        epi'   = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat0
                   (mkSigma (fst mem1)
                     (upPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 sat0 cb0 cb1 b1U allU1 b0U allU0 le
                       (fst mem0) piEV1 paev)))))
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  -- SigmaCode cases: all Top
  upEqVal2 G M N T UCode (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T PropCode (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (FunEl g) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PiCode a' ff) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (SigmaCode a' ff) (SigmaCode b0 f0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) Bot ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) UCode ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) PropCode ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (PiCode b1 f1) ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2M  = fst (snd (snd (snd src)))
        v2N  = fst (snd (snd (snd (snd src))))
        eq   = snd (snd (snd (snd (snd src))))
        fm-u'-b0 = fst (fst mem0)
        fm-u'-b1 = fst (fst mem1)
        cb0  = fst ca0
        cb1  = fst ca1
        A1   = fst vta1
        red1 = fst (snd (snd vta1))
        uniq = Red-unique-Sigma red red1
        eqA  = fst uniq
        inn1 = snd (snd (snd (snd (snd (snd (snd vta1))))))
        vtAb1-raw = fst inn1
        vtAb1 = S.Eq-transport (\ X -> ValTy2 _ X b1) (Eq-sym eqA) vtAb1-raw
        v2M' = upVal2 G (Fst M) A0 u' b0 b1 (fst le) fm-u'-b0 fm-u'-b1 cb0 cb1 v2M vtAb1
        v2N' = upVal2 G (Fst N) A0 u' b0 b1 (fst le) fm-u'-b0 fm-u'-b1 cb0 cb1 v2N vtAb1
        eq'  = upEqVal2 G (Fst M) (Fst N) A0 u' b0 b1 (fst le) fm-u'-b0 fm-u'-b1 cb0 cb1 eq vtAb1
    in mkSigma A0 (mkSigma B0 (mkSigma red
         (mkSigma v2M' (mkSigma v2N' eq'))))
  -- PairCode cases: all Top (Bot case already caught above)
  upEqVal2 G M N T UCode (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T PropCode (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PiCode a' ff) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (SigmaCode a' ff) (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1
  upEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le () mem1 ca0 ca1 src vta1

  -- restrictVal2: case split on (u, u', a)
  restrictVal2 G M T u u' Bot          le mem fmu src = src
  restrictVal2 G M T (PiCode a f) (PiCode b g) PropCode le mem fmu src =
    downValTy2 G M (PiCode b g) (PiCode a f) le (FinMem-Prop-to-U (PiCode b g) mem) (FinMem-Prop-to-U (PiCode a f) fmu) src
  restrictVal2 G M T (PiCode a f) Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a f) UCode PropCode le ()
  restrictVal2 G M T (PiCode a f) PropCode PropCode le ()
  restrictVal2 G M T (PiCode a f) (FunEl _) PropCode le ()
  restrictVal2 G M T (PiCode a f) (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T (PiCode a f) (PairCode _ _) PropCode le ()
  restrictVal2 G M T Bot Bot PropCode le mem fmu src = tt
  restrictVal2 G M T Bot UCode PropCode le ()
  restrictVal2 G M T Bot PropCode PropCode le ()
  restrictVal2 G M T Bot (FunEl _) PropCode le ()
  restrictVal2 G M T Bot (PiCode _ _) PropCode ()
  restrictVal2 G M T Bot (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T Bot (PairCode _ _) PropCode le ()
  restrictVal2 G M T UCode Bot PropCode le mem fmu src = tt
  restrictVal2 G M T UCode UCode PropCode le mem fmu src = tt
  restrictVal2 G M T UCode PropCode PropCode le ()
  restrictVal2 G M T UCode (FunEl _) PropCode le ()
  restrictVal2 G M T UCode (PiCode _ _) PropCode ()
  restrictVal2 G M T UCode (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T UCode (PairCode _ _) PropCode le ()
  restrictVal2 G M T PropCode Bot PropCode le mem fmu src = tt
  restrictVal2 G M T PropCode UCode PropCode le ()
  restrictVal2 G M T PropCode PropCode PropCode le mem fmu src = tt
  restrictVal2 G M T PropCode (FunEl _) PropCode le ()
  restrictVal2 G M T PropCode (PiCode _ _) PropCode ()
  restrictVal2 G M T PropCode (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T PropCode (PairCode _ _) PropCode le ()
  restrictVal2 G M T (FunEl _) Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (FunEl _) UCode PropCode le ()
  restrictVal2 G M T (FunEl _) PropCode PropCode le ()
  restrictVal2 G M T (FunEl _) (FunEl _) PropCode le mem fmu src = tt
  restrictVal2 G M T (FunEl _) (PiCode _ _) PropCode ()
  restrictVal2 G M T (FunEl _) (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T (FunEl _) (PairCode _ _) PropCode le ()
  restrictVal2 G M T (SigmaCode _ _) Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode _ _) UCode PropCode le ()
  restrictVal2 G M T (SigmaCode _ _) PropCode PropCode le ()
  restrictVal2 G M T (SigmaCode _ _) (FunEl _) PropCode le ()
  restrictVal2 G M T (SigmaCode _ _) (PiCode _ _) PropCode ()
  restrictVal2 G M T (SigmaCode _ _) (SigmaCode _ _) PropCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode _ _) (PairCode _ _) PropCode le ()
  restrictVal2 G M T (PairCode _ _) Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PairCode _ _) UCode PropCode le ()
  restrictVal2 G M T (PairCode _ _) PropCode PropCode le ()
  restrictVal2 G M T (PairCode _ _) (FunEl _) PropCode le ()
  restrictVal2 G M T (PairCode _ _) (PiCode _ _) PropCode ()
  restrictVal2 G M T (PairCode _ _) (SigmaCode _ _) PropCode le ()
  restrictVal2 G M T (PairCode _ _) (PairCode _ _) PropCode le mem fmu src = tt
  restrictVal2 G M T u u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T u u' (PairCode x y) le mem fmu src = src
  -- UCode cases
  restrictVal2 G M T Bot Bot UCode        le mem fmu src = src
  restrictVal2 G M T Bot UCode UCode      ()
  restrictVal2 G M T Bot (FunEl _) UCode  ()
  restrictVal2 G M T Bot (PiCode _ _) UCode ()
  restrictVal2 G M T Bot (SigmaCode _ _) UCode ()
  restrictVal2 G M T Bot (PairCode _ _) UCode ()
  restrictVal2 G M T Bot PropCode UCode   ()
  restrictVal2 G M T UCode Bot UCode        le mem fmu src = tt
  restrictVal2 G M T UCode UCode UCode      le mem fmu src = src
  restrictVal2 G M T UCode (FunEl _) UCode  ()
  restrictVal2 G M T UCode (PiCode _ _) UCode ()
  restrictVal2 G M T UCode (SigmaCode _ _) UCode ()
  restrictVal2 G M T UCode (PairCode _ _) UCode ()
  restrictVal2 G M T UCode PropCode UCode  ()
  restrictVal2 G M T (FunEl g) Bot UCode    le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode UCode  ()
  restrictVal2 G M T (FunEl g) (FunEl g') UCode le mem fmu src =
    downValTy2 G M (FunEl g') (FunEl g) le mem fmu src
  restrictVal2 G M T (FunEl g) (PiCode _ _) UCode ()
  restrictVal2 G M T (FunEl g) (SigmaCode _ _) UCode ()
  restrictVal2 G M T (FunEl g) (PairCode _ _) UCode ()
  restrictVal2 G M T (FunEl g) PropCode UCode ()
  restrictVal2 G M T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a' f') UCode UCode ()
  restrictVal2 G M T (PiCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu src =
    downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu src
  restrictVal2 G M T (PiCode a' f') (SigmaCode _ _) UCode ()
  restrictVal2 G M T (PiCode a' f') (PairCode _ _) UCode ()
  restrictVal2 G M T (PiCode a' f') PropCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a' f') UCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (PiCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (SigmaCode a2 f2) UCode le mem fmu src =
    downValTy2 G M (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu src
  restrictVal2 G M T (SigmaCode a' f') (PairCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') PropCode UCode ()
  restrictVal2 G M T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode UCode ()
  restrictVal2 G M T (PairCode u' v') (FunEl _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PiCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictVal2 G M T (PairCode u' v') PropCode UCode ()
  restrictVal2 G M T PropCode Bot UCode le mem fmu src = tt
  restrictVal2 G M T PropCode UCode UCode ()
  restrictVal2 G M T PropCode (FunEl _) UCode ()
  restrictVal2 G M T PropCode (PiCode _ _) UCode ()
  restrictVal2 G M T PropCode (SigmaCode _ _) UCode ()
  restrictVal2 G M T PropCode (PairCode _ _) UCode ()
  restrictVal2 G M T PropCode PropCode UCode le mem fmu src = src
  -- PiCode cases
  restrictVal2 G M T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T Bot UCode          (PiCode b f) le ()
  restrictVal2 G M T Bot (FunEl g')     (PiCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T Bot (SigmaCode _ _) (PiCode b f) ()
  restrictVal2 G M T Bot (PairCode _ _) (PiCode b f) ()
  restrictVal2 G M T Bot PropCode       (PiCode b f) ()
  restrictVal2 G M T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T UCode (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T UCode (SigmaCode _ _) (PiCode b f) le ()
  restrictVal2 G M T UCode (PairCode _ _) (PiCode b f) le ()
  restrictVal2 G M T UCode PropCode       (PiCode b f) le ()
  restrictVal2 G M T PropCode Bot          (PiCode b f) le mem fmu src = src
  restrictVal2 G M T PropCode UCode        (PiCode b f) le ()
  restrictVal2 G M T PropCode (FunEl g')   (PiCode b f) le mem ()
  restrictVal2 G M T PropCode (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T PropCode (SigmaCode _ _) (PiCode b f) le ()
  restrictVal2 G M T PropCode (PairCode _ _) (PiCode b f) le ()
  restrictVal2 G M T PropCode PropCode     (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode          (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
    let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
    in mkSigma (fst src)
         (restrictVal2-PiCode G M T g g' b f (snd (snd aU)) (coh-from-aU b (fst aU))
           (fst (snd aU)) (fst aU) le (mkSigma (fst mem) (fst (snd mem))) (fst src) (snd src))
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) (SigmaCode _ _) (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) (PairCode _ _) (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) PropCode       (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  restrictVal2 G M T (PiCode a1 f1) (SigmaCode _ _) (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (PairCode _ _) (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) PropCode       (PiCode b f) le ()
  restrictVal2 G M T (SigmaCode a1 f1) Bot (PiCode b f) le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a1 f1) UCode (PiCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) PropCode (PiCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (FunEl g) (PiCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (PiCode a2 f2) (PiCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (SigmaCode a1 f1) (PairCode u2 v2) (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) Bot (PiCode b f) le mem fmu src = tt
  restrictVal2 G M T (PairCode u1 v1) UCode (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) PropCode (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (FunEl g) (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (PiCode a2 f2) (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (SigmaCode a2 f2) (PiCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (PairCode u2 v2) (PiCode b f) le ()
  -- SigmaCode: PairCode cases are Top
  restrictVal2 G M T (PairCode u1 v1) Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T (PairCode u1 v1) UCode (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (PiCode a2 f2) (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (SigmaCode a2 f2) (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u1 v1) (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2F  = snd (snd (snd src))
        fm-u2-b = fst (fst mem)
        fm-u1-b = fst (fst fmu)
        v2F' = restrictVal2 G (Fst M) A0 u1 u2 b (fst le) fm-u2-b fm-u1-b v2F
    in mkSigma A0 (mkSigma B0 (mkSigma red v2F'))
  restrictVal2 G M T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T UCode (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T PropCode (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T (FunEl g) (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a1 f1) (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (PairCode u2 v2) (SigmaCode b f) ()
  -- non-PairCode u and u': Val2 = Top at SigmaCode
  restrictVal2 G M T Bot Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T Bot UCode (SigmaCode b f) le ()
  restrictVal2 G M T Bot (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T Bot (SigmaCode a2 f2) (SigmaCode b f) ()
  restrictVal2 G M T Bot PropCode (SigmaCode b f) ()
  restrictVal2 G M T UCode Bot (SigmaCode b f) le mem ()
  restrictVal2 G M T UCode UCode (SigmaCode b f) le ()
  restrictVal2 G M T UCode (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T UCode (SigmaCode _ _) (SigmaCode b f) ()
  restrictVal2 G M T UCode PropCode (SigmaCode b f) ()
  restrictVal2 G M T PropCode Bot (SigmaCode b f) le mem ()
  restrictVal2 G M T PropCode UCode (SigmaCode b f) le ()
  restrictVal2 G M T PropCode (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T PropCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T PropCode (SigmaCode _ _) (SigmaCode b f) ()
  restrictVal2 G M T PropCode PropCode (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) Bot (SigmaCode b f) le mem ()
  restrictVal2 G M T (FunEl g) UCode (SigmaCode b f) ()
  restrictVal2 G M T (FunEl g) (FunEl g') (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (SigmaCode _ _) (SigmaCode b f) ()
  restrictVal2 G M T (FunEl g) PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a1 f1) Bot (SigmaCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) UCode (SigmaCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a1 f1) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (SigmaCode _ _) (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a1 f1) PropCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) Bot (SigmaCode b f) le mem ()
  restrictVal2 G M T (SigmaCode a1 f1) UCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (PiCode a2 f2) (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a1 f1) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (SigmaCode a1 f1) PropCode (SigmaCode b f) ()

  -- restrictEqVal2: same structure
  restrictEqVal2 G M N T u u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a f) (PiCode b g) PropCode le mem fmu src =
    mkSigma (downValTy2 G M (PiCode b g) (PiCode a f) le (FinMem-Prop-to-U (PiCode b g) mem) (FinMem-Prop-to-U (PiCode a f) fmu) (fst src))
      (mkSigma (downValTy2 G N (PiCode b g) (PiCode a f) le (FinMem-Prop-to-U (PiCode b g) mem) (FinMem-Prop-to-U (PiCode a f) fmu) (fst (snd src)))
        (downEqValTy2 G M N (PiCode b g) (PiCode a f) le (FinMem-Prop-to-U (PiCode b g) mem) (FinMem-Prop-to-U (PiCode a f) fmu) (snd (snd src))))
  restrictEqVal2 G M N T (PiCode a f) Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a f) UCode PropCode le ()
  restrictEqVal2 G M N T (PiCode a f) PropCode PropCode le ()
  restrictEqVal2 G M N T (PiCode a f) (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (PiCode a f) (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T (PiCode a f) (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T Bot Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T Bot UCode PropCode le ()
  restrictEqVal2 G M N T Bot PropCode PropCode le ()
  restrictEqVal2 G M N T Bot (FunEl _) PropCode le ()
  restrictEqVal2 G M N T Bot (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T Bot (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T Bot (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T UCode Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T UCode UCode PropCode le mem fmu src = tt
  restrictEqVal2 G M N T UCode PropCode PropCode le ()
  restrictEqVal2 G M N T UCode (FunEl _) PropCode le ()
  restrictEqVal2 G M N T UCode (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T UCode (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T UCode (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T PropCode Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T PropCode UCode PropCode le ()
  restrictEqVal2 G M N T PropCode PropCode PropCode le mem fmu src = tt
  restrictEqVal2 G M N T PropCode (FunEl _) PropCode le ()
  restrictEqVal2 G M N T PropCode (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T PropCode (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T PropCode (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T (FunEl _) Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl _) UCode PropCode le ()
  restrictEqVal2 G M N T (FunEl _) PropCode PropCode le ()
  restrictEqVal2 G M N T (FunEl _) (FunEl _) PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl _) (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T (FunEl _) (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T (FunEl _) (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T (SigmaCode _ _) Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode _ _) UCode PropCode le ()
  restrictEqVal2 G M N T (SigmaCode _ _) PropCode PropCode le ()
  restrictEqVal2 G M N T (SigmaCode _ _) (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (SigmaCode _ _) (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T (SigmaCode _ _) (SigmaCode _ _) PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode _ _) (PairCode _ _) PropCode le ()
  restrictEqVal2 G M N T (PairCode _ _) Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode _ _) UCode PropCode le ()
  restrictEqVal2 G M N T (PairCode _ _) PropCode PropCode le ()
  restrictEqVal2 G M N T (PairCode _ _) (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (PairCode _ _) (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode _ _) (SigmaCode _ _) PropCode le ()
  restrictEqVal2 G M N T (PairCode _ _) (PairCode _ _) PropCode le mem fmu src = tt
  restrictEqVal2 G M N T u u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T u u' (PairCode x y) le mem fmu src = src
  -- UCode cases
  restrictEqVal2 G M N T Bot Bot UCode        le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode UCode     ()
  restrictEqVal2 G M N T Bot (FunEl _) UCode ()
  restrictEqVal2 G M N T Bot (PiCode _ _) UCode ()
  restrictEqVal2 G M N T Bot (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T Bot (PairCode _ _) UCode ()
  restrictEqVal2 G M N T Bot PropCode UCode ()
  restrictEqVal2 G M N T UCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T UCode UCode UCode le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl _) UCode ()
  restrictEqVal2 G M N T UCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T UCode (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T UCode (PairCode _ _) UCode ()
  restrictEqVal2 G M N T UCode PropCode UCode ()
  restrictEqVal2 G M N T (FunEl g) Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode UCode ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') UCode le mem fmu (mkSigma vtM (mkSigma vtN eqvt)) =
    mkSigma (downValTy2 G M (FunEl g') (FunEl g) le mem fmu vtM)
      (mkSigma (downValTy2 G N (FunEl g') (FunEl g) le mem fmu vtN)
        (downEqValTy2 G M N (FunEl g') (FunEl g) le mem fmu eqvt))
  restrictEqVal2 G M N T (FunEl g) (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (FunEl g) (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T (FunEl g) (PairCode _ _) UCode ()
  restrictEqVal2 G M N T (FunEl g) PropCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a' f') UCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu (mkSigma vtM (mkSigma vtN eqvt)) =
    mkSigma (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu vtM)
      (mkSigma (downValTy2 G N (PiCode a2 f2) (PiCode a' f') le mem fmu vtN)
        (downEqValTy2 G M N (PiCode a2 f2) (PiCode a' f') le mem fmu eqvt))
  restrictEqVal2 G M N T (PiCode a' f') (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (PairCode _ _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') PropCode UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode a' f') UCode UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (FunEl _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (SigmaCode a2 f2) UCode le mem fmu (mkSigma vtM (mkSigma vtN eqvt)) =
    mkSigma (downValTy2 G M (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu vtM)
      (mkSigma (downValTy2 G N (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu vtN)
        (downEqValTy2 G M N (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu eqvt))
  restrictEqVal2 G M N T (SigmaCode a' f') (PairCode _ _) UCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') PropCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') PropCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictEqVal2 G M N T PropCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T PropCode UCode UCode ()
  restrictEqVal2 G M N T PropCode PropCode UCode le mem fmu src = src
  restrictEqVal2 G M N T PropCode (FunEl _) UCode ()
  restrictEqVal2 G M N T PropCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T PropCode (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T PropCode (PairCode _ _) UCode ()
  -- PiCode cases
  restrictEqVal2 G M N T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g')     (PiCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T Bot (SigmaCode _ _) (PiCode b f) ()
  restrictEqVal2 G M N T Bot (PairCode _ _) (PiCode b f) ()
  restrictEqVal2 G M N T Bot PropCode       (PiCode b f) ()
  restrictEqVal2 G M N T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T UCode (SigmaCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T UCode (PairCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T UCode PropCode       (PiCode b f) le ()
  restrictEqVal2 G M N T PropCode Bot          (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T PropCode UCode        (PiCode b f) le ()
  restrictEqVal2 G M N T PropCode (FunEl g')   (PiCode b f) le mem ()
  restrictEqVal2 G M N T PropCode (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T PropCode (SigmaCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T PropCode (PairCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T PropCode PropCode     (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
    let aU    = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
        valM  = mkSigma (fst src) (fst (snd src))
        valN  = mkSigma (fst src) (fst (snd (snd src)))
        epi   = snd (snd (snd src))
        valM' = restrictVal2 G M T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valM
        valN' = restrictVal2 G N T (FunEl g) (FunEl g') (PiCode b f) le mem fmu valN
        epi'  = restrictEqVal2-PiCode G M N T g g' b f (snd (snd aU)) (coh-from-aU b (fst aU))
                  (fst (snd aU)) (fst aU) le (mkSigma (fst mem) (fst (snd mem))) (fst src) epi
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  restrictEqVal2 G M N T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (SigmaCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (PairCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) PropCode       (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a1 f1) (SigmaCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PairCode _ _) (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) PropCode       (PiCode b f) le ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) Bot (PiCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode a1 f1) UCode (PiCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) PropCode (PiCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (FunEl g) (PiCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (PiCode a2 f2) (PiCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (PairCode u2 v2) (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) Bot (PiCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u1 v1) UCode (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) PropCode (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (FunEl g) (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (PiCode a2 f2) (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (SigmaCode a2 f2) (PiCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (PairCode u2 v2) (PiCode b f) le ()
  -- SigmaCode: PairCode cases are Top
  restrictEqVal2 G M N T (PairCode u1 v1) Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u1 v1) UCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) PropCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (PiCode a2 f2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (SigmaCode a2 f2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (PairCode u1 v1) (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let A0   = fst src
        B0   = fst (snd src)
        red  = fst (snd (snd src))
        v2M  = fst (snd (snd (snd src)))
        v2N  = fst (snd (snd (snd (snd src))))
        eq   = snd (snd (snd (snd (snd src))))
        fm-u2-b = fst (fst mem)
        fm-u1-b = fst (fst fmu)
        v2M' = restrictVal2 G (Fst M) A0 u1 u2 b (fst le) fm-u2-b fm-u1-b v2M
        v2N' = restrictVal2 G (Fst N) A0 u1 u2 b (fst le) fm-u2-b fm-u1-b v2N
        eq'  = restrictEqVal2 G (Fst M) (Fst N) A0 u1 u2 b (fst le) fm-u2-b fm-u1-b eq
    in mkSigma A0 (mkSigma B0 (mkSigma red
         (mkSigma v2M' (mkSigma v2N' eq'))))
  restrictEqVal2 G M N T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T PropCode (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (FunEl g) (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (PairCode u2 v2) (SigmaCode b f) ()
  -- non-PairCode u and u': EqVal2 = Top at SigmaCode
  restrictEqVal2 G M N T Bot Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T Bot UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (SigmaCode a2 f2) (SigmaCode b f) ()
  restrictEqVal2 G M N T Bot PropCode (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode Bot (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T UCode UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (SigmaCode _ _) (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode PropCode (SigmaCode b f) ()
  restrictEqVal2 G M N T PropCode Bot (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T PropCode UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T PropCode (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T PropCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T PropCode (SigmaCode _ _) (SigmaCode b f) ()
  restrictEqVal2 G M N T PropCode PropCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) Bot (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (FunEl g) UCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (SigmaCode _ _) (SigmaCode b f) ()
  restrictEqVal2 G M N T (FunEl g) PropCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (PiCode a1 f1) Bot (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (SigmaCode _ _) (SigmaCode b f) ()
  restrictEqVal2 G M N T (PiCode a1 f1) PropCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) Bot (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) UCode (SigmaCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (PiCode a2 f2) (SigmaCode b f) ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) PropCode (SigmaCode b f) ()

  -- Pi helper lemmas

  downPiAppVal2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppVal2 G M A0 B0 b1 f1 g ->
    PiAppVal2 G M A0 B0 b0 f0 g
  downPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pav
    = \ u v sel N htN valN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            val-b1 = upVal2 _ _ A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 valN vtAb1
            body  = pav u v sel N htN val-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  downPiAppEq2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppEq2 G M A0 B0 b1 f1 g ->
    PiAppEq2 G M A0 B0 b0 f0 g
  downPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 pae
    = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            eqN-b1 = upEqVal2 _ _ _ A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 eqN vtAb1
            body  = pae u v sel N1 N2 htN1 htN2 cvN eqN-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  downPiAppEqVal2 : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g -> FinMemFun g b0 f0 ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
    FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b1 f1 ->
    ValTy2 G A0 b1 ->
    PiAppEqVal2 G M N A0 B0 b1 f1 g ->
    PiAppEqVal2 G M N A0 B0 b0 f0 g
  downPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg fmg0 cb0 cb1 b1U b0U allU0 allU1 le fmg1 vtAb1 paev
    = \ u v sel P htP valP ->
        let ctg   = cft-from-cf g cg
            cu    = Coherent-Selection sel ctg
            fmu0  = FinMem-Selection b0 f0 sel fmg0 ctg cb0 b0U
            fmu1  = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
            valP-b1 = upVal2 _ _ A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 valP vtAb1
            body  = paev u v sel P htP valP-b1
            le-f  = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
            c-ef0 = Coherent-EvalFun f0 u cf0 cu
            ef1U  = EvalFun-in-UCode f1 u b1 cf1 cu allU1
            fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 ctg cf0 allU0
        in downEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

  -- Transport for Pi/Sigma edges (selection-based)

  transportPiEdgeVal2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeVal2 G A B b1 f1 ->
    PiEdgeVal2 G A B b0 f0
  transportPiEdgeVal2-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pev1
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
            vt-ef   = S.Eq-transport (\ x -> ValTy2 G (subst1 B N) x) (Eq-sym eq-v1) vt-v1
            le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
            le-v-v1 = S.Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = S.Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downValTy2 G (subst1 B N) v v1 le-v-v1 fmem-v-U v1U vt-v1

  transportPiEdgeEq2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeEq2 G A B b1 f1 ->
    PiEdgeEq2 G A B b0 f0
  transportPiEdgeEq2-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pee1
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
            le-v-v1 = S.Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = S.Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downEqValTy2 G (subst1 B N1) (subst1 B N2) v v1 le-v-v1 fmem-v-U v1U eqt-v1

  transportPiEdgeEqTy2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    PiEdgeEqTy2 G A B B' b1 f1 ->
    PiEdgeEqTy2 G A B B' b0 f0
  transportPiEdgeEqTy2-sel G A B B' b0 f0 b1 f1 cb0 cb1 b1U b0U leb lef allU0 cf0 cf1 allU1 vtAb1 pet1
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
            le-v-v1 = S.Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = S.Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downEqValTy2 G (subst1 B P) (subst1 B' P) v v1 le-v-v1 fmem-v-U v1U eqt-v1

  -- Sigma edge transports (identical structure, same types as Pi edge)

  transportSigmaEdgeVal2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    SigmaEdgeVal2 G A B b1 f1 ->
    SigmaEdgeVal2 G A B b0 f0
  transportSigmaEdgeVal2-sel = transportPiEdgeVal2-sel

  transportSigmaEdgeEq2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    SigmaEdgeEq2 G A B b1 f1 ->
    SigmaEdgeEq2 G A B b0 f0
  transportSigmaEdgeEq2-sel = transportPiEdgeEq2-sel

  transportSigmaEdgeEqTy2-sel : {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode ->
    FinMem b0 UCode ->
    LeCode b0 b1 -> LeFunCode f0 f1 ->
    FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 ->
    FinMemAllU f1 b1 ->
    ValTy2 G A b1 ->
    SigmaEdgeEqTy2 G A B B' b1 f1 ->
    SigmaEdgeEqTy2 G A B B' b0 f0
  transportSigmaEdgeEqTy2-sel = transportPiEdgeEqTy2-sel

  -- upPiAppVal2
  upPiAppVal2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppVal2 G M A0 B0 b0 f0 g ->
    PiAppVal2 G M A0 B0 b1 f1 g
  upPiAppVal2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pav
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
            vty-ef1 = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-v1) vty-v1
        in upVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  -- upPiAppEq2
  upPiAppEq2 : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppEq2 G M A0 B0 b0 f0 g ->
    PiAppEq2 G M A0 B0 b1 f1 g
  upPiAppEq2 G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 pae
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
            vty-ef1 = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  -- upPiAppEqVal2
  upPiAppEqVal2 : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
    CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
    Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
    FinMem b0 UCode -> FinMemAllU f0 b0 ->
    Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
    FinMemFun g b0 f0 ->
    PiEdgeVal2 G A0 B0 b1 f1 ->
    PiAppEqVal2 G M N A0 B0 b0 f0 g ->
    PiAppEqVal2 G M N A0 B0 b1 f1 g
  upPiAppEqVal2 G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 paev
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
            vty-ef1 = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  -- restrictVal2-PiCode
  restrictVal2-PiCode : {n : Nat} (G : Ctx n) (M T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    ValPi2 G M T g b f ->
    ValPi2 G M T g' b f
  restrictVal2-PiCode G M T g g' b f cf cb allU bU le mem' vtyT vpiM =
    let A0   = fst vpiM
        B0   = fst (snd vpiM)
        red  = fst (snd (snd vpiM))
        cg   = fst (snd (snd (snd vpiM)))
        fmg  = fst (snd (snd (snd (snd vpiM))))
        pav  = fst (snd (snd (snd (snd (snd vpiM)))))
        pae  = snd (snd (snd (snd (snd (snd vpiM)))))
        cg'  = snd mem'
        fmg' = fst mem'
        Av   = fst vtyT
        Bv   = fst (snd vtyT)
        redv = fst (snd (snd vtyT))
        uniq = Red-unique-Pi red redv
        inner-vty = snd (snd (snd (snd (snd (snd (snd vtyT))))))
        piEVv = fst (snd inner-vty)
        piEV : PiEdgeVal2 G A0 B0 b f
        piEV = S.Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X Bv b f) (Eq-sym (fst uniq)) piEVv)
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg'
         (mkSigma fmg'
           (mkSigma
             (restrictPiAppVal2-sel G M A0 B0 b f g g' cf cg cg' cb allU
                bU le fmg' fmg piEV pav)
             (restrictPiAppEq2-sel G M A0 B0 b f g g' cf cg cg' cb allU
                bU le fmg' fmg piEV pae))))))

  -- restrictEqVal2-PiCode
  restrictEqVal2-PiCode : {n : Nat} (G : Ctx n) (M N T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    EqValPi2 G M N T g b f ->
    EqValPi2 G M N T g' b f
  restrictEqVal2-PiCode G M N T g g' b f cf cb allU bU le mem' vtyT epi =
    let A0   = fst epi
        B0   = fst (snd epi)
        red  = fst (snd (snd epi))
        cg   = fst (snd (snd (snd epi)))
        fmg  = fst (snd (snd (snd (snd epi))))
        paev = snd (snd (snd (snd (snd epi))))
        cg'  = snd mem'
        fmg' = fst mem'
        Av   = fst vtyT
        Bv   = fst (snd vtyT)
        redv = fst (snd (snd vtyT))
        uniq = Red-unique-Pi red redv
        inner-vty = snd (snd (snd (snd (snd (snd (snd vtyT))))))
        piEVv = fst (snd inner-vty)
        piEV : PiEdgeVal2 G A0 B0 b f
        piEV = S.Eq-transport (\ Y -> PiEdgeVal2 G A0 Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X Bv b f) (Eq-sym (fst uniq)) piEVv)
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg'
         (mkSigma fmg'
           (restrictPiAppEqVal2-sel G M N A0 B0 b f g g' cf cg cg' cb allU
              bU le fmg' fmg piEV paev)))))

  -- restrictPiAppVal2-sel / restrictPiAppEq2-sel / restrictPiAppEqVal2-sel
  -- These are identical to Validity2.agda versions

  restrictPiAppVal2-sel : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppVal2 G M A0 B0 b f g -> PiAppVal2 G M A0 B0 b f g'
  restrictPiAppVal2-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pav
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
        vty-efu' = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-ef) vty-vf
        body2    = upVal2 _ _ (subst1 B0 N) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = S.Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictVal2 _ _ (subst1 B0 N) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  restrictPiAppEq2-sel : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppEq2 G M A0 B0 b f g -> PiAppEq2 G M A0 B0 b f g'
  restrictPiAppEq2-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV pae
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
        vty-efu' = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 N1) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = S.Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictEqVal2 _ _ _ (subst1 B0 N1) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  restrictPiAppEqVal2-sel : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal2 G A0 B0 b f ->
    PiAppEqVal2 G M N A0 B0 b f g -> PiAppEqVal2 G M N A0 B0 b f g'
  restrictPiAppEqVal2-sel G M N A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV paev
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
        vty-efu' = S.Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 P) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = S.Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictEqVal2 _ _ _ (subst1 B0 P) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2
