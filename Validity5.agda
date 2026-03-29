{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- Validity5.agda
--
-- Core validity relation for Pi + Sigma + U.
-- Uses RValSigma/REqValSigma (uniform in w) instead of RValPair/REqValPair.
-- Includes all transport lemmas.
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity5 where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              codeFst ; codeSnd)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ; Fst ; Snd ; MkPair ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc)
open import TypingRulesSigma using (Ctx ; empty ; extend ;
  HasType ; ConvTm ;
  WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; conv-Sigma ; conv-Fst ; conv-Snd ;
  conv-App-fun ; conv-App-arg ;
  ty-conv ; ty-Pi ; ty-Sigma ; ty-Fst ; ty-Snd ; ty-App)
open import ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ; headred-refl ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma)
open import PaperSemanticsSigma using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; Comp ; Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem ; FinMem-coh-u ; coh-from-aU ;
  FinMem-a-in-U ; cft-from-cf ;
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
  CFTcons ; CoherentFunTail ; CoherentWith ;
  FinMem-Prop-to-U)
open import SelectionSigma using (Selection ;
  FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow ; Selection-le-EvalFun ; sel-nil ;
  Coherent-Selection ; Coherent-Selection-val)
open import ValiditySigma using (Red-unique-Pi ; Red-unique-Sigma ;
  bU-from-cf-fmFun ;
  FinMem-Coherent)
open import SubstitutionLemmaSigma using (typing-ConvTm ; ctx-conv-ConvTm ; ctx-conv-HasType ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Red3: HeadRed bundled with ConvTm (as in the paper)
------------------------------------------------------------------------

record Red3 {n : Nat} (G : Ctx n) (M N A : Expr n) : Set where
  constructor mkRed3
  field
    hr : HeadRed M N
    ct : ConvTm G M N A

Red3-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red3 G A (Pi B F) U -> Red3 G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red3-unique-Pi {G = G} {A} r1 r2 =
  Red-unique-Pi {G = G} {A} (mkRed (Red3.hr r1)) (mkRed (Red3.hr r2))

Red3-unique-Sigma : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red3 G A (RS.Sigma B F) U -> Red3 G A (RS.Sigma B' F') U ->
  Pair (Eq B B') (Eq F F')
Red3-unique-Sigma {G = G} {A} r1 r2 =
  Red-unique-Sigma {G = G} {A} (mkRed (Red3.hr r1)) (mkRed (Red3.hr r2))

------------------------------------------------------------------------
-- Bundled validity relations (mutual block with records)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Val2, EqVal2: top-level relations, defined by pattern matching on codes
  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

  -- ValTy2, EqValTy2: type validity / type equality
  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

  -- Sigma edge functions (identical type signatures to Pi edges)
  SigmaEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  SigmaEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  SigmaEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) -> FinEl -> FinFun -> Set

  -- Edge functions (unchanged — these are function types, not tuples)
  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
    ValTy2 G (subst1 B N) v

  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
    EqValTy2 G (subst1 B N1) (subst1 B N2) v

  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> Val2 G P A u b ->
    EqValTy2 G (subst1 B P) (subst1 B' P) v

  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppVal2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N : Expr n) -> HasType G N A0 -> Val2 G N A0 u b ->
    Val2 G (App M N) (subst1 B0 N) v (EvalFun f u)

  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEq2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
    ConvTm G N1 N2 A0 -> EqVal2 G N1 N2 A0 u b ->
    EqVal2 G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)

  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEqVal2 {n} G M N A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (P : Expr n) -> HasType G P A0 -> Val2 G P A0 u b ->
    EqVal2 G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)

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

  ------------------------------------------------------------------
  -- Records for Pi type structures
  ------------------------------------------------------------------

  -- ValTyPi2: type validity at PiCode b f
  {-# NO_POSITIVITY_CHECK #-}
  record RValTyPi {n : Nat} (G : Ctx n) (M : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      red    : Red3 G M (Pi domA codB) U
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f b
      htA    : HasType G domA U
      htB    : HasType (extend G domA) codB U
      valA   : ValTy2 G domA b
      edgeV  : PiEdgeVal2 G domA codB b f
      edgeE  : PiEdgeEq2 G domA codB b f

  -- EqValTyPi2: type equality at PiCode b f
  {-# NO_POSITIVITY_CHECK #-}
  record REqValTyPi {n : Nat} (G : Ctx n) (M N : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      domA'  : Expr n
      codB'  : Expr (suc n)
      redM   : Red3 G M (Pi domA codB) U
      redN   : Red3 G N (Pi domA' codB') U
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f b
      convA  : ConvTm G domA domA' U
      convB  : ConvTm (extend G domA) codB codB' U
      eqA    : EqValTy2 G domA domA' b
      edgeET : PiEdgeEqTy2 G domA codB codB' b f

  -- ValPi2: term validity at (FunEl g, PiCode b f)
  {-# NO_POSITIVITY_CHECK #-}
  record RValPi {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      codB0  : Expr (suc n)
      red    : Red3 G A (Pi domA0 codB0) U
      cohG   : CoherentFun g
      fmG    : FinMemFun g b f
      appV   : PiAppVal2 G M domA0 codB0 b f g
      appE   : PiAppEq2 G M domA0 codB0 b f g

  -- EqValPi2: equality at (FunEl g, PiCode b f)
  {-# NO_POSITIVITY_CHECK #-}
  record REqValPi {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      codB0  : Expr (suc n)
      red    : Red3 G A (Pi domA0 codB0) U
      cohG   : CoherentFun g
      fmG    : FinMemFun g b f
      appEV  : PiAppEqVal2 G M N domA0 codB0 b f g

  ------------------------------------------------------------------
  -- Records for Sigma type structures
  ------------------------------------------------------------------

  -- RValTySigma: type validity at SigmaCode b f
  {-# NO_POSITIVITY_CHECK #-}
  record RValTySigma {n : Nat} (G : Ctx n) (M : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      red    : Red3 G M (RS.Sigma domA codB) U
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f b
      fmBU   : FinMem b UCode
      htA    : HasType G domA U
      htB    : HasType (extend G domA) codB U
      valA   : ValTy2 G domA b
      edgeV  : SigmaEdgeVal2 G domA codB b f
      edgeE  : SigmaEdgeEq2 G domA codB b f

  -- REqValTySigma: type equality at SigmaCode b f
  {-# NO_POSITIVITY_CHECK #-}
  record REqValTySigma {n : Nat} (G : Ctx n) (M N : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      domA'  : Expr n
      codB'  : Expr (suc n)
      redM   : Red3 G M (RS.Sigma domA codB) U
      redN   : Red3 G N (RS.Sigma domA' codB') U
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f b
      convA  : ConvTm G domA domA' U
      convB  : ConvTm (extend G domA) codB codB' U
      eqA    : EqValTy2 G domA domA' b
      edgeET : SigmaEdgeEqTy2 G domA codB codB' b f

  -- RValSigma: term validity at (w, SigmaCode b f), uniform in w
  {-# NO_POSITIVITY_CHECK #-}
  record RValSigma {n : Nat} (G : Ctx n) (M A : Expr n) (w : FinEl) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      red    : Red3 G A (RS.Sigma domA codB) U
      htFst  : HasType G (Fst M) domA
      cohW1  : Coherent (codeFst w)
      fmW1   : FinMem (codeFst w) b
      valFst : Val2 G (Fst M) domA (codeFst w) b
      valSnd : Val2 G (Snd M) (subst1 codB (Fst M)) (codeSnd w) (EvalFun f (codeFst w))

  -- REqValSigma: equality at (w, SigmaCode b f), uniform in w
  {-# NO_POSITIVITY_CHECK #-}
  record REqValSigma {n : Nat} (G : Ctx n) (M N A : Expr n) (w : FinEl) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA    : Expr n
      codB    : Expr (suc n)
      red     : Red3 G A (RS.Sigma domA codB) U
      htFstM  : HasType G (Fst M) domA
      htFstN  : HasType G (Fst N) domA
      cohW1   : Coherent (codeFst w)
      fmW1    : FinMem (codeFst w) b
      valFstM : Val2 G (Fst M) domA (codeFst w) b
      valSndM : Val2 G (Snd M) (subst1 codB (Fst M)) (codeSnd w) (EvalFun f (codeFst w))
      valFstN : Val2 G (Fst N) domA (codeFst w) b
      valSndN : Val2 G (Snd N) (subst1 codB (Fst N)) (codeSnd w) (EvalFun f (codeFst w))
      eqFst   : EqVal2 G (Fst M) (Fst N) domA (codeFst w) b

  ------------------------------------------------------------------
  -- Val2: pattern matching on codes
  ------------------------------------------------------------------

  -- Val2: first clause catches Bot value code for all type codes,
  -- second clause catches Bot type code for remaining value codes
  Val2 G M A Bot a                 = Top
  Val2 G M A u Bot                 = Top
  Val2 G M A UCode UCode           = ValTy2 G M UCode
  Val2 G M A (PiCode a' f') UCode  = ValTy2 G M (PiCode a' f')
  Val2 G M A (SigmaCode a' f') UCode = ValTy2 G M (SigmaCode a' f')
  Val2 G M A u UCode               = Top
  Val2 G M A (PiCode a' f') PropCode = ValTy2 G M (PiCode a' f')
  Val2 G M A u PropCode            = Top
  Val2 G M A u (FunEl h)           = Top
  Val2 G M A (FunEl g) (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f)) (RValPi G M A g b f)
  Val2 G M A u (PiCode b f)        = Top
  Val2 G M A w (SigmaCode b f)     =
    Pair (ValTy2 G A (SigmaCode b f)) (RValSigma G M A w b f)
  Val2 G M A u (PairCode x y)      = Top

  ------------------------------------------------------------------
  -- EqVal2: pattern matching on codes
  ------------------------------------------------------------------

  -- EqVal2: first clause catches Bot value code for all type codes,
  -- second clause catches Bot type code for remaining value codes
  EqVal2 G M N A Bot a                 = Top
  EqVal2 G M N A u Bot                 = Top
  EqVal2 G M N A UCode UCode           =
    Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode))
  EqVal2 G M N A (PiCode a' f') UCode  =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2 G M N A (SigmaCode a' f') UCode =
    Pair (ValTy2 G M (SigmaCode a' f')) (Pair (ValTy2 G N (SigmaCode a' f')) (EqValTy2 G M N (SigmaCode a' f')))
  EqVal2 G M N A u UCode               = Top
  EqVal2 G M N A (PiCode a' f') PropCode =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2 G M N A u PropCode            = Top
  EqVal2 G M N A u (FunEl h)           = Top
  EqVal2 G M N A (FunEl g) (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f))
         (Pair (RValPi G M A g b f)
               (Pair (RValPi G N A g b f)
                     (REqValPi G M N A g b f)))
  EqVal2 G M N A u (PiCode b f)        = Top
  EqVal2 G M N A w (SigmaCode b f)     =
    Pair (ValTy2 G A (SigmaCode b f))
         (Pair (RValSigma G M A w b f)
               (Pair (RValSigma G N A w b f)
                     (REqValSigma G M N A w b f)))
  EqVal2 G M N A u (PairCode x y)      = Top

  ------------------------------------------------------------------
  -- ValTy2 / EqValTy2
  ------------------------------------------------------------------

  ValTy2 G M Bot          = Top
  ValTy2 G M UCode        = Red3 G M U U
  ValTy2 G M PropCode     = Top
  ValTy2 G M (FunEl g)    = Top
  ValTy2 G M (PiCode b f) = RValTyPi G M b f
  ValTy2 G M (SigmaCode b f) = RValTySigma G M b f
  ValTy2 G M (PairCode u v) = Top

  EqValTy2 G M N Bot          = Top
  EqValTy2 G M N UCode        = Pair (Red3 G M U U) (Red3 G N U U)
  EqValTy2 G M N PropCode     = Top
  EqValTy2 G M N (FunEl g)    = Top
  EqValTy2 G M N (PiCode b f) =
    Pair (RValTyPi G M b f)
         (Pair (RValTyPi G N b f)
               (REqValTyPi G M N b f))
  EqValTy2 G M N (SigmaCode b f) =
    Pair (RValTySigma G M b f)
         (Pair (RValTySigma G N b f)
               (REqValTySigma G M N b f))
  EqValTy2 G M N (PairCode u v) = Top

  ------------------------------------------------------------------
  -- Val2-Bot / EqVal2-Bot
  ------------------------------------------------------------------

  Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
    (a : FinEl) -> Val2 G M A Bot a
  Val2-Bot Bot              = tt
  Val2-Bot UCode            = tt
  Val2-Bot PropCode         = tt
  Val2-Bot (FunEl h)        = tt
  Val2-Bot (PiCode b f)     = tt
  Val2-Bot (SigmaCode b f)  = tt
  Val2-Bot (PairCode x y)   = tt

  EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    (a : FinEl) -> EqVal2 G M N A Bot a
  EqVal2-Bot Bot              = tt
  EqVal2-Bot UCode            = tt
  EqVal2-Bot PropCode         = tt
  EqVal2-Bot (FunEl h)        = tt
  EqVal2-Bot (PiCode b f)     = tt
  EqVal2-Bot (SigmaCode b f)  = tt
  EqVal2-Bot (PairCode x y)   = tt

  ------------------------------------------------------------------
  -- Val2-to-EqVal2: reflexivity
  ------------------------------------------------------------------

  Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n}
    (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
  Val2-to-EqVal2 Bot a v = tt
  Val2-to-EqVal2 UCode Bot v = tt
  Val2-to-EqVal2 PropCode Bot v = tt
  Val2-to-EqVal2 (FunEl g) Bot v = tt
  Val2-to-EqVal2 (PiCode a f) Bot v = tt
  Val2-to-EqVal2 (SigmaCode a f) Bot v = tt
  Val2-to-EqVal2 (PairCode x y) Bot v = tt
  Val2-to-EqVal2 UCode UCode v = mkSigma v (mkSigma v (mkSigma v v))
  Val2-to-EqVal2 (FunEl g) UCode v = tt
  Val2-to-EqVal2 (PiCode a f) UCode v = mkSigma v (mkSigma v (ValTy2-to-EqValTy2 (PiCode a f) v))
  Val2-to-EqVal2 (SigmaCode a f) UCode v = mkSigma v (mkSigma v (ValTy2-to-EqValTy2 (SigmaCode a f) v))
  Val2-to-EqVal2 (PairCode u' v') UCode v = tt
  Val2-to-EqVal2 PropCode UCode v = tt
  Val2-to-EqVal2 (PiCode a f) PropCode v = mkSigma v (mkSigma v (ValTy2-to-EqValTy2 (PiCode a f) v))
  Val2-to-EqVal2 UCode PropCode v = tt
  Val2-to-EqVal2 PropCode PropCode v = tt
  Val2-to-EqVal2 (FunEl g) PropCode v = tt
  Val2-to-EqVal2 (SigmaCode a' f') PropCode v = tt
  Val2-to-EqVal2 (PairCode u' v') PropCode v = tt
  Val2-to-EqVal2 UCode (FunEl h) v = tt
  Val2-to-EqVal2 PropCode (FunEl h) v = tt
  Val2-to-EqVal2 (FunEl g) (FunEl h) v = tt
  Val2-to-EqVal2 (PiCode a f) (FunEl h) v = tt
  Val2-to-EqVal2 (SigmaCode a f) (FunEl h) v = tt
  Val2-to-EqVal2 (PairCode x y) (FunEl h) v = tt
  Val2-to-EqVal2 UCode (PiCode b f) v = tt
  Val2-to-EqVal2 PropCode (PiCode b f) v = tt
  Val2-to-EqVal2 (PiCode a' f') (PiCode b f) v = tt
  Val2-to-EqVal2 (SigmaCode a' f') (PiCode b f) v = tt
  Val2-to-EqVal2 (PairCode u' v') (PiCode b f) v = tt
  Val2-to-EqVal2 (FunEl g) (PiCode b f) (mkSigma vty vpi) =
    mkSigma vty (mkSigma vpi (mkSigma vpi (ValPi2-to-EqValPi2 g b f vpi)))
  Val2-to-EqVal2 UCode (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 UCode b f vsigma)))
  Val2-to-EqVal2 PropCode (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 PropCode b f vsigma)))
  Val2-to-EqVal2 (FunEl g) (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 (FunEl g) b f vsigma)))
  Val2-to-EqVal2 (PiCode a' f') (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 (PiCode a' f') b f vsigma)))
  Val2-to-EqVal2 (SigmaCode a' f') (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 (SigmaCode a' f') b f vsigma)))
  Val2-to-EqVal2 (PairCode u' v') (SigmaCode b f) (mkSigma vty vsigma) =
    mkSigma vty (mkSigma vsigma (mkSigma vsigma (ValSigma2-to-EqValSigma2 (PairCode u' v') b f vsigma)))
  Val2-to-EqVal2 UCode (PairCode x y) v = tt
  Val2-to-EqVal2 PropCode (PairCode x y) v = tt
  Val2-to-EqVal2 (FunEl g) (PairCode x y) v = tt
  Val2-to-EqVal2 (PiCode a f) (PairCode x y) v = tt
  Val2-to-EqVal2 (SigmaCode a f) (PairCode x y) v = tt
  Val2-to-EqVal2 (PairCode u' v') (PairCode x y) v = tt

  ------------------------------------------------------------------
  -- ValTy2-to-EqValTy2: reflexivity for types
  ------------------------------------------------------------------

  ValSigma2-to-EqValSigma2 : {n : Nat} {G : Ctx n} {M A : Expr n}
    (w : FinEl) (b : FinEl) (f : FinFun) ->
    RValSigma G M A w b f -> REqValSigma G M M A w b f
  ValSigma2-to-EqValSigma2 w b f vsigma = record
    { domA    = RValSigma.domA vsigma
    ; codB    = RValSigma.codB vsigma
    ; red     = RValSigma.red vsigma
    ; htFstM  = RValSigma.htFst vsigma
    ; htFstN  = RValSigma.htFst vsigma
    ; cohW1   = RValSigma.cohW1 vsigma
    ; fmW1    = RValSigma.fmW1 vsigma
    ; valFstM = RValSigma.valFst vsigma
    ; valSndM = RValSigma.valSnd vsigma
    ; valFstN = RValSigma.valFst vsigma
    ; valSndN = RValSigma.valSnd vsigma
    ; eqFst   = Val2-to-EqVal2 (codeFst w) b (RValSigma.valFst vsigma)
    }

  ValTy2-to-EqValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
    (a : FinEl) -> ValTy2 G M a -> EqValTy2 G M M a
  ValTy2-to-EqValTy2 Bot v = tt
  ValTy2-to-EqValTy2 UCode v = mkSigma v v
  ValTy2-to-EqValTy2 PropCode v = tt
  ValTy2-to-EqValTy2 (FunEl g) v = tt
  ValTy2-to-EqValTy2 (PairCode u v) vt = tt
  ValTy2-to-EqValTy2 (PiCode b f) vtyM =
    let eqVtA = ValTy2-to-EqValTy2 b (RValTyPi.valA vtyM)
        A0 = RValTyPi.domA vtyM
        B0 = RValTyPi.codB vtyM
        edgeEqTy : PiEdgeEqTy2 _ A0 B0 B0 b f
        edgeEqTy = \ u' v' sel P htP valP ->
          ValTy2-to-EqValTy2 v' (RValTyPi.edgeV vtyM u' v' sel P htP valP)
        coreEq : REqValTyPi _ _ _ b f
        coreEq = record
          { domA   = RValTyPi.domA vtyM
          ; codB   = RValTyPi.codB vtyM
          ; domA'  = RValTyPi.domA vtyM
          ; codB'  = RValTyPi.codB vtyM
          ; redM   = RValTyPi.red vtyM
          ; redN   = RValTyPi.red vtyM
          ; cohF   = RValTyPi.cohF vtyM
          ; fmAllU = RValTyPi.fmAllU vtyM
          ; convA  = conv-refl (RValTyPi.htA vtyM)
          ; convB  = conv-refl (RValTyPi.htB vtyM)
          ; eqA    = eqVtA
          ; edgeET = edgeEqTy
          }
    in mkSigma vtyM (mkSigma vtyM coreEq)
  ValTy2-to-EqValTy2 (SigmaCode b f) vtyM =
    let eqVtA = ValTy2-to-EqValTy2 b (RValTySigma.valA vtyM)
        A0 = RValTySigma.domA vtyM
        B0 = RValTySigma.codB vtyM
        edgeEqTy : SigmaEdgeEqTy2 _ A0 B0 B0 b f
        edgeEqTy = \ u' v' sel P htP valP ->
          ValTy2-to-EqValTy2 v' (RValTySigma.edgeV vtyM u' v' sel P htP valP)
        coreEq : REqValTySigma _ _ _ b f
        coreEq = record
          { domA   = RValTySigma.domA vtyM
          ; codB   = RValTySigma.codB vtyM
          ; domA'  = RValTySigma.domA vtyM
          ; codB'  = RValTySigma.codB vtyM
          ; redM   = RValTySigma.red vtyM
          ; redN   = RValTySigma.red vtyM
          ; cohF   = RValTySigma.cohF vtyM
          ; fmAllU = RValTySigma.fmAllU vtyM
          ; convA  = conv-refl (RValTySigma.htA vtyM)
          ; convB  = conv-refl (RValTySigma.htB vtyM)
          ; eqA    = eqVtA
          ; edgeET = edgeEqTy
          }
    in mkSigma vtyM (mkSigma vtyM coreEq)

  ------------------------------------------------------------------
  -- ValPi2-to-EqValPi2: reflexivity for term validity at FunEl
  ------------------------------------------------------------------

  ValPi2-to-EqValPi2 : {n : Nat} {G : Ctx n} {M A : Expr n}
    (g : FinFun) (b : FinEl) (f : FinFun) ->
    RValPi G M A g b f -> REqValPi G M M A g b f
  ValPi2-to-EqValPi2 g b f vpi = record
    { domA0 = RValPi.domA0 vpi
    ; codB0 = RValPi.codB0 vpi
    ; red   = RValPi.red vpi
    ; cohG  = RValPi.cohG vpi
    ; fmG   = RValPi.fmG vpi
    ; appEV = \ u v sel P htP valP ->
        Val2-to-EqVal2 v (EvalFun f u) (RValPi.appV vpi u v sel P htP valP)
    }

  ------------------------------------------------------------------
  -- Val2-from-EqVal2-first / second
  ------------------------------------------------------------------

  Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
  Val2-from-EqVal2-first Bot a ev = tt
  Val2-from-EqVal2-first UCode Bot ev = tt
  Val2-from-EqVal2-first PropCode Bot ev = tt
  Val2-from-EqVal2-first (FunEl g) Bot ev = tt
  Val2-from-EqVal2-first (PiCode a f) Bot ev = tt
  Val2-from-EqVal2-first (SigmaCode a f) Bot ev = tt
  Val2-from-EqVal2-first (PairCode x y) Bot ev = tt
  Val2-from-EqVal2-first UCode UCode ev = fst ev
  Val2-from-EqVal2-first (FunEl g) UCode ev = tt
  Val2-from-EqVal2-first (PiCode a f) UCode ev = fst ev
  Val2-from-EqVal2-first (SigmaCode a f) UCode ev = fst ev
  Val2-from-EqVal2-first (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-first PropCode UCode ev = tt
  Val2-from-EqVal2-first (PiCode a f) PropCode ev = fst ev
  Val2-from-EqVal2-first UCode PropCode ev = tt
  Val2-from-EqVal2-first PropCode PropCode ev = tt
  Val2-from-EqVal2-first (FunEl g) PropCode ev = tt
  Val2-from-EqVal2-first (SigmaCode a' f') PropCode ev = tt
  Val2-from-EqVal2-first (PairCode u' v') PropCode ev = tt
  Val2-from-EqVal2-first UCode (FunEl h) ev = tt
  Val2-from-EqVal2-first PropCode (FunEl h) ev = tt
  Val2-from-EqVal2-first (FunEl g) (FunEl h) ev = tt
  Val2-from-EqVal2-first (PiCode a f) (FunEl h) ev = tt
  Val2-from-EqVal2-first (SigmaCode a f) (FunEl h) ev = tt
  Val2-from-EqVal2-first (PairCode x y) (FunEl h) ev = tt
  Val2-from-EqVal2-first UCode (PiCode b f) ev = tt
  Val2-from-EqVal2-first PropCode (PiCode b f) ev = tt
  Val2-from-EqVal2-first (PiCode a' f') (PiCode b f) ev = tt
  Val2-from-EqVal2-first (SigmaCode a' f') (PiCode b f) ev = tt
  Val2-from-EqVal2-first (PairCode u' v') (PiCode b f) ev = tt
  Val2-from-EqVal2-first (FunEl g) (PiCode b f) ev =
    mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first UCode (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first PropCode (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (FunEl g) (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (PiCode a' f') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (SigmaCode a' f') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first UCode (PairCode x y) ev = tt
  Val2-from-EqVal2-first PropCode (PairCode x y) ev = tt
  Val2-from-EqVal2-first (FunEl g) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (PiCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (SigmaCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (PairCode u' v') (PairCode x y) ev = tt

  Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
  Val2-from-EqVal2-second Bot a ev = tt
  Val2-from-EqVal2-second UCode Bot ev = tt
  Val2-from-EqVal2-second PropCode Bot ev = tt
  Val2-from-EqVal2-second (FunEl g) Bot ev = tt
  Val2-from-EqVal2-second (PiCode a f) Bot ev = tt
  Val2-from-EqVal2-second (SigmaCode a f) Bot ev = tt
  Val2-from-EqVal2-second (PairCode x y) Bot ev = tt
  Val2-from-EqVal2-second UCode UCode ev = fst (snd ev)
  Val2-from-EqVal2-second (FunEl g) UCode ev = tt
  Val2-from-EqVal2-second (PiCode a f) UCode ev = fst (snd ev)
  Val2-from-EqVal2-second (SigmaCode a f) UCode ev = fst (snd ev)
  Val2-from-EqVal2-second (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-second PropCode UCode ev = tt
  Val2-from-EqVal2-second (PiCode a f) PropCode ev = fst (snd ev)
  Val2-from-EqVal2-second UCode PropCode ev = tt
  Val2-from-EqVal2-second PropCode PropCode ev = tt
  Val2-from-EqVal2-second (FunEl g) PropCode ev = tt
  Val2-from-EqVal2-second (SigmaCode a' f') PropCode ev = tt
  Val2-from-EqVal2-second (PairCode u' v') PropCode ev = tt
  Val2-from-EqVal2-second UCode (FunEl h) ev = tt
  Val2-from-EqVal2-second PropCode (FunEl h) ev = tt
  Val2-from-EqVal2-second (FunEl g) (FunEl h) ev = tt
  Val2-from-EqVal2-second (PiCode a f) (FunEl h) ev = tt
  Val2-from-EqVal2-second (SigmaCode a f) (FunEl h) ev = tt
  Val2-from-EqVal2-second (PairCode x y) (FunEl h) ev = tt
  Val2-from-EqVal2-second UCode (PiCode b f) ev = tt
  Val2-from-EqVal2-second PropCode (PiCode b f) ev = tt
  Val2-from-EqVal2-second (PiCode a' f') (PiCode b f) ev = tt
  Val2-from-EqVal2-second (SigmaCode a' f') (PiCode b f) ev = tt
  Val2-from-EqVal2-second (PairCode u' v') (PiCode b f) ev = tt
  Val2-from-EqVal2-second (FunEl g) (PiCode b f) ev =
    mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second UCode (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second PropCode (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (FunEl g) (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (PiCode a' f') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (SigmaCode a' f') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b f) ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second UCode (PairCode x y) ev = tt
  Val2-from-EqVal2-second PropCode (PairCode x y) ev = tt
  Val2-from-EqVal2-second (FunEl g) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (PiCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (SigmaCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (PairCode u' v') (PairCode x y) ev = tt
  Val2-EqValTy2-fwd-Sigma : {n : Nat} {G : Ctx n} {C C' M : Expr n}
    (w : FinEl) (b0 : FinEl) (f0 : FinFun) -> Coherent (SigmaCode b0 f0) ->
    EqValTy2 G C C' (SigmaCode b0 f0) ->
    Val2 G M C w (SigmaCode b0 f0) -> Val2 G M C' w (SigmaCode b0 f0)

  EqVal2-EqValTy2-fwd-Sigma : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (w : FinEl) (b0 : FinEl) (f0 : FinFun) -> Coherent (SigmaCode b0 f0) ->
    EqValTy2 G C C' (SigmaCode b0 f0) ->
    EqVal2 G M N C w (SigmaCode b0 f0) -> EqVal2 G M N C' w (SigmaCode b0 f0)

  Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    Val2 G M C u b -> Val2 G M C' u b

  EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b ->
    EqVal2 G M N C u b -> EqVal2 G M N C' u b

  restrictVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    Val2 G M T u a -> Val2 G M T u' a

  EqValTy2-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
    (a : FinEl) -> Coherent a -> EqValTy2 G M N a -> EqValTy2 G N M a

  EqValTy2-sym Bot ca ev = tt
  EqValTy2-sym UCode ca ev = mkSigma (snd ev) (fst ev)
  EqValTy2-sym PropCode ca ev = tt
  EqValTy2-sym (FunEl g) ca ev = tt
  EqValTy2-sym (PairCode u v) ca ev = tt
  EqValTy2-sym (PiCode b f) ca (mkSigma vtyM (mkSigma vtyN core)) =
    mkSigma vtyN (mkSigma vtyM (record
      { domA = REqValTyPi.domA' core ; codB = REqValTyPi.codB' core
      ; domA' = REqValTyPi.domA core ; codB' = REqValTyPi.codB core
      ; redM = REqValTyPi.redN core ; redN = REqValTyPi.redM core
      ; cohF = REqValTyPi.cohF core ; fmAllU = REqValTyPi.fmAllU core
      ; convA = conv-sym (REqValTyPi.convA core)
      ; convB = let htA-e = Eq-transport (\ X -> HasType _ X _)
                             (fst (Red3-unique-Pi (RValTyPi.red vtyM) (REqValTyPi.redM core)))
                             (RValTyPi.htA vtyM)
                    htA'-e = Eq-transport (\ X -> HasType _ X _)
                              (fst (Red3-unique-Pi (RValTyPi.red vtyN) (REqValTyPi.redN core)))
                              (RValTyPi.htA vtyN)
                in ctx-conv-ConvTm htA-e htA'-e (REqValTyPi.convA core) (conv-sym (REqValTyPi.convB core))
      ; eqA = EqValTy2-sym b (fst ca) (REqValTyPi.eqA core)
      ; edgeET = \ u' v' sel P htP valP ->
          let htA'-e = Eq-transport (\ X -> HasType _ X _)
                         (fst (Red3-unique-Pi (RValTyPi.red vtyN) (REqValTyPi.redN core)))
                         (RValTyPi.htA vtyN)
              htA-e = Eq-transport (\ X -> HasType _ X _)
                        (fst (Red3-unique-Pi (RValTyPi.red vtyM) (REqValTyPi.redM core)))
                        (RValTyPi.htA vtyM)
              htP-A = ty-conv htP (conv-sym (REqValTyPi.convA core)) htA-e
              valP-A = Val2-EqValTy2-fwd u' b (fst ca) (EqValTy2-sym b (fst ca) (REqValTyPi.eqA core)) valP
          in EqValTy2-sym v' (Coherent-Selection-val sel (REqValTyPi.cohF core))
               (REqValTyPi.edgeET core u' v' sel P htP-A valP-A)
      }))
  EqValTy2-sym (SigmaCode b f) ca (mkSigma vtyM (mkSigma vtyN core)) =
    mkSigma vtyN (mkSigma vtyM (record
      { domA = REqValTySigma.domA' core ; codB = REqValTySigma.codB' core
      ; domA' = REqValTySigma.domA core ; codB' = REqValTySigma.codB core
      ; redM = REqValTySigma.redN core ; redN = REqValTySigma.redM core
      ; cohF = REqValTySigma.cohF core ; fmAllU = REqValTySigma.fmAllU core
      ; convA = conv-sym (REqValTySigma.convA core)
      ; convB = let htA-e = Eq-transport (\ X -> HasType _ X _)
                             (fst (Red3-unique-Sigma (RValTySigma.red vtyM) (REqValTySigma.redM core)))
                             (RValTySigma.htA vtyM)
                    htA'-e = Eq-transport (\ X -> HasType _ X _)
                              (fst (Red3-unique-Sigma (RValTySigma.red vtyN) (REqValTySigma.redN core)))
                              (RValTySigma.htA vtyN)
                in ctx-conv-ConvTm htA-e htA'-e (REqValTySigma.convA core) (conv-sym (REqValTySigma.convB core))
      ; eqA = EqValTy2-sym b (fst ca) (REqValTySigma.eqA core)
      ; edgeET = \ u' v' sel P htP valP ->
          let htA'-e = Eq-transport (\ X -> HasType _ X _)
                         (fst (Red3-unique-Sigma (RValTySigma.red vtyN) (REqValTySigma.redN core)))
                         (RValTySigma.htA vtyN)
              htA-e = Eq-transport (\ X -> HasType _ X _)
                        (fst (Red3-unique-Sigma (RValTySigma.red vtyM) (REqValTySigma.redM core)))
                        (RValTySigma.htA vtyM)
              htP-A = ty-conv htP (conv-sym (REqValTySigma.convA core)) htA-e
              valP-A = Val2-EqValTy2-fwd u' b (fst ca) (EqValTy2-sym b (fst ca) (REqValTySigma.eqA core)) valP
          in EqValTy2-sym v' (Coherent-Selection-val sel (REqValTySigma.cohF core))
               (REqValTySigma.edgeET core u' v' sel P htP-A valP-A)
      }))
  ------------------------------------------------------------------
  -- EqValTy2-trans
  ------------------------------------------------------------------

  EqValTy2-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
    (u : FinEl) -> Coherent u ->
    EqValTy2 G A B u -> EqValTy2 G B C u -> EqValTy2 G A C u
  EqValTy2-trans Bot cu tt tt = tt
  EqValTy2-trans UCode cu eqAB eqBC = mkSigma (fst eqAB) (snd eqBC)
  EqValTy2-trans PropCode cu tt tt = tt
  EqValTy2-trans (FunEl g) cu tt tt = tt
  EqValTy2-trans (PairCode u v) cu tt tt = tt
  EqValTy2-trans (PiCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = REqValTyPi.domA coreAB
        B0    = REqValTyPi.codB coreAB
        A0'   = REqValTyPi.domA' coreAB
        B0'   = REqValTyPi.codB' coreAB
        rA    = REqValTyPi.redM coreAB
        rB1   = REqValTyPi.redN coreAB
        cf1   = REqValTyPi.cohF coreAB
        fmU1  = REqValTyPi.fmAllU coreAB
        convAA_AB = REqValTyPi.convA coreAB
        convBB_AB = REqValTyPi.convB coreAB
        eqDomAB = REqValTyPi.eqA coreAB
        petAB   = REqValTyPi.edgeET coreAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = REqValTyPi.domA coreBC
        B1    = REqValTyPi.codB coreBC
        A1'   = REqValTyPi.domA' coreBC
        B1'   = REqValTyPi.codB' coreBC
        rB2   = REqValTyPi.redM coreBC
        rC    = REqValTyPi.redN coreBC
        cf2   = REqValTyPi.cohF coreBC
        fmU2  = REqValTyPi.fmAllU coreBC
        convAA_BC = REqValTyPi.convA coreBC
        convBB_BC = REqValTyPi.convB coreBC
        eqDomBC = REqValTyPi.eqA coreBC
        petBC   = REqValTyPi.edgeET coreBC
        uniq = Red3-unique-Pi rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        -- htA0' needed early for petAC
        redB1-vty-e = RValTyPi.red vtyB1
        uniqB1-dom-e = Red3-unique-Pi redB1-vty-e rB1
        htA0'-raw-e = RValTyPi.htA vtyB1
        htA0'-e = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        petAC : PiEdgeEqTy2 _ A0 B0 B1' b f
        petAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = petAB u' v' sel P htP valP
              eqt2 = petBC u' v' sel P htP-A1 valP-A1
              eqt2' = Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        -- convAA_trans
        convAA_BC' = Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        -- convBB_trans
        convBB_BC-transported = Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = RValTyPi.red vtyA
        uniqA-dom = Red3-unique-Pi redA-vty rA
        htA0-raw = RValTyPi.htA vtyA
        htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = RValTyPi.red vtyB1
        uniqB1-dom = Red3-unique-Pi redB1-vty rB1
        htA0'-raw = RValTyPi.htA vtyB1
        htA0' = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = record
          { domA = A0 ; codB = B0 ; domA' = A1' ; codB' = B1'
          ; redM = rA ; redN = rC ; cohF = cf1 ; fmAllU = fmU1
          ; convA = convAA_AC ; convB = convBB_AC
          ; eqA = eqDomAC ; edgeET = petAC
          }
    in mkSigma vtyA (mkSigma vtyC resultCore)
  EqValTy2-trans (SigmaCode b f) cu eqAB eqBC =
    let vtyA  = fst eqAB
        vtyB1 = fst (snd eqAB)
        coreAB = snd (snd eqAB)
        A0    = REqValTySigma.domA coreAB
        B0    = REqValTySigma.codB coreAB
        A0'   = REqValTySigma.domA' coreAB
        B0'   = REqValTySigma.codB' coreAB
        rA    = REqValTySigma.redM coreAB
        rB1   = REqValTySigma.redN coreAB
        cf1   = REqValTySigma.cohF coreAB
        fmU1  = REqValTySigma.fmAllU coreAB
        convAA_AB = REqValTySigma.convA coreAB
        convBB_AB = REqValTySigma.convB coreAB
        eqDomAB = REqValTySigma.eqA coreAB
        petAB   = REqValTySigma.edgeET coreAB
        vtyB2 = fst eqBC
        vtyC  = fst (snd eqBC)
        coreBC = snd (snd eqBC)
        A1    = REqValTySigma.domA coreBC
        B1    = REqValTySigma.codB coreBC
        A1'   = REqValTySigma.domA' coreBC
        B1'   = REqValTySigma.codB' coreBC
        rB2   = REqValTySigma.redM coreBC
        rC    = REqValTySigma.redN coreBC
        cf2   = REqValTySigma.cohF coreBC
        fmU2  = REqValTySigma.fmAllU coreBC
        convAA_BC = REqValTySigma.convA coreBC
        convBB_BC = REqValTySigma.convB coreBC
        eqDomBC = REqValTySigma.eqA coreBC
        petBC   = REqValTySigma.edgeET coreBC
        uniq = Red3-unique-Sigma rB1 rB2
        eqA0'A1 = fst uniq
        eqB0'B1 = snd uniq
        cb = fst cu
        eqDomBC' = Eq-transport (\ X -> EqValTy2 _ X A1' b) (Eq-sym eqA0'A1) eqDomBC
        eqDomAC  = EqValTy2-trans b cb eqDomAB eqDomBC'
        redB1-vty-e = RValTySigma.red vtyB1
        uniqB1-dom-e = Red3-unique-Sigma redB1-vty-e rB1
        htA0'-raw-e = RValTySigma.htA vtyB1
        htA0'-e = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom-e) htA0'-raw-e
        petAC : SigmaEdgeEqTy2 _ A0 B0 B1' b f
        petAC = \ u' v' sel P htP valP ->
          let valP-A0' = Val2-EqValTy2-fwd u' b cb eqDomAB valP
              valP-A1  = Eq-transport (\ X -> Val2 _ P X u' b) eqA0'A1 valP-A0'
              htP-A0'  = ty-conv htP convAA_AB htA0'-e
              htP-A1   = Eq-transport (\ X -> HasType _ P X) eqA0'A1 htP-A0'
              eqt1 = petAB u' v' sel P htP valP
              eqt2 = petBC u' v' sel P htP-A1 valP-A1
              eqt2' = Eq-transport (\ X -> EqValTy2 _ (subst1 X P) (subst1 B1' P) v')
                        (Eq-sym eqB0'B1) eqt2
              cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
          in EqValTy2-trans v' cv' eqt1 eqt2'
        convAA_BC' = Eq-transport (\ X -> ConvTm _ X A1' _) (Eq-sym eqA0'A1) convAA_BC
        convAA_AC = conv-trans convAA_AB convAA_BC'
        convBB_BC-transported = Eq-transport (\ X -> ConvTm (extend _ A0') X B1' _) (Eq-sym eqB0'B1)
                                  (Eq-transport (\ X -> ConvTm (extend _ X) B1 B1' _) (Eq-sym eqA0'A1) convBB_BC)
        redA-vty = RValTySigma.red vtyA
        uniqA-dom = Red3-unique-Sigma redA-vty rA
        htA0-raw = RValTySigma.htA vtyA
        htA0  = Eq-transport (\ X -> HasType _ X _) (fst uniqA-dom) htA0-raw
        redB1-vty = RValTySigma.red vtyB1
        uniqB1-dom = Red3-unique-Sigma redB1-vty rB1
        htA0'-raw = RValTySigma.htA vtyB1
        htA0' = Eq-transport (\ X -> HasType _ X _) (fst uniqB1-dom) htA0'-raw
        convBB_BC' = ctx-conv-ConvTm htA0' htA0 (conv-sym convAA_AB) convBB_BC-transported
        convBB_AC = conv-trans convBB_AB convBB_BC'
        resultCore = record
          { domA = A0 ; codB = B0 ; domA' = A1' ; codB' = B1'
          ; redM = rA ; redN = rC ; cohF = cf1 ; fmAllU = fmU1
          ; convA = convAA_AC ; convB = convBB_AC
          ; eqA = eqDomAC ; edgeET = petAC
          }
    in mkSigma vtyA (mkSigma vtyC resultCore)

  ------------------------------------------------------------------
  -- EqVal2-sym
  ------------------------------------------------------------------

  -- (EqVal2-sym-SigmaCode is inlined at each call site)

  EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M N A u a -> EqVal2 G N M A u a
  EqVal2-sym Bot Bot cu ca tt = tt
  EqVal2-sym UCode Bot cu ca tt = tt
  EqVal2-sym PropCode Bot cu ca tt = tt
  EqVal2-sym (FunEl g) Bot cu ca tt = tt
  EqVal2-sym (PiCode a' f') Bot cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') Bot cu ca tt = tt
  EqVal2-sym (PairCode u' v') Bot cu ca tt = tt
  EqVal2-sym Bot UCode cu ca tt = tt
  EqVal2-sym UCode UCode cu ca ev =
    mkSigma (fst (snd ev)) (mkSigma (fst ev) (EqValTy2-sym UCode cu (snd (snd ev))))
  EqVal2-sym (FunEl g) UCode cu ca ev = tt
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
  EqVal2-sym (FunEl g) PropCode cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') PropCode cu ca tt = tt
  EqVal2-sym (PairCode u' v') PropCode cu ca tt = tt
  EqVal2-sym Bot (FunEl h) cu ca tt = tt
  EqVal2-sym UCode (FunEl h) cu ca tt = tt
  EqVal2-sym PropCode (FunEl h) cu ca tt = tt
  EqVal2-sym (FunEl g) (FunEl h) cu ca tt = tt
  EqVal2-sym (PiCode a' f') (FunEl h) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (FunEl h) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (FunEl h) cu ca tt = tt
  EqVal2-sym Bot (PiCode b f) cu ca tt = tt
  EqVal2-sym UCode (PiCode b f) cu ca tt = tt
  EqVal2-sym PropCode (PiCode b f) cu ca tt = tt
  EqVal2-sym (FunEl g) (PiCode b f) cu ca ev =
    let vty  = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        eqvp = snd (snd (snd ev))
        A0     = REqValPi.domA0 eqvp
        B0     = REqValPi.codB0 eqvp
        redA   = REqValPi.red eqvp
        cg     = REqValPi.cohG eqvp
        fmg    = REqValPi.fmG eqvp
        paev   = REqValPi.appEV eqvp
        cf     = snd ca
        paev'  : PiAppEqVal2 _ _ _ _ B0 b f g
        paev'  = \ u' v' sel P htP valP ->
          let body = paev u' v' sel P htP valP
              ctg  = cft-from-cf g cg
              cu'  = Coherent-Selection sel ctg
              cv'  = Coherent-Selection-val sel ctg
              cev  = Coherent-EvalFun f u' cf cu'
          in EqVal2-sym v' (EvalFun f u') cv' cev body
        eqvp' = record
          { domA0 = A0 ; codB0 = B0 ; red = redA
          ; cohG = cg ; fmG = fmg ; appEV = paev'
          }
    in mkSigma vty (mkSigma vpiN (mkSigma vpiM eqvp'))
  EqVal2-sym (PiCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (PiCode b f) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (PiCode b f) cu ca tt = tt
  EqVal2-sym Bot (SigmaCode b f) cu ca tt = tt
  EqVal2-sym UCode (SigmaCode b f) cu ca ev =
    let eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym Bot b tt (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym PropCode (SigmaCode b f) cu ca ev =
    let eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym Bot b tt (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym (FunEl g) (SigmaCode b f) cu ca ev =
    let eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym Bot b tt (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym (PiCode a' f') (SigmaCode b f) cu ca ev =
    let eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym Bot b tt (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym (SigmaCode a' f') (SigmaCode b f) cu ca ev =
    let eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym Bot b tt (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma (fst (snd ev)) (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym (PairCode u' v') (SigmaCode b f) cu ca ev =
    let vpM = fst (snd ev)
        eqp = snd (snd (snd ev))
        eqFst' = EqVal2-sym u' b (RValSigma.cohW1 vpM) (fst ca) (REqValSigma.eqFst eqp)
    in mkSigma (fst ev) (mkSigma (fst (snd (snd ev))) (mkSigma vpM (record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFstM = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFstM = REqValSigma.valFstN eqp ; valSndM = REqValSigma.valSndN eqp ; htFstN = REqValSigma.htFstM eqp ; valFstN = REqValSigma.valFstM eqp ; valSndN = REqValSigma.valSndM eqp ; eqFst = eqFst' })))
  EqVal2-sym Bot (PairCode x y) cu ca tt = tt
  EqVal2-sym UCode (PairCode x y) cu ca tt = tt
  EqVal2-sym PropCode (PairCode x y) cu ca tt = tt
  EqVal2-sym (FunEl g) (PairCode x y) cu ca tt = tt
  EqVal2-sym (PiCode a' f') (PairCode x y) cu ca tt = tt
  EqVal2-sym (SigmaCode a' f') (PairCode x y) cu ca tt = tt
  EqVal2-sym (PairCode u' v') (PairCode x y) cu ca tt = tt

  ------------------------------------------------------------------
  -- EqVal2-trans
  ------------------------------------------------------------------

  EqVal2-trans-SigmaCode-body : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
    (w : FinEl) (b : FinEl) (f : FinFun) -> Coherent w -> Coherent (SigmaCode b f) ->
    Pair (ValTy2 G A (SigmaCode b f)) (Pair (RValSigma G M1 A w b f) (Pair (RValSigma G M2 A w b f) (REqValSigma G M1 M2 A w b f))) ->
    Pair (ValTy2 G A (SigmaCode b f)) (Pair (RValSigma G M2 A w b f) (Pair (RValSigma G M3 A w b f) (REqValSigma G M2 M3 A w b f))) ->
    Pair (ValTy2 G A (SigmaCode b f)) (Pair (RValSigma G M1 A w b f) (Pair (RValSigma G M3 A w b f) (REqValSigma G M1 M3 A w b f)))
  EqVal2-trans-SigmaCode-body w b f cu ca ev1 ev2 =
    let vty     = fst ev1
        vpM1    = fst (snd ev1)
        vpM3    = fst (snd (snd ev2))
        eqp1    = snd (snd (snd ev1))
        eqp2    = snd (snd (snd ev2))
        Ax      = REqValSigma.domA eqp1
        Bx      = REqValSigma.codB eqp1
        redAx   = REqValSigma.red eqp1
        Ay      = REqValSigma.domA eqp2
        By      = REqValSigma.codB eqp2
        redAy   = REqValSigma.red eqp2
        uniq    = Red3-unique-Sigma redAx redAy
        eqA0    = fst uniq
        eqB0    = snd uniq
        eqFst1  = REqValSigma.eqFst eqp1
        eqFst2  = REqValSigma.eqFst eqp2
        eqFst2' = Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X (codeFst w) b) (Eq-sym eqA0) eqFst2
        eqFst'  = EqVal2-trans (codeFst w) b (RValSigma.cohW1 vpM1) (fst ca) eqFst1 eqFst2'
        eqp'    = record
          { domA    = Ax ; codB = Bx ; red = redAx
          ; htFstM  = REqValSigma.htFstM eqp1
          ; cohW1   = REqValSigma.cohW1 eqp1
          ; fmW1    = REqValSigma.fmW1 eqp1
          ; valFstM = REqValSigma.valFstM eqp1
          ; valSndM = REqValSigma.valSndM eqp1
          ; htFstN  = Eq-transport (\ X -> HasType _ _ X) (Eq-sym eqA0) (REqValSigma.htFstN eqp2)
          ; valFstN = Eq-transport (\ X -> Val2 _ _ X (codeFst w) b) (Eq-sym eqA0) (REqValSigma.valFstN eqp2)
          ; valSndN = Eq-transport (\ X -> Val2 _ _ (subst1 X _) (codeSnd w) (EvalFun f (codeFst w))) (Eq-sym eqB0)
                        (REqValSigma.valSndN eqp2)
          ; eqFst   = eqFst'
          }
    in mkSigma vty (mkSigma vpM1 (mkSigma vpM3 eqp'))

  EqVal2-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a ->
    EqVal2 G M1 M3 A u a
  EqVal2-trans Bot Bot cu ca tt tt = tt
  EqVal2-trans UCode Bot cu ca tt tt = tt
  EqVal2-trans PropCode Bot cu ca tt tt = tt
  EqVal2-trans (FunEl g) Bot cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') Bot cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') Bot cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') Bot cu ca tt tt = tt
  EqVal2-trans Bot UCode cu ca tt tt = tt
  EqVal2-trans UCode UCode cu ca ev1 ev2 =
    mkSigma (fst ev1) (mkSigma (fst (snd ev2)) (EqValTy2-trans UCode cu (snd (snd ev1)) (snd (snd ev2))))
  EqVal2-trans (FunEl g) UCode cu ca ev1 ev2 = tt
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
  EqVal2-trans (FunEl g) PropCode cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') PropCode cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') PropCode cu ca tt tt = tt
  EqVal2-trans Bot (FunEl h) cu ca tt tt = tt
  EqVal2-trans UCode (FunEl h) cu ca tt tt = tt
  EqVal2-trans PropCode (FunEl h) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (FunEl h) cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') (FunEl h) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (FunEl h) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (FunEl h) cu ca tt tt = tt
  EqVal2-trans Bot (PiCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans PropCode (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (PiCode b f) cu ca ev1 ev2 =
    let vty    = fst ev1
        vpiM1  = fst (snd ev1)
        vpiM3  = fst (snd (snd ev2))
        epi1   = snd (snd (snd ev1))
        epi2   = snd (snd (snd ev2))
        Ax     = REqValPi.domA0 epi1
        Bx     = REqValPi.codB0 epi1
        redAx  = REqValPi.red epi1
        cg     = REqValPi.cohG epi1
        fmg    = REqValPi.fmG epi1
        paev1  = REqValPi.appEV epi1
        Ay     = REqValPi.domA0 epi2
        By     = REqValPi.codB0 epi2
        redAy  = REqValPi.red epi2
        paev2  = REqValPi.appEV epi2
        uniq   = Red3-unique-Pi redAx redAy
        eqA0   = fst uniq
        eqB0   = snd uniq
        paev2' : PiAppEqVal2 _ _ _ Ax Bx b f g
        paev2' = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X Bx b f g) (Eq-sym eqA0)
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
        epi' = record
          { domA0 = Ax ; codB0 = Bx ; red = redAx
          ; cohG = cg ; fmG = fmg ; appEV = paev'
          }
    in mkSigma vty (mkSigma vpiM1 (mkSigma vpiM3 epi'))
  EqVal2-trans (PiCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (PiCode b f) cu ca tt tt = tt
  EqVal2-trans Bot (SigmaCode b f) cu ca tt tt = tt
  EqVal2-trans UCode (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body UCode b f cu ca ev1 ev2
  EqVal2-trans PropCode (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body PropCode b f cu ca ev1 ev2
  EqVal2-trans (FunEl g) (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body (FunEl g) b f cu ca ev1 ev2
  EqVal2-trans (PiCode a' f') (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body (PiCode a' f') b f cu ca ev1 ev2
  EqVal2-trans (SigmaCode a' f') (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body (SigmaCode a' f') b f cu ca ev1 ev2
  EqVal2-trans (PairCode u' v') (SigmaCode b f) cu ca ev1 ev2 = EqVal2-trans-SigmaCode-body (PairCode u' v') b f cu ca ev1 ev2
  EqVal2-trans Bot (PairCode x y) cu ca tt tt = tt
  EqVal2-trans UCode (PairCode x y) cu ca tt tt = tt
  EqVal2-trans PropCode (PairCode x y) cu ca tt tt = tt
  EqVal2-trans (FunEl g) (PairCode x y) cu ca tt tt = tt
  EqVal2-trans (PiCode a' f') (PairCode x y) cu ca tt tt = tt
  EqVal2-trans (SigmaCode a' f') (PairCode x y) cu ca tt tt = tt
  EqVal2-trans (PairCode u' v') (PairCode x y) cu ca tt tt = tt

  ------------------------------------------------------------------
  -- downVal2 / downEqVal2 / downValTy2 / downEqValTy2
  ------------------------------------------------------------------

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

  restrictEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u u' a : FinEl) ->
    LeCode u' u -> FinMem u' a -> FinMem u a ->
    EqVal2 G M N T u a -> EqVal2 G M N T u' a

  -- downVal2 cases
  downVal2 G M T Bot Bot          a1             le mem ca0 ca1 src = tt
  downVal2 G M T UCode Bot        a1             le mem ca0 ca1 src = tt
  downVal2 G M T PropCode Bot     a1             le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g) Bot    a1             le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a' f') Bot a1           le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a' f') Bot a1        le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode u' v') Bot a1         le mem ca0 ca1 src = tt
  downVal2 G M T u UCode        Bot            ()
  downVal2 G M T Bot UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T UCode UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T PropCode UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T (FunEl g2) UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T (PiCode a2 f2) UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T (SigmaCode a2 f2) UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T (PairCode x2 y2) UCode        UCode          le mem ca0 ca1 src = src
  downVal2 G M T u UCode        (FunEl h)      ()
  downVal2 G M T u UCode        (PiCode b f)   ()
  downVal2 G M T u UCode        (SigmaCode b f) ()
  downVal2 G M T u UCode        (PairCode x y) ()
  downVal2 G M T u UCode        PropCode       ()
  downVal2 G M T Bot (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downVal2 G M T Bot (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downVal2 G M T Bot (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downVal2 G M T Bot (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downVal2 G M T Bot (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downVal2 G M T Bot (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T UCode (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T PropCode (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T (FunEl g2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T (PiCode a2 f2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T (SigmaCode a2 f2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T (PairCode x2 y2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downVal2 G M T u PropCode       Bot            ()
  downVal2 G M T u PropCode       UCode          ()
  downVal2 G M T Bot PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T UCode PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T PropCode PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T (FunEl g2) PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T (PiCode a2 f2) PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T (SigmaCode a2 f2) PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T (PairCode x2 y2) PropCode       PropCode       le mem ca0 ca1 src = src
  downVal2 G M T u PropCode       (FunEl h)      ()
  downVal2 G M T u PropCode       (PiCode b f)   ()
  downVal2 G M T u PropCode       (SigmaCode b f) ()
  downVal2 G M T u PropCode       (PairCode x y) ()
  downVal2 G M T u (PiCode b0 f0) Bot          ()
  downVal2 G M T u (PiCode b0 f0) UCode        ()
  downVal2 G M T u (PiCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (PiCode b0 f0) PropCode     ()
  downVal2 G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty  = fst src
        vpiM = snd src
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        vty'  = downValTy2 G _ (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
        -- Extract vtAb1 from vty (RValTyPi)
        vtAb1 : ValTy2 G (RValPi.domA0 vpiM) b1
        vtAb1 = Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vty))))
                   (RValTyPi.valA vty)
        -- Extract PiEdgeVal2 from vty for piEV
        piEV-raw = RValTyPi.edgeV vty
        uniq-v = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vty)
        piEV : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b1 f1
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b1 f1) (Eq-sym (snd uniq-v))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vty) b1 f1) (Eq-sym (fst uniq-v)) piEV-raw)
        vpi' = record
          { domA0 = RValPi.domA0 vpiM
          ; codB0 = RValPi.codB0 vpiM
          ; red   = RValPi.red vpiM
          ; cohG  = RValPi.cohG vpiM
          ; fmG   = fst mem
          ; appV  = downPiAppVal2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appV vpiM)
          ; appE  = downPiAppEq2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (RValPi.cohG vpiM) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (RValPi.fmG vpiM) vtAb1 (RValPi.appE vpiM)
          }
    in mkSigma vty' vpi'
  downVal2 G M T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode cases
  downVal2 G M T u (SigmaCode b0 f0) Bot          ()
  downVal2 G M T u (SigmaCode b0 f0) UCode        ()
  downVal2 G M T u (SigmaCode b0 f0) (FunEl h)    ()
  downVal2 G M T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downVal2 G M T u (SigmaCode b0 f0) (PairCode x y) ()
  downVal2 G M T u (SigmaCode b0 f0) PropCode     ()
  downVal2 G M T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downVal2 G M T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downVal2 G M T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downVal2 G M T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downVal2 G M T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downVal2 G M T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let vty   = fst src
        vpair = snd src
        fmu'0 = fst (fst mem)
        v2Fst' = downVal2 G (Fst _) (RValSigma.domA vpair) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpair)
        ctf0  = snd ca0
        ctf1  = snd (snd ca1)
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 (RValSigma.cohW1 vpair) (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 (RValSigma.cohW1 vpair)
        ca1_ef = EvalFun-in-UCode f1 u' b1 ctf1 (RValSigma.cohW1 vpair) (fst (snd ca1))
        v2Snd' = downVal2 G (Snd _) (subst1 (RValSigma.codB vpair) (Fst _)) v' (EvalFun f0 u') (EvalFun f1 u')
                   le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpair)
        vty'  = downValTy2 G _ (SigmaCode b0 f0) (SigmaCode b1 f1) le (snd (snd mem)) ca1 vty
        vpair' = record
          { domA   = RValSigma.domA vpair
          ; codB   = RValSigma.codB vpair
          ; red    = RValSigma.red vpair
          ; htFst  = RValSigma.htFst vpair
          ; cohW1   = RValSigma.cohW1 vpair
          ; fmW1    = fmu'0
          ; valFst = v2Fst'
          ; valSnd = v2Snd'
          }
    in mkSigma vty' vpair'
  -- PairCode: all Val2 cases at PairCode = Top
  downVal2 G M T Bot (PairCode x0 y0) a1 le ()
  downVal2 G M T UCode (PairCode x0 y0) a1 le ()
  downVal2 G M T PropCode (PairCode x0 y0) a1 le ()
  downVal2 G M T (FunEl g) (PairCode x0 y0) a1 le ()
  downVal2 G M T (PiCode a' ff) (PairCode x0 y0) a1 le ()
  downVal2 G M T (SigmaCode a' ff) (PairCode x0 y0) a1 le ()
  downVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le ()

  -- downEqVal2 cases
  downEqVal2 G M N T Bot Bot          a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode Bot        a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode Bot     a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g) Bot    a1             le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a' f') Bot a1           le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a' f') Bot a1        le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode u' v') Bot a1         le mem ca0 ca1 src = tt
  downEqVal2 G M N T u UCode        Bot            ()
  downEqVal2 G M N T Bot UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T UCode UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T PropCode UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T (FunEl g2) UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T (PiCode a2 f2) UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T (SigmaCode a2 f2) UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T (PairCode x2 y2) UCode        UCode          le mem ca0 ca1 src = src
  downEqVal2 G M N T u UCode        (FunEl h)      ()
  downEqVal2 G M N T u UCode        (PiCode b f)   ()
  downEqVal2 G M N T u UCode        (SigmaCode b f) ()
  downEqVal2 G M N T u UCode        (PairCode x y) ()
  downEqVal2 G M N T u UCode        PropCode       ()
  downEqVal2 G M N T Bot (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    Bot            le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    UCode          le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    (SigmaCode b f) le mem ca0 ca1 src = tt
  downEqVal2 G M N T Bot (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T PropCode (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (FunEl g2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PiCode a2 f2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (SigmaCode a2 f2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T (PairCode x2 y2) (FunEl g)    (PairCode x y) le mem ca0 ca1 src = tt
  downEqVal2 G M N T u PropCode       Bot            ()
  downEqVal2 G M N T u PropCode       UCode          ()
  downEqVal2 G M N T Bot PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T UCode PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T PropCode PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T (FunEl g2) PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T (PiCode a2 f2) PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T (SigmaCode a2 f2) PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T (PairCode x2 y2) PropCode       PropCode       le mem ca0 ca1 src = src
  downEqVal2 G M N T u PropCode       (FunEl h)      ()
  downEqVal2 G M N T u PropCode       (PiCode b f)   ()
  downEqVal2 G M N T u PropCode       (SigmaCode b f) ()
  downEqVal2 G M N T u PropCode       (PairCode x y) ()
  downEqVal2 G M N T u (PiCode b0 f0) Bot          ()
  downEqVal2 G M N T u (PiCode b0 f0) UCode        ()
  downEqVal2 G M N T u (PiCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  downEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T u (PiCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
    let vty   = fst src
        vpiM  = fst (snd src)
        vpiN  = fst (snd (snd src))
        epi   = snd (snd (snd src))
        fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
        cf0   = snd ca0
        cb0   = fst ca0
        b1U   = fst ca1
        cb1   = coh-from-aU b1 b1U
        allU1 = fst (snd ca1)
        b0U   = fst fmem-pf
        allU0 = fst (snd fmem-pf)
        vtAb1 : ValTy2 G (REqValPi.domA0 epi) b1
        vtAb1 = Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vty))))
                   (RValTyPi.valA vty)
        valM  = mkSigma vty vpiM
        valN  = mkSigma vty vpiN
        valM' = downVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
        valN' = downVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
        -- piEV for downPiAppEqVal2
        uniq-v = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vty)
        piEV-raw = RValTyPi.edgeV vty
        piEV : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b1 f1
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b1 f1) (Eq-sym (snd uniq-v))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vty) b1 f1) (Eq-sym (fst uniq-v)) piEV-raw)
        epi'  = record
          { domA0 = REqValPi.domA0 epi
          ; codB0 = REqValPi.codB0 epi
          ; red   = REqValPi.red epi
          ; cohG  = REqValPi.cohG epi
          ; fmG   = fst mem
          ; appEV = downPiAppEqVal2 G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 (snd (snd ca1)) (REqValPi.cohG epi) (fst mem)
                      cb0 cb1 b1U b0U allU0 allU1 le (REqValPi.fmG epi) vtAb1 (REqValPi.appEV epi)
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  downEqVal2 G M N T (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
  downEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode cases
  downEqVal2 G M N T u (SigmaCode b0 f0) Bot          ()
  downEqVal2 G M N T u (SigmaCode b0 f0) UCode        ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (FunEl h)    ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) (PairCode x y) ()
  downEqVal2 G M N T u (SigmaCode b0 f0) PropCode     ()
  downEqVal2 G M N T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
  downEqVal2 G M N T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downEqVal2 G M N T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downEqVal2 G M N T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downEqVal2 G M N T (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downEqVal2 G M N T (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  downEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src =
    let vpairM = fst (snd src)
        vpairN = fst (snd (snd src))
        eqp   = snd (snd (snd src))
        fmu'0 = fst (fst mem)
        ctf0  = snd ca0
        ctf1  = snd (snd ca1)
        cu'   = REqValSigma.cohW1 eqp
        v2FstM' = downVal2 G (Fst M) (RValSigma.domA vpairM) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpairM)
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 cu' (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 cu'
        ca1_ef = EvalFun-in-UCode f1 u' b1 ctf1 cu' (fst (snd ca1))
        v2SndM' = downVal2 G (Snd M) (subst1 (RValSigma.codB vpairM) (Fst M)) v' (EvalFun f0 u') (EvalFun f1 u')
                    le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpairM)
        v2FstN' = downVal2 G (Fst N) (RValSigma.domA vpairN) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (RValSigma.valFst vpairN)
        v2SndN' = downVal2 G (Snd N) (subst1 (RValSigma.codB vpairN) (Fst N)) v' (EvalFun f0 u') (EvalFun f1 u')
                    le_ef (snd (fst mem)) ca0_ef ca1_ef (RValSigma.valSnd vpairN)
        vty'  = downValTy2 G _ (SigmaCode b0 f0) (SigmaCode b1 f1) le (snd (snd mem)) ca1 (fst src)
        eqFst' = downEqVal2 G (Fst M) (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.eqFst eqp)
        -- Compute val for eqp' separately from the REqValPair fields
        v2FstM-eq = downVal2 G (Fst M) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.valFstM eqp)
        v2SndM-eq = downVal2 G (Snd M) (subst1 (REqValSigma.codB eqp) (Fst M)) v' (EvalFun f0 u') (EvalFun f1 u')
                      le_ef (snd (fst mem)) ca0_ef ca1_ef (REqValSigma.valSndM eqp)
        v2FstN-eq = downVal2 G (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 (fst ca0) (fst ca1) (REqValSigma.valFstN eqp)
        v2SndN-eq = downVal2 G (Snd N) (subst1 (REqValSigma.codB eqp) (Fst N)) v' (EvalFun f0 u') (EvalFun f1 u')
                      le_ef (snd (fst mem)) ca0_ef ca1_ef (REqValSigma.valSndN eqp)
        vpairM' = record
          { domA = RValSigma.domA vpairM ; codB = RValSigma.codB vpairM ; red = RValSigma.red vpairM
          ; htFst = RValSigma.htFst vpairM ; cohW1 = RValSigma.cohW1 vpairM ; fmW1 = fmu'0
          ; valFst = v2FstM' ; valSnd = v2SndM'
          }
        vpairN' = record
          { domA = RValSigma.domA vpairN ; codB = RValSigma.codB vpairN ; red = RValSigma.red vpairN
          ; htFst = RValSigma.htFst vpairN ; cohW1 = RValSigma.cohW1 vpairN ; fmW1 = fmu'0
          ; valFst = v2FstN' ; valSnd = v2SndN'
          }
        eqp'  = record
          { domA    = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM  = REqValSigma.htFstM eqp
          ; cohW1    = cu'
          ; fmW1     = fmu'0
          ; valFstM = v2FstM-eq
          ; valSndM = v2SndM-eq
          ; htFstN  = REqValSigma.htFstN eqp
          ; valFstN = v2FstN-eq
          ; valSndN = v2SndN-eq
          ; eqFst   = eqFst'
          }
    in mkSigma vty' (mkSigma vpairM' (mkSigma vpairN' eqp'))
  -- PairCode: all EqVal2 = Top
  downEqVal2 G M N T Bot (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T UCode (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T PropCode (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (PiCode a' ff) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (SigmaCode a' ff) (PairCode x0 y0) a1 le ()
  downEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le ()

  -- downValTy2 cases
  downValTy2 G M Bot          u1             le fmem cu1 src = tt
  downValTy2 G M UCode        Bot            ()
  downValTy2 G M UCode        UCode          le fmem cu1 src = src
  downValTy2 G M UCode        (FunEl h)      ()
  downValTy2 G M UCode        (PiCode b f)   ()
  downValTy2 G M UCode        (SigmaCode b f) ()
  downValTy2 G M UCode        (PairCode x y) ()
  downValTy2 G M PropCode      Bot            ()
  downValTy2 G M PropCode      UCode          ()
  downValTy2 G M PropCode      PropCode       le fmem cu1 src = src
  downValTy2 G M PropCode      (FunEl h)      ()
  downValTy2 G M PropCode      (PiCode b f)   ()
  downValTy2 G M PropCode      (SigmaCode b f) ()
  downValTy2 G M PropCode      (PairCode x y) ()
  downValTy2 G M (FunEl g)    u1             le ()
  downValTy2 G M (PiCode b0 f0) Bot          ()
  downValTy2 G M (PiCode b0 f0) UCode        ()
  downValTy2 G M (PiCode b0 f0) (FunEl h)    ()
  downValTy2 G M (PiCode b0 f0) (SigmaCode b1 f1) ()
  downValTy2 G M (PiCode b0 f0) (PairCode x y) ()
  downValTy2 G M (PiCode b0 f0) PropCode     ()
  downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
    let fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b1 = RValTyPi.valA src
        vtA-b0 = downValTy2 G (RValTyPi.domA src) b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        piEV0  = transportPiEdgeVal2-sel G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeV src)
        piEE0  = transportPiEdgeEq2-sel G (RValTyPi.domA src) (RValTyPi.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTyPi.cohF src) (RValTyPi.fmAllU src) vtA-b1 (RValTyPi.edgeE src)
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
  -- SigmaCode downValTy2
  downValTy2 G M (SigmaCode b0 f0) Bot          ()
  downValTy2 G M (SigmaCode b0 f0) UCode        ()
  downValTy2 G M (SigmaCode b0 f0) (FunEl h)    ()
  downValTy2 G M (SigmaCode b0 f0) (PiCode b1 f1) ()
  downValTy2 G M (SigmaCode b0 f0) (PairCode x y) ()
  downValTy2 G M (SigmaCode b0 f0) PropCode     ()
  downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
    let fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        vtA-b1 = RValTySigma.valA src
        vtA-b0 = downValTy2 G (RValTySigma.domA src) b0 b1 (fst le) fmem-b0 (fst cu1) vtA-b1
        sigEV0 = transportPiEdgeVal2-sel G (RValTySigma.domA src) (RValTySigma.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTySigma.cohF src) (RValTySigma.fmAllU src) vtA-b1 (RValTySigma.edgeV src)
        sigEE0 = transportPiEdgeEq2-sel G (RValTySigma.domA src) (RValTySigma.codB src) b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (RValTySigma.cohF src) (RValTySigma.fmAllU src) vtA-b1 (RValTySigma.edgeE src)
    in record
      { domA   = RValTySigma.domA src
      ; codB   = RValTySigma.codB src
      ; red    = RValTySigma.red src
      ; cohF   = sat0
      ; fmAllU = fmemAll0
      ; fmBU   = fmem-b0
      ; htA    = RValTySigma.htA src
      ; htB    = RValTySigma.htB src
      ; valA   = vtA-b0
      ; edgeV  = sigEV0
      ; edgeE  = sigEE0
      }
  -- PairCode downValTy2
  downValTy2 G M (PairCode u v) u1 le ()

  -- downEqValTy2 cases
  downEqValTy2 G M N Bot          u1             le fmem cu1 src = tt
  downEqValTy2 G M N UCode        Bot            ()
  downEqValTy2 G M N UCode        UCode          le fmem cu1 src = src
  downEqValTy2 G M N UCode        (FunEl h)      ()
  downEqValTy2 G M N UCode        (PiCode b f)   ()
  downEqValTy2 G M N UCode        (SigmaCode b f) ()
  downEqValTy2 G M N UCode        (PairCode x y) ()
  downEqValTy2 G M N PropCode      Bot            ()
  downEqValTy2 G M N PropCode      UCode          ()
  downEqValTy2 G M N PropCode      PropCode       le fmem cu1 src = src
  downEqValTy2 G M N PropCode      (FunEl h)      ()
  downEqValTy2 G M N PropCode      (PiCode b f)   ()
  downEqValTy2 G M N PropCode      (SigmaCode b f) ()
  downEqValTy2 G M N PropCode      (PairCode x y) ()
  downEqValTy2 G M N (FunEl g)    u1             le ()
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
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        -- vtA-b1 from vtyM1
        uniqM  = Red3-unique-Pi (RValTyPi.red vtyM1) (REqValTyPi.redM core)
        eqAMA  = fst uniqM
        vtA-b1 = Eq-transport (\ X -> ValTy2 G X b1) eqAMA (RValTyPi.valA vtyM1)
        eqvty0  = downEqValTy2 G (REqValTyPi.domA core) (REqValTyPi.domA' core) b0 b1 (fst le) fmem-b0 (fst cu1) (REqValTyPi.eqA core)
        piEEqT0 = transportPiEdgeEqTy2-sel G (REqValTyPi.domA core) (REqValTyPi.codB core) (REqValTyPi.codB' core) b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (REqValTyPi.cohF core) (REqValTyPi.fmAllU core) vtA-b1 (REqValTyPi.edgeET core)
        vtyM0  = downValTy2 G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
        core0  = record
          { domA = REqValTyPi.domA core ; codB = REqValTyPi.codB core
          ; domA' = REqValTyPi.domA' core ; codB' = REqValTyPi.codB' core
          ; redM = REqValTyPi.redM core ; redN = REqValTyPi.redN core
          ; cohF = sat0 ; fmAllU = fmemAll0
          ; convA = REqValTyPi.convA core ; convB = REqValTyPi.convB core
          ; eqA = eqvty0 ; edgeET = piEEqT0
          }
    in mkSigma vtyM0 (mkSigma vtyN0 core0)
  -- SigmaCode downEqValTy2
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
        fmem-b0  = fst fmem
        fmemAll0 = fst (snd fmem)
        sat0     = snd (snd fmem)
        cb1   = coh-from-aU b1 (fst cu1)
        cb0   = coh-from-aU b0 fmem-b0
        uniqM  = Red3-unique-Sigma (RValTySigma.red vtyM1) (REqValTySigma.redM core)
        eqAMA  = fst uniqM
        vtA-b1 = Eq-transport (\ X -> ValTy2 G X b1) eqAMA (RValTySigma.valA vtyM1)
        eqvty0  = downEqValTy2 G (REqValTySigma.domA core) (REqValTySigma.domA' core) b0 b1 (fst le) fmem-b0 (fst cu1) (REqValTySigma.eqA core)
        sigEEqT0 = transportPiEdgeEqTy2-sel G (REqValTySigma.domA core) (REqValTySigma.codB core) (REqValTySigma.codB' core) b0 f0 b1 f1
                    cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 (REqValTySigma.cohF core) (REqValTySigma.fmAllU core) vtA-b1 (REqValTySigma.edgeET core)
        vtyM0  = downValTy2 G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyM1
        vtyN0  = downValTy2 G N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyN1
        core0  = record
          { domA = REqValTySigma.domA core ; codB = REqValTySigma.codB core
          ; domA' = REqValTySigma.domA' core ; codB' = REqValTySigma.codB' core
          ; redM = REqValTySigma.redM core ; redN = REqValTySigma.redN core
          ; cohF = sat0 ; fmAllU = fmemAll0
          ; convA = REqValTySigma.convA core ; convB = REqValTySigma.convB core
          ; eqA = eqvty0 ; edgeET = sigEEqT0
          }
    in mkSigma vtyM0 (mkSigma vtyN0 core0)
  -- PairCode downEqValTy2
  downEqValTy2 G M N (PairCode u v) u1 le ()

  ------------------------------------------------------------------
  -- upVal2 / upEqVal2
  ------------------------------------------------------------------

  upVal2 G M T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode        Bot a1 le ()
  upVal2 G M T (FunEl g)    Bot a1 le ()
  upVal2 G M T (PiCode a f) Bot a1 le ()
  upVal2 G M T (SigmaCode a f) Bot a1 le ()
  upVal2 G M T (PairCode u' v') Bot a1 le ()
  upVal2 G M T PropCode     Bot a1 le ()
  upVal2 G M T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (FunEl g')     UCode UCode le ()
  upVal2 G M T PropCode        UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T u UCode Bot          ()
  upVal2 G M T u UCode PropCode     ()
  upVal2 G M T u UCode (FunEl h)    ()
  upVal2 G M T u UCode (PiCode b h) ()
  upVal2 G M T u UCode (SigmaCode b h) ()
  upVal2 G M T u UCode (PairCode x y) ()
  upVal2 G M T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (FunEl g) a1             le ()
  upVal2 G M T PropCode       (FunEl g) a1             le ()
  upVal2 G M T (FunEl g')     (FunEl g) a1             le ()
  upVal2 G M T (PiCode a' f') (FunEl g) a1             le ()
  upVal2 G M T (SigmaCode a' f') (FunEl g) a1          le ()
  upVal2 G M T (PairCode u' v') (FunEl g) a1           le ()
  upVal2 G M T UCode          PropCode a1             le ()
  upVal2 G M T PropCode       PropCode a1             le ()
  upVal2 G M T (FunEl g)      PropCode a1             le ()
  upVal2 G M T (SigmaCode a' f') PropCode a1          le ()
  upVal2 G M T (PairCode u' v') PropCode a1           le ()
  upVal2 G M T Bot            PropCode Bot             ()
  upVal2 G M T Bot            PropCode UCode           ()
  upVal2 G M T Bot            PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T Bot            PropCode (FunEl h)       ()
  upVal2 G M T Bot            PropCode (PiCode b1 f1)  ()
  upVal2 G M T Bot            PropCode (SigmaCode b1 f1) ()
  upVal2 G M T Bot            PropCode (PairCode x y)  ()
  upVal2 G M T (PiCode a' f') PropCode Bot             ()
  upVal2 G M T (PiCode a' f') PropCode UCode           ()
  upVal2 G M T (PiCode a' f') PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T (PiCode a' f') PropCode (FunEl h)       ()
  upVal2 G M T (PiCode a' f') PropCode (PiCode b1 f1)  ()
  upVal2 G M T (PiCode a' f') PropCode (SigmaCode b1 f1) ()
  upVal2 G M T (PiCode a' f') PropCode (PairCode x y)  ()
  upVal2 G M T u (PiCode b0 f0) Bot       ()
  upVal2 G M T u (PiCode b0 f0) UCode     ()
  upVal2 G M T u (PiCode b0 f0) PropCode  ()
  upVal2 G M T u (PiCode b0 f0) (FunEl h) ()
  upVal2 G M T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upVal2 G M T u (PiCode b0 f0) (PairCode x y) ()
  upVal2 G M T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = snd src
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
        -- piEV1 from vta1 (RValTyPi G T b1 f1)
        uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vta1)
        piEV1 : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b1 f1
        piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
        vpi' = record
          { domA0 = RValPi.domA0 vpiM
          ; codB0 = RValPi.codB0 vpiM
          ; red   = RValPi.red vpiM
          ; cohG  = RValPi.cohG vpiM
          ; fmG   = fst mem1
          ; appV  = upPiAppVal2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (RValPi.appV vpiM)
          ; appE  = upPiAppEq2 G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b0 f0 b1 f1 g cf0 cf1 (RValPi.cohG vpiM) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (RValPi.appE vpiM)
          }
    in mkSigma vta1 vpi'
  upVal2 G M T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upVal2 G M T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode upVal2
  upVal2 G M T u (SigmaCode b0 f0) Bot       ()
  upVal2 G M T u (SigmaCode b0 f0) UCode     ()
  upVal2 G M T u (SigmaCode b0 f0) PropCode  ()
  upVal2 G M T u (SigmaCode b0 f0) (FunEl h) ()
  upVal2 G M T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  upVal2 G M T u (SigmaCode b0 f0) (PairCode x y) ()
  upVal2 G M T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upVal2 G M T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (PiCode a f)   (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (SigmaCode a f) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty   = fst src
        vpair = snd src
        cf0   = snd ca0
        cf1   = snd ca1
        pf0   = snd (snd mem0)
        pf1   = snd (snd mem1)
        b0U   = fst pf0
        b1U   = fst pf1
        cb0   = coh-from-aU b0 b0U
        cb1   = coh-from-aU b1 b1U
        fmu'0 = fst (fst mem0)
        fmu'1 = fst (fst mem1)
        uniq  = Red3-unique-Sigma (RValSigma.red vpair) (RValTySigma.red vta1)
        sigEV1 : SigmaEdgeVal2 G (RValSigma.domA vpair) (RValSigma.codB vpair) b1 f1
        sigEV1 = Eq-transport (\ Y -> SigmaEdgeVal2 G (RValSigma.domA vpair) Y b1 f1) (Eq-sym (snd uniq))
                   (Eq-transport (\ X -> SigmaEdgeVal2 G X (RValTySigma.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTySigma.edgeV vta1))
        ctf0  = snd ca0
        ctf1  = snd ca1
        le_ef = EvalFun-mon f0 f1 u' ctf0 ctf1 (RValSigma.cohW1 vpair) (snd le)
        ca0_ef = Coherent-EvalFun f0 u' ctf0 (RValSigma.cohW1 vpair)
        ca1_ef = Coherent-EvalFun f1 u' ctf1 (RValSigma.cohW1 vpair)
        ef1U  = EvalFun-in-UCode f1 u' b1 ctf1 (RValSigma.cohW1 vpair) (fst (snd pf1))
        v2Fst' = upVal2 G (Fst _) (RValSigma.domA vpair) u' b0 b1 (fst le) fmu'0 fmu'1 cb0 cb1 (RValSigma.valFst vpair)
                   (Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst uniq)) (RValTySigma.valA vta1))
        v2Snd' = upVal2 G (Snd _) (subst1 (RValSigma.codB vpair) (Fst _)) v' (EvalFun f0 u') (EvalFun f1 u')
                   le_ef (snd (fst mem0)) (snd (fst mem1)) ca0_ef ca1_ef (RValSigma.valSnd vpair)
                   (let sb = selectionBelow f1 u' ctf1 (RValSigma.cohW1 vpair)
                        u1 = fst sb
                        v1 = fst (snd sb)
                        sel1 = fst (snd (snd sb))
                        le-u1 = fst (snd (snd (snd sb)))
                        eq-v1 = snd (snd (snd (snd sb)))
                        fmu1-b1 = FinMemAllU-Selection b1 sel1 (fst (snd pf1)) ctf1 cb1 b1U
                        fmu-b1 = finMem-upward u' b0 b1 (fst le) cb0 cb1 fmu'0 b1U
                        valFst-u1 = restrictVal2 _ _ (RValSigma.domA vpair) u' u1 b1 le-u1 fmu1-b1 fmu-b1 v2Fst'
                        vty-v1 = sigEV1 u1 v1 sel1 (Fst _) (RValSigma.htFst vpair) valFst-u1
                    in Eq-transport (\ x -> ValTy2 G (subst1 (RValSigma.codB vpair) (Fst _)) x) (Eq-sym eq-v1) vty-v1)
        vpair' = record
          { domA   = RValSigma.domA vpair
          ; codB   = RValSigma.codB vpair
          ; red    = RValSigma.red vpair
          ; htFst  = RValSigma.htFst vpair
          ; cohW1   = RValSigma.cohW1 vpair
          ; fmW1    = fmu'1
          ; valFst = v2Fst'
          ; valSnd = v2Snd'
          }
    in mkSigma vta1 vpair'
  -- PairCode upVal2: FinMem Bot (PairCode x y) = Empty
  upVal2 G M T Bot (PairCode x0 y0) a1 le ()
  upVal2 G M T UCode (PairCode x0 y0) a1 le ()
  upVal2 G M T PropCode (PairCode x0 y0) a1 le ()
  upVal2 G M T (FunEl g) (PairCode x0 y0) a1 le ()
  upVal2 G M T (PiCode a f) (PairCode x0 y0) a1 le ()
  upVal2 G M T (SigmaCode a f) (PairCode x0 y0) a1 le ()
  upVal2 G M T (PairCode u' v') (PairCode x0 y0) a1 le ()

  upEqVal2 G M N T Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode        Bot a1 le ()
  upEqVal2 G M N T (FunEl g)    Bot a1 le ()
  upEqVal2 G M N T (PiCode a f) Bot a1 le ()
  upEqVal2 G M N T (SigmaCode a f) Bot a1 le ()
  upEqVal2 G M N T (PairCode u' v') Bot a1 le ()
  upEqVal2 G M N T PropCode     Bot a1 le ()
  upEqVal2 G M N T Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (FunEl g')     UCode UCode le ()
  upEqVal2 G M N T PropCode        UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PairCode u' v') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T u UCode Bot          ()
  upEqVal2 G M N T u UCode PropCode     ()
  upEqVal2 G M N T u UCode (FunEl h)    ()
  upEqVal2 G M N T u UCode (PiCode b h) ()
  upEqVal2 G M N T u UCode (SigmaCode b h) ()
  upEqVal2 G M N T u UCode (PairCode x y) ()
  upEqVal2 G M N T Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (FunEl g) a1             le ()
  upEqVal2 G M N T PropCode       (FunEl g) a1             le ()
  upEqVal2 G M N T (FunEl g')     (FunEl g) a1             le ()
  upEqVal2 G M N T (PiCode a' f') (FunEl g) a1             le ()
  upEqVal2 G M N T (SigmaCode a' f') (FunEl g) a1          le ()
  upEqVal2 G M N T (PairCode u' v') (FunEl g) a1           le ()
  upEqVal2 G M N T UCode          PropCode a1             le ()
  upEqVal2 G M N T PropCode       PropCode a1             le ()
  upEqVal2 G M N T (FunEl g)      PropCode a1             le ()
  upEqVal2 G M N T (SigmaCode a' f') PropCode a1          le ()
  upEqVal2 G M N T (PairCode u' v') PropCode a1           le ()
  upEqVal2 G M N T Bot            PropCode Bot             ()
  upEqVal2 G M N T Bot            PropCode UCode           ()
  upEqVal2 G M N T Bot            PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T Bot            PropCode (FunEl h)       ()
  upEqVal2 G M N T Bot            PropCode (PiCode b1 f1)  ()
  upEqVal2 G M N T Bot            PropCode (SigmaCode b1 f1) ()
  upEqVal2 G M N T Bot            PropCode (PairCode x y)  ()
  upEqVal2 G M N T (PiCode a' f') PropCode Bot             ()
  upEqVal2 G M N T (PiCode a' f') PropCode UCode           ()
  upEqVal2 G M N T (PiCode a' f') PropCode PropCode        le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T (PiCode a' f') PropCode (FunEl h)       ()
  upEqVal2 G M N T (PiCode a' f') PropCode (PiCode b1 f1)  ()
  upEqVal2 G M N T (PiCode a' f') PropCode (SigmaCode b1 f1) ()
  upEqVal2 G M N T (PiCode a' f') PropCode (PairCode x y)  ()
  upEqVal2 G M N T u (PiCode b0 f0) Bot       ()
  upEqVal2 G M N T u (PiCode b0 f0) UCode     ()
  upEqVal2 G M N T u (PiCode b0 f0) PropCode  ()
  upEqVal2 G M N T u (PiCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T u (PiCode b0 f0) (SigmaCode b1 f1) ()
  upEqVal2 G M N T u (PiCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T PropCode       (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vty  = fst src
        vpiM = fst (snd src)
        vpiN = fst (snd (snd src))
        epi  = snd (snd (snd src))
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
        uniq  = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vta1)
        piEV1 : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b1 f1
        piEV1 = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b1 f1) (Eq-sym (snd uniq))
                  (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vta1) b1 f1) (Eq-sym (fst uniq)) (RValTyPi.edgeV vta1))
        valM   = mkSigma vty vpiM
        valN   = mkSigma vty vpiN
        valM'  = upVal2 G M T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
        valN'  = upVal2 G N T (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
        epi'   = record
          { domA0 = REqValPi.domA0 epi
          ; codB0 = REqValPi.codB0 epi
          ; red   = REqValPi.red epi
          ; cohG  = REqValPi.cohG epi
          ; fmG   = fst mem1
          ; appEV = upPiAppEqVal2 G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b0 f0 b1 f1 g cf0 cf1 (REqValPi.cohG epi) cb0 cb1 b1U allU1 b0U allU0 le
                      (fst mem0) piEV1 (REqValPi.appEV epi)
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
  upEqVal2 G M N T (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (SigmaCode a f) (PiCode b0 f0) (PiCode b1 f1) le ()
  upEqVal2 G M N T (PairCode u' v') (PiCode b0 f0) (PiCode b1 f1) le ()
  -- SigmaCode upEqVal2
  upEqVal2 G M N T u (SigmaCode b0 f0) Bot       ()
  upEqVal2 G M N T u (SigmaCode b0 f0) UCode     ()
  upEqVal2 G M N T u (SigmaCode b0 f0) PropCode  ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (FunEl h) ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (PiCode b1 f1) ()
  upEqVal2 G M N T u (SigmaCode b0 f0) (PairCode x y) ()
  upEqVal2 G M N T Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = src
  upEqVal2 G M N T UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (PiCode a f)   (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (SigmaCode a f) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
  upEqVal2 G M N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
    let vpairM = fst (snd src)
        vpairN = fst (snd (snd src))
        eqp    = snd (snd (snd src))
        fmu'0  = fst (fst mem0)
        fmu'1  = fst (fst mem1)
        valM   = mkSigma (fst src) vpairM
        valN   = mkSigma (fst src) vpairN
        valM'  = upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
        valN'  = upVal2 G N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
        -- Compute upVal2 separately for REqValPair M-fields
        vpairM-eq : RValSigma G M T (PairCode u' v') b0 f0
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq' = upVal2 G M T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 (mkSigma (fst src) vpairM-eq) vta1
        vpairN-eq : RValSigma G N T (PairCode u' v') b0 f0
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq' = upVal2 G N T (PairCode u' v') (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 (mkSigma (fst src) vpairN-eq) vta1
        eqFst' = upEqVal2 G (Fst M) (Fst N) (REqValSigma.domA eqp) u' b0 b1 (fst le) fmu'0 fmu'1 (fst ca0) (fst ca1) (REqValSigma.eqFst eqp)
                   (Eq-transport (\ X -> ValTy2 G X b1) (Eq-sym (fst (Red3-unique-Sigma (REqValSigma.red eqp) (RValTySigma.red vta1))))
                      (RValTySigma.valA vta1))
        eqp'   = record
          { domA    = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM  = RValSigma.htFst (snd valM-eq')
          ; cohW1    = REqValSigma.cohW1 eqp
          ; fmW1     = fmu'1
          ; valFstM = RValSigma.valFst (snd valM-eq')
          ; valSndM = RValSigma.valSnd (snd valM-eq')
          ; htFstN  = RValSigma.htFst (snd valN-eq')
          ; valFstN = RValSigma.valFst (snd valN-eq')
          ; valSndN = RValSigma.valSnd (snd valN-eq')
          ; eqFst   = eqFst'
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') eqp'))
  -- PairCode upEqVal2
  upEqVal2 G M N T Bot (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T UCode (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T PropCode (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (FunEl g) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (PiCode a f) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (SigmaCode a f) (PairCode x0 y0) a1 le ()
  upEqVal2 G M N T (PairCode u' v') (PairCode x0 y0) a1 le ()

  ------------------------------------------------------------------
  -- downPiAppVal2 / downPiAppEq2 / downPiAppEqVal2
  ------------------------------------------------------------------

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

  ------------------------------------------------------------------
  -- upPiAppVal2 / upPiAppEq2 / upPiAppEqVal2
  ------------------------------------------------------------------

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
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-v1) vty-v1
        in upVal2 _ _ (subst1 B0 N) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

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
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 N1) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

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
            vty-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-v1) vty-v1
        in upEqVal2 _ _ _ (subst1 B0 P) v (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0
             (finMem-upward v (EvalFun f0 u) (EvalFun f1 u) le-f c-ef0 c-ef1 fmem-v-f0 ef1U)
             c-ef0 c-ef1 body vty-ef1

  ------------------------------------------------------------------
  -- transportPiEdgeVal2-sel / transportPiEdgeEq2-sel / transportPiEdgeEqTy2-sel
  ------------------------------------------------------------------

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
            vt-ef   = Eq-transport (\ x -> ValTy2 G (subst1 B N) x) (Eq-sym eq-v1) vt-v1
            le-v-ef = Selection-le-EvalFun f1 sel lef cf0 cf1 cu
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
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
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
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
            le-v-v1 = Eq-transport (LeCode v) eq-v1 le-v-ef
            fmem-v-U = FinMem-Selection-UCode b0 sel allU0 cf0
            v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1
                    (EvalFun-in-UCode f1 u b1 cf1 cu allU1)
        in downEqValTy2 G (subst1 B P) (subst1 B' P) v v1 le-v-v1 fmem-v-U v1U eqt-v1

  ------------------------------------------------------------------
  -- restrictPiAppVal2-sel / restrictPiAppEq2-sel / restrictPiAppEqVal2-sel
  ------------------------------------------------------------------

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
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 N) x) (Eq-sym eq-ef) vty-vf
        body2    = upVal2 _ _ (subst1 B0 N) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
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
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 N1) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 N1) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
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
        vty-efu' = Eq-transport (\ x -> ValTy2 G (subst1 B0 P) x) (Eq-sym eq-ef) vty-vf
        body2    = upEqVal2 _ _ _ (subst1 B0 P) v_g (EvalFun f u_g) (EvalFun f u') le-ef
                     fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
        le-v'-efgu' = Selection-le-EvalFun g sel' le ctg' ctg cu'
        le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
        fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' ctg' cf allU
    in restrictEqVal2 _ _ _ (subst1 B0 P) v_g v' (EvalFun f u')
         le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

  ------------------------------------------------------------------
  -- restrictVal2-PiCode / restrictEqVal2-PiCode
  ------------------------------------------------------------------

  restrictVal2-PiCode : {n : Nat} (G : Ctx n) (M T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    RValPi G M T g b f ->
    RValPi G M T g' b f
  restrictVal2-PiCode G M T g g' b f cf cb allU bU le mem' vtyT vpiM =
    let cg'  = snd mem'
        fmg' = fst mem'
        -- Derive PiEdgeVal2 from vtyT (RValTyPi)
        uniq = Red3-unique-Pi (RValPi.red vpiM) (RValTyPi.red vtyT)
        piEV : PiEdgeVal2 G (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (RValPi.domA0 vpiM) Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
    in record
      { domA0 = RValPi.domA0 vpiM
      ; codB0 = RValPi.codB0 vpiM
      ; red   = RValPi.red vpiM
      ; cohG  = cg'
      ; fmG   = fmg'
      ; appV  = restrictPiAppVal2-sel G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                  bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appV vpiM)
      ; appE  = restrictPiAppEq2-sel G M (RValPi.domA0 vpiM) (RValPi.codB0 vpiM) b f g g' cf (RValPi.cohG vpiM) cg' cb allU
                  bU le fmg' (RValPi.fmG vpiM) piEV (RValPi.appE vpiM)
      }

  restrictEqVal2-PiCode : {n : Nat} (G : Ctx n) (M N T : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g ->
    Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTy2 G T (PiCode b f) ->
    REqValPi G M N T g b f ->
    REqValPi G M N T g' b f
  restrictEqVal2-PiCode G M N T g g' b f cf cb allU bU le mem' vtyT epi =
    let cg'  = snd mem'
        fmg' = fst mem'
        -- Derive PiEdgeVal2 from vtyT (RValTyPi)
        uniq = Red3-unique-Pi (REqValPi.red epi) (RValTyPi.red vtyT)
        piEV : PiEdgeVal2 G (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f
        piEV = Eq-transport (\ Y -> PiEdgeVal2 G (REqValPi.domA0 epi) Y b f) (Eq-sym (snd uniq))
                 (Eq-transport (\ X -> PiEdgeVal2 G X (RValTyPi.codB vtyT) b f) (Eq-sym (fst uniq)) (RValTyPi.edgeV vtyT))
    in record
      { domA0 = REqValPi.domA0 epi
      ; codB0 = REqValPi.codB0 epi
      ; red   = REqValPi.red epi
      ; cohG  = cg'
      ; fmG   = fmg'
      ; appEV = restrictPiAppEqVal2-sel G M N (REqValPi.domA0 epi) (REqValPi.codB0 epi) b f g g' cf (REqValPi.cohG epi) cg' cb allU
                  bU le fmg' (REqValPi.fmG epi) piEV (REqValPi.appEV epi)
      }

  ------------------------------------------------------------------
  -- Val2-EqValTy2-fwd
  ------------------------------------------------------------------

  -- Leaf cases: Val2 = Top on both sides, return tt
  Val2-EqValTy2-fwd Bot Bot cb eqv val = tt
  Val2-EqValTy2-fwd UCode Bot cb eqv val = tt
  Val2-EqValTy2-fwd PropCode Bot cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) Bot cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') Bot cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' f') Bot cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') Bot cb eqv val = tt
  Val2-EqValTy2-fwd Bot UCode cb eqv val = tt
  Val2-EqValTy2-fwd PropCode UCode cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') UCode cb eqv val = tt
  Val2-EqValTy2-fwd Bot PropCode cb eqv val = tt
  Val2-EqValTy2-fwd UCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd PropCode PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv val = val
  Val2-EqValTy2-fwd (SigmaCode a' f') PropCode cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') PropCode cb eqv val = tt
  Val2-EqValTy2-fwd Bot (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' f') (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (FunEl h) cb eqv val = tt
  Val2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv val = tt
  -- UCode cases: Val2 = ValTy2 G M u, does not depend on C, return val unchanged
  Val2-EqValTy2-fwd UCode UCode cb eqv val = val
  Val2-EqValTy2-fwd (FunEl g) UCode cb eqv val = val
  Val2-EqValTy2-fwd (PiCode a' f') UCode cb eqv val = val
  Val2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv val = val
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        convEE' = REqValTyPi.convA core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        -- htE : HasType G E U from vtyC
        redCv = RValTyPi.red vtyC
        htAc  = RValTyPi.htA vtyC
        uniqC2 = Red3-unique-Pi redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        -- Extract from val : Val2 G M C (FunEl g) (PiCode b0 f0)
        vpiM = snd val
        A0   = RValPi.domA0 vpiM
        B0   = RValPi.codB0 vpiM
        redC = RValPi.red vpiM
        cg   = RValPi.cohG vpiM
        fmg  = RValPi.fmG vpiM
        pav  = RValPi.appV vpiM
        pae  = RValPi.appE vpiM
        uniq = Red3-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        pav-EF : PiAppVal2 _ _ E F b0 f0 g
        pav-EF = Eq-transport (\ X -> PiAppVal2 _ _ X F b0 f0 g) eqA0E
                   (Eq-transport (\ Y -> PiAppVal2 _ _ A0 Y b0 f0 g) eqB0F pav)
        pae-EF : PiAppEq2 _ _ E F b0 f0 g
        pae-EF = Eq-transport (\ X -> PiAppEq2 _ _ X F b0 f0 g) eqA0E
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
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N) (subst1 F' N) w)
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
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F N1) (subst1 F' N1) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        vpi' = record
          { domA0 = E' ; codB0 = F' ; red = rC'
          ; cohG = cg ; fmG = fmg
          ; appV = pav-E'F' ; appE = pae-E'F'
          }
    in mkSigma vtyC' vpi'
  -- SigmaCode cases for Val2-EqValTy2-fwd
  Val2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma UCode b0 f0 cb eqv val
  Val2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma PropCode b0 f0 cb eqv val
  Val2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma (FunEl g) b0 f0 cb eqv val
  Val2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma (PiCode a' ff) b0 f0 cb eqv val
  Val2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma (SigmaCode a' ff) b0 f0 cb eqv val
  Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv val = Val2-EqValTy2-fwd-Sigma (PairCode u' v') b0 f0 cb eqv val
  Val2-EqValTy2-fwd Bot (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd UCode (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd PropCode (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd (FunEl g) (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd (PiCode a' f') (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd (SigmaCode a' f') (PairCode x y) cb eqv val = tt
  Val2-EqValTy2-fwd (PairCode u' v') (PairCode x y) cb eqv val = tt

  ------------------------------------------------------------------
  -- Val2-EqValTy2-fwd-Sigma / EqVal2-EqValTy2-fwd-Sigma
  ------------------------------------------------------------------

  Val2-EqValTy2-fwd-Sigma w b0 f0 cb eqv val =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTySigma.domA core
        F     = REqValTySigma.codB core
        E'    = REqValTySigma.domA' core
        F'    = REqValTySigma.codB' core
        rC    = REqValTySigma.redM core
        rC'   = REqValTySigma.redN core
        cf0   = REqValTySigma.cohF core
        fmU   = REqValTySigma.fmAllU core
        convEE' = REqValTySigma.convA core
        eqE   = REqValTySigma.eqA core
        vpair = snd val
        redC  = RValSigma.red vpair
        uniq  = Red3-unique-Sigma redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        redCv = RValTySigma.red vtyC
        htAc  = RValTySigma.htA vtyC
        uniqC2 = Red3-unique-Sigma redCv rC
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2) htAc
        cb0   = fst cb
        valFst-E = RValSigma.valFst vpair
        valFst-E' = Eq-transport (\ X -> Val2 _ _ X (codeFst w) b0) eqA0E valFst-E
        valFst-E'2 = Val2-EqValTy2-fwd (codeFst w) b0 cb0 eqE valFst-E'
        redC'v = RValTySigma.red vtyC'
        htAc'  = RValTySigma.htA vtyC'
        uniqC2' = Red3-unique-Sigma redC'v rC'
        htE'   = Eq-transport (\ X -> HasType _ X _) (fst uniqC2') htAc'
        htFst-E = RValSigma.htFst vpair
        htFst-E' = Eq-transport (\ X -> HasType _ _ X) eqA0E htFst-E
        htFst-E'2 = ty-conv htFst-E' convEE' htE'
        vpair' = record
          { domA   = E' ; codB = F'
          ; red    = rC'
          ; htFst  = htFst-E'2
          ; cohW1  = RValSigma.cohW1 vpair
          ; fmW1   = RValSigma.fmW1 vpair
          ; valFst = valFst-E'2
          ; valSnd = let valSnd-F = RValSigma.valSnd vpair
                         valSnd-F' = Eq-transport (\ X -> Val2 _ _ (subst1 X _) (codeSnd w) (EvalFun f0 (codeFst w))) eqB0F valSnd-F
                         pet = REqValTySigma.edgeET core
                         cw1 = RValSigma.cohW1 vpair
                         sb  = selectionBelow f0 (codeFst w) cf0 cw1
                         u-f = fst sb
                         v-f = fst (snd sb)
                         sel-f = fst (snd (snd sb))
                         le-uf = fst (snd (snd (snd sb)))
                         eq-ef = snd (snd (snd (snd sb)))
                         b0U = RValTySigma.fmBU vtyC
                         fmu-f = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
                         valFst-uf = restrictVal2 _ _ E (codeFst w) u-f b0 le-uf fmu-f (RValSigma.fmW1 vpair) valFst-E'
                         eqt-vf = pet u-f v-f sel-f (Fst _) htFst-E' valFst-uf
                         eqt-ef = Eq-transport (\ z -> EqValTy2 _ (subst1 F (Fst _)) (subst1 F' (Fst _)) z)
                                    (Eq-sym eq-ef) eqt-vf
                         cev = Coherent-EvalFun f0 (codeFst w) cf0 cw1
                     in Val2-EqValTy2-fwd (codeSnd w) (EvalFun f0 (codeFst w)) cev eqt-ef valSnd-F'
          }
    in mkSigma vtyC' vpair'

  EqVal2-EqValTy2-fwd-Sigma w b0 f0 cb eqv ev =
    let valM-C  = Val2-from-EqVal2-first w (SigmaCode b0 f0) ev
        valN-C  = Val2-from-EqVal2-second w (SigmaCode b0 f0) ev
        valM-C' = Val2-EqValTy2-fwd-Sigma w b0 f0 cb eqv valM-C
        valN-C' = Val2-EqValTy2-fwd-Sigma w b0 f0 cb eqv valN-C
        eqp    = snd (snd (snd ev))
        core   = snd (snd eqv)
        uniqE  = Red3-unique-Sigma (REqValSigma.red eqp) (REqValTySigma.redM core)
        eqFst' = EqVal2-EqValTy2-fwd (codeFst w) b0 (fst cb) (REqValTySigma.eqA core)
                   (Eq-transport (\ X -> EqVal2 _ (Fst _) (Fst _) X (codeFst w) b0) (fst uniqE)
                     (REqValSigma.eqFst eqp))
        vtyC  = fst eqv
        htAc  = RValTySigma.htA vtyC
        uniqC = Red3-unique-Sigma (RValTySigma.red vtyC) (REqValTySigma.redM core)
        htE   = Eq-transport (\ X -> HasType _ X _) (fst uniqC) htAc
        vtyC' = fst (snd eqv)
        htAc' = RValTySigma.htA vtyC'
        uniqC' = Red3-unique-Sigma (RValTySigma.red vtyC') (REqValTySigma.redN core)
        htE'  = Eq-transport (\ X -> HasType _ X _) (fst uniqC') htAc'
        htFstM-E = Eq-transport (\ X -> HasType _ _ X) (fst uniqE) (REqValSigma.htFstM eqp)
        htFstM-E' = ty-conv htFstM-E (REqValTySigma.convA core) htE'
        htFstN-E = Eq-transport (\ X -> HasType _ _ X) (fst uniqE) (REqValSigma.htFstN eqp)
        htFstN-E' = ty-conv htFstN-E (REqValTySigma.convA core) htE'
        -- Compute Val2-EqValTy2-fwd separately for REqValSigma M/N fields
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq-C' = Val2-EqValTy2-fwd-Sigma w b0 f0 cb eqv (mkSigma (fst ev) vpairM-eq)
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq-C' = Val2-EqValTy2-fwd-Sigma w b0 f0 cb eqv (mkSigma (fst ev) vpairN-eq)
        eqp'   = record
          { domA    = REqValTySigma.domA' core ; codB = REqValTySigma.codB' core
          ; red     = REqValTySigma.redN core
          ; htFstM  = RValSigma.htFst (snd valM-eq-C')
          ; cohW1   = REqValSigma.cohW1 eqp
          ; fmW1    = REqValSigma.fmW1 eqp
          ; valFstM = RValSigma.valFst (snd valM-eq-C')
          ; valSndM = RValSigma.valSnd (snd valM-eq-C')
          ; htFstN  = RValSigma.htFst (snd valN-eq-C')
          ; valFstN = RValSigma.valFst (snd valN-eq-C')
          ; valSndN = RValSigma.valSnd (snd valN-eq-C')
          ; eqFst   = eqFst'
          }
    in mkSigma (fst valM-C') (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqp'))

  ------------------------------------------------------------------
  -- EqVal2-EqValTy2-fwd
  ------------------------------------------------------------------

  -- Leaf cases: EqVal2 = Top on both sides, return tt
  EqVal2-EqValTy2-fwd Bot Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl g) Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' f') Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' f') Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') Bot cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') UCode cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd UCode PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd PropCode PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (FunEl g) PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PiCode a' f') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (SigmaCode a' f') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PairCode u' v') PropCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd Bot (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl g) (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' f') (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' f') (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (FunEl h) cb eqv ev = tt
  EqVal2-EqValTy2-fwd Bot (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (PiCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (PiCode b0 f0) cb eqv ev = tt
  -- UCode cases: does not depend on C, return ev unchanged
  EqVal2-EqValTy2-fwd UCode UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (FunEl g) UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (PiCode a' f') UCode cb eqv ev = ev
  EqVal2-EqValTy2-fwd (SigmaCode a' f') UCode cb eqv ev = ev
  -- Non-trivial case: (FunEl g, PiCode b0 f0)
  EqVal2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv ev =
    let vtyC  = fst eqv
        vtyC' = fst (snd eqv)
        core  = snd (snd eqv)
        E     = REqValTyPi.domA core
        F     = REqValTyPi.codB core
        E'    = REqValTyPi.domA' core
        F'    = REqValTyPi.codB' core
        rC    = REqValTyPi.redM core
        rC'   = REqValTyPi.redN core
        cf0   = REqValTyPi.cohF core
        fmU   = REqValTyPi.fmAllU core
        convEE'-eq = REqValTyPi.convA core
        eqE   = REqValTyPi.eqA core
        pet   = REqValTyPi.edgeET core
        -- htE : HasType G E U from vtyC
        redCv-eq = RValTyPi.red vtyC
        htAc-eq = RValTyPi.htA vtyC
        uniqC2-eq = Red3-unique-Pi redCv-eq rC
        htE-eq  = Eq-transport (\ X -> HasType _ X _) (fst uniqC2-eq) htAc-eq
        -- ev : EqVal2 G M N C (FunEl g) (PiCode b0 f0)
        vtyC-ev = fst ev
        vpiM = fst (snd ev)
        vpiN = fst (snd (snd ev))
        epi  = snd (snd (snd ev))
        A0    = REqValPi.domA0 epi
        B0    = REqValPi.codB0 epi
        redC  = REqValPi.red epi
        cg    = REqValPi.cohG epi
        fmg   = REqValPi.fmG epi
        paev  = REqValPi.appEV epi
        uniq = Red3-unique-Pi redC rC
        eqA0E = fst uniq
        eqB0F = snd uniq
        cb0 = fst cb
        b0U = bU-from-cf-fmFun g b0 f0 cg fmg
        paev-EF : PiAppEqVal2 _ _ _ E F b0 f0 g
        paev-EF = Eq-transport (\ X -> PiAppEqVal2 _ _ _ X F b0 f0 g) eqA0E
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
              eqt-ef = Eq-transport (\ w -> EqValTy2 _ (subst1 F P) (subst1 F' P) w)
                         (Eq-sym eq-ef) eqt-vf
              cev    = Coherent-EvalFun f0 u' cf0 cu'
          in EqVal2-EqValTy2-fwd v' (EvalFun f0 u') cev eqt-ef body
        -- Build Val2 G M C' and Val2 G N C'
        valM-C  = Val2-from-EqVal2-first (FunEl g) (PiCode b0 f0) ev
        valN-C  = Val2-from-EqVal2-second (FunEl g) (PiCode b0 f0) ev
        valM-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valM-C
        valN-C' = Val2-EqValTy2-fwd (FunEl g) (PiCode b0 f0) cb eqv valN-C
        eqvpi-C' = record
          { domA0 = E' ; codB0 = F' ; red = rC'
          ; cohG = cg ; fmG = fmg ; appEV = paev-E'F'
          }
    in mkSigma vtyC' (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqvpi-C'))
  -- SigmaCode EqVal2-EqValTy2-fwd
  EqVal2-EqValTy2-fwd Bot (SigmaCode b0 f0) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma UCode b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd PropCode (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma PropCode b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd (FunEl g) (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma (FunEl g) b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd (PiCode a' ff) (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma (PiCode a' ff) b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd (SigmaCode a' ff) (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma (SigmaCode a' ff) b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd (PairCode u' v') (SigmaCode b0 f0) cb eqv ev = EqVal2-EqValTy2-fwd-Sigma (PairCode u' v') b0 f0 cb eqv ev
  EqVal2-EqValTy2-fwd Bot (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd UCode (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd PropCode (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (FunEl g) (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PiCode a' f') (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (SigmaCode a' f') (PairCode x y) cb eqv ev = tt
  EqVal2-EqValTy2-fwd (PairCode u' v') (PairCode x y) cb eqv ev = tt

  ------------------------------------------------------------------
  -- restrictVal2 / restrictEqVal2
  ------------------------------------------------------------------

  restrictVal2 G M T Bot u' Bot          le mem fmu src = src
  restrictVal2 G M T UCode u' Bot          le mem fmu src = src
  restrictVal2 G M T PropCode u' Bot          le mem fmu src = src
  restrictVal2 G M T (FunEl g) u' Bot          le mem fmu src = src
  restrictVal2 G M T (PiCode a' f') u' Bot          le mem fmu src = src
  restrictVal2 G M T (SigmaCode a' f') u' Bot          le mem fmu src = src
  restrictVal2 G M T (PairCode x y) u' Bot          le mem fmu src = src
  restrictVal2 G M T Bot Bot UCode        le mem fmu src = src
  restrictVal2 G M T Bot UCode UCode      ()
  restrictVal2 G M T Bot (FunEl _) UCode  ()
  restrictVal2 G M T Bot (PiCode _ _) UCode ()
  restrictVal2 G M T UCode Bot UCode        le mem fmu src = tt
  restrictVal2 G M T UCode UCode UCode      le mem fmu src = src
  restrictVal2 G M T UCode (FunEl _) UCode  ()
  restrictVal2 G M T UCode (PiCode _ _) UCode ()
  restrictVal2 G M T (FunEl g) Bot UCode    le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode UCode  ()
  restrictVal2 G M T (FunEl g) (FunEl g') UCode le mem fmu src =
    downValTy2 G M (FunEl g') (FunEl g) le mem fmu src
  restrictVal2 G M T (FunEl g) (PiCode _ _) UCode ()
  restrictVal2 G M T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a' f') UCode UCode ()
  restrictVal2 G M T (PiCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu src =
    downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu src
  restrictVal2 G M T PropCode Bot UCode le mem fmu src = tt
  restrictVal2 G M T PropCode UCode UCode ()
  restrictVal2 G M T PropCode PropCode UCode le mem fmu src = src
  restrictVal2 G M T PropCode (FunEl _) UCode ()
  restrictVal2 G M T PropCode (PiCode _ _) UCode ()
  restrictVal2 G M T Bot PropCode UCode ()
  restrictVal2 G M T UCode PropCode UCode ()
  restrictVal2 G M T (FunEl g) PropCode UCode ()
  restrictVal2 G M T (PiCode a' f') PropCode UCode ()
  restrictVal2 G M T Bot Bot PropCode le mem fmu src = src
  restrictVal2 G M T Bot UCode PropCode le ()
  restrictVal2 G M T Bot PropCode PropCode ()
  restrictVal2 G M T Bot (FunEl _) PropCode le ()
  restrictVal2 G M T Bot (PiCode _ _) PropCode ()
  restrictVal2 G M T UCode u' PropCode le mem ()
  restrictVal2 G M T PropCode u' PropCode le mem ()
  restrictVal2 G M T (FunEl _) u' PropCode le mem ()
  restrictVal2 G M T (PiCode a' f') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PiCode a' f') UCode PropCode le ()
  restrictVal2 G M T (PiCode a' f') PropCode PropCode ()
  restrictVal2 G M T (PiCode a' f') (FunEl _) PropCode le ()
  restrictVal2 G M T (PiCode a' f') (PiCode a2 f2) PropCode le mem fmu src =
    downValTy2 G M (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) src
  restrictVal2 G M T Bot u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T UCode u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T PropCode u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T (FunEl g) u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T (PiCode a' f') u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T (SigmaCode a' f') u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T (PairCode x y) u' (FunEl h)    le mem fmu src = src
  restrictVal2 G M T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T Bot UCode          (PiCode b f) le ()
  restrictVal2 G M T Bot (FunEl g')     (PiCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictVal2 G M T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T UCode (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode          (PiCode b f) le ()
  restrictVal2 G M T (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
    let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
    in mkSigma (fst src)
         (restrictVal2-PiCode G M T g g' b f (snd (snd aU)) (coh-from-aU b (fst aU))
           (fst (snd aU)) (fst aU) le (mkSigma (fst mem) (fst (snd mem))) (fst src) (snd src))
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictVal2 G M T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictVal2 G M T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  -- SigmaCode restrictVal2
  restrictVal2 G M T Bot PropCode (SigmaCode b f) ()
  restrictVal2 G M T UCode PropCode (SigmaCode b f) ()
  restrictVal2 G M T (FunEl g) PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PiCode a' f') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a' f') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (PairCode u' v') PropCode (SigmaCode b f) ()
  restrictVal2 G M T (SigmaCode a' f') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a' f') UCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') (FunEl _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (PiCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') (SigmaCode a2 f2) UCode le mem fmu src =
    downValTy2 G M (SigmaCode a2 f2) (SigmaCode a' f') le mem fmu src
  restrictVal2 G M T (SigmaCode a' f') (PairCode _ _) UCode ()
  restrictVal2 G M T (SigmaCode a' f') PropCode UCode ()
  restrictVal2 G M T (SigmaCode a' f') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (SigmaCode a' f') UCode PropCode le ()
  restrictVal2 G M T (SigmaCode a' f') PropCode PropCode ()
  restrictVal2 G M T (SigmaCode a' f') (FunEl _) PropCode le ()
  restrictVal2 G M T (SigmaCode a' f') (PiCode a2 f2) PropCode le mem ()
  restrictVal2 G M T (SigmaCode a' f') (SigmaCode a2 f2) PropCode le mem ()
  restrictVal2 G M T (SigmaCode a' f') (PairCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode UCode ()
  restrictVal2 G M T (PairCode u' v') (FunEl _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PiCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictVal2 G M T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictVal2 G M T (PairCode u' v') PropCode UCode ()
  restrictVal2 G M T (PairCode u' v') Bot PropCode le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode PropCode le ()
  restrictVal2 G M T (PairCode u' v') PropCode PropCode ()
  restrictVal2 G M T (PairCode u' v') (FunEl _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (PiCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode _ _) PropCode ()
  restrictVal2 G M T (PairCode u' v') (PairCode _ _) PropCode le mem ()
  restrictVal2 G M T Bot Bot (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T Bot UCode (SigmaCode b f) le ()
  restrictVal2 G M T Bot (FunEl g') (SigmaCode b f) ()
  restrictVal2 G M T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictVal2 G M T UCode Bot (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T UCode UCode (SigmaCode b f) le mem fmu src = src
  restrictVal2 G M T UCode (FunEl g') (SigmaCode b f) le mem ()
  restrictVal2 G M T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T UCode (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T UCode (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictVal2 G M T PropCode u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (FunEl g) Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T (FunEl g) UCode (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (FunEl g') (SigmaCode b f) le mem ()
  restrictVal2 G M T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (FunEl g) (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictVal2 G M T (PiCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictVal2 G M T (PairCode u' v') Bot (SigmaCode b f) le mem fmu src = tt
  restrictVal2 G M T (PairCode u' v') UCode (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (FunEl g') (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (PiCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let fmu2b = fst (fst mem)
        vpair = snd src
        cfSrc = RValTySigma.cohF (fst src)
        allU  = RValTySigma.fmAllU (fst src)
        cu2   = FinMem-Coherent u2 b fmu2b
        cu'   = RValSigma.cohW1 vpair
        -- Restrict Fst: u' -> u2 at b
        v2Fst' = restrictVal2 _ _ (RValSigma.domA vpair) u' u2 b (fst le) fmu2b (RValSigma.fmW1 vpair) (RValSigma.valFst vpair)
        -- For Snd: down from (EvalFun f u') to (EvalFun f u2) via downVal2 + restrict v' -> v2
        -- Need FinMem v2 (EvalFun f u2) from mem, and need FinMem v' (EvalFun f u2) which we
        -- get from the Sigma FinMem structure: snd (snd mem) gives FinMem (SigmaCode b f) UCode
        -- and fst (snd mem) gives Coherent (PairCode u2 v2).
        -- Actually FinMem (PairCode u2 v2) (SigmaCode b f) already gives us
        -- snd (fst mem) : FinMem v2 (EvalFun f u2)
        fmv2ef2 = snd (fst mem)
        -- For restrictVal2 on Snd, we also need FinMem v' (EvalFun f u2).
        -- We get it from: fst (snd fmu) gives Coherent (PairCode u' v'), and
        -- snd (snd fmu) gives FinMem (SigmaCode b f) UCode
        -- The Sigma FinMem aU = snd (snd fmu) : FinMem (SigmaCode b f) UCode
        -- gives us: fst aU = FinMem b UCode, fst (snd aU) = FinMemAllU f b, snd (snd aU) = CoherentFun f
        aU = snd (snd fmu)
        bU = fst aU
        -- EvalFun-FinMem would give us FinMem (EvalFun g u2) (EvalFun f u2) if we had g
        -- But we need FinMem v' (EvalFun f u2). We only have FinMem v' (EvalFun f u')
        -- The simplest correct approach: use the edge from RValTySigma.
        -- sigmaEdgeVal gives ValTy2 at EvalFun f u2. Then downVal2 from (EvalFun f u') to (EvalFun f u2).
        -- But downVal2 needs FinMem v' (EvalFun f u2) as precondition...
        -- Alternative: since fmu : FinMem (PairCode u' v') (SigmaCode b f),
        -- fst (fst fmu) : FinMem u' b, snd (fst fmu) : FinMem v' (EvalFun f u')
        -- and snd (snd fmu) : FinMem (SigmaCode b f) UCode which gives FinMemAllU f b.
        -- Using FinMem-Selection or selectionBelow, we can find a selection entry.
        -- For now, use upVal2 to go from (EvalFun f u2) to (EvalFun f u') and restrictVal2 there.
        -- Actually, the correct approach for (PairCode, PairCode, SigmaCode) restrict:
        -- Go UP from ef u2 to ef u' (upVal2), restrict v' to v2 there, then DOWN from ef u' to ef u2.
        -- upVal2 needs ValTy2 at ef u' which comes from the Sigma edge.
        le_ef = EvalFun-mon-arg f u2 u' (fst le) cfSrc cu2 cu'
        c_ef_u2 = Coherent-EvalFun f u2 cfSrc cu2
        c_ef_u' = Coherent-EvalFun f u' cfSrc cu'
        ef_u'_U = EvalFun-in-UCode f u' b cfSrc cu' allU
        ef_u2_U = EvalFun-in-UCode f u2 b cfSrc cu2 allU
        fmv'efu' = snd (fst fmu)
        fmv2efu2 = fmv2ef2
        -- Step 1: upVal2 Snd from EvalFun f u2 to EvalFun f u' (need ValTy2 at ef u')
        fmv2efu' = finMem-upward v2 (EvalFun f u2) (EvalFun f u') le_ef c_ef_u2 c_ef_u' fmv2efu2 ef_u'_U
        -- Get ValTy2 at ef u' from the Sigma edge
        sb = selectionBelow f u' cfSrc cu'
        u1 = fst sb
        v1 = fst (snd sb)
        sel1 = fst (snd (snd sb))
        le-u1 = fst (snd (snd (snd sb)))
        eq-v1 = snd (snd (snd (snd sb)))
        fmu1-b = FinMemAllU-Selection b sel1 allU cfSrc (coh-from-aU b bU) bU
        uniqS = Red3-unique-Sigma (RValSigma.red vpair) (RValTySigma.red (fst src))
        eqAS = fst uniqS
        valFst-u1 = restrictVal2 _ _ (RValSigma.domA vpair) u' u1 b le-u1 fmu1-b (RValSigma.fmW1 vpair) (RValSigma.valFst vpair)
        htFst-S = Eq-transport (\ X -> HasType _ _ X) eqAS (RValSigma.htFst vpair)
        valFst-u1-S = Eq-transport (\ X -> Val2 _ _ X u1 b) eqAS valFst-u1
        vty-v1 = RValTySigma.edgeV (fst src) u1 v1 sel1 (Fst _) htFst-S valFst-u1-S
        vty-v1' = Eq-transport (\ X -> ValTy2 _ (subst1 X (Fst _)) v1) (Eq-sym (snd uniqS)) vty-v1
        vty-efu' = Eq-transport (\ x -> ValTy2 _ (subst1 (RValSigma.codB vpair) (Fst _)) x) (Eq-sym eq-v1) vty-v1'
        -- Step: restrict v'->v2 at ef u', then downVal2 to ef u2
        sndRestricted = restrictVal2 _ _ (subst1 (RValSigma.codB vpair) (Fst _)) v' v2 (EvalFun f u') (snd le)
                    fmv2efu' fmv'efu' (RValSigma.valSnd vpair)
        sndDown = downVal2 _ _ (subst1 (RValSigma.codB vpair) (Fst _)) v2 (EvalFun f u2) (EvalFun f u') le_ef fmv2efu2 c_ef_u2 ef_u'_U sndRestricted
        vpair' = record
          { domA = RValSigma.domA vpair ; codB = RValSigma.codB vpair ; red = RValSigma.red vpair
          ; htFst = RValSigma.htFst vpair ; cohW1 = cu2 ; fmW1 = fmu2b
          ; valFst = v2Fst' ; valSnd = sndDown
          }
    in mkSigma (fst src) vpair'
  -- PairCode restrictVal2
  restrictVal2 G M T Bot u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T UCode u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T PropCode u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T (FunEl g) u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T (PiCode a' f') u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T (SigmaCode a' f') u' (PairCode x y) le mem fmu src = src
  restrictVal2 G M T (PairCode u2 v2) u' (PairCode x y) le mem fmu src = src

  restrictEqVal2 G M N T Bot u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T UCode u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T PropCode u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T (FunEl g) u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a' f') u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T (SigmaCode a' f') u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T (PairCode x y) u' Bot          le mem fmu src = src
  restrictEqVal2 G M N T Bot Bot UCode        le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode UCode     ()
  restrictEqVal2 G M N T Bot (FunEl _) UCode ()
  restrictEqVal2 G M N T Bot (PiCode _ _) UCode ()
  restrictEqVal2 G M N T UCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T UCode UCode UCode le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl _) UCode ()
  restrictEqVal2 G M N T UCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (FunEl g) Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode UCode ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') UCode le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a' f') UCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PiCode a' f') (PiCode a2 f2) UCode le mem fmu (mkSigma vtM (mkSigma vtN eqvt)) =
    mkSigma (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le mem fmu vtM)
      (mkSigma (downValTy2 G N (PiCode a2 f2) (PiCode a' f') le mem fmu vtN)
        (downEqValTy2 G M N (PiCode a2 f2) (PiCode a' f') le mem fmu eqvt))
  restrictEqVal2 G M N T PropCode Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T PropCode UCode UCode ()
  restrictEqVal2 G M N T PropCode PropCode UCode le mem fmu src = src
  restrictEqVal2 G M N T PropCode (FunEl _) UCode ()
  restrictEqVal2 G M N T PropCode (PiCode _ _) UCode ()
  restrictEqVal2 G M N T Bot PropCode UCode ()
  restrictEqVal2 G M N T UCode PropCode UCode ()
  restrictEqVal2 G M N T (FunEl g) PropCode UCode ()
  restrictEqVal2 G M N T (PiCode a' f') PropCode UCode ()
  restrictEqVal2 G M N T Bot Bot PropCode le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode PropCode le ()
  restrictEqVal2 G M N T Bot PropCode PropCode ()
  restrictEqVal2 G M N T Bot (FunEl _) PropCode ()
  restrictEqVal2 G M N T Bot (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T UCode u' PropCode le mem ()
  restrictEqVal2 G M N T PropCode u' PropCode le mem ()
  restrictEqVal2 G M N T (FunEl _) u' PropCode le mem ()
  restrictEqVal2 G M N T (PiCode a' f') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PiCode a' f') UCode PropCode le ()
  restrictEqVal2 G M N T (PiCode a' f') PropCode PropCode ()
  restrictEqVal2 G M N T (PiCode a' f') (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (PiCode a' f') (PiCode a2 f2) PropCode le mem fmu (mkSigma vtM (mkSigma vtN eqvt)) =
    mkSigma (downValTy2 G M (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) vtM)
      (mkSigma (downValTy2 G N (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) vtN)
        (downEqValTy2 G M N (PiCode a2 f2) (PiCode a' f') le (FinMem-Prop-to-U (PiCode a2 f2) mem) (FinMem-Prop-to-U (PiCode a' f') fmu) eqvt))
  restrictEqVal2 G M N T Bot u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T UCode u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T PropCode u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T (FunEl g) u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a' f') u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T (SigmaCode a' f') u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T (PairCode x y) u' (FunEl h)    le mem fmu src = src
  restrictEqVal2 G M N T Bot Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g')     (PiCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (PiCode b f) le ()
  restrictEqVal2 G M N T UCode Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode UCode          (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (PiCode b f) le ()
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
  restrictEqVal2 G M N T (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a1 f1) UCode          (PiCode b f) le ()
  restrictEqVal2 G M N T (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = src
  -- SigmaCode restrictEqVal2
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
  restrictEqVal2 G M N T (SigmaCode a' f') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (SigmaCode a' f') UCode PropCode le ()
  restrictEqVal2 G M N T (SigmaCode a' f') PropCode PropCode ()
  restrictEqVal2 G M N T (SigmaCode a' f') (FunEl _) PropCode le ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PiCode a2 f2) PropCode le mem ()
  restrictEqVal2 G M N T (SigmaCode a' f') (SigmaCode a2 f2) PropCode le mem ()
  restrictEqVal2 G M N T (SigmaCode a' f') (PairCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') Bot UCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode _ _) UCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode _ _) UCode le mem ()
  restrictEqVal2 G M N T (PairCode u' v') PropCode UCode ()
  restrictEqVal2 G M N T (PairCode u' v') Bot PropCode le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode PropCode le ()
  restrictEqVal2 G M N T (PairCode u' v') PropCode PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode _ _) PropCode ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode _ _) PropCode le mem ()
  restrictEqVal2 G M N T Bot Bot (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T Bot UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (FunEl g') (SigmaCode b f) ()
  restrictEqVal2 G M N T Bot (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T Bot (PairCode u2 v2) (SigmaCode b f) ()
  restrictEqVal2 G M N T UCode Bot (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode UCode (SigmaCode b f) le mem fmu src = src
  restrictEqVal2 G M N T UCode (FunEl g') (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T UCode (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T UCode (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T PropCode u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (FunEl g) Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (FunEl g) UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (FunEl g') (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (FunEl g) (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (FunEl g) (PairCode u2 v2) (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (PiCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
  restrictEqVal2 G M N T (PairCode u' v') Bot (SigmaCode b f) le mem fmu src = tt
  restrictEqVal2 G M N T (PairCode u' v') UCode (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (FunEl g') (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (PiCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (SigmaCode a2 f2) (SigmaCode b f) le ()
  restrictEqVal2 G M N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu src =
    let valM  = Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b f) src
        valN  = Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b f) src
        valM' = restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu valM
        valN' = restrictVal2 G N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu valN
        eqp   = snd (snd (snd src))
        fmu'0 = fst (fst mem)
        eqFst' = restrictEqVal2 _ _ _ (REqValSigma.domA eqp) u' u2 b (fst le) fmu'0 (REqValSigma.fmW1 eqp) (REqValSigma.eqFst eqp)
        -- Compute restrictVal2 separately for REqValPair M/N fields
        vpairM-eq : RValSigma G M T (PairCode u' v') b f
        vpairM-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstM eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstM eqp ; valSnd = REqValSigma.valSndM eqp }
        valM-eq' = restrictVal2 G M T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu (mkSigma (fst src) vpairM-eq)
        vpairN-eq : RValSigma G N T (PairCode u' v') b f
        vpairN-eq = record { domA = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp ; htFst = REqValSigma.htFstN eqp ; cohW1 = REqValSigma.cohW1 eqp ; fmW1 = REqValSigma.fmW1 eqp ; valFst = REqValSigma.valFstN eqp ; valSnd = REqValSigma.valSndN eqp }
        valN-eq' = restrictVal2 G N T (PairCode u' v') (PairCode u2 v2) (SigmaCode b f) le mem fmu (mkSigma (fst src) vpairN-eq)
        eqp'  = record
          { domA   = REqValSigma.domA eqp ; codB = REqValSigma.codB eqp ; red = REqValSigma.red eqp
          ; htFstM = RValSigma.htFst (snd valM-eq')
          ; cohW1   = FinMem-Coherent u2 b fmu'0
          ; fmW1    = fmu'0
          ; valFstM = RValSigma.valFst (snd valM-eq')
          ; valSndM = RValSigma.valSnd (snd valM-eq')
          ; htFstN = RValSigma.htFst (snd valN-eq')
          ; valFstN = RValSigma.valFst (snd valN-eq')
          ; valSndN = RValSigma.valSnd (snd valN-eq')
          ; eqFst  = eqFst'
          }
    in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') eqp'))
  -- PairCode restrictEqVal2
  restrictEqVal2 G M N T Bot u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T UCode u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T PropCode u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T (FunEl g) u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T (PiCode a' f') u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T (SigmaCode a' f') u' (PairCode x y) le mem fmu src = src
  restrictEqVal2 G M N T (PairCode u2 v2) u' (PairCode x y) le mem fmu src = src

  ValTy2-Sup : {n : Nat} (G : Ctx n) (T : Expr n) (a1 a2 : FinEl) ->
    Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
    ValTy2 G T a1 -> ValTy2 G T a2 -> ValTy2 G T (Sup a1 a2)
  ValTy2-Sup G T Bot a2 comp fm1 fm2 vt1 vt2 = vt2
  ValTy2-Sup G T PropCode Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode UCode ()
  ValTy2-Sup G T PropCode PropCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T PropCode (FunEl g) ()
  ValTy2-Sup G T PropCode (PiCode b g) ()
  ValTy2-Sup G T PropCode (SigmaCode b g) ()
  ValTy2-Sup G T PropCode (PairCode x y) ()
  ValTy2-Sup G T UCode Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T UCode UCode comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T UCode (FunEl g) ()
  ValTy2-Sup G T UCode (PiCode b g) ()
  ValTy2-Sup G T UCode (SigmaCode b g) ()
  ValTy2-Sup G T UCode (PairCode x y) ()
  ValTy2-Sup G T (FunEl g) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) UCode ()
  ValTy2-Sup G T (FunEl g) (FunEl h) comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (FunEl g) (PiCode b h) ()
  ValTy2-Sup G T (FunEl g) (SigmaCode b h) ()
  ValTy2-Sup G T (FunEl g) (PairCode x y) ()
  ValTy2-Sup G T (PiCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (PiCode b1 f1) UCode ()
  ValTy2-Sup G T (PiCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (PiCode b1 f1) (SigmaCode b2 f2) ()
  ValTy2-Sup G T (PiCode b1 f1) (PairCode x y) ()
  ValTy2-Sup G T (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = RValTyPi.domA vt1
        B1    = RValTyPi.codB vt1
        red1  = RValTyPi.red vt1
        cf1   = RValTyPi.cohF vt1
        allU1 = RValTyPi.fmAllU vt1
        htA1  = RValTyPi.htA vt1
        htB1  = RValTyPi.htB vt1
        vtAb1 = RValTyPi.valA vt1
        piEV1 = RValTyPi.edgeV vt1
        piEE1 = RValTyPi.edgeE vt1
        A2    = RValTyPi.domA vt2
        B2    = RValTyPi.codB vt2
        red2  = RValTyPi.red vt2
        cf2   = RValTyPi.cohF vt2
        allU2 = RValTyPi.fmAllU vt2
        vtAb2 = RValTyPi.valA vt2
        piEV2 = RValTyPi.edgeV vt2
        piEE2 = RValTyPi.edgeE vt2
        uniq  = Red3-unique-Pi red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        piEV2' : PiEdgeVal2 G A1 B1 b2 f2
        piEV2' = Eq-transport (\ Y -> PiEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> PiEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) piEV2)
        piEE2' : PiEdgeEq2 G A1 B1 b2 f2
        piEE2' = Eq-transport (\ Y -> PiEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
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
              vt-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
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
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in record
      { domA   = A1
      ; codB   = B1
      ; red    = red1
      ; cohF   = cf-app
      ; fmAllU = allU-app
      ; htA    = htA1
      ; htB    = htB1
      ; valA   = vtA-sup
      ; edgeV  = piEV
      ; edgeE  = piEE
      }
  -- SigmaCode ValTy2-Sup (mirrors PiCode case exactly in structure)
  ValTy2-Sup G T (SigmaCode b1 f1) Bot comp fm1 fm2 vt1 vt2 = vt1
  ValTy2-Sup G T (SigmaCode b1 f1) UCode ()
  ValTy2-Sup G T (SigmaCode b1 f1) (FunEl h) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PiCode b2 f2) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (PairCode x y) ()
  ValTy2-Sup G T (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vt1 vt2 =
    let A1    = RValTySigma.domA vt1
        B1    = RValTySigma.codB vt1
        red1  = RValTySigma.red vt1
        cf1   = RValTySigma.cohF vt1
        allU1 = RValTySigma.fmAllU vt1
        htA1  = RValTySigma.htA vt1
        htB1  = RValTySigma.htB vt1
        vtAb1 = RValTySigma.valA vt1
        sigEV1 = RValTySigma.edgeV vt1
        sigEE1 = RValTySigma.edgeE vt1
        A2    = RValTySigma.domA vt2
        B2    = RValTySigma.codB vt2
        red2  = RValTySigma.red vt2
        cf2   = RValTySigma.cohF vt2
        allU2 = RValTySigma.fmAllU vt2
        vtAb2 = RValTySigma.valA vt2
        sigEV2 = RValTySigma.edgeV vt2
        sigEE2 = RValTySigma.edgeE vt2
        uniq  = Red3-unique-Sigma red1 red2
        eqA   = fst uniq
        eqB   = snd uniq
        vtAb2' : ValTy2 G A1 b2
        vtAb2' = Eq-transport (\ X -> ValTy2 G X b2) (Eq-sym eqA) vtAb2
        sigEV2' : SigmaEdgeVal2 G A1 B1 b2 f2
        sigEV2' = Eq-transport (\ Y -> SigmaEdgeVal2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeVal2 G X B2 b2 f2) (Eq-sym eqA) sigEV2)
        sigEE2' : SigmaEdgeEq2 G A1 B1 b2 f2
        sigEE2' = Eq-transport (\ Y -> SigmaEdgeEq2 G A1 Y b2 f2) (Eq-sym eqB)
                   (Eq-transport (\ X -> SigmaEdgeEq2 G X B2 b2 f2) (Eq-sym eqA) sigEE2)
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
        sigEV : SigmaEdgeVal2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sigEV = \ u v sel N htN valN ->
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
              vt-v1  = sigEV1 u1 v1 sel1 N htN val-u1-b1
              vt-v2  = sigEV2' u2 v2 sel2 N htN val-u2-b2
              vt-ef1 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v1) vt-v1
              vt-ef2 = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-v2) vt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              vt-sup  = ValTy2-Sup G (subst1 B1 N) (EvalFun f1 u) (EvalFun f2 u)
                          comp-ef fm-ef1U fm-ef2U vt-ef1 vt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              vt-ef-app = Eq-transport (\ x -> ValTy2 G (subst1 B1 N) x) (Eq-sym eq-app) vt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downValTy2 _ (subst1 B1 N) v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU vt-ef-app
        sigEE : SigmaEdgeEq2 G A1 B1 (Sup b1 b2) (append f1 f2)
        sigEE = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
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
              eqt-v1 = sigEE1 u1 v1 sel1 N1 N2 htN1 htN2 cvN eqv-u1-b1
              eqt-v2 = sigEE2' u2 v2 sel2 N1 N2 htN1 htN2 cvN eqv-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 B1 N1) (subst1 B1 N2)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 B1 N1) (subst1 B1 N2) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 B1 N1) (subst1 B1 N2)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
    in record
      { domA   = A1
      ; codB   = B1
      ; red    = red1
      ; cohF   = cf-app
      ; fmAllU = allU-app
      ; fmBU   = supU
      ; htA    = htA1
      ; htB    = htB1
      ; valA   = vtA-sup
      ; edgeV  = sigEV
      ; edgeE  = sigEE
      }
  ValTy2-Sup G T (PairCode u v) a2 comp ()

  ------------------------------------------------------------------
  -- EqValTy2-Sup
  ------------------------------------------------------------------

  EqValTy2-Sup : {n : Nat} (G : Ctx n) (M N : Expr n) (u1 u2 : FinEl) ->
    Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
    EqValTy2 G M N u1 -> EqValTy2 G M N u2 -> EqValTy2 G M N (Sup u1 u2)
  EqValTy2-Sup G M N Bot u2 comp fm1 fm2 eq1 eq2 = eq2
  EqValTy2-Sup G M N PropCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode UCode ()
  EqValTy2-Sup G M N PropCode PropCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N PropCode (FunEl g) ()
  EqValTy2-Sup G M N PropCode (PiCode b g) ()
  EqValTy2-Sup G M N PropCode (SigmaCode b g) ()
  EqValTy2-Sup G M N PropCode (PairCode x y) ()
  EqValTy2-Sup G M N UCode Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode UCode comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N UCode (FunEl g) ()
  EqValTy2-Sup G M N UCode (PiCode b g) ()
  EqValTy2-Sup G M N UCode (SigmaCode b g) ()
  EqValTy2-Sup G M N UCode (PairCode x y) ()
  EqValTy2-Sup G M N (FunEl g) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) UCode ()
  EqValTy2-Sup G M N (FunEl g) (FunEl h) comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (FunEl g) (PiCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (SigmaCode b h) ()
  EqValTy2-Sup G M N (FunEl g) (PairCode x y) ()
  EqValTy2-Sup G M N (PiCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (PiCode b1 f1) UCode ()
  EqValTy2-Sup G M N (PiCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (SigmaCode b2 f2) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PairCode x y) ()
  EqValTy2-Sup G M N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM1-eq1 = fst eq1
        vtN1-eq1 = fst (snd eq1)
        eqPi1    = snd (snd eq1)
        vtM2-eq2 = fst eq2
        vtN2-eq2 = fst (snd eq2)
        eqPi2    = snd (snd eq2)
        AM      = REqValTyPi.domA eqPi1
        BM      = REqValTyPi.codB eqPi1
        AN      = REqValTyPi.domA' eqPi1
        BN      = REqValTyPi.codB' eqPi1
        redM1   = REqValTyPi.redM eqPi1
        redN1   = REqValTyPi.redN eqPi1
        cfEq1   = REqValTyPi.cohF eqPi1
        allUEq1 = REqValTyPi.fmAllU eqPi1
        convAA1 = REqValTyPi.convA eqPi1
        convBB1 = REqValTyPi.convB eqPi1
        eqvtA1  = REqValTyPi.eqA eqPi1
        piEET1  = REqValTyPi.edgeET eqPi1
        AM2     = REqValTyPi.domA eqPi2
        BM2     = REqValTyPi.codB eqPi2
        AN2     = REqValTyPi.domA' eqPi2
        BN2     = REqValTyPi.codB' eqPi2
        redM2   = REqValTyPi.redM eqPi2
        redN2   = REqValTyPi.redN eqPi2
        cfEq2   = REqValTyPi.cohF eqPi2
        allUEq2 = REqValTyPi.fmAllU eqPi2
        convAA2 = REqValTyPi.convA eqPi2
        convBB2 = REqValTyPi.convB eqPi2
        eqvtA2  = REqValTyPi.eqA eqPi2
        piEET2  = REqValTyPi.edgeET eqPi2
        uniqM   = Red3-unique-Pi redM1 redM2
        eqAM    = fst uniqM
        eqBM    = snd uniqM
        uniqN   = Red3-unique-Pi redN1 redN2
        eqAN    = fst uniqN
        eqBN    = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) eqvtA2)
        piEET2' : PiEdgeEqTy2 G AM BM BN b2 f2
        piEET2' = Eq-transport (\ X -> PiEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
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
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        vtM-sup = ValTy2-Sup G M (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtM1-eq1 vtM2-eq2
        vtN-sup = ValTy2-Sup G N (PiCode b1 f1) (PiCode b2 f2) comp fm1 fm2 vtN1-eq1 vtN2-eq2
        eqTyPi = record
          { domA   = AM
          ; codB   = BM
          ; domA'  = AN
          ; codB'  = BN
          ; redM   = redM1
          ; redN   = redN1
          ; cohF   = cf-app
          ; fmAllU = allU-app
          ; convA  = convAA1
          ; convB  = convBB1
          ; eqA    = eqvtA-sup
          ; edgeET = piEET
          }
    in mkSigma vtM-sup (mkSigma vtN-sup eqTyPi)
  -- SigmaCode EqValTy2-Sup (mirrors PiCode)
  EqValTy2-Sup G M N (SigmaCode b1 f1) Bot comp fm1 fm2 eq1 eq2 = eq1
  EqValTy2-Sup G M N (SigmaCode b1 f1) UCode ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (FunEl h) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PiCode b2 f2) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (PairCode x y) ()
  EqValTy2-Sup G M N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 eq1 eq2 =
    let vtM1 = fst eq1
        vtN1 = fst (snd eq1)
        eqS1 = snd (snd eq1)
        vtM2 = fst eq2
        vtN2 = fst (snd eq2)
        eqS2 = snd (snd eq2)
        AM   = REqValTySigma.domA eqS1
        BM   = REqValTySigma.codB eqS1
        AN   = REqValTySigma.domA' eqS1
        BN   = REqValTySigma.codB' eqS1
        redM1 = REqValTySigma.redM eqS1
        redN1 = REqValTySigma.redN eqS1
        AM2  = REqValTySigma.domA eqS2
        BM2  = REqValTySigma.codB eqS2
        AN2  = REqValTySigma.domA' eqS2
        BN2  = REqValTySigma.codB' eqS2
        redM2 = REqValTySigma.redM eqS2
        redN2 = REqValTySigma.redN eqS2
        uniqM = Red3-unique-Sigma redM1 redM2
        eqAM  = fst uniqM
        eqBM  = snd uniqM
        uniqN = Red3-unique-Sigma redN1 redN2
        eqAN  = fst uniqN
        eqBN  = snd uniqN
        eqvtA2' : EqValTy2 G AM AN b2
        eqvtA2' = Eq-transport (\ X -> EqValTy2 G X AN b2) (Eq-sym eqAM)
                    (Eq-transport (\ X -> EqValTy2 G AM2 X b2) (Eq-sym eqAN) (REqValTySigma.eqA eqS2))
        sigEET2' : SigmaEdgeEqTy2 G AM BM BN b2 f2
        sigEET2' = Eq-transport (\ X -> SigmaEdgeEqTy2 G AM BM X b2 f2) (Eq-sym eqBN)
                    (Eq-transport (\ X -> SigmaEdgeEqTy2 G AM X BN2 b2 f2) (Eq-sym eqBM)
                      (Eq-transport (\ X -> SigmaEdgeEqTy2 G X BM2 BN2 b2 f2) (Eq-sym eqAM) (REqValTySigma.edgeET eqS2)))
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
        ctf1   = REqValTySigma.cohF eqS1
        ctf2   = REqValTySigma.cohF eqS2
        cf-app = CoherentFunTail-append f1 f2 ctf1 ctf2 comp-f
        ctf-app = cf-app
        allU-app = FinMemAllU-append-Sup b1 b2 f1 f2 comp-b cb1 cb2
                     b1U b2U ctf1 ctf2 allU1' allU2'
        le-b1-sup = LeCode-Sup-left b1 b2 comp-b cb1 cb2
        le-b2-sup = LeCode-Sup-right b1 b2 comp-b cb1 cb2
        eqvtA-sup = EqValTy2-Sup G AM AN b1 b2 comp-b b1U b2U (REqValTySigma.eqA eqS1) eqvtA2'
        sigEET : SigmaEdgeEqTy2 G AM BM BN (Sup b1 b2) (append f1 f2)
        sigEET = \ u v sel P htP valP ->
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
              eqt-v1  = REqValTySigma.edgeET eqS1 u1 v1 sel1 P htP val-u1-b1
              eqt-v2  = sigEET2' u2 v2 sel2 P htP val-u2-b2
              eqt-ef1 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v1) eqt-v1
              eqt-ef2 = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                          (Eq-sym eq-v2) eqt-v2
              comp-ef = comp-EvalFun f1 f2 u comp-f ctf1 cu
              fm-ef1U = EvalFun-in-UCode f1 u b1 ctf1 cu allU1'
              fm-ef2U = EvalFun-in-UCode f2 u b2 ctf2 cu allU2'
              eqt-sup = EqValTy2-Sup G (subst1 BM P) (subst1 BN P)
                          (EvalFun f1 u) (EvalFun f2 u) comp-ef fm-ef1U fm-ef2U eqt-ef1 eqt-ef2
              eq-app  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu
              eqt-ef-app = Eq-transport (\ x -> EqValTy2 G (subst1 BM P) (subst1 BN P) x)
                             (Eq-sym eq-app) eqt-sup
              fmvU   = FinMem-Selection-UCode (Sup b1 b2) sel allU-app ctf-app
              ef-appU = EvalFun-in-UCode (append f1 f2) u (Sup b1 b2) ctf-app cu allU-app
              lf-refl = LeFunCode-refl (append f1 f2) ctf-app
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-refl ctf-app ctf-app cu
          in downEqValTy2 G (subst1 BM P) (subst1 BN P)
               v (EvalFun (append f1 f2) u) le-v-ef fmvU ef-appU eqt-ef-app
        vtM-sup = ValTy2-Sup G M (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vtM1 vtM2
        vtN-sup = ValTy2-Sup G N (SigmaCode b1 f1) (SigmaCode b2 f2) comp fm1 fm2 vtN1 vtN2
        eqTySigma = record
          { domA = AM ; codB = BM ; domA' = AN ; codB' = BN
          ; redM = redM1 ; redN = redN1
          ; cohF = cf-app ; fmAllU = allU-app
          ; convA = REqValTySigma.convA eqS1 ; convB = REqValTySigma.convB eqS1
          ; eqA = eqvtA-sup ; edgeET = sigEET
          }
    in mkSigma vtM-sup (mkSigma vtN-sup eqTySigma)
  EqValTy2-Sup G M N (PairCode u v) a2 comp ()

------------------------------------------------------------------------
-- Transport lemmas (outside the mutual block)
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
