{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- Validity5Core.agda
--
-- Core validity relation for Pi + Sigma + U.
-- Uses RValSigma/REqValSigma (uniform in w) instead of RValPair/REqValPair.
-- No transport lemmas — those will be added separately.
--
-- 0 postulates.
------------------------------------------------------------------------

module Validity5Core where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              codeFst ; codeSnd)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ; Fst ; Snd ; MkPair ;
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

  Val2 G M A u Bot              = Top
  Val2 G M A UCode UCode        = Pair (ValTy2 G A UCode) (ValTy2 G M UCode)
  Val2 G M A PropCode UCode      = Pair (ValTy2 G A UCode) (ValTy2 G M PropCode)
  Val2 G M A (PiCode a' f') UCode  = Pair (ValTy2 G A UCode) (ValTy2 G M (PiCode a' f'))
  Val2 G M A (SigmaCode a' f') UCode = Pair (ValTy2 G A UCode) (ValTy2 G M (SigmaCode a' f'))
  Val2 G M A u UCode               = Top
  Val2 G M A (PiCode a' f') PropCode = Pair (ValTy2 G A PropCode) (ValTy2 G M (PiCode a' f'))
  Val2 G M A u PropCode            = Top
  Val2 G M A u (FunEl h)           = Top
  Val2 G M A (FunEl g) (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f)) (RValPi G M A g b f)
  Val2 G M A u (PiCode b f)        = Top
  Val2 G M A (PairCode u' v') (SigmaCode b f) =
    Pair (ValTy2 G A (SigmaCode b f)) (RValSigma G M A (PairCode u' v') b f)
  Val2 G M A u (SigmaCode b f)     = Top
  Val2 G M A u (PairCode x y)      = Top

  ------------------------------------------------------------------
  -- EqVal2: pattern matching on codes
  ------------------------------------------------------------------

  EqVal2 G M N A u Bot              = Top
  EqVal2 G M N A UCode UCode        =
    Pair (ValTy2 G A UCode) (Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode)))
  EqVal2 G M N A PropCode UCode     =
    Pair (ValTy2 G A UCode) (Pair (ValTy2 G M PropCode) (Pair (ValTy2 G N PropCode) (EqValTy2 G M N PropCode)))
  EqVal2 G M N A (PiCode a' f') UCode  =
    Pair (ValTy2 G A UCode) (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A (SigmaCode a' f') UCode =
    Pair (ValTy2 G A UCode) (Pair (ValTy2 G M (SigmaCode a' f')) (Pair (ValTy2 G N (SigmaCode a' f')) (EqValTy2 G M N (SigmaCode a' f'))))
  EqVal2 G M N A u UCode               = Top
  EqVal2 G M N A (PiCode a' f') PropCode =
    Pair (ValTy2 G A PropCode)
         (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A u PropCode            = Top
  EqVal2 G M N A u (FunEl h)           = Top
  EqVal2 G M N A (FunEl g) (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f))
         (Pair (RValPi G M A g b f)
               (Pair (RValPi G N A g b f)
                     (REqValPi G M N A g b f)))
  EqVal2 G M N A u (PiCode b f)        = Top
  EqVal2 G M N A (PairCode u' v') (SigmaCode b f) =
    Pair (ValTy2 G A (SigmaCode b f))
         (Pair (RValSigma G M A (PairCode u' v') b f)
               (Pair (RValSigma G N A (PairCode u' v') b f)
                     (REqValSigma G M N A (PairCode u' v') b f)))
  EqVal2 G M N A u (SigmaCode b f)     = Top
  EqVal2 G M N A u (PairCode x y)      = Top

  ------------------------------------------------------------------
  -- ValTy2 / EqValTy2
  ------------------------------------------------------------------

  ValTy2 G M Bot          = Top
  ValTy2 G M UCode        = Red3 G M U U
  ValTy2 G M PropCode     = Red3 G M Prop U
  ValTy2 G M (FunEl g)    = Top
  ValTy2 G M (PiCode b f) = RValTyPi G M b f
  ValTy2 G M (SigmaCode b f) = RValTySigma G M b f
  ValTy2 G M (PairCode u v) = Top

  EqValTy2 G M N Bot          = Top
  EqValTy2 G M N UCode        = Pair (Red3 G M U U) (Red3 G N U U)
  EqValTy2 G M N PropCode     = Pair (Red3 G M Prop U) (Red3 G N Prop U)
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
  Val2-to-EqVal2 u Bot v = tt
  Val2-to-EqVal2 Bot UCode v = tt
  Val2-to-EqVal2 Bot PropCode v = tt
  Val2-to-EqVal2 Bot (FunEl h) v = tt
  Val2-to-EqVal2 Bot (PiCode b f) v = tt
  Val2-to-EqVal2 Bot (SigmaCode b f) v = tt
  Val2-to-EqVal2 Bot (PairCode x y) v = tt
  Val2-to-EqVal2 UCode UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (mkSigma (snd v) (snd v))))
  Val2-to-EqVal2 (FunEl g) UCode v = tt
  Val2-to-EqVal2 (PiCode a f) UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (ValTy2-to-EqValTy2 (PiCode a f) (snd v))))
  Val2-to-EqVal2 (SigmaCode a f) UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (ValTy2-to-EqValTy2 (SigmaCode a f) (snd v))))
  Val2-to-EqVal2 (PairCode u' v') UCode v = tt
  Val2-to-EqVal2 PropCode UCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (ValTy2-to-EqValTy2 PropCode (snd v))))
  Val2-to-EqVal2 (PiCode a f) PropCode v = mkSigma (fst v) (mkSigma (snd v) (mkSigma (snd v) (ValTy2-to-EqValTy2 (PiCode a f) (snd v))))
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
  Val2-to-EqVal2 UCode (SigmaCode b f) v = tt
  Val2-to-EqVal2 PropCode (SigmaCode b f) v = tt
  Val2-to-EqVal2 (FunEl g) (SigmaCode b f) v = tt
  Val2-to-EqVal2 (PiCode a' f') (SigmaCode b f) v = tt
  Val2-to-EqVal2 (SigmaCode a' f') (SigmaCode b f) v = tt
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
  ValTy2-to-EqValTy2 PropCode v = mkSigma v v
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
  Val2-from-EqVal2-first u Bot ev = tt
  Val2-from-EqVal2-first Bot UCode ev = tt
  Val2-from-EqVal2-first Bot PropCode ev = tt
  Val2-from-EqVal2-first Bot (FunEl h) ev = tt
  Val2-from-EqVal2-first Bot (PiCode b f) ev = tt
  Val2-from-EqVal2-first Bot (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first Bot (PairCode x y) ev = tt
  Val2-from-EqVal2-first UCode UCode ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (FunEl g) UCode ev = tt
  Val2-from-EqVal2-first (PiCode a f) UCode ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (SigmaCode a f) UCode ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-first PropCode UCode ev = mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first (PiCode a f) PropCode ev = mkSigma (fst ev) (fst (snd ev))
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
  Val2-from-EqVal2-first UCode (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first PropCode (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first (FunEl g) (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first (PiCode a' f') (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first (SigmaCode a' f') (SigmaCode b f) ev = tt
  Val2-from-EqVal2-first (PairCode u' v') (SigmaCode b f) ev =
    mkSigma (fst ev) (fst (snd ev))
  Val2-from-EqVal2-first UCode (PairCode x y) ev = tt
  Val2-from-EqVal2-first PropCode (PairCode x y) ev = tt
  Val2-from-EqVal2-first (FunEl g) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (PiCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (SigmaCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-first (PairCode u' v') (PairCode x y) ev = tt

  Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
  Val2-from-EqVal2-second u Bot ev = tt
  Val2-from-EqVal2-second Bot UCode ev = tt
  Val2-from-EqVal2-second Bot PropCode ev = tt
  Val2-from-EqVal2-second Bot (FunEl h) ev = tt
  Val2-from-EqVal2-second Bot (PiCode b f) ev = tt
  Val2-from-EqVal2-second Bot (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second Bot (PairCode x y) ev = tt
  Val2-from-EqVal2-second UCode UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (FunEl g) UCode ev = tt
  Val2-from-EqVal2-second (PiCode a f) UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (SigmaCode a f) UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (PairCode u' v') UCode ev = tt
  Val2-from-EqVal2-second PropCode UCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second (PiCode a f) PropCode ev = mkSigma (fst ev) (fst (snd (snd ev)))
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
  Val2-from-EqVal2-second UCode (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second PropCode (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second (FunEl g) (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second (PiCode a' f') (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second (SigmaCode a' f') (SigmaCode b f) ev = tt
  Val2-from-EqVal2-second (PairCode u' v') (SigmaCode b f) ev =
    mkSigma (fst ev) (fst (snd (snd ev)))
  Val2-from-EqVal2-second UCode (PairCode x y) ev = tt
  Val2-from-EqVal2-second PropCode (PairCode x y) ev = tt
  Val2-from-EqVal2-second (FunEl g) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (PiCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (SigmaCode a f) (PairCode x y) ev = tt
  Val2-from-EqVal2-second (PairCode u' v') (PairCode x y) ev = tt
