{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- ValidityStratified.agda  (MIN/ — Pi + U fragment)
--
-- Rank-stratified replacement for the mutual block in
-- ValidityCore.agda.  Instead of defining Val2/EqVal2/ValTy2/EqValTy2
-- by recursion through FinEl codes (which Agda cannot see terminates),
-- we define a `Stage : Nat -> Bundle` family by *structural recursion
-- on the step index n*.  Stage (suc n) builds the level-(suc n)
-- relations from the level-n bundle: the type-level relations recurse
-- into level n on strictly-smaller-RANK codes (domain b, edge value
-- EvalFun f u), so one Stage step strips one rank level.
--
-- The public relations are recovered at the canonical level
--   suc (max (RANK u) (RANK a))   -- enough levels for the codes present.
--
-- No postulates.
------------------------------------------------------------------------

module MIN.ValidityStratified where

open import MIN.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
         Sigma ; Eq ; refl ; max ; Le ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons)
open import MIN.RawSyntax using (Expr ; U ; Pi ; App ; subst1)
open import MIN.TypingRules using (Ctx ; extend ; HasType ; ConvTm)
open import MIN.Reduction using (HeadRed)
open import MIN.PaperSemantics
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU)
open import MIN.Selection using (Selection)
open import MIN.Rank using (RANK)

------------------------------------------------------------------------
-- Red3: HeadRed bundled with ConvTm (as in the paper)
------------------------------------------------------------------------

record Red3 {n : Nat} (G : Ctx n) (M N A : Expr n) : Set where
  constructor mkRed3
  field
    hr : HeadRed M N
    ct : ConvTm G M N A

------------------------------------------------------------------------
-- OpenRecords: edge types + records parameterized by abstract relations.
-- (Same as ValidityCore; the relations are supplied by the *previous*
-- Stage level, so there is no cycle.)
------------------------------------------------------------------------

module OpenRecords
  (V2   : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set)
  (EV2  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set)
  (VT2  : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set)
  (EVT2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set)
  where

  -- The edge `forall (u v), Selection f u v -> ...` is already rank-bounded:
  -- Selection forces RANK u <= RANKFun f < RANK (PiCode b f) (SelectionRank),
  -- so no explicit level/bound parameter is needed and the relation is
  -- level-independent above the code's rank.

  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> V2 G N A u b ->
    VT2 G (subst1 B N) v

  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EV2 G N1 N2 A u b ->
    EVT2 G (subst1 B N1) (subst1 B N2) v

  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> V2 G P A u b ->
    EVT2 G (subst1 B P) (subst1 B' P) v

  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppVal2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N : Expr n) -> HasType G N A0 -> V2 G N A0 u b ->
    V2 G (App M N) (subst1 B0 N) v (EvalFun f u)

  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEq2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
    ConvTm G N1 N2 A0 -> EV2 G N1 N2 A0 u b ->
    EV2 G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)

  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEqVal2 {n} G M N A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (P : Expr n) -> HasType G P A0 -> V2 G P A0 u b ->
    EV2 G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)

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
      valA   : VT2 G domA b
      edgeV  : PiEdgeVal2 G domA codB b f
      edgeE  : PiEdgeEq2 G domA codB b f

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
      eqA    : EVT2 G domA domA' b
      edgeET : PiEdgeEqTy2 G domA codB codB' b f

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

  record REqValPi {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      codB0  : Expr (suc n)
      red    : Red3 G A (Pi domA0 codB0) U
      cohG   : CoherentFun g
      fmG    : FinMemFun g b f
      appEV  : PiAppEqVal2 G M N domA0 codB0 b f g

------------------------------------------------------------------------
-- Bundle of the four relations at one stage level
------------------------------------------------------------------------

record Bundle : Set1 where
  field
    val     : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    eqval   : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    valty   : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
    eqvalty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

-- Base: everything trivial. Only ever consulted at codes whose RANK
-- exceeds the available levels (never at the canonical level of a real
-- code), so the trivial value is harmless.
trivBundle : Bundle
trivBundle = record
  { val     = \ _ _ _ _ _   -> Top
  ; eqval   = \ _ _ _ _ _ _ -> Top
  ; valty   = \ _ _ _       -> Top
  ; eqvalty = \ _ _ _ _     -> Top
  }

-- One stage step: build level-(suc n) relations from the level-n bundle B.
buildStage : Bundle -> Bundle
buildStage B = record { val = vl ; eqval = evl ; valty = vty ; eqvalty = evty }
  where
    open Bundle B renaming (val to V ; eqval to EV ; valty to VT ; eqvalty to EVT)
    open OpenRecords V EV VT EVT

    vty : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
    vty G M Bot          = Top
    vty G M UCode        = Red3 G M U U
    vty G M (FunEl g)    = Top
    vty G M (PiCode b f) = RValTyPi G M b f

    evty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
    evty G M N Bot          = Top
    evty G M N UCode        = Pair (Red3 G M U U) (Red3 G N U U)
    evty G M N (FunEl g)    = Top
    evty G M N (PiCode b f) =
      Pair (RValTyPi G M b f)
           (Pair (RValTyPi G N b f) (REqValTyPi G M N b f))

    -- NO-LAG form: val/eqval's direct type-components use the SAME-stage
    -- locally-built vty/evty (not the predecessor VT/EVT).  This makes val
    -- and valty strip rank levels identically => uniform canonical level,
    -- so the property package re-indexes by n without cross-level +-1
    -- bookkeeping.  The records (RValPi/REqValPi) still reference the
    -- predecessor via OpenRecords (that is the rank-stripping recursion).
    -- vty/evty never call vl/evl, so the vl -> vty dependency is acyclic
    -- and buildStage stays structural recursion on n.
    vl : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    vl G M A u Bot                  = Top
    vl G M A UCode UCode            = Pair (vty G A UCode) (vty G M UCode)
    vl G M A (PiCode a' f') UCode   = Pair (vty G A UCode) (vty G M (PiCode a' f'))
    vl G M A u UCode                = Top
    vl G M A u (FunEl h)            = Top
    vl G M A (FunEl g) (PiCode b f) = Pair (vty G A (PiCode b f)) (RValPi G M A g b f)
    vl G M A u (PiCode b f)         = Top

    evl : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    evl G M N A u Bot                  = Top
    evl G M N A UCode UCode            =
      Pair (vty G A UCode)
           (Pair (vty G M UCode) (Pair (vty G N UCode) (evty G M N UCode)))
    evl G M N A (PiCode a' f') UCode   =
      Pair (vty G A UCode)
           (Pair (vty G M (PiCode a' f'))
                 (Pair (vty G N (PiCode a' f')) (evty G M N (PiCode a' f'))))
    evl G M N A u UCode                = Top
    evl G M N A u (FunEl h)            = Top
    evl G M N A (FunEl g) (PiCode b f) =
      Pair (vty G A (PiCode b f))
           (Pair (RValPi G M A g b f)
                 (Pair (RValPi G N A g b f) (REqValPi G M N A g b f)))
    evl G M N A u (PiCode b f)         = Top

-- The stratified family, by structural recursion on the step index.
Stage : Nat -> Bundle
Stage zero    = trivBundle
Stage (suc n) = buildStage (Stage n)

------------------------------------------------------------------------
-- Public relations at the canonical level
------------------------------------------------------------------------

-- NO-LAG: val and valty strip levels identically, so the canonical level
-- for val/eqval is suc (max (RANK u) (RANK a)) (matching the vlU/vlD
-- stability bounds), NOT one higher.
Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Val2 G M A u a = Bundle.val (Stage (suc (max (RANK u) (RANK a)))) G M A u a

EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EqVal2 G M N A u a = Bundle.eqval (Stage (suc (max (RANK u) (RANK a)))) G M N A u a

ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
ValTy2 G M a = Bundle.valty (Stage (suc (RANK a))) G M a

EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
EqValTy2 G M N a = Bundle.eqvalty (Stage (suc (RANK a))) G M N a
