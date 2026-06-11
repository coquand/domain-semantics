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

module CAST.ValidityStratified where

open import CAST.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
         Sigma ; Eq ; refl ; max ; Le ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun ; List ; nil ; cons)
open import CAST.RawSyntax using (Expr ; U ; Pi ; App ; Id ; cast ; subst1)
open import CAST.TypingRules using (Ctx ; extend ; HasType ; ConvTm ;
  ty-Id ; ty-refl ; ty-conv ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Id ; conv-cast-refl ; conv-cast-cong)
open import CAST.SubstitutionLemma using (typing-ConvTm)
open import CAST.Reduction using (HeadRed ; HeadRed1 ; headred-refl ; headred-step ;
  HeadRed-trans ; HeadRed-strip-U ; HeadRed-strip-Pi ; HeadRed-strip-nf ; HeadRed1-not-Pi)
open import CAST.PaperSemantics
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU)
open import CAST.Selection using (Selection)
open import CAST.Rank using (RANK)

------------------------------------------------------------------------
-- Red3: HeadRed bundled with ConvTm (as in the paper)
------------------------------------------------------------------------

-- Head-reduction bundled with its conversion (the paper's Red3 G A M M':
-- M weak-head-reduces to M' AND G |- M = M' : A).  Now PURELY syntactic: the
-- Lean cast iota-rule lives in HeadRed1 (headred-cast-refl : cast A B refl M
-- -> M), so the collapse is an ordinary mkRed3 (HeadRed + conv-cast-refl) and
-- the head-expansion Lemma 10 applies to it like beta.  red3-conv only
-- re-indexes the type along a type conversion (no reduction content).
data Red3 {n : Nat} (G : Ctx n) : Expr n -> Expr n -> Expr n -> Set where
  mkRed3 : {M N A : Expr n} -> HeadRed M N -> ConvTm G M N A -> Red3 G M N A
  red3-conv : {M N A A' : Expr n} ->
    ConvTm G A A' U -> Red3 G M N A -> Red3 G M N A'

-- total extraction of the underlying head reduction (no collapse case now).
Red3-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> HeadRed M N
Red3-hr (mkRed3 hr ct) = hr
Red3-hr (red3-conv c r) = Red3-hr r

-- the collapse conversion  cast A B p M0 == M0 : B  for an ARBITRARY proof p
-- (p == refl by proof irrelevance, then the refl-iota rule conv-cast-refl).
collapse-conv : {n : Nat} {G : Ctx n} {A B p M0 : Expr n} ->
  HasType G A U -> HasType G B U -> HasType G p (Id A B) -> HasType G M0 A ->
  ConvTm G A B U -> ConvTm G (cast A B p M0) M0 B
collapse-conv {G = G} {A} {B} {p} {M0} dA dB dp dM0 cAB =
  let reflAB = ty-conv (ty-refl dA) (conv-Id dA dA dA dB (conv-refl dA) cAB) (ty-Id dA dB)
      cong = conv-cast-cong dA dB dp dM0 dA dB reflAB dM0 (conv-refl dA) (conv-refl dB) (conv-refl dM0)
      rfl  = conv-cast-refl dA dB dM0 cAB
  in conv-trans cong rfl

-- total extraction of the bundled conversion
Red3-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> ConvTm G M N A
Red3-ct (mkRed3 hr ct) = ct
Red3-ct (red3-conv c r) = conv-conv (Red3-ct r) c (snd (typing-ConvTm c))

-- transitivity of the typed head reduction
-- left factor is a fixed mkRed3 (hr, ct); recurse only on the right factor so
-- termination descends on the right Red3's structure (handles a red3-conv on
-- the right by pushing the conversion into ct).
Red3-trans-mk : {n : Nat} {G : Ctx n} {M N P A : Expr n} ->
  HeadRed M N -> ConvTm G M N A -> Red3 G N P A -> Red3 G M P A
Red3-trans-mk hr ct (mkRed3 hr' ct') = mkRed3 (HeadRed-trans hr hr') (conv-trans ct ct')
Red3-trans-mk hr ct (red3-conv c r) =
  red3-conv c (Red3-trans-mk hr (conv-conv ct (conv-sym c) (fst (typing-ConvTm c))) r)

Red3-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n} ->
  Red3 G M N A -> Red3 G N P A -> Red3 G M P A
Red3-trans (mkRed3 hr ct) r2 = Red3-trans-mk hr ct r2
Red3-trans (red3-conv c r1) r2 =
  red3-conv c (Red3-trans r1 (red3-conv (conv-sym c) r2))

-- (kept as an alias of the now-total Red3-hr; the source need not be a Pi.)
Red3-hr-from-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {N T : Expr n} ->
  Red3 G (Pi A B) N T -> HeadRed (Pi A B) N
Red3-hr-from-Pi = Red3-hr

-- strip an untyped prefix M ->* M' from a typed reduction M ->* U / M ->* Pi
-- type index A is general (was U) so the red3-conv case can recurse at the
-- predecessor type A0.
Red3-strip-U : {n : Nat} {G : Ctx n} {M M' A : Expr n} ->
  HeadRed M M' -> ConvTm G M M' A -> Red3 G M U A -> Red3 G M' U A
Red3-strip-U hr cv (mkRed3 hrX ctX) =
  mkRed3 (HeadRed-strip-U hr hrX) (conv-trans (conv-sym cv) ctX)
Red3-strip-U hr cv (red3-conv c r) =
  red3-conv c (Red3-strip-U hr (conv-conv cv (conv-sym c) (fst (typing-ConvTm c))) r)

Red3-strip-Pi : {n : Nat} {G : Ctx n} {M M' A0 T : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> ConvTm G M M' T -> Red3 G M (Pi A0 B) T -> Red3 G M' (Pi A0 B) T
Red3-strip-Pi hr cv (mkRed3 hrX ctX) =
  mkRed3 (HeadRed-strip-Pi hr hrX) (conv-trans (conv-sym cv) ctX)
Red3-strip-Pi hr cv (red3-conv c r) =
  red3-conv c (Red3-strip-Pi hr (conv-conv cv (conv-sym c) (fst (typing-ConvTm c))) r)

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
    vty G M (IdCode b d) = Top

    evty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
    evty G M N Bot          = Top
    evty G M N UCode        = Pair (Red3 G M U U) (Red3 G N U U)
    evty G M N (FunEl g)    = Top
    evty G M N (PiCode b f) =
      Pair (RValTyPi G M b f)
           (Pair (RValTyPi G N b f) (REqValTyPi G M N b f))
    evty G M N (IdCode b d) = Top

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
    vl G M A u (IdCode b f)         = Top

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
    evl G M N A u (IdCode b f)         = Top

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
