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

module ID.Validity.Stratified where

open import ID.Domain.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
         Sigma ; Eq ; refl ; max ; Le ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ; List ; nil ; cons)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; App ; Id ; Ref ; J ; subst1)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm)
open import ID.Syntax.Reduction using (HeadRed)
open import ID.Domain.Kernel
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ; FinMem ; LeCode)
open import ID.Model.Selection using (Selection)
open import ID.Domain.Rank using (RANK)

------------------------------------------------------------------------
-- Red3: the head reduction to canonical form.
--
-- (Historically this ALSO bundled a ConvTm G M N A.  That syntactic
-- conversion is dropped: it forced the head-expansion closure of the
-- logical relation to carry a ConvTm, which for the J eliminator is only
-- obtainable via Id-injectivity -- circular, since Id-injectivity is a
-- COROLLARY of adequacy.  The reduction closure needs only the HeadRed.
-- `mkRed3` is kept as a 2-argument wrapper that ignores the ConvTm, so the
-- ~95 construction sites are unchanged.  The syntactic conversions the
-- corollaries need (Pi/Id injectivity) live in the separate convA/convB
-- fields of the REqValTy* records, not here.)
------------------------------------------------------------------------

record Red3 {n : Nat} (G : Ctx n) (M N A : Expr n) : Set where
  constructor mkRed3
  field
    hr : HeadRed M N
    ct : ConvTm G M N A

-- (RValId / REqValId are now defined INSIDE OpenRecords: the ML-J ty-J driver
-- needs the SEMANTIC witness-to-endpoint equalities endEqL/endEqR : EV2 wit0 ≈
-- lhs0/rhs0 at the witness value-code w, which reference the abstract EV2
-- (predecessor) relation.)

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
  -- Ref value at an Id type A.  Carries the syntactic reduction data
  -- (redTm + witness conversions) AND the SEMANTIC witness-to-endpoint
  -- equalities endEqL/endEqR : the witness `wit0` is EqVal2-equal to each
  -- endpoint (lhs0/rhs0) at the witness value-code w, type-code t.  These feed
  -- the ML-J motive-transport (C's PiEdgeEq2 edges) in the ty-J driver.
  ------------------------------------------------------------------------

  record RValId {n : Nat} (G : Ctx n) (M A : Expr n) (w t u v : FinEl) : Set where
    inductive
    field
      domA0 : Expr n
      lhs0  : Expr n
      rhs0  : Expr n
      red   : Red3 G A (Id domA0 lhs0 rhs0) U
      wit0   : Expr n
      redTm  : Red3 G M (Ref wit0) A
      refConvL : ConvTm G wit0 lhs0 domA0
      refConvR : ConvTm G wit0 rhs0 domA0
      refMem : FinMem (RefEl w) (IdCode t u v)
      endEqL : EV2 G wit0 lhs0 domA0 w t
      endEqR : EV2 G wit0 rhs0 domA0 w t

  record REqValId {n : Nat} (G : Ctx n) (M N A : Expr n) (w t u v : FinEl) : Set where
    inductive
    field
      domA0 : Expr n
      lhs0  : Expr n
      rhs0  : Expr n
      red   : Red3 G A (Id domA0 lhs0 rhs0) U
      wit0M : Expr n
      wit0N : Expr n
      redTmM : Red3 G M (Ref wit0M) A
      redTmN : Red3 G N (Ref wit0N) A
      refMem : FinMem (RefEl w) (IdCode t u v)
      endEqLM : EV2 G wit0M lhs0 domA0 w t
      endEqRM : EV2 G wit0M rhs0 domA0 w t
      endEqLN : EV2 G wit0N lhs0 domA0 w t
      endEqRN : EV2 G wit0N rhs0 domA0 w t

  ------------------------------------------------------------------------
  -- Id records.  An Id type Id A a b evaluates to (IdCode t u v) with
  -- t = A's type-code, u = a's value-code, v = b's value-code.  There is
  -- NO Selection edge (Id is a Prop): the components A@t, a@u, b@v carry
  -- ordinary predecessor-level validity, and proofs are proof-irrelevant.
  ------------------------------------------------------------------------

  record RValTyId {n : Nat} (G : Ctx n) (M : Expr n) (t u v : FinEl) : Set where
    inductive
    field
      domA : Expr n
      lhs  : Expr n
      rhs  : Expr n
      red  : Red3 G M (Id domA lhs rhs) U
      htA  : HasType G domA U
      htL  : HasType G lhs domA
      htR  : HasType G rhs domA
      valA : VT2 G domA t
      -- Endpoints carried at the MEMBERSHIP level (paper Lemma 2, `finMem-Sup-both`).
      valL : FinMem u t
      valR : FinMem v t
      -- LOGICAL endpoint validity (needed to build the diagonal REqValTyId's
      -- eqL/eqR by Val2-to-EqVal2 reflexivity, and to feed the ML-J motive edges).
      valLlog : V2 G lhs domA u t
      valRlog : V2 G rhs domA v t

  record REqValTyId {n : Nat} (G : Ctx n) (M N : Expr n) (t u v : FinEl) : Set where
    inductive
    field
      domA  : Expr n
      lhs   : Expr n
      rhs   : Expr n
      domA' : Expr n
      lhs'  : Expr n
      rhs'  : Expr n
      redM  : Red3 G M (Id domA lhs rhs) U
      redN  : Red3 G N (Id domA' lhs' rhs') U
      convA : ConvTm G domA domA' U
      convL : ConvTm G lhs lhs' domA
      convR : ConvTm G rhs rhs' domA
      eqA   : EVT2 G domA domA' t
      -- REDUCIBLE endpoint equalities (graded-type-theory's Id₌.lhs≡lhs′), needed
      -- to forward-transport the value-record endEq across a type conversion (Vfwd).
      eqL   : EV2 G lhs lhs' domA u t
      eqR   : EV2 G rhs rhs' domA v t

  ------------------------------------------------------------------------
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
    vty G M Bot            = Top
    vty G M UCode          = Red3 G M U U
    vty G M (FunEl g)      = Top
    vty G M (PiCode b f)   = RValTyPi G M b f
    vty G M (IdCode t u v) = RValTyId G M t u v
    vty G M (RefEl w)      = Top

    evty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
    evty G M N Bot          = Top
    evty G M N UCode        = Pair (Red3 G M U U) (Red3 G N U U)
    evty G M N (FunEl g)    = Top
    evty G M N (PiCode b f) =
      Pair (RValTyPi G M b f)
           (Pair (RValTyPi G N b f) (REqValTyPi G M N b f))
    evty G M N (IdCode t u v) =
      Pair (RValTyId G M t u v)
           (Pair (RValTyId G N t u v) (REqValTyId G M N t u v))
    evty G M N (RefEl w)    = Top

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
    vl G M A (IdCode t u v) UCode   = Pair (vty G A UCode) (vty G M (IdCode t u v))
    vl G M A u UCode                = Top
    vl G M A u (FunEl h)            = Top
    vl G M A (FunEl g) (PiCode b f) = Pair (vty G A (PiCode b f)) (RValPi G M A g b f)
    vl G M A u (PiCode b f)         = Top
    vl G M A (RefEl w) (IdCode t' u' v') =
      Pair (vty G A (IdCode t' u' v')) (RValId G M A w t' u' v')
    vl G M A u (IdCode t' u' v')    = Top
    vl G M A u (RefEl w)            = Top

    evl : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    evl G M N A u Bot                  = Top
    evl G M N A UCode UCode            =
      Pair (vty G A UCode)
           (Pair (vty G M UCode) (Pair (vty G N UCode) (evty G M N UCode)))
    evl G M N A (PiCode a' f') UCode   =
      Pair (vty G A UCode)
           (Pair (vty G M (PiCode a' f'))
                 (Pair (vty G N (PiCode a' f')) (evty G M N (PiCode a' f'))))
    evl G M N A (IdCode t u v) UCode   =
      Pair (vty G A UCode)
           (Pair (vty G M (IdCode t u v))
                 (Pair (vty G N (IdCode t u v)) (evty G M N (IdCode t u v))))
    evl G M N A u UCode                = Top
    evl G M N A u (FunEl h)            = Top
    evl G M N A (FunEl g) (PiCode b f) =
      Pair (vty G A (PiCode b f))
           (Pair (RValPi G M A g b f)
                 (Pair (RValPi G N A g b f) (REqValPi G M N A g b f)))
    evl G M N A u (PiCode b f)         = Top
    evl G M N A (RefEl w) (IdCode t' u' v') =
      Pair (vty G A (IdCode t' u' v'))
           (Pair (RValId G M A w t' u' v')
                 (Pair (RValId G N A w t' u' v') (REqValId G M N A w t' u' v')))
    evl G M N A u (IdCode t' u' v')    = Top
    evl G M N A u (RefEl w)            = Top

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
