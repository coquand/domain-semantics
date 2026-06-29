{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityPublic.agda  (NAT/ — Pi + U fragment)
--
-- The index-free public validity API for the adequacy stack, replacing
-- the old ValidityLemmas/ValidityCore/ValidityFwd/ValiditySymTrans/
-- ValiditySup re-export bundle.
--
-- It gathers, under the *old bare names* (so the adequacy stack needs
-- minimal churn):
--   * the stratified public relations Val2/EqVal2/ValTy2/EqValTy2 + Red3
--     (from ValidityStratified);
--   * the public-level Pi records + (un)builders (from AdequacyRecords),
--     renamed RValTyPiP -> RValTyPi etc. and PiEdgeVal2P -> PiEdgeVal2 etc.;
--   * the property package as thin wrappers over the *-pub lemmas
--     (from ValidityLevels), matching the original implicit/explicit
--     argument conventions.
--
-- No postulates.
------------------------------------------------------------------------

module NAT.Validity.Public where

open import NAT.Domain.Basic using (Nat ; zero ; suc ; max ; FinEl)
open import NAT.Syntax.Raw using (Expr)
open import NAT.Syntax.Typing using (Ctx ; HasType ; ConvTm)
open import NAT.Domain.Kernel using (Coherent)
open import NAT.Domain.Rank using (RANK)

-- relations + Red3 (Stage/Bundle/OpenRecords come along, harmlessly)
open import NAT.Validity.Stratified public

-- public records + (un)builders, under the old names
open import NAT.Adequacy.Records public
  renaming ( RValTyPiP   to RValTyPi
           ; REqValTyPiP to REqValTyPi
           ; RValPiP     to RValPi
           ; REqValPiP   to REqValPi
           ; PiEdgeVal2P to PiEdgeVal2
           ; PiEdgeEq2P  to PiEdgeEq2
           ; PiEdgeEqTy2P to PiEdgeEqTy2
           ; PiAppVal2P  to PiAppVal2
           ; PiAppEq2P   to PiAppEq2
           ; PiAppEqVal2P to PiAppEqVal2 )

-- Red3-unique-Pi over ValidityStratified.Red3
open import NAT.Validity.Mono using (MonoPack ; goodStage) public
open import NAT.Validity.Mono using (Red3-unique-Pi) public

-- property lemmas whose *-pub signature already matches the originals
open import NAT.Validity.Levels public
  using ( Val2-EqValTy2-fwd-pub ; EqVal2-EqValTy2-fwd-pub
        ; Val2-type-transport-pub ; EqVal2-type-transport-pub
        ; Val2-beta-expand-pub )
  renaming ( downVal2-pub          to downVal2
           ; downEqVal2-pub        to downEqVal2
           ; downValTy2-pub        to downValTy2
           ; downEqValTy2-pub      to downEqValTy2
           ; upVal2-pub            to upVal2
           ; upEqVal2-pub          to upEqVal2
           ; restrictVal2-pub      to restrictVal2
           ; restrictEqVal2-pub    to restrictEqVal2
           ; EqValTy2-sym-pub      to EqValTy2-sym
           ; EqValTy2-trans-pub    to EqValTy2-trans
           ; EqVal2-sym-pub        to EqVal2-sym
           ; EqVal2-trans-pub      to EqVal2-trans
           ; ValTy2-Sup-pub        to ValTy2-Sup
           ; EqValTy2-Sup-pub      to EqValTy2-Sup
           ; Val2-Bot-pub          to Val2-Bot
           ; EqVal2-Bot-pub        to EqVal2-Bot
           ; Val2-to-EqVal2-pub    to Val2-to-EqVal2
           ; ValTy2-to-EqValTy2-pub to ValTy2-to-EqValTy2 )

------------------------------------------------------------------------
-- Thin wrappers restoring the original implicit-argument conventions
-- for the fwd / type-transport lemmas (the *-pub versions make the
-- context and expressions explicit).
------------------------------------------------------------------------

Val2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b -> Val2 G M C u b -> Val2 G M C' u b
Val2-EqValTy2-fwd {G = G} {C} {C'} {M} u b cb eqv val =
  Val2-EqValTy2-fwd-pub G M C C' u b cb eqv val

EqVal2-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy2 G C C' b -> EqVal2 G M N C u b -> EqVal2 G M N C' u b
EqVal2-EqValTy2-fwd {G = G} {C} {C'} {M} {N} u b cb eqv ev =
  EqVal2-EqValTy2-fwd-pub G M N C C' u b cb eqv ev

Val2-type-transport : {n : Nat} {G : Ctx n} {C C' N : Expr n}
  (u a : FinEl) -> EqValTy2 G C C' a -> Val2 G N C u a -> Val2 G N C' u a
Val2-type-transport {G = G} {C} {C'} {N} u a eqvt val =
  Val2-type-transport-pub G C C' N u a eqvt val

EqVal2-type-transport : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
  (u a : FinEl) -> EqValTy2 G C C' a -> EqVal2 G M N C u a -> EqVal2 G M N C' u a
EqVal2-type-transport {G = G} {C} {C'} {M} {N} u a eqvt ev =
  EqVal2-type-transport-pub G C C' M N u a eqvt ev

------------------------------------------------------------------------
-- Val2-from-EqVal2-first / second : non-recursive MonoPack projections,
-- consumed directly at the canonical level (no shift needed).
------------------------------------------------------------------------

Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
Val2-from-EqVal2-first u a ev =
  MonoPack.Val2-from-EqVal2-first (goodStage (suc (max (RANK u) (RANK a)))) u a ev

Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
Val2-from-EqVal2-second u a ev =
  MonoPack.Val2-from-EqVal2-second (goodStage (suc (max (RANK u) (RANK a)))) u a ev
