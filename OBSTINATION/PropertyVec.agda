{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PropertyVec
--
-- JOINT ultimate obstination: r functions obstinate at a point A, all
-- sharing ONE finite approximant A0 <= A.
--
--   UOfam fs r A = Sigma A0. Below A0 A * ((i < r) -> UOat (fs i) A A0)
--
-- This is the interface the mutual-recursion generalisation needs: a
-- system of r mutually defined functions is analysed at a single
-- approximant, with r independent verdicts over it.
--
-- MAIN RESULT (`UOfam-iso`): the joint property is EQUIVALENT to the
-- conjunction of the r componentwise `UO`s -- sharing the approximant
-- costs nothing.  Two ingredients:
--
--   * each case is upward-stable in the approximant  (`PropertyAt.UOat-up`);
--   * approximants below a common A have joins       (`JoinD.Below-joinT`),
--     because every principal ideal of D is a chain.
--
-- `UOM` specialises the family to the components of a tuple-valued
-- function F : FTup -> FTup, which is how the mutual step function
-- <h_1,...,h_r> will be packaged.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PropertyVec where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Meet using (BndT ; joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.Property
open import OBSTINATION.PropertyAt
open import OBSTINATION.JoinD using (BndT-from-Below ; Below-joinT)
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike)

------------------------------------------------------------------------
-- Joint obstination of a family of r functions at a shared approximant
------------------------------------------------------------------------

UOfam : (Nat -> FTup -> FEl) -> Nat -> Tup -> Set
UOfam fs r A =
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      ((i : Nat) -> LeN (suc i) r -> UOat (fs i) A A0))

UOfamAll : (Nat -> FTup -> FEl) -> Nat -> Set
UOfamAll fs r = (A : Tup) -> UOfam fs r A

-- the componentwise statement it is to be compared with
UOeach : (Nat -> FTup -> FEl) -> Nat -> Tup -> Set
UOeach fs r A = (i : Nat) -> LeN (suc i) r -> UO (fs i) A

------------------------------------------------------------------------
-- Easy direction: a shared approximant gives each component separately
------------------------------------------------------------------------

-- `r` is explicit: UOfam is a definition, so r occurs only under a Pi body
-- and cannot be recovered by unification from the argument's type.
UOfam-each : (fs : Nat -> FTup -> FEl) (r : Nat) (A : Tup) ->
  UOfam fs r A -> UOeach fs r A
UOfam-each fs r A (mkSigma A0 (mkSigma bel v)) i lt = UO-join A0 bel (v i lt)

------------------------------------------------------------------------
-- Main direction: the r approximants can be joined into one
--
-- Induction on r.  At r = 0 take the bottom tuple below A.  At r = 1 + r'
-- split off component 0, recurse on the SHIFTED family  \ i -> fs (suc i),
-- then join the two approximants and lift both verdicts by `UOat-up`.
------------------------------------------------------------------------

UOfam-build : (fs : Nat -> FTup -> FEl) (r : Nat) (A : Tup) ->
  UOeach fs r A -> UOfam fs r A
UOfam-build fs zero A h =
  mkSigma (botLike A) (mkSigma (Below-botLike A) (\ i ()))
UOfam-build fs (suc r') A h = mkSigma J (mkSigma belJ verdicts)
  where
    -- component 0
    s0 = UO-split (h zero tt)
    B0 : FTup
    B0 = fst s0
    bel0 : Below B0 A
    bel0 = fst (snd s0)
    v0 : UOat (fs zero) A B0
    v0 = snd (snd s0)

    -- components 1 .. r', by the induction hypothesis on the shifted family
    rest = UOfam-build (\ i -> fs (suc i)) r' A (\ i lt -> h (suc i) lt)
    B1 : FTup
    B1 = fst rest
    bel1 : Below B1 A
    bel1 = fst (snd rest)
    v1 : (i : Nat) -> LeN (suc i) r' -> UOat (fs (suc i)) A B1
    v1 = snd (snd rest)

    -- the two approximants are bounded (both below A), so they join
    bnd : BndT B0 B1
    bnd = BndT-from-Below bel0 bel1

    J : FTup
    J = joinT B0 B1

    belJ : Below J A
    belJ = Below-joinT bel0 bel1

    leJ0 : LeFTup B0 J
    leJ0 = join-ubT-l bnd

    leJ1 : LeFTup B1 J
    leJ1 = join-ubT-r bnd

    verdicts : (i : Nat) -> LeN (suc i) (suc r') -> UOat (fs i) A J
    verdicts zero    lt = UOat-up v0 leJ0 belJ
    verdicts (suc i) lt = UOat-up (v1 i lt) leJ1 belJ

------------------------------------------------------------------------
-- Joint obstination is exactly componentwise obstination
------------------------------------------------------------------------

UOfam-iso : (fs : Nat -> FTup -> FEl) (r : Nat) (A : Tup) ->
  Pair (UOfam fs r A -> UOeach fs r A) (UOeach fs r A -> UOfam fs r A)
UOfam-iso fs r A = mkSigma (UOfam-each fs r A) (UOfam-build fs r A)

------------------------------------------------------------------------
-- Specialisation to a tuple-valued function
--
-- F : FTup -> FTup packages <f_1,...,f_r>; component i is  getF i o F.
-- This is the shape the mutual step function will take.
------------------------------------------------------------------------

compOf : (FTup -> FTup) -> Nat -> FTup -> FEl
compOf F i X = getF i (F X)

UOM : (FTup -> FTup) -> Nat -> Tup -> Set
UOM F r A = UOfam (compOf F) r A

UOMall : (FTup -> FTup) -> Nat -> Set
UOMall F r = (A : Tup) -> UOM F r A

UOM-build : (F : FTup -> FTup) (r : Nat) (A : Tup) ->
  ((i : Nat) -> LeN (suc i) r -> UO (compOf F i) A) -> UOM F r A
UOM-build F r A h = UOfam-build (compOf F) r A h

UOM-each : (F : FTup -> FTup) (r : Nat) (A : Tup) ->
  UOM F r A -> (i : Nat) -> LeN (suc i) r -> UO (compOf F i) A
UOM-each F r A u = UOfam-each (compOf F) r A u

-- and pointwise over all points
UOMall-build : (F : FTup -> FTup) (r : Nat) ->
  ((i : Nat) -> LeN (suc i) r -> UOall (compOf F i)) -> UOMall F r
UOMall-build F r h A = UOM-build F r A (\ i lt -> h i lt A)
