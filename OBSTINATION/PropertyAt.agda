{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PropertyAt
--
-- The ultimate-obstination property with the approximant SPLIT OUT.
--
-- `Property.UO f A` bundles the finite approximant A0 <= A inside each of
-- the three cases.  For the mutual-recursion generalisation one needs the
-- three cases at a FIXED A0, so that r functions can share one approximant
-- (see `PropertyVec`).  This file provides that form:
--
--   Case1at f A0     Case2at f A A0     Case3at f A A0     UOat f A A0
--
-- and it is set up so that
--
--   Case1 f A  =  Sigma FTup (\ A0 -> Pair (Below A0 A) (Case1at f A0))
--
-- holds DEFINITIONALLY (likewise for Case2/Case3) -- see the `-refold`
-- identities below.  Nothing in `Property.agda` is changed, so the 64
-- existing modules are untouched.
--
-- The content of the file is the upward-stability of each case in the
-- approximant (`Case1at-up`, `Case2at-up`, `Case3at-up`, `UOat-up`):
-- a verdict at A0 is still a verdict at any larger A0' still below A.
-- That is what makes a shared approximant obtainable by joining.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PropertyAt where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using
  (embed-inj ; get-embedTup ; LeFTup-length ; del-LeFTup)
open import OBSTINATION.CompPull using (LeFTup-trans)

------------------------------------------------------------------------
-- The three cases at a fixed approximant A0
------------------------------------------------------------------------

-- 1. eventually constant complete
Case1at : (FTup -> FEl) -> FTup -> Set
Case1at f A0 =
  Sigma Nat (\ m -> (X : FTup) -> LeFTup A0 X -> Eq (f X) (fcpl m))

-- 2. eventually constant incomplete, pinned at coordinate i
Case2at : (FTup -> FEl) -> Tup -> FTup -> Set
Case2at f A A0 =
  Sigma Nat (\ m ->
    Sigma Nat (\ i ->
      Pair (LeN (suc i) (length A0))
      (Pair (IncompleteFinite (get i A))
      (Pair (Eq (embed (getF i A0)) (get i A))
        ((X : FTup) ->
           Eq (length X) (length A0) ->
           Eq (getF i X) (getF i A0) ->
           LeFTup (del i A0) (del i X) ->
           Eq (f X) (fbot m))))))

-- 3. the infinite coordinate, governed by the witness phi
Case3at : (FTup -> FEl) -> Tup -> FTup -> Set
Case3at f A A0 =
  Sigma Nat (\ i ->
    Pair (Eq (get i A) inf)
    (Sigma Nat (\ k ->
      Pair (Eq (getF i A0) (fbot k))
      (Sigma (Nat -> Nat) (\ phi ->
        Pair (PhiOK k phi)
          ((X : FTup) (m : Nat) ->
             Eq (length X) (length A0) ->
             LeN k m ->
             Eq (getF i X) (fbot m) ->
             LeFTup (del i A0) (del i X) ->
             Eq (f X) (fbot (phi m))))))))

------------------------------------------------------------------------
-- Agreement with Property.agda -- these hold by refl, which is exactly
-- the point: the split form is not a new definition, only a reassociation.
------------------------------------------------------------------------

-- `Eq` is Set-monomorphic here, so the agreement is stated as identity
-- functions in both directions: each typechecks exactly because the two
-- descriptions are definitionally the same type.

Case1-unfold : (f : FTup -> FEl) (A : Tup) ->
  Case1 f A -> Sigma FTup (\ A0 -> Pair (Below A0 A) (Case1at f A0))
Case1-unfold f A c = c

Case1-fold : (f : FTup -> FEl) (A : Tup) ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (Case1at f A0)) -> Case1 f A
Case1-fold f A c = c

Case2-unfold : (f : FTup -> FEl) (A : Tup) ->
  Case2 f A -> Sigma FTup (\ A0 -> Pair (Below A0 A) (Case2at f A A0))
Case2-unfold f A c = c

Case2-fold : (f : FTup -> FEl) (A : Tup) ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (Case2at f A A0)) -> Case2 f A
Case2-fold f A c = c

Case3-unfold : (f : FTup -> FEl) (A : Tup) ->
  Case3 f A -> Sigma FTup (\ A0 -> Pair (Below A0 A) (Case3at f A A0))
Case3-unfold f A c = c

Case3-fold : (f : FTup -> FEl) (A : Tup) ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (Case3at f A A0)) -> Case3 f A
Case3-fold f A c = c

------------------------------------------------------------------------
-- The property at a fixed approximant, and the split / join isomorphism
------------------------------------------------------------------------

data UOat (f : FTup -> FEl) (A : Tup) (A0 : FTup) : Set where
  uo1at : Case1at f A0   -> UOat f A A0
  uo2at : Case2at f A A0 -> UOat f A A0
  uo3at : Case3at f A A0 -> UOat f A A0

UO-split : {f : FTup -> FEl} {A : Tup} -> UO f A ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (UOat f A A0))
UO-split (uo1 (mkSigma A0 (mkSigma bel c))) = mkSigma A0 (mkSigma bel (uo1at c))
UO-split (uo2 (mkSigma A0 (mkSigma bel c))) = mkSigma A0 (mkSigma bel (uo2at c))
UO-split (uo3 (mkSigma A0 (mkSigma bel c))) = mkSigma A0 (mkSigma bel (uo3at c))

UO-join : {f : FTup -> FEl} {A : Tup} (A0 : FTup) ->
  Below A0 A -> UOat f A A0 -> UO f A
UO-join A0 bel (uo1at c) = uo1 (mkSigma A0 (mkSigma bel c))
UO-join A0 bel (uo2at c) = uo2 (mkSigma A0 (mkSigma bel c))
UO-join A0 bel (uo3at c) = uo3 (mkSigma A0 (mkSigma bel c))

-- splitting then rejoining is the identity
UO-join-split : {f : FTup -> FEl} {A : Tup} (u : UO f A) ->
  Eq (UO-join (fst (UO-split u)) (fst (snd (UO-split u))) (snd (snd (UO-split u)))) u
UO-join-split (uo1 (mkSigma A0 (mkSigma bel c))) = refl
UO-join-split (uo2 (mkSigma A0 (mkSigma bel c))) = refl
UO-join-split (uo3 (mkSigma A0 (mkSigma bel c))) = refl

------------------------------------------------------------------------
-- Coordinate order, from the tuple order and from Below
------------------------------------------------------------------------

getF-le : (i : Nat) {A0 A0' : FTup} -> LeFTup A0 A0' -> LeF (getF i A0) (getF i A0')
getF-le i {A0} {A0'} le =
  Eq-transport (\ z -> LeD z (embed (getF i A0'))) (get-embedTup i A0)
    (Eq-transport (\ z -> LeD (get i (embedTup A0)) z) (get-embedTup i A0')
      (LeTup-get i {embedTup A0} {embedTup A0'} le))

getF-below : (i : Nat) {A0 : FTup} {A : Tup} ->
  Below A0 A -> LeD (embed (getF i A0)) (get i A)
getF-below i {A0} {A} bel =
  Eq-transport (\ z -> LeD z (get i A)) (get-embedTup i A0)
    (LeTup-get i {embedTup A0} {A} bel)

------------------------------------------------------------------------
-- Case 1 is upward-stable in the approximant
--
-- Enlarging A0 only restricts the quantified X, so the universal clause
-- survives.  (No `Below A0' A` needed here.)
------------------------------------------------------------------------

Case1at-up : {f : FTup -> FEl} {A0 A0' : FTup} ->
  Case1at f A0 -> LeFTup A0 A0' -> Case1at f A0'
Case1at-up (mkSigma m univ) le =
  mkSigma m (\ X leX -> univ X (LeFTup-trans le leX))

------------------------------------------------------------------------
-- Case 2 is upward-stable in the approximant
--
-- The pinned coordinate i satisfies  embed (getF i A0) = get i A, so it is
-- already maximal below A and cannot grow: getF i A0' = getF i A0 by
-- antisymmetry.  Growth off i only strengthens the deletion hypothesis.
------------------------------------------------------------------------

Case2at-up : {f : FTup -> FEl} {A : Tup} {A0 A0' : FTup} ->
  Case2at f A A0 -> LeFTup A0 A0' -> Below A0' A -> Case2at f A A0'
Case2at-up {f} {A} {A0} {A0'}
  (mkSigma m (mkSigma i (mkSigma irng (mkSigma inc (mkSigma eqA0 univ))))) le bel' =
  mkSigma m (mkSigma i (mkSigma irng' (mkSigma inc (mkSigma eqA0' univ'))))
  where
    lenEq : Eq (length A0) (length A0')
    lenEq = LeFTup-length le

    irng' : LeN (suc i) (length A0')
    irng' = Eq-transport (\ n -> LeN (suc i) n) lenEq irng

    -- get i A <= embed (getF i A0'), by  get i A = embed (getF i A0) <= ...
    lowerA : LeD (get i A) (embed (getF i A0'))
    lowerA = Eq-transport (\ z -> LeD z (embed (getF i A0'))) eqA0 (getF-le i le)

    eqA0' : Eq (embed (getF i A0')) (get i A)
    eqA0' = LeD-antisym {embed (getF i A0')} {get i A} (getF-below i bel') lowerA

    coordEq : Eq (getF i A0') (getF i A0)
    coordEq = embed-inj (Eq-trans eqA0' (Eq-sym eqA0))

    univ' : (X : FTup) ->
            Eq (length X) (length A0') ->
            Eq (getF i X) (getF i A0') ->
            LeFTup (del i A0') (del i X) ->
            Eq (f X) (fbot m)
    univ' X lenX coordX delX =
      univ X (Eq-trans lenX (Eq-sym lenEq))
             (Eq-trans coordX coordEq)
             (LeFTup-trans (del-LeFTup i le) delX)

------------------------------------------------------------------------
-- Case 3 is upward-stable in the approximant
--
-- Here get i A = inf, so the coordinate CAN grow -- but only within the
-- incomplete elements, since LeD (cpl j) inf is Empty.  So A0'(i) = fbot k'
-- with k <= k', and both halves of PhiOK restrict from k to k'.
------------------------------------------------------------------------

-- an element below inf is incomplete
below-inf-shape : (x : FEl) -> LeD (embed x) inf -> Sigma Nat (\ k -> Eq x (fbot k))
below-inf-shape (fbot k) le = mkSigma k refl
below-inf-shape (fcpl k) ()

Case3at-up : {f : FTup -> FEl} {A : Tup} {A0 A0' : FTup} ->
  Case3at f A A0 -> LeFTup A0 A0' -> Below A0' A -> Case3at f A A0'
Case3at-up {f} {A} {A0} {A0'}
  (mkSigma i (mkSigma einf (mkSigma k (mkSigma ek (mkSigma phi (mkSigma ok univ))))))
  le bel' =
  mkSigma i (mkSigma einf (mkSigma k' (mkSigma ek' (mkSigma phi (mkSigma ok' univ')))))
  where
    lenEq : Eq (length A0) (length A0')
    lenEq = LeFTup-length le

    coordLe : LeD (embed (getF i A0')) inf
    coordLe = Eq-transport (\ z -> LeD (embed (getF i A0')) z) einf (getF-below i bel')

    shape = below-inf-shape (getF i A0') coordLe

    k' : Nat
    k' = fst shape

    ek' : Eq (getF i A0') (fbot k')
    ek' = snd shape

    kle : LeN k k'
    kle = Eq-transport (\ z -> LeD (embed z) (embed (fbot k'))) ek
            (Eq-transport (\ z -> LeD (embed (getF i A0)) (embed z)) ek'
              (getF-le i le))

    ok' : PhiOK k' phi
    ok' = shift ok
      where
        shift : PhiOK k phi -> PhiOK k' phi
        shift (inl cst) =
          inl (\ m km -> Eq-trans (cst m (LeN-trans {k} {k'} {m} kle km))
                                  (Eq-sym (cst k' kle)))
        shift (inr sinc) =
          inr (\ m km -> sinc m (LeN-trans {k} {k'} {m} kle km))

    univ' : (X : FTup) (m : Nat) ->
            Eq (length X) (length A0') ->
            LeN k' m ->
            Eq (getF i X) (fbot m) ->
            LeFTup (del i A0') (del i X) ->
            Eq (f X) (fbot (phi m))
    univ' X m lenX km coordX delX =
      univ X m (Eq-trans lenX (Eq-sym lenEq))
               (LeN-trans {k} {k'} {m} kle km)
               coordX
               (LeFTup-trans (del-LeFTup i le) delX)

------------------------------------------------------------------------
-- Hence the whole property is upward-stable in the approximant
------------------------------------------------------------------------

UOat-up : {f : FTup -> FEl} {A : Tup} {A0 A0' : FTup} ->
  UOat f A A0 -> LeFTup A0 A0' -> Below A0' A -> UOat f A A0'
UOat-up (uo1at c) le bel = uo1at (Case1at-up c le)
UOat-up (uo2at c) le bel = uo2at (Case2at-up c le bel)
UOat-up (uo3at c) le bel = uo3at (Case3at-up c le bel)
