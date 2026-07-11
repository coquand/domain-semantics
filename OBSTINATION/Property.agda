{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Property
--
-- The ultimate-obstination property, Section 1 of the note.  A monotone
-- function  f : F^n -> F  (here abstractly  f : FTup -> FEl) satisfies
-- the property at a point  A in D^n  when there is a finite  A0 <= A
-- such that one of three cases holds:
--
--   1. exists m,  f(X) = S^m(0)     for all finite X >= A0;
--
--   2. exists m and a coordinate i with A(i) incomplete & finite,
--      A0(i) = A(i),  and  f(X) = S^m(bot)  for all finite X with
--      X(i) = A0(i)  and  X[i] >= A0[i];
--
--   3. a coordinate i with A(i) = S^omega(bot); with k such that
--      A0(i) = S^k(bot), a numeric function phi (defined for m >= k),
--      constant or strictly increasing, with  f(X) = S^{phi(m)}(bot)
--      for all finite X with  X(i) = S^m(bot),  k <= m,  A0[i] <= X[i].
--
-- Existence and disjunction are read intuitionistically, so from the
-- property one can compute the value f-hat(A) of the Scott-continuous
-- extension at A: this is `uoValue` below (page 2 of the note).
--
-- This file is definitions plus one total function -- no postulates, no
-- holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Property where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples

------------------------------------------------------------------------
-- Coordinate access on finite tuples
------------------------------------------------------------------------

getF : Nat -> FTup -> FEl
getF i A = nth (fbot zero) i A

------------------------------------------------------------------------
-- Shapes of a domain element
------------------------------------------------------------------------

-- incomplete and finite:  of the form S^k(bot)
IncompleteFinite : D -> Set
IncompleteFinite (bot k) = Top
IncompleteFinite (cpl k) = Empty
IncompleteFinite inf     = Empty

------------------------------------------------------------------------
-- Witness numeric functions phi : constant, or strictly increasing,
-- from the threshold k onwards.
------------------------------------------------------------------------

ConstFrom : Nat -> (Nat -> Nat) -> Set
ConstFrom k phi = (m : Nat) -> LeN k m -> Eq (phi m) (phi k)

StrictIncFrom : Nat -> (Nat -> Nat) -> Set
StrictIncFrom k phi = (m : Nat) -> LeN k m -> LeN (suc (phi m)) (phi (suc m))

PhiOK : Nat -> (Nat -> Nat) -> Set
PhiOK k phi = Or (ConstFrom k phi) (StrictIncFrom k phi)

------------------------------------------------------------------------
-- The three cases of the property, at f and A, over a finite A0 <= A.
------------------------------------------------------------------------

-- A0 is a finite approximant below the (possibly infinite) point A
Below : FTup -> Tup -> Set
Below A0 A = LeTup (embedTup A0) A

-- 1. eventually constant complete
Case1 : (FTup -> FEl) -> Tup -> Set
Case1 f A =
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      (Sigma Nat (\ m ->
        (X : FTup) -> LeFTup A0 X -> Eq (f X) (fcpl m))))

-- 2. eventually constant incomplete, pinned at coordinate i
Case2 : (FTup -> FEl) -> Tup -> Set
Case2 f A =
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      (Sigma Nat (\ m ->
        Sigma Nat (\ i ->
          Pair (LeN (suc i) (length A0))
          (Pair (IncompleteFinite (get i A))
          (Pair (Eq (embed (getF i A0)) (get i A))
            ((X : FTup) ->
               Eq (length X) (length A0) ->
               Eq (getF i X) (getF i A0) ->
               LeFTup (del i A0) (del i X) ->
               Eq (f X) (fbot m))))))))

-- 3. the infinite coordinate, governed by the witness phi
Case3 : (FTup -> FEl) -> Tup -> Set
Case3 f A =
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      (Sigma Nat (\ i ->
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
                 Eq (f X) (fbot (phi m))))))))))

------------------------------------------------------------------------
-- The property itself (a plain 3-constructor disjunction; the named
-- constructors are what we gain over a nested Or, and phase 3 will
-- pattern-match on them).
------------------------------------------------------------------------

data UO (f : FTup -> FEl) (A : Tup) : Set where
  uo1 : Case1 f A -> UO f A
  uo2 : Case2 f A -> UO f A
  uo3 : Case3 f A -> UO f A

-- "f satisfies the property" means: at every point of D^n.
UOall : (FTup -> FEl) -> Set
UOall f = (A : Tup) -> UO f A

------------------------------------------------------------------------
-- The value of the Scott-continuous extension at A, read off the
-- property (page 2: "on obtient directement la valeur de f(A) ...").
--
--   case 1:  S^m(0)                      = cpl m
--   case 2:  S^m(bot)                    = bot m
--   case 3:  sup_m S^{phi(m)}(bot)  =  bot (phi k)   if phi is constant
--                                    =  S^omega(bot)  if phi is strictly
--                                                     increasing (= inf)
------------------------------------------------------------------------

uoValue : {f : FTup -> FEl} {A : Tup} -> UO f A -> D
uoValue (uo1 (mkSigma _ (mkSigma _ (mkSigma m _)))) = cpl m
uoValue (uo2 (mkSigma _ (mkSigma _ (mkSigma m _)))) = bot m
uoValue (uo3 (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma k (mkSigma _ (mkSigma phi (mkSigma (inl _) _))))))))) = bot (phi k)
uoValue (uo3 (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma _ (mkSigma k (mkSigma _ (mkSigma phi (mkSigma (inr _) _))))))))) = inf

-- the extension value is always finite exactly when we are not in the
-- strictly-increasing sub-case of the infinite coordinate.
uoValue-finite-case1 : {f : FTup -> FEl} {A : Tup} (c : Case1 f A) ->
  Finite (uoValue (uo1 c))
uoValue-finite-case1 (mkSigma _ (mkSigma _ (mkSigma m _))) = tt

uoValue-finite-case2 : {f : FTup -> FEl} {A : Tup} (c : Case2 f A) ->
  Finite (uoValue (uo2 c))
uoValue-finite-case2 (mkSigma _ (mkSigma _ (mkSigma m _))) = tt
