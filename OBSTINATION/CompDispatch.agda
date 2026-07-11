{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompDispatch
--
-- The GENERIC composition of ultimate obstination: if g satisfies the
-- property everywhere and every inner function f_j (packaged as a UOFun)
-- does too, then  X |-> g (mapU fs X)  satisfies it at every point A.
-- Dispatch on g's case at the inner point B = <ext f_j A> and route to
-- the three builders.
--
-- Instantiating fs to the tuple of evalF-interpretations of a `List PR`
-- recovers the composition case of Proposition 1 (`prop1-comp`), via a
-- pointwise-equality transport (`mapU (bundlePR hs au) = mapE hs`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompDispatch where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.CompPull using
  (UOFun ; ufn ; mapU ; innerPtU ; compFn ; UO-pointwise)
open import OBSTINATION.CompCase1 using (comp-Case1-build)
open import OBSTINATION.CompCase2 using (comp-Case2-build)
open import OBSTINATION.CompCase3 using (comp-Case3-build)

------------------------------------------------------------------------
-- Generic composition over an arbitrary inner tuple of UOFuns
------------------------------------------------------------------------

prop1-compose : (gf : FTup -> FEl) -> UOall gf ->
  (fs : List UOFun) (A : Tup) -> UO (compFn gf fs) A
prop1-compose gf uog fs A with uog (innerPtU fs A)
... | uo1 c = uo1 (comp-Case1-build gf fs A c)
... | uo2 c = comp-Case2-build gf fs A c
... | uo3 c = uo3 (comp-Case3-build gf fs A c)

------------------------------------------------------------------------
-- Compatibility layer: composition of PR terms
------------------------------------------------------------------------

AllUO : List PR -> Set
AllUO nil         = Top
AllUO (cons h hs) = Pair (UOall (evalF h)) (AllUO hs)

-- bundle each  evalF h  with its obstination proof and its monotonicity
bundlePR : (hs : List PR) -> AllUO hs -> List UOFun
bundlePR nil         au = nil
bundlePR (cons h hs) au =
  cons (mkSigma (evalF h) (mkSigma (fst au) (evalF-mono h))) (bundlePR hs (snd au))

-- the bundled runtime action is exactly mapE
mapU-bundle-eq : (hs : List PR) (au : AllUO hs) (X : FTup) ->
  Eq (mapU (bundlePR hs au) X) (mapE hs X)
mapU-bundle-eq nil         au X = refl
mapU-bundle-eq (cons h hs) au X = Eq-cong (cons (evalF h X)) (mapU-bundle-eq hs (snd au) X)

prop1-comp : (g : PR) (hs : List PR) ->
  UOall (evalF g) -> AllUO hs -> (A : Tup) ->
  UO (evalF (comp g hs)) A
prop1-comp g hs uog au A =
  UO-pointwise (\ X -> Eq-cong (evalF g) (mapU-bundle-eq hs au X))
    (prop1-compose (evalF g) uog (bundlePR hs au) A)
