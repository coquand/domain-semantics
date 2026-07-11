{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Prop1Base
--
-- Proposition 1, base cases (min1.pdf: "les fonctions constantes, les
-- projections, et la fonction successeur verifient clairement cette
-- propriete").  Each of the constant 0, a projection, and the successor
-- satisfies the ultimate-obstination property at every point.
--
--   * constant 0  -> Case 1 (eventually constant complete, m = 0);
--   * projection / successor at coordinate i, according to the shape of
--     A(i):  complete -> Case 1, incomplete finite -> Case 2,
--     infinite -> Case 3 (with phi the identity resp. successor).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Prop1Base where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (nthF-mono)

------------------------------------------------------------------------
-- The bottom approximant below a point
------------------------------------------------------------------------

botLike : Tup -> FTup
botLike nil         = nil
botLike (cons _ A)  = cons (fbot zero) (botLike A)

length-botLike : (A : Tup) -> Eq (length (botLike A)) (length A)
length-botLike nil        = refl
length-botLike (cons _ A) = Eq-cong suc (length-botLike A)

Below-botLike : (A : Tup) -> Below (botLike A) A
Below-botLike nil        = tt
Below-botLike (cons a A) = mkSigma (LeD-botD a) (Below-botLike A)

------------------------------------------------------------------------
-- Replacing one coordinate
------------------------------------------------------------------------

repl : Nat -> FEl -> FTup -> FTup
repl i       v nil         = nil
repl zero    v (cons x xs) = cons v xs
repl (suc i) v (cons x xs) = cons x (repl i v xs)

getF-repl : (i : Nat) (v : FEl) (T : FTup) ->
  LeN (suc i) (length T) -> Eq (getF i (repl i v T)) v
getF-repl zero    v (cons x xs) le = refl
getF-repl (suc i) v (cons x xs) le = getF-repl i v xs le
getF-repl zero    v nil ()
getF-repl (suc i) v nil ()

length-repl : (i : Nat) (v : FEl) (T : FTup) -> Eq (length (repl i v T)) (length T)
length-repl i       v nil         = refl
length-repl zero    v (cons x xs) = refl
length-repl (suc i) v (cons x xs) = Eq-cong suc (length-repl i v xs)

Below-repl : (i : Nat) (v : FEl) (A : Tup) ->
  LeD (embed v) (get i A) -> LeN (suc i) (length A) ->
  Below (repl i v (botLike A)) A
Below-repl zero    v (cons d A) ub le = mkSigma ub (Below-botLike A)
Below-repl (suc i) v (cons d A) ub le = mkSigma (LeD-botD d) (Below-repl i v A ub le)
Below-repl zero    v nil ub ()
Below-repl (suc i) v nil ub ()

------------------------------------------------------------------------
-- Complete elements are maximal
------------------------------------------------------------------------

fcpl-max : (m : Nat) (w : FEl) -> LeF (fcpl m) w -> Eq w (fcpl m)
fcpl-max m (fbot k) ()
fcpl-max m (fcpl k) p = Eq-cong fcpl (Eq-sym p)

------------------------------------------------------------------------
-- Constant 0
------------------------------------------------------------------------

prop1-zerf : (A : Tup) -> UO (evalF zerf) A
prop1-zerf A =
  uo1 (mkSigma (botLike A) (mkSigma (Below-botLike A) (mkSigma zero (\ X _ -> refl))))

------------------------------------------------------------------------
-- Successor  (unary; stated at any non-empty point cons a A')
------------------------------------------------------------------------

prop1-succ : (a : D) (A' : Tup) -> UO (evalF succ) (cons a A')
prop1-succ (cpl m) A' =
  uo1 (mkSigma (cons (fcpl m) (botLike A'))
        (mkSigma (mkSigma (LeD-refl (cpl m)) (Below-botLike A'))
          (mkSigma (suc m) univ)))
  where
    univ : (X : FTup) -> LeFTup (cons (fcpl m) (botLike A')) X ->
           Eq (evalF succ X) (fcpl (suc m))
    univ nil ()
    univ (cons x xs) leX = Eq-cong sucF (fcpl-max m x (fst leX))
prop1-succ (bot m) A' =
  uo2 (mkSigma (cons (fbot m) (botLike A'))
        (mkSigma (mkSigma (LeD-refl (bot m)) (Below-botLike A'))
          (mkSigma (suc m) (mkSigma zero (mkSigma tt (mkSigma tt (mkSigma refl univ)))))))
  where
    univ : (X : FTup) -> Eq (length X) (length (cons (fbot m) (botLike A'))) ->
           Eq (getF zero X) (getF zero (cons (fbot m) (botLike A'))) ->
           LeFTup (del zero (cons (fbot m) (botLike A'))) (del zero X) ->
           Eq (evalF succ X) (fbot (suc m))
    univ nil ()
    univ (cons x xs) leq hyp2 hlt = Eq-cong sucF hyp2
prop1-succ inf A' =
  uo3 (mkSigma (cons (fbot zero) (botLike A'))
        (mkSigma (mkSigma tt (Below-botLike A'))
          (mkSigma zero (mkSigma refl (mkSigma zero (mkSigma refl
            (mkSigma (\ m -> suc m) (mkSigma (inr (\ m _ -> LeN-refl (suc (suc m)))) univ))))))))
  where
    univ : (X : FTup) (mm : Nat) ->
           Eq (length X) (length (cons (fbot zero) (botLike A'))) ->
           LeN zero mm -> Eq (getF zero X) (fbot mm) ->
           LeFTup (del zero (cons (fbot zero) (botLike A'))) (del zero X) ->
           Eq (evalF succ X) (fbot (suc mm))
    univ nil mm ()
    univ (cons x xs) mm leq lek hyp hlt = Eq-cong sucF hyp

------------------------------------------------------------------------
-- Projection
------------------------------------------------------------------------

prop1-proj : (i : Nat) (A : Tup) -> LeN (suc i) (length A) -> UO (evalF (proj i)) A
prop1-proj i A ilt = go (get i A) refl
  where
    ilt' : LeN (suc i) (length (botLike A))
    ilt' = Eq-transport (\ n -> LeN (suc i) n) (Eq-sym (length-botLike A)) ilt

    go : (d : D) -> Eq (get i A) d -> UO (evalF (proj i)) A
    go (cpl m) e =
      uo1 (mkSigma A0 (mkSigma below (mkSigma m univ)))
      where
        A0 : FTup
        A0 = repl i (fcpl m) (botLike A)
        e0 : Eq (getF i A0) (fcpl m)
        e0 = getF-repl i (fcpl m) (botLike A) ilt'
        below : Below A0 A
        below = Below-repl i (fcpl m) A
                  (Eq-transport (\ z -> LeD (cpl m) z) (Eq-sym e) (LeD-refl (cpl m))) ilt
        univ : (X : FTup) -> LeFTup A0 X -> Eq (evalF (proj i) X) (fcpl m)
        univ X leX =
          fcpl-max m (getF i X)
            (Eq-transport (\ z -> LeF z (getF i X)) e0 (nthF-mono i {A0} {X} leX))
    go (bot m) e =
      uo2 (mkSigma A0 (mkSigma below
            (mkSigma m (mkSigma i (mkSigma inrange
              (mkSigma (Eq-transport IncompleteFinite (Eq-sym e) tt)
                (mkSigma (Eq-trans (Eq-cong embed e0) (Eq-sym e)) univ)))))))
      where
        A0 : FTup
        A0 = repl i (fbot m) (botLike A)
        inrange : LeN (suc i) (length A0)
        inrange = Eq-transport (\ n -> LeN (suc i) n)
                    (Eq-sym (length-repl i (fbot m) (botLike A))) ilt'
        e0 : Eq (getF i A0) (fbot m)
        e0 = getF-repl i (fbot m) (botLike A) ilt'
        below : Below A0 A
        below = Below-repl i (fbot m) A
                  (Eq-transport (\ z -> LeD (bot m) z) (Eq-sym e) (LeD-refl (bot m))) ilt
        univ : (X : FTup) -> Eq (length X) (length A0) ->
               Eq (getF i X) (getF i A0) -> LeFTup (del i A0) (del i X) ->
               Eq (evalF (proj i) X) (fbot m)
        univ X leq hyp2 hlt = Eq-trans hyp2 e0
    go inf e =
      uo3 (mkSigma A0 (mkSigma below
            (mkSigma i (mkSigma e (mkSigma zero (mkSigma e0
              (mkSigma (\ m -> m) (mkSigma (inr (\ m _ -> LeN-refl (suc m))) univ))))))))
      where
        A0 : FTup
        A0 = repl i (fbot zero) (botLike A)
        e0 : Eq (getF i A0) (fbot zero)
        e0 = getF-repl i (fbot zero) (botLike A) ilt'
        below : Below A0 A
        below = Below-repl i (fbot zero) A (LeD-botD (get i A)) ilt
        univ : (X : FTup) (mm : Nat) -> Eq (length X) (length A0) ->
               LeN zero mm -> Eq (getF i X) (fbot mm) ->
               LeFTup (del i A0) (del i X) -> Eq (evalF (proj i) X) (fbot mm)
        univ X mm leq lek hyp hlt = hyp
