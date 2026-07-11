{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecUnshift
--
-- Restricting obstination at a complete leading coordinate.  If f
-- satisfies ultimate obstination at (S^c(0), Z), then the tail function
-- Z' |-> f(S^c(0), Z') satisfies it at Z.  Because S^c(0) is complete
-- (maximal), the witness coordinate cannot be 0 (IncompleteFinite and
-- "= inf" are both empty at cpl c), so it lives among Z's coordinates
-- and is simply un-shifted by one.
--
-- This is the inverse of PrecCpl0's shift; it feeds the finite-recursion
-- sub-case (which composes h with the recursive result f(pred, -)).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecUnshift where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.CompCase3Helpers using (cpl-not-inf)

unshift-cpl : (f : FTup -> FEl) (c : Nat) (Z : Tup) ->
  UO f (cons (cpl c) Z) -> UO (\ Z' -> f (cons (fcpl c) Z')) Z
-- Case 1
unshift-cpl f c Z (uo1 (mkSigma nil (mkSigma below _))) = Empty-elim below
unshift-cpl f c Z (uo1 (mkSigma (cons f0 F0') (mkSigma below (mkSigma m univ)))) =
  uo1 (mkSigma F0' (mkSigma (snd below) (mkSigma m univ')))
  where
    univ' : (Z' : FTup) -> LeFTup F0' Z' -> Eq (f (cons (fcpl c) Z')) (fcpl m)
    univ' Z' leZ' = univ (cons (fcpl c) Z') (mkSigma (fst below) leZ')
-- Case 2
unshift-cpl f c Z (uo2 (mkSigma nil (mkSigma below _))) = Empty-elim below
unshift-cpl f c Z (uo2 (mkSigma (cons f0 F0') (mkSigma below
  (mkSigma m (mkSigma zero (mkSigma _ (mkSigma incompl _))))))) = Empty-elim incompl
unshift-cpl f c Z (uo2 (mkSigma (cons f0 F0') (mkSigma below
  (mkSigma m (mkSigma (suc i') (mkSigma irange (mkSigma incompl (mkSigma eqinv univ)))))))) =
  uo2 (mkSigma F0' (mkSigma (snd below)
    (mkSigma m (mkSigma i' (mkSigma irange (mkSigma incompl (mkSigma eqinv univ')))))))
  where
    univ' : (Z' : FTup) -> Eq (length Z') (length F0') ->
            Eq (getF i' Z') (getF i' F0') -> LeFTup (del i' F0') (del i' Z') ->
            Eq (f (cons (fcpl c) Z')) (fbot m)
    univ' Z' lenZ' coordZ' delZ' =
      univ (cons (fcpl c) Z') (Eq-cong suc lenZ') coordZ' (mkSigma (fst below) delZ')
-- Case 3
unshift-cpl f c Z (uo3 (mkSigma nil (mkSigma below _))) = Empty-elim below
unshift-cpl f c Z (uo3 (mkSigma (cons f0 F0') (mkSigma below
  (mkSigma zero (mkSigma eqinf _))))) = Empty-elim (cpl-not-inf eqinf)
unshift-cpl f c Z (uo3 (mkSigma (cons f0 F0') (mkSigma below
  (mkSigma (suc i') (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ))))))))) =
  uo3 (mkSigma F0' (mkSigma (snd below)
    (mkSigma i' (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ'))))))))
  where
    univ' : (Z' : FTup) (p : Nat) -> Eq (length Z') (length F0') -> LeN k p ->
            Eq (getF i' Z') (fbot p) -> LeFTup (del i' F0') (del i' Z') ->
            Eq (f (cons (fcpl c) Z')) (fbot (phi p))
    univ' Z' p lenZ' pk coordZ' delZ' =
      univ (cons (fcpl c) Z') p (Eq-cong suc lenZ') pk coordZ' (mkSigma (fst below) delZ')
