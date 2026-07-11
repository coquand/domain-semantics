{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompCase1
--
-- Composition, the eventually-constant-complete branch: if g is in
-- Case 1 at the inner point B = <ext f_j A>, then the composite
-- g o <f_1,...,f_k> is in Case 1 at A.  Directly via `pullback`:
-- whenever X >= A0 we have mapU fs X >= B0, so
--   (compFn gf fs)(X) = gf (mapU fs X) = S^m(0).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompCase1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.CompPull using (UOFun ; mapU ; innerPtU ; compFn ; pullback)

comp-Case1-build : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup) ->
  Case1 gf (innerPtU fs A) ->
  Case1 (compFn gf fs) A
comp-Case1-build gf fs A (mkSigma B0 (mkSigma belowB (mkSigma m univG))) =
  let pb    = pullback fs A B0 belowB
      A0    = fst pb
      belA  = fst (snd pb)
      pull  = snd (snd pb)
  in mkSigma A0 (mkSigma belA
       (mkSigma m (\ X leX -> univG (mapU fs X) (pull X leX))))
