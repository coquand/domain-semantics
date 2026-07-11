{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompMapE
--
-- Indexing into mapU: the i-th coordinate of  mapU fs X  is the value of
-- the i-th inner function at X.  This is the runtime counterpart of
-- `index-innerU` (which indexes the inner point of extensions), and lets
-- the Case-2 / Case-3 branches read off  f_i(X)  from  mapU fs X.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompMapE where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF)
open import OBSTINATION.CompPull using (UOFun ; ufn ; mapU)
open import OBSTINATION.CompIndex using (nthFn)

getF-mapU : (i : Nat) (fs : List UOFun) (X : FTup) ->
  LeN (suc i) (length fs) ->
  Eq (getF i (mapU fs X)) (nthFn i fs X)
getF-mapU zero    (cons u us) X le = refl
getF-mapU (suc i) (cons u us) X le = getF-mapU i us X le
getF-mapU i       nil         X ()

-- mapU has the length of fs
length-mapU : (fs : List UOFun) (X : FTup) -> Eq (length (mapU fs X)) (length fs)
length-mapU nil         X = refl
length-mapU (cons u us) X = Eq-cong suc (length-mapU us X)
