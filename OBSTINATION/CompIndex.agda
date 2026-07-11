{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompIndex
--
-- Indexing into the inner point of a composition.  The i-th coordinate
-- of B = innerPtU fs A is the extension of the i-th inner function at A.
-- This lets the Case-2 / Case-3 branches recurse into that inner
-- function's own obstination.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompIndex where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (ext)
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike)
open import OBSTINATION.CompPull using
  (UOFun ; ufn ; ufnUO ; ufnMono ; Mono ; mapU ; innerPtU)

------------------------------------------------------------------------
-- A default inner function (the constant 0), used out of range.
------------------------------------------------------------------------

zeroUO : UOall (\ _ -> fcpl zero)
zeroUO A =
  uo1 (mkSigma (botLike A) (mkSigma (Below-botLike A) (mkSigma zero (\ _ _ -> refl))))

zeroMono : Mono (\ _ -> fcpl zero)
zeroMono _ = LeF-refl (fcpl zero)

defUO : UOFun
defUO = mkSigma (\ _ -> fcpl zero) (mkSigma zeroUO zeroMono)

------------------------------------------------------------------------
-- The i-th inner function (as a UOFun), with the constant-0 default.
------------------------------------------------------------------------

nthU : Nat -> List UOFun -> UOFun
nthU i       nil         = defUO
nthU zero    (cons u us) = u
nthU (suc i) (cons u us) = nthU i us

nthFn : Nat -> List UOFun -> (FTup -> FEl)
nthFn i fs = ufn (nthU i fs)

nthUO : (i : Nat) (fs : List UOFun) -> UOall (nthFn i fs)
nthUO i fs = ufnUO (nthU i fs)

------------------------------------------------------------------------
-- innerPtU has the length of fs, and its i-th coordinate is the i-th
-- extension.
------------------------------------------------------------------------

length-innerPtU : (fs : List UOFun) (A : Tup) ->
  Eq (length (innerPtU fs A)) (length fs)
length-innerPtU nil         A = refl
length-innerPtU (cons u us) A = Eq-cong suc (length-innerPtU us A)

index-innerU : (i : Nat) (fs : List UOFun) (A : Tup) ->
  LeN (suc i) (length fs) ->
  Eq (get i (innerPtU fs A)) (ext (nthFn i fs) (nthUO i fs) A)
index-innerU zero    (cons u us) A le = refl
index-innerU (suc i) (cons u us) A le = index-innerU i us A le
index-innerU i       nil         A ()
