{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.JoinLub
--
-- The join on the finite domain is the LEAST upper bound: if a <= c and
-- b <= c then joinF a b <= c (pointwise joinT for tuples).  This is what
-- lets the composition case combine the per-coordinate witnesses
-- produced by `refine` into a single finite A0 <= A.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.JoinLub where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Meet

------------------------------------------------------------------------
-- max is the least upper bound on Nat
------------------------------------------------------------------------

maxN-lub : {j k l : Nat} -> LeN j l -> LeN k l -> LeN (maxN j k) l
maxN-lub {zero}  {k}     {l}     p q = q
maxN-lub {suc j} {zero}  {l}     p q = p
maxN-lub {suc j} {suc k} {zero}  () q
maxN-lub {suc j} {suc k} {suc l} p q = maxN-lub {j} {k} {l} p q

------------------------------------------------------------------------
-- joinF is the least upper bound on FEl
------------------------------------------------------------------------

joinF-lub : {a b c : FEl} -> LeF a c -> LeF b c -> LeF (joinF a b) c
joinF-lub {fbot j} {fbot k} {fbot l} p q = maxN-lub {j} {k} {l} p q
joinF-lub {fbot j} {fbot k} {fcpl l} p q = maxN-lub {j} {k} {l} p q
joinF-lub {fbot j} {fcpl k} {fbot l} p ()
joinF-lub {fbot j} {fcpl k} {fcpl l} p q = q
joinF-lub {fcpl j} {fbot k} {fbot l} () q
joinF-lub {fcpl j} {fbot k} {fcpl l} p q = p
joinF-lub {fcpl j} {fcpl k} {fbot l} () q
joinF-lub {fcpl j} {fcpl k} {fcpl l} refl refl = maxN-r {l} {l} (LeN-refl l)

------------------------------------------------------------------------
-- joinT is the least upper bound on tuples
------------------------------------------------------------------------

joinT-lub : {A B C : FTup} -> LeFTup A C -> LeFTup B C -> LeFTup (joinT A B) C
joinT-lub {nil}      {nil}      {nil}      p q = tt
joinT-lub {nil}      {nil}      {cons _ _} () q
joinT-lub {nil}      {cons _ _} {nil}      p ()
joinT-lub {nil}      {cons _ _} {cons _ _} () q
joinT-lub {cons _ _} {nil}      {nil}      () q
joinT-lub {cons _ _} {nil}      {cons _ _} p ()
joinT-lub {cons a A} {cons b B} {nil}      () q
joinT-lub {cons a A} {cons b B} {cons c C} p q =
  mkSigma (joinF-lub {a} {b} {c} (fst p) (fst q)) (joinT-lub {A} {B} {C} (snd p) (snd q))
