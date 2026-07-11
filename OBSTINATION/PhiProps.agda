{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PhiProps
--
-- Properties of the witness functions phi (min1.pdf, Case 3).  The key
-- fact is that a STRICTLY INCREASING phi (from a threshold k) escapes
-- every bound: for any p there is a stage m >= k with p <= phi m.  This
-- is the computational content of "S^{phi(m)}(bot) has supremum
-- S^omega(bot) when phi is strictly increasing", and is what the
-- composition and primitive-recursion cases use to reach the infinite
-- element.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PhiProps where

open import OBSTINATION.Prelude
open import OBSTINATION.Property using (StrictIncFrom ; ConstFrom ; PhiOK)

------------------------------------------------------------------------
-- Addition (recursion on the second argument, so addN k (suc p) reduces)
------------------------------------------------------------------------

addN : Nat -> Nat -> Nat
addN k zero    = k
addN k (suc p) = suc (addN k p)

LeN-addN-l : (k p : Nat) -> LeN k (addN k p)
LeN-addN-l k zero    = LeN-refl k
LeN-addN-l k (suc p) = LeN-trans {k} {addN k p} {suc (addN k p)}
                         (LeN-addN-l k p) (LeN-suc (addN k p))

------------------------------------------------------------------------
-- A strictly increasing phi grows at least linearly, hence escapes any
-- bound.
------------------------------------------------------------------------

module _ (k : Nat) (phi : Nat -> Nat) (sinc : StrictIncFrom k phi) where

  -- phi (k + p) >= p
  phi-grow : (p : Nat) -> LeN p (phi (addN k p))
  phi-grow zero    = tt
  phi-grow (suc p) =
    LeN-trans {suc p} {suc (phi (addN k p))} {phi (suc (addN k p))}
      (phi-grow p)
      (sinc (addN k p) (LeN-addN-l k p))

  -- for every bound p there is a stage m >= k with p <= phi m
  phi-escape : (p : Nat) -> Sigma Nat (\ m -> Pair (LeN k m) (LeN p (phi m)))
  phi-escape p = mkSigma (addN k p) (mkSigma (LeN-addN-l k p) (phi-grow p))

------------------------------------------------------------------------
-- A constant phi stays at its threshold value: phi m = phi k for m >= k.
-- (The Case-3 value is then the finite S^{phi(k)}(bot).)
------------------------------------------------------------------------

module _ (k : Nat) (phi : Nat -> Nat) (cst : ConstFrom k phi) where

  phi-const-bound : (m : Nat) -> LeN k m -> Eq (phi m) (phi k)
  phi-const-bound = cst
