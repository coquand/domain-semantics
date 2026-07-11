{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Computable
--
-- The corollary of Proposition 1 (min1.pdf, resume + p.2): the denotation
-- of a primitive-recursive term is a COMPUTABLE object.  Concretely, its
-- Scott-continuous extension  f-hat : D^n -> D  can be evaluated at every
-- point, because the ultimate-obstination witness carries the value and
-- `uoValue` reads it off.  `prop1` and `uoValue` are total, postulate-free
-- functions, so their composition IS the algorithm.
--
-- In particular this computes  f-hat(x, ..., x)  at the diagonal infinite
-- point  x = S^omega(bot).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Computable where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property using (UO ; uoValue)
open import OBSTINATION.Prop1 using (Wf ; prop1)

------------------------------------------------------------------------
-- The extension value at an arbitrary arity-n point is computable.
------------------------------------------------------------------------

fhat : (f : PR) (A : Tup) -> Wf f (length A) -> D
fhat f A wf = uoValue (prop1 f A wf)

------------------------------------------------------------------------
-- The diagonal infinite point  (x, ..., x),  x = S^omega(bot).
------------------------------------------------------------------------

diag : Nat -> Tup
diag zero    = nil
diag (suc n) = cons inf (diag n)

length-diag : (n : Nat) -> Eq (length (diag n)) n
length-diag zero    = refl
length-diag (suc n) = Eq-cong suc (length-diag n)

-- Hence  f-hat(S^omega(bot), ..., S^omega(bot))  is computable for every
-- primitive-recursive f well-formed of arity n.
fhat-diag : (f : PR) (n : Nat) -> Wf f n -> D
fhat-diag f n wf =
  uoValue (prop1 f (diag n) (Eq-transport (Wf f) (Eq-sym (length-diag n)) wf))

------------------------------------------------------------------------
-- It really computes: sample diagonal evaluations reduce definitionally.
--   * the constant 0 is 0 everywhere:            f-hat(x)      = 0
--   * successor of the infinite is the infinite: succ-hat(x)   = x = S^omega(bot)
--   * a projection returns its infinite input:   (proj 0)-hat(x,x) = x
------------------------------------------------------------------------

_ : Eq (fhat-diag zerf     (suc zero) tt) (cpl zero)
_ = refl

_ : Eq (fhat-diag succ     (suc zero) tt) inf
_ = refl

_ : Eq (fhat-diag (proj zero) (suc (suc zero)) tt) inf
_ = refl
