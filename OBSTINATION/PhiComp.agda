{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PhiComp
--
-- Monotonicity of a strictly increasing witness function phi (from a
-- threshold k).  These are the arithmetic facts behind "the phi-class
-- is closed under composition" (composition case, Case 3):
--
--   sinc-mono-le : a >= k, a <= b   ==>   phi a <= phi b
--   sinc-mono-lt : a >= k, a <  b   ==>   phi a <  phi b
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PhiComp where

open import OBSTINATION.Prelude
open import OBSTINATION.Property using (StrictIncFrom)
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)

------------------------------------------------------------------------
-- Addition facts (phi-independent)
------------------------------------------------------------------------

addN-suc-l : (a d : Nat) -> Eq (addN (suc a) d) (suc (addN a d))
addN-suc-l a zero    = refl
addN-suc-l a (suc d) = Eq-cong suc (addN-suc-l a d)

addN-zero-l : (b : Nat) -> Eq (addN zero b) b
addN-zero-l zero    = refl
addN-zero-l (suc b) = Eq-cong suc (addN-zero-l b)

-- a <= b  yields the difference d with a + d = b
le-to-addN : (a b : Nat) -> LeN a b -> Sigma Nat (\ d -> Eq (addN a d) b)
le-to-addN zero    b       le = mkSigma b (addN-zero-l b)
le-to-addN (suc a) zero    ()
le-to-addN (suc a) (suc b) le =
  let r = le-to-addN a b le
  in mkSigma (fst r) (Eq-trans (addN-suc-l a (fst r)) (Eq-cong suc (snd r)))

------------------------------------------------------------------------
-- Monotonicity of a strictly increasing phi
------------------------------------------------------------------------

module _ (k : Nat) (phi : Nat -> Nat) (sinc : StrictIncFrom k phi) where

  sinc-mono-addN : (a : Nat) -> LeN k a -> (d : Nat) -> LeN (phi a) (phi (addN a d))
  sinc-mono-addN a ka zero    = LeN-refl (phi a)
  sinc-mono-addN a ka (suc d) =
    LeN-trans {phi a} {phi (addN a d)} {phi (suc (addN a d))}
      (sinc-mono-addN a ka d)
      (LeN-trans {phi (addN a d)} {suc (phi (addN a d))} {phi (suc (addN a d))}
        (LeN-suc (phi (addN a d)))
        (sinc (addN a d) (LeN-trans {k} {a} {addN a d} ka (LeN-addN-l a d))))

  sinc-mono-le : (a b : Nat) -> LeN k a -> LeN a b -> LeN (phi a) (phi b)
  sinc-mono-le a b ka ab =
    let r = le-to-addN a b ab
    in Eq-transport (\ n -> LeN (phi a) (phi n)) (snd r) (sinc-mono-addN a ka (fst r))

  sinc-mono-lt : (a b : Nat) -> LeN k a -> LeN (suc a) b -> LeN (suc (phi a)) (phi b)
  sinc-mono-lt a b ka altb =
    LeN-trans {suc (phi a)} {phi (suc a)} {phi b}
      (sinc a ka)
      (sinc-mono-le (suc a) b (LeN-trans {k} {a} {suc a} ka (LeN-suc a)) altb)
