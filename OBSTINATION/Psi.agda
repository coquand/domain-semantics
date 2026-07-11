{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Psi
--
-- The witness function psi for the hardest sub-case of the infinite
-- recursion (min1.pdf p.4 / min.pdf p.4, case 4, phi strictly
-- increasing).  When h's germ is governed by its recursion-result
-- coordinate with function phi, the value of f at successive recursion
-- depths follows  psi(n0) = N,  psi(n+1) = phi(psi n).
--
--   psi p = phi^{p - n0}(N).
--
-- Two regimes, selected by comparing N and phi N (and N <= phi N always
-- holds by monotonicity of f, supplied by the caller):
--   * N = phi N   : psi is CONSTANT N from n0;
--   * N < phi N   : psi is STRICTLY INCREASING from n0 (invariant: the
--     offset sequence stays >= k0 and strictly increases, via
--     sinc-mono-lt).
-- Either way  PhiOK n0 psi,  as required to build f's Case 3 witness.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Psi where

open import OBSTINATION.Prelude
open import OBSTINATION.Property using (StrictIncFrom ; ConstFrom ; PhiOK)
open import OBSTINATION.PhiComp using (sinc-mono-lt)

------------------------------------------------------------------------
-- Iteration and truncated subtraction
------------------------------------------------------------------------

iterN : (Nat -> Nat) -> Nat -> Nat -> Nat
iterN f zero    x = x
iterN f (suc l) x = f (iterN f l x)

monus : Nat -> Nat -> Nat
monus n       zero    = n
monus zero    (suc m) = zero
monus (suc n) (suc m) = monus n m

monus-refl : (n : Nat) -> Eq (monus n n) zero
monus-refl zero    = refl
monus-refl (suc n) = monus-refl n

monus-suc : (m n0 : Nat) -> LeN n0 m -> Eq (monus (suc m) n0) (suc (monus m n0))
monus-suc m       zero     le = refl
monus-suc zero    (suc n0) ()
monus-suc (suc m) (suc n0) le = monus-suc m n0 le

------------------------------------------------------------------------
-- The witness function and its recurrence
------------------------------------------------------------------------

module _ (phi : Nat -> Nat) (N n0 : Nat) where

  psiSeq : Nat -> Nat
  psiSeq l = iterN phi l N

  psi : Nat -> Nat
  psi p = psiSeq (monus p n0)

  psi-base : Eq (psi n0) N
  psi-base = Eq-cong psiSeq (monus-refl n0)

  psi-rec : (p : Nat) -> LeN n0 p -> Eq (psi (suc p)) (phi (psi p))
  psi-rec p le = Eq-cong psiSeq (monus-suc p n0 le)

  ----------------------------------------------------------------------
  -- Constant regime
  ----------------------------------------------------------------------

  psi-ok-const : Eq N (phi N) -> PhiOK n0 psi
  psi-ok-const eN = inl cst
    where
      seq-const : (l : Nat) -> Eq (psiSeq l) N
      seq-const zero    = refl
      seq-const (suc l) = Eq-trans (Eq-cong phi (seq-const l)) (Eq-sym eN)
      cst : ConstFrom n0 psi
      cst m le = Eq-trans (seq-const (monus m n0)) (Eq-sym psi-base)

  ----------------------------------------------------------------------
  -- Strictly increasing regime
  ----------------------------------------------------------------------

  psi-ok-sinc : (k0 : Nat) -> StrictIncFrom k0 phi ->
    LeN k0 N -> LeN (suc N) (phi N) -> PhiOK n0 psi
  psi-ok-sinc k0 sincphi k0N N-lt = inr sinc
    where
      inv : (l : Nat) ->
        Pair (LeN k0 (psiSeq l)) (LeN (suc (psiSeq l)) (psiSeq (suc l)))
      inv zero    = mkSigma k0N N-lt
      inv (suc l) = mkSigma k0-next lt-next
        where
          IHk  = fst (inv l)
          IHlt = snd (inv l)
          k0-next : LeN k0 (psiSeq (suc l))
          k0-next =
            LeN-trans {k0} {suc (psiSeq l)} {psiSeq (suc l)}
              (LeN-trans {k0} {psiSeq l} {suc (psiSeq l)} IHk (LeN-suc (psiSeq l)))
              IHlt
          lt-next : LeN (suc (psiSeq (suc l))) (psiSeq (suc (suc l)))
          lt-next = sinc-mono-lt k0 phi sincphi (psiSeq l) (psiSeq (suc l)) IHk IHlt
      sinc : StrictIncFrom n0 psi
      sinc m le =
        Eq-transport (\ z -> LeN (suc (psi m)) (psiSeq z))
          (Eq-sym (monus-suc m n0 le)) (snd (inv (monus m n0)))
