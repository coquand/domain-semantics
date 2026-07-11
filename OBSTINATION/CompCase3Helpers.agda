{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompCase3Helpers
--
-- Helpers for the composition Case-3 branch:
--   * anything below the infinite element is incomplete finite;
--   * from `uoValue pf = inf` one extracts pf's Case-3-INCREASING data
--     (the only case whose extension value is S^omega(bot)).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompCase3Helpers where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property

------------------------------------------------------------------------
-- Distinctness from inf, and "below inf implies fbot"
------------------------------------------------------------------------

cpl-not-inf : {m : Nat} -> Eq (cpl m) inf -> Empty
cpl-not-inf ()

bot-not-inf : {m : Nat} -> Eq (bot m) inf -> Empty
bot-not-inf ()

le-inf-fbot : (w : FEl) -> LeD (embed w) inf -> Sigma Nat (\ q -> Eq w (fbot q))
le-inf-fbot (fbot q) le = mkSigma q refl
le-inf-fbot (fcpl q) ()

------------------------------------------------------------------------
-- The Case-3-increasing payload, and its extraction from an inf value
------------------------------------------------------------------------

Case3Inr : (FTup -> FEl) -> Tup -> Set
Case3Inr f A =
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      (Sigma Nat (\ i ->
        Pair (Eq (get i A) inf)
        (Sigma Nat (\ k ->
          Pair (Eq (getF i A0) (fbot k))
          (Sigma (Nat -> Nat) (\ phi ->
            Pair (StrictIncFrom k phi)
              ((X : FTup) (m : Nat) ->
                 Eq (length X) (length A0) ->
                 LeN k m ->
                 Eq (getF i X) (fbot m) ->
                 LeFTup (del i A0) (del i X) ->
                 Eq (f X) (fbot (phi m))))))))))

extract-inr : (f : FTup -> FEl) (A : Tup) (pf : UO f A) ->
  Eq (uoValue pf) inf -> Case3Inr f A
extract-inr f A (uo1 (mkSigma _ (mkSigma _ (mkSigma m _)))) eq =
  Empty-elim (cpl-not-inf eq)
extract-inr f A (uo2 (mkSigma _ (mkSigma _ (mkSigma m _)))) eq =
  Empty-elim (bot-not-inf eq)
extract-inr f A (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei
  (mkSigma k (mkSigma ea (mkSigma phi (mkSigma (inl cst) univ))))))))) eq =
  Empty-elim (bot-not-inf eq)
extract-inr f A (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei
  (mkSigma k (mkSigma ea (mkSigma phi (mkSigma (inr sinc) univ))))))))) eq =
  mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei
    (mkSigma k (mkSigma ea (mkSigma phi (mkSigma sinc univ)))))))
