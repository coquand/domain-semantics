{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfExtract
--
-- Extraction helpers for the infinite-recursion dispatch (min1.pdf p.3):
--
--   * `approx` / `approx-below` : the finite approximant carried by any
--     UO witness, together with its Below evidence.
--   * `below-inf-fbot` : a coordinate that is S^omega(bot) in the point
--     forces the approximant's coordinate there to be some S^k(bot).
--   * `uSeq-dichotomy-b` : the stabilisation dichotomy REFINED to record
--     that the stabilisation index is <= n (needed to identify the finite
--     limit with u_{k0}).
--   * `finite-stab` : from  not (S^{k0}(bot) <= u_{k0})  (the first
--     principal case), a genuine stabilisation point whose value is a
--     concrete finite element  embed w.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfExtract where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.USeq using (uSeq ; uSeq-mono ; uSeq-stab)
open import OBSTINATION.USeqDich using (dich-step)
open import OBSTINATION.PrecFun using (RecData)

------------------------------------------------------------------------
-- The approximant of a UO witness
------------------------------------------------------------------------

approx : {f : FTup -> FEl} {A : Tup} -> UO f A -> FTup
approx (uo1 (mkSigma B0 _)) = B0
approx (uo2 (mkSigma B0 _)) = B0
approx (uo3 (mkSigma B0 _)) = B0

approx-below : {f : FTup -> FEl} {A : Tup} (u : UO f A) -> Below (approx u) A
approx-below (uo1 (mkSigma B0 (mkSigma bel _))) = bel
approx-below (uo2 (mkSigma B0 (mkSigma bel _))) = bel
approx-below (uo3 (mkSigma B0 (mkSigma bel _))) = bel

------------------------------------------------------------------------
-- Coordinate access commutes with embedding (in range)
------------------------------------------------------------------------

get-embedTup : (i : Nat) (B0 : FTup) -> LeN (suc i) (length B0) ->
  Eq (get i (embedTup B0)) (embed (getF i B0))
get-embedTup zero    (cons b bs) le = refl
get-embedTup (suc i) (cons b bs) le = get-embedTup i bs le
get-embedTup i       nil         ()

------------------------------------------------------------------------
-- An infinite coordinate forces an incomplete approximant coordinate
------------------------------------------------------------------------

below-inf-fbot : (i : Nat) (B0 : FTup) (A : Tup) -> Below B0 A ->
  Eq (get i A) inf -> LeN (suc i) (length B0) ->
  Sigma Nat (\ k -> Eq (getF i B0) (fbot k))
below-inf-fbot i B0 A bel einf irng = aux (getF i B0) refl coordLe
  where
    coordLe : LeD (embed (getF i B0)) inf
    coordLe = Eq-transport (\ z -> LeD z inf) (get-embedTup i B0 irng)
                (Eq-transport (\ z -> LeD (get i (embedTup B0)) z) einf
                  (LeTup-get i {embedTup B0} {A} bel))
    aux : (x : FEl) -> Eq (getF i B0) x -> LeD (embed x) inf ->
          Sigma Nat (\ k -> Eq (getF i B0) (fbot k))
    aux (fbot k) e le = mkSigma k e
    aux (fcpl k) e ()

------------------------------------------------------------------------
-- Bounded stabilisation dichotomy
------------------------------------------------------------------------

module _ (rd : RecData) (Y : Tup) where
  open RecData rd

  private
    u : Nat -> D
    u k = uSeq rd Y k

  uSeq-dichotomy-b : (n : Nat) ->
    Or (Sigma Nat (\ k -> Pair (LeN k n) (Eq (u k) (u (suc k)))))
       (LeD (bot n) (u n))
  uSeq-dichotomy-b zero    = inr tt
  uSeq-dichotomy-b (suc n') with uSeq-dichotomy-b n'
  ... | inl (mkSigma k (mkSigma kn' e)) =
          inl (mkSigma k (mkSigma (LeN-trans {k} {n'} {suc n'} kn' (LeN-suc n')) e))
  ... | inr bn' with dich-step n' (u n') (u (suc n')) (u (suc (suc n')))
                       bn' (uSeq-mono rd Y n') (uSeq-mono rd Y (suc n'))
  ...   | inl e       = inl (mkSigma n' (mkSigma (LeN-suc n') e))
  ...   | inr (inl e) = inl (mkSigma (suc n') (mkSigma (LeN-refl (suc n')) e))
  ...   | inr (inr l) = inr l

  ----------------------------------------------------------------------
  -- The finite-limit trigger (first principal case)
  ----------------------------------------------------------------------

  finite-stab : (k0 : Nat) -> Not (LeD (bot k0) (u k0)) ->
    Sigma Nat (\ k -> Pair (Eq (u k) (u (suc k)))
                           (Sigma FEl (\ w -> Eq (u k) (embed w))))
  finite-stab k0 nle with uSeq-dichotomy-b k0
  ... | inr l = Empty-elim (nle l)
  ... | inl (mkSigma k (mkSigma kk0 e)) = mkSigma k (mkSigma e (aux (u k0) refl))
    where
      ukk0 : Eq (u k) (u k0)
      ukk0 = uSeq-stab rd Y k e k0 kk0
      aux : (d : D) -> Eq (u k0) d -> Sigma FEl (\ w -> Eq (u k) (embed w))
      aux (bot j) e0 = mkSigma (fbot j) (Eq-trans ukk0 e0)
      aux (cpl j) e0 = mkSigma (fcpl j) (Eq-trans ukk0 e0)
      aux inf     e0 = Empty-elim (nle (Eq-transport (\ z -> LeD (bot k0) z) (Eq-sym e0) tt))
