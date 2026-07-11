{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotReach
--
-- Compactness / reach for the recursion restriction Fc, used by the
-- finite-incomplete first-argument case.
--
-- From the classification of Fc at Y (a genuine `UO Fc Y`, or the
-- constant-incomplete `FcConst`), extract uniformly:
--
--   * `fc-v1`    : the Scott-continuous extension value of Fc at Y;
--   * `fc-reach` : compactness -- any finite u below fc-v1 is realised on
--     an UPWARD-CLOSED region of Y  (Fc X' >= u for all X' >= A0').
--
-- and the recursion-result lower bound engine
--
--   * `frec-ge`  : if Fc dominates u on a region, then the deeper
--     recursion result  precF g h p tail  (any coord0-pred p >= S^c(bot),
--     tail in the region) also dominates u -- by monotonicity of precF.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotReach where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Refine using (refine-aux)
open import OBSTINATION.PrecBotEngine using (FcFun ; FcConst)
open import OBSTINATION.PrecFun using (RecData ; precFun ; precFun-mono)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- Fc is monotone (from precFun-mono with a fixed incomplete leading coord)
  ------------------------------------------------------------------------

  FcFun-mono : (c : Nat) {X Y : FTup} ->
    LeFTup X Y -> LeF (FcFun rd c X) (FcFun rd c Y)
  FcFun-mono c {X} {Y} le =
    precFun-mono G H monoG monoH {fbot c} {fbot c} {X} {Y} (LeF-refl (fbot c)) le

  ------------------------------------------------------------------------
  -- Extension value and reach, uniformly from the Or-classification.
  ------------------------------------------------------------------------

  fc-v1 : (c : Nat) (Y : Tup) ->
    Or (UO (FcFun rd c) Y) (FcConst rd c Y) -> D
  fc-v1 c Y (inl pf)                 = uoValue pf
  fc-v1 c Y (inr (mkSigma m' _))     = bot m'

  fc-reach : (c : Nat) (Y : Tup)
    (o : Or (UO (FcFun rd c) Y) (FcConst rd c Y))
    (u : FEl) -> LeD (embed u) (fc-v1 c Y o) ->
    Sigma FTup (\ A0' -> Pair (Below A0' Y)
      ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X')))
  fc-reach c Y (inl pf) u le =
    mkSigma A0' (mkSigma bel
      (\ X' leX' -> LeF-trans {u} {FcFun rd c A0'} {FcFun rd c X'}
                      leA0 (FcFun-mono c {A0'} {X'} leX')))
    where
      r    = refine-aux (FcFun rd c) Y u pf le
      A0'  = fst r
      bel  = fst (snd r)
      leA0 = snd (snd r)               -- LeF u (Fc A0')
  fc-reach c Y (inr (mkSigma m' (mkSigma A0c (mkSigma belc univc)))) u le =
    mkSigma A0c (mkSigma belc
      (\ X' leX' -> Eq-transport (\ z -> LeF u z) (Eq-sym (univc X' leX')) le))

  ------------------------------------------------------------------------
  -- The recursion-result lower bound: from Fc dominating u on a region,
  -- any deeper recursion result dominates u too.
  ------------------------------------------------------------------------

  frec-ge : (c : Nat) (u : FEl) (A0' : FTup) ->
    ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X')) ->
    (p : FEl) (tail : FTup) -> LeF (fbot c) p -> LeFTup A0' tail ->
    LeF u (precFun G H p tail)
  frec-ge c u A0' reach p tail lecp letail =
    LeF-trans {u} {precFun G H (fbot c) tail} {precFun G H p tail}
      (reach tail letail)
      (precFun-mono G H monoG monoH {fbot c} {p} {tail} {tail} lecp (LeFTup-refl tail))
