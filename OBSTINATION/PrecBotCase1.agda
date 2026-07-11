{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotCase1
--
-- Finite-incomplete first argument, the branch where h is Case 1 at the
-- inner point  B = cons (bot c) (cons v1 Y):  h is eventually the
-- complete value S^m(0).  Then f = prec g h is Case 1 at
-- cons (bot (suc c)) Y:  a single realiser at coord0 = S^{c+1}(bot)
-- reaches S^m(0), and completeness (maximality) pins it upward.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotCase1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Prop1Base using (fcpl-max)
open import OBSTINATION.PrecBotEngine using (FcFun)
open import OBSTINATION.PrecBotPull using (pull-h)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono ; precFun)

module _ (rd : RecData) where
  open RecData rd

  prec-bot-Case1 : (c : Nat) (Y : Tup) (v1 : D)
    (reach : (u : FEl) -> LeD (embed u) v1 ->
       Sigma FTup (\ A0' -> Pair (Below A0' Y)
         ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X'))))
    (B0 : FTup) -> Below B0 (cons (bot c) (cons v1 Y)) -> (m : Nat) ->
    ((Z : FTup) -> LeFTup B0 Z -> Eq (H Z) (fcpl m)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  prec-bot-Case1 c Y v1 reach B0 belB0 m univG =
    uo1 (mkSigma A0 (mkSigma belA0 (mkSigma m univ)))
    where
      pb    = pull-h rd c Y v1 reach B0 belB0
      A0t   = fst pb
      belA0t = fst (snd pb)
      dom   = snd (snd pb)
      A0 : FTup
      A0 = cons (fbot (suc c)) A0t
      belA0 : Below A0 (cons (bot (suc c)) Y)
      belA0 = mkSigma (LeD-refl (bot (suc c))) belA0t
      -- the realiser: f at coord0 = S^{c+1}(bot), tail A0t, equals S^m(0)
      realiser : Eq (precFun G H (fbot (suc c)) A0t) (fcpl m)
      realiser =
        univG (cons (fbot c) (cons (precFun G H (fbot c) A0t) A0t))
          (dom (fbot c) A0t (LeF-refl (fbot c)) (LeFTup-refl A0t))
      univ : (X : FTup) -> LeFTup A0 X -> Eq (PF G H X) (fcpl m)
      univ nil ()
      univ (cons x xs) leX =
        fcpl-max m (precFun G H x xs)
          (Eq-transport (\ z -> LeF z (precFun G H x xs)) realiser
            (PF-mono G H monoG monoH {A0} {cons x xs} leX))
