{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PRInfTest
--
-- `prVal` really COMPUTES.  Every equation below is checked by `refl`,
-- so the value at the all-infinite point is produced, not merely proved
-- to exist:
--
--   zerf (S^w bot)          = 0                 (cpl 0)
--   proj0 (S^w bot)         = S^w bot           (inf)
--   succ (S^w bot)          = S^w bot           (inf)
--   E (S^w bot)             = 0                 (cpl 0)   E = prec zerf zerf
--   plus (S^w bot, S^w bot) = S^w bot           (inf)
--
-- `E` is the interesting one: `E(bot) = bot` but `E(S^(m+1) bot) = 0`,
-- so the chain is `bot 0, cpl 0, cpl 0, ...` and the lub is the NUMERAL
-- -- Case 1 of the property, at a point that is infinite.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PRInfTest where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (D ; bot ; cpl ; inf)
open import OBSTINATION.PR using (PR ; zerf ; succ ; proj ; comp ; prec)
open import OBSTINATION.Prop1 using (Wf)
open import OBSTINATION.PRInf using (prVal)

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

------------------------------------------------------------------------
-- the base cases
------------------------------------------------------------------------

zerf-inf : Eq (prVal zerf one tt) (cpl zero)
zerf-inf = refl

proj0-inf : Eq (prVal (proj zero) one tt) inf
proj0-inf = refl

succ-inf : Eq (prVal succ one tt) inf
succ-inf = refl

------------------------------------------------------------------------
-- E = prec zerf zerf : the chain is  bot , 0 , 0 , ...
------------------------------------------------------------------------

E : PR
E = prec zerf zerf

E-wf : Wf E one
E-wf = mkSigma zero (mkSigma refl (mkSigma tt tt))

E-inf : Eq (prVal E one E-wf) (cpl zero)
E-inf = refl

------------------------------------------------------------------------
-- plus = prec (proj 0) (comp succ [proj 1]) : obstinate on its first
-- argument, so the value at (S^w bot , S^w bot) is S^w bot
------------------------------------------------------------------------

plus : PR
plus = prec (proj zero) (comp succ (cons (proj one) nil))

plus-wf : Wf plus two
plus-wf =
  mkSigma one (mkSigma refl (mkSigma tt (mkSigma tt (mkSigma tt tt))))

plus-inf : Eq (prVal plus two plus-wf) inf
plus-inf = refl
