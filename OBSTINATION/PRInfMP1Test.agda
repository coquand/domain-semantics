{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PRInfMP1Test
--
-- `PRInfMP1.prValMP` RUNS.  Every equation is checked by `refl`, so the
-- value at the all-infinite point really is produced by computation from
-- the trace's MP1 -- no Proposition 1 anywhere.
--
--   E    = prec zerf zerf        E(S^w bot)      = 0            (`cpl 0`)
--   P0   = proj 0                P0(S^w bot)     = S^w(bot)     (`inf`)
--   Z    = zerf                  Z(S^w bot)      = 0            (`cpl 0`)
--   S0   = succ o proj 0         S0(S^w bot)     = S^w(bot)     (`inf`)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PRInfMP1Test where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (D ; bot ; cpl ; inf)
open import OBSTINATION.PR using (PR ; zerf ; proj ; succ ; comp ; prec)
open import OBSTINATION.PRInfMP1 using (prValMP)

one : Nat
one = suc zero

-- prec zerf zerf : arity 1
E-val : Eq (prValMP (prec zerf zerf) one (mkSigma zero (mkSigma refl (mkSigma tt tt)))) (cpl zero)
E-val = refl

-- proj 0 : arity 1
P0-val : Eq (prValMP (proj zero) one tt) inf
P0-val = refl

-- zerf : arity 1
Z-val : Eq (prValMP zerf one tt) (cpl zero)
Z-val = refl

-- succ o proj 0 : arity 1
S0-val : Eq (prValMP (comp succ (cons (proj zero) nil)) one
              (mkSigma tt (mkSigma tt tt))) inf
S0-val = refl
