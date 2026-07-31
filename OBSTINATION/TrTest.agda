{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrTest
--
-- The corrected trace, on the two terms that broke the old one and on
-- addition.  Every equation below is checked by `refl`, so the traces
-- really compute -- base cases, composition, recursion, the numeral
-- continuations and the freezing of a total argument, all together.
--
--   E    = prec zerf zerf                E(bot) = bot ,  E(S^(m+1) bot) = 0
--   plus = prec (proj 0) (comp succ [proj 1])
--
-- `E` is the term that refutes the old height-only trace (`MP1BridgeFail`);
-- `plus` exercises `compTr` inside `precTr`, and its `fcpl` cases exercise
-- `N.atNum`, i.e. the base term `g`, which the main walk never sees.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrTest where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrComp using (compTr)
open import OBSTINATION.TrPrec using (precTr)

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

------------------------------------------------------------------------
-- E = prec zerf zerf,  arity 1
------------------------------------------------------------------------

ETr : Tr one
ETr = precTr zero (zerfTr zero) (zerfTr two)

-- bot at bot ...
E-bot : Eq (sem one ETr (cons (fbot zero) nil)) (fbot zero)
E-bot = refl

-- ... and the COMPLETE 0 at every higher level: the very behaviour the
-- old height-only trace could not express
E-cpl-1 : Eq (sem one ETr (cons (fbot one) nil)) (fcpl zero)
E-cpl-1 = refl

E-cpl-3 : Eq (sem one ETr (cons (fbot three) nil)) (fcpl zero)
E-cpl-3 = refl

------------------------------------------------------------------------
-- plus = prec (proj 0) (comp succ [proj 1]),  arity 2
------------------------------------------------------------------------

-- the step term  h (x , r , y) = S r,  arity 3
hTr : Tr three
hTr = compTr one succTr three (\ _ -> projTr three one tt)

plusTr : Tr two
plusTr = precTr one (projTr one zero tt) hTr

-- on the incomplete cone `plus` is obstinate: it keeps reading its first
-- argument and never looks at the second
plus-obst-2-3 : Eq (sem two plusTr (cons (fbot two) (cons (fbot three) nil)))
                   (fbot two)
plus-obst-2-3 = refl

plus-obst-0-3 : Eq (sem two plusTr (cons (fbot zero) (cons (fbot three) nil)))
                   (fbot zero)
plus-obst-0-3 = refl

-- a TOTAL first argument takes the continuation, where the base term `g`
-- lives:  plus (0 , y) = y
plus-cpl-0 : Eq (sem two plusTr (cons (fcpl zero) (cons (fbot three) nil)))
                (fbot three)
plus-cpl-0 = refl

-- and  plus (S 0 , y) = S y,  which goes through `N.atNum`'s composition
plus-cpl-1 : Eq (sem two plusTr (cons (fcpl one) (cons (fbot three) nil)))
                (fbot (suc three))
plus-cpl-1 = refl

plus-cpl-2 : Eq (sem two plusTr (cons (fcpl two) (cons (fbot three) nil)))
                (fbot (suc (suc three)))
plus-cpl-2 = refl

-- both arguments total: plus (2 , 3) = 5
plus-tot : Eq (sem two plusTr (cons (fcpl two) (cons (fcpl three) nil)))
              (fcpl (suc (suc three)))
plus-tot = refl
