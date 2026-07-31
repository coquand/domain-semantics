{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrTermTest
--
-- `traceOf` -- the trace built by induction on a PR TERM, from its `Wf`
-- proof -- evaluated against `PR.evalF`.  Every equation below is checked
-- by `refl`, so the whole-term construction really computes, and computes
-- the right thing: `traceOf-sem` proves the agreement, this file confirms
-- that neither side is stuck.
--
--   E    = prec zerf zerf                     the term that refuted the
--                                             old height-only trace
--   plus = prec (proj 0) (comp succ [proj 1])
--   f x  = g (x , x)   with  g = prec zerf (proj 2)     -- the sharing test
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrTermTest where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using
  (PR ; zerf ; proj ; succ ; comp ; prec ; evalF)
open import OBSTINATION.Prop1 using (Wf)
open import OBSTINATION.TraceDef using (Tr ; sem)
open import OBSTINATION.TrTerm using (traceOf)

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

------------------------------------------------------------------------
-- E = prec zerf zerf,  arity 1
------------------------------------------------------------------------

EPR : PR
EPR = prec zerf zerf

E-wf : Wf EPR one
E-wf = mkSigma zero (mkSigma refl (mkSigma tt tt))

ETr : Tr one
ETr = traceOf EPR one E-wf

E-0 : Eq (sem one ETr (cons (fbot zero) nil))
         (evalF EPR (cons (fbot zero) nil))
E-0 = refl

E-1 : Eq (sem one ETr (cons (fbot one) nil))
         (evalF EPR (cons (fbot one) nil))
E-1 = refl

E-val-0 : Eq (sem one ETr (cons (fbot zero) nil)) (fbot zero)
E-val-0 = refl

E-val-3 : Eq (sem one ETr (cons (fbot three) nil)) (fcpl zero)
E-val-3 = refl

------------------------------------------------------------------------
-- plus = prec (proj 0) (comp succ [proj 1]),  arity 2
------------------------------------------------------------------------

plusPR : PR
plusPR = prec (proj zero) (comp succ (cons (proj one) nil))

plus-wf : Wf plusPR two
plus-wf = mkSigma one (mkSigma refl (mkSigma tt (mkSigma tt (mkSigma tt tt))))

plusTr : Tr two
plusTr = traceOf plusPR two plus-wf

-- obstinate on the incomplete cone: it never looks at the second argument
plus-obst : Eq (sem two plusTr (cons (fbot two) (cons (fbot three) nil)))
               (evalF plusPR (cons (fbot two) (cons (fbot three) nil)))
plus-obst = refl

plus-obst-val : Eq (sem two plusTr (cons (fbot two) (cons (fbot three) nil)))
                   (fbot two)
plus-obst-val = refl

-- a total first argument goes through the numeral continuations
plus-cpl-0 : Eq (sem two plusTr (cons (fcpl zero) (cons (fbot three) nil)))
                (evalF plusPR (cons (fcpl zero) (cons (fbot three) nil)))
plus-cpl-0 = refl

plus-cpl-2 : Eq (sem two plusTr (cons (fcpl two) (cons (fbot three) nil)))
                (evalF plusPR (cons (fcpl two) (cons (fbot three) nil)))
plus-cpl-2 = refl

-- both arguments total:  plus (2 , 3) = 5
plus-tot : Eq (sem two plusTr (cons (fcpl two) (cons (fcpl three) nil)))
              (evalF plusPR (cons (fcpl two) (cons (fcpl three) nil)))
plus-tot = refl

plus-tot-val : Eq (sem two plusTr (cons (fcpl two) (cons (fcpl three) nil)))
                  (fcpl (suc (suc three)))
plus-tot-val = refl

------------------------------------------------------------------------
-- SHARING:  f (x) = g (x , x),  g (0 , v) = 0,  g (S u , v) = v
--
-- so `f` is the identity.  This is the term that killed the first
-- `TrComp` (see `TrShare`); here it is run through `traceOf`.
------------------------------------------------------------------------

gPR : PR
gPR = prec zerf (proj two)

fPR : PR
fPR = comp gPR (cons (proj zero) (cons (proj zero) nil))

f-wf : Wf fPR one
f-wf =
  mkSigma (mkSigma one (mkSigma refl (mkSigma tt tt)))
    (mkSigma tt (mkSigma tt tt))

fTr : Tr one
fTr = traceOf fPR one f-wf

f-0 : Eq (sem one fTr (cons (fbot zero) nil))
         (evalF fPR (cons (fbot zero) nil))
f-0 = refl

f-2 : Eq (sem one fTr (cons (fbot two) nil))
         (evalF fPR (cons (fbot two) nil))
f-2 = refl

f-3 : Eq (sem one fTr (cons (fbot three) nil))
         (evalF fPR (cons (fbot three) nil))
f-3 = refl

-- ... and the values really are the identity, not something constant
f-val-2 : Eq (sem one fTr (cons (fbot two) nil)) (fbot two)
f-val-2 = refl

f-val-3 : Eq (sem one fTr (cons (fbot three) nil)) (fbot three)
f-val-3 = refl
