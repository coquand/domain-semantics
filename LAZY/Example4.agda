{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- LAZY/Example4.agda
--
-- The paper's Example 4 (henderson.pdf, section II), as a DERIVATION in
-- the observation relation of LAZY.Obs.
--
--     alpha : (FUNARG
--               ((LAMBDA INTS (CAR (CDR (INTS 0))))
--                (LABEL INTEGERS
--                  (LAMBDA I (CONS I (INTEGERS (PLUS I 1)))))))
--
-- The paper runs its lazy evaluator on this for two pages and ends with
-- "Return to alpha, Apply C -- alpha: 1".  Here we exhibit instead the
-- semantic fact that the evaluator is supposed to preserve:
--
--     mu |- alpha , empty |-> At (num 1)
--
-- i.e. 1 is a finite observation of the value of alpha in the INITIAL
-- memory.  No reduction rule is used: this is L3 only.
--
-- The point of the exercise is that the derivation goes through the
-- CIRCULAR definition of INTEGERS twice, using obs-label at two
-- unfolding depths, with no fixed point ever constructed.
--
-- (--exact-split is off here only because the memory is a Nat-indexed
-- partial function written with a catch-all clause.)
------------------------------------------------------------------------

module LAZY.Example4 where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Obs

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

INTS INTEGERS I : Var
INTS     = 0
INTEGERS = 1
I        = 2

------------------------------------------------------------------------
-- The memory.  Addresses, following the paper's layout; the addresses
-- it leaves unnamed ("each pair of parentheses indicates the presence of
-- an unnamed address") are given numbers here.
--
--    0  alpha  (FUNARG 1 <empty>)
--    1         (2 3)                        the outer application
--    2         (LAMBDA INTS 4)
--    3         (LABEL INTEGERS 9)
--    4         (CAR 5)
--    5         (CDR 6)
--    6         (7 8)                        (INTS 0)
--    7         INTS
--    8         (QUOTE 0)
--    9         (LAMBDA I 10)
--   10         (CONS 11 12)
--   11         I
--   12         (13 14)                      (INTEGERS (PLUS I 1))
--   13         INTEGERS
--   14         (PLUS 15 16)
--   15         I
--   16         (QUOTE 1)
------------------------------------------------------------------------

mu : Heap
mu 0  = just (efunarg 1 nil)
mu 1  = just (eapp 2 3)
mu 2  = just (elam INTS 4)
mu 3  = just (elabel INTEGERS 9)
mu 4  = just (ecar 5)
mu 5  = just (ecdr 6)
mu 6  = just (eapp 7 8)
mu 7  = just (evar INTS)
mu 8  = just (equote (num 0))
mu 9  = just (elam I 10)
mu 10 = just (econs 11 12)
mu 11 = just (evar I)
mu 12 = just (eapp 13 14)
mu 13 = just (evar INTEGERS)
mu 14 = just (eplus 15 16)
mu 15 = just (evar I)
mu 16 = just (equote (num 1))
mu _  = nothing

------------------------------------------------------------------------
-- The two approximants to INTEGERS that the derivation needs.
--
--   u1 : "given 1, I produce a list whose head is 1"      (1 unfolding)
--   u2 : "given 0, I produce a list whose head is 0 and
--         whose second element is 1"                      (2 unfoldings)
--
-- These are exactly F(Bot) and F(F(Bot)) restricted to the demands the
-- computation actually makes -- the paper's V_1, V_2, but as finite
-- codes rather than as stages of a limit.
------------------------------------------------------------------------

u1 : FinEl
u1 = Fn (cons (mkSigma (At (num 1)) (Prd (At (num 1)) Bot)) nil)

u2 : FinEl
u2 = Fn (cons (mkSigma (At (num 0))
                       (Prd (At (num 0)) (Prd (At (num 1)) Bot))) nil)

-- Their coherence: one entry, coherent key, coherent non-Bot value,
-- nothing to be compatible with.
coh1 : CoherentFun (cons (mkSigma (At (num 1)) (Prd (At (num 1)) Bot)) nil)
coh1 = mkCF tt (mkSigma tt tt) tt tt tt

coh2 : CoherentFun
         (cons (mkSigma (At (num 0))
                        (Prd (At (num 0)) (Prd (At (num 1)) Bot))) nil)
coh2 = mkCF tt (mkSigma tt (mkSigma tt tt)) tt tt tt

------------------------------------------------------------------------
-- First unfolding of the LABEL:  Bot  |->  u1
--
-- With INTEGERS bound to Bot the recursive call (INTEGERS (PLUS I 1))
-- can only be observed as Bot, so the list stops after its head.
------------------------------------------------------------------------

round1 : Obs mu 3 emptyEnv u1
round1 =
  obs-label refl
    obs-bot
    (obs-lam refl coh1
      (og-cons
        (obs-cons refl
          (obs-var refl)     -- 11 : I      |-> At (num 1)
          obs-bot)           -- 12 : the recursive call, unobservable yet
        og-nil))

------------------------------------------------------------------------
-- Second unfolding:  u1  |->  u2
--
-- Now INTEGERS is bound to u1, so the recursive call at 12 CAN be
-- observed: PLUS turns I = 0 into 1, and u1 answers the demand 1.
------------------------------------------------------------------------

round2 : Obs mu 3 emptyEnv u2
round2 =
  obs-label refl
    round1
    (obs-lam refl coh2
      (og-cons
        (obs-cons refl
          (obs-var refl)     -- 11 : I |-> At (num 0)
          (obs-app refl
            (obs-var refl)   -- 13 : INTEGERS |-> u1
            (obs-plus refl
              (obs-var refl)   -- 15 : I       |-> At (num 0)
              (obs-quote refl))  -- 16 : (QUOTE 1)
            in-here))
        og-nil))

------------------------------------------------------------------------
-- The body of the outer LAMBDA:  car (cdr (INTS 0))  observes 1,
-- provided INTS is bound to u2.
------------------------------------------------------------------------

body : Obs mu 4 (ext emptyEnv INTS u2) (At (num 1))
body =
  obs-car refl                       -- 4 : (CAR 5)
    (obs-cdr refl                    -- 5 : (CDR 6)
      (obs-app refl                  -- 6 : (INTS 0)
        (obs-var refl)               -- 7 : INTS |-> u2
        (obs-quote refl)             -- 8 : (QUOTE 0)
        in-here))

------------------------------------------------------------------------
-- The answer.
------------------------------------------------------------------------

example4 : Observes mu 0 (At (num 1))
example4 =
  obs-funarg refl oa-nil             -- 0 : (FUNARG 1 <empty>)
    (obs-app refl                    -- 1 : (2 3)
      (obs-lam refl (mkCF coh2 tt tt tt tt)
        (og-cons body og-nil))               -- 2 : (LAMBDA INTS 4)
      round2                                 -- 3 : the LABEL
      in-here)

------------------------------------------------------------------------
-- Sanity: the same memory also observes the FIRST element of the list,
-- car (integers 0) = 0, at only ONE unfolding -- and observes nothing
-- but Bot if the LABEL is never unfolded.
------------------------------------------------------------------------

u1' : FinEl
u1' = Fn (cons (mkSigma (At (num 0)) (Prd (At (num 0)) Bot)) nil)

coh1' : CoherentFun (cons (mkSigma (At (num 0)) (Prd (At (num 0)) Bot)) nil)
coh1' = mkCF tt (mkSigma tt tt) tt tt tt

round1' : Obs mu 3 emptyEnv u1'
round1' =
  obs-label refl
    obs-bot
    (obs-lam refl coh1'
      (og-cons (obs-cons refl (obs-var refl) obs-bot) og-nil))
