{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- Rank.agda  (NAT/ — Pi + U fragment)
--
-- The iterative-stage RANK on finite elements (NOT the syntactic size
-- measure `rk` in Basic, which counts cons cells and does NOT satisfy
-- the bounds below — see RankCounterexamplesSigma).
--
--   RANK Bot = RANK UCode = 0
--   RANK (FunEl g)    = 1 + RANKFun g
--   RANK (PiCode a f) = 1 + max (RANK a) (RANKFun f)
--   RANKFun nil       = 0
--   RANKFun (cons p ps) = max (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))
--                         -- NO `suc` per cons
--
-- Key bounds (for rank-stratified Val_n):
--   RANK a < RANK (PiCode a f),  RANKFun g < RANK (FunEl g)
--   RANKFun (append f g) <= max (RANKFun f) (RANKFun g)
--   RANK (Sup x y)       <= max (RANK x) (RANK y)
--   RANK (EvalFun f u)   <= RANKFun f      <      RANK (FunEl f)
--   applyEl x v <> Bot   ->  RANK (applyEl x v) < RANK x
--
-- 0 postulates.
------------------------------------------------------------------------

module MAHLOINJ.Domain.Rank where

open import MAHLOINJ.Domain.Basic
  using (Nat ; zero ; suc ; max ; Le ; Le-refl ; Le-trans ; Le-suc ;
         Le-max-l ; Le-max-r ; Top ; tt ; Empty ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode ;
         FinFun ; List ; nil ; cons ; Pair ; fst ; snd)
open import MAHLOINJ.Domain.Kernel
  using (Sup ; append ; applyEl ; EvalFun ; EvalFun-step ; leFinEl ; NotBot)

------------------------------------------------------------------------
-- max / Le toolkit
------------------------------------------------------------------------

-- least upper bound
Le-max-lub : (a b c : Nat) -> Le a c -> Le b c -> Le (max a b) c
Le-max-lub zero    b       c       h1 h2 = h2
Le-max-lub (suc a) zero    c       h1 h2 = h1
Le-max-lub (suc a) (suc b) zero    () h2
Le-max-lub (suc a) (suc b) (suc c) h1 h2 = Le-max-lub a b c h1 h2

-- monotonicity of max in both arguments
max-mono : (a b c d : Nat) -> Le a c -> Le b d -> Le (max a b) (max c d)
max-mono a b c d hac hbd =
  Le-max-lub a b (max c d)
    (Le-trans a c (max c d) hac (Le-max-l c d))
    (Le-trans b d (max c d) hbd (Le-max-r c d))

------------------------------------------------------------------------
-- Component 1: RANK / RANKFun
------------------------------------------------------------------------

open import MAHLOINJ.Domain.OrderStage public using (RANK ; RANKFun ; RANK-append ; RANK-Sup)

------------------------------------------------------------------------
-- Component 2: structural inequalities
------------------------------------------------------------------------

-- RANK a < RANK (PiCode a f)
RANK-dom : (a : FinEl) (f : FinFun) -> Le (suc (RANK a)) (RANK (PiCode a f))
RANK-dom a f = Le-max-l (RANK a) (RANKFun f)

-- RANKFun f < RANK (PiCode a f)
RANK-cod : (a : FinEl) (f : FinFun) -> Le (suc (RANKFun f)) (RANK (PiCode a f))
RANK-cod a f = Le-max-r (RANK a) (RANKFun f)

-- RANKFun g < RANK (FunEl g)
RANK-fun : (g : FinFun) -> Le (suc (RANKFun g)) (RANK (FunEl g))
RANK-fun g = Le-refl (suc (RANKFun g))

------------------------------------------------------------------------
-- Component 3: RANK-append
------------------------------------------------------------------------

-- (RANK-append is re-exported from OrderStage)

------------------------------------------------------------------------
-- Component 4: RANK-Sup  (RANK (Sup x y) <= max (RANK x) (RANK y))
--
-- Structural recursion on x, y; the only recursive call is RANK-Sup a b
-- on strict sub-codes in the (PiCode, PiCode) case.
------------------------------------------------------------------------

-- (RANK-Sup is re-exported from OrderStage)

------------------------------------------------------------------------
-- Component 5: RANK-EvalFun  (RANK (EvalFun f u) <= RANKFun f)
------------------------------------------------------------------------

mutual
  RANK-EvalFun : (f : FinFun) (u : FinEl) ->
    Le (RANK (EvalFun f u)) (RANKFun f)
  RANK-EvalFun nil u = tt
  RANK-EvalFun (cons p ps) u =
    Le-trans (RANK (EvalFun-step (leFinEl (fst p) u) (snd p) ps u))
             (max (RANK (snd p)) (RANKFun ps))
             (RANKFun (cons p ps))
             (RANK-EvalFun-step (leFinEl (fst p) u) (snd p) ps u)
             (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

  RANK-EvalFun-step : (n : Nat) (bi : FinEl) (rest : FinFun) (u : FinEl) ->
    Le (RANK (EvalFun-step n bi rest u)) (max (RANK bi) (RANKFun rest))
  RANK-EvalFun-step zero bi rest u =
    Le-trans (RANK (EvalFun rest u)) (RANKFun rest)
             (max (RANK bi) (RANKFun rest))
             (RANK-EvalFun rest u) (Le-max-r (RANK bi) (RANKFun rest))
  RANK-EvalFun-step (suc n) bi rest u =
    Le-trans (RANK (Sup bi (EvalFun rest u)))
             (max (RANK bi) (RANK (EvalFun rest u)))
             (max (RANK bi) (RANKFun rest))
             (RANK-Sup bi (EvalFun rest u))
             (max-mono (RANK bi) (RANK (EvalFun rest u))
                       (RANK bi) (RANKFun rest)
                       (Le-refl (RANK bi)) (RANK-EvalFun rest u))

------------------------------------------------------------------------
-- Component 6: strict bounds for application
------------------------------------------------------------------------

-- RANK (EvalFun g u) < RANK (FunEl g)  (unconditional)
RANK-EvalFun-strict : (g : FinFun) (u : FinEl) ->
  Le (suc (RANK (EvalFun g u))) (RANK (FunEl g))
RANK-EvalFun-strict g u = RANK-EvalFun g u

-- applyEl x v <> Bot  ->  RANK (applyEl x v) < RANK x
-- (non-Bot forces x = FunEl g; for Bot/UCode/PiCode the result is Bot.)
RANK-applyEl : (x v : FinEl) -> NotBot (applyEl x v) ->
  Le (suc (RANK (applyEl x v))) (RANK x)
RANK-applyEl Bot          v ()
RANK-applyEl UCode        v ()
RANK-applyEl (FunEl g)    v nb = RANK-EvalFun-strict g v
RANK-applyEl (PiCode a f) v ()
RANK-applyEl NatCode      v ()
RANK-applyEl ZeroEl       v ()
RANK-applyEl (SucEl a)    v ()
