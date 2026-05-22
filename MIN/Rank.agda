{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Rank.agda  (MIN/ — Pi + U fragment)
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

module MIN.Rank where

open import MIN.Basic
  using (Nat ; zero ; suc ; max ; Le ; Le-refl ; Le-trans ; Le-suc ;
         Le-max-l ; Le-max-r ; Top ; tt ; Empty ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ;
         FinFun ; List ; nil ; cons ; Pair ; fst ; snd)
open import MIN.PaperSemantics
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

mutual
  RANK : FinEl -> Nat
  RANK Bot          = zero
  RANK UCode        = zero
  RANK (FunEl g)    = suc (RANKFun g)
  RANK (PiCode a f) = suc (max (RANK a) (RANKFun f))

  RANKFun : FinFun -> Nat
  RANKFun nil         = zero
  RANKFun (cons p ps) = max (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

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

RANK-append : (f g : FinFun) ->
  Le (RANKFun (append f g)) (max (RANKFun f) (RANKFun g))
RANK-append nil g = Le-refl (RANKFun g)
RANK-append (cons p ps) g =
  let a   = RANK (fst p)
      b   = RANK (snd p)
      cps = RANKFun ps
      dg  = RANKFun g
      c'  = RANKFun (append ps g)
      rhs = max (max a (max b cps)) dg
      ih  : Le c' (max cps dg)
      ih  = RANK-append ps g
      leA : Le a rhs
      leA = Le-trans a (max a (max b cps)) rhs
              (Le-max-l a (max b cps)) (Le-max-l (max a (max b cps)) dg)
      leB : Le b rhs
      leB = Le-trans b (max a (max b cps)) rhs
              (Le-trans b (max b cps) (max a (max b cps))
                 (Le-max-l b cps) (Le-max-r a (max b cps)))
              (Le-max-l (max a (max b cps)) dg)
      leCps : Le cps (max a (max b cps))
      leCps = Le-trans cps (max b cps) (max a (max b cps))
                (Le-max-r b cps) (Le-max-r a (max b cps))
      leC' : Le c' rhs
      leC' = Le-trans c' (max cps dg) rhs ih
               (max-mono cps dg (max a (max b cps)) dg leCps (Le-refl dg))
  in Le-max-lub a (max b c') rhs leA
       (Le-max-lub b c' rhs leB leC')

------------------------------------------------------------------------
-- Component 4: RANK-Sup  (RANK (Sup x y) <= max (RANK x) (RANK y))
--
-- Structural recursion on x, y; the only recursive call is RANK-Sup a b
-- on strict sub-codes in the (PiCode, PiCode) case.
------------------------------------------------------------------------

RANK-Sup : (x y : FinEl) -> Le (RANK (Sup x y)) (max (RANK x) (RANK y))
RANK-Sup Bot          y             = Le-refl (RANK y)
RANK-Sup UCode        Bot           = tt
RANK-Sup UCode        UCode         = tt
RANK-Sup UCode        (FunEl g)     = tt
RANK-Sup UCode        (PiCode b g)  = tt
RANK-Sup (FunEl g)    Bot           = Le-refl (RANK (FunEl g))
RANK-Sup (FunEl g)    UCode         = tt
RANK-Sup (FunEl g)    (FunEl h)     = RANK-append g h
RANK-Sup (FunEl g)    (PiCode b h)  = tt
RANK-Sup (PiCode a f) Bot           = Le-refl (RANK (PiCode a f))
RANK-Sup (PiCode a f) UCode         = tt
RANK-Sup (PiCode a f) (FunEl h)     = tt
RANK-Sup (PiCode a f) (PiCode b g)  =
  let ra = RANK a ; rb = RANK b ; rf = RANKFun f ; rg = RANKFun g
      p = RANK (Sup a b) ; q = RANKFun (append f g)
      laf = max ra rf ; lbg = max rb rg
      rhs = max laf lbg
      hP : Le p (max ra rb)
      hP = RANK-Sup a b
      hQ : Le q (max rf rg)
      hQ = RANK-append f g
      le-ab : Le (max ra rb) rhs
      le-ab = Le-max-lub ra rb rhs
        (Le-trans ra laf rhs (Le-max-l ra rf) (Le-max-l laf lbg))
        (Le-trans rb lbg rhs (Le-max-l rb rg) (Le-max-r laf lbg))
      le-fg : Le (max rf rg) rhs
      le-fg = Le-max-lub rf rg rhs
        (Le-trans rf laf rhs (Le-max-r ra rf) (Le-max-l laf lbg))
        (Le-trans rg lbg rhs (Le-max-r rb rg) (Le-max-r laf lbg))
      leP : Le p rhs
      leP = Le-trans p (max ra rb) rhs hP le-ab
      leQ : Le q rhs
      leQ = Le-trans q (max rf rg) rhs hQ le-fg
  in Le-max-lub p q rhs leP leQ

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
