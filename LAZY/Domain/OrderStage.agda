{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderStage.agda        (L1, part 1)
--
-- Sup, Comp, Coherent, and the STAGE-STRATIFIED information order.
--
-- Port of MIN/Domain/OrderStage.agda.  The problem it solves is the same
-- here as there: the order on the reflexive summand,
--
--     Fn g <= Fn h   iff   for every (u,v) in g,  v <= (h applied to u)
--
-- makes <= and application mutually recursive, with no obvious
-- decreasing measure (the result of applying h has RANK bounded by h's,
-- not below it).  The fix, unchanged from MIN: build the order at a
-- STAGE index by structural recursion on the stage, taking the
-- "vertical" recursions (compare a component / a value of the graph)
-- through the PREDECESSOR bundle, so one stage step strips one RANK
-- level; then read the public order off at the canonical stage
-- suc (max (RANK u) (RANK v)) and prove stability above the rank.
--
-- Adaptation to the Henderson-Morris domain:
--   * UCode        -> At a       (order clause is AtEq, not Top)
--   * PiCode a f   -> Prd u v    (STRICTLY SIMPLER: both components are
--                                 elements, both compared at the
--                                 predecessor stage; no FinFun tail)
--   * FunEl / FinFun clauses are unchanged.
--
-- ONE DELIBERATE DIVERGENCE FROM MIN.  MIN has
--     Coherent (FunEl g) = CoherentFun g,  CoherentFun nil = Empty,
-- i.e. the empty graph is not a legal value.  Here Coherent (Fn nil) is
-- Top: in Reynolds's separated sum, Fn nil is the least FUNCTION, the
-- element that carries the observation "this is a function" and nothing
-- more -- which is exactly what the answer (FUNARG(LAMBDA..)..) reveals.
--
-- NO postulates.
------------------------------------------------------------------------

module LAZY.Domain.OrderStage where

open import LAZY.Domain.Basic

------------------------------------------------------------------------
-- Compatible supremum
------------------------------------------------------------------------

-- Sup of two atoms: they join iff they are equal, else Bot marks the
-- incompatibility (the same convention MIN uses).
supAt : Nat -> Atom -> Atom -> FinEl
supAt zero    a b = Bot
supAt (suc n) a b = At a

Sup : FinEl -> FinEl -> FinEl
Sup Bot        x           = x
Sup (At a)     Bot         = At a
Sup (At a)     (At b)      = supAt (atEqN a b) a b
Sup (At a)     (Prd u v)   = Bot
Sup (At a)     (Fn h)      = Bot
Sup (Prd u v)  Bot         = Prd u v
Sup (Prd u v)  (At b)      = Bot
Sup (Prd u v)  (Prd u' v') = Prd (Sup u u') (Sup v v')
Sup (Prd u v)  (Fn h)      = Bot
Sup (Fn g)     Bot         = Fn g
Sup (Fn g)     (At b)      = Bot
Sup (Fn g)     (Prd u v)   = Bot
Sup (Fn g)     (Fn h)      = Fn (append g h)

------------------------------------------------------------------------
-- Compatibility and coherence.
--
-- Structural and INDEPENDENT of the order's recursion -- Comp and
-- Coherent never mention the order or application, so they live safely
-- in the definition layer.
------------------------------------------------------------------------

mutual
  Comp : FinEl -> FinEl -> Set
  Comp Bot        x           = Top
  Comp (At a)     Bot         = Top
  Comp (At a)     (At b)      = AtEq a b
  Comp (At a)     (Prd u v)   = Empty
  Comp (At a)     (Fn h)      = Empty
  Comp (Prd u v)  Bot         = Top
  Comp (Prd u v)  (At b)      = Empty
  Comp (Prd u v)  (Prd u' v') = Pair (Comp u u') (Comp v v')
  Comp (Prd u v)  (Fn h)      = Empty
  Comp (Fn g)     Bot         = Top
  Comp (Fn g)     (At b)      = Empty
  Comp (Fn g)     (Prd u v)   = Empty
  Comp (Fn g)     (Fn h)      = CompFun g h

  CompFun : FinFun -> FinFun -> Set
  CompFun nil        g = Top
  CompFun (cons s f) g = Pair (CompStepFun s g) (CompFun f g)

  CompStepFun : Pair FinEl FinEl -> FinFun -> Set
  CompStepFun s nil        = Top
  CompStepFun s (cons t g) = Pair (CompStepStep s t) (CompStepFun s g)

  CompStepStep : Pair FinEl FinEl -> Pair FinEl FinEl -> Set
  CompStepStep s t = Comp (fst s) (fst t) -> Comp (snd s) (snd t)

mutual
  Coherent : FinEl -> Set
  Coherent Bot       = Top
  Coherent (At a)    = Top
  Coherent (Prd u v) = Pair (Coherent u) (Coherent v)
  Coherent (Fn g)    = CoherentFun g

  record CFcons (p : Pair FinEl FinEl) (ps : FinFun) : Set where
    inductive
    constructor mkCF
    field
      key-coh  : Coherent (fst p)
      val-coh  : Coherent (snd p)
      val-nbot : NotBot (snd p)
      compat   : CoherentWith p ps
      tail-coh : CoherentFun ps

  -- NB: nil IS coherent here (unlike MIN) -- see the header.
  CoherentFun : FinFun -> Set
  CoherentFun nil         = Top
  CoherentFun (cons p ps) = CFcons p ps

  CoherentWith : Pair FinEl FinEl -> FinFun -> Set
  CoherentWith p nil         = Top
  CoherentWith p (cons q qs) =
    Pair (Comp (fst p) (fst q) -> Comp (snd p) (snd q))
         (CoherentWith p qs)

------------------------------------------------------------------------
-- One stage of the order.
------------------------------------------------------------------------

-- one evaluation step: include `w` in the running Sup iff the key fired
evCombine : Nat -> FinEl -> FinEl -> FinEl
evCombine zero    _ r = r
evCombine (suc _) w r = Sup w r

record OrderBundle : Set1 where
  field
    leq  : FinEl  -> FinEl -> Set
    leqf : FinFun -> FinFun -> Set
    lei  : FinEl  -> FinEl -> Nat
    lef  : FinFun -> FinFun -> Nat
    ev   : FinFun -> FinEl -> FinEl

-- Stage 0: correct on the rank-0 codes (Bot and atoms), trivially false
-- on the compound ones.  Compound codes have RANK >= 1 so their
-- canonical stage is >= 1 and never lands here.
trivBundle : OrderBundle
trivBundle = record { leq = leq0 ; leqf = leqf0 ; lei = lei0 ; lef = lef0 ; ev = ev0 }
  where
    leq0 : FinEl -> FinEl -> Set
    leq0 Bot        _         = Top
    leq0 (At a)     Bot       = Empty
    leq0 (At a)     (At b)    = AtEq a b
    leq0 (At a)     (Prd _ _) = Empty
    leq0 (At a)     (Fn _)    = Empty
    leq0 (Prd _ _)  _         = Empty
    leq0 (Fn _)     _         = Empty

    leqf0 : FinFun -> FinFun -> Set
    leqf0 nil        _ = Top
    leqf0 (cons _ _) _ = Empty

    lei0 : FinEl -> FinEl -> Nat
    lei0 Bot        _         = suc zero
    lei0 (At a)     Bot       = zero
    lei0 (At a)     (At b)    = atEqN a b
    lei0 (At a)     (Prd _ _) = zero
    lei0 (At a)     (Fn _)    = zero
    lei0 (Prd _ _)  _         = zero
    lei0 (Fn _)     _         = zero

    lef0 : FinFun -> FinFun -> Nat
    lef0 nil        _ = suc zero
    lef0 (cons _ _) _ = zero

    ev0 : FinFun -> FinEl -> FinEl
    ev0 nil        _ = Bot
    ev0 (cons _ _) _ = Bot

------------------------------------------------------------------------
-- buildOrderStage : level-(suc n) operations from the level-n bundle B.
------------------------------------------------------------------------

buildOrderStage : OrderBundle -> OrderBundle
buildOrderStage B =
  record { leq = leq' ; leqf = leqf' ; lei = lei' ; lef = lef' ; ev = ev' }
  where
    open OrderBundle B renaming (leq to leqP ; lei to leiP)

    -- internal application: structural on the graph, decision via leiP
    ev' : FinFun -> FinEl -> FinEl
    ev' nil         u = Bot
    ev' (cons p ps) u = evCombine (leiP (fst p) u) (snd p) (ev' ps u)

    -- NO-LAG: leqf'/lef' apply via the SAME-stage ev' (not the
    -- predecessor), so a stage-(suc m) comparison resolves rank-m
    -- arguments correctly and stability has no off-by-one.

    leqf' : FinFun -> FinFun -> Set
    leqf' nil         _ = Top
    leqf' (cons p ps) h = Pair (leqP (snd p) (ev' h (fst p))) (leqf' ps h)

    leq' : FinEl -> FinEl -> Set
    leq' Bot        _           = Top
    leq' (At a)     Bot         = Empty
    leq' (At a)     (At b)      = AtEq a b
    leq' (At a)     (Prd _ _)   = Empty
    leq' (At a)     (Fn _)      = Empty
    leq' (Prd u v)  Bot         = Empty
    leq' (Prd u v)  (At b)      = Empty
    leq' (Prd u v)  (Prd u' v') = Pair (leqP u u') (leqP v v')
    leq' (Prd u v)  (Fn _)      = Empty
    leq' (Fn g)     Bot         = Empty
    leq' (Fn g)     (At b)      = Empty
    leq' (Fn g)     (Prd _ _)   = Empty
    leq' (Fn g)     (Fn h)      = leqf' g h

    lef' : FinFun -> FinFun -> Nat
    lef' nil         _ = suc zero
    lef' (cons p ps) h = min (leiP (snd p) (ev' h (fst p))) (lef' ps h)

    lei' : FinEl -> FinEl -> Nat
    lei' Bot        _           = suc zero
    lei' (At a)     Bot         = zero
    lei' (At a)     (At b)      = atEqN a b
    lei' (At a)     (Prd _ _)   = zero
    lei' (At a)     (Fn _)      = zero
    lei' (Prd u v)  Bot         = zero
    lei' (Prd u v)  (At b)      = zero
    lei' (Prd u v)  (Prd u' v') = min (leiP u u') (leiP v v')
    lei' (Prd u v)  (Fn _)      = zero
    lei' (Fn g)     Bot         = zero
    lei' (Fn g)     (At b)      = zero
    lei' (Fn g)     (Prd _ _)   = zero
    lei' (Fn g)     (Fn h)      = lef' g h

------------------------------------------------------------------------
-- The stratified family, by structural recursion on the stage index.
------------------------------------------------------------------------

Stage : Nat -> OrderBundle
Stage zero    = trivBundle
Stage (suc n) = buildOrderStage (Stage n)

module OB (n : Nat) = OrderBundle (Stage n)

------------------------------------------------------------------------
-- Public order at the canonical stage.
------------------------------------------------------------------------

LeqC : FinEl -> FinEl -> Set
LeqC u v = OrderBundle.leq (Stage (suc (max (RANK u) (RANK v)))) u v

leiC : FinEl -> FinEl -> Nat
leiC u v = OrderBundle.lei (Stage (suc (max (RANK u) (RANK v)))) u v

------------------------------------------------------------------------
-- RANK arithmetic for Sup / append / ev.
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

RANK-supAt : (w : Nat) (a b : Atom) -> Le (RANK (supAt w a b)) zero
RANK-supAt zero    a b = tt
RANK-supAt (suc n) a b = tt

RANK-Sup : (x y : FinEl) -> Le (RANK (Sup x y)) (max (RANK x) (RANK y))
RANK-Sup Bot        y           = Le-refl (RANK y)
RANK-Sup (At a)     Bot         = tt
RANK-Sup (At a)     (At b)      = RANK-supAt (atEqN a b) a b
RANK-Sup (At a)     (Prd u v)   = tt
RANK-Sup (At a)     (Fn h)      = tt
RANK-Sup (Prd u v)  Bot         = Le-refl (RANK (Prd u v))
RANK-Sup (Prd u v)  (At b)      = tt
RANK-Sup (Prd u v)  (Prd u' v') =
  Le-trans (max (RANK (Sup u u')) (RANK (Sup v v')))
           (max (max (RANK u) (RANK u')) (max (RANK v) (RANK v')))
           (max (max (RANK u) (RANK v)) (max (RANK u') (RANK v')))
    (max-mono (RANK (Sup u u')) (RANK (Sup v v'))
              (max (RANK u) (RANK u')) (max (RANK v) (RANK v'))
              (RANK-Sup u u') (RANK-Sup v v'))
    (shuffle (RANK u) (RANK v) (RANK u') (RANK v'))
  where
    -- max (max a c) (max b d)  <=  max (max a b) (max c d)
    shuffle : (a b c d : Nat) ->
              Le (max (max a c) (max b d)) (max (max a b) (max c d))
    shuffle a b c d =
      Le-max-lub (max a c) (max b d) rhs
        (Le-max-lub a c rhs
          (Le-trans a (max a b) rhs (Le-max-l a b) (Le-max-l (max a b) (max c d)))
          (Le-trans c (max c d) rhs (Le-max-l c d) (Le-max-r (max a b) (max c d))))
        (Le-max-lub b d rhs
          (Le-trans b (max a b) rhs (Le-max-r a b) (Le-max-l (max a b) (max c d)))
          (Le-trans d (max c d) rhs (Le-max-r c d) (Le-max-r (max a b) (max c d))))
      where rhs = max (max a b) (max c d)
RANK-Sup (Prd u v)  (Fn h)      = tt
RANK-Sup (Fn g)     Bot         = Le-refl (RANK (Fn g))
RANK-Sup (Fn g)     (At b)      = tt
RANK-Sup (Fn g)     (Prd u v)   = tt
RANK-Sup (Fn g)     (Fn h)      = RANK-append g h

------------------------------------------------------------------------
-- RANK-ev : RANK (ev n h u) <= RANKFun h
------------------------------------------------------------------------

RANK-evCombine : (w : Nat) (x r : FinEl) ->
  Le (RANK (evCombine w x r)) (max (RANK x) (RANK r))
RANK-evCombine zero    x r = Le-max-r (RANK x) (RANK r)
RANK-evCombine (suc _) x r = RANK-Sup x r

RANK-ev : (n : Nat) (h : FinFun) (u : FinEl) ->
  Le (RANK (OB.ev n h u)) (RANKFun h)
RANK-ev zero    nil        u = tt
RANK-ev zero    (cons _ _) u = tt
RANK-ev (suc n) nil        u = tt
RANK-ev (suc n) (cons p ps) u =
  Le-trans (RANK (OB.ev (suc n) (cons p ps) u))
    (max (RANK (snd p)) (RANK (OB.ev (suc n) ps u)))
    (RANKFun (cons p ps))
    (RANK-evCombine (OB.lei n (fst p) u) (snd p) (OB.ev (suc n) ps u))
    (Le-trans (max (RANK (snd p)) (RANK (OB.ev (suc n) ps u)))
      (max (RANK (snd p)) (RANKFun ps))
      (RANKFun (cons p ps))
      (max-mono (RANK (snd p)) (RANK (OB.ev (suc n) ps u))
                (RANK (snd p)) (RANKFun ps)
                (Le-refl (RANK (snd p))) (RANK-ev (suc n) ps u))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))))
