{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStage.agda  (MIN/ — Pi + U fragment)
--
-- Stage-stratified order on finite elements, defined INDEPENDENTLY of
-- the public EvalFun (so the EvalFun <-> order cycle is broken).
--
-- The order at stage `n` is built by structural recursion on `n`
-- (the GoodStage / ValidityStratified `Bundle` template, one level
-- down): `buildOrderStage` builds the level-(suc n) operations from the
-- level-n bundle.  The "vertical" recursions -- comparing/evaluating at
-- a strictly smaller RANK (domain `a`, codomain value `ev h u`) -- go
-- through the predecessor bundle, so one Stage step strips one RANK
-- level.  The "horizontal" recursions (down a FinFun list) stay at the
-- same stage and are structural.
--
-- An INTERNAL stage-indexed evaluation `ev` is bundled here purely to
-- phrase the function-order clause without the public EvalFun.  It is
-- never re-exported; the cone consumes only the (collapsed, Set-valued)
-- order `Leq` and its abstract properties, so `ev`'s stage-collapse is
-- invisible (cf. the Val2 collapse).
--
-- NO postulates.
------------------------------------------------------------------------

module BCDE4.Dom.OrderStage where

open import BCDE4.Dom.Basic using (EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

open import BCDE4.Dom.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; min ; isPos ; min-isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun ; List ; nil ; cons
        ; EqL ; eqL ; EqL-trans )

------------------------------------------------------------------------
-- Structural, EvalFun-free primitives (inlined here to avoid an import
-- cycle with PaperOrder, which will later be re-founded on this file).
------------------------------------------------------------------------

append : FinFun -> FinFun -> FinFun
append nil         g = g
append (cons p ps) g = cons p (append ps g)

Sup : FinEl -> FinEl -> FinEl
Sup Bot             x             = x
Sup (UCode k)       Bot           = UCode k
Sup (UCode k)       (UCode m)     = UCode k
Sup (UCode k)       (FunEl g)     = Bot
Sup (UCode k)       (PiCode b g)  = Bot
Sup (UCode k)       LevTy         = Bot
Sup (UCode k)       (LevEl m)     = Bot
Sup LevTy           Bot           = LevTy
Sup LevTy           (UCode m)     = Bot
Sup LevTy           LevTy         = LevTy
Sup LevTy           (LevEl m)     = Bot
Sup LevTy           (FunEl h)     = Bot
Sup LevTy           (PiCode b h)  = Bot
Sup (LevEl k)       Bot           = LevEl k
Sup (LevEl k)       (UCode m)     = Bot
Sup (LevEl k)       LevTy         = Bot
Sup (LevEl k)       (LevEl m)     = LevEl k
Sup (LevEl k)       (FunEl h)     = Bot
Sup (LevEl k)       (PiCode b h)  = Bot
Sup (FunEl g)       Bot           = FunEl g
Sup (FunEl g)       (UCode m)     = Bot
Sup (FunEl g)       (FunEl h)     = FunEl (append g h)
Sup (FunEl g)       (PiCode b h)  = Bot
Sup (FunEl g)       LevTy         = Bot
Sup (FunEl g)       (LevEl m)     = Bot
Sup (PiCode a f)    Bot           = PiCode a f
Sup (PiCode a f)    (UCode m)     = Bot
Sup (PiCode a f)    (FunEl h)     = Bot
Sup (PiCode a f)    LevTy         = Bot
Sup (PiCode a f)    (LevEl m)     = Bot
Sup (UCode _)      (LPiCode g)    = Bot
Sup LevTy          (LPiCode g)    = Bot
Sup (LevEl _)      (LPiCode g)    = Bot
Sup (FunEl f)      (LPiCode g)    = Bot
Sup (PiCode a f)   (LPiCode g)    = Bot
Sup (LPiCode f)    Bot            = LPiCode f
Sup (LPiCode f)    (UCode _)      = Bot
Sup (LPiCode f)    LevTy          = Bot
Sup (LPiCode f)    (LevEl _)      = Bot
Sup (LPiCode f)    (FunEl _)      = Bot
Sup (LPiCode f)    (PiCode _ _)   = Bot
Sup (LPiCode f)    (LPiCode g)    = LPiCode (append f g)
Sup (PiCode a f)    (PiCode b g)  = PiCode (Sup a b) (append f g)

mutual
  RANK : FinEl -> Nat
  RANK Bot          = zero
  RANK (UCode _)    = zero
  RANK LevTy        = zero
  RANK (LevEl _)    = zero
  RANK (FunEl g)    = suc (RANKFun g)
  RANK (PiCode a f) = suc (max (RANK a) (RANKFun f))
  RANK (LPiCode f)  = suc (RANKFun f)

  RANKFun : FinFun -> Nat
  RANKFun nil         = zero
  RANKFun (cons p ps) = max (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

------------------------------------------------------------------------
-- Compatibility and Coherence (copied from PaperOrder; structural and
-- INDEPENDENT of the order's recursion -- Comp/Coherent never mention
-- leFinEl/EvalFun, so they live safely in the definition layer.  The
-- order properties refl/trans/Sup-* are conditional on Coherent.)
------------------------------------------------------------------------

mutual
  Comp : FinEl -> FinEl -> Set
  Comp Bot             x             = Top
  Comp (UCode k)       Bot           = Top
  Comp (UCode k)       (UCode m)     = EqL k m
  Comp (UCode k)       (FunEl g)     = Empty
  Comp (UCode k)       (PiCode b g)  = Empty
  Comp (UCode k)       LevTy         = Empty
  Comp (UCode k)       (LevEl m)     = Empty
  Comp LevTy           Bot           = Top
  Comp LevTy           (UCode m)     = Empty
  Comp LevTy           LevTy         = Top
  Comp LevTy           (LevEl m)     = Empty
  Comp LevTy           (FunEl h)     = Empty
  Comp LevTy           (PiCode b h)  = Empty
  Comp (LevEl k)       Bot           = Top
  Comp (LevEl k)       (UCode m)     = Empty
  Comp (LevEl k)       LevTy         = Empty
  Comp (LevEl k)       (LevEl m)     = EqL k m
  Comp (LevEl k)       (FunEl h)     = Empty
  Comp (LevEl k)       (PiCode b h)  = Empty
  Comp (FunEl g)       Bot           = Top
  Comp (FunEl g)       (UCode m)     = Empty
  Comp (FunEl g)       (FunEl h)     = CompFun g h
  Comp (FunEl g)       (PiCode b h)  = Empty
  Comp (FunEl g)       LevTy         = Empty
  Comp (FunEl g)       (LevEl m)     = Empty
  Comp (PiCode a f)    Bot           = Top
  Comp (PiCode a f)    (UCode m)     = Empty
  Comp (PiCode a f)    (FunEl h)     = Empty
  Comp (PiCode a f)    LevTy         = Empty
  Comp (PiCode a f)    (LevEl m)     = Empty
  Comp (UCode _)      (LPiCode g)    = Empty
  Comp LevTy          (LPiCode g)    = Empty
  Comp (LevEl _)      (LPiCode g)    = Empty
  Comp (FunEl _)      (LPiCode g)    = Empty
  Comp (PiCode _ _)   (LPiCode g)    = Empty
  Comp (LPiCode f)    Bot            = Top
  Comp (LPiCode f)    (UCode _)      = Empty
  Comp (LPiCode f)    LevTy          = Empty
  Comp (LPiCode f)    (LevEl _)      = Empty
  Comp (LPiCode f)    (FunEl _)      = Empty
  Comp (LPiCode f)    (PiCode _ _)   = Empty
  Comp (LPiCode f)    (LPiCode g)    = CompFun f g
  Comp (PiCode a f)    (PiCode b g)  = Pair (Comp a b) (CompFun f g)

  CompFun : FinFun -> FinFun -> Set
  CompFun nil         g = Top
  CompFun (cons s f)  g = Pair (CompStepFun s g) (CompFun f g)

  CompStepFun : Pair FinEl FinEl -> FinFun -> Set
  CompStepFun s nil         = Top
  CompStepFun s (cons t g)  = Pair (CompStepStep s t) (CompStepFun s g)

  CompStepStep : Pair FinEl FinEl -> Pair FinEl FinEl -> Set
  CompStepStep s t = Comp (fst s) (fst t) -> Comp (snd s) (snd t)

NotBot : FinEl -> Set
NotBot Bot             = Empty
NotBot (UCode _)       = Top
NotBot LevTy           = Top
NotBot (LevEl _)       = Top
NotBot (LPiCode _)     = Top
NotBot (FunEl g)       = Top
NotBot (PiCode a f)    = Top

mutual
  Coherent : FinEl -> Set
  Coherent Bot             = Top
  Coherent (UCode _)       = Top
  Coherent LevTy           = Top
  Coherent (LevEl _)       = Top
  Coherent (LPiCode f)     = CoherentFunTail f
  Coherent (FunEl g)       = CoherentFun g
  Coherent (PiCode a f)    = Pair (Coherent a) (CoherentFunTail f)

  CoherentFun : FinFun -> Set
  CoherentFun nil         = Empty
  CoherentFun (cons p ps) = CoherentFunTail (cons p ps)

  record CFTcons (p : Pair FinEl FinEl) (ps : FinFun) : Set where
    inductive
    constructor mkCFT
    field
      key-coh  : Coherent (fst p)
      val-coh  : Coherent (snd p)
      val-nbot : NotBot (snd p)
      compat   : CoherentWith p ps
      tail-coh : CoherentFunTail ps

  CoherentFunTail : FinFun -> Set
  CoherentFunTail nil         = Top
  CoherentFunTail (cons p ps) = CFTcons p ps

  CoherentWith : Pair FinEl FinEl -> FinFun -> Set
  CoherentWith p nil         = Top
  CoherentWith p (cons q qs) =
    Pair (Comp (fst p) (fst q) -> Comp (snd p) (snd q))
         (CoherentWith p qs)

cft-from-cf : (g : FinFun) -> CoherentFun g -> CoherentFunTail g
cft-from-cf nil         ()
cft-from-cf (cons p ps) coh = coh

------------------------------------------------------------------------
-- One stage of the order: the Set-valued order `leq`/`leqf`, the
-- numeric decision `lei`/`lef`, and the internal evaluation `ev`.
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

-- Minimal base (Stage 0): correct on atoms, trivially-false (Empty /
-- Bot / 0) on compound codes.  Compound codes have RANK >= 1, so their
-- canonical level is >= 1 and never lands on Stage 0; the base values
-- are only ever consulted above nothing and are <= every later stage,
-- which keeps upward monotonicity clean.
trivBundle : OrderBundle
trivBundle = record { leq = leq0 ; leqf = leqf0 ; lei = lei0 ; lef = lef0 ; ev = ev0 }
  where
    leq0 : FinEl -> FinEl -> Set
    leq0 Bot          _             = Top
    leq0 (UCode k)    Bot           = Empty
    leq0 (UCode k)    (UCode m)     = EqL k m
    leq0 (UCode k)    (FunEl _)     = Empty
    leq0 (UCode k)    (PiCode _ _)  = Empty
    leq0 (UCode k)    LevTy         = Empty
    leq0 (UCode k)    (LevEl _)     = Empty
    leq0 LevTy        Bot           = Empty
    leq0 LevTy        (UCode _)     = Empty
    leq0 LevTy        LevTy         = Top
    leq0 LevTy        (LevEl _)     = Empty
    leq0 LevTy        (FunEl _)     = Empty
    leq0 LevTy        (PiCode _ _)  = Empty
    leq0 (LevEl k)    Bot           = Empty
    leq0 (LevEl k)    (UCode _)     = Empty
    leq0 (LevEl k)    LevTy         = Empty
    leq0 (LevEl k)    (LevEl m)     = EqL k m
    leq0 (LevEl k)    (FunEl _)     = Empty
    leq0 (LevEl k)    (PiCode _ _)  = Empty
    leq0 (FunEl _)    _             = Empty
    leq0 (PiCode _ _) _             = Empty
    leq0 (UCode k) (LPiCode _)   = Empty
    leq0 LevTy (LPiCode _)   = Empty
    leq0 (LevEl k) (LPiCode _)   = Empty
    leq0 (LPiCode _)  _             = Empty

    leqf0 : FinFun -> FinFun -> Set
    leqf0 nil         _ = Top
    leqf0 (cons _ _)  _ = Empty

    lei0 : FinEl -> FinEl -> Nat
    lei0 Bot          _             = suc zero
    lei0 (UCode k)    Bot           = zero
    lei0 (UCode k)    (UCode m)     = eqL k m
    lei0 (UCode k)    (FunEl _)     = zero
    lei0 (UCode k)    (PiCode _ _)  = zero
    lei0 (UCode k)    LevTy         = zero
    lei0 (UCode k)    (LevEl _)     = zero
    lei0 LevTy        Bot           = zero
    lei0 LevTy        (UCode _)     = zero
    lei0 LevTy        LevTy         = suc zero
    lei0 LevTy        (LevEl _)     = zero
    lei0 LevTy        (FunEl _)     = zero
    lei0 LevTy        (PiCode _ _)  = zero
    lei0 (LevEl k)    Bot           = zero
    lei0 (LevEl k)    (UCode _)     = zero
    lei0 (LevEl k)    LevTy         = zero
    lei0 (LevEl k)    (LevEl m)     = eqL k m
    lei0 (LevEl k)    (FunEl _)     = zero
    lei0 (LevEl k)    (PiCode _ _)  = zero
    lei0 (FunEl _)    _             = zero
    lei0 (PiCode _ _) _             = zero
    lei0 (UCode k) (LPiCode _)   = zero
    lei0 LevTy (LPiCode _)   = zero
    lei0 (LevEl k) (LPiCode _)   = zero
    lei0 (LPiCode _)  _             = zero

    lef0 : FinFun -> FinFun -> Nat
    lef0 nil         _ = suc zero
    lef0 (cons _ _)  _ = zero

    ev0 : FinFun -> FinEl -> FinEl
    ev0 nil         _ = Bot
    ev0 (cons _ _)  _ = Bot

------------------------------------------------------------------------
-- buildOrderStage : level-(suc n) operations from the level-n bundle B.
------------------------------------------------------------------------

buildOrderStage : OrderBundle -> OrderBundle
buildOrderStage B =
  record { leq = leq' ; leqf = leqf' ; lei = lei' ; lef = lef' ; ev = ev' }
  where
    open OrderBundle B renaming (leq to leqP ; lei to leiP)

    -- internal evaluation: structural on the list, decision via leiP
    ev' : FinFun -> FinEl -> FinEl
    ev' nil         u = Bot
    ev' (cons p ps) u = evCombine (leiP (fst p) u) (snd p) (ev' ps u)

    -- NO-LAG: leqf'/lef' evaluate the codomain via the SAME-stage ev'
    -- (not the predecessor), so a stage-(suc m) comparison resolves
    -- rank-m arguments correctly and stability has no off-by-one.

    -- Set-valued order
    leqf' : FinFun -> FinFun -> Set
    leqf' nil         _ = Top
    leqf' (cons p ps) h = Pair (leqP (snd p) (ev' h (fst p))) (leqf' ps h)

    leq' : FinEl -> FinEl -> Set
    leq' Bot          _             = Top
    leq' (UCode k)    Bot           = Empty
    leq' (UCode k)    (UCode m)     = EqL k m
    leq' (UCode k)    (FunEl _)     = Empty
    leq' (UCode k)    (PiCode _ _)  = Empty
    leq' (UCode k)    LevTy         = Empty
    leq' (UCode k)    (LevEl _)     = Empty
    leq' LevTy        Bot           = Empty
    leq' LevTy        (UCode _)     = Empty
    leq' LevTy        LevTy         = Top
    leq' LevTy        (LevEl _)     = Empty
    leq' LevTy        (FunEl _)     = Empty
    leq' LevTy        (PiCode _ _)  = Empty
    leq' (LevEl k)    Bot           = Empty
    leq' (LevEl k)    (UCode _)     = Empty
    leq' (LevEl k)    LevTy         = Empty
    leq' (LevEl k)    (LevEl m)     = EqL k m
    leq' (LevEl k)    (FunEl _)     = Empty
    leq' (LevEl k)    (PiCode _ _)  = Empty
    leq' (UCode _)      (LPiCode g)    = Empty
    leq' LevTy          (LPiCode g)    = Empty
    leq' (LevEl _)      (LPiCode g)    = Empty
    leq' (FunEl _)      (LPiCode g)    = Empty
    leq' (PiCode _ _)   (LPiCode g)    = Empty
    leq' (LPiCode f)    Bot            = Empty
    leq' (LPiCode f)    (UCode _)      = Empty
    leq' (LPiCode f)    LevTy          = Empty
    leq' (LPiCode f)    (LevEl _)      = Empty
    leq' (LPiCode f)    (FunEl _)      = Empty
    leq' (LPiCode f)    (PiCode _ _)   = Empty
    leq' (LPiCode f)    (LPiCode g)    = leqf' f g
    leq' (FunEl _)    Bot           = Empty
    leq' (FunEl _)    (UCode _)     = Empty
    leq' (FunEl g)    (FunEl h)     = leqf' g h
    leq' (FunEl _)    (PiCode _ _)  = Empty
    leq' (FunEl _)    LevTy         = Empty
    leq' (FunEl _)    (LevEl _)     = Empty
    leq' (PiCode _ _) Bot           = Empty
    leq' (PiCode _ _) (UCode _)     = Empty
    leq' (PiCode _ _) (FunEl _)     = Empty
    leq' (PiCode _ _) LevTy         = Empty
    leq' (PiCode _ _) (LevEl _)     = Empty
    leq' (PiCode a f) (PiCode b g)  = Pair (leqP a b) (leqf' f g)

    -- numeric decision (mirrors the Set-valued order)
    lef' : FinFun -> FinFun -> Nat
    lef' nil         _ = suc zero
    lef' (cons p ps) h = min (leiP (snd p) (ev' h (fst p))) (lef' ps h)

    lei' : FinEl -> FinEl -> Nat
    lei' Bot          _             = suc zero
    lei' (UCode k)    Bot           = zero
    lei' (UCode k)    (UCode m)     = eqL k m
    lei' (UCode k)    (FunEl _)     = zero
    lei' (UCode k)    (PiCode _ _)  = zero
    lei' (UCode k)    LevTy         = zero
    lei' (UCode k)    (LevEl _)     = zero
    lei' LevTy        Bot           = zero
    lei' LevTy        (UCode _)     = zero
    lei' LevTy        LevTy         = suc zero
    lei' LevTy        (LevEl _)     = zero
    lei' LevTy        (FunEl _)     = zero
    lei' LevTy        (PiCode _ _)  = zero
    lei' (LevEl k)    Bot           = zero
    lei' (LevEl k)    (UCode _)     = zero
    lei' (LevEl k)    LevTy         = zero
    lei' (LevEl k)    (LevEl m)     = eqL k m
    lei' (LevEl k)    (FunEl _)     = zero
    lei' (LevEl k)    (PiCode _ _)  = zero
    lei' (UCode _)      (LPiCode g)    = zero
    lei' LevTy          (LPiCode g)    = zero
    lei' (LevEl _)      (LPiCode g)    = zero
    lei' (FunEl _)      (LPiCode g)    = zero
    lei' (PiCode _ _)   (LPiCode g)    = zero
    lei' (LPiCode f)    Bot            = zero
    lei' (LPiCode f)    (UCode _)      = zero
    lei' (LPiCode f)    LevTy          = zero
    lei' (LPiCode f)    (LevEl _)      = zero
    lei' (LPiCode f)    (FunEl _)      = zero
    lei' (LPiCode f)    (PiCode _ _)   = zero
    lei' (LPiCode f)    (LPiCode g)    = lef' f g
    lei' (FunEl _)    Bot           = zero
    lei' (FunEl _)    (UCode _)     = zero
    lei' (FunEl g)    (FunEl h)     = lef' g h
    lei' (FunEl _)    (PiCode _ _)  = zero
    lei' (FunEl _)    LevTy         = zero
    lei' (FunEl _)    (LevEl _)     = zero
    lei' (PiCode _ _) Bot           = zero
    lei' (PiCode _ _) (UCode _)     = zero
    lei' (PiCode _ _) (FunEl _)     = zero
    lei' (PiCode _ _) LevTy         = zero
    lei' (PiCode _ _) (LevEl _)     = zero
    lei' (PiCode a f) (PiCode b g)  = min (leiP a b) (lef' f g)

------------------------------------------------------------------------
-- The stratified family, by structural recursion on the stage index.
------------------------------------------------------------------------

Stage : Nat -> OrderBundle
Stage zero    = trivBundle
Stage (suc n) = buildOrderStage (Stage n)

------------------------------------------------------------------------
-- Public order at the canonical level  suc (max (RANK u) (RANK v)).
------------------------------------------------------------------------

LeqC : FinEl -> FinEl -> Set
LeqC u v = OrderBundle.leq (Stage (suc (max (RANK u) (RANK v)))) u v

leiC : FinEl -> FinEl -> Nat
leiC u v = OrderBundle.lei (Stage (suc (max (RANK u) (RANK v)))) u v

------------------------------------------------------------------------
-- OB n : the bundle operations at stage n (used by the Props / Stable files).
------------------------------------------------------------------------

module OB (n : Nat) = OrderBundle (Stage n)

------------------------------------------------------------------------
-- Le / RANK toolkit (inlined; cannot import Rank.agda -- it imports
-- PaperSemantics, which will import this file).
------------------------------------------------------------------------

Le-max-lub : (a b c : Nat) -> Le a c -> Le b c -> Le (max a b) c
Le-max-lub zero    b       c       h1 h2 = h2
Le-max-lub (suc a) zero    c       h1 h2 = h1
Le-max-lub (suc a) (suc b) zero    () h2
Le-max-lub (suc a) (suc b) (suc c) h1 h2 = Le-max-lub a b c h1 h2

max-mono : (a b c d : Nat) -> Le a c -> Le b d -> Le (max a b) (max c d)
max-mono a b c d hac hbd =
  Le-max-lub a b (max c d)
    (Le-trans a c (max c d) hac (Le-max-l c d))
    (Le-trans b d (max c d) hbd (Le-max-r c d))

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

RANK-Sup : (x y : FinEl) -> Le (RANK (Sup x y)) (max (RANK x) (RANK y))
RANK-Sup Bot          y             = Le-refl (RANK y)
RANK-Sup (UCode k)    Bot           = tt
RANK-Sup (UCode k)    (UCode m)     = tt
RANK-Sup (UCode k)    (FunEl g)     = tt
RANK-Sup (UCode k)    (PiCode b g)  = tt
RANK-Sup (UCode k)    LevTy         = tt
RANK-Sup (UCode k)    (LevEl m)     = tt
RANK-Sup LevTy        Bot           = tt
RANK-Sup LevTy        (UCode m)     = tt
RANK-Sup LevTy        LevTy         = tt
RANK-Sup LevTy        (LevEl m)     = tt
RANK-Sup LevTy        (FunEl g)     = tt
RANK-Sup LevTy        (PiCode b g)  = tt
RANK-Sup (LevEl k)    Bot           = tt
RANK-Sup (LevEl k)    (UCode m)     = tt
RANK-Sup (LevEl k)    LevTy         = tt
RANK-Sup (LevEl k)    (LevEl m)     = tt
RANK-Sup (LevEl k)    (FunEl g)     = tt
RANK-Sup (LevEl k)    (PiCode b g)  = tt
RANK-Sup (FunEl g)    Bot           = Le-refl (RANK (FunEl g))
RANK-Sup (FunEl g)    (UCode m)     = tt
RANK-Sup (FunEl g)    (FunEl h)     = RANK-append g h
RANK-Sup (FunEl g)    (PiCode b h)  = tt
RANK-Sup (FunEl g)    LevTy         = tt
RANK-Sup (FunEl g)    (LevEl m)     = tt
RANK-Sup (PiCode a f) Bot           = Le-refl (RANK (PiCode a f))
RANK-Sup (PiCode a f) (UCode m)     = tt
RANK-Sup (PiCode a f) (FunEl h)     = tt
RANK-Sup (PiCode a f) LevTy         = tt
RANK-Sup (PiCode a f) (LevEl m)     = tt
RANK-Sup (UCode _)      (LPiCode g)    = tt
RANK-Sup LevTy          (LPiCode g)    = tt
RANK-Sup (LevEl _)      (LPiCode g)    = tt
RANK-Sup (FunEl _)      (LPiCode g)    = tt
RANK-Sup (PiCode _ _)   (LPiCode g)    = tt
RANK-Sup (LPiCode f)    Bot            = Le-refl (RANK (LPiCode f))
RANK-Sup (LPiCode f)    (UCode _)      = tt
RANK-Sup (LPiCode f)    LevTy          = tt
RANK-Sup (LPiCode f)    (LevEl _)      = tt
RANK-Sup (LPiCode f)    (FunEl _)      = tt
RANK-Sup (LPiCode f)    (PiCode _ _)   = tt
RANK-Sup (LPiCode f)    (LPiCode g)    = RANK-append f g
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
-- RANK-ev : RANK (ev n h u) <= RANKFun h  (ev only produces values
-- bounded by h's codomain ranks; at low stages it is Bot).
------------------------------------------------------------------------

RANK-evCombine : (w : Nat) (x r : FinEl) ->
  Le (RANK (evCombine w x r)) (max (RANK x) (RANK r))
RANK-evCombine zero    x r = Le-max-r (RANK x) (RANK r)
RANK-evCombine (suc _) x r = RANK-Sup x r

RANK-ev : (n : Nat) (h : FinFun) (u : FinEl) ->
  Le (RANK (OB.ev n h u)) (RANKFun h)
RANK-ev zero    nil         u = tt
RANK-ev zero    (cons _ _)  u = tt
RANK-ev (suc n) nil         u = tt
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

------------------------------------------------------------------------
-- Universes: transporting along a level equality.
------------------------------------------------------------------------

comp-U-transport : (k m : Nat) (v : FinEl) -> EqL k m -> Comp (UCode m) v -> Comp (UCode k) v
comp-U-transport k m Bot          e c = tt
comp-U-transport k m (UCode w)    e c = EqL-trans k m w e c
comp-U-transport k m (FunEl g)    e ()
comp-U-transport k m (PiCode b g) e ()
comp-U-transport k m LevTy        e ()
comp-U-transport k m (LevEl w)    e ()
comp-U-transport k m (LPiCode g)  e ()

leq-U-EqL : (n k m : Nat) -> OB.leq n (UCode k) (UCode m) -> EqL k m
leq-U-EqL zero    k m e = e
leq-U-EqL (suc n) k m e = e

leq-U-transport : (n k m : Nat) (z : FinEl) -> OB.leq n (UCode k) (UCode m)
  -> OB.leq n (UCode m) z -> OB.leq n (UCode k) z
leq-U-transport zero    k m Bot          e ()
leq-U-transport zero    k m (UCode w)    e c = EqL-trans k m w e c
leq-U-transport zero    k m (FunEl g)    e ()
leq-U-transport zero    k m (PiCode b g) e ()
leq-U-transport zero    k m LevTy        e ()
leq-U-transport zero    k m (LevEl w)    e ()
leq-U-transport zero    k m (LPiCode g)  e ()
leq-U-transport (suc n) k m Bot          e ()
leq-U-transport (suc n) k m (UCode w)    e c = EqL-trans k m w e c
leq-U-transport (suc n) k m (FunEl g)    e ()
leq-U-transport (suc n) k m (PiCode b g) e ()
leq-U-transport (suc n) k m LevTy        e ()
leq-U-transport (suc n) k m (LevEl w)    e ()
leq-U-transport (suc n) k m (LPiCode g)  e ()

------------------------------------------------------------------------
-- Level tokens: transporting along a level equality (mirrors UCode).
------------------------------------------------------------------------

comp-L-transport : (k m : Nat) (v : FinEl) -> EqL k m -> Comp (LevEl m) v -> Comp (LevEl k) v
comp-L-transport k m Bot          e c = tt
comp-L-transport k m (UCode w)    e ()
comp-L-transport k m LevTy        e ()
comp-L-transport k m (LevEl w)    e c = EqL-trans k m w e c
comp-L-transport k m (FunEl g)    e ()
comp-L-transport k m (PiCode b g) e ()
comp-L-transport k m (LPiCode g)  e ()

leq-L-EqL : (n k m : Nat) -> OB.leq n (LevEl k) (LevEl m) -> EqL k m
leq-L-EqL zero    k m e = e
leq-L-EqL (suc n) k m e = e

leq-L-transport : (n k m : Nat) (z : FinEl) -> OB.leq n (LevEl k) (LevEl m)
  -> OB.leq n (LevEl m) z -> OB.leq n (LevEl k) z
leq-L-transport zero    k m Bot          e ()
leq-L-transport zero    k m (UCode w)    e ()
leq-L-transport zero    k m LevTy        e ()
leq-L-transport zero    k m (LevEl w)    e c = EqL-trans k m w e c
leq-L-transport zero    k m (FunEl g)    e ()
leq-L-transport zero    k m (PiCode b g) e ()
leq-L-transport zero    k m (LPiCode g)  e ()
leq-L-transport (suc n) k m Bot          e ()
leq-L-transport (suc n) k m (UCode w)    e ()
leq-L-transport (suc n) k m LevTy        e ()
leq-L-transport (suc n) k m (LevEl w)    e c = EqL-trans k m w e c
leq-L-transport (suc n) k m (FunEl g)    e ()
leq-L-transport (suc n) k m (PiCode b g) e ()
leq-L-transport (suc n) k m (LPiCode g)  e ()
