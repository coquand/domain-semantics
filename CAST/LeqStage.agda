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

module CAST.LeqStage where

open import CAST.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; min ; isPos ; min-isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun ; List ; nil ; cons )

------------------------------------------------------------------------
-- Structural, EvalFun-free primitives (inlined here to avoid an import
-- cycle with PaperOrder, which will later be re-founded on this file).
------------------------------------------------------------------------

append : FinFun -> FinFun -> FinFun
append nil         g = g
append (cons p ps) g = cons p (append ps g)

Sup : FinEl -> FinEl -> FinEl
Sup Bot             x             = x
Sup UCode           Bot           = UCode
Sup UCode           UCode         = UCode
Sup UCode           (FunEl g)     = Bot
Sup UCode           (PiCode b g)  = Bot
Sup UCode           (IdCode b d)  = Bot
Sup (FunEl g)       Bot           = FunEl g
Sup (FunEl g)       UCode         = Bot
Sup (FunEl g)       (FunEl h)     = FunEl (append g h)
Sup (FunEl g)       (PiCode b h)  = Bot
Sup (FunEl g)       (IdCode b d)  = Bot
Sup (PiCode a f)    Bot           = PiCode a f
Sup (PiCode a f)    UCode         = Bot
Sup (PiCode a f)    (FunEl h)     = Bot
Sup (PiCode a f)    (PiCode b g)  = PiCode (Sup a b) (append f g)
Sup (PiCode a f)    (IdCode b d)  = Bot
Sup (IdCode a b)    Bot           = IdCode a b
Sup (IdCode a b)    UCode         = Bot
Sup (IdCode a b)    (FunEl h)     = Bot
Sup (IdCode a b)    (PiCode c g)  = Bot
Sup (IdCode a b)    (IdCode c d)  = IdCode (Sup a c) (Sup b d)

mutual
  RANK : FinEl -> Nat
  RANK Bot          = zero
  RANK UCode        = zero
  RANK (FunEl g)    = suc (RANKFun g)
  RANK (PiCode a f) = suc (max (RANK a) (RANKFun f))
  RANK (IdCode a b) = suc (max (RANK a) (RANK b))

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
  Comp UCode           Bot           = Top
  Comp UCode           UCode         = Top
  Comp UCode           (FunEl g)     = Empty
  Comp UCode           (PiCode b g)  = Empty
  Comp UCode           (IdCode b d)  = Empty
  Comp (FunEl g)       Bot           = Top
  Comp (FunEl g)       UCode         = Empty
  Comp (FunEl g)       (FunEl h)     = CompFun g h
  Comp (FunEl g)       (PiCode b h)  = Empty
  Comp (FunEl g)       (IdCode b d)  = Empty
  Comp (PiCode a f)    Bot           = Top
  Comp (PiCode a f)    UCode         = Empty
  Comp (PiCode a f)    (FunEl h)     = Empty
  Comp (PiCode a f)    (PiCode b g)  = Pair (Comp a b) (CompFun f g)
  Comp (PiCode a f)    (IdCode b d)  = Empty
  Comp (IdCode a b)    Bot           = Top
  Comp (IdCode a b)    UCode         = Empty
  Comp (IdCode a b)    (FunEl h)     = Empty
  Comp (IdCode a b)    (PiCode c g)  = Empty
  Comp (IdCode a b)    (IdCode c d)  = Pair (Comp a c) (Comp b d)

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
NotBot UCode           = Top
NotBot (FunEl g)       = Top
NotBot (PiCode a f)    = Top
NotBot (IdCode a b)    = Top

mutual
  Coherent : FinEl -> Set
  Coherent Bot             = Top
  Coherent UCode           = Top
  Coherent (FunEl g)       = CoherentFun g
  Coherent (PiCode a f)    = Pair (Coherent a) (CoherentFunTail f)
  Coherent (IdCode a b)    = Pair (Coherent a) (Coherent b)

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
    leq0 UCode        Bot           = Empty
    leq0 UCode        UCode         = Top
    leq0 UCode        (FunEl _)     = Empty
    leq0 UCode        (PiCode _ _)  = Empty
    leq0 UCode        (IdCode _ _)  = Empty
    leq0 (FunEl _)    _             = Empty
    leq0 (PiCode _ _) _             = Empty
    leq0 (IdCode _ _) _             = Empty

    leqf0 : FinFun -> FinFun -> Set
    leqf0 nil         _ = Top
    leqf0 (cons _ _)  _ = Empty

    lei0 : FinEl -> FinEl -> Nat
    lei0 Bot          _             = suc zero
    lei0 UCode        Bot           = zero
    lei0 UCode        UCode         = suc zero
    lei0 UCode        (FunEl _)     = zero
    lei0 UCode        (PiCode _ _)  = zero
    lei0 UCode        (IdCode _ _)  = zero
    lei0 (FunEl _)    _             = zero
    lei0 (PiCode _ _) _             = zero
    lei0 (IdCode _ _) _             = zero

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
    leq' UCode        Bot           = Empty
    leq' UCode        UCode         = Top
    leq' UCode        (FunEl _)     = Empty
    leq' UCode        (PiCode _ _)  = Empty
    leq' UCode        (IdCode _ _)  = Empty
    leq' (FunEl _)    Bot           = Empty
    leq' (FunEl _)    UCode         = Empty
    leq' (FunEl g)    (FunEl h)     = leqf' g h
    leq' (FunEl _)    (PiCode _ _)  = Empty
    leq' (FunEl _)    (IdCode _ _)  = Empty
    leq' (PiCode _ _) Bot           = Empty
    leq' (PiCode _ _) UCode         = Empty
    leq' (PiCode _ _) (FunEl _)     = Empty
    leq' (PiCode a f) (PiCode b g)  = Pair (leqP a b) (leqf' f g)
    leq' (PiCode _ _) (IdCode _ _)  = Empty
    leq' (IdCode _ _) Bot           = Empty
    leq' (IdCode _ _) UCode         = Empty
    leq' (IdCode _ _) (FunEl _)     = Empty
    leq' (IdCode _ _) (PiCode _ _)  = Empty
    leq' (IdCode a b) (IdCode c d)  = Pair (leqP a c) (leqP b d)

    -- numeric decision (mirrors the Set-valued order)
    lef' : FinFun -> FinFun -> Nat
    lef' nil         _ = suc zero
    lef' (cons p ps) h = min (leiP (snd p) (ev' h (fst p))) (lef' ps h)

    lei' : FinEl -> FinEl -> Nat
    lei' Bot          _             = suc zero
    lei' UCode        Bot           = zero
    lei' UCode        UCode         = suc zero
    lei' UCode        (FunEl _)     = zero
    lei' UCode        (PiCode _ _)  = zero
    lei' UCode        (IdCode _ _)  = zero
    lei' (FunEl _)    Bot           = zero
    lei' (FunEl _)    UCode         = zero
    lei' (FunEl g)    (FunEl h)     = lef' g h
    lei' (FunEl _)    (PiCode _ _)  = zero
    lei' (FunEl _)    (IdCode _ _)  = zero
    lei' (PiCode _ _) Bot           = zero
    lei' (PiCode _ _) UCode         = zero
    lei' (PiCode _ _) (FunEl _)     = zero
    lei' (PiCode a f) (PiCode b g)  = min (leiP a b) (lef' f g)
    lei' (PiCode _ _) (IdCode _ _)  = zero
    lei' (IdCode _ _) Bot           = zero
    lei' (IdCode _ _) UCode         = zero
    lei' (IdCode _ _) (FunEl _)     = zero
    lei' (IdCode _ _) (PiCode _ _)  = zero
    lei' (IdCode a b) (IdCode c d)  = min (leiP a c) (leiP b d)

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
RANK-Sup UCode        Bot           = tt
RANK-Sup UCode        UCode         = tt
RANK-Sup UCode        (FunEl g)     = tt
RANK-Sup UCode        (PiCode b g)  = tt
RANK-Sup UCode        (IdCode b d)  = tt
RANK-Sup (FunEl g)    Bot           = Le-refl (RANK (FunEl g))
RANK-Sup (FunEl g)    UCode         = tt
RANK-Sup (FunEl g)    (FunEl h)     = RANK-append g h
RANK-Sup (FunEl g)    (PiCode b h)  = tt
RANK-Sup (FunEl g)    (IdCode b d)  = tt
RANK-Sup (PiCode a f) Bot           = Le-refl (RANK (PiCode a f))
RANK-Sup (PiCode a f) UCode         = tt
RANK-Sup (PiCode a f) (FunEl h)     = tt
RANK-Sup (PiCode a f) (IdCode b d)  = tt
RANK-Sup (IdCode a b) Bot           = Le-refl (RANK (IdCode a b))
RANK-Sup (IdCode a b) UCode         = tt
RANK-Sup (IdCode a b) (FunEl h)     = tt
RANK-Sup (IdCode a b) (PiCode c g)  = tt
RANK-Sup (IdCode a b) (IdCode c d)  =
  let ra = RANK a ; rc = RANK c ; rb = RANK b ; rd = RANK d
      p = RANK (Sup a c) ; q = RANK (Sup b d)
      rhs = max (max ra rb) (max rc rd)
      hP : Le p (max ra rc)
      hP = RANK-Sup a c
      hQ : Le q (max rb rd)
      hQ = RANK-Sup b d
      le-ac : Le (max ra rc) rhs
      le-ac = Le-max-lub ra rc rhs
        (Le-trans ra (max ra rb) rhs (Le-max-l ra rb) (Le-max-l (max ra rb) (max rc rd)))
        (Le-trans rc (max rc rd) rhs (Le-max-l rc rd) (Le-max-r (max ra rb) (max rc rd)))
      le-bd : Le (max rb rd) rhs
      le-bd = Le-max-lub rb rd rhs
        (Le-trans rb (max ra rb) rhs (Le-max-r ra rb) (Le-max-l (max ra rb) (max rc rd)))
        (Le-trans rd (max rc rd) rhs (Le-max-r rc rd) (Le-max-r (max ra rb) (max rc rd)))
      leP : Le p rhs
      leP = Le-trans p (max ra rc) rhs hP le-ac
      leQ : Le q rhs
      leQ = Le-trans q (max rb rd) rhs hQ le-bd
  in Le-max-lub p q rhs leP leQ
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
