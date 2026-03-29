{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperSemanticsSigma.agda
--
-- Extension of PaperSemantics with SigmaCode and PairCode.
-- Parallel version — does not modify the original files.
--
-- SigmaCode a f : type code for Σ(x:a).f(x)  (like PiCode)
-- PairCode u v  : pair value (u, v)
--
-- Design: Coherent (PairCode u v) = (Coherent u × Coherent v) × NotBot (Sup u v)
-- so PairCode Bot Bot is incoherent (morally = Bot).
--
-- 0 postulates.
------------------------------------------------------------------------

module PaperSemanticsSigma where

open import BasicSigma
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; Sigma ; mkSigma ; fst ; snd ; Pair
        ; List ; nil ; cons ; All
        ; FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun
        ; rk ; rkFun
        ; min ; isPos ; min-isPos
        ; pair-eq ; cons-eq
        )

------------------------------------------------------------------------
-- Or (disjoint union)
------------------------------------------------------------------------

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

------------------------------------------------------------------------
-- Part 1: append and Sup
------------------------------------------------------------------------

append : FinFun -> FinFun -> FinFun
append nil         g = g
append (cons p ps) g = cons p (append ps g)

Sup : FinEl -> FinEl -> FinEl
Sup Bot             x             = x
Sup UCode           Bot           = UCode
Sup UCode           UCode         = UCode
Sup UCode           PropCode      = Bot
Sup UCode           (FunEl g)     = Bot
Sup UCode           (PiCode b g)  = Bot
Sup UCode           (SigmaCode b g) = Bot
Sup UCode           (PairCode u v)  = Bot
Sup PropCode        Bot           = PropCode
Sup PropCode        UCode         = Bot
Sup PropCode        PropCode      = PropCode
Sup PropCode        (FunEl g)     = Bot
Sup PropCode        (PiCode b g)  = Bot
Sup PropCode        (SigmaCode b g) = Bot
Sup PropCode        (PairCode u v)  = Bot
Sup (FunEl g)       Bot           = FunEl g
Sup (FunEl g)       UCode         = Bot
Sup (FunEl g)       PropCode      = Bot
Sup (FunEl g)       (FunEl h)     = FunEl (append g h)
Sup (FunEl g)       (PiCode b h)  = Bot
Sup (FunEl g)       (SigmaCode b h) = Bot
Sup (FunEl g)       (PairCode u v)  = Bot
Sup (PiCode a f)    Bot           = PiCode a f
Sup (PiCode a f)    UCode         = Bot
Sup (PiCode a f)    PropCode      = Bot
Sup (PiCode a f)    (FunEl h)     = Bot
Sup (PiCode a f)    (PiCode b g)  = PiCode (Sup a b) (append f g)
Sup (PiCode a f)    (SigmaCode b g) = Bot
Sup (PiCode a f)    (PairCode u v)  = Bot
Sup (SigmaCode a f) Bot           = SigmaCode a f
Sup (SigmaCode a f) UCode         = Bot
Sup (SigmaCode a f) PropCode      = Bot
Sup (SigmaCode a f) (FunEl h)     = Bot
Sup (SigmaCode a f) (PiCode b g)  = Bot
Sup (SigmaCode a f) (SigmaCode b g) = SigmaCode (Sup a b) (append f g)
Sup (SigmaCode a f) (PairCode u v)  = Bot
Sup (PairCode u v)  Bot           = PairCode u v
Sup (PairCode u v)  UCode         = Bot
Sup (PairCode u v)  PropCode      = Bot
Sup (PairCode u v)  (FunEl h)     = Bot
Sup (PairCode u v)  (PiCode b g)  = Bot
Sup (PairCode u v)  (SigmaCode b g) = Bot
Sup (PairCode u1 v1) (PairCode u2 v2) = PairCode (Sup u1 u2) (Sup v1 v2)

------------------------------------------------------------------------
-- Part 2: Main mutual block
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  leFinEl : FinEl -> FinEl -> Nat
  leFinEl Bot             x             = 1
  leFinEl UCode           Bot           = 0
  leFinEl UCode           UCode         = 1
  leFinEl UCode           PropCode      = 0
  leFinEl UCode           (FunEl h)     = 0
  leFinEl UCode           (PiCode b g)  = 0
  leFinEl UCode           (SigmaCode b g) = 0
  leFinEl UCode           (PairCode u v)  = 0
  leFinEl PropCode        Bot           = 0
  leFinEl PropCode        UCode         = 0
  leFinEl PropCode        PropCode      = 1
  leFinEl PropCode        (FunEl h)     = 0
  leFinEl PropCode        (PiCode b g)  = 0
  leFinEl PropCode        (SigmaCode b g) = 0
  leFinEl PropCode        (PairCode u v)  = 0
  leFinEl (FunEl g)       Bot           = 0
  leFinEl (FunEl g)       UCode         = 0
  leFinEl (FunEl g)       PropCode      = 0
  leFinEl (FunEl g)       (FunEl h)     = leFun g h
  leFinEl (FunEl g)       (PiCode b h)  = 0
  leFinEl (FunEl g)       (SigmaCode b h) = 0
  leFinEl (FunEl g)       (PairCode u v)  = 0
  leFinEl (PiCode a f)    Bot           = 0
  leFinEl (PiCode a f)    UCode         = 0
  leFinEl (PiCode a f)    PropCode      = 0
  leFinEl (PiCode a f)    (FunEl h)     = 0
  leFinEl (PiCode a f)    (PiCode b g)  = min (leFinEl a b) (leFun f g)
  leFinEl (PiCode a f)    (SigmaCode b g) = 0
  leFinEl (PiCode a f)    (PairCode u v)  = 0
  leFinEl (SigmaCode a f) Bot           = 0
  leFinEl (SigmaCode a f) UCode         = 0
  leFinEl (SigmaCode a f) PropCode      = 0
  leFinEl (SigmaCode a f) (FunEl h)     = 0
  leFinEl (SigmaCode a f) (PiCode b g)  = 0
  leFinEl (SigmaCode a f) (SigmaCode b g) = min (leFinEl a b) (leFun f g)
  leFinEl (SigmaCode a f) (PairCode u v)  = 0
  leFinEl (PairCode u v)  Bot           = 0
  leFinEl (PairCode u v)  UCode         = 0
  leFinEl (PairCode u v)  PropCode      = 0
  leFinEl (PairCode u v)  (FunEl h)     = 0
  leFinEl (PairCode u v)  (PiCode b g)  = 0
  leFinEl (PairCode u v)  (SigmaCode b g) = 0
  leFinEl (PairCode u1 v1) (PairCode u2 v2) = min (leFinEl u1 u2) (leFinEl v1 v2)

  leFun : FinFun -> FinFun -> Nat
  leFun nil         h = 1
  leFun (cons p ps) h = min (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h)

  EvalFun : FinFun -> FinEl -> FinEl
  EvalFun nil         u = Bot
  EvalFun (cons p ps) u = EvalFun-step (leFinEl (fst p) u) (snd p) ps u

  EvalFun-step : Nat -> FinEl -> FinFun -> FinEl -> FinEl
  EvalFun-step zero    bi rest u = EvalFun rest u
  EvalFun-step (suc n) bi rest u = Sup bi (EvalFun rest u)

  LeCode : FinEl -> FinEl -> Set
  LeCode Bot             v             = Top
  LeCode UCode           Bot           = Empty
  LeCode UCode           UCode         = Top
  LeCode UCode           PropCode      = Empty
  LeCode UCode           (FunEl h)     = Empty
  LeCode UCode           (PiCode b g)  = Empty
  LeCode UCode           (SigmaCode b g) = Empty
  LeCode UCode           (PairCode u v)  = Empty
  LeCode PropCode        Bot           = Empty
  LeCode PropCode        UCode         = Empty
  LeCode PropCode        PropCode      = Top
  LeCode PropCode        (FunEl h)     = Empty
  LeCode PropCode        (PiCode b g)  = Empty
  LeCode PropCode        (SigmaCode b g) = Empty
  LeCode PropCode        (PairCode u v)  = Empty
  LeCode (FunEl g)       Bot           = Empty
  LeCode (FunEl g)       UCode         = Empty
  LeCode (FunEl g)       PropCode      = Empty
  LeCode (FunEl g)       (FunEl h)     = LeFunCode g h
  LeCode (FunEl g)       (PiCode b h)  = Empty
  LeCode (FunEl g)       (SigmaCode b h) = Empty
  LeCode (FunEl g)       (PairCode u v)  = Empty
  LeCode (PiCode a f)    Bot           = Empty
  LeCode (PiCode a f)    UCode         = Empty
  LeCode (PiCode a f)    PropCode      = Empty
  LeCode (PiCode a f)    (FunEl h)     = Empty
  LeCode (PiCode a f)    (PiCode b g)  = Pair (LeCode a b) (LeFunCode f g)
  LeCode (PiCode a f)    (SigmaCode b g) = Empty
  LeCode (PiCode a f)    (PairCode u v)  = Empty
  LeCode (SigmaCode a f) Bot           = Empty
  LeCode (SigmaCode a f) UCode         = Empty
  LeCode (SigmaCode a f) PropCode      = Empty
  LeCode (SigmaCode a f) (FunEl h)     = Empty
  LeCode (SigmaCode a f) (PiCode b g)  = Empty
  LeCode (SigmaCode a f) (SigmaCode b g) = Pair (LeCode a b) (LeFunCode f g)
  LeCode (SigmaCode a f) (PairCode u v)  = Empty
  LeCode (PairCode u v)  Bot           = Empty
  LeCode (PairCode u v)  UCode         = Empty
  LeCode (PairCode u v)  PropCode      = Empty
  LeCode (PairCode u v)  (FunEl h)     = Empty
  LeCode (PairCode u v)  (PiCode b g)  = Empty
  LeCode (PairCode u v)  (SigmaCode b g) = Empty
  LeCode (PairCode u1 v1) (PairCode u2 v2) = Pair (LeCode u1 u2) (LeCode v1 v2)

  LeFunCode : FinFun -> FinFun -> Set
  LeFunCode nil         h = Top
  LeFunCode (cons p ps) h =
    Pair (LeCode (snd p) (EvalFun h (fst p))) (LeFunCode ps h)

------------------------------------------------------------------------
-- Part 2.5: Application and projections on finite elements
------------------------------------------------------------------------

applyEl : FinEl -> FinEl -> FinEl
applyEl Bot             v = Bot
applyEl UCode           v = Bot
applyEl PropCode        v = Bot
applyEl (FunEl g)       v = EvalFun g v
applyEl (PiCode a f)    v = Bot
applyEl (SigmaCode a f) v = Bot
applyEl (PairCode u v)  w = Bot

fstEl : FinEl -> FinEl
fstEl Bot             = Bot
fstEl UCode           = Bot
fstEl PropCode        = Bot
fstEl (FunEl g)       = Bot
fstEl (PiCode a f)    = Bot
fstEl (SigmaCode a f) = Bot
fstEl (PairCode u v)  = u

sndEl : FinEl -> FinEl
sndEl Bot             = Bot
sndEl UCode           = Bot
sndEl PropCode        = Bot
sndEl (FunEl g)       = Bot
sndEl (PiCode a f)    = Bot
sndEl (SigmaCode a f) = Bot
sndEl (PairCode u v)  = v

------------------------------------------------------------------------
-- Part 3a: Compatibility
------------------------------------------------------------------------

mutual
  Comp : FinEl -> FinEl -> Set
  Comp Bot             x             = Top
  Comp UCode           Bot           = Top
  Comp UCode           UCode         = Top
  Comp UCode           PropCode      = Empty
  Comp UCode           (FunEl g)     = Empty
  Comp UCode           (PiCode b g)  = Empty
  Comp UCode           (SigmaCode b g) = Empty
  Comp UCode           (PairCode u v)  = Empty
  Comp PropCode        Bot           = Top
  Comp PropCode        UCode         = Empty
  Comp PropCode        PropCode      = Top
  Comp PropCode        (FunEl g)     = Empty
  Comp PropCode        (PiCode b g)  = Empty
  Comp PropCode        (SigmaCode b g) = Empty
  Comp PropCode        (PairCode u v)  = Empty
  Comp (FunEl g)       Bot           = Top
  Comp (FunEl g)       UCode         = Empty
  Comp (FunEl g)       PropCode      = Empty
  Comp (FunEl g)       (FunEl h)     = CompFun g h
  Comp (FunEl g)       (PiCode b h)  = Empty
  Comp (FunEl g)       (SigmaCode b h) = Empty
  Comp (FunEl g)       (PairCode u v)  = Empty
  Comp (PiCode a f)    Bot           = Top
  Comp (PiCode a f)    UCode         = Empty
  Comp (PiCode a f)    PropCode      = Empty
  Comp (PiCode a f)    (FunEl h)     = Empty
  Comp (PiCode a f)    (PiCode b g)  = Pair (Comp a b) (CompFun f g)
  Comp (PiCode a f)    (SigmaCode b g) = Empty
  Comp (PiCode a f)    (PairCode u v)  = Empty
  Comp (SigmaCode a f) Bot           = Top
  Comp (SigmaCode a f) UCode         = Empty
  Comp (SigmaCode a f) PropCode      = Empty
  Comp (SigmaCode a f) (FunEl h)     = Empty
  Comp (SigmaCode a f) (PiCode b g)  = Empty
  Comp (SigmaCode a f) (SigmaCode b g) = Pair (Comp a b) (CompFun f g)
  Comp (SigmaCode a f) (PairCode u v)  = Empty
  Comp (PairCode u v)  Bot           = Top
  Comp (PairCode u v)  UCode         = Empty
  Comp (PairCode u v)  PropCode      = Empty
  Comp (PairCode u v)  (FunEl h)     = Empty
  Comp (PairCode u v)  (PiCode b g)  = Empty
  Comp (PairCode u v)  (SigmaCode b g) = Empty
  Comp (PairCode u1 v1) (PairCode u2 v2) = Pair (Comp u1 u2) (Comp v1 v2)

  CompFun : FinFun -> FinFun -> Set
  CompFun nil         g = Top
  CompFun (cons s f)  g = Pair (CompStepFun s g) (CompFun f g)

  CompStepFun : Pair FinEl FinEl -> FinFun -> Set
  CompStepFun s nil         = Top
  CompStepFun s (cons t g)  = Pair (CompStepStep s t) (CompStepFun s g)

  CompStepStep : Pair FinEl FinEl -> Pair FinEl FinEl -> Set
  CompStepStep s t = Comp (fst s) (fst t) -> Comp (snd s) (snd t)

------------------------------------------------------------------------
-- Part 3: FinMem + Coherence
------------------------------------------------------------------------

NotBot : FinEl -> Set
NotBot Bot             = Empty
NotBot UCode           = Top
NotBot PropCode        = Top
NotBot (FunEl g)       = Top
NotBot (PiCode a f)    = Top
NotBot (SigmaCode a f) = Top
NotBot (PairCode u v)  = Top

{-# TERMINATING #-}
mutual
  FinMem : FinEl -> FinEl -> Set
  FinMem Bot             a               = FinMem a UCode
  -- UCode
  FinMem UCode           UCode           = Top
  FinMem UCode           PropCode        = Empty
  FinMem UCode           Bot             = Empty
  FinMem UCode           (FunEl g)       = Empty
  FinMem UCode           (PiCode a f)    = Empty
  FinMem UCode           (SigmaCode a f) = Empty
  FinMem UCode           (PairCode u v)  = Empty
  -- PropCode
  FinMem PropCode        UCode           = Top
  FinMem PropCode        PropCode        = Empty
  FinMem PropCode        Bot             = Empty
  FinMem PropCode        (FunEl g)       = Empty
  FinMem PropCode        (PiCode a f)    = Empty
  FinMem PropCode        (SigmaCode a f) = Empty
  FinMem PropCode        (PairCode u v)  = Empty
  -- FunEl
  FinMem (FunEl g)       (PiCode a f)    = Pair (FinMemFun g a f)
                                                (Pair (CoherentFun g)
                                                      (FinMem (PiCode a f) UCode))
  FinMem (FunEl g)       Bot             = Empty
  FinMem (FunEl g)       UCode           = Empty
  FinMem (FunEl g)       PropCode        = Empty
  FinMem (FunEl g)       (FunEl h)       = Empty
  FinMem (FunEl g)       (SigmaCode a f) = Empty
  FinMem (FunEl g)       (PairCode u v)  = Empty
  -- PiCode
  FinMem (PiCode a f)    UCode           = Pair (FinMem a UCode)
                                                (Pair (FinMemAllU f a)
                                                      (CoherentFunTail f))
  FinMem (PiCode a f)    PropCode        = Pair (FinMem a UCode)
                                                (Pair (FinMemAllProp f a)
                                                      (CoherentFunTail f))
  FinMem (PiCode a f)    Bot             = Empty
  FinMem (PiCode a f)    (FunEl g)       = Empty
  FinMem (PiCode a f)    (PiCode b g)    = Empty
  FinMem (PiCode a f)    (SigmaCode b g) = Empty
  FinMem (PiCode a f)    (PairCode u v)  = Empty
  -- SigmaCode
  FinMem (SigmaCode a f) UCode           = Pair (FinMem a UCode)
                                                (Pair (FinMemAllU f a)
                                                      (CoherentFunTail f))
  FinMem (SigmaCode a f) Bot             = Empty
  FinMem (SigmaCode a f) PropCode        = Empty
  FinMem (SigmaCode a f) (FunEl g)       = Empty
  FinMem (SigmaCode a f) (PiCode b g)    = Empty
  FinMem (SigmaCode a f) (SigmaCode b g) = Empty
  FinMem (SigmaCode a f) (PairCode u v)  = Empty
  -- PairCode
  FinMem (PairCode u v)  (SigmaCode a f) = Pair (Pair (FinMem u a)
                                                       (FinMem v (EvalFun f u)))
                                                (Pair (Coherent (PairCode u v))
                                                      (FinMem (SigmaCode a f) UCode))
  FinMem (PairCode u v)  Bot             = Empty
  FinMem (PairCode u v)  UCode           = Empty
  FinMem (PairCode u v)  PropCode        = Empty
  FinMem (PairCode u v)  (FunEl g)       = Empty
  FinMem (PairCode u v)  (PiCode b g)    = Empty
  FinMem (PairCode u v)  (PairCode u2 v2) = Empty

  FinMemFun : FinFun -> FinEl -> FinFun -> Set
  FinMemFun nil         a f = Top
  FinMemFun (cons p ps) a f =
    Pair (Pair (FinMem (fst p) a) (FinMem (snd p) (EvalFun f (fst p))))
         (FinMemFun ps a f)

  FinMemAllU : FinFun -> FinEl -> Set
  FinMemAllU nil         a = Top
  FinMemAllU (cons p ps) a =
    Pair (Pair (FinMem (fst p) a) (FinMem (snd p) UCode))
         (FinMemAllU ps a)

  FinMemAllProp : FinFun -> FinEl -> Set
  FinMemAllProp nil         a = Top
  FinMemAllProp (cons p ps) a =
    Pair (Pair (FinMem (fst p) a) (FinMem (snd p) PropCode))
         (FinMemAllProp ps a)

  Coherent : FinEl -> Set
  Coherent Bot             = Top
  Coherent UCode           = Top
  Coherent PropCode        = Top
  Coherent (FunEl g)       = CoherentFun g
  Coherent (PiCode a f)    = Pair (Coherent a) (CoherentFunTail f)
  Coherent (SigmaCode a f) = Pair (Coherent a) (CoherentFunTail f)
  Coherent (PairCode u v)  = Pair (Pair (Coherent u) (Coherent v))
                                  (Or (NotBot u) (NotBot v))

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

Coherent-singleton-key : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent u
Coherent-singleton-key u v coh = CFTcons.key-coh coh

Coherent-singleton-val : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent v
Coherent-singleton-val u v coh = CFTcons.val-coh coh

------------------------------------------------------------------------
-- Part 5b: Structural projections from FinMem
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  FinMem-coh-u : (u a : FinEl) -> FinMem u a -> Coherent u
  FinMem-coh-u Bot             a               mem = tt
  -- UCode
  FinMem-coh-u UCode           UCode           mem = tt
  FinMem-coh-u UCode           PropCode        ()
  FinMem-coh-u UCode           Bot             ()
  FinMem-coh-u UCode           (FunEl g)       ()
  FinMem-coh-u UCode           (PiCode a f)    ()
  FinMem-coh-u UCode           (SigmaCode a f) ()
  FinMem-coh-u UCode           (PairCode u v)  ()
  -- PropCode
  FinMem-coh-u PropCode        UCode           mem = tt
  FinMem-coh-u PropCode        PropCode        ()
  FinMem-coh-u PropCode        Bot             ()
  FinMem-coh-u PropCode        (FunEl g)       ()
  FinMem-coh-u PropCode        (PiCode a f)    ()
  FinMem-coh-u PropCode        (SigmaCode a f) ()
  FinMem-coh-u PropCode        (PairCode u v)  ()
  -- FunEl
  FinMem-coh-u (FunEl g)       (PiCode a f)    mem = fst (snd mem)
  FinMem-coh-u (FunEl g)       Bot             ()
  FinMem-coh-u (FunEl g)       UCode           ()
  FinMem-coh-u (FunEl g)       PropCode        ()
  FinMem-coh-u (FunEl g)       (FunEl h)       ()
  FinMem-coh-u (FunEl g)       (SigmaCode a f) ()
  FinMem-coh-u (FunEl g)       (PairCode u v)  ()
  -- PiCode
  FinMem-coh-u (PiCode a f)    UCode           mem =
    mkSigma (FinMem-coh-u a UCode (fst mem)) (snd (snd mem))
  FinMem-coh-u (PiCode a f)    PropCode        mem =
    mkSigma (FinMem-coh-u a UCode (fst mem)) (snd (snd mem))
  FinMem-coh-u (PiCode a f)    Bot             ()
  FinMem-coh-u (PiCode a f)    (FunEl g)       ()
  FinMem-coh-u (PiCode a f)    (PiCode b g)    ()
  FinMem-coh-u (PiCode a f)    (SigmaCode b g) ()
  FinMem-coh-u (PiCode a f)    (PairCode u v)  ()
  -- SigmaCode
  FinMem-coh-u (SigmaCode a f) UCode           mem =
    mkSigma (FinMem-coh-u a UCode (fst mem)) (snd (snd mem))
  FinMem-coh-u (SigmaCode a f) Bot             ()
  FinMem-coh-u (SigmaCode a f) PropCode        ()
  FinMem-coh-u (SigmaCode a f) (FunEl g)       ()
  FinMem-coh-u (SigmaCode a f) (PiCode b g)    ()
  FinMem-coh-u (SigmaCode a f) (SigmaCode b g) ()
  FinMem-coh-u (SigmaCode a f) (PairCode u v)  ()
  -- PairCode
  FinMem-coh-u (PairCode u v)  (SigmaCode a f) mem = fst (snd mem)
  FinMem-coh-u (PairCode u v)  Bot             ()
  FinMem-coh-u (PairCode u v)  UCode           ()
  FinMem-coh-u (PairCode u v)  PropCode        ()
  FinMem-coh-u (PairCode u v)  (FunEl g)       ()
  FinMem-coh-u (PairCode u v)  (PiCode b g)    ()
  FinMem-coh-u (PairCode u v)  (PairCode u2 v2) ()

  FinMem-a-in-U : (u a : FinEl) -> FinMem u a -> FinMem a UCode
  FinMem-a-in-U Bot             a               mem = mem
  -- UCode
  FinMem-a-in-U UCode           UCode           mem = tt
  FinMem-a-in-U UCode           PropCode        ()
  FinMem-a-in-U UCode           Bot             ()
  FinMem-a-in-U UCode           (FunEl g)       ()
  FinMem-a-in-U UCode           (PiCode a f)    ()
  FinMem-a-in-U UCode           (SigmaCode a f) ()
  FinMem-a-in-U UCode           (PairCode u v)  ()
  -- PropCode
  FinMem-a-in-U PropCode        UCode           mem = tt
  FinMem-a-in-U PropCode        PropCode        ()
  FinMem-a-in-U PropCode        Bot             ()
  FinMem-a-in-U PropCode        (FunEl g)       ()
  FinMem-a-in-U PropCode        (PiCode a f)    ()
  FinMem-a-in-U PropCode        (SigmaCode a f) ()
  FinMem-a-in-U PropCode        (PairCode u v)  ()
  -- FunEl
  FinMem-a-in-U (FunEl g)       (PiCode a f)    mem = snd (snd mem)
  FinMem-a-in-U (FunEl g)       Bot             ()
  FinMem-a-in-U (FunEl g)       UCode           ()
  FinMem-a-in-U (FunEl g)       PropCode        ()
  FinMem-a-in-U (FunEl g)       (FunEl h)       ()
  FinMem-a-in-U (FunEl g)       (SigmaCode a f) ()
  FinMem-a-in-U (FunEl g)       (PairCode u v)  ()
  -- PiCode
  FinMem-a-in-U (PiCode a f)    UCode           mem = tt
  FinMem-a-in-U (PiCode a f)    PropCode        mem = tt
  FinMem-a-in-U (PiCode a f)    Bot             ()
  FinMem-a-in-U (PiCode a f)    (FunEl g)       ()
  FinMem-a-in-U (PiCode a f)    (PiCode b g)    ()
  FinMem-a-in-U (PiCode a f)    (SigmaCode b g) ()
  FinMem-a-in-U (PiCode a f)    (PairCode u v)  ()
  -- SigmaCode
  FinMem-a-in-U (SigmaCode a f) UCode           mem = tt
  FinMem-a-in-U (SigmaCode a f) Bot             ()
  FinMem-a-in-U (SigmaCode a f) PropCode        ()
  FinMem-a-in-U (SigmaCode a f) (FunEl g)       ()
  FinMem-a-in-U (SigmaCode a f) (PiCode b g)    ()
  FinMem-a-in-U (SigmaCode a f) (SigmaCode b g) ()
  FinMem-a-in-U (SigmaCode a f) (PairCode u v)  ()
  -- PairCode
  FinMem-a-in-U (PairCode u v)  (SigmaCode a f) mem = snd (snd mem)
  FinMem-a-in-U (PairCode u v)  Bot             ()
  FinMem-a-in-U (PairCode u v)  UCode           ()
  FinMem-a-in-U (PairCode u v)  PropCode        ()
  FinMem-a-in-U (PairCode u v)  (FunEl g)       ()
  FinMem-a-in-U (PairCode u v)  (PiCode b g)    ()
  FinMem-a-in-U (PairCode u v)  (PairCode u2 v2) ()

  FinMem-coh-a : (u a : FinEl) -> FinMem u a -> Coherent a
  FinMem-coh-a Bot             a               mem = FinMem-coh-u a UCode mem
  -- UCode
  FinMem-coh-a UCode           UCode           mem = tt
  FinMem-coh-a UCode           PropCode        ()
  FinMem-coh-a UCode           Bot             ()
  FinMem-coh-a UCode           (FunEl g)       ()
  FinMem-coh-a UCode           (PiCode a f)    ()
  FinMem-coh-a UCode           (SigmaCode a f) ()
  FinMem-coh-a UCode           (PairCode u v)  ()
  -- PropCode
  FinMem-coh-a PropCode        UCode           mem = tt
  FinMem-coh-a PropCode        PropCode        ()
  FinMem-coh-a PropCode        Bot             ()
  FinMem-coh-a PropCode        (FunEl g)       ()
  FinMem-coh-a PropCode        (PiCode a f)    ()
  FinMem-coh-a PropCode        (SigmaCode a f) ()
  FinMem-coh-a PropCode        (PairCode u v)  ()
  -- FunEl
  FinMem-coh-a (FunEl g)       (PiCode a f)    mem =
    FinMem-coh-u (PiCode a f) UCode (snd (snd mem))
  FinMem-coh-a (FunEl g)       Bot             ()
  FinMem-coh-a (FunEl g)       UCode           ()
  FinMem-coh-a (FunEl g)       PropCode        ()
  FinMem-coh-a (FunEl g)       (FunEl h)       ()
  FinMem-coh-a (FunEl g)       (SigmaCode a f) ()
  FinMem-coh-a (FunEl g)       (PairCode u v)  ()
  -- PiCode
  FinMem-coh-a (PiCode a f)    UCode           mem = tt
  FinMem-coh-a (PiCode a f)    PropCode        mem = tt
  FinMem-coh-a (PiCode a f)    Bot             ()
  FinMem-coh-a (PiCode a f)    (FunEl g)       ()
  FinMem-coh-a (PiCode a f)    (PiCode b g)    ()
  FinMem-coh-a (PiCode a f)    (SigmaCode b g) ()
  FinMem-coh-a (PiCode a f)    (PairCode u v)  ()
  -- SigmaCode
  FinMem-coh-a (SigmaCode a f) UCode           mem = tt
  FinMem-coh-a (SigmaCode a f) Bot             ()
  FinMem-coh-a (SigmaCode a f) PropCode        ()
  FinMem-coh-a (SigmaCode a f) (FunEl g)       ()
  FinMem-coh-a (SigmaCode a f) (PiCode b g)    ()
  FinMem-coh-a (SigmaCode a f) (SigmaCode b g) ()
  FinMem-coh-a (SigmaCode a f) (PairCode u v)  ()
  -- PairCode
  FinMem-coh-a (PairCode u v)  (SigmaCode a f) mem =
    FinMem-coh-u (SigmaCode a f) UCode (snd (snd mem))
  FinMem-coh-a (PairCode u v)  Bot             ()
  FinMem-coh-a (PairCode u v)  UCode           ()
  FinMem-coh-a (PairCode u v)  PropCode        ()
  FinMem-coh-a (PairCode u v)  (FunEl g)       ()
  FinMem-coh-a (PairCode u v)  (PiCode b g)    ()
  FinMem-coh-a (PairCode u v)  (PairCode u2 v2) ()

coh-from-aU : (a : FinEl) -> FinMem a UCode -> Coherent a
coh-from-aU a mem = FinMem-coh-u a UCode mem

------------------------------------------------------------------------
-- Part 6: Soundness of leFinEl
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  leFinEl-sound : (u v : FinEl) -> isPos (leFinEl u v) -> LeCode u v
  leFinEl-sound Bot             v               h = tt
  -- UCode
  leFinEl-sound UCode           Bot             ()
  leFinEl-sound UCode           UCode           h = tt
  leFinEl-sound UCode           PropCode        ()
  leFinEl-sound UCode           (FunEl g)       ()
  leFinEl-sound UCode           (PiCode b g)    ()
  leFinEl-sound UCode           (SigmaCode b g) ()
  leFinEl-sound UCode           (PairCode u v)  ()
  -- PropCode
  leFinEl-sound PropCode        Bot             ()
  leFinEl-sound PropCode        UCode           ()
  leFinEl-sound PropCode        PropCode        h = tt
  leFinEl-sound PropCode        (FunEl g)       ()
  leFinEl-sound PropCode        (PiCode b g)    ()
  leFinEl-sound PropCode        (SigmaCode b g) ()
  leFinEl-sound PropCode        (PairCode u v)  ()
  -- FunEl
  leFinEl-sound (FunEl g)       Bot             ()
  leFinEl-sound (FunEl g)       UCode           ()
  leFinEl-sound (FunEl g)       PropCode        ()
  leFinEl-sound (FunEl g)       (FunEl h)       p = leFun-sound g h p
  leFinEl-sound (FunEl g)       (PiCode b h)    ()
  leFinEl-sound (FunEl g)       (SigmaCode b h) ()
  leFinEl-sound (FunEl g)       (PairCode u v)  ()
  -- PiCode
  leFinEl-sound (PiCode a f)    Bot             ()
  leFinEl-sound (PiCode a f)    UCode           ()
  leFinEl-sound (PiCode a f)    PropCode        ()
  leFinEl-sound (PiCode a f)    (FunEl h)       ()
  leFinEl-sound (PiCode a f)    (PiCode b g)    p =
    let pp = min-isPos (leFinEl a b) (leFun f g) p
    in mkSigma (leFinEl-sound a b (fst pp)) (leFun-sound f g (snd pp))
  leFinEl-sound (PiCode a f)    (SigmaCode b g) ()
  leFinEl-sound (PiCode a f)    (PairCode u v)  ()
  -- SigmaCode
  leFinEl-sound (SigmaCode a f) Bot             ()
  leFinEl-sound (SigmaCode a f) UCode           ()
  leFinEl-sound (SigmaCode a f) PropCode        ()
  leFinEl-sound (SigmaCode a f) (FunEl h)       ()
  leFinEl-sound (SigmaCode a f) (PiCode b g)    ()
  leFinEl-sound (SigmaCode a f) (SigmaCode b g) p =
    let pp = min-isPos (leFinEl a b) (leFun f g) p
    in mkSigma (leFinEl-sound a b (fst pp)) (leFun-sound f g (snd pp))
  leFinEl-sound (SigmaCode a f) (PairCode u v)  ()
  -- PairCode
  leFinEl-sound (PairCode u v)  Bot             ()
  leFinEl-sound (PairCode u v)  UCode           ()
  leFinEl-sound (PairCode u v)  PropCode        ()
  leFinEl-sound (PairCode u v)  (FunEl h)       ()
  leFinEl-sound (PairCode u v)  (PiCode b g)    ()
  leFinEl-sound (PairCode u v)  (SigmaCode b g) ()
  leFinEl-sound (PairCode u1 v1) (PairCode u2 v2) p =
    let pp = min-isPos (leFinEl u1 u2) (leFinEl v1 v2) p
    in mkSigma (leFinEl-sound u1 u2 (fst pp)) (leFinEl-sound v1 v2 (snd pp))

  leFun-sound : (g h : FinFun) -> isPos (leFun g h) -> LeFunCode g h
  leFun-sound nil         h p = tt
  leFun-sound (cons p ps) h q =
    let pp = min-isPos (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h) q
    in mkSigma (leFinEl-sound (snd p) (EvalFun h (fst p)) (fst pp))
               (leFun-sound ps h (snd pp))

------------------------------------------------------------------------
-- Part 6b: Completeness of leFinEl
------------------------------------------------------------------------

isPos-min : (m n : Nat) -> isPos m -> isPos n -> isPos (min m n)
isPos-min zero    n       () _
isPos-min (suc m) zero    _  ()
isPos-min (suc m) (suc n) _  _ = tt

{-# TERMINATING #-}
mutual
  leFinEl-complete : (u v : FinEl) -> LeCode u v -> isPos (leFinEl u v)
  leFinEl-complete Bot             Bot             _ = tt
  leFinEl-complete Bot             UCode           _ = tt
  leFinEl-complete Bot             PropCode        _ = tt
  leFinEl-complete Bot             (FunEl h)       _ = tt
  leFinEl-complete Bot             (PiCode b g)    _ = tt
  leFinEl-complete Bot             (SigmaCode b g) _ = tt
  leFinEl-complete Bot             (PairCode u v)  _ = tt
  -- UCode
  leFinEl-complete UCode           Bot             ()
  leFinEl-complete UCode           UCode           _ = tt
  leFinEl-complete UCode           PropCode        ()
  leFinEl-complete UCode           (FunEl g)       ()
  leFinEl-complete UCode           (PiCode b g)    ()
  leFinEl-complete UCode           (SigmaCode b g) ()
  leFinEl-complete UCode           (PairCode u v)  ()
  -- PropCode
  leFinEl-complete PropCode        Bot             ()
  leFinEl-complete PropCode        UCode           ()
  leFinEl-complete PropCode        PropCode        _ = tt
  leFinEl-complete PropCode        (FunEl g)       ()
  leFinEl-complete PropCode        (PiCode b g)    ()
  leFinEl-complete PropCode        (SigmaCode b g) ()
  leFinEl-complete PropCode        (PairCode u v)  ()
  -- FunEl
  leFinEl-complete (FunEl g)       Bot             ()
  leFinEl-complete (FunEl g)       UCode           ()
  leFinEl-complete (FunEl g)       PropCode        ()
  leFinEl-complete (FunEl g)       (FunEl h)       p = leFun-complete g h p
  leFinEl-complete (FunEl g)       (PiCode b h)    ()
  leFinEl-complete (FunEl g)       (SigmaCode b h) ()
  leFinEl-complete (FunEl g)       (PairCode u v)  ()
  -- PiCode
  leFinEl-complete (PiCode a f)    Bot             ()
  leFinEl-complete (PiCode a f)    UCode           ()
  leFinEl-complete (PiCode a f)    PropCode        ()
  leFinEl-complete (PiCode a f)    (FunEl h)       ()
  leFinEl-complete (PiCode a f)    (PiCode b g)    p =
    isPos-min (leFinEl a b) (leFun f g)
              (leFinEl-complete a b (fst p))
              (leFun-complete f g (snd p))
  leFinEl-complete (PiCode a f)    (SigmaCode b g) ()
  leFinEl-complete (PiCode a f)    (PairCode u v)  ()
  -- SigmaCode
  leFinEl-complete (SigmaCode a f) Bot             ()
  leFinEl-complete (SigmaCode a f) UCode           ()
  leFinEl-complete (SigmaCode a f) PropCode        ()
  leFinEl-complete (SigmaCode a f) (FunEl h)       ()
  leFinEl-complete (SigmaCode a f) (PiCode b g)    ()
  leFinEl-complete (SigmaCode a f) (SigmaCode b g) p =
    isPos-min (leFinEl a b) (leFun f g)
              (leFinEl-complete a b (fst p))
              (leFun-complete f g (snd p))
  leFinEl-complete (SigmaCode a f) (PairCode u v)  ()
  -- PairCode
  leFinEl-complete (PairCode u v)  Bot             ()
  leFinEl-complete (PairCode u v)  UCode           ()
  leFinEl-complete (PairCode u v)  PropCode        ()
  leFinEl-complete (PairCode u v)  (FunEl h)       ()
  leFinEl-complete (PairCode u v)  (PiCode b g)    ()
  leFinEl-complete (PairCode u v)  (SigmaCode b g) ()
  leFinEl-complete (PairCode u1 v1) (PairCode u2 v2) p =
    isPos-min (leFinEl u1 u2) (leFinEl v1 v2)
              (leFinEl-complete u1 u2 (fst p))
              (leFinEl-complete v1 v2 (snd p))

  leFun-complete : (g h : FinFun) -> LeFunCode g h -> isPos (leFun g h)
  leFun-complete nil         h _ = tt
  leFun-complete (cons p ps) h q =
    isPos-min (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h)
              (leFinEl-complete (snd p) (EvalFun h (fst p)) (fst q))
              (leFun-complete ps h (snd q))

------------------------------------------------------------------------
-- Part 7: Sup lemmas
------------------------------------------------------------------------

Sup-Bot-l : (v : FinEl) -> Eq (Sup Bot v) v
Sup-Bot-l Bot             = refl
Sup-Bot-l UCode           = refl
Sup-Bot-l PropCode        = refl
Sup-Bot-l (FunEl g)       = refl
Sup-Bot-l (PiCode b g)    = refl
Sup-Bot-l (SigmaCode b g) = refl
Sup-Bot-l (PairCode u v)  = refl

Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot             = refl
Sup-Bot-r UCode           = refl
Sup-Bot-r PropCode        = refl
Sup-Bot-r (FunEl g)       = refl
Sup-Bot-r (PiCode a f)    = refl
Sup-Bot-r (SigmaCode a f) = refl
Sup-Bot-r (PairCode u v)  = refl

LeCode-Bot : (v : FinEl) -> LeCode Bot v
LeCode-Bot v = tt

------------------------------------------------------------------------
-- Part 7b: Basic compatibility lemmas
------------------------------------------------------------------------

comp-Bot-r : (u : FinEl) -> Comp u Bot
comp-Bot-r Bot             = tt
comp-Bot-r UCode           = tt
comp-Bot-r PropCode        = tt
comp-Bot-r (FunEl g)       = tt
comp-Bot-r (PiCode a f)    = tt
comp-Bot-r (SigmaCode a f) = tt
comp-Bot-r (PairCode u v)  = tt

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot             = tt
comp-Bot-l UCode           = tt
comp-Bot-l PropCode        = tt
comp-Bot-l (FunEl g)       = tt
comp-Bot-l (PiCode a f)    = tt
comp-Bot-l (SigmaCode a f) = tt
comp-Bot-l (PairCode u v)  = tt

Sup-Bot-right : (x : FinEl) -> Eq (Sup x Bot) x
Sup-Bot-right Bot             = refl
Sup-Bot-right UCode           = refl
Sup-Bot-right PropCode        = refl
Sup-Bot-right (FunEl g)       = refl
Sup-Bot-right (PiCode a f)    = refl
Sup-Bot-right (SigmaCode a f) = refl
Sup-Bot-right (PairCode u v)  = refl

compStepFun-append : (s : Pair FinEl FinEl) (g h : FinFun) ->
  CompStepFun s g -> CompStepFun s h -> CompStepFun s (append g h)
compStepFun-append s nil         h cg ch = ch
compStepFun-append s (cons t ts) h cg ch =
  mkSigma (fst cg) (compStepFun-append s ts h (snd cg) ch)

compFun-append : (g h j : FinFun) ->
  CompFun g h -> CompFun g j -> CompFun g (append h j)
compFun-append nil         h j ch cj = tt
compFun-append (cons s ss) h j ch cj =
  mkSigma (compStepFun-append s h j (fst ch) (fst cj))
          (compFun-append ss h j (snd ch) (snd cj))

LeFunCode-append-nil : (g h : FinFun) ->
  LeFunCode g nil -> LeFunCode h nil -> LeFunCode (append g h) nil
LeFunCode-append-nil nil         h lg lh = lh
LeFunCode-append-nil (cons p ps) h lg lh =
  mkSigma (fst lg) (LeFunCode-append-nil ps h (snd lg) lh)

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

SigmaCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (SigmaCode a f) (SigmaCode b g)
SigmaCode-cong refl refl = refl

PairCode-cong : {u1 u2 v1 v2 : FinEl} ->
  Eq u1 u2 -> Eq v1 v2 -> Eq (PairCode u1 v1) (PairCode u2 v2)
PairCode-cong refl refl = refl

append-assoc : (f g h : FinFun) -> Eq (append f (append g h)) (append (append f g) h)
append-assoc nil         g h = refl
append-assoc (cons p ps) g h = cons-eq refl (append-assoc ps g h)

------------------------------------------------------------------------
-- isPos-to-LeCode
------------------------------------------------------------------------

isPos-to-LeCode : (x xi : FinEl) -> isPos (leFinEl x xi) -> LeCode x xi
isPos-to-LeCode = leFinEl-sound

------------------------------------------------------------------------
-- Part 7c: comp-Sup
------------------------------------------------------------------------

{-# TERMINATING #-}
comp-Sup : (a b c : FinEl) -> Comp a b -> Comp a c -> Comp a (Sup b c)
-- a = Bot
comp-Sup Bot b c ab ac = comp-Bot-l (Sup b c)
-- a = UCode
comp-Sup UCode Bot c ab ac = ac
comp-Sup UCode UCode Bot             ab ac = tt
comp-Sup UCode UCode UCode           ab ac = tt
comp-Sup UCode UCode PropCode        ab ac = tt
comp-Sup UCode UCode (FunEl j)       ab ac = tt
comp-Sup UCode UCode (PiCode e j)    ab ac = tt
comp-Sup UCode UCode (SigmaCode e j) ab ac = tt
comp-Sup UCode UCode (PairCode u2 v2) ab ac = tt
comp-Sup UCode PropCode c () ac
comp-Sup UCode (FunEl h) c () ac
comp-Sup UCode (PiCode d k) c () ac
comp-Sup UCode (SigmaCode d k) c () ac
comp-Sup UCode (PairCode u v) c () ac
-- a = PropCode
comp-Sup PropCode Bot c ab ac = ac
comp-Sup PropCode UCode c () ac
comp-Sup PropCode PropCode Bot             ab ac = tt
comp-Sup PropCode PropCode UCode           ab ac = tt
comp-Sup PropCode PropCode PropCode        ab ac = tt
comp-Sup PropCode PropCode (FunEl j)       ab ac = tt
comp-Sup PropCode PropCode (PiCode e j)    ab ac = tt
comp-Sup PropCode PropCode (SigmaCode e j) ab ac = tt
comp-Sup PropCode PropCode (PairCode u2 v2) ab ac = tt
comp-Sup PropCode (FunEl h) c () ac
comp-Sup PropCode (PiCode d k) c () ac
comp-Sup PropCode (SigmaCode d k) c () ac
comp-Sup PropCode (PairCode u v) c () ac
-- a = FunEl g
comp-Sup (FunEl g) Bot c ab ac = ac
comp-Sup (FunEl g) UCode c () ac
comp-Sup (FunEl g) PropCode c () ac
comp-Sup (FunEl g) (FunEl h) Bot ab ac = ab
comp-Sup (FunEl g) (FunEl h) UCode ab ()
comp-Sup (FunEl g) (FunEl h) PropCode ab ()
comp-Sup (FunEl g) (FunEl h) (FunEl j) ab ac = compFun-append g h j ab ac
comp-Sup (FunEl g) (FunEl h) (PiCode d k) ab ()
comp-Sup (FunEl g) (FunEl h) (SigmaCode d k) ab ()
comp-Sup (FunEl g) (FunEl h) (PairCode u v) ab ()
comp-Sup (FunEl g) (PiCode d k) c () ac
comp-Sup (FunEl g) (SigmaCode d k) c () ac
comp-Sup (FunEl g) (PairCode u v) c () ac
-- a = PiCode a f
comp-Sup (PiCode a f) Bot c ab ac = ac
comp-Sup (PiCode a f) UCode c () ac
comp-Sup (PiCode a f) PropCode c () ac
comp-Sup (PiCode a f) (FunEl h) c () ac
comp-Sup (PiCode a f) (PiCode d k) Bot ab ac = ab
comp-Sup (PiCode a f) (PiCode d k) UCode ab ()
comp-Sup (PiCode a f) (PiCode d k) PropCode ab ()
comp-Sup (PiCode a f) (PiCode d k) (FunEl h) ab ()
comp-Sup (PiCode a f) (PiCode d k) (PiCode e j) ab ac =
  mkSigma (comp-Sup a d e (fst ab) (fst ac))
          (compFun-append f k j (snd ab) (snd ac))
comp-Sup (PiCode a f) (PiCode d k) (SigmaCode e j) ab ()
comp-Sup (PiCode a f) (PiCode d k) (PairCode u v) ab ()
comp-Sup (PiCode a f) (SigmaCode d k) c () ac
comp-Sup (PiCode a f) (PairCode u v) c () ac
-- a = SigmaCode a f (mirrors PiCode)
comp-Sup (SigmaCode a f) Bot c ab ac = ac
comp-Sup (SigmaCode a f) UCode c () ac
comp-Sup (SigmaCode a f) PropCode c () ac
comp-Sup (SigmaCode a f) (FunEl h) c () ac
comp-Sup (SigmaCode a f) (PiCode d k) c () ac
comp-Sup (SigmaCode a f) (SigmaCode d k) Bot ab ac = ab
comp-Sup (SigmaCode a f) (SigmaCode d k) UCode ab ()
comp-Sup (SigmaCode a f) (SigmaCode d k) PropCode ab ()
comp-Sup (SigmaCode a f) (SigmaCode d k) (FunEl h) ab ()
comp-Sup (SigmaCode a f) (SigmaCode d k) (PiCode e j) ab ()
comp-Sup (SigmaCode a f) (SigmaCode d k) (SigmaCode e j) ab ac =
  mkSigma (comp-Sup a d e (fst ab) (fst ac))
          (compFun-append f k j (snd ab) (snd ac))
comp-Sup (SigmaCode a f) (SigmaCode d k) (PairCode u v) ab ()
comp-Sup (SigmaCode a f) (PairCode u v) c () ac
-- a = PairCode u1 v1
comp-Sup (PairCode u1 v1) Bot c ab ac = ac
comp-Sup (PairCode u1 v1) UCode c () ac
comp-Sup (PairCode u1 v1) PropCode c () ac
comp-Sup (PairCode u1 v1) (FunEl h) c () ac
comp-Sup (PairCode u1 v1) (PiCode d k) c () ac
comp-Sup (PairCode u1 v1) (SigmaCode d k) c () ac
comp-Sup (PairCode u1 v1) (PairCode u2 v2) Bot ab ac = ab
comp-Sup (PairCode u1 v1) (PairCode u2 v2) UCode ab ()
comp-Sup (PairCode u1 v1) (PairCode u2 v2) PropCode ab ()
comp-Sup (PairCode u1 v1) (PairCode u2 v2) (FunEl h) ab ()
comp-Sup (PairCode u1 v1) (PairCode u2 v2) (PiCode d k) ab ()
comp-Sup (PairCode u1 v1) (PairCode u2 v2) (SigmaCode d k) ab ()
comp-Sup (PairCode u1 v1) (PairCode u2 v2) (PairCode u3 v3) ab ac =
  mkSigma (comp-Sup u1 u2 u3 (fst ab) (fst ac))
          (comp-Sup v1 v2 v3 (snd ab) (snd ac))

------------------------------------------------------------------------
-- Part 7d: Comp-sym
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  Comp-sym : (u v : FinEl) -> Comp u v -> Comp v u
  Comp-sym Bot Bot c = tt
  Comp-sym Bot UCode c = tt
  Comp-sym Bot PropCode c = tt
  Comp-sym Bot (FunEl h) c = tt
  Comp-sym Bot (PiCode b g) c = tt
  Comp-sym Bot (SigmaCode b g) c = tt
  Comp-sym Bot (PairCode u v) c = tt
  Comp-sym UCode Bot c = tt
  Comp-sym UCode UCode c = tt
  Comp-sym UCode PropCode ()
  Comp-sym UCode (FunEl h) c = c
  Comp-sym UCode (PiCode b g) ()
  Comp-sym UCode (SigmaCode b g) ()
  Comp-sym UCode (PairCode u v) ()
  Comp-sym PropCode Bot c = tt
  Comp-sym PropCode UCode ()
  Comp-sym PropCode PropCode c = tt
  Comp-sym PropCode (FunEl h) c = c
  Comp-sym PropCode (PiCode b g) ()
  Comp-sym PropCode (SigmaCode b g) ()
  Comp-sym PropCode (PairCode u v) ()
  Comp-sym (FunEl g) Bot c = tt
  Comp-sym (FunEl g) UCode c = c
  Comp-sym (FunEl g) PropCode c = c
  Comp-sym (FunEl g) (FunEl h) c = CompFun-sym g h c
  Comp-sym (FunEl g) (PiCode b h) c = c
  Comp-sym (FunEl g) (SigmaCode b h) c = c
  Comp-sym (FunEl g) (PairCode u v) c = c
  Comp-sym (PiCode a f) Bot c = tt
  Comp-sym (PiCode a f) UCode ()
  Comp-sym (PiCode a f) PropCode ()
  Comp-sym (PiCode a f) (FunEl h) c = c
  Comp-sym (PiCode a f) (PiCode b g) c =
    mkSigma (Comp-sym a b (fst c)) (CompFun-sym f g (snd c))
  Comp-sym (PiCode a f) (SigmaCode b g) c = c
  Comp-sym (PiCode a f) (PairCode u v) c = c
  Comp-sym (SigmaCode a f) Bot c = tt
  Comp-sym (SigmaCode a f) UCode ()
  Comp-sym (SigmaCode a f) PropCode ()
  Comp-sym (SigmaCode a f) (FunEl h) c = c
  Comp-sym (SigmaCode a f) (PiCode b g) c = c
  Comp-sym (SigmaCode a f) (SigmaCode b g) c =
    mkSigma (Comp-sym a b (fst c)) (CompFun-sym f g (snd c))
  Comp-sym (SigmaCode a f) (PairCode u v) c = c
  Comp-sym (PairCode u1 v1) Bot c = tt
  Comp-sym (PairCode u1 v1) UCode ()
  Comp-sym (PairCode u1 v1) PropCode ()
  Comp-sym (PairCode u1 v1) (FunEl h) c = c
  Comp-sym (PairCode u1 v1) (PiCode b g) c = c
  Comp-sym (PairCode u1 v1) (SigmaCode b g) c = c
  Comp-sym (PairCode u1 v1) (PairCode u2 v2) c =
    mkSigma (Comp-sym u1 u2 (fst c)) (Comp-sym v1 v2 (snd c))

  CompFun-sym : (g h : FinFun) -> CompFun g h -> CompFun h g
  CompFun-sym g nil cf = tt
  CompFun-sym g (cons t ts) cf =
    mkSigma (CompFun-sym-col g t ts cf)
            (CompFun-sym g ts (CompFun-drop-col g t ts cf))

  CompFun-sym-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompStepFun t g
  CompFun-sym-col nil t ts cf = tt
  CompFun-sym-col (cons s ss) t ts cf =
    mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst (fst cf) (Comp-sym (fst t) (fst s) c)))
            (CompFun-sym-col ss t ts (snd cf))

  CompFun-drop-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompFun g ts
  CompFun-drop-col nil t ts cf = tt
  CompFun-drop-col (cons s ss) t ts cf =
    mkSigma (snd (fst cf)) (CompFun-drop-col ss t ts (snd cf))

coherentWith-to-compStepFun : (q : Pair FinEl FinEl) (qs : FinFun) ->
  CoherentWith q qs -> CompStepFun q qs
coherentWith-to-compStepFun q nil cw = tt
coherentWith-to-compStepFun q (cons r rs) cw =
  mkSigma (fst cw) (coherentWith-to-compStepFun q rs (snd cw))

------------------------------------------------------------------------
-- Part 7e: Comp-refl
------------------------------------------------------------------------

CompFun-cons-right : (s : Pair FinEl FinEl) (ss hs : FinFun) ->
  CoherentWith s ss -> CompFun ss hs -> CompFun ss (cons s hs)
CompFun-cons-right s nil hs cw cf = tt
CompFun-cons-right s (cons t ts) hs cw cf =
  mkSigma (mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst cw (Comp-sym (fst t) (fst s) c)))
                    (fst cf))
          (CompFun-cons-right s ts hs (snd cw) (snd cf))

{-# TERMINATING #-}
mutual
  Comp-refl : (v : FinEl) -> Coherent v -> Comp v v
  Comp-refl Bot coh = tt
  Comp-refl UCode coh = tt
  Comp-refl PropCode coh = tt
  Comp-refl (FunEl g) coh = CompFun-refl g (cft-from-cf g coh)
  Comp-refl (PiCode a f) coh =
    mkSigma (Comp-refl a (fst coh)) (CompFun-refl f (snd coh))
  Comp-refl (SigmaCode a f) coh =
    mkSigma (Comp-refl a (fst coh)) (CompFun-refl f (snd coh))
  Comp-refl (PairCode u v) coh =
    mkSigma (Comp-refl u (fst (fst coh))) (Comp-refl v (snd (fst coh)))

  CompFun-refl : (g : FinFun) -> CoherentFunTail g -> CompFun g g
  CompFun-refl nil coh = tt
  CompFun-refl (cons s ss) coh =
    mkSigma (mkSigma (\ _ -> Comp-refl (snd s) (CFTcons.val-coh coh))
                      (coherentWith-to-compStepFun s ss (CFTcons.compat coh)))
            (CompFun-cons-right s ss ss (CFTcons.compat coh)
              (CompFun-refl ss (CFTcons.tail-coh coh)))

------------------------------------------------------------------------
-- Part 7f-pre: Helper lemmas
------------------------------------------------------------------------

LeCode-Sup-Bot : (x y : FinEl) -> LeCode x Bot -> LeCode y Bot -> LeCode (Sup x y) Bot
LeCode-Sup-Bot Bot          y lx ly = ly
LeCode-Sup-Bot UCode        y ()
LeCode-Sup-Bot PropCode     y ()
LeCode-Sup-Bot (FunEl g)    y ()
LeCode-Sup-Bot (PiCode a f) y ()
LeCode-Sup-Bot (SigmaCode a f) y ()
LeCode-Sup-Bot (PairCode u v) y ()

mutual
  EvalFun-step-le-Bot : (n : Nat) (b : FinEl) (ps : FinFun) (u : FinEl) ->
    LeCode b Bot -> LeFunCode ps nil -> LeCode (EvalFun-step n b ps u) Bot
  EvalFun-step-le-Bot zero b ps u lb lps = EvalFun-le-Bot ps u lps
  EvalFun-step-le-Bot (suc _) b ps u lb lps =
    LeCode-Sup-Bot b (EvalFun ps u) lb (EvalFun-le-Bot ps u lps)

  EvalFun-le-Bot : (h : FinFun) (u : FinEl) -> LeFunCode h nil -> LeCode (EvalFun h u) Bot
  EvalFun-le-Bot nil u lh = tt
  EvalFun-le-Bot (cons p ps) u lh =
    EvalFun-step-le-Bot (leFinEl (fst p) u) (snd p) ps u (fst lh) (snd lh)

{-# TERMINATING #-}
mutual
  LeCode-trans-to-Bot : (u v : FinEl) -> LeCode u v -> LeCode v Bot -> LeCode u Bot
  LeCode-trans-to-Bot Bot v lu lv = tt
  LeCode-trans-to-Bot UCode Bot ()
  LeCode-trans-to-Bot UCode UCode lu ()
  LeCode-trans-to-Bot UCode PropCode ()
  LeCode-trans-to-Bot UCode (FunEl h) ()
  LeCode-trans-to-Bot UCode (PiCode b h) ()
  LeCode-trans-to-Bot UCode (SigmaCode b h) ()
  LeCode-trans-to-Bot UCode (PairCode u v) ()
  LeCode-trans-to-Bot PropCode Bot ()
  LeCode-trans-to-Bot PropCode UCode ()
  LeCode-trans-to-Bot PropCode PropCode lu ()
  LeCode-trans-to-Bot PropCode (FunEl h) ()
  LeCode-trans-to-Bot PropCode (PiCode b h) ()
  LeCode-trans-to-Bot PropCode (SigmaCode b h) ()
  LeCode-trans-to-Bot PropCode (PairCode u v) ()
  LeCode-trans-to-Bot (FunEl g) Bot ()
  LeCode-trans-to-Bot (FunEl g) UCode ()
  LeCode-trans-to-Bot (FunEl g) PropCode ()
  LeCode-trans-to-Bot (FunEl g) (FunEl h) lu ()
  LeCode-trans-to-Bot (FunEl g) (PiCode b h) ()
  LeCode-trans-to-Bot (FunEl g) (SigmaCode b h) ()
  LeCode-trans-to-Bot (FunEl g) (PairCode u v) ()
  LeCode-trans-to-Bot (PiCode a f) Bot ()
  LeCode-trans-to-Bot (PiCode a f) UCode ()
  LeCode-trans-to-Bot (PiCode a f) PropCode ()
  LeCode-trans-to-Bot (PiCode a f) (FunEl h) ()
  LeCode-trans-to-Bot (PiCode a f) (PiCode b g) lu ()
  LeCode-trans-to-Bot (PiCode a f) (SigmaCode b g) ()
  LeCode-trans-to-Bot (PiCode a f) (PairCode u v) ()
  LeCode-trans-to-Bot (SigmaCode a f) Bot ()
  LeCode-trans-to-Bot (SigmaCode a f) UCode ()
  LeCode-trans-to-Bot (SigmaCode a f) PropCode ()
  LeCode-trans-to-Bot (SigmaCode a f) (FunEl h) ()
  LeCode-trans-to-Bot (SigmaCode a f) (PiCode b g) ()
  LeCode-trans-to-Bot (SigmaCode a f) (SigmaCode b g) lu ()
  LeCode-trans-to-Bot (SigmaCode a f) (PairCode u v) ()
  LeCode-trans-to-Bot (PairCode u1 v1) Bot ()
  LeCode-trans-to-Bot (PairCode u1 v1) UCode ()
  LeCode-trans-to-Bot (PairCode u1 v1) PropCode ()
  LeCode-trans-to-Bot (PairCode u1 v1) (FunEl h) ()
  LeCode-trans-to-Bot (PairCode u1 v1) (PiCode b g) ()
  LeCode-trans-to-Bot (PairCode u1 v1) (SigmaCode b g) ()
  LeCode-trans-to-Bot (PairCode u1 v1) (PairCode u2 v2) lu ()

  LeFunCode-trans-to-nil : (g h : FinFun) -> LeFunCode g h -> LeFunCode h nil -> LeFunCode g nil
  LeFunCode-trans-to-nil nil h lg lh = tt
  LeFunCode-trans-to-nil (cons s ss) h lg lh =
    mkSigma (LeCode-trans-to-Bot (snd s) (EvalFun h (fst s)) (fst lg) (EvalFun-le-Bot h (fst s) lh))
            (LeFunCode-trans-to-nil ss h (snd lg) lh)

{-# TERMINATING #-}
mutual
  LeCode-Bot-Comp : (u v : FinEl) -> LeCode u Bot -> Comp u v
  LeCode-Bot-Comp Bot v le = tt
  LeCode-Bot-Comp UCode v ()
  LeCode-Bot-Comp PropCode v ()
  LeCode-Bot-Comp (FunEl g) v ()
  LeCode-Bot-Comp (PiCode a f) v ()
  LeCode-Bot-Comp (SigmaCode a f) v ()
  LeCode-Bot-Comp (PairCode u v2) v ()

  LeFunCode-nil-CompFun : (g h : FinFun) -> LeFunCode g nil -> CompFun g h
  LeFunCode-nil-CompFun nil h lg = tt
  LeFunCode-nil-CompFun (cons s ss) h lg =
    mkSigma (LeFunCode-nil-CompStepFun s h (fst lg))
            (LeFunCode-nil-CompFun ss h (snd lg))

  LeFunCode-nil-CompStepFun : (s : Pair FinEl FinEl) (h : FinFun) ->
    LeCode (snd s) Bot -> CompStepFun s h
  LeFunCode-nil-CompStepFun s nil lb = tt
  LeFunCode-nil-CompStepFun s (cons t ts) lb =
    mkSigma (\ _ -> LeCode-Bot-Comp (snd s) (snd t) lb)
            (LeFunCode-nil-CompStepFun s ts lb)

------------------------------------------------------------------------
-- Part 7f: Comp-down
------------------------------------------------------------------------

comp-Sup-sym : (a b v : FinEl) -> Comp a v -> Comp b v -> Comp (Sup a b) v
comp-Sup-sym a b v ca cb =
  Comp-sym v (Sup a b) (comp-Sup v a b (Comp-sym a v ca) (Comp-sym b v cb))

{-# TERMINATING #-}
mutual
  Comp-down : (u u' v : FinEl) -> LeCode u u' -> Comp u' v -> Comp u v
  Comp-down Bot u' v le c = comp-Bot-l v
  -- UCode
  Comp-down UCode Bot v () c
  Comp-down UCode UCode v le c = c
  Comp-down UCode PropCode v () c
  Comp-down UCode (FunEl h) v () c
  Comp-down UCode (PiCode b g) v () c
  Comp-down UCode (SigmaCode b g) v () c
  Comp-down UCode (PairCode u v2) v () c
  -- PropCode
  Comp-down PropCode Bot v () c
  Comp-down PropCode UCode v () c
  Comp-down PropCode PropCode v le c = c
  Comp-down PropCode (FunEl h) v () c
  Comp-down PropCode (PiCode b g) v () c
  Comp-down PropCode (SigmaCode b g) v () c
  Comp-down PropCode (PairCode u v2) v () c
  -- FunEl
  Comp-down (FunEl g) Bot v () c
  Comp-down (FunEl g) UCode v () c
  Comp-down (FunEl g) PropCode v () c
  Comp-down (FunEl g) (FunEl h) Bot le c = tt
  Comp-down (FunEl g) (FunEl h) UCode le ()
  Comp-down (FunEl g) (FunEl h) PropCode le ()
  Comp-down (FunEl g) (FunEl h) (FunEl j) le c =
    LeFunCode-CompFun-trans g h j le c
  Comp-down (FunEl g) (FunEl h) (PiCode b k) le ()
  Comp-down (FunEl g) (FunEl h) (SigmaCode b k) le ()
  Comp-down (FunEl g) (FunEl h) (PairCode u v2) le ()
  Comp-down (FunEl g) (PiCode b h) v () c
  Comp-down (FunEl g) (SigmaCode b h) v () c
  Comp-down (FunEl g) (PairCode u v2) v () c
  -- PiCode
  Comp-down (PiCode a f) Bot v () c
  Comp-down (PiCode a f) UCode v () c
  Comp-down (PiCode a f) PropCode v () c
  Comp-down (PiCode a f) (FunEl h) v () c
  Comp-down (PiCode a f) (PiCode b g) Bot le c = tt
  Comp-down (PiCode a f) (PiCode b g) UCode le ()
  Comp-down (PiCode a f) (PiCode b g) PropCode le ()
  Comp-down (PiCode a f) (PiCode b g) (FunEl j) le c = c
  Comp-down (PiCode a f) (PiCode b g) (PiCode c2 k) le comp =
    mkSigma (Comp-down a b c2 (fst le) (fst comp))
            (LeFunCode-CompFun-trans f g k (snd le) (snd comp))
  Comp-down (PiCode a f) (PiCode b g) (SigmaCode c2 k) le ()
  Comp-down (PiCode a f) (PiCode b g) (PairCode u v2) le ()
  Comp-down (PiCode a f) (SigmaCode b g) v () c
  Comp-down (PiCode a f) (PairCode u v2) v () c
  -- SigmaCode (mirrors PiCode)
  Comp-down (SigmaCode a f) Bot v () c
  Comp-down (SigmaCode a f) UCode v () c
  Comp-down (SigmaCode a f) PropCode v () c
  Comp-down (SigmaCode a f) (FunEl h) v () c
  Comp-down (SigmaCode a f) (PiCode b g) v () c
  Comp-down (SigmaCode a f) (SigmaCode b g) Bot le c = tt
  Comp-down (SigmaCode a f) (SigmaCode b g) UCode le ()
  Comp-down (SigmaCode a f) (SigmaCode b g) PropCode le ()
  Comp-down (SigmaCode a f) (SigmaCode b g) (FunEl j) le c = c
  Comp-down (SigmaCode a f) (SigmaCode b g) (PiCode c2 k) le ()
  Comp-down (SigmaCode a f) (SigmaCode b g) (SigmaCode c2 k) le comp =
    mkSigma (Comp-down a b c2 (fst le) (fst comp))
            (LeFunCode-CompFun-trans f g k (snd le) (snd comp))
  Comp-down (SigmaCode a f) (SigmaCode b g) (PairCode u v2) le ()
  Comp-down (SigmaCode a f) (PairCode u v2) v () c
  -- PairCode
  Comp-down (PairCode u1 v1) Bot v () c
  Comp-down (PairCode u1 v1) UCode v () c
  Comp-down (PairCode u1 v1) PropCode v () c
  Comp-down (PairCode u1 v1) (FunEl h) v () c
  Comp-down (PairCode u1 v1) (PiCode b g) v () c
  Comp-down (PairCode u1 v1) (SigmaCode b g) v () c
  Comp-down (PairCode u1 v1) (PairCode u2 v2) Bot le c = tt
  Comp-down (PairCode u1 v1) (PairCode u2 v2) UCode le ()
  Comp-down (PairCode u1 v1) (PairCode u2 v2) PropCode le ()
  Comp-down (PairCode u1 v1) (PairCode u2 v2) (FunEl j) le ()
  Comp-down (PairCode u1 v1) (PairCode u2 v2) (PiCode c2 k) le ()
  Comp-down (PairCode u1 v1) (PairCode u2 v2) (SigmaCode c2 k) le ()
  Comp-down (PairCode u1 v1) (PairCode u2 v2) (PairCode u3 v3) le comp =
    mkSigma (Comp-down u1 u2 u3 (fst le) (fst comp))
            (Comp-down v1 v2 v3 (snd le) (snd comp))

  LeFunCode-CompFun-trans : (g h j : FinFun) ->
    LeFunCode g h -> CompFun h j -> CompFun g j
  LeFunCode-CompFun-trans nil h j le cf = tt
  LeFunCode-CompFun-trans (cons s ss) h j le cf =
    mkSigma (build-CompStepFun s j h (fst le) cf)
            (LeFunCode-CompFun-trans ss h j (snd le) cf)

  build-CompStepFun : (s : Pair FinEl FinEl) (j h : FinFun) ->
    LeCode (snd s) (EvalFun h (fst s)) -> CompFun h j -> CompStepFun s j
  build-CompStepFun s nil h le cf = tt
  build-CompStepFun s (cons t ts) h le cf =
    mkSigma
      (\ comp-keys ->
        let col = extract-col h t ts cf
            comp-eval = EvalFun-guarded-comp h (fst s) t col comp-keys
        in Comp-down (snd s) (EvalFun h (fst s)) (snd t) le comp-eval)
      (build-CompStepFun s ts h le (CompFun-drop-col h t ts cf))

  extract-col : (h : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun h (cons t ts) -> CompFun h (cons t nil)
  extract-col nil t ts cf = tt
  extract-col (cons r rs) t ts cf =
    mkSigma (mkSigma (fst (fst cf)) tt)
            (extract-col rs t ts (snd cf))

  EvalFun-guarded-comp : (h : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
    CompFun h (cons t nil) -> Comp xi (fst t) ->
    Comp (EvalFun h xi) (snd t)
  EvalFun-guarded-comp nil xi t col cxi = comp-Bot-l (snd t)
  EvalFun-guarded-comp (cons r rs) xi t col cxi =
    EvalFun-guarded-comp-step (leFinEl (fst r) xi) r rs xi t refl
      (fst (fst col)) cxi (EvalFun-guarded-comp rs xi t (snd col) cxi)

  EvalFun-guarded-comp-step : (n : Nat) (r : Pair FinEl FinEl) (rs : FinFun)
    (xi : FinEl) (t : Pair FinEl FinEl) ->
    Eq n (leFinEl (fst r) xi) ->
    CompStepStep r t -> Comp xi (fst t) ->
    Comp (EvalFun rs xi) (snd t) ->
    Comp (EvalFun-step n (snd r) rs xi) (snd t)
  EvalFun-guarded-comp-step zero r rs xi t eq css cxi ih = ih
  EvalFun-guarded-comp-step (suc _) r rs xi t eq css cxi ih =
    let le = leFinEl-sound (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = Comp-down (fst r) xi (fst t) le cxi
    in comp-Sup-sym (snd r) (EvalFun rs xi) (snd t) (css comp-keys) ih

------------------------------------------------------------------------
-- Part 7g: LeCode-Comp
------------------------------------------------------------------------

LeCode-Comp : (u v w : FinEl) -> Coherent w -> LeCode u w -> LeCode v w -> Comp u v
LeCode-Comp u v w coh lu lv =
  Comp-down u w v lu (Comp-sym v w (Comp-down v w w lv (Comp-refl w coh)))

compStepFun-to-coherentWith : (q : Pair FinEl FinEl) (h : FinFun) ->
  CompStepFun q h -> CoherentWith q h
compStepFun-to-coherentWith q nil csf = tt
compStepFun-to-coherentWith q (cons r rs) csf =
  mkSigma (fst csf) (compStepFun-to-coherentWith q rs (snd csf))

coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
coherentWith-append q nil h cw1 cw2 = cw2
coherentWith-append q (cons r rs) h cw1 cw2 =
  mkSigma (fst cw1) (coherentWith-append q rs h (snd cw1) cw2)

------------------------------------------------------------------------
-- NotBot-Sup-Comp: non-Bot is preserved by Sup with compatible element
------------------------------------------------------------------------

NotBot-Sup-Comp : (u v : FinEl) -> NotBot u -> Comp u v -> NotBot (Sup u v)
NotBot-Sup-Comp Bot v ()
NotBot-Sup-Comp UCode Bot nb c = tt
NotBot-Sup-Comp UCode UCode nb c = tt
NotBot-Sup-Comp UCode PropCode nb ()
NotBot-Sup-Comp UCode (FunEl h) nb ()
NotBot-Sup-Comp UCode (PiCode b g) nb ()
NotBot-Sup-Comp UCode (SigmaCode b g) nb ()
NotBot-Sup-Comp UCode (PairCode u2 v2) nb ()
NotBot-Sup-Comp PropCode Bot nb c = tt
NotBot-Sup-Comp PropCode UCode nb ()
NotBot-Sup-Comp PropCode PropCode nb c = tt
NotBot-Sup-Comp PropCode (FunEl h) nb ()
NotBot-Sup-Comp PropCode (PiCode b g) nb ()
NotBot-Sup-Comp PropCode (SigmaCode b g) nb ()
NotBot-Sup-Comp PropCode (PairCode u2 v2) nb ()
NotBot-Sup-Comp (FunEl g) Bot nb c = tt
NotBot-Sup-Comp (FunEl g) UCode nb ()
NotBot-Sup-Comp (FunEl g) PropCode nb ()
NotBot-Sup-Comp (FunEl g) (FunEl h) nb c = tt
NotBot-Sup-Comp (FunEl g) (PiCode b h) nb ()
NotBot-Sup-Comp (FunEl g) (SigmaCode b h) nb ()
NotBot-Sup-Comp (FunEl g) (PairCode u2 v2) nb ()
NotBot-Sup-Comp (PiCode a f) Bot nb c = tt
NotBot-Sup-Comp (PiCode a f) UCode nb ()
NotBot-Sup-Comp (PiCode a f) PropCode nb ()
NotBot-Sup-Comp (PiCode a f) (FunEl h) nb ()
NotBot-Sup-Comp (PiCode a f) (PiCode b g) nb c = tt
NotBot-Sup-Comp (PiCode a f) (SigmaCode b g) nb ()
NotBot-Sup-Comp (PiCode a f) (PairCode u2 v2) nb ()
NotBot-Sup-Comp (SigmaCode a f) Bot nb c = tt
NotBot-Sup-Comp (SigmaCode a f) UCode nb ()
NotBot-Sup-Comp (SigmaCode a f) PropCode nb ()
NotBot-Sup-Comp (SigmaCode a f) (FunEl h) nb ()
NotBot-Sup-Comp (SigmaCode a f) (PiCode b g) nb ()
NotBot-Sup-Comp (SigmaCode a f) (SigmaCode b g) nb c = tt
NotBot-Sup-Comp (SigmaCode a f) (PairCode u2 v2) nb ()
NotBot-Sup-Comp (PairCode u1 v1) Bot nb c = tt
NotBot-Sup-Comp (PairCode u1 v1) UCode nb ()
NotBot-Sup-Comp (PairCode u1 v1) PropCode nb ()
NotBot-Sup-Comp (PairCode u1 v1) (FunEl h) nb ()
NotBot-Sup-Comp (PairCode u1 v1) (PiCode b g) nb ()
NotBot-Sup-Comp (PairCode u1 v1) (SigmaCode b g) nb ()
NotBot-Sup-Comp (PairCode u1 v1) (PairCode u2 v2) nb c = tt

------------------------------------------------------------------------
-- Or-NotBot helper for Coherent-Sup on PairCode
------------------------------------------------------------------------

Or-NotBot-Sup : (u1 v1 u2 v2 : FinEl) ->
  Or (NotBot u1) (NotBot v1) -> Comp u1 u2 -> Comp v1 v2 ->
  Or (NotBot (Sup u1 u2)) (NotBot (Sup v1 v2))
Or-NotBot-Sup u1 v1 u2 v2 (inl nb) cu cv = inl (NotBot-Sup-Comp u1 u2 nb cu)
Or-NotBot-Sup u1 v1 u2 v2 (inr nb) cu cv = inr (NotBot-Sup-Comp v1 v2 nb cv)

------------------------------------------------------------------------
-- Part 7h: Comp-value-EvalFun, Coherent-Sup, finMem-Sup, etc.
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  Comp-value-EvalFun : (q : Pair FinEl FinEl) (rest : FinFun) (xi : FinEl) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    CoherentWith q rest -> CompStepFun q rest ->
    Comp (snd q) (EvalFun rest xi)
  Comp-value-EvalFun q nil xi le cxi cohv cw csf = comp-Bot-r (snd q)
  Comp-value-EvalFun q (cons r rs) xi le cxi cohv cw csf =
    Comp-value-EvalFun-step (leFinEl (fst r) xi) q r rs xi refl
      le cxi cohv (fst cw) (snd cw) (fst csf) (snd csf)

  Comp-value-EvalFun-step : (n : Nat) (q r : Pair FinEl FinEl)
    (rs : FinFun) (xi : FinEl) ->
    Eq n (leFinEl (fst r) xi) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    (Comp (fst q) (fst r) -> Comp (snd q) (snd r)) ->
    CoherentWith q rs ->
    CompStepStep q r ->
    CompStepFun q rs ->
    Comp (snd q) (EvalFun-step n (snd r) rs xi)
  Comp-value-EvalFun-step zero q r rs xi eq le cxi cohv css cw css2 csf =
    Comp-value-EvalFun q rs xi le cxi cohv cw csf
  Comp-value-EvalFun-step (suc _) q r rs xi eq le cxi cohv css cw css2 csf =
    let le-r = leFinEl-sound (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = LeCode-Comp (fst q) (fst r) xi cxi le le-r
    in comp-Sup (snd q) (snd r) (EvalFun rs xi)
         (css comp-keys)
         (Comp-value-EvalFun q rs xi le cxi cohv cw csf)

  comp-EvalFun : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Comp (EvalFun k xi) (EvalFun h xi)
  comp-EvalFun nil h xi ckh cohk cxi = comp-Bot-l (EvalFun h xi)
  comp-EvalFun (cons q rest) h xi ckh cohk cxi =
    comp-EvalFun-step (leFinEl (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  comp-EvalFun-step : (n : Nat) (q : Pair FinEl FinEl) (rest h : FinFun)
    (xi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Comp (EvalFun-step n (snd q) rest xi) (EvalFun h xi)
  comp-EvalFun-step zero q rest h xi eq csf crf cohk cxi =
    comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
  comp-EvalFun-step (suc _) q rest h xi eq csf crf cohk cxi =
    let comp1 = Comp-value-EvalFun q h xi
                  (leFinEl-sound (fst q) xi (Eq-transport isPos eq tt))
                  cxi (CFTcons.val-coh cohk)
                  (compStepFun-to-coherentWith q h csf) csf
        comp2 = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
    in comp-Sup-sym (snd q) (EvalFun rest xi) (EvalFun h xi) comp1 comp2

  -- Sup-assoc
  Sup-assoc : (a b c : FinEl) -> Comp a b -> Comp b c ->
    Eq (Sup (Sup a b) c) (Sup a (Sup b c))
  Sup-assoc Bot b c cab cbc = refl
  -- UCode
  Sup-assoc UCode Bot c cab cbc = refl
  Sup-assoc UCode UCode Bot cab cbc = refl
  Sup-assoc UCode UCode UCode cab cbc = refl
  Sup-assoc UCode UCode PropCode cab ()
  Sup-assoc UCode UCode (FunEl j) cab ()
  Sup-assoc UCode UCode (PiCode e j) cab ()
  Sup-assoc UCode UCode (SigmaCode e j) cab ()
  Sup-assoc UCode UCode (PairCode u v) cab ()
  Sup-assoc UCode PropCode c () cbc
  Sup-assoc UCode (FunEl h) c () cbc
  Sup-assoc UCode (PiCode d h) c () cbc
  Sup-assoc UCode (SigmaCode d h) c () cbc
  Sup-assoc UCode (PairCode u v) c () cbc
  -- PropCode
  Sup-assoc PropCode Bot c cab cbc = refl
  Sup-assoc PropCode UCode c () cbc
  Sup-assoc PropCode PropCode Bot cab cbc = refl
  Sup-assoc PropCode PropCode UCode cab ()
  Sup-assoc PropCode PropCode PropCode cab cbc = refl
  Sup-assoc PropCode PropCode (FunEl j) cab ()
  Sup-assoc PropCode PropCode (PiCode e j) cab ()
  Sup-assoc PropCode PropCode (SigmaCode e j) cab ()
  Sup-assoc PropCode PropCode (PairCode u v) cab ()
  Sup-assoc PropCode (FunEl h) c () cbc
  Sup-assoc PropCode (PiCode d h) c () cbc
  Sup-assoc PropCode (SigmaCode d h) c () cbc
  Sup-assoc PropCode (PairCode u v) c () cbc
  -- FunEl
  Sup-assoc (FunEl g) Bot c cab cbc = refl
  Sup-assoc (FunEl g) UCode c () cbc
  Sup-assoc (FunEl g) PropCode c () cbc
  Sup-assoc (FunEl g) (FunEl h) Bot cab cbc = refl
  Sup-assoc (FunEl g) (FunEl h) UCode cab ()
  Sup-assoc (FunEl g) (FunEl h) PropCode cab ()
  Sup-assoc (FunEl g) (FunEl h) (FunEl j) cab cbc =
    Eq-cong FunEl (Eq-sym (append-assoc g h j))
  Sup-assoc (FunEl g) (FunEl h) (PiCode e j) cab ()
  Sup-assoc (FunEl g) (FunEl h) (SigmaCode e j) cab ()
  Sup-assoc (FunEl g) (FunEl h) (PairCode u v) cab ()
  Sup-assoc (FunEl g) (PiCode d h) c () cbc
  Sup-assoc (FunEl g) (SigmaCode d h) c () cbc
  Sup-assoc (FunEl g) (PairCode u v) c () cbc
  -- PiCode
  Sup-assoc (PiCode a f) Bot c cab cbc = refl
  Sup-assoc (PiCode a f) UCode c () cbc
  Sup-assoc (PiCode a f) PropCode c () cbc
  Sup-assoc (PiCode a f) (FunEl h) c () cbc
  Sup-assoc (PiCode a f) (PiCode d h) Bot cab cbc = refl
  Sup-assoc (PiCode a f) (PiCode d h) UCode cab ()
  Sup-assoc (PiCode a f) (PiCode d h) PropCode cab ()
  Sup-assoc (PiCode a f) (PiCode d h) (FunEl j) cab ()
  Sup-assoc (PiCode a f) (PiCode d h) (PiCode e j) cab cbc =
    PiCode-cong (Sup-assoc a d e (fst cab) (fst cbc))
                (Eq-sym (append-assoc f h j))
  Sup-assoc (PiCode a f) (PiCode d h) (SigmaCode e j) cab ()
  Sup-assoc (PiCode a f) (PiCode d h) (PairCode u v) cab ()
  Sup-assoc (PiCode a f) (SigmaCode d h) c () cbc
  Sup-assoc (PiCode a f) (PairCode u v) c () cbc
  -- SigmaCode
  Sup-assoc (SigmaCode a f) Bot c cab cbc = refl
  Sup-assoc (SigmaCode a f) UCode c () cbc
  Sup-assoc (SigmaCode a f) PropCode c () cbc
  Sup-assoc (SigmaCode a f) (FunEl h) c () cbc
  Sup-assoc (SigmaCode a f) (PiCode d h) c () cbc
  Sup-assoc (SigmaCode a f) (SigmaCode d h) Bot cab cbc = refl
  Sup-assoc (SigmaCode a f) (SigmaCode d h) UCode cab ()
  Sup-assoc (SigmaCode a f) (SigmaCode d h) PropCode cab ()
  Sup-assoc (SigmaCode a f) (SigmaCode d h) (FunEl j) cab ()
  Sup-assoc (SigmaCode a f) (SigmaCode d h) (PiCode e j) cab ()
  Sup-assoc (SigmaCode a f) (SigmaCode d h) (SigmaCode e j) cab cbc =
    SigmaCode-cong (Sup-assoc a d e (fst cab) (fst cbc))
                   (Eq-sym (append-assoc f h j))
  Sup-assoc (SigmaCode a f) (SigmaCode d h) (PairCode u v) cab ()
  Sup-assoc (SigmaCode a f) (PairCode u v) c () cbc
  -- PairCode
  Sup-assoc (PairCode u1 v1) Bot c cab cbc = refl
  Sup-assoc (PairCode u1 v1) UCode c () cbc
  Sup-assoc (PairCode u1 v1) PropCode c () cbc
  Sup-assoc (PairCode u1 v1) (FunEl h) c () cbc
  Sup-assoc (PairCode u1 v1) (PiCode d h) c () cbc
  Sup-assoc (PairCode u1 v1) (SigmaCode d h) c () cbc
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) Bot cab cbc = refl
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) UCode cab ()
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) PropCode cab ()
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) (FunEl j) cab ()
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) (PiCode e j) cab ()
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) (SigmaCode e j) cab ()
  Sup-assoc (PairCode u1 v1) (PairCode u2 v2) (PairCode u3 v3) cab cbc =
    PairCode-cong (Sup-assoc u1 u2 u3 (fst cab) (fst cbc))
                  (Sup-assoc v1 v2 v3 (snd cab) (snd cbc))

  -- EvalFun-append-eq
  EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
  EvalFun-append-eq nil h xi ckh cohk cxi = refl
  EvalFun-append-eq (cons q rest) h xi ckh cohk cxi =
    EvalFun-append-eq-step (leFinEl (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  EvalFun-append-eq-step : (n : Nat) (q : Pair FinEl FinEl) (rest h : FinFun)
    (xi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Eq (EvalFun-step n (snd q) (append rest h) xi)
       (Sup (EvalFun-step n (snd q) rest xi) (EvalFun h xi))
  EvalFun-append-eq-step zero q rest h xi eq csf crf cohk cxi =
    EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
  EvalFun-append-eq-step (suc _) q rest h xi eq csf crf cohk cxi =
    let ih = EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
        step1 : Eq (Sup (snd q) (EvalFun (append rest h) xi))
                    (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step1 = Eq-cong (Sup (snd q)) ih
        le-q = leFinEl-sound (fst q) xi (Eq-transport isPos eq tt)
        comp-qr = Comp-value-EvalFun q rest xi le-q cxi (CFTcons.val-coh cohk)
                    (CFTcons.compat cohk) (coherentWith-to-compStepFun q rest (CFTcons.compat cohk))
        comp-rh = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
        step2 : Eq (Sup (Sup (snd q) (EvalFun rest xi)) (EvalFun h xi))
                    (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step2 = Sup-assoc (snd q) (EvalFun rest xi) (EvalFun h xi)
                  comp-qr comp-rh
    in Eq-transport
         (\ z -> Eq (Sup (snd q) (EvalFun (append rest h) xi)) z)
         (Eq-sym step2) step1

  -- Coherent-Sup
  Coherent-Sup : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    Coherent (Sup a b)
  Coherent-Sup Bot b comp coha cohb = cohb
  -- UCode
  Coherent-Sup UCode Bot comp coha cohb = tt
  Coherent-Sup UCode UCode comp coha cohb = tt
  Coherent-Sup UCode PropCode () coha cohb
  Coherent-Sup UCode (FunEl h) comp coha cohb = tt
  Coherent-Sup UCode (PiCode c h) () coha cohb
  Coherent-Sup UCode (SigmaCode c h) () coha cohb
  Coherent-Sup UCode (PairCode u v) () coha cohb
  -- PropCode
  Coherent-Sup PropCode Bot comp coha cohb = tt
  Coherent-Sup PropCode UCode () coha cohb
  Coherent-Sup PropCode PropCode comp coha cohb = tt
  Coherent-Sup PropCode (FunEl h) comp coha cohb = tt
  Coherent-Sup PropCode (PiCode c h) () coha cohb
  Coherent-Sup PropCode (SigmaCode c h) () coha cohb
  Coherent-Sup PropCode (PairCode u v) () coha cohb
  -- FunEl
  Coherent-Sup (FunEl g) Bot comp coha cohb = coha
  Coherent-Sup (FunEl g) UCode comp coha cohb = tt
  Coherent-Sup (FunEl g) PropCode comp coha cohb = tt
  Coherent-Sup (FunEl g) (FunEl h) comp coha cohb =
    CoherentFun-append g h coha cohb comp
  Coherent-Sup (FunEl g) (PiCode c h) () coha cohb
  Coherent-Sup (FunEl g) (SigmaCode c h) () coha cohb
  Coherent-Sup (FunEl g) (PairCode u v) () coha cohb
  -- PiCode
  Coherent-Sup (PiCode a f) Bot comp coha cohb = coha
  Coherent-Sup (PiCode a f) UCode () coha cohb
  Coherent-Sup (PiCode a f) PropCode () coha cohb
  Coherent-Sup (PiCode a f) (FunEl h) () coha cohb
  Coherent-Sup (PiCode a f) (PiCode c h) comp coha cohb =
    mkSigma (Coherent-Sup a c (fst comp) (fst coha) (fst cohb))
            (CoherentFunTail-append f h (snd coha) (snd cohb) (snd comp))
  Coherent-Sup (PiCode a f) (SigmaCode c h) () coha cohb
  Coherent-Sup (PiCode a f) (PairCode u v) () coha cohb
  -- SigmaCode
  Coherent-Sup (SigmaCode a f) Bot comp coha cohb = coha
  Coherent-Sup (SigmaCode a f) UCode () coha cohb
  Coherent-Sup (SigmaCode a f) PropCode () coha cohb
  Coherent-Sup (SigmaCode a f) (FunEl h) () coha cohb
  Coherent-Sup (SigmaCode a f) (PiCode c h) () coha cohb
  Coherent-Sup (SigmaCode a f) (SigmaCode c h) comp coha cohb =
    mkSigma (Coherent-Sup a c (fst comp) (fst coha) (fst cohb))
            (CoherentFunTail-append f h (snd coha) (snd cohb) (snd comp))
  Coherent-Sup (SigmaCode a f) (PairCode u v) () coha cohb
  -- PairCode
  Coherent-Sup (PairCode u1 v1) Bot comp coha cohb = coha
  Coherent-Sup (PairCode u1 v1) UCode () coha cohb
  Coherent-Sup (PairCode u1 v1) PropCode () coha cohb
  Coherent-Sup (PairCode u1 v1) (FunEl h) () coha cohb
  Coherent-Sup (PairCode u1 v1) (PiCode c h) () coha cohb
  Coherent-Sup (PairCode u1 v1) (SigmaCode c h) () coha cohb
  Coherent-Sup (PairCode u1 v1) (PairCode u2 v2) comp coha cohb =
    mkSigma (mkSigma (Coherent-Sup u1 u2 (fst comp) (fst (fst coha)) (fst (fst cohb)))
                      (Coherent-Sup v1 v2 (snd comp) (snd (fst coha)) (snd (fst cohb))))
            (Or-NotBot-Sup u1 v1 u2 v2 (snd coha) (fst comp) (snd comp))

  -- CoherentFunTail-append
  CoherentFunTail-append : (g h : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CompFun g h ->
    CoherentFunTail (append g h)
  CoherentFunTail-append nil h cohg cohh cgh = cohh
  CoherentFunTail-append (cons p ps) h cohg cohh cgh =
    mkCFT (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) (CFTcons.val-nbot cohg)
          (coherentWith-append p ps h (CFTcons.compat cohg)
            (compStepFun-to-coherentWith p h (fst cgh)))
          (CoherentFunTail-append ps h (CFTcons.tail-coh cohg) cohh (snd cgh))

  CoherentFun-append : (g h : FinFun) ->
    CoherentFun g -> CoherentFun h -> CompFun g h ->
    CoherentFun (append g h)
  CoherentFun-append nil h () cohh cgh
  CoherentFun-append (cons p ps) h cohg cohh cgh =
    CoherentFunTail-append (cons p ps) h cohg (cft-from-cf h cohh) cgh

  -- finMemUCode-Sup
  finMemUCode-Sup : (a c : FinEl) -> Comp a c ->
    FinMem a UCode -> FinMem c UCode -> FinMem (Sup a c) UCode
  finMemUCode-Sup Bot c comp aU cU = cU
  -- UCode
  finMemUCode-Sup UCode Bot comp aU cU = tt
  finMemUCode-Sup UCode UCode comp aU cU = tt
  finMemUCode-Sup UCode PropCode () aU cU
  finMemUCode-Sup UCode (FunEl h) comp aU ()
  finMemUCode-Sup UCode (PiCode c h) () aU cU
  finMemUCode-Sup UCode (SigmaCode c h) () aU cU
  finMemUCode-Sup UCode (PairCode u v) () aU cU
  -- PropCode
  finMemUCode-Sup PropCode Bot comp aU cU = tt
  finMemUCode-Sup PropCode UCode () aU cU
  finMemUCode-Sup PropCode PropCode comp aU cU = tt
  finMemUCode-Sup PropCode (FunEl h) comp aU ()
  finMemUCode-Sup PropCode (PiCode c h) () aU cU
  finMemUCode-Sup PropCode (SigmaCode c h) () aU cU
  finMemUCode-Sup PropCode (PairCode u v) () aU cU
  -- FunEl
  finMemUCode-Sup (FunEl g) c comp () cU
  -- PiCode
  finMemUCode-Sup (PiCode a f) Bot comp aU cU = aU
  finMemUCode-Sup (PiCode a f) UCode () aU cU
  finMemUCode-Sup (PiCode a f) PropCode () aU cU
  finMemUCode-Sup (PiCode a f) (FunEl h) comp aU ()
  finMemUCode-Sup (PiCode a f) (PiCode c h) comp aU cU =
    mkSigma (finMemUCode-Sup a c (fst comp) (fst aU) (fst cU))
            (mkSigma (FinMemAllU-append-Sup a c f h (fst comp)
                       (coh-from-aU a (fst aU)) (coh-from-aU c (fst cU))
                       (fst aU) (fst cU)
                       (snd (snd aU)) (snd (snd cU))
                       (fst (snd aU)) (fst (snd cU)))
                     (CoherentFunTail-append f h (snd (snd aU)) (snd (snd cU)) (snd comp)))
  finMemUCode-Sup (PiCode a f) (SigmaCode c h) () aU cU
  finMemUCode-Sup (PiCode a f) (PairCode u v) () aU cU
  -- SigmaCode
  finMemUCode-Sup (SigmaCode a f) Bot comp aU cU = aU
  finMemUCode-Sup (SigmaCode a f) UCode () aU cU
  finMemUCode-Sup (SigmaCode a f) PropCode () aU cU
  finMemUCode-Sup (SigmaCode a f) (FunEl h) comp aU ()
  finMemUCode-Sup (SigmaCode a f) (PiCode c h) () aU cU
  finMemUCode-Sup (SigmaCode a f) (SigmaCode c h) comp aU cU =
    mkSigma (finMemUCode-Sup a c (fst comp) (fst aU) (fst cU))
            (mkSigma (FinMemAllU-append-Sup a c f h (fst comp)
                       (coh-from-aU a (fst aU)) (coh-from-aU c (fst cU))
                       (fst aU) (fst cU)
                       (snd (snd aU)) (snd (snd cU))
                       (fst (snd aU)) (fst (snd cU)))
                     (CoherentFunTail-append f h (snd (snd aU)) (snd (snd cU)) (snd comp)))
  finMemUCode-Sup (SigmaCode a f) (PairCode u v) () aU cU
  -- PairCode
  finMemUCode-Sup (PairCode u v) c comp () cU

  -- finMemPropCode-Sup
  finMemPropCode-Sup : (a c : FinEl) -> Comp a c ->
    FinMem a PropCode -> FinMem c PropCode -> FinMem (Sup a c) PropCode
  finMemPropCode-Sup Bot c comp aP cP = cP
  finMemPropCode-Sup UCode Bot comp aP cP = aP
  finMemPropCode-Sup UCode UCode comp aP ()
  finMemPropCode-Sup UCode PropCode () aP cP
  finMemPropCode-Sup UCode (FunEl h) comp aP ()
  finMemPropCode-Sup UCode (PiCode c h) () aP cP
  finMemPropCode-Sup UCode (SigmaCode c h) () aP cP
  finMemPropCode-Sup UCode (PairCode u v) () aP cP
  finMemPropCode-Sup PropCode Bot comp aP cP = aP
  finMemPropCode-Sup PropCode UCode () aP cP
  finMemPropCode-Sup PropCode PropCode comp aP ()
  finMemPropCode-Sup PropCode (FunEl h) comp aP ()
  finMemPropCode-Sup PropCode (PiCode c h) () aP cP
  finMemPropCode-Sup PropCode (SigmaCode c h) () aP cP
  finMemPropCode-Sup PropCode (PairCode u v) () aP cP
  finMemPropCode-Sup (FunEl g) c comp () cP
  finMemPropCode-Sup (PiCode a f) Bot comp aP cP = aP
  finMemPropCode-Sup (PiCode a f) UCode () aP cP
  finMemPropCode-Sup (PiCode a f) PropCode () aP cP
  finMemPropCode-Sup (PiCode a f) (FunEl h) comp aP ()
  finMemPropCode-Sup (PiCode a f) (PiCode c h) comp aP cP =
    mkSigma (finMemUCode-Sup a c (fst comp) (fst aP) (fst cP))
            (mkSigma (FinMemAllProp-append-Sup a c f h (fst comp)
                       (coh-from-aU a (fst aP)) (coh-from-aU c (fst cP))
                       (fst aP) (fst cP)
                       (snd (snd aP)) (snd (snd cP))
                       (fst (snd aP)) (fst (snd cP)))
                     (CoherentFunTail-append f h (snd (snd aP)) (snd (snd cP)) (snd comp)))
  finMemPropCode-Sup (PiCode a f) (SigmaCode c h) () aP cP
  finMemPropCode-Sup (PiCode a f) (PairCode u v) () aP cP
  finMemPropCode-Sup (SigmaCode a f) c comp () cP
  finMemPropCode-Sup (PairCode u v) c comp () cP

  -- FinMemAllProp-append-Sup
  FinMemAllProp-append-Sup : (d c : FinEl) (f h : FinFun) ->
    Comp d c -> Coherent d -> Coherent c ->
    FinMem d UCode -> FinMem c UCode ->
    CoherentFunTail f -> CoherentFunTail h ->
    FinMemAllProp f d -> FinMemAllProp h c ->
    FinMemAllProp (append f h) (Sup d c)
  FinMemAllProp-append-Sup d c nil h cd cohd cohc dU cU cohf cohh memf memh =
    FinMemAllProp-Sup-right d c h cd dU cohc cohh memh
  FinMemAllProp-append-Sup d c (cons p ps) h cd cohd cohc dU cU cohf cohh memf memh =
    mkSigma
      (mkSigma (finMem-Sup-left d c (fst p) cd cohd cohc cU
                  (CFTcons.key-coh cohf) (fst (fst memf)))
               (snd (fst memf)))
      (FinMemAllProp-append-Sup d c ps h cd cohd cohc dU cU
        (CFTcons.tail-coh cohf) cohh (snd memf) memh)

  FinMemAllProp-Sup-right : (d c : FinEl) (h : FinFun) ->
    Comp d c -> FinMem d UCode -> Coherent c ->
    CoherentFunTail h ->
    FinMemAllProp h c ->
    FinMemAllProp h (Sup d c)
  FinMemAllProp-Sup-right d c nil cd dU cohc cohh memh = tt
  FinMemAllProp-Sup-right d c (cons p ps) cd dU cohc cohh memh =
    mkSigma
      (mkSigma (finMem-Sup-right d c (fst p) cd dU
                  (CFTcons.key-coh cohh) (fst (fst memh)))
               (snd (fst memh)))
      (FinMemAllProp-Sup-right d c ps cd dU cohc
        (CFTcons.tail-coh cohh) (snd memh))

  -- FinMemAllU-append-Sup (unchanged — operates on FinFun)
  FinMemAllU-append-Sup : (d c : FinEl) (f h : FinFun) ->
    Comp d c -> Coherent d -> Coherent c ->
    FinMem d UCode -> FinMem c UCode ->
    CoherentFunTail f -> CoherentFunTail h ->
    FinMemAllU f d -> FinMemAllU h c ->
    FinMemAllU (append f h) (Sup d c)
  FinMemAllU-append-Sup d c nil h cd cohd cohc dU cU cohf cohh memf memh =
    FinMemAllU-Sup-right d c h cd dU cohc cohh memh
  FinMemAllU-append-Sup d c (cons p ps) h cd cohd cohc dU cU cohf cohh memf memh =
    mkSigma
      (mkSigma (finMem-Sup-left d c (fst p) cd cohd cohc cU
                  (CFTcons.key-coh cohf) (fst (fst memf)))
               (snd (fst memf)))
      (FinMemAllU-append-Sup d c ps h cd cohd cohc dU cU
        (CFTcons.tail-coh cohf) cohh (snd memf) memh)

  FinMemAllU-Sup-right : (d c : FinEl) (h : FinFun) ->
    Comp d c -> FinMem d UCode -> Coherent c ->
    CoherentFunTail h ->
    FinMemAllU h c ->
    FinMemAllU h (Sup d c)
  FinMemAllU-Sup-right d c nil cd dU cohc cohh memh = tt
  FinMemAllU-Sup-right d c (cons p ps) cd dU cohc cohh memh =
    mkSigma
      (mkSigma (finMem-Sup-right d c (fst p) cd dU
                  (CFTcons.key-coh cohh) (fst (fst memh)))
               (snd (fst memh)))
      (FinMemAllU-Sup-right d c ps cd dU cohc
        (CFTcons.tail-coh cohh) (snd memh))

  -- EvalFun-in-UCode (unchanged)
  EvalFun-in-UCode : (f : FinFun) (x d : FinEl) ->
    CoherentFunTail f -> Coherent x -> FinMemAllU f d ->
    FinMem (EvalFun f x) UCode
  EvalFun-in-UCode nil x d cohf cx allU = tt
  EvalFun-in-UCode (cons q rest) x d cohf cx allU =
    EvalFun-in-UCode-step (leFinEl (fst q) x) q rest x d refl cohf cx allU

  EvalFun-in-UCode-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (x d : FinEl) ->
    Eq n (leFinEl (fst q) x) ->
    CoherentFunTail (cons q rest) -> Coherent x -> FinMemAllU (cons q rest) d ->
    FinMem (EvalFun-step n (snd q) rest x) UCode
  EvalFun-in-UCode-step zero q rest x d eq cohf cx allU =
    EvalFun-in-UCode rest x d (CFTcons.tail-coh cohf) cx (snd allU)
  EvalFun-in-UCode-step (suc _) q rest x d eq cohf cx allU =
    let vU = snd (fst allU)
        restU = EvalFun-in-UCode rest x d (CFTcons.tail-coh cohf) cx (snd allU)
        comp-vr = Comp-value-EvalFun q rest x
                    (leFinEl-sound (fst q) x (Eq-transport isPos eq tt))
                    cx (CFTcons.val-coh cohf) (CFTcons.compat cohf)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohf))
    in finMemUCode-Sup (snd q) (EvalFun rest x) comp-vr vU restU

  -- Coherent-EvalFun (unchanged)
  Coherent-EvalFun : (k : FinFun) (u : FinEl) ->
    CoherentFunTail k -> Coherent u -> Coherent (EvalFun k u)
  Coherent-EvalFun nil u cohk cohu = tt
  Coherent-EvalFun (cons q rest) u cohk cohu =
    Coherent-EvalFun-step (leFinEl (fst q) u) q rest u refl cohk cohu

  Coherent-EvalFun-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    Coherent (EvalFun-step n (snd q) rest u)
  Coherent-EvalFun-step zero q rest u eq cohk cohu =
    Coherent-EvalFun rest u (CFTcons.tail-coh cohk) cohu
  Coherent-EvalFun-step (suc _) q rest u eq cohk cohu =
    let cohv = CFTcons.val-coh cohk
        coh-rest = Coherent-EvalFun rest u (CFTcons.tail-coh cohk) cohu
        comp-vr = Comp-value-EvalFun q rest u
                    (leFinEl-sound (fst q) u (Eq-transport isPos eq tt))
                    cohu cohv (CFTcons.compat cohk)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohk))
    in Coherent-Sup (snd q) (EvalFun rest u) comp-vr cohv coh-rest

  -- finMem-Sup-right: membership in right implies membership in Sup
  finMem-Sup-right : (a b u : FinEl) -> Comp a b -> FinMem a UCode -> Coherent u ->
    FinMem u b -> FinMem u (Sup a b)

  finMem-Sup-right a b Bot comp aU cohu mem = finMemUCode-Sup a b comp aU mem

  -- u = UCode
  finMem-Sup-right Bot          UCode UCode comp aU cohu mem = tt
  finMem-Sup-right UCode        UCode UCode comp aU cohu mem = tt
  finMem-Sup-right PropCode     UCode UCode () aU cohu mem
  finMem-Sup-right (FunEl g)    UCode UCode comp () cohu mem
  finMem-Sup-right (PiCode d k) UCode UCode () aU cohu mem
  finMem-Sup-right (SigmaCode d k) UCode UCode () aU cohu mem
  finMem-Sup-right (PairCode u2 v2) UCode UCode () aU cohu mem
  finMem-Sup-right a Bot          UCode comp aU cohu ()
  finMem-Sup-right a PropCode     UCode comp aU cohu ()
  finMem-Sup-right a (FunEl h)    UCode comp aU cohu ()
  finMem-Sup-right a (PiCode c h) UCode comp aU cohu ()
  finMem-Sup-right a (SigmaCode c h) UCode comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) UCode comp aU cohu ()

  -- u = PropCode
  finMem-Sup-right Bot          UCode PropCode comp aU cohu mem = tt
  finMem-Sup-right UCode        UCode PropCode comp aU cohu mem = tt
  finMem-Sup-right PropCode     UCode PropCode () aU cohu mem
  finMem-Sup-right (FunEl g)    UCode PropCode comp () cohu mem
  finMem-Sup-right (PiCode d k) UCode PropCode () aU cohu mem
  finMem-Sup-right (SigmaCode d k) UCode PropCode () aU cohu mem
  finMem-Sup-right (PairCode u2 v2) UCode PropCode () aU cohu mem
  finMem-Sup-right a Bot          PropCode comp aU cohu ()
  finMem-Sup-right a PropCode     PropCode comp aU cohu ()
  finMem-Sup-right a (FunEl h)    PropCode comp aU cohu ()
  finMem-Sup-right a (PiCode c h) PropCode comp aU cohu ()
  finMem-Sup-right a (SigmaCode c h) PropCode comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) PropCode comp aU cohu ()

  -- u = PiCode: target b must be UCode or PropCode
  finMem-Sup-right a UCode (PiCode b' h') comp aU cohu mem =
    finMem-Sup-right-PiCode a UCode b' h' comp aU mem
  finMem-Sup-right a PropCode (PiCode b' h') comp aU cohu mem =
    finMem-Sup-right-PiCode a PropCode b' h' comp aU mem
  finMem-Sup-right a Bot          (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (FunEl g)    (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (PiCode c h) (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (SigmaCode c h) (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) (PiCode b' h') comp aU cohu ()

  -- u = SigmaCode: target b must be UCode
  finMem-Sup-right a UCode (SigmaCode b' h') comp aU cohu mem =
    finMem-Sup-right-SigmaCode a UCode b' h' comp aU mem
  finMem-Sup-right a Bot          (SigmaCode b' h') comp aU cohu ()
  finMem-Sup-right a PropCode     (SigmaCode b' h') comp aU cohu ()
  finMem-Sup-right a (FunEl g)    (SigmaCode b' h') comp aU cohu ()
  finMem-Sup-right a (PiCode c h) (SigmaCode b' h') comp aU cohu ()
  finMem-Sup-right a (SigmaCode c h) (SigmaCode b' h') comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) (SigmaCode b' h') comp aU cohu ()

  -- u = FunEl: target b must be PiCode
  finMem-Sup-right a (PiCode c h) (FunEl g) comp aU cohu mem =
    finMem-Sup-right-FunEl a c h g comp aU cohu mem
  finMem-Sup-right a Bot       (FunEl g) comp aU cohu ()
  finMem-Sup-right a UCode     (FunEl g) comp aU cohu ()
  finMem-Sup-right a PropCode  (FunEl g) comp aU cohu ()
  finMem-Sup-right a (FunEl h) (FunEl g) comp aU cohu ()
  finMem-Sup-right a (SigmaCode c h) (FunEl g) comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) (FunEl g) comp aU cohu ()

  -- u = PairCode: target b must be SigmaCode
  finMem-Sup-right a (SigmaCode c h) (PairCode u' v') comp aU cohu mem =
    finMem-Sup-right-PairCode a c h u' v' comp aU cohu mem
  finMem-Sup-right a Bot       (PairCode u' v') comp aU cohu ()
  finMem-Sup-right a UCode     (PairCode u' v') comp aU cohu ()
  finMem-Sup-right a PropCode  (PairCode u' v') comp aU cohu ()
  finMem-Sup-right a (FunEl h) (PairCode u' v') comp aU cohu ()
  finMem-Sup-right a (PiCode c h) (PairCode u' v') comp aU cohu ()
  finMem-Sup-right a (PairCode u2 v2) (PairCode u' v') comp aU cohu ()

  -- Helper: PiCode case
  finMem-Sup-right-PiCode : (a b : FinEl) (b' : FinEl) (h' : FinFun) ->
    Comp a b -> FinMem a UCode ->
    FinMem (PiCode b' h') b -> FinMem (PiCode b' h') (Sup a b)
  finMem-Sup-right-PiCode Bot   UCode b' h' comp aU mem = mem
  finMem-Sup-right-PiCode UCode UCode b' h' comp aU mem = mem
  finMem-Sup-right-PiCode PropCode UCode b' h' () aU mem
  finMem-Sup-right-PiCode (FunEl g) UCode b' h' comp () mem
  finMem-Sup-right-PiCode (PiCode d k) UCode b' h' () aU mem
  finMem-Sup-right-PiCode (SigmaCode d k) UCode b' h' () aU mem
  finMem-Sup-right-PiCode (PairCode u v) UCode b' h' () aU mem
  finMem-Sup-right-PiCode Bot   PropCode b' h' comp aU mem = mem
  finMem-Sup-right-PiCode UCode PropCode b' h' () aU mem
  finMem-Sup-right-PiCode PropCode PropCode b' h' comp aU mem = mem
  finMem-Sup-right-PiCode (FunEl g) PropCode b' h' comp () mem
  finMem-Sup-right-PiCode (PiCode d k) PropCode b' h' () aU mem
  finMem-Sup-right-PiCode (SigmaCode d k) PropCode b' h' () aU mem
  finMem-Sup-right-PiCode (PairCode u v) PropCode b' h' () aU mem

  -- Helper: SigmaCode case (mirrors PiCode)
  finMem-Sup-right-SigmaCode : (a b : FinEl) (b' : FinEl) (h' : FinFun) ->
    Comp a b -> FinMem a UCode ->
    FinMem (SigmaCode b' h') b -> FinMem (SigmaCode b' h') (Sup a b)
  finMem-Sup-right-SigmaCode Bot   UCode b' h' comp aU mem = mem
  finMem-Sup-right-SigmaCode UCode UCode b' h' comp aU mem = mem
  finMem-Sup-right-SigmaCode PropCode UCode b' h' () aU mem
  finMem-Sup-right-SigmaCode (FunEl g) UCode b' h' comp () mem
  finMem-Sup-right-SigmaCode (PiCode d k) UCode b' h' () aU mem
  finMem-Sup-right-SigmaCode (SigmaCode d k) UCode b' h' () aU mem
  finMem-Sup-right-SigmaCode (PairCode u v) UCode b' h' () aU mem

  -- Helper: FunEl case (u = FunEl g, b = PiCode c h)
  finMem-Sup-right-FunEl : (a : FinEl) (c : FinEl) (h : FinFun) (g : FinFun) ->
    Comp a (PiCode c h) -> FinMem a UCode -> Coherent (FunEl g) ->
    FinMem (FunEl g) (PiCode c h) -> FinMem (FunEl g) (Sup a (PiCode c h))
  finMem-Sup-right-FunEl Bot c h g comp aU cohg mem = mem
  finMem-Sup-right-FunEl UCode c h g () aU cohg mem
  finMem-Sup-right-FunEl PropCode c h g () aU cohg mem
  finMem-Sup-right-FunEl (FunEl j) c h g comp () cohg mem
  finMem-Sup-right-FunEl (SigmaCode d k) c h g () aU cohg mem
  finMem-Sup-right-FunEl (PairCode u v) c h g () aU cohg mem
  finMem-Sup-right-FunEl (PiCode d k) c h g comp aU cohg mem =
    let piU = snd (snd mem)
        dU = fst aU
        allUk = fst (snd aU)
        cohk = snd (snd aU)
        cU = fst piU
        allUh = fst (snd piU)
        cohh = snd (snd piU)
        cohd = coh-from-aU d dU
        cohc = coh-from-aU c cU
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
    in mkSigma (finMemFun-Sup-right d c k h g (fst comp) (snd comp) dU allUk cohk (cft-from-cf g cohg) (fst mem))
               (mkSigma (fst (snd mem)) (mkSigma supU (mkSigma allUkh cohkh)))

  -- Helper: PairCode case (u = PairCode u' v', b = SigmaCode c h)
  finMem-Sup-right-PairCode : (a : FinEl) (c : FinEl) (h : FinFun)
    (u' v' : FinEl) ->
    Comp a (SigmaCode c h) -> FinMem a UCode -> Coherent (PairCode u' v') ->
    FinMem (PairCode u' v') (SigmaCode c h) ->
    FinMem (PairCode u' v') (Sup a (SigmaCode c h))
  finMem-Sup-right-PairCode Bot c h u' v' comp aU cohp mem = mem
  finMem-Sup-right-PairCode UCode c h u' v' () aU cohp mem
  finMem-Sup-right-PairCode PropCode c h u' v' () aU cohp mem
  finMem-Sup-right-PairCode (FunEl j) c h u' v' () aU cohp mem
  finMem-Sup-right-PairCode (PiCode d k) c h u' v' () aU cohp mem
  finMem-Sup-right-PairCode (PairCode u2 v2) c h u' v' () aU cohp mem
  finMem-Sup-right-PairCode (SigmaCode d k) c h u' v' comp aU cohp mem =
    let sigU = snd (snd mem)
        dU = fst aU
        allUk = fst (snd aU)
        cohk = snd (snd aU)
        cU = fst sigU
        allUh = fst (snd sigU)
        cohh = snd (snd sigU)
        cohd = coh-from-aU d dU
        cohc = coh-from-aU c cU
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
        -- key mem: FinMem u' c and FinMem v' (EvalFun h u')
        key-mem = fst (fst mem)
        val-mem = snd (fst mem)
        -- need: FinMem u' (Sup d c)
        key-mem' = finMem-Sup-right d c u' (fst comp) dU (fst (fst cohp)) key-mem
        -- need: FinMem v' (EvalFun (append k h) u')
        val-mem' = finMem-EvalFun-append d k h u' v' (snd comp) cohk (fst (fst cohp)) (snd (fst cohp)) allUk val-mem
    in mkSigma (mkSigma key-mem' val-mem')
               (mkSigma (fst (snd mem)) (mkSigma supU (mkSigma allUkh cohkh)))

  -- finMemFun-Sup-right (unchanged — operates on FinFun)
  finMemFun-Sup-right : (d c : FinEl) (k h : FinFun) (g : FinFun) ->
    Comp d c -> CompFun k h -> FinMem d UCode -> FinMemAllU k d -> CoherentFunTail k ->
    CoherentFunTail g ->
    FinMemFun g c h -> FinMemFun g (Sup d c) (append k h)
  finMemFun-Sup-right d c k h nil cd ckh dU allUk cohk cohg mem = tt
  finMemFun-Sup-right d c k h (cons p ps) cd ckh dU allUk cohk cohg mem =
    let key-mem = finMem-Sup-right d c (fst p) cd dU (CFTcons.key-coh cohg) (fst (fst mem))
        val-mem = finMem-EvalFun-append d k h (fst p) (snd p) ckh cohk (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) allUk (snd (fst mem))
        tail-mem = finMemFun-Sup-right d c k h ps cd ckh dU allUk cohk (CFTcons.tail-coh cohg) (snd mem)
    in mkSigma (mkSigma key-mem val-mem) tail-mem

  -- finMem-EvalFun-append (unchanged)
  finMem-EvalFun-append : (d : FinEl) (k h : FinFun) (xi yi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi -> Coherent yi ->
    FinMemAllU k d ->
    FinMem yi (EvalFun h xi) -> FinMem yi (EvalFun (append k h) xi)
  finMem-EvalFun-append d nil h xi yi ckh cohk cxi cohyi allU mem = mem
  finMem-EvalFun-append d (cons q qs) h xi yi ckh cohk cxi cohyi allU mem =
    let ih = finMem-EvalFun-append d qs h xi yi (snd ckh) (CFTcons.tail-coh cohk) cxi cohyi (snd allU) mem
        csf = compStepFun-append q qs h
                (coherentWith-to-compStepFun q qs (CFTcons.compat cohk))
                (fst ckh)
        cw  = coherentWith-append q qs h
                (CFTcons.compat cohk)
                (compStepFun-to-coherentWith q h (fst ckh))
        vU  = snd (fst allU)
    in finMem-EvalFun-prepend (leFinEl (fst q) xi) q (append qs h) xi yi
         refl cxi (CFTcons.val-coh cohk) vU cw csf cohyi ih

  finMem-EvalFun-prepend : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (xi yi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    Coherent xi -> Coherent (snd q) -> FinMem (snd q) UCode ->
    CoherentWith q rest -> CompStepFun q rest ->
    Coherent yi ->
    FinMem yi (EvalFun rest xi) ->
    FinMem yi (EvalFun-step n (snd q) rest xi)
  finMem-EvalFun-prepend zero q rest xi yi eq cxi cohv vU cw csf cohyi ih = ih
  finMem-EvalFun-prepend (suc _) q rest xi yi eq cxi cohv vU cw csf cohyi ih =
    finMem-Sup-right (snd q) (EvalFun rest xi) yi
      (Comp-value-EvalFun q rest xi
        (leFinEl-sound (fst q) xi (Eq-transport isPos eq tt))
        cxi cohv cw csf)
      vU cohyi ih

  -- finMem-Sup-left (symmetric version)
  finMem-Sup-left : (a b u : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    FinMem b UCode -> Coherent u -> FinMem u a -> FinMem u (Sup a b)

  finMem-Sup-left a b Bot comp coha cohb bU cohu mem = finMemUCode-Sup a b comp mem bU

  -- u = UCode
  finMem-Sup-left Bot          b UCode comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          UCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        UCode        UCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        PropCode     UCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (FunEl h)    UCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) UCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (SigmaCode c h) UCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PairCode u2 v2) UCode () coha cohb bU cohu mem
  finMem-Sup-left PropCode     b UCode comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl g)    b UCode comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b UCode comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode a f) b UCode comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b UCode comp coha cohb bU cohu ()

  -- u = PropCode
  finMem-Sup-left Bot          b PropCode comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          PropCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        UCode        PropCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        PropCode     PropCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (FunEl h)    PropCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) PropCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (SigmaCode c h) PropCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PairCode u2 v2) PropCode () coha cohb bU cohu mem
  finMem-Sup-left PropCode     b PropCode comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl g)    b PropCode comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b PropCode comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode a f) b PropCode comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b PropCode comp coha cohb bU cohu ()

  -- u = PiCode: a must be UCode or PropCode (FinMem (PiCode ..) a non-empty)
  finMem-Sup-left Bot          b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        UCode        (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        PropCode     (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (FunEl h)    (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (SigmaCode c h) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PairCode u2 v2) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     Bot          (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left PropCode     UCode        (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     PropCode     (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left PropCode     (FunEl h)    (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     (PiCode c h) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     (SigmaCode c h) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     (PairCode u2 v2) (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left (FunEl g)    b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode a f) b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b (PiCode b' h') comp coha cohb bU cohu ()

  -- u = SigmaCode: a must be UCode
  finMem-Sup-left Bot          b (SigmaCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          (SigmaCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        UCode        (SigmaCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        PropCode     (SigmaCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (FunEl h)    (SigmaCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) (SigmaCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (SigmaCode c h) (SigmaCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PairCode u2 v2) (SigmaCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left PropCode     b (SigmaCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl g)    b (SigmaCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b (SigmaCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode a f) b (SigmaCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b (SigmaCode b' h') comp coha cohb bU cohu ()

  -- u = FunEl
  finMem-Sup-left Bot          b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left UCode        b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left PropCode     b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl j)    b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode a f) b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode d k) Bot          (FunEl g) comp coha cohb bU cohu mem = mem
  finMem-Sup-left (PiCode d k) UCode        (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) PropCode     (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (FunEl h)    (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (SigmaCode c h) (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (PairCode u2 v2) (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (PiCode c h) (FunEl g) comp coha cohb bU cohu mem =
    let cohd = fst coha
        cohc = fst cohb
        dkU = snd (snd mem)
        dU = fst dkU
        allUk = fst (snd dkU)
        cU = fst bU
        allUh = fst (snd bU)
        cohk = snd coha
        cohh = snd cohb
        cohg = cft-from-cf g (fst (snd mem))
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
    in mkSigma (finMemFun-Sup-left d c k h g (fst comp) (snd comp) cohd cohc cU allUh cohk cohh cohg (fst mem))
               (mkSigma (fst (snd mem)) (mkSigma supU (mkSigma allUkh cohkh)))

  -- u = PairCode: a must be SigmaCode
  finMem-Sup-left Bot          b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left UCode        b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left PropCode     b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl j)    b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left (PairCode u2 v2) b (PairCode u' v') comp coha cohb bU cohu ()
  finMem-Sup-left (SigmaCode d k) Bot          (PairCode u' v') comp coha cohb bU cohu mem = mem
  finMem-Sup-left (SigmaCode d k) UCode        (PairCode u' v') () coha cohb bU cohu mem
  finMem-Sup-left (SigmaCode d k) PropCode     (PairCode u' v') () coha cohb bU cohu mem
  finMem-Sup-left (SigmaCode d k) (FunEl h)    (PairCode u' v') () coha cohb bU cohu mem
  finMem-Sup-left (SigmaCode d k) (PiCode c h) (PairCode u' v') () coha cohb bU cohu mem
  finMem-Sup-left (SigmaCode d k) (PairCode u2 v2) (PairCode u' v') () coha cohb bU cohu mem
  finMem-Sup-left (SigmaCode d k) (SigmaCode c h) (PairCode u' v') comp coha cohb bU cohu mem =
    let cohd = fst coha
        cohc = fst cohb
        sigdkU = snd (snd mem)
        dU = fst sigdkU
        allUk = fst (snd sigdkU)
        cU = fst bU
        allUh = fst (snd bU)
        cohk = snd coha
        cohh = snd cohb
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
        -- transport key and val membership
        key-mem = fst (fst mem)
        val-mem = snd (fst mem)
        cohp = fst (snd mem)
        key-mem' = finMem-Sup-left d c u' (fst comp) cohd cohc cU
                     (fst (fst cohp)) key-mem
        eval-eq = EvalFun-append-eq k h u' (snd comp) cohk (fst (fst cohp))
        comp-eval = comp-EvalFun k h u' (snd comp) cohk (fst (fst cohp))
        coh-eval-k = Coherent-EvalFun k u' cohk (fst (fst cohp))
        coh-eval-h = Coherent-EvalFun h u' cohh (fst (fst cohp))
        evalh-U = EvalFun-in-UCode h u' c cohh (fst (fst cohp)) allUh
        val-left = finMem-Sup-left (EvalFun k u') (EvalFun h u') v'
                     comp-eval coh-eval-k coh-eval-h evalh-U
                     (snd (fst cohp)) val-mem
        val-mem' = Eq-transport (FinMem v') (Eq-sym eval-eq) val-left
    in mkSigma (mkSigma key-mem' val-mem')
               (mkSigma cohp (mkSigma supU (mkSigma allUkh cohkh)))

  -- finMemFun-Sup-left (unchanged — operates on FinFun)
  finMemFun-Sup-left : (d c : FinEl) (k h : FinFun) (g : FinFun) ->
    Comp d c -> CompFun k h ->
    Coherent d -> Coherent c -> FinMem c UCode -> FinMemAllU h c ->
    CoherentFunTail k -> CoherentFunTail h ->
    CoherentFunTail g ->
    FinMemFun g d k -> FinMemFun g (Sup d c) (append k h)
  finMemFun-Sup-left d c k h nil cd ckh cohd cohc cU allUh cohk cohh cohg mem = tt
  finMemFun-Sup-left d c k h (cons p ps) cd ckh cohd cohc cU allUh cohk cohh cohg mem =
    let key-mem = finMem-Sup-left d c (fst p) cd cohd cohc cU
                    (CFTcons.key-coh cohg) (fst (fst mem))
        eval-eq = EvalFun-append-eq k h (fst p) ckh cohk (CFTcons.key-coh cohg)
        comp-eval = comp-EvalFun k h (fst p) ckh cohk (CFTcons.key-coh cohg)
        coh-eval-k = Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg)
        coh-eval-h = Coherent-EvalFun h (fst p) cohh (CFTcons.key-coh cohg)
        evalh-U = EvalFun-in-UCode h (fst p) c cohh (CFTcons.key-coh cohg) allUh
        val-left = finMem-Sup-left (EvalFun k (fst p)) (EvalFun h (fst p)) (snd p)
                     comp-eval coh-eval-k coh-eval-h evalh-U
                     (CFTcons.val-coh cohg) (snd (fst mem))
        val-mem = Eq-transport (FinMem (snd p)) (Eq-sym eval-eq) val-left
        tail-mem = finMemFun-Sup-left d c k h ps cd ckh cohd cohc cU allUh cohk cohh
                     (CFTcons.tail-coh cohg) (snd mem)
    in mkSigma (mkSigma key-mem val-mem) tail-mem

------------------------------------------------------------------------
-- Part 7i: LeCode-refl, LeCode-trans, LeCode-Sup-left/right/lub,
--          EvalFun-mon, EvalFun-mon-arg
------------------------------------------------------------------------

Coherent-keys : FinFun -> Set
Coherent-keys nil         = Top
Coherent-keys (cons p ps) = Pair (Coherent (fst p)) (Coherent-keys ps)

CoherentFun-keys : (g : FinFun) -> CoherentFunTail g -> Coherent-keys g
CoherentFun-keys nil         coh = tt
CoherentFun-keys (cons p ps) coh =
  mkSigma (CFTcons.key-coh coh) (CoherentFun-keys ps (CFTcons.tail-coh coh))

{-# TERMINATING #-}
mutual
  LeCode-refl : (a : FinEl) -> Coherent a -> LeCode a a
  LeCode-refl Bot ca = tt
  LeCode-refl UCode ca = tt
  LeCode-refl PropCode ca = tt
  LeCode-refl (FunEl g) ca = LeFunCode-refl g (cft-from-cf g ca)
  LeCode-refl (PiCode a f) ca =
    mkSigma (LeCode-refl a (fst ca)) (LeFunCode-refl f (snd ca))
  LeCode-refl (SigmaCode a f) ca =
    mkSigma (LeCode-refl a (fst ca)) (LeFunCode-refl f (snd ca))
  LeCode-refl (PairCode u v) ca =
    mkSigma (LeCode-refl u (fst (fst ca))) (LeCode-refl v (snd (fst ca)))

  LeFunCode-refl : (g : FinFun) -> CoherentFunTail g -> LeFunCode g g
  LeFunCode-refl nil coh = tt
  LeFunCode-refl (cons p ps) coh =
    mkSigma
      (LeFunCode-refl-head-step (leFinEl (fst p) (fst p)) p ps refl coh)
      (LeFunCode-cons-lift ps p ps coh (CFTcons.tail-coh coh)
        (LeFunCode-refl ps (CFTcons.tail-coh coh)))

  LeFunCode-refl-head-step : (n : Nat) (p : Pair FinEl FinEl) (ps : FinFun) ->
    Eq n (leFinEl (fst p) (fst p)) ->
    CoherentFunTail (cons p ps) ->
    LeCode (snd p) (EvalFun-step n (snd p) ps (fst p))
  LeFunCode-refl-head-step zero p ps eq coh
    with Eq-transport isPos (Eq-sym eq)
           (leFinEl-complete (fst p) (fst p)
             (LeCode-refl (fst p) (CFTcons.key-coh coh)))
  ... | ()
  LeFunCode-refl-head-step (suc _) p ps eq coh =
    LeCode-Sup-left (snd p) (EvalFun ps (fst p))
      (Comp-value-EvalFun p ps (fst p)
        (LeCode-refl (fst p) (CFTcons.key-coh coh)) (CFTcons.key-coh coh)
        (CFTcons.val-coh coh)
        (CFTcons.compat coh) (coherentWith-to-compStepFun p ps (CFTcons.compat coh)))
      (CFTcons.val-coh coh)
      (Coherent-EvalFun ps (fst p) (CFTcons.tail-coh coh) (CFTcons.key-coh coh))

  LeFunCode-cons-lift : (g : FinFun) (p : Pair FinEl FinEl) (rest : FinFun) ->
    CoherentFunTail (cons p rest) -> CoherentFunTail g ->
    LeFunCode g rest -> LeFunCode g (cons p rest)
  LeFunCode-cons-lift nil p rest coh cohg le = tt
  LeFunCode-cons-lift (cons q qs) p rest coh cohg le =
    mkSigma
      (LeCode-trans (snd q) (EvalFun rest (fst q)) (EvalFun (cons p rest) (fst q))
        (CFTcons.val-coh cohg)
        (Coherent-EvalFun rest (fst q) (CFTcons.tail-coh coh) (CFTcons.key-coh cohg))
        (Coherent-EvalFun (cons p rest) (fst q) coh (CFTcons.key-coh cohg))
        (fst le)
        (EvalFun-cons-mono p rest (fst q) coh (CFTcons.key-coh cohg)))
      (LeFunCode-cons-lift qs p rest coh (CFTcons.tail-coh cohg) (snd le))

  EvalFun-cons-mono : (q : Pair FinEl FinEl) (rest : FinFun) (u : FinEl) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    LeCode (EvalFun rest u) (EvalFun (cons q rest) u)
  EvalFun-cons-mono q rest u coh cu =
    EvalFun-cons-mono-step (leFinEl (fst q) u) q rest u refl coh cu

  EvalFun-cons-mono-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    LeCode (EvalFun rest u) (EvalFun-step n (snd q) rest u)
  EvalFun-cons-mono-step zero q rest u eq coh cu =
    LeCode-refl (EvalFun rest u) (Coherent-EvalFun rest u (CFTcons.tail-coh coh) cu)
  EvalFun-cons-mono-step (suc _) q rest u eq coh cu =
    let le-key = leFinEl-sound (fst q) u (Eq-transport isPos eq tt)
        cohv = CFTcons.val-coh coh
        cw = CFTcons.compat coh
        cohrest = CFTcons.tail-coh coh
        comp = Comp-value-EvalFun q rest u le-key cu cohv
                 cw (coherentWith-to-compStepFun q rest cw)
    in LeCode-Sup-right (snd q) (EvalFun rest u) comp
         cohv (Coherent-EvalFun rest u cohrest cu)

  LeCode-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode a (Sup a b)
  LeCode-Sup-left Bot b comp ca cb = tt
  LeCode-Sup-left UCode Bot comp ca cb = tt
  LeCode-Sup-left UCode UCode comp ca cb = tt
  LeCode-Sup-left UCode PropCode ()
  LeCode-Sup-left UCode (FunEl h) () ca cb
  LeCode-Sup-left UCode (PiCode b h) ()
  LeCode-Sup-left UCode (SigmaCode b h) ()
  LeCode-Sup-left UCode (PairCode u v) ()
  LeCode-Sup-left PropCode Bot comp ca cb = tt
  LeCode-Sup-left PropCode UCode ()
  LeCode-Sup-left PropCode PropCode comp ca cb = tt
  LeCode-Sup-left PropCode (FunEl h) () ca cb
  LeCode-Sup-left PropCode (PiCode b h) ()
  LeCode-Sup-left PropCode (SigmaCode b h) ()
  LeCode-Sup-left PropCode (PairCode u v) ()
  LeCode-Sup-left (FunEl g) Bot comp ca cb = LeCode-refl (FunEl g) ca
  LeCode-Sup-left (FunEl g) UCode () ca cb
  LeCode-Sup-left (FunEl g) PropCode () ca cb
  LeCode-Sup-left (FunEl g) (FunEl h) comp ca cb =
    LeFunCode-append-left g h comp (cft-from-cf g ca) (cft-from-cf h cb)
  LeCode-Sup-left (FunEl g) (PiCode b h) () ca cb
  LeCode-Sup-left (FunEl g) (SigmaCode b h) () ca cb
  LeCode-Sup-left (FunEl g) (PairCode u v) () ca cb
  LeCode-Sup-left (PiCode a f) Bot comp ca cb = LeCode-refl (PiCode a f) ca
  LeCode-Sup-left (PiCode a f) UCode ()
  LeCode-Sup-left (PiCode a f) PropCode ()
  LeCode-Sup-left (PiCode a f) (FunEl h) () ca cb
  LeCode-Sup-left (PiCode a f) (PiCode b h) comp ca cb =
    mkSigma (LeCode-Sup-left a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-left f h (snd comp) (snd ca) (snd cb))
  LeCode-Sup-left (PiCode a f) (SigmaCode b h) () ca cb
  LeCode-Sup-left (PiCode a f) (PairCode u v) () ca cb
  LeCode-Sup-left (SigmaCode a f) Bot comp ca cb = LeCode-refl (SigmaCode a f) ca
  LeCode-Sup-left (SigmaCode a f) UCode ()
  LeCode-Sup-left (SigmaCode a f) PropCode ()
  LeCode-Sup-left (SigmaCode a f) (FunEl h) () ca cb
  LeCode-Sup-left (SigmaCode a f) (PiCode b h) () ca cb
  LeCode-Sup-left (SigmaCode a f) (SigmaCode b h) comp ca cb =
    mkSigma (LeCode-Sup-left a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-left f h (snd comp) (snd ca) (snd cb))
  LeCode-Sup-left (SigmaCode a f) (PairCode u v) () ca cb
  LeCode-Sup-left (PairCode u1 v1) Bot comp ca cb = LeCode-refl (PairCode u1 v1) ca
  LeCode-Sup-left (PairCode u1 v1) UCode () ca cb
  LeCode-Sup-left (PairCode u1 v1) PropCode () ca cb
  LeCode-Sup-left (PairCode u1 v1) (FunEl h) () ca cb
  LeCode-Sup-left (PairCode u1 v1) (PiCode b h) () ca cb
  LeCode-Sup-left (PairCode u1 v1) (SigmaCode b h) () ca cb
  LeCode-Sup-left (PairCode u1 v1) (PairCode u2 v2) comp ca cb =
    mkSigma (LeCode-Sup-left u1 u2 (fst comp) (fst (fst ca)) (fst (fst cb)))
            (LeCode-Sup-left v1 v2 (snd comp) (snd (fst ca)) (snd (fst cb)))

  LeCode-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode b (Sup a b)
  LeCode-Sup-right a Bot comp ca cb = tt
  LeCode-Sup-right Bot UCode comp ca cb = tt
  LeCode-Sup-right UCode UCode comp ca cb = tt
  LeCode-Sup-right PropCode UCode () ca cb
  LeCode-Sup-right (FunEl g) UCode () ca cb
  LeCode-Sup-right (PiCode a f) UCode ()
  LeCode-Sup-right (SigmaCode a f) UCode ()
  LeCode-Sup-right (PairCode u v) UCode ()
  LeCode-Sup-right Bot PropCode comp ca cb = tt
  LeCode-Sup-right UCode PropCode ()
  LeCode-Sup-right PropCode PropCode comp ca cb = tt
  LeCode-Sup-right (FunEl g) PropCode () ca cb
  LeCode-Sup-right (PiCode a f) PropCode ()
  LeCode-Sup-right (SigmaCode a f) PropCode ()
  LeCode-Sup-right (PairCode u v) PropCode ()
  LeCode-Sup-right Bot (FunEl h) comp ca cb = LeCode-refl (FunEl h) cb
  LeCode-Sup-right UCode (FunEl h) () ca cb
  LeCode-Sup-right PropCode (FunEl h) () ca cb
  LeCode-Sup-right (FunEl g) (FunEl h) comp ca cb =
    LeFunCode-append-right g h comp (cft-from-cf g ca) (cft-from-cf h cb)
  LeCode-Sup-right (PiCode a f) (FunEl h) () ca cb
  LeCode-Sup-right (SigmaCode a f) (FunEl h) () ca cb
  LeCode-Sup-right (PairCode u v) (FunEl h) () ca cb
  LeCode-Sup-right Bot (PiCode b h) comp ca cb = LeCode-refl (PiCode b h) cb
  LeCode-Sup-right UCode (PiCode b h) ()
  LeCode-Sup-right PropCode (PiCode b h) ()
  LeCode-Sup-right (FunEl g) (PiCode b h) () ca cb
  LeCode-Sup-right (PiCode a f) (PiCode b h) comp ca cb =
    mkSigma (LeCode-Sup-right a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-right f h (snd comp) (snd ca) (snd cb))
  LeCode-Sup-right (SigmaCode a f) (PiCode b h) () ca cb
  LeCode-Sup-right (PairCode u v) (PiCode b h) () ca cb
  LeCode-Sup-right Bot (SigmaCode b h) comp ca cb = LeCode-refl (SigmaCode b h) cb
  LeCode-Sup-right UCode (SigmaCode b h) ()
  LeCode-Sup-right PropCode (SigmaCode b h) ()
  LeCode-Sup-right (FunEl g) (SigmaCode b h) () ca cb
  LeCode-Sup-right (PiCode a f) (SigmaCode b h) () ca cb
  LeCode-Sup-right (SigmaCode a f) (SigmaCode b h) comp ca cb =
    mkSigma (LeCode-Sup-right a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-right f h (snd comp) (snd ca) (snd cb))
  LeCode-Sup-right (PairCode u v) (SigmaCode b h) () ca cb
  LeCode-Sup-right Bot (PairCode u2 v2) comp ca cb = LeCode-refl (PairCode u2 v2) cb
  LeCode-Sup-right UCode (PairCode u2 v2) ()
  LeCode-Sup-right PropCode (PairCode u2 v2) ()
  LeCode-Sup-right (FunEl g) (PairCode u2 v2) () ca cb
  LeCode-Sup-right (PiCode a f) (PairCode u2 v2) () ca cb
  LeCode-Sup-right (SigmaCode a f) (PairCode u2 v2) () ca cb
  LeCode-Sup-right (PairCode u1 v1) (PairCode u2 v2) comp ca cb =
    mkSigma (LeCode-Sup-right u1 u2 (fst comp) (fst (fst ca)) (fst (fst cb)))
            (LeCode-Sup-right v1 v2 (snd comp) (snd (fst ca)) (snd (fst cb)))

  LeCode-trans : (x y z : FinEl) -> Coherent x -> Coherent y -> Coherent z ->
    LeCode x y -> LeCode y z -> LeCode x z
  LeCode-trans Bot y z cx cy cz xy yz = tt
  LeCode-trans UCode Bot z cx cy cz ()
  LeCode-trans UCode UCode z cx cy cz xy yz = yz
  LeCode-trans UCode PropCode z cx cy cz ()
  LeCode-trans UCode (FunEl h) z cx cy cz ()
  LeCode-trans UCode (PiCode b g) z cx cy cz ()
  LeCode-trans UCode (SigmaCode b g) z cx cy cz ()
  LeCode-trans UCode (PairCode u v) z cx cy cz ()
  LeCode-trans PropCode Bot z cx cy cz ()
  LeCode-trans PropCode UCode z cx cy cz ()
  LeCode-trans PropCode PropCode z cx cy cz xy yz = yz
  LeCode-trans PropCode (FunEl h) z cx cy cz ()
  LeCode-trans PropCode (PiCode b g) z cx cy cz ()
  LeCode-trans PropCode (SigmaCode b g) z cx cy cz ()
  LeCode-trans PropCode (PairCode u v) z cx cy cz ()
  LeCode-trans (FunEl g) Bot z cx cy cz ()
  LeCode-trans (FunEl g) UCode z cx cy cz ()
  LeCode-trans (FunEl g) PropCode z cx cy cz ()
  LeCode-trans (FunEl g) (FunEl h) Bot cx cy cz xy ()
  LeCode-trans (FunEl g) (FunEl h) UCode cx cy cz xy ()
  LeCode-trans (FunEl g) (FunEl h) PropCode cx cy cz xy ()
  LeCode-trans (FunEl g) (FunEl h) (FunEl k) cx cy cz xy yz =
    LeFunCode-trans g h k (cft-from-cf g cx) (cft-from-cf h cy) (cft-from-cf k cz) xy yz
  LeCode-trans (FunEl g) (FunEl h) (PiCode c k) cx cy cz xy ()
  LeCode-trans (FunEl g) (FunEl h) (SigmaCode c k) cx cy cz xy ()
  LeCode-trans (FunEl g) (FunEl h) (PairCode u v) cx cy cz xy ()
  LeCode-trans (FunEl g) (PiCode b h) z cx cy cz ()
  LeCode-trans (FunEl g) (SigmaCode b h) z cx cy cz ()
  LeCode-trans (FunEl g) (PairCode u v) z cx cy cz ()
  LeCode-trans (PiCode a f) Bot z cx cy cz ()
  LeCode-trans (PiCode a f) UCode z cx cy cz ()
  LeCode-trans (PiCode a f) PropCode z cx cy cz ()
  LeCode-trans (PiCode a f) (FunEl h) z cx cy cz ()
  LeCode-trans (PiCode a f) (PiCode b g) Bot cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) UCode cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) PropCode cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) (FunEl k) cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) (PiCode c k) cx cy cz xy yz =
    mkSigma (LeCode-trans a b c (fst cx) (fst cy) (fst cz) (fst xy) (fst yz))
            (LeFunCode-trans f g k (snd cx) (snd cy) (snd cz) (snd xy) (snd yz))
  LeCode-trans (PiCode a f) (PiCode b g) (SigmaCode c k) cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) (PairCode u v) cx cy cz xy ()
  LeCode-trans (PiCode a f) (SigmaCode b g) z cx cy cz ()
  LeCode-trans (PiCode a f) (PairCode u v) z cx cy cz ()
  LeCode-trans (SigmaCode a f) Bot z cx cy cz ()
  LeCode-trans (SigmaCode a f) UCode z cx cy cz ()
  LeCode-trans (SigmaCode a f) PropCode z cx cy cz ()
  LeCode-trans (SigmaCode a f) (FunEl h) z cx cy cz ()
  LeCode-trans (SigmaCode a f) (PiCode b g) z cx cy cz ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) Bot cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) UCode cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) PropCode cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) (FunEl k) cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) (PiCode c k) cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (SigmaCode b g) (SigmaCode c k) cx cy cz xy yz =
    mkSigma (LeCode-trans a b c (fst cx) (fst cy) (fst cz) (fst xy) (fst yz))
            (LeFunCode-trans f g k (snd cx) (snd cy) (snd cz) (snd xy) (snd yz))
  LeCode-trans (SigmaCode a f) (SigmaCode b g) (PairCode u v) cx cy cz xy ()
  LeCode-trans (SigmaCode a f) (PairCode u v) z cx cy cz ()
  LeCode-trans (PairCode u1 v1) Bot z cx cy cz ()
  LeCode-trans (PairCode u1 v1) UCode z cx cy cz ()
  LeCode-trans (PairCode u1 v1) PropCode z cx cy cz ()
  LeCode-trans (PairCode u1 v1) (FunEl h) z cx cy cz ()
  LeCode-trans (PairCode u1 v1) (PiCode b g) z cx cy cz ()
  LeCode-trans (PairCode u1 v1) (SigmaCode b g) z cx cy cz ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) Bot cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) UCode cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) PropCode cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) (FunEl k) cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) (PiCode c k) cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) (SigmaCode c k) cx cy cz xy ()
  LeCode-trans (PairCode u1 v1) (PairCode u2 v2) (PairCode u3 v3) cx cy cz xy yz =
    mkSigma (LeCode-trans u1 u2 u3 (fst (fst cx)) (fst (fst cy)) (fst (fst cz)) (fst xy) (fst yz))
            (LeCode-trans v1 v2 v3 (snd (fst cx)) (snd (fst cy)) (snd (fst cz)) (snd xy) (snd yz))

  LeFunCode-trans : (g h k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CoherentFunTail k ->
    LeFunCode g h -> LeFunCode h k -> LeFunCode g k
  LeFunCode-trans nil h k cohg cohh cohk gh hk = tt
  LeFunCode-trans (cons p ps) h k cohg cohh cohk gh hk =
    mkSigma
      (LeCode-trans (snd p) (EvalFun h (fst p)) (EvalFun k (fst p))
        (CFTcons.val-coh cohg)
        (Coherent-EvalFun h (fst p) cohh (CFTcons.key-coh cohg))
        (Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg))
        (fst gh)
        (EvalFun-mon h k (fst p) cohh cohk (CFTcons.key-coh cohg) hk))
      (LeFunCode-trans ps h k (CFTcons.tail-coh cohg) cohh cohk (snd gh) hk)

  LeFunCode-nil-any : (g k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail k -> LeFunCode g nil -> LeFunCode g k
  LeFunCode-nil-any nil k cohg cohk lg = tt
  LeFunCode-nil-any (cons p ps) k cohg cohk lg =
    mkSigma
      (LeCode-trans (snd p) Bot (EvalFun k (fst p))
        (CFTcons.val-coh cohg) tt
        (Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg))
        (fst lg) tt)
      (LeFunCode-nil-any ps k (CFTcons.tail-coh cohg) cohk (snd lg))

  EvalFun-mon : (h k : FinFun) (u : FinEl) ->
    CoherentFunTail h -> CoherentFunTail k -> Coherent u ->
    LeFunCode h k -> LeCode (EvalFun h u) (EvalFun k u)
  EvalFun-mon nil k u cohh cohk cu hk = tt
  EvalFun-mon (cons q qs) k u cohh cohk cu hk =
    EvalFun-mon-step (leFinEl (fst q) u) q qs k u refl cohh cohk cu hk

  EvalFun-mon-step : (n : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (k : FinFun) (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q qs) -> CoherentFunTail k -> Coherent u ->
    LeFunCode (cons q qs) k ->
    LeCode (EvalFun-step n (snd q) qs u) (EvalFun k u)
  EvalFun-mon-step zero q qs k u eq cohh cohk cu hk =
    EvalFun-mon qs k u (CFTcons.tail-coh cohh) cohk cu (snd hk)
  EvalFun-mon-step (suc _) q qs k u eq cohh cohk cu hk =
    let le-key = leFinEl-sound (fst q) u (Eq-transport isPos eq tt)
    in LeCode-Sup-lub (snd q) (EvalFun qs u) (EvalFun k u)
         (LeCode-trans (snd q) (EvalFun k (fst q)) (EvalFun k u)
           (CFTcons.val-coh cohh)
           (Coherent-EvalFun k (fst q) cohk (CFTcons.key-coh cohh))
           (Coherent-EvalFun k u cohk cu)
           (fst hk)
           (EvalFun-mon-arg k (fst q) u le-key cohk (CFTcons.key-coh cohh) cu))
         (EvalFun-mon qs k u (CFTcons.tail-coh cohh) cohk cu (snd hk))

  LeCode-Sup-lub : (a b c : FinEl) -> LeCode a c -> LeCode b c ->
    LeCode (Sup a b) c
  LeCode-Sup-lub Bot b c ac bc = bc
  LeCode-Sup-lub UCode Bot c ac bc = ac
  LeCode-Sup-lub UCode UCode c ac bc = ac
  LeCode-Sup-lub UCode PropCode c ac bc = tt
  LeCode-Sup-lub UCode (FunEl h) c ac bc = tt
  LeCode-Sup-lub UCode (PiCode b h) c ac bc = tt
  LeCode-Sup-lub UCode (SigmaCode b h) c ac bc = tt
  LeCode-Sup-lub UCode (PairCode u v) c ac bc = tt
  LeCode-Sup-lub PropCode Bot c ac bc = ac
  LeCode-Sup-lub PropCode UCode c ac bc = tt
  LeCode-Sup-lub PropCode PropCode c ac bc = ac
  LeCode-Sup-lub PropCode (FunEl h) c ac bc = tt
  LeCode-Sup-lub PropCode (PiCode b h) c ac bc = tt
  LeCode-Sup-lub PropCode (SigmaCode b h) c ac bc = tt
  LeCode-Sup-lub PropCode (PairCode u v) c ac bc = tt
  LeCode-Sup-lub (FunEl g) Bot c ac bc = ac
  LeCode-Sup-lub (FunEl g) UCode c ac bc = tt
  LeCode-Sup-lub (FunEl g) PropCode c ac bc = tt
  LeCode-Sup-lub (FunEl g) (FunEl h) Bot () bc
  LeCode-Sup-lub (FunEl g) (FunEl h) UCode () bc
  LeCode-Sup-lub (FunEl g) (FunEl h) PropCode () bc
  LeCode-Sup-lub (FunEl g) (FunEl h) (FunEl k) ac bc =
    LeFunCode-append-combine g h k ac bc
  LeCode-Sup-lub (FunEl g) (FunEl h) (PiCode c k) () bc
  LeCode-Sup-lub (FunEl g) (FunEl h) (SigmaCode c k) () bc
  LeCode-Sup-lub (FunEl g) (FunEl h) (PairCode u v) () bc
  LeCode-Sup-lub (FunEl g) (PiCode b h) c ac bc = tt
  LeCode-Sup-lub (FunEl g) (SigmaCode b h) c ac bc = tt
  LeCode-Sup-lub (FunEl g) (PairCode u v) c ac bc = tt
  LeCode-Sup-lub (PiCode a f) Bot c ac bc = ac
  LeCode-Sup-lub (PiCode a f) UCode c ac bc = tt
  LeCode-Sup-lub (PiCode a f) PropCode c ac bc = tt
  LeCode-Sup-lub (PiCode a f) (FunEl h) c ac bc = tt
  LeCode-Sup-lub (PiCode a f) (PiCode b g) Bot ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) UCode ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) PropCode ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (FunEl k) ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (PiCode c k) ac bc =
    mkSigma (LeCode-Sup-lub a b c (fst ac) (fst bc))
            (LeFunCode-append-combine f g k (snd ac) (snd bc))
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (SigmaCode c k) ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (PairCode u v) ac ()
  LeCode-Sup-lub (PiCode a f) (SigmaCode b h) c ac bc = tt
  LeCode-Sup-lub (PiCode a f) (PairCode u v) c ac bc = tt
  LeCode-Sup-lub (SigmaCode a f) Bot c ac bc = ac
  LeCode-Sup-lub (SigmaCode a f) UCode c ac bc = tt
  LeCode-Sup-lub (SigmaCode a f) PropCode c ac bc = tt
  LeCode-Sup-lub (SigmaCode a f) (FunEl h) c ac bc = tt
  LeCode-Sup-lub (SigmaCode a f) (PiCode b h) c ac bc = tt
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) Bot ac ()
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) UCode ac ()
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) PropCode ac ()
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) (FunEl k) ac ()
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) (PiCode c k) ac ()
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) (SigmaCode c k) ac bc =
    mkSigma (LeCode-Sup-lub a b c (fst ac) (fst bc))
            (LeFunCode-append-combine f g k (snd ac) (snd bc))
  LeCode-Sup-lub (SigmaCode a f) (SigmaCode b g) (PairCode u v) ac ()
  LeCode-Sup-lub (SigmaCode a f) (PairCode u v) c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) Bot c ac bc = ac
  LeCode-Sup-lub (PairCode u1 v1) UCode c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) PropCode c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) (FunEl h) c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) (PiCode b h) c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) (SigmaCode b h) c ac bc = tt
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) Bot ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) UCode ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) PropCode ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) (FunEl k) ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) (PiCode c k) ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) (SigmaCode c k) ac ()
  LeCode-Sup-lub (PairCode u1 v1) (PairCode u2 v2) (PairCode u3 v3) ac bc =
    mkSigma (LeCode-Sup-lub u1 u2 u3 (fst ac) (fst bc))
            (LeCode-Sup-lub v1 v2 v3 (snd ac) (snd bc))

  LeFunCode-append-combine : (g h k : FinFun) ->
    LeFunCode g k -> LeFunCode h k -> LeFunCode (append g h) k
  LeFunCode-append-combine nil h k gk hk = hk
  LeFunCode-append-combine (cons p ps) h k gk hk =
    mkSigma (fst gk) (LeFunCode-append-combine ps h k (snd gk) hk)

  LeFunCode-append-left : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode g (append g h)
  LeFunCode-append-left nil h comp cohg cohh = tt
  LeFunCode-append-left (cons p ps) h comp cohg cohh =
    let coh-append = CoherentFunTail-append (cons p ps) h cohg cohh comp
    in mkSigma
      (LeFunCode-refl-head-step
        (leFinEl (fst p) (fst p)) p (append ps h) refl coh-append)
      (LeFunCode-cons-lift ps p (append ps h)
        coh-append (CFTcons.tail-coh cohg)
        (LeFunCode-append-left ps h (snd comp) (CFTcons.tail-coh cohg) cohh))

  LeFunCode-append-right : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode h (append g h)
  LeFunCode-append-right g h comp cohg cohh =
    let coh-append = CoherentFunTail-append g h cohg cohh comp
    in LeFunCode-append-right-go g h h comp coh-append cohh
         (LeFunCode-refl h cohh)

  LeFunCode-append-right-go : (g h rest : FinFun) -> CompFun g h ->
    CoherentFunTail (append g rest) -> CoherentFunTail h ->
    LeFunCode h rest -> LeFunCode h (append g rest)
  LeFunCode-append-right-go nil h rest comp coh cohh le = le
  LeFunCode-append-right-go (cons p ps) h rest comp coh cohh le =
    LeFunCode-cons-lift h p (append ps rest) coh cohh
      (LeFunCode-append-right-go ps h rest (snd comp) (CFTcons.tail-coh coh) cohh le)

  EvalFun-mon-arg : (k : FinFun) (u v : FinEl) ->
    LeCode u v -> CoherentFunTail k -> Coherent u -> Coherent v ->
    LeCode (EvalFun k u) (EvalFun k v)
  EvalFun-mon-arg nil u v le cohk cu cv = tt
  EvalFun-mon-arg (cons q qs) u v le cohk cu cv =
    EvalFun-mon-arg-step (leFinEl (fst q) u) q qs u v refl le cohk cu cv

  EvalFun-mon-arg-step : (n : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (u v : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    LeCode u v -> CoherentFunTail (cons q qs) -> Coherent u -> Coherent v ->
    LeCode (EvalFun-step n (snd q) qs u) (EvalFun (cons q qs) v)
  EvalFun-mon-arg-step zero q qs u v eq le cohk cu cv =
    LeCode-trans (EvalFun qs u) (EvalFun qs v) (EvalFun (cons q qs) v)
      (Coherent-EvalFun qs u (CFTcons.tail-coh cohk) cu)
      (Coherent-EvalFun qs v (CFTcons.tail-coh cohk) cv)
      (Coherent-EvalFun (cons q qs) v cohk cv)
      (EvalFun-mon-arg qs u v le (CFTcons.tail-coh cohk) cu cv)
      (EvalFun-cons-mono q qs v cohk cv)
  EvalFun-mon-arg-step (suc x) q qs u v eq le cohk cu cv =
    EvalFun-mon-arg-suc x (leFinEl (fst q) v) q qs u v eq refl le cohk cu cv

  EvalFun-mon-arg-suc : (x : Nat) (m : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (u v : FinEl) ->
    Eq (suc x) (leFinEl (fst q) u) ->
    Eq m (leFinEl (fst q) v) ->
    LeCode u v -> CoherentFunTail (cons q qs) -> Coherent u -> Coherent v ->
    LeCode (Sup (snd q) (EvalFun qs u)) (EvalFun-step m (snd q) qs v)
  EvalFun-mon-arg-suc x zero q qs u v equ eqv le cohk cu cv
    with Eq-transport isPos (Eq-sym eqv)
           (leFinEl-complete (fst q) v
             (LeCode-trans (fst q) u v
               (CFTcons.key-coh cohk) cu cv
               (leFinEl-sound (fst q) u (Eq-transport isPos equ tt)) le))
  ... | ()
  EvalFun-mon-arg-suc x (suc _) q qs u v equ eqv le cohk cu cv =
    let cohv = CFTcons.val-coh cohk
        cohrest = CFTcons.tail-coh cohk
        cw = CFTcons.compat cohk
        le-key-v = LeCode-trans (fst q) u v
                     (CFTcons.key-coh cohk) cu cv
                     (leFinEl-sound (fst q) u (Eq-transport isPos equ tt)) le
        coh-rest-u = Coherent-EvalFun qs u cohrest cu
        coh-rest-v = Coherent-EvalFun qs v cohrest cv
        comp-v = Comp-value-EvalFun q qs v le-key-v cv cohv
                   cw (coherentWith-to-compStepFun q qs cw)
        ih = EvalFun-mon-arg qs u v le cohrest cu cv
        sup-left = LeCode-Sup-left (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        sup-right = LeCode-Sup-right (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        coh-sup = Coherent-Sup (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        tail-le = LeCode-trans (EvalFun qs u) (EvalFun qs v)
                    (Sup (snd q) (EvalFun qs v))
                    coh-rest-u coh-rest-v coh-sup
                    ih sup-right
    in LeCode-Sup-lub (snd q) (EvalFun qs u) (Sup (snd q) (EvalFun qs v))
         sup-left tail-le

------------------------------------------------------------------------
-- Part 7j: finMem-upward
------------------------------------------------------------------------

finMem-upward : (v a b : FinEl) -> LeCode a b -> Coherent a -> Coherent b ->
  FinMem v a -> FinMem b UCode -> FinMem v b
finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
  LeCode a b -> Coherent a -> Coherent b ->
  CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
  FinMemFun g a f -> FinMem b UCode -> FinMemAllU h b -> FinMemFun g b h

finMem-upward Bot a b le ca cb mem bU = bU
-- UCode
finMem-upward UCode UCode UCode le ca cb mem bU = tt
finMem-upward UCode UCode PropCode ()
finMem-upward UCode UCode Bot ()
finMem-upward UCode UCode (FunEl h) ()
finMem-upward UCode UCode (PiCode c h) ()
finMem-upward UCode UCode (SigmaCode c h) ()
finMem-upward UCode UCode (PairCode u v) ()
finMem-upward UCode PropCode b le ca cb ()
finMem-upward UCode Bot b le ca cb ()
finMem-upward UCode (FunEl g) b le ca cb ()
finMem-upward UCode (PiCode c h) b le ca cb ()
finMem-upward UCode (SigmaCode c h) b le ca cb ()
finMem-upward UCode (PairCode u v) b le ca cb ()
-- PropCode
finMem-upward PropCode UCode UCode le ca cb mem bU = tt
finMem-upward PropCode UCode PropCode ()
finMem-upward PropCode UCode Bot ()
finMem-upward PropCode UCode (FunEl h) ()
finMem-upward PropCode UCode (PiCode c h) ()
finMem-upward PropCode UCode (SigmaCode c h) ()
finMem-upward PropCode UCode (PairCode u v) ()
finMem-upward PropCode PropCode b le ca cb ()
finMem-upward PropCode Bot b le ca cb ()
finMem-upward PropCode (FunEl g) b le ca cb ()
finMem-upward PropCode (PiCode c h) b le ca cb ()
finMem-upward PropCode (SigmaCode c h) b le ca cb ()
finMem-upward PropCode (PairCode u v) b le ca cb ()
-- FunEl
finMem-upward (FunEl g) (PiCode a f) (PiCode b h) le ca cb mem bU =
  mkSigma
    (finMemFun-upward g a b f h (fst le) (fst ca) (coh-from-aU b (fst bU))
      (snd ca) (snd (snd bU)) (snd le) (fst mem) (fst bU) (fst (snd bU)))
    (mkSigma (fst (snd mem)) bU)
finMem-upward (FunEl g) (PiCode a f) Bot ()
finMem-upward (FunEl g) (PiCode a f) UCode ()
finMem-upward (FunEl g) (PiCode a f) PropCode ()
finMem-upward (FunEl g) (PiCode a f) (FunEl h) ()
finMem-upward (FunEl g) (PiCode a f) (SigmaCode c h) ()
finMem-upward (FunEl g) (PiCode a f) (PairCode u v) ()
finMem-upward (FunEl g) Bot b le ca cb ()
finMem-upward (FunEl g) UCode b le ca cb ()
finMem-upward (FunEl g) PropCode b le ca cb ()
finMem-upward (FunEl g) (FunEl h) b le ca cb ()
finMem-upward (FunEl g) (SigmaCode c h) b le ca cb ()
finMem-upward (FunEl g) (PairCode u v) b le ca cb ()
-- PiCode
finMem-upward (PiCode a f) UCode UCode le ca cb mem bU = mem
finMem-upward (PiCode a f) UCode PropCode ()
finMem-upward (PiCode a f) UCode Bot ()
finMem-upward (PiCode a f) UCode (FunEl h) ()
finMem-upward (PiCode a f) UCode (PiCode c h) ()
finMem-upward (PiCode a f) UCode (SigmaCode c h) ()
finMem-upward (PiCode a f) UCode (PairCode u v) ()
finMem-upward (PiCode a f) PropCode PropCode le ca cb mem bU = mem
finMem-upward (PiCode a f) PropCode UCode ()
finMem-upward (PiCode a f) PropCode Bot ()
finMem-upward (PiCode a f) PropCode (FunEl h) ()
finMem-upward (PiCode a f) PropCode (PiCode c h) ()
finMem-upward (PiCode a f) PropCode (SigmaCode c h) ()
finMem-upward (PiCode a f) PropCode (PairCode u v) ()
finMem-upward (PiCode a f) Bot b le ca cb ()
finMem-upward (PiCode a f) (FunEl g) b le ca cb ()
finMem-upward (PiCode a f) (PiCode c h) b le ca cb ()
finMem-upward (PiCode a f) (SigmaCode c h) b le ca cb ()
finMem-upward (PiCode a f) (PairCode u v) b le ca cb ()
-- SigmaCode
finMem-upward (SigmaCode a f) UCode UCode le ca cb mem bU = mem
finMem-upward (SigmaCode a f) UCode PropCode ()
finMem-upward (SigmaCode a f) UCode Bot ()
finMem-upward (SigmaCode a f) UCode (FunEl h) ()
finMem-upward (SigmaCode a f) UCode (PiCode c h) ()
finMem-upward (SigmaCode a f) UCode (SigmaCode c h) ()
finMem-upward (SigmaCode a f) UCode (PairCode u v) ()
finMem-upward (SigmaCode a f) Bot b le ca cb ()
finMem-upward (SigmaCode a f) PropCode b le ca cb ()
finMem-upward (SigmaCode a f) (FunEl g) b le ca cb ()
finMem-upward (SigmaCode a f) (PiCode c h) b le ca cb ()
finMem-upward (SigmaCode a f) (SigmaCode c h) b le ca cb ()
finMem-upward (SigmaCode a f) (PairCode u v) b le ca cb ()
-- PairCode
finMem-upward (PairCode u v) (SigmaCode a f) (SigmaCode b h) le ca cb mem bU =
  let le-fh = EvalFun-mon f h u (snd ca) (snd (snd bU)) (fst (fst (fst (snd mem)))) (snd le)
      c-ef = Coherent-EvalFun f u (snd ca) (fst (fst (fst (snd mem))))
      c-eh = Coherent-EvalFun h u (snd (snd bU)) (fst (fst (fst (snd mem))))
      efhU = EvalFun-in-UCode h u b (snd (snd bU)) (fst (fst (fst (snd mem)))) (fst (snd bU))
  in mkSigma
    (mkSigma
      (finMem-upward u a b (fst le) (fst ca) (coh-from-aU b (fst bU)) (fst (fst mem)) (fst bU))
      (finMem-upward v (EvalFun f u) (EvalFun h u) le-fh c-ef c-eh (snd (fst mem)) efhU))
    (mkSigma (fst (snd mem)) bU)
finMem-upward (PairCode u v) (SigmaCode a f) Bot ()
finMem-upward (PairCode u v) (SigmaCode a f) UCode ()
finMem-upward (PairCode u v) (SigmaCode a f) PropCode ()
finMem-upward (PairCode u v) (SigmaCode a f) (FunEl h) ()
finMem-upward (PairCode u v) (SigmaCode a f) (PiCode c h) ()
finMem-upward (PairCode u v) (SigmaCode a f) (PairCode u2 v2) ()
finMem-upward (PairCode u v) Bot b le ca cb ()
finMem-upward (PairCode u v) UCode b le ca cb ()
finMem-upward (PairCode u v) PropCode b le ca cb ()
finMem-upward (PairCode u v) (FunEl g) b le ca cb ()
finMem-upward (PairCode u v) (PiCode c h) b le ca cb ()
finMem-upward (PairCode u v) (PairCode u2 v2) b le ca cb ()

finMemFun-upward nil a b f h le-a ca cb cf ch lfh mem bU allUh = tt
finMemFun-upward (cons p ps) a b f h le-a ca cb cf ch lfh mem bU allUh =
  let cp = FinMem-coh-u (fst p) a (fst (fst mem))
      le-fh = EvalFun-mon f h (fst p) cf ch cp lfh
      c-ef = Coherent-EvalFun f (fst p) cf cp
      c-eh = Coherent-EvalFun h (fst p) ch cp
      efhU = EvalFun-in-UCode h (fst p) b ch cp allUh
  in mkSigma
    (mkSigma
      (finMem-upward (fst p) a b le-a ca cb (fst (fst mem)) bU)
      (finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun h (fst p))
        le-fh c-ef c-eh (snd (fst mem)) efhU))
    (finMemFun-upward ps a b f h le-a ca cb cf ch lfh (snd mem) bU allUh)

------------------------------------------------------------------------
-- Part 7k: FinMem-Sup-element
------------------------------------------------------------------------

FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  FinMemFun g b f -> FinMemFun h b f -> FinMemFun (append g h) b f
FinMemFun-append nil h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh =
  mkSigma (fst mg) (FinMemFun-append ps h b f (snd mg) mh)

FinMem-Sup-element : (u v a : FinEl) -> Comp u v -> Coherent a ->
  FinMem u a -> FinMem v a -> FinMem (Sup u v) a
FinMem-Sup-element Bot v a comp ca mu mv = mv
FinMem-Sup-element UCode Bot a comp ca mu mv = mu
FinMem-Sup-element PropCode Bot a comp ca mu mv = mu
FinMem-Sup-element (FunEl g) Bot a comp ca mu mv = mu
FinMem-Sup-element (PiCode a1 f1) Bot a comp ca mu mv = mu
FinMem-Sup-element (SigmaCode a1 f1) Bot a comp ca mu mv = mu
FinMem-Sup-element (PairCode u1 v1) Bot a comp ca mu mv = mu
-- UCode × UCode
FinMem-Sup-element UCode UCode UCode comp ca mu mv = tt
FinMem-Sup-element UCode UCode PropCode comp ca () mv
FinMem-Sup-element UCode UCode Bot comp ca () mv
FinMem-Sup-element UCode UCode (FunEl h) comp ca () mv
FinMem-Sup-element UCode UCode (PiCode b f) comp ca () mv
FinMem-Sup-element UCode UCode (SigmaCode b f) comp ca () mv
FinMem-Sup-element UCode UCode (PairCode u v) comp ca () mv
FinMem-Sup-element UCode PropCode a () ca mu mv
FinMem-Sup-element UCode (FunEl h) a () ca mu mv
FinMem-Sup-element UCode (PiCode b f) a () ca mu mv
FinMem-Sup-element UCode (SigmaCode b f) a () ca mu mv
FinMem-Sup-element UCode (PairCode u v) a () ca mu mv
-- PropCode × PropCode
FinMem-Sup-element PropCode PropCode UCode comp ca mu mv = tt
FinMem-Sup-element PropCode PropCode PropCode comp ca () mv
FinMem-Sup-element PropCode PropCode Bot comp ca () mv
FinMem-Sup-element PropCode PropCode (FunEl h) comp ca () mv
FinMem-Sup-element PropCode PropCode (PiCode b f) comp ca () mv
FinMem-Sup-element PropCode PropCode (SigmaCode b f) comp ca () mv
FinMem-Sup-element PropCode PropCode (PairCode u v) comp ca () mv
FinMem-Sup-element PropCode UCode a () ca mu mv
FinMem-Sup-element PropCode (FunEl h) a () ca mu mv
FinMem-Sup-element PropCode (PiCode b f) a () ca mu mv
FinMem-Sup-element PropCode (SigmaCode b f) a () ca mu mv
FinMem-Sup-element PropCode (PairCode u v) a () ca mu mv
-- FunEl × FunEl
FinMem-Sup-element (FunEl g) UCode a () ca mu mv
FinMem-Sup-element (FunEl g) PropCode a () ca mu mv
FinMem-Sup-element (FunEl g) (PiCode b f) a () ca mu mv
FinMem-Sup-element (FunEl g) (SigmaCode b f) a () ca mu mv
FinMem-Sup-element (FunEl g) (PairCode u v) a () ca mu mv
FinMem-Sup-element (FunEl g) (FunEl h) Bot comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) UCode comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) PropCode comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) (FunEl k) comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) (PiCode b f) comp ca mu mv =
  mkSigma (FinMemFun-append g h b f (fst mu) (fst mv))
    (mkSigma (CoherentFun-append g h (fst (snd mu)) (fst (snd mv)) comp)
             (snd (snd mu)))
FinMem-Sup-element (FunEl g) (FunEl h) (SigmaCode b f) comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) (PairCode u v) comp ca () mv
-- PiCode × PiCode
FinMem-Sup-element (PiCode a1 f1) UCode a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) PropCode a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (FunEl h) a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (SigmaCode b f) a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (PairCode u v) a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) Bot comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) UCode comp ca mu mv =
  finMemUCode-Sup (PiCode a1 f1) (PiCode a2 f2) comp mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) PropCode comp ca mu mv =
  finMemPropCode-Sup (PiCode a1 f1) (PiCode a2 f2) comp mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (FunEl h) comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (SigmaCode b f) comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (PairCode u v) comp ca () mv
-- SigmaCode × SigmaCode
FinMem-Sup-element (SigmaCode a1 f1) UCode a () ca mu mv
FinMem-Sup-element (SigmaCode a1 f1) PropCode a () ca mu mv
FinMem-Sup-element (SigmaCode a1 f1) (FunEl h) a () ca mu mv
FinMem-Sup-element (SigmaCode a1 f1) (PiCode b f) a () ca mu mv
FinMem-Sup-element (SigmaCode a1 f1) (PairCode u v) a () ca mu mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) Bot comp ca () mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) UCode comp ca mu mv =
  finMemUCode-Sup (SigmaCode a1 f1) (SigmaCode a2 f2) comp mu mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) (FunEl h) comp ca () mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) (PiCode b f) comp ca () mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) (SigmaCode b f) comp ca () mv
FinMem-Sup-element (SigmaCode a1 f1) (SigmaCode a2 f2) (PairCode u v) comp ca () mv
-- PairCode × PairCode
FinMem-Sup-element (PairCode u1 v1) UCode a () ca mu mv
FinMem-Sup-element (PairCode u1 v1) PropCode a () ca mu mv
FinMem-Sup-element (PairCode u1 v1) (FunEl h) a () ca mu mv
FinMem-Sup-element (PairCode u1 v1) (PiCode b f) a () ca mu mv
FinMem-Sup-element (PairCode u1 v1) (SigmaCode b f) a () ca mu mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) Bot comp ca () mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) UCode comp ca () mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) PropCode comp ca () mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) (FunEl h) comp ca () mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) (PiCode b f) comp ca () mv
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) (SigmaCode b f) comp ca mu mv =
  let cu1 = fst (fst (fst (snd mu)))
      cv1 = snd (fst (fst (snd mu)))
      cu2 = fst (fst (fst (snd mv)))
      cv2 = snd (fst (fst (snd mv)))
      cu12 = Coherent-Sup u1 u2 (fst comp) cu1 cu2
      cv12 = Coherent-Sup v1 v2 (snd comp) cv1 cv2
      cohf = snd ca
      le-u1 = LeCode-Sup-left u1 u2 (fst comp) cu1 cu2
      le-u2 = LeCode-Sup-right u1 u2 (fst comp) cu1 cu2
      le-f1 = EvalFun-mon-arg f u1 (Sup u1 u2) le-u1 cohf cu1 cu12
      le-f2 = EvalFun-mon-arg f u2 (Sup u1 u2) le-u2 cohf cu2 cu12
      cf1 = Coherent-EvalFun f u1 cohf cu1
      cf2 = Coherent-EvalFun f u2 cohf cu2
      cf12 = Coherent-EvalFun f (Sup u1 u2) cohf cu12
      sigU = snd (snd mu)
      efU1 = EvalFun-in-UCode f u1 b cohf cu1 (fst (snd sigU))
      efU12 = EvalFun-in-UCode f (Sup u1 u2) b cohf cu12 (fst (snd sigU))
      v1' = finMem-upward v1 (EvalFun f u1) (EvalFun f (Sup u1 u2)) le-f1 cf1 cf12 (snd (fst mu)) efU12
      v2' = finMem-upward v2 (EvalFun f u2) (EvalFun f (Sup u1 u2)) le-f2 cf2 cf12 (snd (fst mv)) efU12
  in mkSigma
    (mkSigma
      (FinMem-Sup-element u1 u2 b (fst comp) (fst ca) (fst (fst mu)) (fst (fst mv)))
      (FinMem-Sup-element v1 v2 (EvalFun f (Sup u1 u2)) (snd comp) cf12 v1' v2'))
    (mkSigma
      (mkSigma (mkSigma cu12 cv12) (Or-NotBot-Sup u1 v1 u2 v2 (snd (fst (snd mu))) (fst comp) (snd comp)))
      sigU)
FinMem-Sup-element (PairCode u1 v1) (PairCode u2 v2) (PairCode u v) comp ca () mv

------------------------------------------------------------------------
-- Part 7k continued: finMem-Sup-both
------------------------------------------------------------------------

finMem-Sup-both : (a1 a2 u1 u2 : FinEl) ->
  FinMem a1 u1 -> FinMem a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
  FinMem (Sup a1 a2) (Sup u1 u2)
finMem-Sup-both a1 a2 u1 u2 m1 m2 comp-u comp-a =
  let u1U   = FinMem-a-in-U a1 u1 m1
      u2U   = FinMem-a-in-U a2 u2 m2
      cu1   = coh-from-aU u1 u1U
      cu2   = coh-from-aU u2 u2U
      ca1   = FinMem-coh-u a1 u1 m1
      ca2   = FinMem-coh-u a2 u2 m2
      c-sup = Coherent-Sup u1 u2 comp-u cu1 cu2
      m1'   = finMem-Sup-left u1 u2 a1 comp-u cu1 cu2 u2U ca1 m1
      m2'   = finMem-Sup-right u1 u2 a2 comp-u u1U ca2 m2
  in FinMem-Sup-element a1 a2 (Sup u1 u2) comp-a c-sup m1' m2'

------------------------------------------------------------------------
-- Part 7l: FinMem-Prop-Bot
------------------------------------------------------------------------

absurdEl : {A : Set} -> Empty -> A
absurdEl ()

{-# TERMINATING #-}
mutual
  FinMem-Prop-Bot : (u a : FinEl) -> FinMem u a -> FinMem a PropCode -> Eq u Bot
  FinMem-Prop-Bot Bot a mem aP = refl
  FinMem-Prop-Bot UCode UCode mem ()
  FinMem-Prop-Bot UCode PropCode ()
  FinMem-Prop-Bot UCode Bot ()
  FinMem-Prop-Bot UCode (FunEl g) ()
  FinMem-Prop-Bot UCode (PiCode a f) ()
  FinMem-Prop-Bot UCode (SigmaCode a f) ()
  FinMem-Prop-Bot UCode (PairCode u v) ()
  FinMem-Prop-Bot PropCode UCode mem ()
  FinMem-Prop-Bot PropCode PropCode ()
  FinMem-Prop-Bot PropCode Bot ()
  FinMem-Prop-Bot PropCode (FunEl g) ()
  FinMem-Prop-Bot PropCode (PiCode a f) ()
  FinMem-Prop-Bot PropCode (SigmaCode a f) ()
  FinMem-Prop-Bot PropCode (PairCode u v) ()
  FinMem-Prop-Bot (PiCode a' f') UCode mem ()
  FinMem-Prop-Bot (PiCode a' f') PropCode mem ()
  FinMem-Prop-Bot (PiCode a' f') Bot ()
  FinMem-Prop-Bot (PiCode a' f') (FunEl g) ()
  FinMem-Prop-Bot (PiCode a' f') (PiCode b g) ()
  FinMem-Prop-Bot (PiCode a' f') (SigmaCode b g) ()
  FinMem-Prop-Bot (PiCode a' f') (PairCode u v) ()
  FinMem-Prop-Bot (SigmaCode a' f') UCode mem ()
  FinMem-Prop-Bot (SigmaCode a' f') Bot ()
  FinMem-Prop-Bot (SigmaCode a' f') PropCode ()
  FinMem-Prop-Bot (SigmaCode a' f') (FunEl g) ()
  FinMem-Prop-Bot (SigmaCode a' f') (PiCode b g) ()
  FinMem-Prop-Bot (SigmaCode a' f') (SigmaCode b g) ()
  FinMem-Prop-Bot (SigmaCode a' f') (PairCode u v) ()
  FinMem-Prop-Bot (FunEl g) (PiCode b f) mem aP =
    FinMem-Prop-Bot-FunEl g b f mem aP
  FinMem-Prop-Bot (FunEl g) Bot ()
  FinMem-Prop-Bot (FunEl g) UCode ()
  FinMem-Prop-Bot (FunEl g) PropCode ()
  FinMem-Prop-Bot (FunEl g) (FunEl h) ()
  FinMem-Prop-Bot (FunEl g) (SigmaCode a f) ()
  FinMem-Prop-Bot (FunEl g) (PairCode u v) ()
  FinMem-Prop-Bot (PairCode u v) (SigmaCode a f) mem aP =
    FinMem-Prop-Bot-PairCode u v a f mem aP
  FinMem-Prop-Bot (PairCode u v) Bot ()
  FinMem-Prop-Bot (PairCode u v) UCode ()
  FinMem-Prop-Bot (PairCode u v) PropCode ()
  FinMem-Prop-Bot (PairCode u v) (FunEl g) ()
  FinMem-Prop-Bot (PairCode u v) (PiCode b g) ()
  FinMem-Prop-Bot (PairCode u v) (PairCode u2 v2) ()

  FinMem-Prop-Bot-FunEl : (g : FinFun) (b : FinEl) (f : FinFun) ->
    FinMem (FunEl g) (PiCode b f) -> FinMem (PiCode b f) PropCode ->
    Eq (FunEl g) Bot
  FinMem-Prop-Bot-FunEl nil b f mem aP
    with fst (snd mem)
  ... | ()
  FinMem-Prop-Bot-FunEl (cons p ps) b f mem aP =
    let cft = cft-from-cf (cons p ps) (fst (snd mem))
        nb = CFTcons.val-nbot cft
        allP = fst (snd aP)
        cohf = snd (snd aP)
        cp = CFTcons.key-coh cft
        evP = EvalFun-in-PropCode f (fst p) b cohf cp allP
        mem-v = snd (fst (fst mem))
        eq = FinMem-Prop-Bot (snd p) (EvalFun f (fst p)) mem-v evP
    in absurdEl (Eq-transport NotBot eq nb)

  -- PairCode case: Coherent (PairCode u v) requires Or (NotBot u) (NotBot v)
  -- but both u and v must be Bot by IH, contradiction
  FinMem-Prop-Bot-PairCode : (u v : FinEl) (a : FinEl) (f : FinFun) ->
    FinMem (PairCode u v) (SigmaCode a f) -> FinMem (SigmaCode a f) PropCode ->
    Eq (PairCode u v) Bot
  FinMem-Prop-Bot-PairCode u v a f mem ()

  -- EvalFun-in-PropCode (unchanged — operates on FinFun)
  EvalFun-in-PropCode : (f : FinFun) (x d : FinEl) ->
    CoherentFunTail f -> Coherent x -> FinMemAllProp f d ->
    FinMem (EvalFun f x) PropCode
  EvalFun-in-PropCode nil x d cohf cx allP = tt
  EvalFun-in-PropCode (cons q rest) x d cohf cx allP =
    EvalFun-in-PropCode-step (leFinEl (fst q) x) q rest x d refl cohf cx allP

  EvalFun-in-PropCode-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (x d : FinEl) ->
    Eq n (leFinEl (fst q) x) ->
    CoherentFunTail (cons q rest) -> Coherent x -> FinMemAllProp (cons q rest) d ->
    FinMem (EvalFun-step n (snd q) rest x) PropCode
  EvalFun-in-PropCode-step zero q rest x d eq cohf cx allP =
    EvalFun-in-PropCode rest x d (CFTcons.tail-coh cohf) cx (snd allP)
  EvalFun-in-PropCode-step (suc _) q rest x d eq cohf cx allP =
    let vP = snd (fst allP)
        restP = EvalFun-in-PropCode rest x d (CFTcons.tail-coh cohf) cx (snd allP)
        comp-vr = Comp-value-EvalFun q rest x
                    (leFinEl-sound (fst q) x (Eq-transport isPos eq tt))
                    cx (CFTcons.val-coh cohf) (CFTcons.compat cohf)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohf))
    in finMemPropCode-Sup (snd q) (EvalFun rest x) comp-vr vP restP

------------------------------------------------------------------------
-- FinMem-Prop-to-U
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  FinMem-Prop-to-U : (u : FinEl) -> FinMem u PropCode -> FinMem u UCode
  FinMem-Prop-to-U Bot mem = tt
  FinMem-Prop-to-U UCode ()
  FinMem-Prop-to-U PropCode ()
  FinMem-Prop-to-U (FunEl g) ()
  FinMem-Prop-to-U (PiCode a f) mem =
    mkSigma (fst mem)
      (mkSigma (FinMemAllProp-to-AllU f a (fst (snd mem)))
               (snd (snd mem)))
  FinMem-Prop-to-U (SigmaCode a f) ()
  FinMem-Prop-to-U (PairCode u v) ()

  FinMemAllProp-to-AllU : (f : FinFun) (a : FinEl) ->
    FinMemAllProp f a -> FinMemAllU f a
  FinMemAllProp-to-AllU nil a allP = tt
  FinMemAllProp-to-AllU (cons p ps) a allP =
    mkSigma (mkSigma (fst (fst allP)) (FinMem-Prop-to-U (snd p) (snd (fst allP))))
            (FinMemAllProp-to-AllU ps a (snd allP))

------------------------------------------------------------------------
-- LeCode-PropCode-cases
------------------------------------------------------------------------

LeCode-PropCode-cases : (a : FinEl) -> LeCode a PropCode ->
  Or (Eq a Bot) (Eq a PropCode)
LeCode-PropCode-cases Bot le = inl refl
LeCode-PropCode-cases UCode ()
LeCode-PropCode-cases PropCode le = inr refl
LeCode-PropCode-cases (FunEl g) ()
LeCode-PropCode-cases (PiCode a f) ()
LeCode-PropCode-cases (SigmaCode a f) ()
LeCode-PropCode-cases (PairCode u v) ()

------------------------------------------------------------------------
-- FinMem-U-to-PropCode: if v ∈ UCode, v ≤ w, w ∈ PropCode then v ∈ PropCode
-- Used to show FunEl-at-PiCode-at-Prop is absurd via FinMem-Prop-Bot-FunEl
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  FinMem-U-to-PropCode : (v w : FinEl) ->
    FinMem v UCode -> LeCode v w -> FinMem w PropCode ->
    FinMem v PropCode
  FinMem-U-to-PropCode Bot w memU le memP = tt
  FinMem-U-to-PropCode UCode w memU le memP =
    -- LeCode UCode w means w = UCode, FinMem UCode PropCode = Empty
    absurdEl (LeCode-UCode-PropCode w le memP)
    where
      LeCode-UCode-PropCode : (w : FinEl) -> LeCode UCode w -> FinMem w PropCode -> Empty
      LeCode-UCode-PropCode Bot ()
      LeCode-UCode-PropCode UCode le ()
      LeCode-UCode-PropCode PropCode ()
      LeCode-UCode-PropCode (FunEl _) ()
      LeCode-UCode-PropCode (PiCode _ _) ()
      LeCode-UCode-PropCode (SigmaCode _ _) ()
      LeCode-UCode-PropCode (PairCode _ _) ()
  FinMem-U-to-PropCode PropCode w memU le memP =
    absurdEl (LeCode-PropCode-PropCode w le memP)
    where
      LeCode-PropCode-PropCode : (w : FinEl) -> LeCode PropCode w -> FinMem w PropCode -> Empty
      LeCode-PropCode-PropCode Bot ()
      LeCode-PropCode-PropCode UCode ()
      LeCode-PropCode-PropCode PropCode le ()
      LeCode-PropCode-PropCode (FunEl _) ()
      LeCode-PropCode-PropCode (PiCode _ _) ()
      LeCode-PropCode-PropCode (SigmaCode _ _) ()
      LeCode-PropCode-PropCode (PairCode _ _) ()
  FinMem-U-to-PropCode (FunEl _) w () le memP
  FinMem-U-to-PropCode (PairCode _ _) w () le memP
  FinMem-U-to-PropCode (SigmaCode a0 f0) w memU le memP =
    absurdEl (LeCode-SigmaCode-PropCode w le memP)
    where
      LeCode-SigmaCode-PropCode : (w : FinEl) -> LeCode (SigmaCode a0 f0) w -> FinMem w PropCode -> Empty
      LeCode-SigmaCode-PropCode Bot ()
      LeCode-SigmaCode-PropCode UCode ()
      LeCode-SigmaCode-PropCode PropCode ()
      LeCode-SigmaCode-PropCode (FunEl _) ()
      LeCode-SigmaCode-PropCode (PiCode _ _) ()
      LeCode-SigmaCode-PropCode (SigmaCode _ _) le ()
      LeCode-SigmaCode-PropCode (PairCode _ _) ()
  FinMem-U-to-PropCode (PiCode a f) (PiCode b g) memU le memP =
    mkSigma (fst memU)
      (mkSigma (FinMemAllU-to-AllProp f a b g (fst (snd memU)) (snd le) (fst (snd memP)) (snd (snd memP)) (snd (snd memU)))
               (snd (snd memU)))
  FinMem-U-to-PropCode (PiCode a f) Bot memU () memP
  FinMem-U-to-PropCode (PiCode a f) UCode memU () memP
  FinMem-U-to-PropCode (PiCode a f) PropCode memU () memP
  FinMem-U-to-PropCode (PiCode a f) (FunEl _) memU () memP
  FinMem-U-to-PropCode (PiCode a f) (SigmaCode _ _) memU () memP
  FinMem-U-to-PropCode (PiCode a f) (PairCode _ _) memU () memP

  -- Convert FinMemAllU to FinMemAllProp using ordering and PropCode membership of target
  FinMemAllU-to-AllProp : (f : FinFun) (a b : FinEl) (g : FinFun) ->
    FinMemAllU f a -> LeFunCode f g ->
    FinMemAllProp g b -> CoherentFunTail g -> CoherentFunTail f ->
    FinMemAllProp f a
  FinMemAllU-to-AllProp nil a b g allU lf allP cohG cohF = tt
  FinMemAllU-to-AllProp (cons p ps) a b g allU lf allP cohG cohF =
    let keyA   = fst (fst allU)
        valU   = snd (fst allU)
        valLe  = fst lf
        ck     = CFTcons.key-coh cohF
        evP    = EvalFun-in-PropCode g (fst p) b cohG ck allP
        valP   = FinMem-U-to-PropCode (snd p) (EvalFun g (fst p)) valU valLe evP
    in mkSigma (mkSigma keyA valP)
               (FinMemAllU-to-AllProp ps a b g (snd allU) (snd lf) allP cohG (CFTcons.tail-coh cohF))
