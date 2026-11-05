{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderBridge.agda        (L1, part 4)
--
-- The structural core: application (EvalFun) and the order (LeCode) as
-- ORDINARY structural definitions, firing on the FINISHED numeric
-- decision leiC, plus the bridges to the staged versions.
--
--     f . u  =  Sup { v | (u',v) in f, u' <= u }
--
-- is the paper's demand reading of a closure: those are the finitely
-- many behaviours of the function observed so far.
--
-- Port of MIN/Domain/OrderBridge.agda.
------------------------------------------------------------------------

module LAZY.Domain.OrderBridge where

open import LAZY.Domain.Basic
open import LAZY.Domain.OrderStage
open import LAZY.Domain.OrderProps
open import LAZY.Domain.OrderStable

private
  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  evCombine-cong : (x : FinEl) {w w' : Nat} {r r' : FinEl} ->
    Eq w w' -> Eq r r' -> Eq (evCombine w x r) (evCombine w' x r')
  evCombine-cong x refl refl = refl

  rk-key : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANK (fst p)) (RANKFun (cons p ps))
  rk-key p ps = Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

  rk-val : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANK (snd p)) (RANKFun (cons p ps))
  rk-val p ps =
    Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-l (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

  rk-tail : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANKFun ps) (RANKFun (cons p ps))
  rk-tail p ps =
    Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-r (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

------------------------------------------------------------------------
-- The structural core.
------------------------------------------------------------------------

mutual
  EvalFun : FinFun -> FinEl -> FinEl
  EvalFun nil         u = Bot
  EvalFun (cons p ps) u = EvalFun-step (leiC (fst p) u) (snd p) ps u

  EvalFun-step : Nat -> FinEl -> FinFun -> FinEl -> FinEl
  EvalFun-step zero    bi rest u = EvalFun rest u
  EvalFun-step (suc n) bi rest u = Sup bi (EvalFun rest u)

-- Application of an element to an element: only functions apply.
applyEl : FinEl -> FinEl -> FinEl
applyEl Bot       v = Bot
applyEl (At a)    v = Bot
applyEl (Prd _ _) v = Bot
applyEl (Fn g)    v = EvalFun g v

mutual
  LeCode : FinEl -> FinEl -> Set
  LeCode Bot        v           = Top
  LeCode (At a)     Bot         = Empty
  LeCode (At a)     (At b)      = AtEq a b
  LeCode (At a)     (Prd _ _)   = Empty
  LeCode (At a)     (Fn _)      = Empty
  LeCode (Prd u v)  Bot         = Empty
  LeCode (Prd u v)  (At _)      = Empty
  LeCode (Prd u v)  (Prd u' v') = Pair (LeCode u u') (LeCode v v')
  LeCode (Prd u v)  (Fn _)      = Empty
  LeCode (Fn g)     Bot         = Empty
  LeCode (Fn g)     (At _)      = Empty
  LeCode (Fn g)     (Prd _ _)   = Empty
  LeCode (Fn g)     (Fn h)      = LeFunCode g h

  LeFunCode : FinFun -> FinFun -> Set
  LeFunCode nil         h = Top
  LeFunCode (cons p ps) h =
    Pair (LeCode (snd p) (EvalFun h (fst p))) (LeFunCode ps h)

------------------------------------------------------------------------
-- ev-bridge : the structural EvalFun equals OB.ev (suc n) above the rank.
------------------------------------------------------------------------

private
  step-evCombine-eq : (n : Nat) (w : Nat) (bi : FinEl) (ps : FinFun) (u : FinEl) ->
    Eq (EvalFun ps u) (OB.ev (suc n) ps u) ->
    Eq (EvalFun-step w bi ps u) (evCombine w bi (OB.ev (suc n) ps u))
  step-evCombine-eq n zero    bi ps u rec = rec
  step-evCombine-eq n (suc _) bi ps u rec = Eq-cong (Sup bi) rec

ev-bridge : (n : Nat) (h : FinFun) (u : FinEl) ->
  Le (max (RANKFun h) (RANK u)) n -> Eq (EvalFun h u) (OB.ev (suc n) h u)
ev-bridge n nil         u bnd = refl
ev-bridge n (cons p ps) u bnd =
  Eq-trans
    (step-evCombine-eq n (leiC (fst p) u) (snd p) ps u
      (ev-bridge n ps u
        (Le-trans (max (RANKFun ps) (RANK u)) (max (RANKFun (cons p ps)) (RANK u)) n
          (max-mono (RANKFun ps) (RANK u) (RANKFun (cons p ps)) (RANK u)
            (rk-tail p ps) (Le-refl (RANK u)))
          bnd)))
    (evCombine-cong (snd p)
      (lei-shift (suc (max (RANK (fst p)) (RANK u))) n (fst p) u
        (Le-suc (max (RANK (fst p)) (RANK u)) (max (RANK (fst p)) (RANK u))
          (Le-refl (max (RANK (fst p)) (RANK u))))
        (Le-trans (max (RANK (fst p)) (RANK u)) (max (RANKFun (cons p ps)) (RANK u)) n
          (max-mono (RANK (fst p)) (RANK u) (RANKFun (cons p ps)) (RANK u)
            (rk-key p ps) (Le-refl (RANK u)))
          bnd))
      refl)

private
  ev-rank : (n : Nat) (h : FinFun) (u : FinEl) ->
    Le (max (RANKFun h) (RANK u)) n -> Le (RANK (EvalFun h u)) (RANKFun h)
  ev-rank n h u bnd =
    Eq-transport (\ x -> Le (RANK x) (RANKFun h)) (Eq-sym (ev-bridge n h u bnd))
      (RANK-ev (suc n) h u)

------------------------------------------------------------------------
-- LeCode <-> OB.leq n   and   LeFunCode <-> OB.leqf (suc n).
------------------------------------------------------------------------

mutual
  toLeq : (n : Nat) (u v : FinEl) ->
    Le (max (RANK u) (RANK v)) n -> LeCode u v -> OB.leq n u v
  toLeq n Bot          v         bnd lc = leq-Bot-any n v
  toLeq n (At a)       Bot       bnd ()
  toLeq zero    (At a) (At b)    bnd lc = lc
  toLeq (suc m) (At a) (At b)    bnd lc = lc
  toLeq n (At a)       (Prd _ _) bnd ()
  toLeq n (At a)       (Fn _)    bnd ()
  toLeq n (Prd u v)    Bot       bnd ()
  toLeq n (Prd u v)    (At _)    bnd ()
  toLeq zero    (Prd u v) (Prd u' v') bnd lc = bnd
  toLeq (suc m) (Prd u v) (Prd u' v') bnd lc =
    mkSigma
      (toLeq m u u' (prd-l u v u' v' m bnd) (fst lc))
      (toLeq m v v' (prd-r u v u' v' m bnd) (snd lc))
  toLeq n (Prd u v)    (Fn _)    bnd ()
  toLeq n (Fn g)       Bot       bnd ()
  toLeq n (Fn g)       (At _)    bnd ()
  toLeq n (Fn g)       (Prd _ _) bnd ()
  toLeq zero    (Fn g) (Fn h)    bnd lc = bnd
  toLeq (suc m) (Fn g) (Fn h)    bnd lc = toLeqf m g h bnd lc

  toLeqf : (n : Nat) (g h : FinFun) ->
    Le (max (RANKFun g) (RANKFun h)) n -> LeFunCode g h -> OB.leqf (suc n) g h
  toLeqf n nil         h bnd lc = tt
  toLeqf n (cons p ps) h bnd lc =
    mkSigma
      (Eq-transport (\ x -> OB.leq n (snd p) x)
        (ev-bridge n h (fst p) (evb n p ps h bnd))
        (toLeq n (snd p) (EvalFun h (fst p))
          (Le-max-lub (RANK (snd p)) (RANK (EvalFun h (fst p))) n
            (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) n (rk-val p ps)
              (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))
            (Le-trans (RANK (EvalFun h (fst p))) (RANKFun h) n
              (ev-rank n h (fst p) (evb n p ps h bnd))
              (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)))
          (fst lc)))
      (toLeqf n ps h
        (Le-max-lub (RANKFun ps) (RANKFun h) n
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) n (rk-tail p ps)
            (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))
          (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd))
        (snd lc))

  fromLeq : (n : Nat) (u v : FinEl) ->
    Le (max (RANK u) (RANK v)) n -> OB.leq n u v -> LeCode u v
  fromLeq n Bot          v       bnd le = tt
  fromLeq zero    (At a) Bot     bnd ()
  fromLeq (suc m) (At a) Bot     bnd ()
  fromLeq zero    (At a) (At b)  bnd le = le
  fromLeq (suc m) (At a) (At b)  bnd le = le
  fromLeq zero    (At a) (Prd _ _) bnd ()
  fromLeq (suc m) (At a) (Prd _ _) bnd ()
  fromLeq zero    (At a) (Fn _)  bnd ()
  fromLeq (suc m) (At a) (Fn _)  bnd ()
  fromLeq zero    (Prd u v) Bot  bnd ()
  fromLeq (suc m) (Prd u v) Bot  bnd ()
  fromLeq zero    (Prd u v) (At _) bnd ()
  fromLeq (suc m) (Prd u v) (At _) bnd ()
  fromLeq zero    (Prd u v) (Prd u' v') bnd ()
  fromLeq (suc m) (Prd u v) (Prd u' v') bnd le =
    mkSigma
      (fromLeq m u u' (prd-l u v u' v' m bnd) (fst le))
      (fromLeq m v v' (prd-r u v u' v' m bnd) (snd le))
  fromLeq zero    (Prd u v) (Fn _) bnd ()
  fromLeq (suc m) (Prd u v) (Fn _) bnd ()
  fromLeq zero    (Fn g) Bot     bnd ()
  fromLeq (suc m) (Fn g) Bot     bnd ()
  fromLeq zero    (Fn g) (At _)  bnd ()
  fromLeq (suc m) (Fn g) (At _)  bnd ()
  fromLeq zero    (Fn g) (Prd _ _) bnd ()
  fromLeq (suc m) (Fn g) (Prd _ _) bnd ()
  fromLeq zero    (Fn g) (Fn h)  bnd ()
  fromLeq (suc m) (Fn g) (Fn h)  bnd le = fromLeqf m g h bnd le

  fromLeqf : (n : Nat) (g h : FinFun) ->
    Le (max (RANKFun g) (RANKFun h)) n -> OB.leqf (suc n) g h -> LeFunCode g h
  fromLeqf n nil         h bnd le = tt
  fromLeqf n (cons p ps) h bnd le =
    mkSigma
      (Eq-transport (\ x -> LeCode (snd p) x)
        (Eq-sym (ev-bridge n h (fst p) (evb n p ps h bnd)))
        (fromLeq n (snd p) (OB.ev (suc n) h (fst p))
          (Le-max-lub (RANK (snd p)) (RANK (OB.ev (suc n) h (fst p))) n
            (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) n (rk-val p ps)
              (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))
            (Le-trans (RANK (OB.ev (suc n) h (fst p))) (RANKFun h) n
              (RANK-ev (suc n) h (fst p))
              (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)))
          (fst le)))
      (fromLeqf n ps h
        (Le-max-lub (RANKFun ps) (RANKFun h) n
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) n (rk-tail p ps)
            (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))
          (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd))
        (snd le))

  -- the bound the ev-bridge needs inside a cons step
  evb : (n : Nat) (p : Pair FinEl FinEl) (ps h : FinFun) ->
    Le (max (RANKFun (cons p ps)) (RANKFun h)) n ->
    Le (max (RANKFun h) (RANK (fst p))) n
  evb n p ps h bnd =
    Le-max-lub (RANKFun h) (RANK (fst p)) n
      (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)
      (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) n (rk-key p ps)
        (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))

  -- bounds for the Prd descent
  prd-l : (u v u' v' : FinEl) (m : Nat) ->
    Le (max (RANK (Prd u v)) (RANK (Prd u' v'))) (suc m) ->
    Le (max (RANK u) (RANK u')) m
  prd-l u v u' v' m bnd =
    Le-max-lub (RANK u) (RANK u') m
      (Le-trans (RANK u) (max (RANK u) (RANK v)) m (Le-max-l (RANK u) (RANK v))
        (max-Le-l (max (RANK u) (RANK v)) (max (RANK u') (RANK v')) m bnd))
      (Le-trans (RANK u') (max (RANK u') (RANK v')) m (Le-max-l (RANK u') (RANK v'))
        (max-Le-r (max (RANK u) (RANK v)) (max (RANK u') (RANK v')) m bnd))

  prd-r : (u v u' v' : FinEl) (m : Nat) ->
    Le (max (RANK (Prd u v)) (RANK (Prd u' v'))) (suc m) ->
    Le (max (RANK v) (RANK v')) m
  prd-r u v u' v' m bnd =
    Le-max-lub (RANK v) (RANK v') m
      (Le-trans (RANK v) (max (RANK u) (RANK v)) m (Le-max-r (RANK u) (RANK v))
        (max-Le-l (max (RANK u) (RANK v)) (max (RANK u') (RANK v')) m bnd))
      (Le-trans (RANK v') (max (RANK u') (RANK v')) m (Le-max-r (RANK u') (RANK v'))
        (max-Le-r (max (RANK u) (RANK v)) (max (RANK u') (RANK v')) m bnd))

------------------------------------------------------------------------
-- LeCode <-> LeqC (the public, stage-free order).
------------------------------------------------------------------------

LeCode-to-LeqC : (u v : FinEl) -> LeCode u v -> LeqC u v
LeCode-to-LeqC u v lc =
  leqC-from (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v)))
    (toLeq (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v))) lc)

LeqC-to-LeCode : (u v : FinEl) -> LeqC u v -> LeCode u v
LeqC-to-LeCode u v lq =
  fromLeq (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v)))
    (leqC-to (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v))) lq)
