{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageBridge.agda  (MIN/ — Pi + U fragment)
--
-- The re-founded ORDER CORE (what PaperOrder's line-66 block becomes),
-- structural, plus the bridges connecting it to the stage-stratified
-- order of LeqStage.
--
--   * EvalFun : structural recursion over the FINISHED decision leiC
--     (NOT mutual with leFinEl any more) -> reduces normally, terminates.
--   * LeCode / LeFunCode : kept STRUCTURAL (the original definitions),
--     so `LeCode (PiCode a f)(PiCode b g) = Pair (LeCode a b)(LeFunCode f g)`
--     etc. still hold DEFINITIONALLY and the cone is unaffected.
--   * ev-bridge   : EvalFun h u = OB.ev (suc n) h u  (n above the ranks)
--   * toLeq/fromLeq/toLeqf/fromLeqf : LeCode u v <-> OB.leq n u v
--     (and the LeFunCode <-> OB.leqf (suc n) versions), so the
--     stage-proved order properties transfer to the structural LeCode.
--
-- All bridges are structural on the first FinEl arg / the FinFun list
-- (the EvalFun-result sits only in a non-measure position), with a
-- stage-shift (lei-shift) at the leaves.
--
-- NO postulates.
------------------------------------------------------------------------

module MIN.Domain.OrderBridge where

open import MIN.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.Domain.OrderStage
open import MIN.Domain.OrderProps using ( leq-Bot-any )
open import MIN.Domain.OrderStable using ( leqC-from ; leqC-to ; lei-shift )

private
  Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
  Eq-trans refl q = q

  evCombine-cong : (x : FinEl) {w w' : Nat} {r r' : FinEl} ->
    Eq w w' -> Eq r r' -> Eq (evCombine w x r) (evCombine w' x r')
  evCombine-cong x refl refl = refl

  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  rk-key : (p : Pair FinEl FinEl) (ps : FinFun) -> Le (RANK (fst p)) (RANKFun (cons p ps))
  rk-key p ps = Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

  rk-val : (p : Pair FinEl FinEl) (ps : FinFun) -> Le (RANK (snd p)) (RANKFun (cons p ps))
  rk-val p ps =
    Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-l (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

  rk-tail : (p : Pair FinEl FinEl) (ps : FinFun) -> Le (RANKFun ps) (RANKFun (cons p ps))
  rk-tail p ps =
    Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-r (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

------------------------------------------------------------------------
-- The re-founded structural core.
------------------------------------------------------------------------

-- EvalFun via EvalFun-step, firing on the FINISHED decision leiC (so it
-- is structural, NOT mutual with leFinEl), and keeping the
-- EvalFun-step shape the cone (Selection, PaperTyping) consumes.
mutual
  EvalFun : FinFun -> FinEl -> FinEl
  EvalFun nil         u = Bot
  EvalFun (cons p ps) u = EvalFun-step (leiC (fst p) u) (snd p) ps u

  EvalFun-step : Nat -> FinEl -> FinFun -> FinEl -> FinEl
  EvalFun-step zero    bi rest u = EvalFun rest u
  EvalFun-step (suc n) bi rest u = Sup bi (EvalFun rest u)

applyEl : FinEl -> FinEl -> FinEl
applyEl Bot          v = Bot
applyEl UCode        v = Bot
applyEl (FunEl g)    v = EvalFun g v
applyEl (PiCode a f) v = Bot

mutual
  LeCode : FinEl -> FinEl -> Set
  LeCode Bot             v             = Top
  LeCode UCode           Bot           = Empty
  LeCode UCode           UCode         = Top
  LeCode UCode           (FunEl h)     = Empty
  LeCode UCode           (PiCode b g)  = Empty
  LeCode (FunEl g)       Bot           = Empty
  LeCode (FunEl g)       UCode         = Empty
  LeCode (FunEl g)       (FunEl h)     = LeFunCode g h
  LeCode (FunEl g)       (PiCode b h)  = Empty
  LeCode (PiCode a f)    Bot           = Empty
  LeCode (PiCode a f)    UCode         = Empty
  LeCode (PiCode a f)    (FunEl h)     = Empty
  LeCode (PiCode a f)    (PiCode b g)  = Pair (LeCode a b) (LeFunCode f g)

  LeFunCode : FinFun -> FinFun -> Set
  LeFunCode nil         h = Top
  LeFunCode (cons p ps) h =
    Pair (LeCode (snd p) (EvalFun h (fst p))) (LeFunCode ps h)

------------------------------------------------------------------------
-- ev-bridge : the structural EvalFun equals the stage eval OB.ev (suc n)
-- for n above max(RANKFun h, RANK u).
------------------------------------------------------------------------

private
  -- EvalFun-step w bi ps u  =  evCombine w bi (OB.ev (suc n) ps u)
  -- given the tail-bridge  EvalFun ps u = OB.ev (suc n) ps u.
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
  -- RANK bound for a structural EvalFun-result, via the bridge + RANK-ev.
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
  toLeq n Bot          v             bnd lc = leq-Bot-any n v
  toLeq n UCode        Bot           bnd ()
  toLeq zero    UCode  UCode         bnd lc = tt
  toLeq (suc m) UCode  UCode         bnd lc = tt
  toLeq n UCode        (FunEl h)     bnd ()
  toLeq n UCode        (PiCode b g)  bnd ()
  toLeq n (FunEl g)    Bot           bnd ()
  toLeq n (FunEl g)    UCode         bnd ()
  toLeq zero    (FunEl g) (FunEl h)  bnd lc = bnd
  toLeq (suc m) (FunEl g) (FunEl h)  bnd lc = toLeqf m g h bnd lc
  toLeq n (FunEl g)    (PiCode b h)  bnd ()
  toLeq n (PiCode a f) Bot           bnd ()
  toLeq n (PiCode a f) UCode         bnd ()
  toLeq n (PiCode a f) (FunEl h)     bnd ()
  toLeq zero    (PiCode a f) (PiCode b g) bnd lc = bnd
  toLeq (suc m) (PiCode a f) (PiCode b g) bnd lc =
    mkSigma
      (toLeq m a b (max-mono-l a f b g m bnd) (fst lc))
      (toLeqf m f g (max-mono-r a f b g m bnd) (snd lc))

  toLeqf : (n : Nat) (g h : FinFun) ->
    Le (max (RANKFun g) (RANKFun h)) n -> LeFunCode g h -> OB.leqf (suc n) g h
  toLeqf n nil         h bnd lc = tt
  toLeqf n (cons p ps) h bnd lc =
    mkSigma
      (Eq-transport (\ x -> OB.leq n (snd p) x)
        (ev-bridge n h (fst p)
          (Le-max-lub (RANKFun h) (RANK (fst p)) n
            (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)
            (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) n (rk-key p ps)
              (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))))
        (toLeq n (snd p) (EvalFun h (fst p))
          (Le-max-lub (RANK (snd p)) (RANK (EvalFun h (fst p))) n
            (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) n (rk-val p ps)
              (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))
            (Le-trans (RANK (EvalFun h (fst p))) (RANKFun h) n
              (ev-rank n h (fst p)
                (Le-max-lub (RANKFun h) (RANK (fst p)) n
                  (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)
                  (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) n (rk-key p ps)
                    (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd))))
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
  fromLeq n Bot          v             bnd le = tt
  fromLeq zero    UCode  Bot           bnd ()
  fromLeq (suc m) UCode  Bot           bnd ()
  fromLeq zero    UCode  UCode         bnd le = tt
  fromLeq (suc m) UCode  UCode         bnd le = tt
  fromLeq zero    UCode  (FunEl h)     bnd ()
  fromLeq (suc m) UCode  (FunEl h)     bnd ()
  fromLeq zero    UCode  (PiCode b g)  bnd ()
  fromLeq (suc m) UCode  (PiCode b g)  bnd ()
  fromLeq zero    (FunEl g) Bot        bnd ()
  fromLeq (suc m) (FunEl g) Bot        bnd ()
  fromLeq zero    (FunEl g) UCode      bnd ()
  fromLeq (suc m) (FunEl g) UCode      bnd ()
  fromLeq zero    (FunEl g) (FunEl h)  bnd ()
  fromLeq (suc m) (FunEl g) (FunEl h)  bnd le = fromLeqf m g h bnd le
  fromLeq zero    (FunEl g) (PiCode b h) bnd ()
  fromLeq (suc m) (FunEl g) (PiCode b h) bnd ()
  fromLeq zero    (PiCode a f) Bot     bnd ()
  fromLeq (suc m) (PiCode a f) Bot     bnd ()
  fromLeq zero    (PiCode a f) UCode   bnd ()
  fromLeq (suc m) (PiCode a f) UCode   bnd ()
  fromLeq zero    (PiCode a f) (FunEl h) bnd ()
  fromLeq (suc m) (PiCode a f) (FunEl h) bnd ()
  fromLeq zero    (PiCode a f) (PiCode b g) bnd ()
  fromLeq (suc m) (PiCode a f) (PiCode b g) bnd le =
    mkSigma
      (fromLeq m a b (max-mono-l a f b g m bnd) (fst le))
      (fromLeqf m f g (max-mono-r a f b g m bnd) (snd le))

  fromLeqf : (n : Nat) (g h : FinFun) ->
    Le (max (RANKFun g) (RANKFun h)) n -> OB.leqf (suc n) g h -> LeFunCode g h
  fromLeqf n nil         h bnd le = tt
  fromLeqf n (cons p ps) h bnd le =
    mkSigma
      (Eq-transport (\ x -> LeCode (snd p) x)
        (Eq-sym (ev-bridge n h (fst p)
          (Le-max-lub (RANKFun h) (RANK (fst p)) n
            (max-Le-r (RANKFun (cons p ps)) (RANKFun h) n bnd)
            (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) n (rk-key p ps)
              (max-Le-l (RANKFun (cons p ps)) (RANKFun h) n bnd)))))
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

  -- bounds for the PiCode descent (n = suc m): RANK(PiCode a f)=suc(max(RANK a)(RANKFun f))
  max-mono-l : (a : FinEl) (f : FinFun) (b : FinEl) (g : FinFun) (m : Nat) ->
    Le (max (RANK (PiCode a f)) (RANK (PiCode b g))) (suc m) ->
    Le (max (RANK a) (RANK b)) m
  max-mono-l a f b g m bnd =
    Le-max-lub (RANK a) (RANK b) m
      (Le-trans (RANK a) (max (RANK a) (RANKFun f)) m
        (Le-max-l (RANK a) (RANKFun f))
        (max-Le-l (max (RANK a) (RANKFun f)) (max (RANK b) (RANKFun g)) m bnd))
      (Le-trans (RANK b) (max (RANK b) (RANKFun g)) m
        (Le-max-l (RANK b) (RANKFun g))
        (max-Le-r (max (RANK a) (RANKFun f)) (max (RANK b) (RANKFun g)) m bnd))

  max-mono-r : (a : FinEl) (f : FinFun) (b : FinEl) (g : FinFun) (m : Nat) ->
    Le (max (RANK (PiCode a f)) (RANK (PiCode b g))) (suc m) ->
    Le (max (RANKFun f) (RANKFun g)) m
  max-mono-r a f b g m bnd =
    Le-max-lub (RANKFun f) (RANKFun g) m
      (Le-trans (RANKFun f) (max (RANK a) (RANKFun f)) m
        (Le-max-r (RANK a) (RANKFun f))
        (max-Le-l (max (RANK a) (RANKFun f)) (max (RANK b) (RANKFun g)) m bnd))
      (Le-trans (RANKFun g) (max (RANK b) (RANKFun g)) m
        (Le-max-r (RANK b) (RANKFun g))
        (max-Le-r (max (RANK a) (RANKFun f)) (max (RANK b) (RANKFun g)) m bnd))

------------------------------------------------------------------------
-- LeCode <-> LeqC (the public level-free order).
------------------------------------------------------------------------

LeCode-to-LeqC : (u v : FinEl) -> LeCode u v -> LeqC u v
LeCode-to-LeqC u v lc =
  leqC-from (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v)))
    (toLeq (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v))) lc)

LeqC-to-LeCode : (u v : FinEl) -> LeqC u v -> LeCode u v
LeqC-to-LeCode u v lq =
  fromLeq (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v)))
    (leqC-to (max (RANK u) (RANK v)) u v (Le-refl (max (RANK u) (RANK v))) lq)
