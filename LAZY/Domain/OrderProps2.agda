{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderProps2.agda        (L1, part 6)
--
-- The stage-indexed ORDER + COHERENCE-OF-APPLICATION pack: the part of
-- the order theory whose termination genuinely needs the stage RANK
-- measure (the lemmas that recurse through an application-result in a
-- non-structural position).  Made structural by the stage index `n`:
-- recursion that descends RANK drops the stage suc m -> m; same-stage
-- recursion is structural on the FinEl / FinFun argument.
--
-- Convention ("a fact @ n"):
--   * FinEl order facts are about   OB.leq n
--   * FinFun order facts are about  OB.leqf (suc n)
--   * application appears as        OB.ev (suc n)
--
-- Port of MIN/Domain/OrderProps2.agda.  Two shape changes:
--   * UCode -> At a: the order on atoms is AtEq, so the atom clauses
--     transport along AtEq-sound instead of being trivially Top, and
--     the Sup clauses are guarded by the decision atEqN a b.
--   * PiCode a f -> Prd u v: BOTH components descend through leq at the
--     predecessor stage, so the Prd clauses are two copies of the FinEl
--     case rather than one FinEl + one FinFun case.
------------------------------------------------------------------------

module LAZY.Domain.OrderProps2 where

open import LAZY.Domain.Basic
open import LAZY.Domain.OrderStage
open import LAZY.Domain.OrderComp
open import LAZY.Domain.OrderProps
open import LAZY.Domain.OrderStable using ()

------------------------------------------------------------------------
-- small RANK helpers
------------------------------------------------------------------------

private
  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

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
-- extract-col : stage-free CompFun manipulation (used by Comp-down).
------------------------------------------------------------------------

extract-col : (h : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
  CompFun h (cons t ts) -> CompFun h (cons t nil)
extract-col nil        t ts cf = tt
extract-col (cons r rs) t ts cf =
  mkSigma (mkSigma (fst (fst cf)) tt)
          (extract-col rs t ts (snd cf))

------------------------------------------------------------------------
-- GROUP A: Comp-down family, stage-indexed.
------------------------------------------------------------------------

mutual
  Comp-down-n : (n : Nat) (u u' v : FinEl) ->
    Le (RANK u) n -> Le (RANK u') n ->
    OB.leq n u u' -> Comp u' v -> Comp u v
  -- n = zero
  Comp-down-n zero Bot       u'         v cu cu' le c = comp-Bot-l v
  Comp-down-n zero (At a)    Bot        v cu cu' () c
  Comp-down-n zero (At a)    (At b)     v cu cu' le c =
    Eq-transport (\ x -> Comp (At x) v) (Eq-sym (AtEq-sound a b le)) c
  Comp-down-n zero (At a)    (Prd _ _)  v cu cu' () c
  Comp-down-n zero (At a)    (Fn _)     v cu cu' () c
  Comp-down-n zero (Prd _ _) u'         v () cu' le c
  Comp-down-n zero (Fn g)    u'         v () cu' le c
  -- n = suc m
  Comp-down-n (suc m) Bot       u'        v cu cu' le c = comp-Bot-l v
  Comp-down-n (suc m) (At a)    Bot       v cu cu' () c
  Comp-down-n (suc m) (At a)    (At b)    v cu cu' le c =
    Eq-transport (\ x -> Comp (At x) v) (Eq-sym (AtEq-sound a b le)) c
  Comp-down-n (suc m) (At a)    (Prd _ _) v cu cu' () c
  Comp-down-n (suc m) (At a)    (Fn _)    v cu cu' () c
  Comp-down-n (suc m) (Prd u v) Bot       w cu cu' () c
  Comp-down-n (suc m) (Prd u v) (At _)    w cu cu' () c
  Comp-down-n (suc m) (Prd u v) (Prd u' v') Bot         cu cu' le c = tt
  Comp-down-n (suc m) (Prd u v) (Prd u' v') (At _)      cu cu' le ()
  Comp-down-n (suc m) (Prd u v) (Prd u' v') (Prd w1 w2) cu cu' le comp =
    mkSigma
      (Comp-down-n m u u' w1
        (max-Le-l (RANK u) (RANK v) m cu) (max-Le-l (RANK u') (RANK v') m cu')
        (fst le) (fst comp))
      (Comp-down-n m v v' w2
        (max-Le-r (RANK u) (RANK v) m cu) (max-Le-r (RANK u') (RANK v') m cu')
        (snd le) (snd comp))
  Comp-down-n (suc m) (Prd u v) (Prd u' v') (Fn _)      cu cu' le ()
  Comp-down-n (suc m) (Prd u v) (Fn _)    w cu cu' () c
  Comp-down-n (suc m) (Fn g)    Bot       v cu cu' () c
  Comp-down-n (suc m) (Fn g)    (At _)    v cu cu' () c
  Comp-down-n (suc m) (Fn g)    (Prd _ _) v cu cu' () c
  Comp-down-n (suc m) (Fn g)    (Fn h)    Bot       cu cu' le c = tt
  Comp-down-n (suc m) (Fn g)    (Fn h)    (At _)    cu cu' le ()
  Comp-down-n (suc m) (Fn g)    (Fn h)    (Prd _ _) cu cu' le ()
  Comp-down-n (suc m) (Fn g)    (Fn h)    (Fn j)    cu cu' le c =
    LeFunCode-CompFun-trans-n m g h j cu cu' le c

  LeFunCode-CompFun-trans-n : (m : Nat) (g h j : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m ->
    OB.leqf (suc m) g h -> CompFun h j -> CompFun g j
  LeFunCode-CompFun-trans-n m nil         h j bg bh le cf = tt
  LeFunCode-CompFun-trans-n m (cons s ss) h j bg bh le cf =
    mkSigma
      (build-CompStepFun-n m s j h
        (max-Le-l (RANK (fst s)) (max (RANK (snd s)) (RANKFun ss)) m bg)
        (max-Le-l (RANK (snd s)) (RANKFun ss) m
          (max-Le-r (RANK (fst s)) (max (RANK (snd s)) (RANKFun ss)) m bg))
        bh (fst le) cf)
      (LeFunCode-CompFun-trans-n m ss h j
        (max-Le-r (RANK (snd s)) (RANKFun ss) m
          (max-Le-r (RANK (fst s)) (max (RANK (snd s)) (RANKFun ss)) m bg))
        bh (snd le) cf)

  build-CompStepFun-n : (m : Nat) (s : Pair FinEl FinEl) (j h : FinFun) ->
    Le (RANK (fst s)) m -> Le (RANK (snd s)) m -> Le (RANKFun h) m ->
    OB.leq m (snd s) (OB.ev (suc m) h (fst s)) -> CompFun h j -> CompStepFun s j
  build-CompStepFun-n m s nil         h bks bvs bh le cf = tt
  build-CompStepFun-n m s (cons t ts) h bks bvs bh le cf =
    mkSigma
      (\ comp-keys ->
        let col       = extract-col h t ts cf
            comp-eval = EvalFun-guarded-comp-n m h (fst s) t bh bks col comp-keys
        in Comp-down-n m (snd s) (OB.ev (suc m) h (fst s)) (snd t)
             bvs
             (Le-trans (RANK (OB.ev (suc m) h (fst s))) (RANKFun h) m
               (RANK-ev (suc m) h (fst s)) bh)
             le comp-eval)
      (build-CompStepFun-n m s ts h bks bvs bh le (CompFun-drop-col h t ts cf))

  EvalFun-guarded-comp-n : (m : Nat) (h : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
    Le (RANKFun h) m -> Le (RANK xi) m ->
    CompFun h (cons t nil) -> Comp xi (fst t) ->
    Comp (OB.ev (suc m) h xi) (snd t)
  EvalFun-guarded-comp-n m nil         xi t bh bxi col cxi = comp-Bot-l (snd t)
  EvalFun-guarded-comp-n m (cons r rs) xi t bh bxi col cxi =
    EvalFun-guarded-comp-step-n m (OB.lei m (fst r) xi) r rs xi t refl
      (max-Le-l (RANK (fst r)) (max (RANK (snd r)) (RANKFun rs)) m bh)
      bxi
      (fst (fst col)) cxi
      (EvalFun-guarded-comp-n m rs xi t
        (max-Le-r (RANK (snd r)) (RANKFun rs) m
          (max-Le-r (RANK (fst r)) (max (RANK (snd r)) (RANKFun rs)) m bh))
        bxi (snd col) cxi)

  EvalFun-guarded-comp-step-n : (m : Nat) (w : Nat)
    (r : Pair FinEl FinEl) (rs : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
    Eq w (OB.lei m (fst r) xi) ->
    Le (RANK (fst r)) m -> Le (RANK xi) m ->
    CompStepStep r t -> Comp xi (fst t) ->
    Comp (OB.ev (suc m) rs xi) (snd t) ->
    Comp (evCombine w (snd r) (OB.ev (suc m) rs xi)) (snd t)
  EvalFun-guarded-comp-step-n m zero    r rs xi t eq bkr bxi css cxi ih = ih
  EvalFun-guarded-comp-step-n m (suc w) r rs xi t eq bkr bxi css cxi ih =
    let le        = lei-sound m (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = Comp-down-n m (fst r) xi (fst t) bkr bxi le cxi
    in comp-Sup-sym (snd r) (OB.ev (suc m) rs xi) (snd t) (css comp-keys) ih

------------------------------------------------------------------------
-- GROUP B: LeCode-Comp.
------------------------------------------------------------------------

LeCode-Comp-n : (n : Nat) (u v w : FinEl) ->
  Le (RANK u) n -> Le (RANK v) n -> Le (RANK w) n ->
  Coherent w -> OB.leq n u w -> OB.leq n v w -> Comp u v
LeCode-Comp-n n u v w bu bv bw coh lu lv =
  Comp-down-n n u w v bu bw lu
    (Comp-sym v w
      (Comp-down-n n v w w bv bw lv (Comp-refl w coh)))

------------------------------------------------------------------------
-- GROUP C: Comp-value-EvalFun.
------------------------------------------------------------------------

mutual
  Comp-value-EvalFun-n : (m : Nat) (q : Pair FinEl FinEl) (rest : FinFun) (xi : FinEl) ->
    Le (RANK (fst q)) m -> Le (RANK xi) m -> Le (RANKFun rest) m ->
    OB.leq m (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    CoherentWith q rest -> CompStepFun q rest ->
    Comp (snd q) (OB.ev (suc m) rest xi)
  Comp-value-EvalFun-n m q nil         xi bkq bxi brest le cxi cohv cw csf =
    comp-Bot-r (snd q)
  Comp-value-EvalFun-n m q (cons r rs) xi bkq bxi brest le cxi cohv cw csf =
    Comp-value-EvalFun-step-n m (OB.lei m (fst r) xi) q r rs xi refl
      bkq bxi
      (Le-trans (RANK (fst r)) (RANKFun (cons r rs)) m (rk-key r rs) brest)
      (Le-trans (RANKFun rs) (RANKFun (cons r rs)) m (rk-tail r rs) brest)
      le cxi cohv (fst cw) (snd cw) (fst csf) (snd csf)

  Comp-value-EvalFun-step-n : (m : Nat) (w : Nat) (q r : Pair FinEl FinEl)
    (rs : FinFun) (xi : FinEl) ->
    Eq w (OB.lei m (fst r) xi) ->
    Le (RANK (fst q)) m -> Le (RANK xi) m -> Le (RANK (fst r)) m -> Le (RANKFun rs) m ->
    OB.leq m (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    (Comp (fst q) (fst r) -> Comp (snd q) (snd r)) ->
    CoherentWith q rs -> CompStepStep q r -> CompStepFun q rs ->
    Comp (snd q) (evCombine w (snd r) (OB.ev (suc m) rs xi))
  Comp-value-EvalFun-step-n m zero q r rs xi eq bkq bxi bkr brs le cxi cohv css cw css2 csf =
    Comp-value-EvalFun-n m q rs xi bkq bxi brs le cxi cohv cw csf
  Comp-value-EvalFun-step-n m (suc w) q r rs xi eq bkq bxi bkr brs le cxi cohv css cw css2 csf =
    let le-r      = lei-sound m (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = LeCode-Comp-n m (fst q) (fst r) xi bkq bkr bxi cxi le le-r
    in comp-Sup (snd q) (snd r) (OB.ev (suc m) rs xi)
         (css comp-keys)
         (Comp-value-EvalFun-n m q rs xi bkq bxi brs le cxi cohv cw csf)

------------------------------------------------------------------------
-- GROUP C': Coherent-EvalFun.
------------------------------------------------------------------------

mutual
  Coherent-EvalFun-n : (m : Nat) (k : FinFun) (u : FinEl) ->
    Le (RANKFun k) m -> Le (RANK u) m ->
    CoherentFun k -> Coherent u -> Coherent (OB.ev (suc m) k u)
  Coherent-EvalFun-n m nil          u bk bu cohk cohu = tt
  Coherent-EvalFun-n m (cons q rest) u bk bu cohk cohu =
    Coherent-EvalFun-step-n m (OB.lei m (fst q) u) q rest u refl
      (Le-trans (RANK (fst q)) (RANKFun (cons q rest)) m (rk-key q rest) bk)
      (Le-trans (RANK (snd q)) (RANKFun (cons q rest)) m (rk-val q rest) bk)
      (Le-trans (RANKFun rest) (RANKFun (cons q rest)) m (rk-tail q rest) bk)
      bu cohk cohu

  Coherent-EvalFun-step-n : (m : Nat) (w : Nat) (q : Pair FinEl FinEl)
    (rest : FinFun) (u : FinEl) ->
    Eq w (OB.lei m (fst q) u) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun rest) m -> Le (RANK u) m ->
    CoherentFun (cons q rest) -> Coherent u ->
    Coherent (evCombine w (snd q) (OB.ev (suc m) rest u))
  Coherent-EvalFun-step-n m zero    q rest u eq bkq bvq brest bu cohk cohu =
    Coherent-EvalFun-n m rest u brest bu (CFcons.tail-coh cohk) cohu
  Coherent-EvalFun-step-n m (suc w) q rest u eq bkq bvq brest bu cohk cohu =
    let cohv     = CFcons.val-coh cohk
        coh-rest = Coherent-EvalFun-n m rest u brest bu (CFcons.tail-coh cohk) cohu
        comp-vr  = Comp-value-EvalFun-n m q rest u bkq bu brest
                     (lei-sound m (fst q) u (Eq-transport isPos eq tt))
                     cohu cohv (CFcons.compat cohk)
                     (coherentWith-to-compStepFun q rest (CFcons.compat cohk))
    in Coherent-Sup (snd q) (OB.ev (suc m) rest u) comp-vr cohv coh-rest

------------------------------------------------------------------------
-- more RANK helpers for GROUP D
------------------------------------------------------------------------

private
  ev-bound : (m : Nat) (k : FinFun) (u : FinEl) ->
    Le (RANKFun k) m -> Le (RANK (OB.ev (suc m) k u)) m
  ev-bound m k u bk =
    Le-trans (RANK (OB.ev (suc m) k u)) (RANKFun k) m (RANK-ev (suc m) k u) bk

  sup-bound : (m : Nat) (x y : FinEl) ->
    Le (RANK x) m -> Le (RANK y) m -> Le (RANK (Sup x y)) m
  sup-bound m x y bx by =
    Le-trans (RANK (Sup x y)) (max (RANK x) (RANK y)) m
      (RANK-Sup x y) (Le-max-lub (RANK x) (RANK y) m bx by)

  append-bound : (m : Nat) (g h : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m -> Le (RANKFun (append g h)) m
  append-bound m g h bg bh =
    Le-trans (RANKFun (append g h)) (max (RANKFun g) (RANKFun h)) m
      (RANK-append g h) (Le-max-lub (RANKFun g) (RANKFun h) m bg bh)

  -- atom Sup, guarded by the decision
  supAtL : (n w : Nat) -> isPos w -> (a b : Atom) -> OB.leq n (At a) (supAt w a b)
  supAtL n       zero    () a b
  supAtL zero    (suc x) _  a b = AtEq-refl a
  supAtL (suc m) (suc x) _  a b = AtEq-refl a

  supAtR : (n w : Nat) (a b : Atom) -> Eq w (atEqN a b) -> isPos w ->
           OB.leq n (At b) (supAt w a b)
  supAtR n       zero    a b eq ()
  supAtR zero    (suc x) a b eq _ = AtEq-sym a b (Eq-transport isPos eq tt)
  supAtR (suc m) (suc x) a b eq _ = AtEq-sym a b (Eq-transport isPos eq tt)

------------------------------------------------------------------------
-- GROUP D: the big order property block, stage-indexed.
------------------------------------------------------------------------

mutual
  ----------------------------------------------------------------------
  -- reflexivity
  ----------------------------------------------------------------------
  LeCode-refl-n : (n : Nat) (a : FinEl) ->
    Le (RANK a) n -> Coherent a -> OB.leq n a a
  LeCode-refl-n zero    Bot       cond ca = tt
  LeCode-refl-n zero    (At a)    cond ca = AtEq-refl a
  LeCode-refl-n zero    (Prd _ _) ()   ca
  LeCode-refl-n zero    (Fn g)    ()   ca
  LeCode-refl-n (suc m) Bot       cond ca = tt
  LeCode-refl-n (suc m) (At a)    cond ca = AtEq-refl a
  LeCode-refl-n (suc m) (Prd u v) cond ca =
    mkSigma (LeCode-refl-n m u (max-Le-l (RANK u) (RANK v) m cond) (fst ca))
            (LeCode-refl-n m v (max-Le-r (RANK u) (RANK v) m cond) (snd ca))
  LeCode-refl-n (suc m) (Fn g)    cond ca = LeFunCode-refl-n m g cond ca

  LeFunCode-refl-n : (m : Nat) (g : FinFun) ->
    Le (RANKFun g) m -> CoherentFun g -> OB.leqf (suc m) g g
  LeFunCode-refl-n m nil         cond coh = tt
  LeFunCode-refl-n m (cons p ps) cond coh =
    mkSigma
      (LeFunCode-refl-head-step-n m (OB.lei m (fst p) (fst p)) p ps refl
        (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) cond)
        (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) cond)
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) cond)
        coh)
      (LeFunCode-cons-lift-n m ps p ps
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) cond)
        (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) cond)
        (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) cond)
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) cond)
        coh (CFcons.tail-coh coh)
        (LeFunCode-refl-n m ps
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) cond)
          (CFcons.tail-coh coh)))

  LeFunCode-refl-head-step-n : (m : Nat) (w : Nat)
    (p : Pair FinEl FinEl) (ps : FinFun) ->
    Eq w (OB.lei m (fst p) (fst p)) ->
    Le (RANK (fst p)) m -> Le (RANK (snd p)) m -> Le (RANKFun ps) m ->
    CoherentFun (cons p ps) ->
    OB.leq m (snd p) (evCombine w (snd p) (OB.ev (suc m) ps (fst p)))
  LeFunCode-refl-head-step-n m zero p ps eq bkp bvp bps coh
    with Eq-transport isPos (Eq-sym eq)
           (lei-complete m (fst p) (fst p)
             (LeCode-refl-n m (fst p) bkp (CFcons.key-coh coh)))
  ... | ()
  LeFunCode-refl-head-step-n m (suc w) p ps eq bkp bvp bps coh =
    LeCode-Sup-left-n m (snd p) (OB.ev (suc m) ps (fst p))
      bvp (ev-bound m ps (fst p) bps)
      (Comp-value-EvalFun-n m p ps (fst p) bkp bkp bps
        (LeCode-refl-n m (fst p) bkp (CFcons.key-coh coh))
        (CFcons.key-coh coh) (CFcons.val-coh coh)
        (CFcons.compat coh)
        (coherentWith-to-compStepFun p ps (CFcons.compat coh)))
      (CFcons.val-coh coh)
      (Coherent-EvalFun-n m ps (fst p) bps bkp
        (CFcons.tail-coh coh) (CFcons.key-coh coh))

  LeFunCode-cons-lift-n : (m : Nat) (g : FinFun) (p : Pair FinEl FinEl) (rest : FinFun) ->
    Le (RANKFun g) m -> Le (RANK (fst p)) m -> Le (RANK (snd p)) m -> Le (RANKFun rest) m ->
    CoherentFun (cons p rest) -> CoherentFun g ->
    OB.leqf (suc m) g rest -> OB.leqf (suc m) g (cons p rest)
  LeFunCode-cons-lift-n m nil         p rest bg bkp bvp brest coh cohg le = tt
  LeFunCode-cons-lift-n m (cons q qs) p rest bg bkp bvp brest coh cohg le =
    mkSigma
      (LeCode-trans-n m (snd q) (OB.ev (suc m) rest (fst q))
                        (OB.ev (suc m) (cons p rest) (fst q))
        (Le-trans (RANK (snd q)) (RANKFun (cons q qs)) m (rk-val q qs) bg)
        (ev-bound m rest (fst q) brest)
        (ev-bound m (cons p rest) (fst q)
          (Le-max-lub (RANK (fst p)) (max (RANK (snd p)) (RANKFun rest)) m bkp
            (Le-max-lub (RANK (snd p)) (RANKFun rest) m bvp brest)))
        (CFcons.val-coh cohg)
        (Coherent-EvalFun-n m rest (fst q) brest
          (Le-trans (RANK (fst q)) (RANKFun (cons q qs)) m (rk-key q qs) bg)
          (CFcons.tail-coh coh) (CFcons.key-coh cohg))
        (Coherent-EvalFun-n m (cons p rest) (fst q)
          (Le-max-lub (RANK (fst p)) (max (RANK (snd p)) (RANKFun rest)) m bkp
            (Le-max-lub (RANK (snd p)) (RANKFun rest) m bvp brest))
          (Le-trans (RANK (fst q)) (RANKFun (cons q qs)) m (rk-key q qs) bg)
          coh (CFcons.key-coh cohg))
        (fst le)
        (EvalFun-cons-mono-n m p rest (fst q) bkp bvp brest
          (Le-trans (RANK (fst q)) (RANKFun (cons q qs)) m (rk-key q qs) bg)
          coh (CFcons.key-coh cohg)))
      (LeFunCode-cons-lift-n m qs p rest
        (Le-trans (RANKFun qs) (RANKFun (cons q qs)) m (rk-tail q qs) bg)
        bkp bvp brest coh (CFcons.tail-coh cohg) (snd le))

  EvalFun-cons-mono-n : (m : Nat) (q : Pair FinEl FinEl) (rest : FinFun) (u : FinEl) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun rest) m -> Le (RANK u) m ->
    CoherentFun (cons q rest) -> Coherent u ->
    OB.leq m (OB.ev (suc m) rest u) (OB.ev (suc m) (cons q rest) u)
  EvalFun-cons-mono-n m q rest u bkq bvq brest bu coh cu =
    EvalFun-cons-mono-step-n m (OB.lei m (fst q) u) q rest u refl
      bkq bvq brest bu coh cu

  EvalFun-cons-mono-step-n : (m : Nat) (w : Nat)
    (q : Pair FinEl FinEl) (rest : FinFun) (u : FinEl) ->
    Eq w (OB.lei m (fst q) u) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun rest) m -> Le (RANK u) m ->
    CoherentFun (cons q rest) -> Coherent u ->
    OB.leq m (OB.ev (suc m) rest u) (evCombine w (snd q) (OB.ev (suc m) rest u))
  EvalFun-cons-mono-step-n m zero    q rest u eq bkq bvq brest bu coh cu =
    LeCode-refl-n m (OB.ev (suc m) rest u) (ev-bound m rest u brest)
      (Coherent-EvalFun-n m rest u brest bu (CFcons.tail-coh coh) cu)
  EvalFun-cons-mono-step-n m (suc w) q rest u eq bkq bvq brest bu coh cu =
    LeCode-Sup-right-n m (snd q) (OB.ev (suc m) rest u)
      bvq (ev-bound m rest u brest)
      (Comp-value-EvalFun-n m q rest u bkq bu brest
        (lei-sound m (fst q) u (Eq-transport isPos eq tt))
        cu (CFcons.val-coh coh) (CFcons.compat coh)
        (coherentWith-to-compStepFun q rest (CFcons.compat coh)))
      (CFcons.val-coh coh)
      (Coherent-EvalFun-n m rest u brest bu (CFcons.tail-coh coh) cu)

  ----------------------------------------------------------------------
  -- Sup-left / Sup-right
  ----------------------------------------------------------------------
  LeCode-Sup-left-n : (n : Nat) (a b : FinEl) ->
    Le (RANK a) n -> Le (RANK b) n ->
    Comp a b -> Coherent a -> Coherent b -> OB.leq n a (Sup a b)
  LeCode-Sup-left-n n Bot b ba bb comp ca cb = leq-Bot-any n (Sup Bot b)
  -- zero
  LeCode-Sup-left-n zero (At a)    Bot       ba bb comp ca cb = AtEq-refl a
  LeCode-Sup-left-n zero (At a)    (At b)    ba bb comp ca cb =
    supAtL zero (atEqN a b) comp a b
  LeCode-Sup-left-n zero (At a)    (Prd _ _) ba ()   comp ca cb
  LeCode-Sup-left-n zero (At a)    (Fn h)    ba ()   comp ca cb
  LeCode-Sup-left-n zero (Prd _ _) b         () bb   comp ca cb
  LeCode-Sup-left-n zero (Fn g)    b         () bb   comp ca cb
  -- suc
  LeCode-Sup-left-n (suc m) (At a)    Bot       ba bb comp ca cb = AtEq-refl a
  LeCode-Sup-left-n (suc m) (At a)    (At b)    ba bb comp ca cb =
    supAtL (suc m) (atEqN a b) comp a b
  LeCode-Sup-left-n (suc m) (At a)    (Prd _ _) ba bb () ca cb
  LeCode-Sup-left-n (suc m) (At a)    (Fn h)    ba bb () ca cb
  LeCode-Sup-left-n (suc m) (Prd u v) Bot       ba bb comp ca cb =
    LeCode-refl-n (suc m) (Prd u v) ba ca
  LeCode-Sup-left-n (suc m) (Prd u v) (At _)    ba bb () ca cb
  LeCode-Sup-left-n (suc m) (Prd u v) (Prd u' v') ba bb comp ca cb =
    mkSigma
      (LeCode-Sup-left-n m u u'
        (max-Le-l (RANK u) (RANK v) m ba) (max-Le-l (RANK u') (RANK v') m bb)
        (fst comp) (fst ca) (fst cb))
      (LeCode-Sup-left-n m v v'
        (max-Le-r (RANK u) (RANK v) m ba) (max-Le-r (RANK u') (RANK v') m bb)
        (snd comp) (snd ca) (snd cb))
  LeCode-Sup-left-n (suc m) (Prd u v) (Fn h)    ba bb () ca cb
  LeCode-Sup-left-n (suc m) (Fn g)    Bot       ba bb comp ca cb =
    LeCode-refl-n (suc m) (Fn g) ba ca
  LeCode-Sup-left-n (suc m) (Fn g)    (At _)    ba bb () ca cb
  LeCode-Sup-left-n (suc m) (Fn g)    (Prd _ _) ba bb () ca cb
  LeCode-Sup-left-n (suc m) (Fn g)    (Fn h)    ba bb comp ca cb =
    LeFunCode-append-left-n m g h ba bb comp ca cb

  LeCode-Sup-right-n : (n : Nat) (a b : FinEl) ->
    Le (RANK a) n -> Le (RANK b) n ->
    Comp a b -> Coherent a -> Coherent b -> OB.leq n b (Sup a b)
  LeCode-Sup-right-n n a Bot ba bb comp ca cb = leq-Bot-any n (Sup a Bot)
  -- zero
  LeCode-Sup-right-n zero Bot       (At b)    ba bb comp ca cb = AtEq-refl b
  LeCode-Sup-right-n zero (At a)    (At b)    ba bb comp ca cb =
    supAtR zero (atEqN a b) a b refl comp
  LeCode-Sup-right-n zero (Prd _ _) (At b)    () bb comp ca cb
  LeCode-Sup-right-n zero (Fn g)    (At b)    () bb comp ca cb
  LeCode-Sup-right-n zero a         (Prd _ _) ba () comp ca cb
  LeCode-Sup-right-n zero a         (Fn h)    ba () comp ca cb
  -- suc
  LeCode-Sup-right-n (suc m) Bot       (At b)    ba bb comp ca cb = AtEq-refl b
  LeCode-Sup-right-n (suc m) (At a)    (At b)    ba bb comp ca cb =
    supAtR (suc m) (atEqN a b) a b refl comp
  LeCode-Sup-right-n (suc m) (Prd _ _) (At b)    ba bb () ca cb
  LeCode-Sup-right-n (suc m) (Fn g)    (At b)    ba bb () ca cb
  LeCode-Sup-right-n (suc m) Bot       (Prd u' v') ba bb comp ca cb =
    LeCode-refl-n (suc m) (Prd u' v') bb cb
  LeCode-Sup-right-n (suc m) (At a)    (Prd _ _) ba bb () ca cb
  LeCode-Sup-right-n (suc m) (Prd u v) (Prd u' v') ba bb comp ca cb =
    mkSigma
      (LeCode-Sup-right-n m u u'
        (max-Le-l (RANK u) (RANK v) m ba) (max-Le-l (RANK u') (RANK v') m bb)
        (fst comp) (fst ca) (fst cb))
      (LeCode-Sup-right-n m v v'
        (max-Le-r (RANK u) (RANK v) m ba) (max-Le-r (RANK u') (RANK v') m bb)
        (snd comp) (snd ca) (snd cb))
  LeCode-Sup-right-n (suc m) (Fn g)    (Prd _ _) ba bb () ca cb
  LeCode-Sup-right-n (suc m) Bot       (Fn h)    ba bb comp ca cb =
    LeCode-refl-n (suc m) (Fn h) bb cb
  LeCode-Sup-right-n (suc m) (At a)    (Fn h)    ba bb () ca cb
  LeCode-Sup-right-n (suc m) (Prd _ _) (Fn h)    ba bb () ca cb
  LeCode-Sup-right-n (suc m) (Fn g)    (Fn h)    ba bb comp ca cb =
    LeFunCode-append-right-n m g h ba bb comp ca cb

  ----------------------------------------------------------------------
  -- transitivity
  ----------------------------------------------------------------------
  LeCode-trans-n : (n : Nat) (x y z : FinEl) ->
    Le (RANK x) n -> Le (RANK y) n -> Le (RANK z) n ->
    Coherent x -> Coherent y -> Coherent z ->
    OB.leq n x y -> OB.leq n y z -> OB.leq n x z
  LeCode-trans-n n Bot y z bx by bz cx cy cz xy yz = leq-Bot-any n z
  -- At
  LeCode-trans-n zero    (At a) Bot       z bx by bz cx cy cz () yz
  LeCode-trans-n zero    (At a) (At b)    z bx by bz cx cy cz xy yz =
    Eq-transport (\ w -> OB.leq zero (At w) z) (Eq-sym (AtEq-sound a b xy)) yz
  LeCode-trans-n zero    (At a) (Prd _ _) z bx by bz cx cy cz () yz
  LeCode-trans-n zero    (At a) (Fn _)    z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (At a) Bot       z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (At a) (At b)    z bx by bz cx cy cz xy yz =
    Eq-transport (\ w -> OB.leq (suc m) (At w) z) (Eq-sym (AtEq-sound a b xy)) yz
  LeCode-trans-n (suc m) (At a) (Prd _ _) z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (At a) (Fn _)    z bx by bz cx cy cz () yz
  -- Prd
  LeCode-trans-n zero    (Prd _ _) y z () by bz cx cy cz xy yz
  LeCode-trans-n (suc m) (Prd u v) Bot       z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (Prd u v) (At _)    z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (Prd u v) (Prd u' v') Bot         bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Prd u v) (Prd u' v') (At _)      bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Prd u v) (Prd u' v') (Prd u'' v'') bx by bz cx cy cz xy yz =
    mkSigma
      (LeCode-trans-n m u u' u''
        (max-Le-l (RANK u) (RANK v) m bx) (max-Le-l (RANK u') (RANK v') m by)
        (max-Le-l (RANK u'') (RANK v'') m bz)
        (fst cx) (fst cy) (fst cz) (fst xy) (fst yz))
      (LeCode-trans-n m v v' v''
        (max-Le-r (RANK u) (RANK v) m bx) (max-Le-r (RANK u') (RANK v') m by)
        (max-Le-r (RANK u'') (RANK v'') m bz)
        (snd cx) (snd cy) (snd cz) (snd xy) (snd yz))
  LeCode-trans-n (suc m) (Prd u v) (Prd u' v') (Fn _)      bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Prd u v) (Fn _)    z bx by bz cx cy cz () yz
  -- Fn
  LeCode-trans-n zero    (Fn g) y z () by bz cx cy cz xy yz
  LeCode-trans-n (suc m) (Fn g) Bot       z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (Fn g) (At _)    z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (Fn g) (Prd _ _) z bx by bz cx cy cz () yz
  LeCode-trans-n (suc m) (Fn g) (Fn h) Bot       bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Fn g) (Fn h) (At _)    bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Fn g) (Fn h) (Prd _ _) bx by bz cx cy cz xy ()
  LeCode-trans-n (suc m) (Fn g) (Fn h) (Fn k)    bx by bz cx cy cz xy yz =
    LeFunCode-trans-n m g h k bx by bz cx cy cz xy yz

  LeFunCode-trans-n : (m : Nat) (g h k : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m -> Le (RANKFun k) m ->
    CoherentFun g -> CoherentFun h -> CoherentFun k ->
    OB.leqf (suc m) g h -> OB.leqf (suc m) h k -> OB.leqf (suc m) g k
  LeFunCode-trans-n m nil         h k bg bh bk cohg cohh cohk gh hk = tt
  LeFunCode-trans-n m (cons p ps) h k bg bh bk cohg cohh cohk gh hk =
    mkSigma
      (LeCode-trans-n m (snd p) (OB.ev (suc m) h (fst p)) (OB.ev (suc m) k (fst p))
        (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) bg)
        (ev-bound m h (fst p) bh) (ev-bound m k (fst p) bk)
        (CFcons.val-coh cohg)
        (Coherent-EvalFun-n m h (fst p) bh
          (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
          cohh (CFcons.key-coh cohg))
        (Coherent-EvalFun-n m k (fst p) bk
          (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
          cohk (CFcons.key-coh cohg))
        (fst gh)
        (EvalFun-mon-n m h k (fst p) bh bk
          (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
          cohh cohk (CFcons.key-coh cohg) hk))
      (LeFunCode-trans-n m ps h k
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg)
        bh bk (CFcons.tail-coh cohg) cohh cohk (snd gh) hk)

  ----------------------------------------------------------------------
  -- monotonicity of application in the function
  ----------------------------------------------------------------------
  EvalFun-mon-n : (m : Nat) (h k : FinFun) (u : FinEl) ->
    Le (RANKFun h) m -> Le (RANKFun k) m -> Le (RANK u) m ->
    CoherentFun h -> CoherentFun k -> Coherent u ->
    OB.leqf (suc m) h k -> OB.leq m (OB.ev (suc m) h u) (OB.ev (suc m) k u)
  EvalFun-mon-n m nil         k u bh bk bu cohh cohk cu hk =
    leq-Bot-any m (OB.ev (suc m) k u)
  EvalFun-mon-n m (cons q qs) k u bh bk bu cohh cohk cu hk =
    EvalFun-mon-step-n m (OB.lei m (fst q) u) q qs k u refl
      (Le-trans (RANK (fst q)) (RANKFun (cons q qs)) m (rk-key q qs) bh)
      (Le-trans (RANK (snd q)) (RANKFun (cons q qs)) m (rk-val q qs) bh)
      (Le-trans (RANKFun qs) (RANKFun (cons q qs)) m (rk-tail q qs) bh)
      bk bu cohh cohk cu hk

  EvalFun-mon-step-n : (m : Nat) (w : Nat)
    (q : Pair FinEl FinEl) (qs k : FinFun) (u : FinEl) ->
    Eq w (OB.lei m (fst q) u) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun qs) m ->
    Le (RANKFun k) m -> Le (RANK u) m ->
    CoherentFun (cons q qs) -> CoherentFun k -> Coherent u ->
    OB.leqf (suc m) (cons q qs) k ->
    OB.leq m (evCombine w (snd q) (OB.ev (suc m) qs u)) (OB.ev (suc m) k u)
  EvalFun-mon-step-n m zero    q qs k u eq bkq bvq bqs bk bu cohh cohk cu hk =
    EvalFun-mon-n m qs k u bqs bk bu (CFcons.tail-coh cohh) cohk cu (snd hk)
  EvalFun-mon-step-n m (suc w) q qs k u eq bkq bvq bqs bk bu cohh cohk cu hk =
    leq-Sup-lub m (snd q) (OB.ev (suc m) qs u) (OB.ev (suc m) k u)
      (LeCode-trans-n m (snd q) (OB.ev (suc m) k (fst q)) (OB.ev (suc m) k u)
        bvq (ev-bound m k (fst q) bk) (ev-bound m k u bk)
        (CFcons.val-coh cohh)
        (Coherent-EvalFun-n m k (fst q) bk bkq cohk (CFcons.key-coh cohh))
        (Coherent-EvalFun-n m k u bk bu cohk cu)
        (fst hk)
        (EvalFun-mon-arg-n m k (fst q) u bk bkq bu
          (lei-sound m (fst q) u (Eq-transport isPos eq tt))
          cohk (CFcons.key-coh cohh) cu))
      (EvalFun-mon-n m qs k u bqs bk bu (CFcons.tail-coh cohh) cohk cu (snd hk))

  ----------------------------------------------------------------------
  -- monotonicity of application in the argument
  ----------------------------------------------------------------------
  EvalFun-mon-arg-n : (m : Nat) (k : FinFun) (u v : FinEl) ->
    Le (RANKFun k) m -> Le (RANK u) m -> Le (RANK v) m ->
    OB.leq m u v -> CoherentFun k -> Coherent u -> Coherent v ->
    OB.leq m (OB.ev (suc m) k u) (OB.ev (suc m) k v)
  EvalFun-mon-arg-n m nil         u v bk bu bv le cohk cu cv =
    leq-Bot-any m (OB.ev (suc m) nil v)
  EvalFun-mon-arg-n m (cons q qs) u v bk bu bv le cohk cu cv =
    EvalFun-mon-arg-step-n m (OB.lei m (fst q) u) q qs u v refl
      (Le-trans (RANK (fst q)) (RANKFun (cons q qs)) m (rk-key q qs) bk)
      (Le-trans (RANK (snd q)) (RANKFun (cons q qs)) m (rk-val q qs) bk)
      (Le-trans (RANKFun qs) (RANKFun (cons q qs)) m (rk-tail q qs) bk)
      bu bv le cohk cu cv

  EvalFun-mon-arg-step-n : (m : Nat) (w : Nat)
    (q : Pair FinEl FinEl) (qs : FinFun) (u v : FinEl) ->
    Eq w (OB.lei m (fst q) u) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun qs) m ->
    Le (RANK u) m -> Le (RANK v) m ->
    OB.leq m u v -> CoherentFun (cons q qs) -> Coherent u -> Coherent v ->
    OB.leq m (evCombine w (snd q) (OB.ev (suc m) qs u)) (OB.ev (suc m) (cons q qs) v)
  EvalFun-mon-arg-step-n m zero    q qs u v eq bkq bvq bqs bu bv le cohk cu cv =
    LeCode-trans-n m (OB.ev (suc m) qs u) (OB.ev (suc m) qs v)
                     (OB.ev (suc m) (cons q qs) v)
      (ev-bound m qs u bqs) (ev-bound m qs v bqs)
      (ev-bound m (cons q qs) v
        (Le-max-lub (RANK (fst q)) (max (RANK (snd q)) (RANKFun qs)) m bkq
          (Le-max-lub (RANK (snd q)) (RANKFun qs) m bvq bqs)))
      (Coherent-EvalFun-n m qs u bqs bu (CFcons.tail-coh cohk) cu)
      (Coherent-EvalFun-n m qs v bqs bv (CFcons.tail-coh cohk) cv)
      (Coherent-EvalFun-n m (cons q qs) v
        (Le-max-lub (RANK (fst q)) (max (RANK (snd q)) (RANKFun qs)) m bkq
          (Le-max-lub (RANK (snd q)) (RANKFun qs) m bvq bqs))
        bv cohk cv)
      (EvalFun-mon-arg-n m qs u v bqs bu bv le (CFcons.tail-coh cohk) cu cv)
      (EvalFun-cons-mono-n m q qs v bkq bvq bqs bv cohk cv)
  EvalFun-mon-arg-step-n m (suc x) q qs u v eq bkq bvq bqs bu bv le cohk cu cv =
    EvalFun-mon-arg-suc-n m x (OB.lei m (fst q) v) q qs u v eq refl
      bkq bvq bqs bu bv le cohk cu cv

  EvalFun-mon-arg-suc-n : (m : Nat) (x : Nat) (w2 : Nat)
    (q : Pair FinEl FinEl) (qs : FinFun) (u v : FinEl) ->
    Eq (suc x) (OB.lei m (fst q) u) ->
    Eq w2 (OB.lei m (fst q) v) ->
    Le (RANK (fst q)) m -> Le (RANK (snd q)) m -> Le (RANKFun qs) m ->
    Le (RANK u) m -> Le (RANK v) m ->
    OB.leq m u v -> CoherentFun (cons q qs) -> Coherent u -> Coherent v ->
    OB.leq m (Sup (snd q) (OB.ev (suc m) qs u)) (evCombine w2 (snd q) (OB.ev (suc m) qs v))
  EvalFun-mon-arg-suc-n m x zero q qs u v equ eqv bkq bvq bqs bu bv le cohk cu cv
    with Eq-transport isPos (Eq-sym eqv)
           (lei-complete m (fst q) v
             (LeCode-trans-n m (fst q) u v bkq bu bv
               (CFcons.key-coh cohk) cu cv
               (lei-sound m (fst q) u (Eq-transport isPos equ tt)) le))
  ... | ()
  EvalFun-mon-arg-suc-n m x (suc w2) q qs u v equ eqv bkq bvq bqs bu bv le cohk cu cv =
    let cohv      = CFcons.val-coh cohk
        cohrest   = CFcons.tail-coh cohk
        cw        = CFcons.compat cohk
        le-key-v  = LeCode-trans-n m (fst q) u v bkq bu bv
                      (CFcons.key-coh cohk) cu cv
                      (lei-sound m (fst q) u (Eq-transport isPos equ tt)) le
        coh-rest-u = Coherent-EvalFun-n m qs u bqs bu cohrest cu
        coh-rest-v = Coherent-EvalFun-n m qs v bqs bv cohrest cv
        comp-v    = Comp-value-EvalFun-n m q qs v bkq bv bqs le-key-v cv cohv cw
                      (coherentWith-to-compStepFun q qs cw)
        ih        = EvalFun-mon-arg-n m qs u v bqs bu bv le cohrest cu cv
        sup-left  = LeCode-Sup-left-n m (snd q) (OB.ev (suc m) qs v)
                      bvq (ev-bound m qs v bqs) comp-v cohv coh-rest-v
        sup-right = LeCode-Sup-right-n m (snd q) (OB.ev (suc m) qs v)
                      bvq (ev-bound m qs v bqs) comp-v cohv coh-rest-v
        coh-sup   = Coherent-Sup (snd q) (OB.ev (suc m) qs v) comp-v cohv coh-rest-v
        tail-le   = LeCode-trans-n m (OB.ev (suc m) qs u) (OB.ev (suc m) qs v)
                      (Sup (snd q) (OB.ev (suc m) qs v))
                      (ev-bound m qs u bqs) (ev-bound m qs v bqs)
                      (sup-bound m (snd q) (OB.ev (suc m) qs v) bvq (ev-bound m qs v bqs))
                      coh-rest-u coh-rest-v coh-sup ih sup-right
    in leq-Sup-lub m (snd q) (OB.ev (suc m) qs u) (Sup (snd q) (OB.ev (suc m) qs v))
         sup-left tail-le

  ----------------------------------------------------------------------
  -- append-left / append-right
  ----------------------------------------------------------------------
  LeFunCode-append-left-n : (m : Nat) (g h : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m ->
    CompFun g h -> CoherentFun g -> CoherentFun h ->
    OB.leqf (suc m) g (append g h)
  LeFunCode-append-left-n m nil         h bg bh comp cohg cohh = tt
  LeFunCode-append-left-n m (cons p ps) h bg bh comp cohg cohh =
    let coh-append = CoherentFun-append (cons p ps) h cohg cohh comp
    in mkSigma
      (LeFunCode-refl-head-step-n m (OB.lei m (fst p) (fst p)) p (append ps h) refl
        (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
        (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) bg)
        (append-bound m ps h
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg) bh)
        coh-append)
      (LeFunCode-cons-lift-n m ps p (append ps h)
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg)
        (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
        (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) bg)
        (append-bound m ps h
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg) bh)
        coh-append (CFcons.tail-coh cohg)
        (LeFunCode-append-left-n m ps h
          (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg) bh
          (snd comp) (CFcons.tail-coh cohg) cohh))

  LeFunCode-append-right-n : (m : Nat) (g h : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m ->
    CompFun g h -> CoherentFun g -> CoherentFun h ->
    OB.leqf (suc m) h (append g h)
  LeFunCode-append-right-n m g h bg bh comp cohg cohh =
    LeFunCode-append-right-go-n m g h h bg bh bh comp
      (CoherentFun-append g h cohg cohh comp) cohh
      (LeFunCode-refl-n m h bh cohh)

  LeFunCode-append-right-go-n : (m : Nat) (g h rest : FinFun) ->
    Le (RANKFun g) m -> Le (RANKFun h) m -> Le (RANKFun rest) m ->
    CompFun g h -> CoherentFun (append g rest) -> CoherentFun h ->
    OB.leqf (suc m) h rest -> OB.leqf (suc m) h (append g rest)
  LeFunCode-append-right-go-n m nil         h rest bg bh brest comp coh cohh le = le
  LeFunCode-append-right-go-n m (cons p ps) h rest bg bh brest comp coh cohh le =
    LeFunCode-cons-lift-n m h p (append ps rest)
      bh
      (Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m (rk-key p ps) bg)
      (Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m (rk-val p ps) bg)
      (append-bound m ps rest
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg) brest)
      coh cohh
      (LeFunCode-append-right-go-n m ps h rest
        (Le-trans (RANKFun ps) (RANKFun (cons p ps)) m (rk-tail p ps) bg) bh brest
        (snd comp) (CFcons.tail-coh coh) cohh le)
