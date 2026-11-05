{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderStable.agda        (L1, part 3)
--
-- STABILITY: above the canonical RANK level the stage operations stop
-- changing, so the public order LeqC (read off at stage
-- suc (max (RANK u) (RANK v))) is stage-independent.
--
-- Port of MIN/Domain/OrderStable.agda.
------------------------------------------------------------------------

module LAZY.Domain.OrderStable where

open import LAZY.Domain.Basic
open import LAZY.Domain.OrderStage
open import LAZY.Domain.OrderProps

private
  min-cong : {w w' r r' : Nat} -> Eq w w' -> Eq r r' -> Eq (min w r) (min w' r')
  min-cong refl refl = refl

  evCombine-cong : (x : FinEl) {w w' : Nat} {r r' : FinEl} ->
    Eq w w' -> Eq r r' -> Eq (evCombine w x r) (evCombine w' x r')
  evCombine-cong x refl refl = refl

  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  RANKFun-cons-key : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANK (fst p)) (RANKFun (cons p ps))
  RANKFun-cons-key p ps = Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))

  RANKFun-cons-val : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANK (snd p)) (RANKFun (cons p ps))
  RANKFun-cons-val p ps =
    Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-l (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

  RANKFun-cons-tail : (p : Pair FinEl FinEl) (ps : FinFun) ->
    Le (RANKFun ps) (RANKFun (cons p ps))
  RANKFun-cons-tail p ps =
    Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
      (Le-max-r (RANK (snd p)) (RANKFun ps))
      (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))

record StabPack (n : Nat) : Set where
  field
    ev-st  : (h : FinFun) (u : FinEl) ->
             Le (suc (max (RANKFun h) (RANK u))) n ->
             Eq (OB.ev n h u) (OB.ev (suc n) h u)
    lei-st : (u v : FinEl) ->
             Le (max (RANK u) (RANK v)) n ->
             Eq (OB.lei n u v) (OB.lei (suc n) u v)
    lef-st : (g h : FinFun) ->
             Le (suc (max (RANKFun g) (RANKFun h))) n ->
             Eq (OB.lef n g h) (OB.lef (suc n) g h)

goodStab : (n : Nat) -> StabPack n
goodStab zero = record { ev-st = evS0 ; lei-st = leiS0 ; lef-st = lefS0 }
  where
    evS0 : (h : FinFun) (u : FinEl) ->
           Le (suc (max (RANKFun h) (RANK u))) zero ->
           Eq (OB.ev zero h u) (OB.ev (suc zero) h u)
    evS0 h u ()

    lefS0 : (g h : FinFun) ->
            Le (suc (max (RANKFun g) (RANKFun h))) zero ->
            Eq (OB.lef zero g h) (OB.lef (suc zero) g h)
    lefS0 g h ()

    leiS0 : (u v : FinEl) ->
            Le (max (RANK u) (RANK v)) zero ->
            Eq (OB.lei zero u v) (OB.lei (suc zero) u v)
    leiS0 Bot        v         _ = refl
    leiS0 (At a)     Bot       _ = refl
    leiS0 (At a)     (At b)    _ = refl
    leiS0 (At a)     (Prd _ _) _ = refl
    leiS0 (At a)     (Fn _)    _ = refl
    leiS0 (Prd _ _)  Bot       ()
    leiS0 (Prd _ _)  (At _)    ()
    leiS0 (Prd _ _)  (Prd _ _) ()
    leiS0 (Prd _ _)  (Fn _)    ()
    leiS0 (Fn _)     Bot       ()
    leiS0 (Fn _)     (At _)    ()
    leiS0 (Fn _)     (Prd _ _) ()
    leiS0 (Fn _)     (Fn _)    ()

goodStab (suc m) = record { ev-st = evS ; lei-st = leiS ; lef-st = lefS }
  where
    ih : StabPack m
    ih = goodStab m

    ihlei : (u v : FinEl) -> Le (max (RANK u) (RANK v)) m ->
            Eq (OB.lei m u v) (OB.lei (suc m) u v)
    ihlei = StabPack.lei-st ih

    evS : (h : FinFun) (u : FinEl) ->
          Le (suc (max (RANKFun h) (RANK u))) (suc m) ->
          Eq (OB.ev (suc m) h u) (OB.ev (suc (suc m)) h u)
    evS nil         u _    = refl
    evS (cons p ps) u cond =
      evCombine-cong (snd p)
        (ihlei (fst p) u
          (Le-trans (max (RANK (fst p)) (RANK u))
                    (max (RANKFun (cons p ps)) (RANK u)) m
            (max-mono (RANK (fst p)) (RANK u) (RANKFun (cons p ps)) (RANK u)
              (RANKFun-cons-key p ps) (Le-refl (RANK u)))
            cond))
        (evS ps u
          (Le-trans (max (RANKFun ps) (RANK u))
                    (max (RANKFun (cons p ps)) (RANK u)) m
            (max-mono (RANKFun ps) (RANK u) (RANKFun (cons p ps)) (RANK u)
              (RANKFun-cons-tail p ps) (Le-refl (RANK u)))
            cond))

    lefS : (g h : FinFun) ->
           Le (suc (max (RANKFun g) (RANKFun h))) (suc m) ->
           Eq (OB.lef (suc m) g h) (OB.lef (suc (suc m)) g h)
    lefS nil         h _    = refl
    lefS (cons p ps) h cond =
      let rfg  = max (RANKFun (cons p ps)) (RANKFun h)
          rfgT = max (RANKFun ps) (RANKFun h)
          E1   = OB.ev (suc m) h (fst p)
          E2   = OB.ev (suc (suc m)) h (fst p)
          hRk  : Le (RANKFun h) m
          hRk  = max-Le-r (RANKFun (cons p ps)) (RANKFun h) m cond
          gRk  : Le (RANKFun (cons p ps)) m
          gRk  = max-Le-l (RANKFun (cons p ps)) (RANKFun h) m cond
          keyRk : Le (RANK (fst p)) m
          keyRk = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m
                    (RANKFun-cons-key p ps) gRk
          valRk : Le (RANK (snd p)) m
          valRk = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m
                    (RANKFun-cons-val p ps) gRk
          E1Rk : Le (RANK E1) m
          E1Rk = Le-trans (RANK E1) (RANKFun h) m (RANK-ev (suc m) h (fst p)) hRk
          evEq : Eq E1 E2
          evEq = evS h (fst p)
                   (Le-max-lub (RANKFun h) (RANK (fst p)) m hRk keyRk)
          leiEq1 : Eq (OB.lei m (snd p) E1) (OB.lei (suc m) (snd p) E1)
          leiEq1 = ihlei (snd p) E1 (Le-max-lub (RANK (snd p)) (RANK E1) m valRk E1Rk)
          leiEq2 : Eq (OB.lei (suc m) (snd p) E1) (OB.lei (suc m) (snd p) E2)
          leiEq2 = Eq-cong (OB.lei (suc m) (snd p)) evEq
          firstEq : Eq (OB.lei m (snd p) E1) (OB.lei (suc m) (snd p) E2)
          firstEq = Eq-trans leiEq1 leiEq2
      in min-cong firstEq
           (lefS ps h
             (Le-trans rfgT rfg m
               (max-mono (RANKFun ps) (RANKFun h) (RANKFun (cons p ps)) (RANKFun h)
                 (RANKFun-cons-tail p ps) (Le-refl (RANKFun h)))
               cond))

    leiS : (u v : FinEl) ->
           Le (max (RANK u) (RANK v)) (suc m) ->
           Eq (OB.lei (suc m) u v) (OB.lei (suc (suc m)) u v)
    leiS Bot        v           _    = refl
    leiS (At a)     Bot         _    = refl
    leiS (At a)     (At b)      _    = refl
    leiS (At a)     (Prd _ _)   _    = refl
    leiS (At a)     (Fn _)      _    = refl
    leiS (Prd _ _)  Bot         _    = refl
    leiS (Prd _ _)  (At _)      _    = refl
    leiS (Prd u v)  (Prd u' v') cond =
      let bigL = max (RANK u) (RANK v)
          bigR = max (RANK u') (RANK v')
          bigLle : Le bigL m
          bigLle = max-Le-l bigL bigR m cond
          bigRle : Le bigR m
          bigRle = max-Le-r bigL bigR m cond
          uRk : Le (RANK u) m
          uRk = max-Le-l (RANK u) (RANK v) m bigLle
          vRk : Le (RANK v) m
          vRk = max-Le-r (RANK u) (RANK v) m bigLle
          u'Rk : Le (RANK u') m
          u'Rk = max-Le-l (RANK u') (RANK v') m bigRle
          v'Rk : Le (RANK v') m
          v'Rk = max-Le-r (RANK u') (RANK v') m bigRle
      in min-cong
           (ihlei u u' (Le-max-lub (RANK u) (RANK u') m uRk u'Rk))
           (ihlei v v' (Le-max-lub (RANK v) (RANK v') m vRk v'Rk))
    leiS (Prd _ _)  (Fn _)      _    = refl
    leiS (Fn _)     Bot         _    = refl
    leiS (Fn _)     (At _)      _    = refl
    leiS (Fn _)     (Prd _ _)   _    = refl
    leiS (Fn g)     (Fn h)      cond = lefS g h cond

------------------------------------------------------------------------
-- Set-valued stability (one step), via lei-stability + decidability.
------------------------------------------------------------------------

leq-stable-fwd : (n : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) n ->
  OB.leq n u v -> OB.leq (suc n) u v
leq-stable-fwd n u v cond p =
  lei-sound (suc n) u v
    (Eq-transport isPos (StabPack.lei-st (goodStab n) u v cond)
      (lei-complete n u v p))

leq-stable-bwd : (n : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) n ->
  OB.leq (suc n) u v -> OB.leq n u v
leq-stable-bwd n u v cond p =
  lei-sound n u v
    (Eq-transport isPos (Eq-sym (StabPack.lei-st (goodStab n) u v cond))
      (lei-complete (suc n) u v p))

------------------------------------------------------------------------
-- Stage-shift: leq is stage-independent at any two stages above the
-- canonical level max (RANK u) (RANK v).
------------------------------------------------------------------------

private
  plus : Nat -> Nat -> Nat
  plus zero    a = a
  plus (suc g) a = suc (plus g a)

  plus-0 : (g : Nat) -> Eq (plus g zero) g
  plus-0 zero    = refl
  plus-0 (suc g) = Eq-cong suc (plus-0 g)

  plus-suc : (g a : Nat) -> Eq (plus g (suc a)) (suc (plus g a))
  plus-suc zero    a = refl
  plus-suc (suc g) a = Eq-cong suc (plus-suc g a)

  Le-plus : (g a : Nat) -> Le a (plus g a)
  Le-plus zero    a = Le-refl a
  Le-plus (suc g) a = Le-suc a (plus g a) (Le-plus g a)

  Le-gap : (a b : Nat) -> Le a b -> Sigma Nat (\ g -> Eq b (plus g a))
  Le-gap zero    b       lab = mkSigma b (Eq-sym (plus-0 b))
  Le-gap (suc a) zero    ()
  Le-gap (suc a) (suc b) lab =
    let r = Le-gap a b lab
    in mkSigma (fst r)
         (Eq-transport (\ x -> Eq (suc b) x) (Eq-sym (plus-suc (fst r) a))
           (Eq-cong suc (snd r)))

leq-lift : (g j : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) j ->
  OB.leq j u v -> OB.leq (plus g j) u v
leq-lift zero    j u v bnd p = p
leq-lift (suc g) j u v bnd p =
  leq-stable-fwd (plus g j) u v
    (Le-trans (max (RANK u) (RANK v)) j (plus g j) bnd (Le-plus g j))
    (leq-lift g j u v bnd p)

leq-lower : (g j : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) j ->
  OB.leq (plus g j) u v -> OB.leq j u v
leq-lower zero    j u v bnd p = p
leq-lower (suc g) j u v bnd p =
  leq-lower g j u v bnd
    (leq-stable-bwd (plus g j) u v
      (Le-trans (max (RANK u) (RANK v)) j (plus g j) bnd (Le-plus g j)) p)

leq-shift : (j k : Nat) (u v : FinEl) ->
  Le (max (RANK u) (RANK v)) j -> Le (max (RANK u) (RANK v)) k ->
  OB.leq j u v -> OB.leq k u v
leq-shift j k u v bj bk p =
  let M  = max (RANK u) (RANK v)
      gj = Le-gap M j bj
      gk = Le-gap M k bk
      p-pj = Eq-transport (\ x -> OB.leq x u v) (snd gj) p
      p-c  = leq-lower (fst gj) M u v (Le-refl M) p-pj
      p-pk = leq-lift (fst gk) M u v (Le-refl M) p-c
  in Eq-transport (\ x -> OB.leq x u v) (Eq-sym (snd gk)) p-pk

------------------------------------------------------------------------
-- Public order LeqC at the canonical stage.
------------------------------------------------------------------------

leqC-from : (j : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) j ->
  OB.leq j u v -> LeqC u v
leqC-from j u v bnd p =
  leq-shift j (suc (max (RANK u) (RANK v))) u v bnd
    (Le-suc (max (RANK u) (RANK v)) (max (RANK u) (RANK v))
      (Le-refl (max (RANK u) (RANK v)))) p

leqC-to : (j : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) j ->
  LeqC u v -> OB.leq j u v
leqC-to j u v bnd p =
  leq-shift (suc (max (RANK u) (RANK v))) j u v
    (Le-suc (max (RANK u) (RANK v)) (max (RANK u) (RANK v))
      (Le-refl (max (RANK u) (RANK v)))) bnd p

Leq-Bot : (v : FinEl) -> LeqC Bot v
Leq-Bot v = tt

leiC-sound : (u v : FinEl) -> isPos (leiC u v) -> LeqC u v
leiC-sound u v = lei-sound (suc (max (RANK u) (RANK v))) u v

leiC-complete : (u v : FinEl) -> LeqC u v -> isPos (leiC u v)
leiC-complete u v = lei-complete (suc (max (RANK u) (RANK v))) u v

------------------------------------------------------------------------
-- Numeric stage-shift for lei (needed by the EvalFun = OB.ev bridge).
------------------------------------------------------------------------

lei-lift : (g j : Nat) (u v : FinEl) -> Le (max (RANK u) (RANK v)) j ->
  Eq (OB.lei j u v) (OB.lei (plus g j) u v)
lei-lift zero    j u v bnd = refl
lei-lift (suc g) j u v bnd =
  Eq-trans (lei-lift g j u v bnd)
    (StabPack.lei-st (goodStab (plus g j)) u v
      (Le-trans (max (RANK u) (RANK v)) j (plus g j) bnd (Le-plus g j)))

lei-shift : (j k : Nat) (u v : FinEl) ->
  Le (max (RANK u) (RANK v)) j -> Le (max (RANK u) (RANK v)) k ->
  Eq (OB.lei j u v) (OB.lei k u v)
lei-shift j k u v bj bk =
  let M  = max (RANK u) (RANK v)
      gj = Le-gap M j bj
      gk = Le-gap M k bk
      ej : Eq (OB.lei M u v) (OB.lei j u v)
      ej = Eq-transport (\ x -> Eq (OB.lei M u v) (OB.lei x u v))
             (Eq-sym (snd gj)) (lei-lift (fst gj) M u v (Le-refl M))
      ek : Eq (OB.lei M u v) (OB.lei k u v)
      ek = Eq-transport (\ x -> Eq (OB.lei M u v) (OB.lei x u v))
             (Eq-sym (snd gk)) (lei-lift (fst gk) M u v (Le-refl M))
  in Eq-trans (Eq-sym ej) ek
