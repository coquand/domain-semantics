{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/ObsInv.agda        (L5, part 1 -- inversion)
--
-- Because the observation relation is presented as an IDEAL, it is not
-- syntax-directed: obs-down and obs-sup can appear anywhere.  So
-- "invert the derivation at a CONS cell" is not a pattern match, and
-- the usual existential form of the inversion
--
--     Obs mu p rho w  ->  exists u v. Obs p1 u * Obs p2 v * w <= Prd u v
--
-- does NOT go through: its obs-sup case would need to JOIN two
-- observations of p1, i.e. it would need consistency.
--
-- The fix is to state inversion in SHAPE-DIRECTED form: a predicate on
-- the observed code, defined by cases on the code, saying what the code
-- must look like at that cell.  Then
--
--   * obs-down is handled by the shape's downward closure, and
--   * obs-sup by its closure under compatible Sup -- and there the side
--     condition Comp u v delivers exactly the componentwise
--     compatibility needed to join the SUB-observations.
--
-- So inversion costs no consistency at all.  This is the technical
-- payoff of the ideal presentation.
------------------------------------------------------------------------

module LAZY.ObsInv where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Obs
open import LAZY.ObsIdeal

------------------------------------------------------------------------
-- A cell holding (QUOTE a) can only be observed as Bot or as a.
------------------------------------------------------------------------

AtShape : Atom -> FinEl -> Set
AtShape a Bot       = Top
AtShape a (At b)    = AtEq b a
AtShape a (Prd _ _) = Empty
AtShape a (Fn _)    = Empty

private
  AtShape-down : (a : Atom) (u u' : FinEl) ->
    AtShape a u -> LeCode u' u -> AtShape a u'
  AtShape-down a Bot       Bot       s le = tt
  AtShape-down a Bot       (At c)    s ()
  AtShape-down a Bot       (Prd _ _) s ()
  AtShape-down a Bot       (Fn _)    s ()
  AtShape-down a (At b)    Bot       s le = tt
  AtShape-down a (At b)    (At c)    s le = AtEq-trans c b a le s
  AtShape-down a (At b)    (Prd _ _) s ()
  AtShape-down a (At b)    (Fn _)    s ()
  AtShape-down a (Prd _ _) u'        () le
  AtShape-down a (Fn _)    u'        () le

  AtShape-supAt : (a : Atom) (w : Nat) (b c : Atom) ->
    AtEq b a -> AtShape a (supAt w b c)
  AtShape-supAt a zero    b c s = tt
  AtShape-supAt a (suc n) b c s = s

  AtShape-sup : (a : Atom) (u v : FinEl) ->
    AtShape a u -> AtShape a v -> Comp u v -> AtShape a (Sup u v)
  AtShape-sup a Bot       v         su sv c = sv
  AtShape-sup a (At b)    Bot       su sv c = su
  AtShape-sup a (At b)    (At d)    su sv c = AtShape-supAt a (atEqN b d) b d su
  AtShape-sup a (At b)    (Prd _ _) su ()  c
  AtShape-sup a (At b)    (Fn _)    su ()  c
  AtShape-sup a (Prd _ _) v         ()  sv c
  AtShape-sup a (Fn _)    v         ()  sv c

inv-quote : (mu : Heap) (p : Addr) {rho : FinEnv} {a : Atom} {u : FinEl} ->
  Eq (mu p) (just (equote a)) -> Obs mu p rho u -> AtShape a u
inv-quote mu p q obs-bot                  = tt
inv-quote mu p q (obs-var q2)             = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-quote q2)           =
  AtEq-of-Eq _ _ (equote-inj (Eq-sym (cell-eq {mu = mu} {p = p} q q2)))
inv-quote mu p q (obs-cons q2 _ _)        = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-car q2 _)           = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-cdr q2 _)           = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-atom-T q2 _)        = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-atom-NIL q2 _)      = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-eq-T q2 _ _ _)      = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-eq-NIL q2 _ _ _)    = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-if-T q2 _ _)        = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-if-NIL q2 _ _)      = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-app q2 _ _ _)       = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-lam q2 _ _)         = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-label q2 _ _)       = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-funarg q2 _ _)      = absurd (cell-clash mu p q q2)
inv-quote mu p q (obs-plus q2 _ _)        = absurd (cell-clash mu p q q2)
inv-quote mu p {a = a} q (obs-down {u = u} {u' = u'} o cu le) =
  AtShape-down a u u' (inv-quote mu p q o) le
inv-quote mu p {a = a} q (obs-sup {u = u} {v = v} o1 o2 c) =
  AtShape-sup a u v (inv-quote mu p q o1) (inv-quote mu p q o2) c

------------------------------------------------------------------------
-- A cell holding (CONS p1 p2) can only be observed as Bot or as a pair
-- whose components are observations of p1 and p2.
------------------------------------------------------------------------

PrdShape : Heap -> Addr -> Addr -> FinEnv -> FinEl -> Set
PrdShape mu p1 p2 rho Bot       = Top
PrdShape mu p1 p2 rho (At _)    = Empty
PrdShape mu p1 p2 rho (Prd u v) = Pair (Obs mu p1 rho u) (Obs mu p2 rho v)
PrdShape mu p1 p2 rho (Fn _)    = Empty

private
  PrdShape-down : (mu : Heap) (p1 p2 : Addr) (rho : FinEnv) (u u' : FinEl) ->
    PrdShape mu p1 p2 rho u -> Coherent u' -> LeCode u' u ->
    PrdShape mu p1 p2 rho u'
  PrdShape-down mu p1 p2 rho Bot       Bot         s cu le = tt
  PrdShape-down mu p1 p2 rho Bot       (At _)      s cu ()
  PrdShape-down mu p1 p2 rho Bot       (Prd _ _)   s cu ()
  PrdShape-down mu p1 p2 rho Bot       (Fn _)      s cu ()
  PrdShape-down mu p1 p2 rho (At _)    u'          () cu le
  PrdShape-down mu p1 p2 rho (Prd u v) Bot         s cu le = tt
  PrdShape-down mu p1 p2 rho (Prd u v) (At _)      s cu ()
  PrdShape-down mu p1 p2 rho (Prd u v) (Prd u' v') s cu le =
    mkSigma (obs-down (fst s) (fst cu) (fst le))
            (obs-down (snd s) (snd cu) (snd le))
  PrdShape-down mu p1 p2 rho (Prd u v) (Fn _)      s cu ()
  PrdShape-down mu p1 p2 rho (Fn _)    u'          () cu le

  PrdShape-sup : (mu : Heap) (p1 p2 : Addr) (rho : FinEnv) (u v : FinEl) ->
    PrdShape mu p1 p2 rho u -> PrdShape mu p1 p2 rho v -> Comp u v ->
    PrdShape mu p1 p2 rho (Sup u v)
  PrdShape-sup mu p1 p2 rho Bot         v           su sv c = sv
  PrdShape-sup mu p1 p2 rho (At _)      v           ()  sv c
  PrdShape-sup mu p1 p2 rho (Prd u1 v1) Bot         su sv c = su
  PrdShape-sup mu p1 p2 rho (Prd u1 v1) (At _)      su ()  c
  PrdShape-sup mu p1 p2 rho (Prd u1 v1) (Prd u2 v2) su sv c =
    mkSigma (obs-sup (fst su) (fst sv) (fst c))
            (obs-sup (snd su) (snd sv) (snd c))
  PrdShape-sup mu p1 p2 rho (Prd u1 v1) (Fn _)      su ()  c
  PrdShape-sup mu p1 p2 rho (Fn _)      v           ()  sv c

inv-cons : (mu : Heap) (p : Addr) {p1 p2 : Addr} {rho : FinEnv} {u : FinEl} ->
  Eq (mu p) (just (econs p1 p2)) -> Obs mu p rho u -> PrdShape mu p1 p2 rho u
inv-cons mu p q obs-bot               = tt
inv-cons mu p q (obs-var q2)          = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-quote q2)        = absurd (cell-clash mu p q q2)
inv-cons mu p {p1} {p2} q (obs-cons {p1 = r1} {p2 = r2} q2 o1 o2) =
  mkSigma
    (Eq-transport (\ z -> Obs mu z _ _)
      (Eq-sym (econs-inj1 (cell-eq {mu = mu} {p = p} q q2))) o1)
    (Eq-transport (\ z -> Obs mu z _ _)
      (Eq-sym (econs-inj2 (cell-eq {mu = mu} {p = p} q q2))) o2)
inv-cons mu p q (obs-car q2 _)        = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-cdr q2 _)        = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-atom-T q2 _)     = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-atom-NIL q2 _)   = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-eq-T q2 _ _ _)   = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-eq-NIL q2 _ _ _) = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-if-T q2 _ _)     = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-if-NIL q2 _ _)   = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-app q2 _ _ _)    = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-lam q2 _ _)      = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-label q2 _ _)    = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-funarg q2 _ _)   = absurd (cell-clash mu p q q2)
inv-cons mu p q (obs-plus q2 _ _)     = absurd (cell-clash mu p q q2)
inv-cons mu p {p1} {p2} {rho} q (obs-down {u = u} {u' = u'} o cu le) =
  PrdShape-down mu p1 p2 rho u u' (inv-cons mu p q o) cu le
inv-cons mu p {p1} {p2} {rho} q (obs-sup {u = u} {v = v} o1 o2 c) =
  PrdShape-sup mu p1 p2 rho u v (inv-cons mu p q o1) (inv-cons mu p q o2) c

------------------------------------------------------------------------
-- A cell holding the variable x can only be observed below rho(x).
------------------------------------------------------------------------

VarShape : FinEnv -> Var -> FinEl -> Set
VarShape rho x u = LeCode u (lookupEnv rho x)

inv-var : (mu : Heap) (p : Addr) {rho : FinEnv} {x : Var} {u : FinEl} ->
  CohEnv rho -> Eq (mu p) (just (evar x)) -> Obs mu p rho u -> VarShape rho x u
inv-var mu p ce q obs-bot               = tt
inv-var mu p {rho} {x} ce q (obs-var {x = y} q2) =
  Eq-transport (\ z -> LeCode (lookupEnv rho z) (lookupEnv rho x))
    (evar-inj (cell-eq {mu = mu} {p = p} q q2))
    (LeCode-refl (lookupEnv rho x) (lookupEnv-Coh rho x ce))
inv-var mu p ce q (obs-quote q2)        = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-cons q2 _ _)     = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-car q2 _)        = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-cdr q2 _)        = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-atom-T q2 _)     = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-atom-NIL q2 _)   = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-eq-T q2 _ _ _)   = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-eq-NIL q2 _ _ _) = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-if-T q2 _ _)     = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-if-NIL q2 _ _)   = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-app q2 _ _ _)    = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-lam q2 _ _)      = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-label q2 _ _)    = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-funarg q2 _ _)   = absurd (cell-clash mu p q q2)
inv-var mu p ce q (obs-plus q2 _ _)     = absurd (cell-clash mu p q q2)
inv-var mu p {rho} {x} ce q (obs-down {u = u} {u' = u'} o cu le) =
  LeCode-trans u' u (lookupEnv rho x) cu (Obs-Coherent ce o)
    (lookupEnv-Coh rho x ce) le (inv-var mu p ce q o)
inv-var mu p {rho} {x} ce q (obs-sup {u = u} {v = v} o1 o2 c) =
  LeCode-Sup-lub u v (lookupEnv rho x)
    (inv-var mu p ce q o1) (inv-var mu p ce q o2)
