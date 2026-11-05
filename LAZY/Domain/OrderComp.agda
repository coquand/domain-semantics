{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderComp.agda        (L1, part 5)
--
-- Structural Comp / Coherent / Sup algebra.  Stage-free: none of this
-- mentions the order or application.
--
-- Port of MIN/Domain/OrderComp.agda, restricted to what the order
-- property pack actually consumes (comp-Sup, comp-Sup-sym, Comp-sym,
-- Comp-refl, Coherent-Sup).
--
-- The atom clauses are the one new shape: Sup (At a) (At b) is guarded
-- by the decision atEqN a b, so each atom case is discharged by a small
-- lemma quantified over that decision.
------------------------------------------------------------------------

module LAZY.Domain.OrderComp where

open import LAZY.Domain.Basic
open import LAZY.Domain.OrderStage

------------------------------------------------------------------------
-- Sup with Bot, congruences
------------------------------------------------------------------------

Sup-Bot-l : (v : FinEl) -> Eq (Sup Bot v) v
Sup-Bot-l Bot       = refl
Sup-Bot-l (At a)    = refl
Sup-Bot-l (Prd u v) = refl
Sup-Bot-l (Fn g)    = refl

Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot       = refl
Sup-Bot-r (At a)    = refl
Sup-Bot-r (Prd u v) = refl
Sup-Bot-r (Fn g)    = refl

cons-eq : {p q : Pair FinEl FinEl} {ps qs : FinFun} ->
  Eq p q -> Eq ps qs -> Eq (cons p ps) (cons q qs)
cons-eq refl refl = refl

append-assoc : (f g h : FinFun) ->
  Eq (append f (append g h)) (append (append f g) h)
append-assoc nil         g h = refl
append-assoc (cons p ps) g h = cons-eq refl (append-assoc ps g h)

------------------------------------------------------------------------
-- Comp with Bot
------------------------------------------------------------------------

comp-Bot-r : (u : FinEl) -> Comp u Bot
comp-Bot-r Bot       = tt
comp-Bot-r (At a)    = tt
comp-Bot-r (Prd u v) = tt
comp-Bot-r (Fn g)    = tt

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot       = tt
comp-Bot-l (At a)    = tt
comp-Bot-l (Prd u v) = tt
comp-Bot-l (Fn g)    = tt

------------------------------------------------------------------------
-- CompFun / CompStepFun append
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- comp-Sup  (structural on the first FinEl arg)
------------------------------------------------------------------------

private
  -- Comp (At a) (Sup (At b) (At c)), given only At a comp At b.
  comp-supAt : (w : Nat) (a b c : Atom) -> AtEq a b -> Comp (At a) (supAt w b c)
  comp-supAt zero    a b c ab = tt
  comp-supAt (suc n) a b c ab = ab

comp-Sup : (a b c : FinEl) -> Comp a b -> Comp a c -> Comp a (Sup b c)
comp-Sup Bot b c ab ac = comp-Bot-l (Sup b c)
comp-Sup (At a)    Bot         c ab ac = ac
comp-Sup (At a)    (At b)      Bot       ab ac = ab
comp-Sup (At a)    (At b)      (At c)    ab ac = comp-supAt (atEqN b c) a b c ab
comp-Sup (At a)    (At b)      (Prd _ _) ab ()
comp-Sup (At a)    (At b)      (Fn _)    ab ()
comp-Sup (At a)    (Prd _ _)   c ()  ac
comp-Sup (At a)    (Fn _)      c ()  ac
comp-Sup (Prd u v) Bot         c ab ac = ac
comp-Sup (Prd u v) (At _)      c ()  ac
comp-Sup (Prd u v) (Prd u' v') Bot         ab ac = ab
comp-Sup (Prd u v) (Prd u' v') (At _)      ab ()
comp-Sup (Prd u v) (Prd u' v') (Prd u'' v'') ab ac =
  mkSigma (comp-Sup u u' u'' (fst ab) (fst ac))
          (comp-Sup v v' v'' (snd ab) (snd ac))
comp-Sup (Prd u v) (Prd u' v') (Fn _)      ab ()
comp-Sup (Prd u v) (Fn _)      c ()  ac
comp-Sup (Fn g)    Bot         c ab ac = ac
comp-Sup (Fn g)    (At _)      c ()  ac
comp-Sup (Fn g)    (Prd _ _)   c ()  ac
comp-Sup (Fn g)    (Fn h)      Bot       ab ac = ab
comp-Sup (Fn g)    (Fn h)      (At _)    ab ()
comp-Sup (Fn g)    (Fn h)      (Prd _ _) ab ()
comp-Sup (Fn g)    (Fn h)      (Fn j)    ab ac = compFun-append g h j ab ac

------------------------------------------------------------------------
-- Comp-sym
------------------------------------------------------------------------

mutual
  Comp-sym : (u v : FinEl) -> Comp u v -> Comp v u
  Comp-sym Bot       Bot         c = tt
  Comp-sym Bot       (At b)      c = tt
  Comp-sym Bot       (Prd _ _)   c = tt
  Comp-sym Bot       (Fn h)      c = tt
  Comp-sym (At a)    Bot         c = tt
  Comp-sym (At a)    (At b)      c = AtEq-sym a b c
  Comp-sym (At a)    (Prd _ _)   ()
  Comp-sym (At a)    (Fn h)      ()
  Comp-sym (Prd u v) Bot         c = tt
  Comp-sym (Prd u v) (At b)      ()
  Comp-sym (Prd u v) (Prd u' v') c =
    mkSigma (Comp-sym u u' (fst c)) (Comp-sym v v' (snd c))
  Comp-sym (Prd u v) (Fn h)      ()
  Comp-sym (Fn g)    Bot         c = tt
  Comp-sym (Fn g)    (At b)      ()
  Comp-sym (Fn g)    (Prd _ _)   ()
  Comp-sym (Fn g)    (Fn h)      c = CompFun-sym g h c

  CompFun-sym : (g h : FinFun) -> CompFun g h -> CompFun h g
  CompFun-sym g nil        cf = tt
  CompFun-sym g (cons t ts) cf =
    mkSigma (CompFun-sym-col g t ts cf)
            (CompFun-sym g ts (CompFun-drop-col g t ts cf))

  CompFun-sym-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompStepFun t g
  CompFun-sym-col nil        t ts cf = tt
  CompFun-sym-col (cons s ss) t ts cf =
    mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst (fst cf) (Comp-sym (fst t) (fst s) c)))
            (CompFun-sym-col ss t ts (snd cf))

  CompFun-drop-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompFun g ts
  CompFun-drop-col nil        t ts cf = tt
  CompFun-drop-col (cons s ss) t ts cf =
    mkSigma (snd (fst cf)) (CompFun-drop-col ss t ts (snd cf))

------------------------------------------------------------------------
-- coherentWith <-> compStepFun
------------------------------------------------------------------------

coherentWith-to-compStepFun : (q : Pair FinEl FinEl) (qs : FinFun) ->
  CoherentWith q qs -> CompStepFun q qs
coherentWith-to-compStepFun q nil        cw = tt
coherentWith-to-compStepFun q (cons r rs) cw =
  mkSigma (fst cw) (coherentWith-to-compStepFun q rs (snd cw))

compStepFun-to-coherentWith : (q : Pair FinEl FinEl) (h : FinFun) ->
  CompStepFun q h -> CoherentWith q h
compStepFun-to-coherentWith q nil        csf = tt
compStepFun-to-coherentWith q (cons r rs) csf =
  mkSigma (fst csf) (compStepFun-to-coherentWith q rs (snd csf))

coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
coherentWith-append q nil        h cw1 cw2 = cw2
coherentWith-append q (cons r rs) h cw1 cw2 =
  mkSigma (fst cw1) (coherentWith-append q rs h (snd cw1) cw2)

------------------------------------------------------------------------
-- Comp-refl
------------------------------------------------------------------------

CompFun-cons-right : (s : Pair FinEl FinEl) (ss hs : FinFun) ->
  CoherentWith s ss -> CompFun ss hs -> CompFun ss (cons s hs)
CompFun-cons-right s nil        hs cw cf = tt
CompFun-cons-right s (cons t ts) hs cw cf =
  mkSigma (mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst cw (Comp-sym (fst t) (fst s) c)))
                   (fst cf))
          (CompFun-cons-right s ts hs (snd cw) (snd cf))

mutual
  Comp-refl : (v : FinEl) -> Coherent v -> Comp v v
  Comp-refl Bot       coh = tt
  Comp-refl (At a)    coh = AtEq-refl a
  Comp-refl (Prd u v) coh =
    mkSigma (Comp-refl u (fst coh)) (Comp-refl v (snd coh))
  Comp-refl (Fn g)    coh = CompFun-refl g coh

  CompFun-refl : (g : FinFun) -> CoherentFun g -> CompFun g g
  CompFun-refl nil        coh = tt
  CompFun-refl (cons s ss) coh =
    mkSigma (mkSigma (\ _ -> Comp-refl (snd s) (CFcons.val-coh coh))
                     (coherentWith-to-compStepFun s ss (CFcons.compat coh)))
            (CompFun-cons-right s ss ss (CFcons.compat coh)
              (CompFun-refl ss (CFcons.tail-coh coh)))

------------------------------------------------------------------------
-- comp-Sup-sym
------------------------------------------------------------------------

comp-Sup-sym : (a b v : FinEl) -> Comp a v -> Comp b v -> Comp (Sup a b) v
comp-Sup-sym a b v ca cb =
  Comp-sym v (Sup a b) (comp-Sup v a b (Comp-sym a v ca) (Comp-sym b v cb))

------------------------------------------------------------------------
-- Coherent-Sup
------------------------------------------------------------------------

private
  coh-supAt : (w : Nat) (a b : Atom) -> Coherent (supAt w a b)
  coh-supAt zero    a b = tt
  coh-supAt (suc n) a b = tt

mutual
  Coherent-Sup : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    Coherent (Sup a b)
  Coherent-Sup Bot       b           comp coha cohb = cohb
  Coherent-Sup (At a)    Bot         comp coha cohb = tt
  Coherent-Sup (At a)    (At b)      comp coha cohb = coh-supAt (atEqN a b) a b
  Coherent-Sup (At a)    (Prd _ _)   ()   coha cohb
  Coherent-Sup (At a)    (Fn h)      ()   coha cohb
  Coherent-Sup (Prd u v) Bot         comp coha cohb = coha
  Coherent-Sup (Prd u v) (At b)      ()   coha cohb
  Coherent-Sup (Prd u v) (Prd u' v') comp coha cohb =
    mkSigma (Coherent-Sup u u' (fst comp) (fst coha) (fst cohb))
            (Coherent-Sup v v' (snd comp) (snd coha) (snd cohb))
  Coherent-Sup (Prd u v) (Fn h)      ()   coha cohb
  Coherent-Sup (Fn g)    Bot         comp coha cohb = coha
  Coherent-Sup (Fn g)    (At b)      ()   coha cohb
  Coherent-Sup (Fn g)    (Prd _ _)   ()   coha cohb
  Coherent-Sup (Fn g)    (Fn h)      comp coha cohb =
    CoherentFun-append g h coha cohb comp

  CoherentFun-append : (g h : FinFun) ->
    CoherentFun g -> CoherentFun h -> CompFun g h ->
    CoherentFun (append g h)
  CoherentFun-append nil        h cohg cohh cgh = cohh
  CoherentFun-append (cons p ps) h cohg cohh cgh =
    mkCF (CFcons.key-coh cohg) (CFcons.val-coh cohg) (CFcons.val-nbot cohg)
         (coherentWith-append p ps h (CFcons.compat cohg)
           (compStepFun-to-coherentWith p h (fst cgh)))
         (CoherentFun-append ps h (CFcons.tail-coh cohg) cohh (snd cgh))
