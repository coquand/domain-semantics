{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PropCodes.agda  (MINPROP/ — Pi + U + Prop)
--
-- Structural facts about the stage-free predicate IsProp (MemStage):
-- the codes of propositions are closed under Sup and EvalFun, and are
-- downward closed for the order.  None of this mentions membership, so
-- it is plain structural recursion on FinEl / FinFun.
--
-- NO postulates.
------------------------------------------------------------------------

module MINPROP.Domain.PropCodes where

open import MINPROP.Domain.Basic
  using ( Top ; tt ; Empty ; Nat ; zero ; suc
        ; Pair ; mkSigma ; fst ; snd
        ; FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MINPROP.Domain.Order
  using ( Sup ; append ; EvalFun ; EvalFun-step ; leiC ; LeCode ; LeFunCode )
open import MINPROP.Domain.MemStage using ( IsProp ; IsPropFun )

IsPropFun-append : (f g : FinFun) -> IsPropFun f -> IsPropFun g -> IsPropFun (append f g)
IsPropFun-append nil         g pf pg = pg
IsPropFun-append (cons p ps) g pf pg = mkSigma (fst pf) (IsPropFun-append ps g (snd pf) pg)

IsProp-Sup : (a b : FinEl) -> IsProp a -> IsProp b -> IsProp (Sup a b)
IsProp-Sup Bot          b            pa pb = pb
IsProp-Sup UCode        b            ()
IsProp-Sup PropCode     b            ()
IsProp-Sup (FunEl g)    b            ()
IsProp-Sup (PiCode a f) Bot          pa pb = pa
IsProp-Sup (PiCode a f) UCode        pa pb = tt
IsProp-Sup (PiCode a f) PropCode     pa pb = tt
IsProp-Sup (PiCode a f) (FunEl h)    pa pb = tt
IsProp-Sup (PiCode a f) (PiCode b g) pa pb = IsPropFun-append f g pa pb

mutual
  IsProp-EvalFun : (f : FinFun) (x : FinEl) -> IsPropFun f -> IsProp (EvalFun f x)
  IsProp-EvalFun nil         x pf = tt
  IsProp-EvalFun (cons p ps) x pf = IsProp-EvalFun-step (leiC (fst p) x) (snd p) ps x (fst pf) (snd pf)

  IsProp-EvalFun-step : (n : Nat) (v : FinEl) (ps : FinFun) (x : FinEl) ->
    IsProp v -> IsPropFun ps -> IsProp (EvalFun-step n v ps x)
  IsProp-EvalFun-step zero    v ps x pv pps = IsProp-EvalFun ps x pps
  IsProp-EvalFun-step (suc n) v ps x pv pps = IsProp-Sup v (EvalFun ps x) pv (IsProp-EvalFun ps x pps)

mutual
  IsProp-down : (a b : FinEl) -> LeCode a b -> IsProp b -> IsProp a
  IsProp-down Bot          b            le pb = tt
  IsProp-down UCode        UCode        le ()
  IsProp-down PropCode     PropCode     le ()
  IsProp-down (FunEl g)    (FunEl h)    le ()
  IsProp-down (PiCode c g) (PiCode b h) le pb = IsPropFun-down g h (snd le) pb

  IsPropFun-down : (g h : FinFun) -> LeFunCode g h -> IsPropFun h -> IsPropFun g
  IsPropFun-down nil         h le ph = tt
  IsPropFun-down (cons p ps) h le ph =
    mkSigma (IsProp-down (snd p) (EvalFun h (fst p)) (fst le) (IsProp-EvalFun h (fst p) ph))
            (IsPropFun-down ps h (snd le) ph)
