{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecFun
--
-- Function-parameterised primitive recursion.  The recursion chain that
-- proves ultimate obstination of  prec g h  only ever uses the base and
-- step through their FINITE interpretations  evalF g / evalF h  (plus the
-- monotonicity and stability of those, and the obstination hypotheses).
-- It never inspects the PR syntax of g or h.
--
-- Abstracting that interface out - a base function G, a step function H,
-- their monotonicity / stability / obstination - lets the whole chain be
-- restated over arbitrary G, H.  The top-level `prop1` then instantiates
-- G, H with the arity-guarded interpretations of the sub-terms (which ARE
-- total and obstinate), sidestepping the fact that  evalF g / evalF h  are
-- not obstinate at out-of-arity tuples.
--
-- `precFun G H` mirrors `precF g h`; on  G = evalF g, H = evalF h  the two
-- agree (`precFun-eq`), so results proved over the abstract chain transport
-- back to the concrete interpreter.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecFun where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Meet using (Bnd ; BndT ; meetF ; meetT)
open import OBSTINATION.PR using (PR ; prec ; evalF ; precF)
open import OBSTINATION.Property using (UO ; UOall)
open import OBSTINATION.Mono using (evalF-mono ; LeF-fbot0)
open import OBSTINATION.CompPull using (Mono)

------------------------------------------------------------------------
-- Stability of an abstract finite function (mirrors Stability.stable)
------------------------------------------------------------------------

Stable : (FTup -> FEl) -> Set
Stable f = {A B : FTup} -> BndT A B -> Eq (f (meetT A B)) (meetF (f A) (f B))

------------------------------------------------------------------------
-- The function-parameterised recursion operator (mirrors PR.precF)
------------------------------------------------------------------------

precFun : (FTup -> FEl) -> (FTup -> FEl) -> FEl -> FTup -> FEl
precFun G H (fbot zero)    Y = fbot zero
precFun G H (fbot (suc j)) Y = H (cons (fbot j) (cons (precFun G H (fbot j) Y) Y))
precFun G H (fcpl zero)    Y = G Y
precFun G H (fcpl (suc j)) Y = H (cons (fcpl j) (cons (precFun G H (fcpl j) Y) Y))

-- as a function of a whole tuple (mirrors  evalF (prec g h))
PF : (FTup -> FEl) -> (FTup -> FEl) -> FTup -> FEl
PF G H nil        = fbot zero
PF G H (cons a Y) = precFun G H a Y

------------------------------------------------------------------------
-- Agreement with the concrete interpreter on  G = evalF g, H = evalF h
------------------------------------------------------------------------

precFun-eq : (g h : PR) (a : FEl) (Y : FTup) ->
  Eq (precFun (evalF g) (evalF h) a Y) (precF g h a Y)
precFun-eq g h (fbot zero)    Y = refl
precFun-eq g h (fbot (suc j)) Y =
  Eq-cong (\ r -> evalF h (cons (fbot j) (cons r Y))) (precFun-eq g h (fbot j) Y)
precFun-eq g h (fcpl zero)    Y = refl
precFun-eq g h (fcpl (suc j)) Y =
  Eq-cong (\ r -> evalF h (cons (fcpl j) (cons r Y))) (precFun-eq g h (fcpl j) Y)

PF-eq : (g h : PR) (X : FTup) ->
  Eq (PF (evalF g) (evalF h) X) (evalF (prec g h) X)
PF-eq g h nil        = refl
PF-eq g h (cons a Y) = precFun-eq g h a Y

------------------------------------------------------------------------
-- Monotonicity of the abstract recursion (port of Mono.precF-mono)
------------------------------------------------------------------------

precFun-mono : (G H : FTup -> FEl) -> Mono G -> Mono H ->
  {a a' : FEl} {Y Y' : FTup} ->
  LeF a a' -> LeFTup Y Y' -> LeF (precFun G H a Y) (precFun G H a' Y')
precFun-mono G H mg mh {fbot zero}    {fbot k}       {Y} {Y'} la lY =
  LeF-fbot0 (precFun G H (fbot k) Y')
precFun-mono G H mg mh {fbot (suc j)} {fbot zero}    {Y} {Y'} () lY
precFun-mono G H mg mh {fbot (suc j)} {fbot (suc k)} {Y} {Y'} la lY =
  mh {cons (fbot j) (cons (precFun G H (fbot j) Y) Y)}
     {cons (fbot k) (cons (precFun G H (fbot k) Y') Y')}
     (mkSigma la (mkSigma (precFun-mono G H mg mh {fbot j} {fbot k} {Y} {Y'} la lY) lY))
precFun-mono G H mg mh {fbot zero}    {fcpl k}       {Y} {Y'} la lY =
  LeF-fbot0 (precFun G H (fcpl k) Y')
precFun-mono G H mg mh {fbot (suc j)} {fcpl zero}    {Y} {Y'} () lY
precFun-mono G H mg mh {fbot (suc j)} {fcpl (suc k)} {Y} {Y'} la lY =
  mh {cons (fbot j) (cons (precFun G H (fbot j) Y) Y)}
     {cons (fcpl k) (cons (precFun G H (fcpl k) Y') Y')}
     (mkSigma la (mkSigma (precFun-mono G H mg mh {fbot j} {fcpl k} {Y} {Y'} la lY) lY))
precFun-mono G H mg mh {fcpl j}       {fbot k}       {Y} {Y'} () lY
precFun-mono G H mg mh {fcpl zero}    {fcpl zero}    {Y} {Y'} refl lY = mg lY
precFun-mono G H mg mh {fcpl (suc j)} {fcpl (suc j)} {Y} {Y'} refl lY =
  mh {cons (fcpl j) (cons (precFun G H (fcpl j) Y) Y)}
     {cons (fcpl j) (cons (precFun G H (fcpl j) Y') Y')}
     (mkSigma (LeF-refl (fcpl j))
       (mkSigma (precFun-mono G H mg mh {fcpl j} {fcpl j} {Y} {Y'} refl lY) lY))

PF-mono : (G H : FTup -> FEl) -> Mono G -> Mono H -> Mono (PF G H)
PF-mono G H mg mh {nil}      {nil}       le = LeF-refl (fbot zero)
PF-mono G H mg mh {nil}      {cons _ _}  ()
PF-mono G H mg mh {cons _ _} {nil}       ()
PF-mono G H mg mh {cons a Y} {cons a' Y'} le =
  precFun-mono G H mg mh {a} {a'} {Y} {Y'} (fst le) (snd le)

------------------------------------------------------------------------
-- The recursion data: the abstract interface the chain consumes.
------------------------------------------------------------------------

record RecData : Set where
  constructor mkRecData
  field
    G H     : FTup -> FEl
    monoG   : Mono G
    monoH   : Mono H
    stableH : Stable H
    uog     : UOall G
    uoh     : UOall H
