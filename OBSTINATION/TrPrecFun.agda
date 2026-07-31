{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecFun
--
-- PRIMITIVE RECURSION AS AN OPERATOR ON FUNCTIONS.
--
-- `PR.precF` recurses on PR TERMS `g` and `h`.  That is not enough here:
-- the continuation of `precTr` at a frozen PARAMETER is the recursion
-- built from the FROZEN base and step, and freezing is an operation on
-- functions, not on terms.  So the correctness statement for `precTr` has
-- to be about
--
--     precFun g h  --  the recursion with base `g` and step `h`
--
-- for arbitrary `g , h : FTup -> FEl`.  `precFun-eval` says this agrees
-- with `evalF (prec g h)` when the two are the denotations of PR terms,
-- so nothing is lost; `precFun-ins` says freezing a parameter of the
-- recursion is the recursion of the frozen base and step, which is the
-- clause that makes the induction on the arity go through.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecFun where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; prec ; evalF ; precF)
open import OBSTINATION.TraceDef using (hgt)
open import OBSTINATION.TrSat using (LeX ; MonoF)
open import OBSTINATION.TrDen using (ins)

------------------------------------------------------------------------
-- THE OPERATOR
------------------------------------------------------------------------

precA : (FTup -> FEl) -> (FTup -> FEl) -> FEl -> FTup -> FEl
precA g h (fbot zero)    Y = fbot zero
precA g h (fbot (suc j)) Y = h (cons (fbot j) (cons (precA g h (fbot j) Y) Y))
precA g h (fcpl zero)    Y = g Y
precA g h (fcpl (suc v)) Y = h (cons (fcpl v) (cons (precA g h (fcpl v) Y) Y))

precFun : (FTup -> FEl) -> (FTup -> FEl) -> FTup -> FEl
precFun g h nil        = fbot zero
precFun g h (cons x Y) = precA g h x Y

------------------------------------------------------------------------
-- IT IS `PR.precF` ON THE DENOTATIONS OF TERMS
------------------------------------------------------------------------

precA-eval : (g h : PR) (x : FEl) (Y : FTup)
           -> Eq (precA (evalF g) (evalF h) x Y) (precF g h x Y)
precA-eval g h (fbot zero)    Y = refl
precA-eval g h (fbot (suc j)) Y =
  Eq-cong (\ z -> evalF h (cons (fbot j) (cons z Y))) (precA-eval g h (fbot j) Y)
precA-eval g h (fcpl zero)    Y = refl
precA-eval g h (fcpl (suc v)) Y =
  Eq-cong (\ z -> evalF h (cons (fcpl v) (cons z Y))) (precA-eval g h (fcpl v) Y)

precFun-eval : (g h : PR) (X : FTup)
             -> Eq (precFun (evalF g) (evalF h) X) (evalF (prec g h) X)
precFun-eval g h nil        = refl
precFun-eval g h (cons x Y) = precA-eval g h x Y

------------------------------------------------------------------------
-- ORDER PLUMBING
------------------------------------------------------------------------

leF-bot0 : (z : FEl) -> LeF (fbot zero) z
leF-bot0 (fbot k) = tt
leF-bot0 (fcpl k) = tt

LeX-cons : (x y : FEl) (Y Y' : FTup) -> LeF x y -> LeX Y Y'
         -> LeX (cons x Y) (cons y Y')
LeX-cons x y Y Y' lx lY zero    = lx
LeX-cons x y Y Y' lx lY (suc c) = lY c

LeX-tail : (x y : FEl) (Y Y' : FTup) -> LeX (cons x Y) (cons y Y') -> LeX Y Y'
LeX-tail x y Y Y' l c = l (suc c)

------------------------------------------------------------------------
-- MONOTONICITY
------------------------------------------------------------------------

precA-mono : (p : Nat) (g h : FTup -> FEl)
           -> MonoF p g -> MonoF (suc (suc p)) h
           -> (x x' : FEl) -> LeF x x'
           -> (Y Y' : FTup) -> Eq (length Y) p -> Eq (length Y') p -> LeX Y Y'
           -> LeF (precA g h x Y) (precA g h x' Y')
precA-mono p g h mg mh (fbot zero)    x'             le Y Y' ly ly' lY =
  leF-bot0 (precA g h x' Y')
precA-mono p g h mg mh (fbot (suc j)) (fbot zero)    () Y Y' ly ly' lY
precA-mono p g h mg mh (fbot (suc j)) (fcpl zero)    () Y Y' ly ly' lY
precA-mono p g h mg mh (fcpl zero)    (fbot k)       () Y Y' ly ly' lY
precA-mono p g h mg mh (fcpl (suc v)) (fbot k)       () Y Y' ly ly' lY
precA-mono p g h mg mh (fbot (suc j)) (fbot (suc k)) le Y Y' ly ly' lY =
  mh _ _ (Eq-cong suc (Eq-cong suc ly)) (Eq-cong suc (Eq-cong suc ly'))
    (LeX-cons (fbot j) (fbot k) _ _ le
      (LeX-cons _ _ Y Y'
        (precA-mono p g h mg mh (fbot j) (fbot k) le Y Y' ly ly' lY) lY))
precA-mono p g h mg mh (fbot (suc j)) (fcpl (suc k)) le Y Y' ly ly' lY =
  mh _ _ (Eq-cong suc (Eq-cong suc ly)) (Eq-cong suc (Eq-cong suc ly'))
    (LeX-cons (fbot j) (fcpl k) _ _ le
      (LeX-cons _ _ Y Y'
        (precA-mono p g h mg mh (fbot j) (fcpl k) le Y Y' ly ly' lY) lY))
precA-mono p g h mg mh (fcpl zero)    (fcpl zero)    refl Y Y' ly ly' lY =
  mg Y Y' ly ly' lY
precA-mono p g h mg mh (fcpl (suc v)) (fcpl (suc v)) refl Y Y' ly ly' lY =
  mh _ _ (Eq-cong suc (Eq-cong suc ly)) (Eq-cong suc (Eq-cong suc ly'))
    (LeX-cons (fcpl v) (fcpl v) _ _ (LeF-refl (fcpl v))
      (LeX-cons _ _ Y Y'
        (precA-mono p g h mg mh (fcpl v) (fcpl v) (LeF-refl (fcpl v))
          Y Y' ly ly' lY) lY))

precFun-mono : (p : Nat) (g h : FTup -> FEl)
             -> MonoF p g -> MonoF (suc (suc p)) h
             -> MonoF (suc p) (precFun g h)
precFun-mono p g h mg mh nil        X'          () lx' le
precFun-mono p g h mg mh (cons x Y) nil         lx () le
precFun-mono p g h mg mh (cons x Y) (cons y Y') lx lx' le =
  precA-mono p g h mg mh x y (le zero) Y Y'
    (suc-inj lx) (suc-inj lx') (LeX-tail x y Y Y' le)

------------------------------------------------------------------------
-- FREEZING A PARAMETER
--
-- Freezing coordinate `1+i` of the recursion -- a PARAMETER, not the
-- recursion argument -- is the recursion of the frozen base and the
-- frozen step.  This is what lets `precTr-den` recurse on the arity.
------------------------------------------------------------------------

precA-ins : (g h : FTup -> FEl) (i v : Nat) (y : FEl) (ys : FTup)
          -> Eq (precA (\ Y' -> g (ins i (fcpl v) Y'))
                       (\ Z  -> h (ins (suc (suc i)) (fcpl v) Z)) y ys)
                (precA g h y (ins i (fcpl v) ys))
precA-ins g h i v (fbot zero)    ys = refl
precA-ins g h i v (fcpl zero)    ys = refl
precA-ins g h i v (fbot (suc j)) ys =
  Eq-cong (\ z -> h (cons (fbot j) (cons z (ins i (fcpl v) ys))))
    (precA-ins g h i v (fbot j) ys)
precA-ins g h i v (fcpl (suc w)) ys =
  Eq-cong (\ z -> h (cons (fcpl w) (cons z (ins i (fcpl v) ys))))
    (precA-ins g h i v (fcpl w) ys)

precFun-ins : (g h : FTup -> FEl) (i v : Nat) (Y : FTup)
            -> Eq (precFun (\ Y' -> g (ins i (fcpl v) Y'))
                           (\ Z  -> h (ins (suc (suc i)) (fcpl v) Z)) Y)
                  (precFun g h (ins (suc i) (fcpl v) Y))
precFun-ins g h i v nil          = refl
precFun-ins g h i v (cons y ys)  = precA-ins g h i v y ys

------------------------------------------------------------------------
-- UNFOLDING ONE SUCCESSOR
--
-- Above `S(bot)` the recursion always takes a step, whether its first
-- argument is incomplete or a numeral; `pre` is that step.
------------------------------------------------------------------------

pre : FEl -> FEl
pre (fbot zero)    = fbot zero
pre (fbot (suc m)) = fbot m
pre (fcpl zero)    = fcpl zero
pre (fcpl (suc m)) = fcpl m

precA-unf : (g h : FTup -> FEl) (j : Nat) (x : FEl) (Y : FTup)
          -> LeF (fbot (suc j)) x
          -> Eq (precA g h x Y) (h (cons (pre x) (cons (precA g h (pre x) Y) Y)))
precA-unf g h j (fbot zero)    Y ()
precA-unf g h j (fcpl zero)    Y ()
precA-unf g h j (fbot (suc m)) Y l = refl
precA-unf g h j (fcpl (suc m)) Y l = refl

pre-le : (j : Nat) (x : FEl) -> LeF (fbot (suc j)) x -> LeF (fbot j) (pre x)
pre-le j (fbot zero)    ()
pre-le j (fcpl zero)    ()
pre-le j (fbot (suc m)) l = l
pre-le j (fcpl (suc m)) l = l
