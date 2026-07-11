{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PR
--
-- Primitive-recursive denotations, Section 1.  PR is the syntax of the
-- class of primitive recursive functions: the constant 0, the
-- projections, the successor, closed under composition and primitive
-- recursion.  Arity is NOT tracked in the type (spartan: PR is a plain
-- inductive type, not indexed); a term is applied to a tuple (List) of
-- finite arguments of the appropriate length.
--
-- Its interpretation on finite tuples, evalF : PR -> FTup -> FEl, is a
-- total, structurally terminating function: primitive recursion peels
-- one successor off the first argument at a time, so it recurses on the
-- height of that finite element.  (The Scott-continuous extension to the
-- infinite argument S^omega(bot) -- which needs the ultimate obstination
-- property -- is a later phase.)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PR where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples

------------------------------------------------------------------------
-- Syntax of primitive recursive functions
--
--   zerf         : the constant 0                  (= cpl 0)
--   proj i       : the i-th projection
--   succ         : the successor
--   comp g hs    : g o (h_1,...,h_k)
--   prec g h     : primitive recursion from base g and step h:
--                    f(0,Y)   = g(Y)
--                    f(S x,Y) = h(x, f(x,Y), Y)
------------------------------------------------------------------------

data PR : Set where
  zerf : PR
  proj : Nat -> PR
  succ : PR
  comp : PR -> List PR -> PR
  prec : PR -> PR -> PR

------------------------------------------------------------------------
-- Interpretation on finite tuples
--
-- The mutual block:
--   evalF   -- interpret a PR term at a finite tuple
--   mapE    -- interpret a list of PR terms (for composition)
--   precF   -- the primitive recursion operator, recursing on the
--              successor-height of the (finite) first argument.
--
-- Termination: precF strictly decreases the height of its FEl argument;
-- evalF/mapE strictly decrease the PR term.  The only calls from precF
-- back into evalF are on the *sub-terms* g and h of the prec node, so
-- every evalF -> precF -> evalF cycle strictly decreases the term.
-- Hence no TERMINATING pragma is needed.
--
-- Out-of-arity applications (succ / prec at the empty tuple) return bot;
-- they are junk that the well-formed statements never exercise.
------------------------------------------------------------------------

mutual
  evalF : PR -> FTup -> FEl
  evalF zerf        xs           = fcpl zero
  evalF (proj i)    xs           = nth (fbot zero) i xs
  evalF succ        nil          = fbot zero
  evalF succ        (cons x xs)  = sucF x
  evalF (comp g hs) xs           = evalF g (mapE hs xs)
  evalF (prec g h)  nil          = fbot zero
  evalF (prec g h)  (cons a Y)   = precF g h a Y

  mapE : List PR -> FTup -> FTup
  mapE nil         xs = nil
  mapE (cons p ps) xs = cons (evalF p xs) (mapE ps xs)

  precF : PR -> PR -> FEl -> FTup -> FEl
  -- f(bot, Y) = bot
  precF g h (fbot zero)    Y = fbot zero
  -- f(S x, Y) = h(x, f(x,Y), Y)     with x = fbot j
  precF g h (fbot (suc j)) Y = evalF h (cons (fbot j) (cons (precF g h (fbot j) Y) Y))
  -- f(0, Y) = g(Y)
  precF g h (fcpl zero)    Y = evalF g Y
  -- f(S x, Y) = h(x, f(x,Y), Y)     with x = fcpl j
  precF g h (fcpl (suc j)) Y = evalF h (cons (fcpl j) (cons (precF g h (fcpl j) Y) Y))

------------------------------------------------------------------------
-- Sanity checks (definitional): the primitive recursion equations hold.
------------------------------------------------------------------------

-- f(bot, Y) = bot
prec-bot : (g h : PR) (Y : FTup) ->
  Eq (evalF (prec g h) (cons (fbot zero) Y)) (fbot zero)
prec-bot g h Y = refl

-- f(0, Y) = g(Y)
prec-zero : (g h : PR) (Y : FTup) ->
  Eq (evalF (prec g h) (cons (fcpl zero) Y)) (evalF g Y)
prec-zero g h Y = refl

-- f(S x, Y) = h(x, f(x,Y), Y)   for a complete first argument x = fcpl j
prec-suc-cpl : (g h : PR) (j : Nat) (Y : FTup) ->
  Eq (evalF (prec g h) (cons (fcpl (suc j)) Y))
     (evalF h (cons (fcpl j) (cons (evalF (prec g h) (cons (fcpl j) Y)) Y)))
prec-suc-cpl g h j Y = refl

-- f(S x, Y) = h(x, f(x,Y), Y)   for an incomplete first argument x = fbot j
prec-suc-bot : (g h : PR) (j : Nat) (Y : FTup) ->
  Eq (evalF (prec g h) (cons (fbot (suc j)) Y))
     (evalF h (cons (fbot j) (cons (evalF (prec g h) (cons (fbot j) Y)) Y)))
prec-suc-bot g h j Y = refl

-- successor really is the successor
succ-eq : (x : FEl) (xs : FTup) -> Eq (evalF succ (cons x xs)) (sucF x)
succ-eq x xs = refl
