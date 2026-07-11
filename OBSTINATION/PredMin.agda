{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PredMin
--
-- Two concrete primitive-recursive terms -- predecessor and min -- and
-- evaluation of their Scott-continuous extensions at the infinite
-- diagonal point, via  fhat-diag  (Proposition 1's computability corollary).
------------------------------------------------------------------------

module OBSTINATION.PredMin where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Prop1 using (Wf ; prop1)
open import OBSTINATION.Computable using (fhat-diag)

------------------------------------------------------------------------
-- predecessor:  pred 0 = 0,  pred (S x) = x
--   = prec g h with g = 0 (constant), h(x, pred x) = x = proj 0
------------------------------------------------------------------------

predPR : PR
predPR = prec zerf (proj zero)

wf-pred : Wf predPR (suc zero)
wf-pred = mkSigma zero (mkSigma refl (mkSigma tt tt))

------------------------------------------------------------------------
-- truncated subtraction, recursion on the FIRST argument:
--   sub' (0   , x) = x
--   sub' (S y , x) = pred (sub' (y , x))
-- so  sub' (y , x) = x - y  (monus).  Arity 2.
------------------------------------------------------------------------

subPR : PR
subPR = prec (proj zero) (comp predPR (cons (proj (suc zero)) nil))

wf-sub : Wf subPR (suc (suc zero))
wf-sub =
  mkSigma (suc zero)
    (mkSigma refl
      (mkSigma tt
        (mkSigma (mkSigma zero (mkSigma refl (mkSigma tt tt)))
                 (mkSigma tt tt))))

------------------------------------------------------------------------
-- min x y = x - (x - y) = sub'(sub'(y,x), x).  Arity 2.
------------------------------------------------------------------------

minPR : PR
minPR =
  comp subPR
    (cons (comp subPR (cons (proj (suc zero)) (cons (proj zero) nil)))
    (cons (proj zero) nil))

wf-min : Wf minPR (suc (suc zero))
wf-min =
  mkSigma wf-sub
    (mkSigma
      (mkSigma wf-sub (mkSigma tt (mkSigma tt tt)))
      (mkSigma tt tt))

------------------------------------------------------------------------
-- addition, recursion on the FIRST argument:
--   add (0   , y) = y
--   add (S x , y) = S (add (x , y))          -- step function = succ
-- Arity 2.  (Positive contrast to min: the step is strictly increasing.)
------------------------------------------------------------------------

addPR : PR
addPR = prec (proj zero) (comp succ (cons (proj (suc zero)) nil))

wf-add : Wf addPR (suc (suc zero))
wf-add =
  mkSigma (suc zero)
    (mkSigma refl (mkSigma tt (mkSigma tt (mkSigma tt tt))))

------------------------------------------------------------------------
-- Sanity: on TOTAL inputs these terms really are pred / monus / min / add.
------------------------------------------------------------------------

-- pred (S^3 0) = S^2 0
_ : Eq (evalF predPR (cons (fcpl (suc (suc (suc zero)))) nil)) (fcpl (suc (suc zero)))
_ = refl

-- sub'(1,3) = 3 - 1 = 2       (subPR args: first = y, second = x;  value = x - y)
_ : Eq (evalF subPR (cons (fcpl (suc zero)) (cons (fcpl (suc (suc (suc zero)))) nil)))
       (fcpl (suc (suc zero)))
_ = refl

-- min(2,3) = 2  and  min(3,1) = 1
_ : Eq (evalF minPR (cons (fcpl (suc (suc zero))) (cons (fcpl (suc (suc (suc zero)))) nil)))
       (fcpl (suc (suc zero)))
_ = refl
_ : Eq (evalF minPR (cons (fcpl (suc (suc (suc zero)))) (cons (fcpl (suc zero)) nil)))
       (fcpl (suc zero))
_ = refl

-- add(2,3) = 5
_ : Eq (evalF addPR (cons (fcpl (suc (suc zero))) (cons (fcpl (suc (suc (suc zero)))) nil)))
       (fcpl (suc (suc (suc (suc (suc zero))))))
_ = refl

------------------------------------------------------------------------
-- Denotations at the infinite diagonal  x = S^omega(bot).
--
-- These are the *intensional* values -- the Scott-continuous extension of
-- each ALGORITHM, not the ideal function.  Colson's obstination in action:
--
--   pred-hat(x)      = x                    (pred is lazy in its argument)
--   sub'-hat(x , x)  = bot                  (recursion on the 1st arg never
--                                            terminates: S^omega(bot) has no
--                                            outermost successor to peel)
--   min-hat(x , x)   = bot   (NOT x!)       (min = x - (x - x) inherits the
--                                            obstination of subtraction)
--   add-hat(x , x)   = x = S^omega(bot)     (POSITIVE contrast: the step is
--                                            succ, strictly increasing, so the
--                                            Kleene sequence S^k(bot) rises to
--                                            infinity -- Case 3, phi strict)
--
-- So the primitive-recursive min, run on two copies of the infinite element,
-- yields bottom -- it is "ultimately obstinate", exactly Colson -- whereas
-- add yields the infinite element (infinity + infinity = infinity).
------------------------------------------------------------------------

pred-inf : Eq (fhat-diag predPR (suc zero) wf-pred) inf
pred-inf = refl

sub-inf : Eq (fhat-diag subPR (suc (suc zero)) wf-sub) (bot zero)
sub-inf = refl

min-inf : Eq (fhat-diag minPR (suc (suc zero)) wf-min) (bot zero)
min-inf = refl

add-inf : Eq (fhat-diag addPR (suc (suc zero)) wf-add) inf
add-inf = refl
