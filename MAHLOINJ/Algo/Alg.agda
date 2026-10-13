{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/Alg.agda
--
-- The conversion algorithm (plan, Soundness of the conversion
-- algorithm): the UNTYPED algorithm of lfsigma Sec. 3, extended by
--   * weak-head evaluation with beta, pi, iota AND delta (HRs, from
--     Valid/HeadRed);
--   * constructor-headed weak-head normal forms compared argumentwise;
--   * rec compared as a neutral elimination, its motive included
--     (under Nat);
--   * lambda-annotations ignored (the only annotations ignored).
-- eta is by shape: a lambda against any term, a pair against any term.
--
-- Given as judgements (one constructor per rule).  The relation is
-- not required to be deterministic: soundness holds for every
-- derivation.  The deterministic procedure (lambda/pair rules tried
-- first, then the structural ones) is the subject of termination.
------------------------------------------------------------------------

module MAHLOINJ.Algo.Alg where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLOINJ.Valid.HeadRed

mutual

  -- t ~ t' : evaluate both sides, compare the weak-head normal forms
  data AlgEq {n : Num} : Expr n -> Expr n -> Set where
    alg : {t t' w w' : Expr n} -> HRs t w -> HRs t' w' -> AlgW w w' -> AlgEq t t'

  -- comparison of weak-head normal forms
  data AlgW {n : Num} : Expr n -> Expr n -> Set where
    -- eta for functions (annotations ignored)
    w-lam   : {A A' : Expr n} {b b' : Expr (suc n)} -> AlgEq b b' -> AlgW (Lam A b) (Lam A' b')
    w-lamL  : {A t' : Expr n} {b : Expr (suc n)} -> AlgEq b (App (wkExpr t') x0) -> AlgW (Lam A b) t'
    w-lamR  : {A' t : Expr n} {b' : Expr (suc n)} -> AlgEq (App (wkExpr t) x0) b' -> AlgW t (Lam A' b')
    -- eta for pairs
    w-pair  : {t u t' u' : Expr n} -> AlgEq t t' -> AlgEq u u' -> AlgW (Pair t u) (Pair t' u')
    w-pairL : {t u t' : Expr n} -> AlgEq t (Fst t') -> AlgEq u (Snd t') -> AlgW (Pair t u) t'
    w-pairR : {t t' u' : Expr n} -> AlgEq (Fst t) t' -> AlgEq (Snd t) u' -> AlgW t (Pair t' u')
    -- constructors, argumentwise (the family of Pi/Sigma by its body)
    w-pi    : {A A' A0 A0' : Expr n} {B B' : Expr (suc n)} -> AlgEq A A' -> AlgEq B B' ->
              AlgW (Pi A (Lam A0 B)) (Pi A' (Lam A0' B'))
    w-sigma : {A A' A0 A0' : Expr n} {B B' : Expr (suc n)} -> AlgEq A A' -> AlgEq B B' ->
              AlgW (Sigma A (Lam A0 B)) (Sigma A' (Lam A0' B'))
    w-nat   : AlgW Nat Nat
    w-zero  : AlgW Zero Zero
    w-suc   : {k k' : Expr n} -> AlgEq k k' -> AlgW (Suc k) (Suc k')
    w-V     : AlgW V V
    w-ucode : {f g f' g' : Expr n} -> AlgEq f f' -> AlgEq g g' -> AlgW (Ucode f g) (Ucode f' g')
    -- neutrals
    w-ne    : {u u' : Expr n} -> AlgNe u u' -> AlgW u u'

  -- comparison of neutrals (structural; arguments by AlgEq)
  data AlgNe {n : Num} : Expr n -> Expr n -> Set where
    ne-var : {i : Fin n} -> AlgNe (Var i) (Var i)
    ne-app : {u u' v v' : Expr n} -> AlgNe u u' -> AlgEq v v' -> AlgNe (App u v) (App u' v')
    ne-fst : {u u' : Expr n} -> AlgNe u u' -> AlgNe (Fst u) (Fst u')
    ne-snd : {u u' : Expr n} -> AlgNe u u' -> AlgNe (Snd u) (Snd u')
    ne-rec : {N N' z z' s s' k k' : Expr n} {C C' : Expr (suc n)} ->
             AlgEq C C' -> AlgEq z z' -> AlgEq s s' -> AlgNe k k' ->
             AlgNe (Rec (Lam N C) z s k) (Rec (Lam N' C') z' s' k')
