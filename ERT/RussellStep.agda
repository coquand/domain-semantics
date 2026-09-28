{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.RussellStep
--
-- β-steps of T_R at the positions that `strip` keeps (β ignores the
-- annotations), and the lifting of T_P β-steps along strip: a T_P step
-- of strip(u) is performed by a T_R step of u, for EVERY preimage u.
-- (Streicher: "we can perform on t and s the same sequence of
-- reduction steps, as reductions do not take care of the typing
-- information".)
------------------------------------------------------------------------

module ERT.RussellStep where

open import ERT.Basic
open import ERT.RussellSyntax
import ERT.Model.Core as C
import ERT.PReduction as PR
open import ERT.Model.Strip using (strip ; strip-subst1)

data StepR : {n : Nat} -> Expr n -> Expr n -> Set where
  r-beta  : {n : Nat} {A A' : Expr n} {B B' b : Expr (suc n)} {a : Expr n} ->
    StepR (App A B (Lam A' B' b) a) (subst1 b a)
  r-app-l : {n : Nat} {A : Expr n} {B : Expr (suc n)} {c c' a : Expr n} ->
    StepR c c' -> StepR (App A B c a) (App A B c' a)
  r-app-r : {n : Nat} {A : Expr n} {B : Expr (suc n)} {c a a' : Expr n} ->
    StepR a a' -> StepR (App A B c a) (App A B c a')
  r-lam-d : {n : Nat} {A A' : Expr n} {B b : Expr (suc n)} ->
    StepR A A' -> StepR (Lam A B b) (Lam A' B b)
  r-lam-b : {n : Nat} {A : Expr n} {B b b' : Expr (suc n)} ->
    StepR b b' -> StepR (Lam A B b) (Lam A B b')
  r-pi-d  : {n : Nat} {A A' : Expr n} {B : Expr (suc n)} ->
    StepR A A' -> StepR (Pi A B) (Pi A' B)
  r-pi-c  : {n : Nat} {A : Expr n} {B B' : Expr (suc n)} ->
    StepR B B' -> StepR (Pi A B) (Pi A B')

data StarR {n : Nat} : Expr n -> Expr n -> Set where
  r-refl : {M : Expr n} -> StarR M M
  r-step : {M N K : Expr n} -> StepR M N -> StarR N K -> StarR M K

------------------------------------------------------------------------
-- Lifting
------------------------------------------------------------------------

record Lifted {n : Nat} (u : Expr n) (M' : C.Expr n) : Set where
  constructor mkLifted
  field
    u'   : Expr n
    step : StepR u u'
    eq   : Eq (strip u') M'

liftStep : {n : Nat} {M M' : C.Expr n} -> PR.Step M M' ->
  (u : Expr n) -> Eq (strip u) M -> Lifted u M'
liftStep PR.st-beta (App A B (Lam A' B' b) a) refl = mkLifted (subst1 b a) r-beta (strip-subst1 b a)
liftStep PR.st-beta (App A B (Var _) a)       ()
liftStep PR.st-beta (App A B (U _) a)         ()
liftStep PR.st-beta (App A B (Pi _ _) a)      ()
liftStep PR.st-beta (App A B (App _ _ _ _) a) ()
liftStep PR.st-beta (Var _)         ()
liftStep PR.st-beta (U _)           ()
liftStep PR.st-beta (Pi _ _)        ()
liftStep PR.st-beta (Lam _ _ _)     ()
liftStep (PR.st-app-l s) (App A B c a) refl =
  let r = liftStep s c refl
  in mkLifted (App A B (Lifted.u' r) a) (r-app-l (Lifted.step r)) (Eq-cong (\ X -> C.App X (strip a)) (Lifted.eq r))
liftStep (PR.st-app-l s) (Var _)     ()
liftStep (PR.st-app-l s) (U _)       ()
liftStep (PR.st-app-l s) (Pi _ _)    ()
liftStep (PR.st-app-l s) (Lam _ _ _) ()
liftStep (PR.st-app-r s) (App A B c a) refl =
  let r = liftStep s a refl
  in mkLifted (App A B c (Lifted.u' r)) (r-app-r (Lifted.step r)) (Eq-cong (\ X -> C.App (strip c) X) (Lifted.eq r))
liftStep (PR.st-app-r s) (Var _)     ()
liftStep (PR.st-app-r s) (U _)       ()
liftStep (PR.st-app-r s) (Pi _ _)    ()
liftStep (PR.st-app-r s) (Lam _ _ _) ()
liftStep (PR.st-lam-d s) (Lam A B b) refl =
  let r = liftStep s A refl
  in mkLifted (Lam (Lifted.u' r) B b) (r-lam-d (Lifted.step r)) (Eq-cong (\ X -> C.Lam X (strip b)) (Lifted.eq r))
liftStep (PR.st-lam-d s) (Var _)       ()
liftStep (PR.st-lam-d s) (U _)         ()
liftStep (PR.st-lam-d s) (Pi _ _)      ()
liftStep (PR.st-lam-d s) (App _ _ _ _) ()
liftStep (PR.st-lam-b s) (Lam A B b) refl =
  let r = liftStep s b refl
  in mkLifted (Lam A B (Lifted.u' r)) (r-lam-b (Lifted.step r)) (Eq-cong (\ X -> C.Lam (strip A) X) (Lifted.eq r))
liftStep (PR.st-lam-b s) (Var _)       ()
liftStep (PR.st-lam-b s) (U _)         ()
liftStep (PR.st-lam-b s) (Pi _ _)      ()
liftStep (PR.st-lam-b s) (App _ _ _ _) ()
liftStep (PR.st-pi-d s) (Pi A B) refl =
  let r = liftStep s A refl
  in mkLifted (Pi (Lifted.u' r) B) (r-pi-d (Lifted.step r)) (Eq-cong (\ X -> C.Pi X (strip B)) (Lifted.eq r))
liftStep (PR.st-pi-d s) (Var _)       ()
liftStep (PR.st-pi-d s) (U _)         ()
liftStep (PR.st-pi-d s) (Lam _ _ _)   ()
liftStep (PR.st-pi-d s) (App _ _ _ _) ()
liftStep (PR.st-pi-c s) (Pi A B) refl =
  let r = liftStep s B refl
  in mkLifted (Pi A (Lifted.u' r)) (r-pi-c (Lifted.step r)) (Eq-cong (\ X -> C.Pi (strip A) X) (Lifted.eq r))
liftStep (PR.st-pi-c s) (Var _)       ()
liftStep (PR.st-pi-c s) (U _)         ()
liftStep (PR.st-pi-c s) (Lam _ _ _)   ()
liftStep (PR.st-pi-c s) (App _ _ _ _) ()

record LiftedStar {n : Nat} (u : Expr n) (N : C.Expr n) : Set where
  constructor mkLiftedStar
  field
    u'   : Expr n
    red  : StarR u u'
    eq   : Eq (strip u') N

liftStar : {n : Nat} {M N : C.Expr n} -> PR.Star M N ->
  (u : Expr n) -> Eq (strip u) M -> LiftedStar u N
liftStar PR.st-refl u e = mkLiftedStar u r-refl e
liftStar (PR.st-step s ss) u e =
  let r1 = liftStep s u e
      r2 = liftStar ss (Lifted.u' r1) (Lifted.eq r1)
  in mkLiftedStar (LiftedStar.u' r2) (r-step (Lifted.step r1) (LiftedStar.red r2)) (LiftedStar.eq r2)
