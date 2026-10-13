{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/WhnfNoDelta.agda
--
-- Weak-head normalisation for the reduction WITHOUT delta: beta, pi,
-- iota (WhRed of MAHLOINJ/Inversion/SR), for which subject reduction
-- holds at every type, U(f,g) included.  fhat and ghat are then normal
-- forms; delta is an equation of conversion at V only, and a step of
-- the algorithm (HR), not of reduction.
--
-- Route: a HR-step is a WhRed-step, or it is a delta-step on the head
-- spine, and then its source is already WhRed-normal.  So a HR-path to
-- a HR-normal form (MAHLOALG/Whnf) is cut at its first delta-step.
------------------------------------------------------------------------

module MAHLOALG.WhnfNoDelta where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLO.Fixpoint using (Fixpoint)
open import MAHLO.Concrete.Instance using (concreteTM)
open import MAHLO.Concrete.Rel using (SR)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Final using (injHyp)
open import MAHLOINJ.Inversion.SR injHyp using (WhRed ; wh-beta ; wh-app ;
  wh-fst-pair ; wh-snd-pair ; wh-fst ; wh-snd ; wh-rec-zero ; wh-rec-suc ; wh-rec)
open import MAHLOALG.Whnf using (WhnfRes ; whnfOf)

------------------------------------------------------------------------
-- WhRed-normal forms and paths
------------------------------------------------------------------------

NoWh : {n : Num} -> Expr n -> Set
NoWh t = {t' : _} -> WhRed t t' -> Empty

data WhReds {n : Num} : Expr n -> Expr n -> Set where
  whs-refl : {t : Expr n} -> WhReds t t
  whs-step : {t t' t'' : Expr n} -> WhRed t t' -> WhReds t' t'' -> WhReds t t''

-- WhRed is HR without delta
wh-hr : {n : Num} {t t' : Expr n} -> WhRed t t' -> HR t t'
wh-hr wh-beta = hr-beta
wh-hr (wh-app r) = hr-app (wh-hr r)
wh-hr wh-fst-pair = hr-fst-pair
wh-hr wh-snd-pair = hr-snd-pair
wh-hr (wh-fst r) = hr-fst (wh-hr r)
wh-hr (wh-snd r) = hr-snd (wh-hr r)
wh-hr wh-rec-zero = hr-rec-zero
wh-hr wh-rec-suc = hr-rec-suc
wh-hr (wh-rec r) = hr-rec (wh-hr r)

nored-nowh : {n : Num} {t : Expr n} -> NoRed t -> NoWh t
nored-nowh nr r = nr (wh-hr r)

------------------------------------------------------------------------
-- a HR-step is a WhRed-step, or its source is WhRed-normal
------------------------------------------------------------------------

split : {n : Num} {t t' : Expr n} -> HR t t' -> WhRed t t' + NoWh t
split hr-beta = inl wh-beta
split (hr-app r) with split r
... | inl w = inl (wh-app w)
... | inr nw = inr (\ { wh-beta -> nored-Lam r ; (wh-app w) -> nw w })
split hr-fst-pair = inl wh-fst-pair
split hr-snd-pair = inl wh-snd-pair
split (hr-fst r) with split r
... | inl w = inl (wh-fst w)
... | inr nw = inr (\ { wh-fst-pair -> nored-Pair r ; (wh-fst w) -> nw w })
split (hr-snd r) with split r
... | inl w = inl (wh-snd w)
... | inr nw = inr (\ { wh-snd-pair -> nored-Pair r ; (wh-snd w) -> nw w })
split hr-rec-zero = inl wh-rec-zero
split hr-rec-suc = inl wh-rec-suc
split (hr-rec r) with split r
... | inl w = inl (wh-rec w)
... | inr nw = inr (\ { wh-rec-zero -> nored-Zero r ; wh-rec-suc -> nored-Suc r ;
                        (wh-rec w) -> nw w })
split hr-fhat = inr (\ ())
split hr-ghat = inr (\ ())

------------------------------------------------------------------------
-- cutting a HR-path at its first delta-step
------------------------------------------------------------------------

record WhNoDelta {n : Num} (t : Expr n) : Set where
  constructor whnodelta
  field
    w  : Expr n
    rs : WhReds t w
    nw : NoWh w

cut : {n : Num} {t u : Expr n} -> HRs t u -> NoRed u -> WhNoDelta t
cut hrs-refl nr = whnodelta _ whs-refl (nored-nowh nr)
cut (hrs-step r p) nr with split r
... | inr nw = whnodelta _ whs-refl nw
... | inl s  = let c = cut p nr in
               whnodelta (WhNoDelta.w c) (whs-step s (WhNoDelta.rs c)) (WhNoDelta.nw c)

------------------------------------------------------------------------
-- every well-typed term weak-head normalises without delta,
-- relative to the fixed point
------------------------------------------------------------------------

module _ (Fx : Fixpoint concreteTM) where

  open import MAHLOALG.T3 Fx using (tmS ; tySelf)

  whnf-tm : {n : Num} {G : Ctx n} {t C : Expr n} -> HasType G t C -> WhNoDelta t
  whnf-tm {t = t} h = let W = whnfOf t (SR.da (tmS h)) in cut (WhnfRes.rs W) (WhnfRes.nr W)

  whnf-ty : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> WhNoDelta A
  whnf-ty {A = A} iA = let W = whnfOf A (SR.da (tySelf iA)) in cut (WhnfRes.rs W) (WhnfRes.nr W)
