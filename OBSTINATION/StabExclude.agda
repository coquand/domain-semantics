{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.StabExclude
--
-- The cross-meet stability kernel (min.pdf p.4, min1.pdf: "les elements
-- de PR sont stables").  A stable function cannot be "driven to infinity"
-- by two independent coordinates: if H is Case-3 STRICTLY
-- INCREASING at a coordinate i1 (on some region) AND Case-3 strictly
-- increasing at another coordinate i2 (i1 /= i2), we derive a
-- contradiction, purely from Berry stability (`Stability.stable`).
--
-- CROSS-MEET RECIPE.  From a common finite base C with
--   getF i1 C = fbot k1,   getF i2 C = fbot k2,
-- build, for p >= k1 and m >= k2,
--   A p = repl i1 (fbot p) C     (so H (A p) = fbot (phi1 p)),
--   B m = repl i2 (fbot m) C     (so H (B m) = fbot (phi2 m)).
-- Then, because p >= k1 and m >= k2, the pointwise meet  A p /\ B m  is
-- CONSTANT and equal to C (its coord i1 = min(p,k1) = k1 etc.), so
--   H (A p /\ B m) = H C  is a FIXED value.
-- Stability gives  H C = fbot (min (phi1 p) (phi2 m))  for ALL such
-- p, m.  Choosing p, m with phi1 p, phi2 m both above that fixed height
-- (phi's strict-increasing escape) forces  H0 = min(...) > H0  -- Empty.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.StabExclude where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property using (StrictIncFrom ; getF)
open import OBSTINATION.Meet
open import OBSTINATION.Stability using (stable)
open import OBSTINATION.Prop1Base using (repl)
open import OBSTINATION.PrecFun using (RecData)
import OBSTINATION.PhiProps as PhiProps

------------------------------------------------------------------------
-- Small numeric lemmas
------------------------------------------------------------------------

minN-comm : (m n : Nat) -> Eq (minN m n) (minN n m)
minN-comm zero    n       = Eq-sym (minN-zero-r n)
minN-comm (suc m) zero    = refl
minN-comm (suc m) (suc n) = Eq-cong suc (minN-comm m n)

minN-ge : {c x y : Nat} -> LeN c x -> LeN c y -> LeN c (minN x y)
minN-ge {zero}                      lx ly = tt
minN-ge {suc c} {zero}              () ly
minN-ge {suc c} {suc x} {zero}      lx ()
minN-ge {suc c} {suc x} {suc y}     lx ly = minN-ge {c} {x} {y} lx ly

LeN-suc-not : (n : Nat) -> LeN (suc n) n -> Empty
LeN-suc-not zero    ()
LeN-suc-not (suc n) p = LeN-suc-not n p

------------------------------------------------------------------------
-- fbot is injective
------------------------------------------------------------------------

unbot : FEl -> Nat
unbot (fbot k) = k
unbot (fcpl k) = k

fbot-inj : {a b : Nat} -> Eq (fbot a) (fbot b) -> Eq a b
fbot-inj e = Eq-cong unbot e

------------------------------------------------------------------------
-- meet and boundedness are idempotent / reflexive
------------------------------------------------------------------------

meetF-idem : (x : FEl) -> Eq (meetF x x) x
meetF-idem (fbot j) = Eq-cong fbot (minN-l {j} {j} (LeN-refl j))
meetF-idem (fcpl j) = Eq-cong fcpl (minN-l {j} {j} (LeN-refl j))

meetT-idem : (C : FTup) -> Eq (meetT C C) C
meetT-idem nil         = refl
meetT-idem (cons x xs) = cons-eq (meetF-idem x) (meetT-idem xs)

Bnd-self : (x : FEl) -> Bnd x x
Bnd-self (fbot j) = tt
Bnd-self (fcpl j) = refl

BndT-self : (C : FTup) -> BndT C C
BndT-self nil         = tt
BndT-self (cons x xs) = mkSigma (Bnd-self x) (BndT-self xs)

------------------------------------------------------------------------
-- meet of a tuple with one coordinate replaced (one-sided) equals the
-- tuple, when the replacement absorbs at that coordinate.
------------------------------------------------------------------------

meet-repl-r : (i : Nat) (b : FEl) (C : FTup) ->
  Eq (meetF (getF i C) b) (getF i C) -> Eq (meetT C (repl i b C)) C
meet-repl-r i       b nil         hyp = refl
meet-repl-r zero    b (cons x xs) hyp = cons-eq hyp (meetT-idem xs)
meet-repl-r (suc i) b (cons x xs) hyp = cons-eq (meetF-idem x) (meet-repl-r i b xs hyp)

meet-repl-l : (i : Nat) (a : FEl) (C : FTup) ->
  Eq (meetF a (getF i C)) (getF i C) -> Eq (meetT (repl i a C) C) C
meet-repl-l i       a nil         hyp = refl
meet-repl-l zero    a (cons x xs) hyp = cons-eq hyp (meetT-idem xs)
meet-repl-l (suc i) a (cons x xs) hyp = cons-eq (meetF-idem x) (meet-repl-l i a xs hyp)

------------------------------------------------------------------------
-- meet of two DIFFERENT coordinate replacements equals the base tuple.
------------------------------------------------------------------------

meet-repl2 : (i1 i2 : Nat) (a b : FEl) (C : FTup) -> Not (Eq i1 i2) ->
  Eq (meetF a (getF i1 C)) (getF i1 C) ->
  Eq (meetF (getF i2 C) b) (getF i2 C) ->
  Eq (meetT (repl i1 a C) (repl i2 b C)) C
meet-repl2 i1        i2        a b nil         neq h1 h2 = refl
meet-repl2 zero      zero      a b (cons x xs) neq h1 h2 = Empty-elim (neq refl)
meet-repl2 zero      (suc i2') a b (cons x xs) neq h1 h2 =
  cons-eq h1 (meet-repl-r i2' b xs h2)
meet-repl2 (suc i1') zero      a b (cons x xs) neq h1 h2 =
  cons-eq h2 (meet-repl-l i1' a xs h1)
meet-repl2 (suc i1') (suc i2') a b (cons x xs) neq h1 h2 =
  cons-eq (meetF-idem x)
    (meet-repl2 i1' i2' a b xs (\ e -> neq (Eq-cong suc e)) h1 h2)

------------------------------------------------------------------------
-- boundedness of one, resp. two, coordinate replacements.
------------------------------------------------------------------------

Bnd-repl-r : (i : Nat) (b : FEl) (C : FTup) ->
  Bnd (getF i C) b -> BndT C (repl i b C)
Bnd-repl-r i       b nil         hyp = tt
Bnd-repl-r zero    b (cons x xs) hyp = mkSigma hyp (BndT-self xs)
Bnd-repl-r (suc i) b (cons x xs) hyp = mkSigma (Bnd-self x) (Bnd-repl-r i b xs hyp)

Bnd-repl-l : (i : Nat) (a : FEl) (C : FTup) ->
  Bnd a (getF i C) -> BndT (repl i a C) C
Bnd-repl-l i       a nil         hyp = tt
Bnd-repl-l zero    a (cons x xs) hyp = mkSigma hyp (BndT-self xs)
Bnd-repl-l (suc i) a (cons x xs) hyp = mkSigma (Bnd-self x) (Bnd-repl-l i a xs hyp)

Bnd-repl2 : (i1 i2 : Nat) (a b : FEl) (C : FTup) -> Not (Eq i1 i2) ->
  Bnd a (getF i1 C) -> Bnd (getF i2 C) b ->
  BndT (repl i1 a C) (repl i2 b C)
Bnd-repl2 i1        i2        a b nil         neq hA hB = tt
Bnd-repl2 zero      zero      a b (cons x xs) neq hA hB = Empty-elim (neq refl)
Bnd-repl2 zero      (suc i2') a b (cons x xs) neq hA hB =
  mkSigma hA (Bnd-repl-r i2' b xs hB)
Bnd-repl2 (suc i1') zero      a b (cons x xs) neq hA hB =
  mkSigma hB (Bnd-repl-l i1' a xs hA)
Bnd-repl2 (suc i1') (suc i2') a b (cons x xs) neq hA hB =
  mkSigma (Bnd-self x)
    (Bnd-repl2 i1' i2' a b xs (\ e -> neq (Eq-cong suc e)) hA hB)

------------------------------------------------------------------------
-- The cross-meet stability exclusion.
------------------------------------------------------------------------

stab-exclude : (rd : RecData) (C : FTup) (i1 i2 k1 k2 : Nat) (phi1 phi2 : Nat -> Nat) ->
  Not (Eq i1 i2) ->
  Eq (getF i1 C) (fbot k1) ->
  Eq (getF i2 C) (fbot k2) ->
  ((p : Nat) -> LeN k1 p -> Eq (RecData.H rd (repl i1 (fbot p) C)) (fbot (phi1 p))) ->
  ((m : Nat) -> LeN k2 m -> Eq (RecData.H rd (repl i2 (fbot m) C)) (fbot (phi2 m))) ->
  StrictIncFrom k1 phi1 ->
  StrictIncFrom k2 phi2 ->
  Empty
stab-exclude rd C i1 i2 k1 k2 phi1 phi2 neq cA cB hyA hyB sinc1 sinc2 =
  LeN-suc-not H0 contra
  where
    open RecData rd
    -- meet-absorption at each replaced coordinate
    eqA : (p : Nat) -> LeN k1 p -> Eq (meetF (fbot p) (getF i1 C)) (getF i1 C)
    eqA p le =
      Eq-transport (\ z -> Eq (meetF (fbot p) z) z) (Eq-sym cA)
        (Eq-cong fbot (Eq-trans (minN-comm p k1) (minN-l {k1} {p} le)))

    eqB : (m : Nat) -> LeN k2 m -> Eq (meetF (getF i2 C) (fbot m)) (getF i2 C)
    eqB m le =
      Eq-transport (\ z -> Eq (meetF z (fbot m)) z) (Eq-sym cB)
        (Eq-cong fbot (minN-l {k2} {m} le))

    bndA : (p : Nat) -> Bnd (fbot p) (getF i1 C)
    bndA p = Eq-transport (\ z -> Bnd (fbot p) z) (Eq-sym cA) tt

    bndB : (m : Nat) -> Bnd (getF i2 C) (fbot m)
    bndB m = Eq-transport (\ z -> Bnd z (fbot m)) (Eq-sym cB) tt

    -- for p >= k1, m >= k2 the meet of the two replacements is C
    meq : (p m : Nat) -> LeN k1 p -> LeN k2 m ->
          Eq (meetT (repl i1 (fbot p) C) (repl i2 (fbot m) C)) C
    meq p m lp lm =
      meet-repl2 i1 i2 (fbot p) (fbot m) C neq (eqA p lp) (eqB m lm)

    bnd : (p m : Nat) -> BndT (repl i1 (fbot p) C) (repl i2 (fbot m) C)
    bnd p m = Bnd-repl2 i1 i2 (fbot p) (fbot m) C neq (bndA p) (bndB m)

    -- meetF of the two germ values
    meetF-eq : (p m : Nat) -> LeN k1 p -> LeN k2 m ->
      Eq (meetF (H (repl i1 (fbot p) C)) (H (repl i2 (fbot m) C)))
         (fbot (minN (phi1 p) (phi2 m)))
    meetF-eq p m lp lm =
      Eq-trans (Eq-cong (\ z -> meetF z (H (repl i2 (fbot m) C))) (hyA p lp))
               (Eq-cong (\ z -> meetF (fbot (phi1 p)) z) (hyB m lm))

    -- the key equation: H C = fbot (min (phi1 p) (phi2 m)) for all valid p,m
    star : (p m : Nat) -> LeN k1 p -> LeN k2 m ->
           Eq (H C) (fbot (minN (phi1 p) (phi2 m)))
    star p m lp lm =
      Eq-trans (Eq-sym (Eq-cong H (meq p m lp lm)))
        (Eq-trans (stableH {repl i1 (fbot p) C} {repl i2 (fbot m) C} (bnd p m))
                  (meetF-eq p m lp lm))

    H0 : Nat
    H0 = minN (phi1 k1) (phi2 k2)

    V0eq : Eq (H C) (fbot H0)
    V0eq = star k1 k2 (LeN-refl k1) (LeN-refl k2)

    esc1 = PhiProps.phi-escape k1 phi1 sinc1 (suc H0)
    esc2 = PhiProps.phi-escape k2 phi2 sinc2 (suc H0)

    p* = fst esc1
    lp* : LeN k1 p*
    lp* = fst (snd esc1)
    gp : LeN (suc H0) (phi1 p*)
    gp = snd (snd esc1)

    m* = fst esc2
    lm* : LeN k2 m*
    lm* = fst (snd esc2)
    gm : LeN (suc H0) (phi2 m*)
    gm = snd (snd esc2)

    eqH0 : Eq (fbot H0) (fbot (minN (phi1 p*) (phi2 m*)))
    eqH0 = Eq-trans (Eq-sym V0eq) (star p* m* lp* lm*)

    Hbig : LeN (suc H0) (minN (phi1 p*) (phi2 m*))
    Hbig = minN-ge {suc H0} {phi1 p*} {phi2 m*} gp gm

    contra : LeN (suc H0) H0
    contra = Eq-transport (\ z -> LeN (suc H0) z) (Eq-sym (fbot-inj eqH0)) Hbig
