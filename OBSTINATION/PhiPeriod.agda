{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PhiPeriod
--
-- The REFINED case-3 invariant for mutual iteration.
--
-- `Property.StrictIncFrom k phi` demands an increase at EVERY step, which
-- `IterPhiFail` shows is false for mutual iteration: there phi_1 = floor(m/2)
-- advances only every other step.  The refinement is to allow a PERIOD d:
--
--   StrictIncBy k d phi  =  (m : Nat) -> LeN k m -> phi m < phi (m + d)
--
-- with d the length of the live cycle through that component in the
-- read-graph (`IterGraph2`), hence d <= r.  Then:
--
--   * d = 1 is exactly the old `StrictIncFrom` (`StrictIncFrom-By`,
--     `By-StrictIncFrom`), so nothing is lost in the unary case;
--   * the counterexample fits at d = 2 = r (`half-IncBy2`), and indeed
--     `half` satisfies the refined invariant while provably failing the
--     old one (`IterPhiFail.notPhiOK`);
--   * the only thing `Refine`/`ExtMono` ask of the increasing branch --
--     that phi escapes every bound -- still holds (`phi-escape-by`), by
--     iterating the d-step jump instead of the 1-step one.
--
-- So `uoValue` keeps its meaning: constant branch -> the finite value
-- S^{phi k}(bot); increasing-by-d branch -> S^omega(bot), justified by
-- `phi-escape-by`.  `Property.agda` is NOT modified here -- this module
-- only establishes that the refinement is viable.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PhiPeriod where

open import OBSTINATION.Prelude
open import OBSTINATION.Property using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (getF)
open import OBSTINATION.StabExclude using (LeN-suc-not)
open import OBSTINATION.IterFun using (iterVec ; appF)
open import OBSTINATION.IterPhiFail using (half ; notPhiOK)

------------------------------------------------------------------------
-- Increase with a period
------------------------------------------------------------------------

StrictIncBy : Nat -> Nat -> (Nat -> Nat) -> Set
StrictIncBy k d phi = (m : Nat) -> LeN k m -> LeN (suc (phi m)) (phi (addN m d))

-- the refined case-3 disjunction
PhiOKBy : Nat -> Nat -> (Nat -> Nat) -> Set
PhiOKBy k d phi = Or (ConstFrom k phi) (StrictIncBy k d phi)

------------------------------------------------------------------------
-- Period 1 is exactly the old notion  (addN m (suc zero) reduces to suc m)
------------------------------------------------------------------------

StrictIncFrom-By : (k : Nat) (phi : Nat -> Nat) ->
  StrictIncFrom k phi -> StrictIncBy k (suc zero) phi
StrictIncFrom-By k phi si m km = si m km

By-StrictIncFrom : (k : Nat) (phi : Nat -> Nat) ->
  StrictIncBy k (suc zero) phi -> StrictIncFrom k phi
By-StrictIncFrom k phi si m km = si m km

-- hence the refinement is a genuine weakening of the old invariant
PhiOK-By : (k : Nat) (phi : Nat -> Nat) -> PhiOK k phi -> PhiOKBy k (suc zero) phi
PhiOK-By k phi (inl c) = inl c
PhiOK-By k phi (inr s) = inr (StrictIncFrom-By k phi s)

------------------------------------------------------------------------
-- Iterating the d-step jump
------------------------------------------------------------------------

-- stepN k d n  =  k + n*d
stepN : Nat -> Nat -> Nat -> Nat
stepN k d zero    = k
stepN k d (suc n) = addN (stepN k d n) d

stepN-ge : (k d n : Nat) -> LeN k (stepN k d n)
stepN-ge k d zero    = LeN-refl k
stepN-ge k d (suc n) =
  LeN-trans {k} {stepN k d n} {addN (stepN k d n) d}
    (stepN-ge k d n) (LeN-addN-l (stepN k d n) d)

-- b <= a + b
LeN-addN-r : (a b : Nat) -> LeN b (addN a b)
LeN-addN-r a zero    = tt
LeN-addN-r a (suc b) = LeN-addN-r a b

-- after n jumps the value has grown by at least n
climb : (k d : Nat) (phi : Nat -> Nat) -> StrictIncBy k d phi ->
  (n : Nat) -> LeN (addN (phi k) n) (phi (stepN k d n))
climb k d phi si zero    = LeN-refl (phi k)
climb k d phi si (suc n) =
  LeN-trans {suc (addN (phi k) n)}
            {suc (phi (stepN k d n))}
            {phi (addN (stepN k d n) d)}
    (climb k d phi si n)
    (si (stepN k d n) (stepN-ge k d n))

------------------------------------------------------------------------
-- Escape: the increasing-by-d branch is still unbounded
--
-- This is what `Refine.refine-aux` uses in the strictly-increasing case
-- (through `PhiProps.phi-escape`), and it is all it uses.
------------------------------------------------------------------------

phi-escape-by : (k d : Nat) (phi : Nat -> Nat) -> StrictIncBy k d phi ->
  (p : Nat) -> Sigma Nat (\ m -> Pair (LeN k m) (LeN p (phi m)))
phi-escape-by k d phi si p =
  mkSigma (stepN k d p)
    (mkSigma (stepN-ge k d p)
      (LeN-trans {p} {addN (phi k) p} {phi (stepN k d p)}
        (LeN-addN-r (phi k) p) (climb k d phi si p)))

------------------------------------------------------------------------
-- The counterexample fits, at period 2 = r
--
-- half (m+2) = suc (half m) by definition, so the increase is exact.
-- Together with `IterPhiFail.notPhiOK` this says precisely that the
-- refinement is STRICTLY weaker: `half` satisfies PhiOKBy at d = 2 and
-- satisfies PhiOK at no threshold at all.
------------------------------------------------------------------------

two : Nat
two = suc (suc zero)

half-IncBy2 : StrictIncBy zero two half
half-IncBy2 m km = LeN-refl (half m)

half-PhiOKBy : PhiOKBy zero two half
half-PhiOKBy = inr half-IncBy2

half-not-PhiOK : (k : Nat) -> PhiOK k half -> Empty
half-not-PhiOK = notPhiOK

-- and the escape lemma really does fire on it: half is unbounded
half-unbounded : (p : Nat) ->
  Sigma Nat (\ m -> Pair (LeN zero m) (LeN p (half m)))
half-unbounded = phi-escape-by zero two half half-IncBy2

------------------------------------------------------------------------
-- A SECOND, structurally different instance
--
-- To check that d = 2 is not an artifact of where the successor sits in
-- the first block, here is the mirror image: the successor is applied on
-- the OTHER side of the cycle,
--
--   f_1(S(x)) = S(f_2(x)),   f_2(S(x)) = f_1(x)
--
-- i.e. H<z1,z2> = <S(z2), z1>.  Now the iterates are
--
--   iterVec (S^m bot) = < S^{half (m+1)}(bot) , S^{half m}(bot) >
--
-- so phi_1 = ceil(m/2) = half (m+1) -- the complementary stalling pattern
-- 0,1,1,2,2,3,... -- and it again satisfies the refined invariant at
-- exactly d = 2 = r, and again fails the old one.
------------------------------------------------------------------------

Gc2 : FTup -> FTup
Gc2 Y = cons (fcpl zero) (cons (fcpl zero) nil)

Hc2 : FTup -> FTup
Hc2 X = cons (sucF (getF (suc zero) X)) (cons (getF zero X) nil)

iterate-formula2 : (m : Nat) ->
  Eq (iterVec Gc2 Hc2 two (fbot m) nil)
     (cons (fbot (half (suc m))) (cons (fbot (half m)) nil))
iterate-formula2 zero    = refl
iterate-formula2 (suc m) = Eq-cong (\ Z -> Hc2 (appF Z nil)) (iterate-formula2 m)

-- phi_1 for the mirror block
ceilH : Nat -> Nat
ceilH m = half (suc m)

-- ceilH (m+2) = suc (ceilH m), so period 2 again -- and exactly 2
ceilH-IncBy2 : StrictIncBy zero two ceilH
ceilH-IncBy2 m km = LeN-refl (half (suc m))

ceilH-PhiOKBy : PhiOKBy zero two ceilH
ceilH-PhiOKBy = inr ceilH-IncBy2

-- it stalls too -- on the OTHER parity from `half`: here ceilH 1 = ceilH 2 = 1
-- (whereas half stalls at the even steps).  So period 1 is genuinely
-- unavailable for this block as well.
ceilH-stalls : Eq (ceilH (suc zero)) (ceilH (suc (suc zero)))
ceilH-stalls = refl

ceilH-not-IncBy1 : StrictIncBy zero (suc zero) ceilH -> Empty
ceilH-not-IncBy1 si = si (suc zero) tt
