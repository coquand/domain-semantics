{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterSeq
--
-- The VECTOR Kleene fixpoint sequence for mutual iteration at the
-- infinite recursion argument -- the port of `USeq` from a single value
-- to an r-tuple of values.
--
-- For a block f_1,...,f_r defined by mutual iteration, the value at
-- (S^omega(bot), Y) is the least fixpoint of the r-ary operator
--
--   Phi(zbar) = < h_1-hat(zbar, Y) , ... , h_r-hat(zbar, Y) >
--
-- approximated from below by  u 0 = <bot,...,bot>,  u(k+1) = Phi(u k).
--
-- The whole order-theoretic backbone of `USeq` ports COMPONENTWISE and
-- unchanged -- it uses only monotonicity of the extension and congruence
-- of the step:
--   * uVec-mono : the sequence is increasing;
--   * uVec-le   : hence monotone in the index;
--   * uVec-stab : once two consecutive terms agree it is constant onward.
--
-- The tuple-valued extension `extT` is assembled from the JOINT
-- obstination witness (`PropertyVec.UOMall`) by `Build.buildB`.
--
-- What does NOT port is the DISPATCH (`PrecInfDispatch`): with r mutually
-- defined functions each h_i pins a slot, giving a read-graph rather than
-- a single index.  That is the remaining open step.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterSeq where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using (UOall ; getF)
open import OBSTINATION.PropertyAt using (getF-le)
open import OBSTINATION.PropertyVec using (compOf ; UOM-each ; UOMall)
open import OBSTINATION.Extension using (ext)
open import OBSTINATION.ExtMono using (ext-mono)
open import OBSTINATION.CompPull using (Mono)
open import OBSTINATION.PhiProps using (addN)
open import OBSTINATION.PhiComp using (le-to-addN)
open import OBSTINATION.Build using (buildB ; length-buildB ; buildB-LeTup)
open import OBSTINATION.IterFun using (MonoT ; IterData)

------------------------------------------------------------------------
-- Append and constant tuples, on D-valued tuples
------------------------------------------------------------------------

appT : Tup -> Tup -> Tup
appT nil        B = B
appT (cons a A) B = cons a (appT A B)

botT : Nat -> Tup
botT zero    = nil
botT (suc r) = cons botD (botT r)

length-botT : (r : Nat) -> Eq (length (botT r)) r
length-botT zero    = refl
length-botT (suc r) = Eq-cong suc (length-botT r)

botT-le : (r : Nat) (Z : Tup) -> Eq (length Z) r -> LeTup (botT r) Z
botT-le zero    nil        e = tt
botT-le zero    (cons _ _) ()
botT-le (suc r) nil        ()
botT-le (suc r) (cons z zs) e = mkSigma (LeD-botD z) (botT-le r zs (suc-inj e))

appT-mono : {A B C E : Tup} -> LeTup A B -> LeTup C E -> LeTup (appT A C) (appT B E)
appT-mono {nil}      {nil}      lAB lCE = lCE
appT-mono {nil}      {cons _ _} ()  lCE
appT-mono {cons _ _} {nil}      ()  lCE
appT-mono {cons a A} {cons b B} lAB lCE =
  mkSigma (fst lAB) (appT-mono {A} {B} (snd lAB) lCE)

------------------------------------------------------------------------
-- Componentwise monotonicity of a tuple-valued function
------------------------------------------------------------------------

compOf-mono : (H : FTup -> FTup) -> MonoT H -> (i : Nat) -> Mono (compOf H i)
compOf-mono H mh i le = getF-le i (mh le)

------------------------------------------------------------------------
-- The tuple-valued Scott-continuous extension
--
-- Component i is the ordinary extension of  getF i o H, whose UOall comes
-- from the joint witness by `UOM-each`.  buildB assembles the r of them.
------------------------------------------------------------------------

module _ (H : FTup -> FTup) (r : Nat) (uo : UOMall H r) where

  extC : (i : Nat) -> LeN (suc i) r -> UOall (compOf H i)
  extC i lt A = UOM-each H r A (uo A) i lt

  extT : Tup -> Tup
  extT A = buildB r (\ i lt -> ext (compOf H i) (extC i lt) A)

  extT-length : (A : Tup) -> Eq (length (extT A)) r
  extT-length A = length-buildB r (\ i lt -> ext (compOf H i) (extC i lt) A)

  extT-mono : MonoT H -> {A B : Tup} -> LeTup A B -> LeTup (extT A) (extT B)
  extT-mono mh {A} {B} leAB =
    buildB-LeTup r
      (\ i lt -> ext (compOf H i) (extC i lt) A)
      (\ i lt -> ext (compOf H i) (extC i lt) B)
      (\ i lt -> ext-mono (compOf H i) (compOf-mono H mh i) (extC i lt) leAB)

------------------------------------------------------------------------
-- The vector Kleene sequence
------------------------------------------------------------------------

module _ (idt : IterData) (Y : Tup) where
  open IterData idt

  -- Phi zbar = < h_1-hat , ... , h_r-hat > (zbar, Y)
  stepV : Tup -> Tup
  stepV z = extT H ar uoh (appT z Y)

  uVec : Nat -> Tup
  uVec zero    = botT ar
  uVec (suc k) = stepV (uVec k)

  ------------------------------------------------------------------------
  -- Lengths: the sequence stays an ar-tuple
  ------------------------------------------------------------------------

  stepV-length : (z : Tup) -> Eq (length (stepV z)) ar
  stepV-length z = extT-length H ar uoh (appT z Y)

  uVec-length : (k : Nat) -> Eq (length (uVec k)) ar
  uVec-length zero    = length-botT ar
  uVec-length (suc k) = stepV-length (uVec k)

  ------------------------------------------------------------------------
  -- stepV is monotone, and the sequence increases
  ------------------------------------------------------------------------

  stepV-mono : {a b : Tup} -> LeTup a b -> LeTup (stepV a) (stepV b)
  stepV-mono {a} {b} le =
    extT-mono H ar uoh monoH {appT a Y} {appT b Y} (appT-mono le (LeTup-refl Y))

  uVec-mono : (k : Nat) -> LeTup (uVec k) (uVec (suc k))
  uVec-mono zero    = botT-le ar (uVec (suc zero)) (uVec-length (suc zero))
  uVec-mono (suc k) = stepV-mono (uVec-mono k)

  -- monotone in the index
  uVec-le-from : (k d : Nat) -> LeTup (uVec k) (uVec (addN k d))
  uVec-le-from k zero    = LeTup-refl (uVec k)
  uVec-le-from k (suc d) =
    LeTup-trans {uVec k} {uVec (addN k d)} {uVec (suc (addN k d))}
      (uVec-le-from k d) (uVec-mono (addN k d))

  uVec-le : (k n : Nat) -> LeN k n -> LeTup (uVec k) (uVec n)
  uVec-le k n kn =
    Eq-transport (\ z -> LeTup (uVec k) (uVec z)) (snd rr) (uVec-le-from k (fst rr))
    where rr = le-to-addN k n kn

  ------------------------------------------------------------------------
  -- Stabilisation propagates forward
  ------------------------------------------------------------------------

  module _ (k : Nat) (e : Eq (uVec k) (uVec (suc k))) where

    stabV-step : (m : Nat) -> Eq (uVec k) (uVec m) -> Eq (uVec k) (uVec (suc m))
    stabV-step m em = Eq-sym (Eq-trans (Eq-cong stepV (Eq-sym em)) (Eq-sym e))

    stabV-add : (d : Nat) -> Eq (uVec k) (uVec (addN k d))
    stabV-add zero    = refl
    stabV-add (suc d) = stabV-step (addN k d) (stabV-add d)

    uVec-stab : (n : Nat) -> LeN k n -> Eq (uVec k) (uVec n)
    uVec-stab n kn =
      Eq-transport (\ z -> Eq (uVec k) (uVec z)) (snd rr) (stabV-add (fst rr))
      where rr = le-to-addN k n kn
