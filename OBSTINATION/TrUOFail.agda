{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrUOFail
--
-- **MP1 ALONE DOES NOT IMPLY PROPOSITION 1.**
--
--     uo-fails : UO (\ _ -> fbot zero) (cons (cpl zero) nil) -> Empty
--
-- with a trace that has EVERYTHING MP1 asks for:
--
--     T = stop (fbot zero) : Tr 1 ,   MonoTr 1 T = Top ,   MP1T 1 T = Top ,
--     Den 1 T (\ _ -> fbot zero)
--
-- so `traceOf-MP1np`'s hypotheses are all met by `T`, and yet `Property.UO`
-- fails for what it denotes, at the ALL-COMPLETE point `A = (0)`.
--
-- WHY.  At an all-complete `A` the three cases of `UO` leave no room:
-- Case 2 needs a coordinate of `A` that is incomplete and finite, Case 3
-- needs one that is `S^omega(bot)`, and `A` has neither -- so Case 1 must
-- hold, i.e. the value must be a NUMERAL.  A constant `S^m(bot)` is not.
--
-- WHAT IT MEANS FOR THE CONVERSE.  `Prop 1 from MP1` cannot be a mere
-- repackaging of `TrVerdict.verdict-of`: the missing ingredient is
-- TOTALITY -- a primitive recursive term applied to numerals returns a
-- numeral -- which the trace does not know and which has to be carried as
-- a separate structural invariant (in trace terms: every `stop` reachable
-- in the trace of a PR term carries a COMPLETE value, and this is where
-- `zerfTr = stop (fcpl 0)` and `projPick … (yes _) = stop (fcpl v)` are
-- doing work).
--
-- Note this does NOT weaken `TrTermMP1.traceOf-MP1np`: that direction is
-- proved, and Proposition 1 is not used in it.  It says only that the
-- OTHER direction needs one more input.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrUOFail where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (D ; bot ; cpl ; inf ; FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using
  (FTup ; Tup ; LeFTup ; LeFTup-refl ; embedTup)
open import OBSTINATION.Property using
  (UO ; uo1 ; uo2 ; uo3 ; Case1 ; Case2 ; Case3 ; getF ; IncompleteFinite)
open import OBSTINATION.TraceDef using (Tr ; stop)
open import OBSTINATION.TrSat using (MonoTr)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMP1 using (MP1T)
open import OBSTINATION.TrVerdict using (embedTup-len ; LeTup-len)

------------------------------------------------------------------------
-- THE TRACE, AND WHAT IT DENOTES
------------------------------------------------------------------------

f0 : FTup -> FEl
f0 _ = fbot zero

T0 : Tr (suc zero)
T0 = stop (fbot zero)

T0-mono : MonoTr (suc zero) T0
T0-mono = tt

T0-mp1 : MP1T (suc zero) T0
T0-mp1 = tt

T0-den : Den (suc zero) T0 f0
T0-den X lx = refl

------------------------------------------------------------------------
-- THE POINT: ONE COORDINATE, THE NUMERAL 0
------------------------------------------------------------------------

A0pt : Tup
A0pt = cons (cpl zero) nil

------------------------------------------------------------------------
-- ... AND `UO` FAILS THERE
------------------------------------------------------------------------

uo-fails : UO f0 A0pt -> Empty
------------------------------------------------------------------------
-- Case 1 wants a numeral; the value is `S^0(bot)`
------------------------------------------------------------------------
uo-fails (uo1 (mkSigma A0 (mkSigma bel (mkSigma m eq)))) = bad (eq A0 (LeFTup-refl A0))
  where
    bad : Not (Eq (fbot zero) (fcpl m))
    bad ()
------------------------------------------------------------------------
-- Case 2 wants an incomplete finite coordinate; the only one is `cpl 0`
------------------------------------------------------------------------
uo-fails (uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma li (mkSigma incf rest))))))) =
  shape i (Eq-transport (\ z -> LeN (suc i) z) len1 li) incf
  where
    len1 : Eq (length A0) (suc zero)
    len1 =
      Eq-trans (Eq-sym (embedTup-len A0))
        (LeTup-len (embedTup A0) A0pt bel)

    shape : (c : Nat) -> LeN (suc c) (suc zero)
          -> IncompleteFinite (nth (bot zero) c A0pt) -> Empty
    shape zero    lc ic = ic
    shape (suc c) ()  ic
------------------------------------------------------------------------
-- Case 3 wants an infinite coordinate; there is none
------------------------------------------------------------------------
uo-fails (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf rest))))) = shape i einf
  where
    shape : (c : Nat) -> Eq (nth (bot zero) c A0pt) inf -> Empty
    shape zero          ()
    shape (suc zero)    ()
    shape (suc (suc c)) ()
