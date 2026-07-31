{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecIvPMP
--
-- **MP1's INDEX CLAUSE FOR `precTr`, WITHOUT PROPOSITION 1.**
--
--     precTr-ivP-mp : MonoTr Th -> MP1T Th -> Den Th h
--                   -> MonoF g -> MonoF h
--                   -> EvConstN (P.ivP p Th)
--
-- `TrPrecIvP.precTr-ivP` needed one more hypothesis,
--
--     (A : Tup) -> Eq (length A) (suc p) -> UO (precFun g h) A
--
-- -- Proposition 1 for THE RECURSION ITSELF -- and spent it in exactly one
-- place, `TrPrecDec.Vd-tot-or-never`.  `TrPrecDecMP.DEC.decide` proves
-- that from `TrMP1.Verdict ovh` instead, and `Verdict ovh` is the second
-- component of `MP1T Th`, which `precTr-ivP` ALREADY had in scope.  So
-- the hypothesis simply disappears: the induction hypothesis (MP1 for the
-- step term) was always enough.
--
-- `Vd-mono` and `Vd-mono-L`, the other two facts `TrPrecPar.PAR` needs,
-- never used Proposition 1 -- they are `Den` plus monotonicity.
--
-- WHAT IS STILL OPEN.  This is the INDEX half only.  MP1's VALUE half
-- (`TrMP1Red.mp1T-from-iv`, via `TrVerdict.verdict-of` and
-- `TrUOfrz.uofrz-PR`) still reads `Verdict ov` off Proposition 1, and
-- there the use is self-referential in the same way.  See
-- `NEXT_SESSION_MP1_NOPROP1.md`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecIvPMP where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (MonoTr ; MonoF)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMP1 using (MP1T ; verdict-TN)
open import OBSTINATION.TrMPT using (MPT ; mpT-TN)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TrPrec using (module R ; module P)
open import OBSTINATION.TrPrecDec using (Vd-mono ; Vd-mono-L)
open import OBSTINATION.TrPrecPar using (module PAR)
open import OBSTINATION.TrPrecIvP using (Qd-stop)
open import OBSTINATION.TrPrecDecMP using (module DEC)

precTr-ivP-mp : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
              -> MonoTr (suc (suc p)) Th -> MPT (suc (suc p)) Th
              -> Den (suc (suc p)) Th h
              -> MonoF p g -> MonoF (suc (suc p)) h
              -> EvConstN (P.ivP p Th)
precTr-ivP-mp p (stop v) g h mth m1th dh mg mh =
  mkSigma zero go
  where
    go : (n : Nat) -> LeN zero n
       -> Eq (P.ivP p (stop v) n) (P.ivP p (stop v) zero)
    go n ln =
      Eq-trans
        (Qd-stop p v (P.Lv p (stop v) n) (P.Lv p (stop v) n zero))
        (Eq-sym
          (Qd-stop p v (P.Lv p (stop v) zero) (P.Lv p (stop v) zero zero)))
precTr-ivP-mp p (node ivh ivhr ovh conth) g h mth m1th dh mg mh =
  PAR.ivP-EvConstN p ivh ivhr ovh conth mth m1th
    (\ L -> Vd-mono p Th g h dh mg mh L)
    (\ L L' lp -> Vd-mono-L p Th g h dh mg mh L L' lp)
    (\ L -> DEC.decide p ivh ivhr ovh conth L (fst mth)
              (Vd-mono p Th g h dh mg mh L) (mpT-TN (suc (suc p)) Th mth m1th))
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth
