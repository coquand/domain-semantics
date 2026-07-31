{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecIvP
--
-- THE RECURSION TRACE'S INDEX IS EVENTUALLY CONSTANT -- NO HYPOTHESES.
--
-- `TrPrecPar.PAR.ivP-EvConstN` takes three facts about the recursion
-- chain as parameters: that it is monotone in the depth, that it is
-- monotone in the parameter levels, and whether the recursive value
-- ever becomes a numeral.  For the trace of an ACTUAL primitive
-- recursion all three are theorems -- `TrPrecDec.Vd-mono`,
-- `Vd-mono-L`, `Vd-tot-or-never`, the last of them Proposition 1
-- applied to the chain.  This file discharges them.
--
-- The `stop` case is trivial: a `stop` waits for nothing, so every
-- fold step is `qsel _ (inl tt) = 0` and the index is constantly `0`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecIvP where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl)
open import OBSTINATION.Tuples using (FTup ; Tup)
open import OBSTINATION.Property using (UO)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (MonoTr ; MonoF)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMP1 using (MP1T)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TrPrecFun using (precFun)
open import OBSTINATION.TrPrec using (module R ; module P)
open import OBSTINATION.TrPrecDec using
  (Vd-mono ; Vd-mono-L ; Vd-tot-or-never)
open import OBSTINATION.TrPrecPar using (module PAR)

------------------------------------------------------------------------
-- A `stop` STEP TERM NEVER WAITS, SO THE FOLD IS CONSTANTLY `0`
------------------------------------------------------------------------

Qd-stop : (p : Nat) (v : FEl) (L : Nat -> Nat) (m : Nat)
        -> Eq (R.Qd p (stop v) L m) zero
Qd-stop p v L zero    = refl
Qd-stop p v L (suc j) = refl

------------------------------------------------------------------------
-- THE INDEX CLAUSE OF MP1 FOR `precTr`
------------------------------------------------------------------------

precTr-ivP : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
           -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
           -> Den (suc (suc p)) Th h
           -> MonoF p g -> MonoF (suc (suc p)) h
           -> ((A : Tup) -> Eq (length A) (suc p) -> UO (precFun g h) A)
           -> EvConstN (P.ivP p Th)
precTr-ivP p (stop v) g h mth m1th dh mg mh uo =
  mkSigma zero go
  where
    go : (n : Nat) -> LeN zero n
       -> Eq (P.ivP p (stop v) n) (P.ivP p (stop v) zero)
    go n ln =
      Eq-trans
        (Qd-stop p v (P.Lv p (stop v) n) (P.Lv p (stop v) n zero))
        (Eq-sym
          (Qd-stop p v (P.Lv p (stop v) zero) (P.Lv p (stop v) zero zero)))
precTr-ivP p (node ivh ivhr ovh conth) g h mth m1th dh mg mh uo =
  PAR.ivP-EvConstN p ivh ivhr ovh conth mth m1th
    (\ L -> Vd-mono p Th g h dh mg mh L)
    (\ L L' lp -> Vd-mono-L p Th g h dh mg mh L L' lp)
    (\ L -> Vd-tot-or-never p Th g h dh mg mh uo L)
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth
