{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrShare
--
-- SHARING: TWO ARGUMENTS READING THE SAME COORDINATE.
--
--     g (0 , v) = 0 ,  g (S u , v) = v        -- one level of u, then v
--     f (x)     = g (x , x)                   -- so f is the identity
--
-- This is the example that killed the FIRST `TrComp`, which drove the
-- arguments one step at a time: the second copy of `x` re-demanded level
-- 0, the walk charged it a second time, and the composite answered
-- `S^1 bot` at `S^2 bot`.
--
-- With the state being the composite's own LEVELS (`W.L`) and each
-- argument REPLAYED against them, raising a level advances every argument
-- that was waiting for it, so the sharing is automatic.  Below, trace and
-- `evalF` agree at `bot`, `S bot` and `S^2 bot`, all by `refl`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrShare where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; zerf ; proj ; succ ; comp ; prec ; evalF)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrComp using (compTr)
open import OBSTINATION.TrPrec using (precTr)

two : Nat
two = suc (suc zero)

three : Nat
three = suc two

-- g (0 , v) = 0 ;  g (S u , v) = v
gPR : PR
gPR = prec zerf (proj two)

-- f (x) = g (x , x)
fPR : PR
fPR = comp gPR (cons (proj zero) (cons (proj zero) nil))

gTr : Tr two
gTr = precTr (suc zero) (zerfTr (suc zero)) (projTr three two tt)

fTr : Tr (suc zero)
fTr = compTr two gTr (suc zero) (\ _ -> projTr (suc zero) zero tt)

------------------------------------------------------------------------
-- trace = evalF, at every level
------------------------------------------------------------------------

agree-0 : Eq (sem (suc zero) fTr (cons (fbot zero) nil))
             (evalF fPR (cons (fbot zero) nil))
agree-0 = refl

agree-1 : Eq (sem (suc zero) fTr (cons (fbot (suc zero)) nil))
             (evalF fPR (cons (fbot (suc zero)) nil))
agree-1 = refl

agree-2 : Eq (sem (suc zero) fTr (cons (fbot two) nil))
             (evalF fPR (cons (fbot two) nil))
agree-2 = refl

agree-3 : Eq (sem (suc zero) fTr (cons (fbot three) nil))
             (evalF fPR (cons (fbot three) nil))
agree-3 = refl

-- and the values really are the identity, not something constant
val-2 : Eq (sem (suc zero) fTr (cons (fbot two) nil)) (fbot two)
val-2 = refl

val-3 : Eq (sem (suc zero) fTr (cons (fbot three) nil)) (fbot three)
val-3 = refl
