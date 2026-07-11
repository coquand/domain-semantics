{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotPull
--
-- The single-coordinate "pull-back" for the finite-incomplete first
-- argument.  The step function unfolds to
--
--   f(cons x X')  =  h(cons (pred x) (cons (rec) X'))     (x >= S^{c+1} bot)
--
-- with  rec = precF g h (pred x) X'.  Given a finite witness region B0
-- below h's inner point  B = cons (bot c) (cons v1 Y), we pull it back to
-- a region A0t <= Y of the tail such that, for EVERY coord0-predecessor
-- p >= S^c(bot) and every tail X' >= A0t, the actual h-input tuple
-- dominates B0:
--
--   B0  <=  cons p (cons (precF g h p X') X').
--
-- Coordinate 0 (>= b00) is discharged since  b00 <= S^c(bot) <= p;
-- coordinate 1 (the recursion result) by `frec-ge` (reach + monotonicity);
-- the tail (>= B0-tail) by the join.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotPull where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.PrecBotEngine using (FcFun)
open import OBSTINATION.PrecBotReach using (frec-ge)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below)
open import OBSTINATION.PrecFun using (RecData ; precFun)

LeFTup-trans : {A B C : FTup} -> LeFTup A B -> LeFTup B C -> LeFTup A C
LeFTup-trans {A} {B} {C} p q = LeTup-trans {embedTup A} {embedTup B} {embedTup C} p q

module _ (rd : RecData) where
  open RecData rd

  pull-h : (c : Nat) (Y : Tup) (v1 : D)
    (reach : (u : FEl) -> LeD (embed u) v1 ->
       Sigma FTup (\ A0' -> Pair (Below A0' Y)
         ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X'))))
    (B0 : FTup) -> Below B0 (cons (bot c) (cons v1 Y)) ->
    Sigma FTup (\ A0t -> Pair (Below A0t Y)
      ((p : FEl) (X' : FTup) -> LeF (fbot c) p -> LeFTup A0t X' ->
         LeFTup B0 (cons p (cons (precFun G H p X') X'))))
  pull-h c Y v1 reach nil                        ()
  pull-h c Y v1 reach (cons b00 nil)             (mkSigma _ ())
  pull-h c Y v1 reach (cons b00 (cons b01 B0t))
    (mkSigma le00 (mkSigma le01 belB0t)) =
    mkSigma A0t (mkSigma belA0t dom)
    where
      rr    = reach b01 le01
      A0''  = fst rr
      belA'' = fst (snd rr)
      domFc  = snd (snd rr)
      A0t    = joinT A0'' B0t
      bndT   = BndT-from-Below belA'' belB0t
      belA0t = Below-joinT belA'' belB0t
      dom : (p : FEl) (X' : FTup) -> LeF (fbot c) p -> LeFTup A0t X' ->
            LeFTup (cons b00 (cons b01 B0t)) (cons p (cons (precFun G H p X') X'))
      dom p X' lecp leX' =
        mkSigma
          (LeD-trans {embed b00} {bot c} {embed p} le00 lecp)
          (mkSigma
            (frec-ge rd c b01 A0'' domFc p X' lecp leA''X')
            leB0tX')
        where
          leA''X' = LeFTup-trans (join-ubT-l bndT) leX'
          leB0tX' = LeFTup-trans (join-ubT-r bndT) leX'
