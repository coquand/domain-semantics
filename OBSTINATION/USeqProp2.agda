{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.USeqProp2
--
-- The second property of the fixpoint sequence (min1.pdf p.3): if a
-- finite element  a <= u_n,  then one can compute  m_0  and a finite
-- Y_0 <= Y  with  a <= f(S^{m_0}(bot), Y_0),  where  f = prec g h.
--
-- This is what lets the infinite-argument argument descend from the
-- abstract Kleene approximant u_n back to genuine finite stages of f.
-- Proof by recurrence on n:
--   * n = 0 : u_0 = bot, so a = bot and  a <= f(bot, botLike Y) = bot.
--   * n+1   : u_{n+1} = h-hat(S^omega(bot), u_n, Y).  Compactness (refine)
--     gives a finite  <b_0, c_0, Y_0'> <= <S^omega(bot), u_n, Y>  with
--     a <= h(b_0, c_0, Y_0'); apply the induction hypothesis to
--     c_0 <= u_n to get  c_0 <= f(S^{m_1}(bot), Y_1); then
--     m_0 = 1 + max(t, m_1)  and  Y_0 = Y_0' \/ Y_1  work, by
--     monotonicity of h and of f.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.USeqProp2 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property using (UOall ; Below)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Refine using (refine)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (BndT-from-Below ; Below-joinT)
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono ; precFun)
open import OBSTINATION.USeq using (uSeq)

module _ (rd : RecData) where
  open RecData rd

  -- the target: a is realised at a finite stage of f = prec g h
  Realised : (Y : Tup) (a : FEl) -> Set
  Realised Y a =
    Sigma Nat (\ m0 -> Sigma FTup (\ Y0 ->
      Pair (Below Y0 Y) (LeF a (PF G H (cons (fbot m0) Y0)))))

  uSeq-prop2 : (Y : Tup) (n : Nat) (a : FEl) ->
    LeD (embed a) (uSeq rd Y n) -> Realised Y a
  -- base
  uSeq-prop2 Y zero (fbot zero) le =
    mkSigma zero (mkSigma (botLike Y) (mkSigma (Below-botLike Y) tt))
  uSeq-prop2 Y zero (fbot (suc s)) ()
  uSeq-prop2 Y zero (fcpl s)       ()
  -- step
  uSeq-prop2 Y (suc n) a le = step-case (fst r) (fst (snd r)) (snd (snd r))
    where
      B : Tup
      B = cons inf (cons (uSeq rd Y n) Y)
      r = refine H uoh B a le
      step-case : (B0 : FTup) -> Below B0 B -> LeF a (H B0) -> Realised Y a
      step-case nil                    () aH
      step-case (cons b0 nil)          bel aH = Empty-elim (snd bel)
      step-case (cons b0 (cons c0 Y0')) bel aH =
        mkSigma (suc M) (mkSigma Y0 (mkSigma belY0 final))
        where
          b0-le-inf = fst bel
          c0-le-un  = fst (snd bel)
          Y0'-le-Y  = snd (snd bel)
          tE = le-inf-fbot b0 b0-le-inf
          t  = fst tE
          eqb0 = snd tE
          ih = uSeq-prop2 Y n c0 c0-le-un
          m1    = fst ih
          Y1    = fst (snd ih)
          belY1 = fst (snd (snd ih))
          ihLe  = snd (snd (snd ih))
          M  = maxN t m1
          bnd = BndT-from-Below Y0'-le-Y belY1
          Y0 = joinT Y0' Y1
          belY0 : Below Y0 Y
          belY0 = Below-joinT Y0'-le-Y belY1
          fM = PF G H (cons (fbot M) Y0)
          le-b0 : LeD (embed b0) (bot M)
          le-b0 = Eq-transport (\ z -> LeD (embed z) (bot M)) (Eq-sym eqb0) (maxN-le-l t m1)
          monoF : LeF (PF G H (cons (fbot m1) Y1)) fM
          monoF = PF-mono G H monoG monoH {cons (fbot m1) Y1} {cons (fbot M) Y0}
                    (mkSigma (maxN-le-r t m1) (join-ubT-r bnd))
          le-c0 : LeF c0 fM
          le-c0 = LeF-trans {c0} {PF G H (cons (fbot m1) Y1)} {fM} ihLe monoF
          bigLe : LeFTup (cons b0 (cons c0 Y0')) (cons (fbot M) (cons fM Y0))
          bigLe = mkSigma le-b0 (mkSigma le-c0 (join-ubT-l bnd))
          final : LeF a (H (cons (fbot M) (cons fM Y0)))
          final = LeF-trans {a} {H (cons b0 (cons c0 Y0'))}
                    {H (cons (fbot M) (cons fM Y0))}
                    aH (monoH {cons b0 (cons c0 Y0')} {cons (fbot M) (cons fM Y0)} bigLe)
