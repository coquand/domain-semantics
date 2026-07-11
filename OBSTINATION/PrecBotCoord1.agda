{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotCoord1
--
-- The recursion-result coupling (coordinate 1) for the finite-incomplete
-- first argument.  When h is Case 2 at coordinate 1 of the inner point
-- B = cons (bot c) (cons v1 Y) -- i.e. h is controlled by the recursion
-- result -- Berry stability (via `base-const`) forces the recursion
-- restriction Fc to be CONSTANT (= S^{m'}(bot)) on a region.  Then
-- f = prec g h is Case 2 at coordinate 0 (W2).
--
-- The one fact needed to feed base-const is a region on which
-- Fc = S^{m'}(bot) EXACTLY; it is pinned by `refine` (>=) together with
-- `fc-le-ext` (<=).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotCoord1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (embed-inj ; LeFTup-length)
open import OBSTINATION.Refine using (refine-aux ; Below-length)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below)
open import OBSTINATION.PrecBaseConst using (base-const)
open import OBSTINATION.PrecBotEngine using (FcFun ; FcConst)
open import OBSTINATION.PrecBotReach using (FcFun-mono ; fc-v1)
open import OBSTINATION.PrecBotExt using (fc-le-ext)
open import OBSTINATION.PrecBotCase23 using (prec-bot-Case2-coord0)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- A region on which Fc equals a target incomplete value exactly.
  ------------------------------------------------------------------------

  realise-eq : (c : Nat) (Y : Tup)
    (o : Or (UO (FcFun rd c) Y) (FcConst rd c Y)) (m' : Nat) ->
    Eq (fc-v1 rd c Y o) (bot m') ->
    (A0Ht : FTup) -> Below A0Ht Y ->
    Sigma FTup (\ Y0 -> Pair (Below Y0 Y)
      (Pair (LeFTup A0Ht Y0) (Eq (FcFun rd c Y0) (fbot m'))))
  realise-eq c Y (inr (mkSigma m'' (mkSigma A0c (mkSigma belc univc)))) m' veq A0Ht belA0Ht =
    mkSigma Y0 (mkSigma belY0 (mkSigma (join-ubT-r bnd)
      (Eq-transport (\ n -> Eq (FcFun rd c Y0) (fbot n)) (bot-inj veq)
        (univc Y0 (join-ubT-l bnd)))))
    where
      Y0 = joinT A0c A0Ht
      bnd = BndT-from-Below belc belA0Ht
      belY0 = Below-joinT belc belA0Ht
      bot-inj : {a b : Nat} -> Eq (bot a) (bot b) -> Eq a b
      bot-inj refl = refl
  realise-eq c Y (inl pf) m' veq A0Ht belA0Ht =
    mkSigma Y0 (mkSigma belY0 (mkSigma (join-ubT-r bnd) fcY0))
    where
      le : LeD (embed (fbot m')) (uoValue pf)
      le = Eq-transport (\ z -> LeD (bot m') z) (Eq-sym veq) (LeD-refl (bot m'))
      rr  = refine-aux (FcFun rd c) Y (fbot m') pf le
      A0r = fst rr
      belA0r = fst (snd rr)
      ler = snd (snd rr)                       -- LeF (fbot m') (Fc A0r)
      Y0  = joinT A0r A0Ht
      bnd = BndT-from-Below belA0r belA0Ht
      belY0 = Below-joinT belA0r belA0Ht
      ge : LeD (bot m') (embed (FcFun rd c Y0))
      ge = LeF-trans {fbot m'} {FcFun rd c A0r} {FcFun rd c Y0}
             ler (FcFun-mono rd c {A0r} {Y0} (join-ubT-l bnd))
      le' : LeD (embed (FcFun rd c Y0)) (bot m')
      le' = Eq-transport (\ z -> LeD (embed (FcFun rd c Y0)) z) veq
              (fc-le-ext (FcFun rd c) (\ {X} {X'} -> FcFun-mono rd c {X} {X'}) Y pf Y0 belY0)
      fcY0 : Eq (FcFun rd c Y0) (fbot m')
      fcY0 = embed-inj {FcFun rd c Y0} {fbot m'}
               (LeD-antisym {embed (FcFun rd c Y0)} {bot m'} le' ge)

  ------------------------------------------------------------------------
  -- h Case 2 at coordinate 1  ->  f Case 2 at coordinate 0.
  ------------------------------------------------------------------------

  hval-coord1-Case2 : (c mh m' : Nat) (Y : Tup)
    (o : Or (UO (FcFun rd c) Y) (FcConst rd c Y)) ->
    Eq (fc-v1 rd c Y o) (bot m') ->
    (a0 : FEl) (A0Ht : FTup)
    (le0 : LeD (embed a0) (bot c)) (belA0Ht : Below A0Ht Y)
    (univH : (Z : FTup) -> Eq (length Z) (suc (suc (length A0Ht))) ->
       Eq (getF (suc zero) Z) (fbot m') ->
       LeFTup (cons a0 A0Ht) (del (suc zero) Z) -> Eq (H Z) (fbot mh)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  hval-coord1-Case2 c mh m' Y o veq a0 A0Ht le0 belA0Ht univH =
    prec-bot-Case2-coord0 rd c mh Y Y0 belY0 hval
    where
      re  = realise-eq c Y o m' veq A0Ht belA0Ht
      Y0  = fst re
      belY0 = fst (snd re)
      A0Ht-le-Y0 = fst (snd (snd re))
      fcY0 = snd (snd (snd re))                -- Eq (Fc Y0) (fbot m')
      lenA0Ht-Y : Eq (length A0Ht) (length Y)
      lenA0Ht-Y = Below-length belA0Ht
      lenY0-Y : Eq (length Y0) (length Y)
      lenY0-Y = Below-length belY0
      -- germ for base-const:  h at coord0 = c, coord1 = m', is constant mh.
      germN0 : (X : FTup) -> LeFTup Y0 X ->
               Eq (H (cons (fbot c) (cons (fbot m') X))) (fbot mh)
      germN0 X leX =
        univH Z lenZ refl delZ
        where
          Z : FTup
          Z = cons (fbot c) (cons (fbot m') X)
          lenX-A0Ht : Eq (length X) (length A0Ht)
          lenX-A0Ht = Eq-trans (Eq-sym (LeFTup-length {Y0} {X} leX))
                        (Eq-trans lenY0-Y (Eq-sym lenA0Ht-Y))
          lenZ : Eq (length Z) (suc (suc (length A0Ht)))
          lenZ = Eq-cong (\ n -> suc (suc n)) lenX-A0Ht
          delZ : LeFTup (cons a0 A0Ht) (cons (fbot c) X)
          delZ = mkSigma le0 (LeFTup-trans-local A0Ht-le-Y0 leX)
            where
              LeFTup-trans-local : {A B C : FTup} -> LeFTup A B -> LeFTup B C -> LeFTup A C
              LeFTup-trans-local {A} {B} {C} p q = LeTup-trans {embedTup A} {embedTup B} {embedTup C} p q
      -- Neq for base-const: f(cons(fbot c) Y0) = fbot m'.
      Neq : Eq (PF G H (cons (fbot c) Y0)) (fbot m')
      Neq = fcY0
      -- base-const: Fc is constant fbot m' on { X >= Y0 }.
      fcConst : (X : FTup) -> LeFTup Y0 X -> Eq (FcFun rd c X) (fbot m')
      fcConst X leX =
        Eq-trans (base-const rd c m' mh Y0 Neq germN0 c X (LeN-refl c) leX) Neq
      -- hval for W2:  h(cons(fbot c)(cons(Fc X) X)) = fbot mh on the region.
      hval : (X : FTup) -> LeFTup Y0 X ->
             Eq (H (cons (fbot c) (cons (FcFun rd c X) X))) (fbot mh)
      hval X leX =
        Eq-transport
          (\ w -> Eq (H (cons (fbot c) (cons w X))) (fbot mh))
          (Eq-sym (fcConst X leX))
          (germN0 X leX)
