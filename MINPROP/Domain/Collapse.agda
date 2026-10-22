{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Collapse.agda  (MINPROP/ — Pi + U + Prop)
--
-- The semantic core of definitional proof irrelevance:
--
--   prop-collapse : u : a  ->  IsProp a  ->  u = Bot
--
-- i.e. the only approximant of a proof is Bot.  A Prop code is Bot (whose
-- only member is Bot) or a Pi code with Prop-code values; a member of the
-- latter is Bot or a coherent FunEl, whose first edge value lies in a
-- Prop code of smaller RANK, hence is Bot by induction -- contradicting
-- the coherence requirement that edge values are not Bot (val-nbot).
-- Fuel `k` bounds the RANK of the type, as in MemProps.
--
-- Plus the public Prop-membership interface (u : Prop <-> u : U, IsProp u).
--
-- NO postulates.
------------------------------------------------------------------------

module MINPROP.Domain.Collapse where

open import MINPROP.Domain.Basic
  using ( Top ; tt ; Empty ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-trans ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MINPROP.Domain.Order
  using ( RANK ; RANKFun ; EvalFun ; LeCode ; NotBot ; CFTcons ; RANK-ev ; ev-bridge )
open import MINPROP.Domain.MemStage using ( IsProp ; IsPropFun )
open import MINPROP.Domain.MemUnfold
  using ( finMemC-prop-U ; finMemC-prop-isProp ; finMemC-prop-mk )
open import MINPROP.Domain.Membership
  using ( FinMem ; FinMemFun ; finMem-funel-fun ; finMem-funel-coh )
open import MINPROP.Domain.PropCodes public

------------------------------------------------------------------------
-- Prop membership interface.
------------------------------------------------------------------------

open MINPROP.Domain.MemStage public using ( IsProp ; IsPropFun )

finMem-prop-U : (u : FinEl) -> FinMem u PropCode -> FinMem u UCode
finMem-prop-U = finMemC-prop-U

finMem-prop-isProp : (u : FinEl) -> FinMem u PropCode -> IsProp u
finMem-prop-isProp = finMemC-prop-isProp

finMem-prop-mk : (u : FinEl) -> FinMem u UCode -> IsProp u -> FinMem u PropCode
finMem-prop-mk = finMemC-prop-mk

------------------------------------------------------------------------
-- Collapse.
------------------------------------------------------------------------

private
  RANK-EvalFun : (h : FinFun) (u : FinEl) -> Le (RANK (EvalFun h u)) (RANKFun h)
  RANK-EvalFun h u =
    let M = max (RANKFun h) (RANK u)
    in Eq-transport (\ x -> Le (RANK x) (RANKFun h))
         (Eq-sym (ev-bridge M h u (Le-refl M)))
         (RANK-ev (suc M) h u)

  nbot-absurd : {A : Set} (v : FinEl) -> Eq v Bot -> NotBot v -> A
  nbot-absurd .Bot refl ()

collapse-k : (k : Nat) (u a : FinEl) -> Le (RANK a) k -> FinMem u a -> IsProp a -> Eq u Bot
collapse-k k       Bot          a            ba mem ip = refl
collapse-k k       UCode        Bot          ba ()  ip
collapse-k k       PropCode     Bot          ba ()  ip
collapse-k k       (FunEl h)    Bot          ba ()  ip
collapse-k k       (PiCode c g) Bot          ba ()  ip
collapse-k k       u            UCode        ba mem ()
collapse-k k       u            PropCode     ba mem ()
collapse-k k       u            (FunEl g)    ba mem ()
collapse-k k       UCode        (PiCode c g) ba ()  ip
collapse-k k       PropCode     (PiCode c g) ba ()  ip
collapse-k k       (PiCode b f) (PiCode c g) ba ()  ip
collapse-k zero    (FunEl h)    (PiCode c g) ()  mem ip
collapse-k (suc k) (FunEl nil)  (PiCode c g) ba mem ip with finMem-funel-coh nil c g mem
... | ()
collapse-k (suc k) (FunEl (cons p ps)) (PiCode c g) ba mem ip =
  let coh = finMem-funel-coh (cons p ps) c g mem
      val = snd (fst (finMem-funel-fun (cons p ps) c g mem))
      bnd = Le-trans (RANK (EvalFun g (fst p))) (RANKFun g) k
              (RANK-EvalFun g (fst p))
              (Le-trans (RANKFun g) (max (RANK c) (RANKFun g)) k (Le-max-r (RANK c) (RANKFun g)) ba)
      isBot = collapse-k k (snd p) (EvalFun g (fst p)) bnd val (IsProp-EvalFun g (fst p) ip)
  in nbot-absurd (snd p) isBot (CFTcons.val-nbot coh)

-- The only approximant of an inhabitant of a Prop code is Bot.
prop-collapse : (u a : FinEl) -> FinMem u a -> IsProp a -> Eq u Bot
prop-collapse u a = collapse-k (RANK a) u a (Le-refl (RANK a))

-- Form used by adequacy: u : a, a <= a', a' : Prop.
prop-collapse-le : (u a a' : FinEl) -> FinMem u a -> LeCode a a' -> FinMem a' PropCode -> Eq u Bot
prop-collapse-le u a a' mem le pa' =
  prop-collapse u a mem (IsProp-down a a' le (finMem-prop-isProp a' pa'))
