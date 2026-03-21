{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinitaryProjection.agda
--
-- Finitary projection on finite elements, corresponding to
-- Proposition 1 of Coquand & Huber (2018).
--
-- pCode a u : FinEl  with  pCode a u = u  iff  FinMem u a
--
-- Forward direction proved.  Backward direction requires coherence
-- lemmas that are work in progress.
------------------------------------------------------------------------

module FinitaryProjection where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; List ; nil ; cons ; Eq ; refl ;
              Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              pair-eq ; cons-eq)
open import PaperSemantics using (EvalFun ; FinMem ; FinMemFun ; FinMemAllU ;
  Coherent ; CoherentFun ; CoherentFunTail ; cft-from-cf)

------------------------------------------------------------------------
-- pCode: finitary projection on finite elements
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  pCode : FinEl -> FinEl -> FinEl
  pCode Bot          u            = Bot
  pCode UCode        UCode        = UCode
  pCode UCode        Bot          = Bot
  pCode UCode        (FunEl g)    = Bot
  pCode UCode        (PiCode a f) = PiCode (pCode UCode a) (projectUFun a f)
  pCode (FunEl g)    u            = Bot
  pCode (PiCode a f) Bot          = Bot
  pCode (PiCode a f) UCode        = Bot
  pCode (PiCode a f) (FunEl g)    = FunEl (projectPiFun a f g)
  pCode (PiCode a f) (PiCode b h) = Bot

  projectUFun : FinEl -> FinFun -> FinFun
  projectUFun a nil         = nil
  projectUFun a (cons p ps) =
    cons (mkSigma (pCode a (fst p)) (pCode UCode (snd p)))
         (projectUFun a ps)

  projectPiFun : FinEl -> FinFun -> FinFun -> FinFun
  projectPiFun a f nil         = nil
  projectPiFun a f (cons p ps) =
    let x' = pCode a (fst p)
    in cons (mkSigma x' (pCode (EvalFun f x') (snd p)))
            (projectPiFun a f ps)

------------------------------------------------------------------------
-- Basic helpers
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

pCode-Bot : (a : FinEl) -> Eq (pCode a Bot) Bot
pCode-Bot Bot          = refl
pCode-Bot UCode        = refl
pCode-Bot (FunEl g)    = refl
pCode-Bot (PiCode a f) = refl

------------------------------------------------------------------------
-- Forward: FinMem u a -> Eq (pCode a u) u
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  pCode-forward : (a u : FinEl) -> FinMem u a -> Eq (pCode a u) u

  pCode-forward a Bot mem = pCode-Bot a

  pCode-forward UCode UCode mem = refl
  pCode-forward Bot          UCode ()
  pCode-forward (FunEl g)    UCode ()
  pCode-forward (PiCode a f) UCode ()

  pCode-forward UCode (PiCode a' f') mem =
    let dom-eq = pCode-forward UCode a' (fst mem)
        cod-eq = projectUFun-forward a' f' (fst (snd mem))
    in PiCode-cong dom-eq cod-eq
  pCode-forward Bot          (PiCode a' f') ()
  pCode-forward (FunEl g)    (PiCode a' f') ()
  pCode-forward (PiCode b h) (PiCode a' f') ()

  pCode-forward (PiCode a f) (FunEl g) mem =
    Eq-cong FunEl (projectPiFun-forward a f g (fst mem))
  pCode-forward Bot       (FunEl g) ()
  pCode-forward UCode     (FunEl g) ()
  pCode-forward (FunEl h) (FunEl g) ()

  projectUFun-forward : (a : FinEl) (f : FinFun) ->
    FinMemAllU f a -> Eq (projectUFun a f) f
  projectUFun-forward a nil mem = refl
  projectUFun-forward a (cons p ps) mem =
    let key-eq = pCode-forward a (fst p) (fst (fst mem))
        val-eq = pCode-forward UCode (snd p) (snd (fst mem))
        tail-eq = projectUFun-forward a ps (snd mem)
    in cons-eq (pair-eq key-eq val-eq) tail-eq

  projectPiFun-forward : (a : FinEl) (f : FinFun) (g : FinFun) ->
    FinMemFun g a f -> Eq (projectPiFun a f g) g
  projectPiFun-forward a f nil mem = refl
  projectPiFun-forward a f (cons p ps) mem =
    let key-eq = pCode-forward a (fst p) (fst (fst mem))
        val-eq = Eq-transport
          (\ x -> Eq (pCode (EvalFun f x) (snd p)) (snd p))
          (Eq-sym key-eq)
          (pCode-forward (EvalFun f (fst p)) (snd p) (snd (fst mem)))
        tail-eq = projectPiFun-forward a f ps (snd mem)
    in cons-eq (pair-eq key-eq val-eq) tail-eq
