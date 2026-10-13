{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/Aux.agda : domain facts used by the relation's proofs
------------------------------------------------------------------------

module MAHLOINJ.Valid.Aux where

open import MAHLOINJ.Domain.Basic
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb using (bot-or ; NotBot-from-Le ; Empty-elim)

EvalFun-FinMem-step : (n : Nat) (p : Edge) (ps : FinFun)
  (b : FinEl) (f : FinFun) (v : FinEl) ->
  Eq (leFinEl (fst p) v) n ->
  FinMemFun (cons p ps) b f -> CoherentFunTail (cons p ps) ->
  CoherentFunTail f -> FinMemAllU f b ->
  Coherent v -> FinMem v b ->
  FinMem (EvalFun-step n (snd p) ps v) (EvalFun f v)

EvalFun-FinMem : (g : FinFun) (b : FinEl) (f : FinFun) (v : FinEl) ->
  FinMemFun g b f -> CoherentFunTail g ->
  CoherentFunTail f -> FinMemAllU f b ->
  Coherent v -> FinMem v b ->
  FinMem (EvalFun g v) (EvalFun f v)
EvalFun-FinMem nil b f v fmg cg cf allU cv mv =
  finMem-bot-from (EvalFun f v) (EvalFun-in-UCode f v b cf cv allU)
EvalFun-FinMem (cons p ps) b f v fmg cg cf allU cv mv =
  EvalFun-FinMem-step (leFinEl (fst p) v) p ps b f v refl fmg cg cf allU cv mv

EvalFun-FinMem-step zero p ps b f v eq fmg cg cf allU cv mv =
  EvalFun-FinMem ps b f v (snd fmg) (CFTcons.tail-coh cg) cf allU cv mv
EvalFun-FinMem-step (suc n) p ps b f v eq fmg cg cf allU cv mv =
  let le-k = leFinEl-sound (fst p) v (Eq-transport isPos (Eq-sym eq) tt)
      cpv = CFTcons.val-coh cg
      cw = CFTcons.compat cg
      ih = EvalFun-FinMem ps b f v (snd fmg) (CFTcons.tail-coh cg) cf allU cv mv
      c-efp = Coherent-EvalFun f (fst p) cf (CFTcons.key-coh cg)
      c-efv = Coherent-EvalFun f v cf cv
      le-ef = EvalFun-mon-arg f (fst p) v le-k cf (CFTcons.key-coh cg) cv
      efvU = EvalFun-in-UCode f v b cf cv allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f v)
                le-ef c-efp c-efv (snd (fst fmg)) efvU
      comp-pv = Comp-value-EvalFun p ps v le-k cv cpv cw
                  (coherentWith-to-compStepFun p ps cw)
  in FinMem-Sup-element (snd p) (EvalFun ps v) (EvalFun f v)
       comp-pv c-efv mem-p ih

-- a code below another one in U, with u : the smaller
mem-up : (u a0 a1 : FinEl) -> LeCode a0 a1 -> FinMem u a0 -> FinMem a1 UCode -> FinMem u a1
mem-up u a0 a1 le m a1U =
  finMem-upward u a0 a1 le (coh-from-aU a0 (FinMem-a-in-U u a0 m)) (coh-from-aU a1 a1U) m a1U
