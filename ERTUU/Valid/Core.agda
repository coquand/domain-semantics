{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity.agda  (MIN/ — Pi + U fragment)
--
-- Logical relation (validity) for dependent type theory with U : U.
-- Defines:
--   Val / EqVal  -- term/equality validity
--   ValTy/EqValTy -- type validity (= Val at UCode)
--   ValTyPi/EqValTyPi -- type validity at Pi-code
--   PiEdge families
-- 0 postulates.
------------------------------------------------------------------------

module ERTUU.Valid.Core where

open import ERTUU.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

import ERTUU.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons ;
              isPos)
import ERTUU.RussellSyntax as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc ;
  Sub ; substExpr ; liftSub ;
  Ren ; renExpr ; wkRen ; liftRen ; subst-ren ;
  subst-subst ; substExpr-ext ; liftSub-subst-ext ; Eq-trans)
open import ERTUU.RussellTyping
open import ERTUU.RussellReduction
open import ERTUU.Dom.Kernel using (applyEl ; EvalFun ; EvalFun-step ;
  leFinEl ; leFinEl-sound ;
  LeCode ; LeFunCode ; LeCode-Bot ; LeCode-Sup-lub ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-refl ; LeCode-trans ;
  Sup ; append ; Comp ; CompStepFun ; Coherent-Sup ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; CoherentWith ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon ; EvalFun-mon-arg ;
  CoherentFun-append ; CoherentFunTail-append ;
  Comp-value-EvalFun ; comp-Bot-r ;
  coh-from-aU ; LeCode-Comp ;
  FinMem ; FinMemFun ; FinMemAllU ; EvalFun-in-UCode ; finMem-bot-from ;
  FinMem-coh-u ;
  Sup-Bot-right ;
  Comp-refl ; comp-Sup ; finMem-Sup-left ; finMem-Sup-right ;
  finMemUCode-Sup ; FinMem-a-in-U ;
  Comp-down ; Comp-sym ;
  coherentWith-to-compStepFun ;
  finMem-upward ; finMemFun-upward ;
  FinMemFun-append ; FinMem-Sup-element ;
  comp-EvalFun ; EvalFun-append-eq ; FinMemAllU-append-Sup ;
  LeFunCode-refl)
open import ERTUU.Model.Selection public
open import ERTUU.Model.Eval using (absurd)

------------------------------------------------------------------------
-- FinMem-Coherent
------------------------------------------------------------------------

FinMem-Coherent : (u a : FinEl) -> FinMem u a -> Coherent u
FinMem-Coherent = FinMem-coh-u

------------------------------------------------------------------------
-- EvalFun-FinMem
------------------------------------------------------------------------

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


bU-from-cf-fmU : (f : FinFun) (b : FinEl) -> CoherentFun f -> FinMemAllU f b -> FinMem b U0
bU-from-cf-fmU nil         b ()
bU-from-cf-fmU (cons p ps) b cf fmU = FinMem-a-in-U (fst p) b (fst (fst fmU))

bU-from-cf-fmFun : (g : FinFun) (b : FinEl) (f : FinFun) -> CoherentFun g -> FinMemFun g b f -> FinMem b U0
bU-from-cf-fmFun nil         b f ()
bU-from-cf-fmFun (cons p ps) b f cg fmFun = FinMem-a-in-U (fst p) b (fst (fst fmFun))

------------------------------------------------------------------------
-- Transport along an equality of universe levels
------------------------------------------------------------------------

U-tr : (P : Nat -> Set) (k m : Nat) -> EqL k m -> P k -> P m
U-tr P k m e x = Eq-transport P (EqL-Eq k m e) x
