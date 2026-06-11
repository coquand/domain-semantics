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

module MIN.Validity.Core where

import MIN.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons ;
              isPos)
import MIN.Syntax.Raw as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc ;
  Sub ; substExpr ; liftSub ;
  Ren ; renExpr ; wkRen ; liftRen ; subst-ren ;
  subst-subst ; substExpr-ext ; liftSub-subst-ext ; Eq-trans)
open import MIN.Syntax.Typing using (Ctx ; empty ; extend ; ConvTm ;
  conv-sym ; conv-trans)
open import MIN.Syntax.Reduction using (Red ; mkRed ; HeadRed ; HeadRed-trans ;
  HeadRed-App ;
  HeadRed-strip-Pi ; HeadRed-unique-Pi)
open import MIN.Domain.Kernel using (applyEl ; EvalFun ; EvalFun-step ;
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
open import MIN.Model.Selection public
open import MIN.Model.Eval using (absurd)

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


------------------------------------------------------------------------
-- Red-unique-Pi
------------------------------------------------------------------------

Red-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red G A (Pi B F) U -> Red G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red-unique-Pi (mkRed r1) (mkRed r2) = HeadRed-unique-Pi r1 r2

bU-from-cf-fmU : (f : FinFun) (b : FinEl) -> CoherentFun f -> FinMemAllU f b -> FinMem b UCode
bU-from-cf-fmU nil         b ()
bU-from-cf-fmU (cons p ps) b cf fmU = FinMem-a-in-U (fst p) b (fst (fst fmU))

bU-from-cf-fmFun : (g : FinFun) (b : FinEl) (f : FinFun) -> CoherentFun g -> FinMemFun g b f -> FinMem b UCode
bU-from-cf-fmFun nil         b f ()
bU-from-cf-fmFun (cons p ps) b f cg fmFun = FinMem-a-in-U (fst p) b (fst (fst fmFun))
