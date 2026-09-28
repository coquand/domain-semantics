{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.PiInjectivityR
--
-- Π-injectivity for the Russell theory T_R, from the adequacy of the
-- domain model (ERT.Adeq.Driver), following MIN/PiInjectivity:
--
--   PiInj-R : Γ ⊢ Π(C0,B0) = Π(C1,B1)
--          -> (Γ ⊢ C0 = C1)  ×  (Γ.C0 ⊢ B0 = B1)
--
-- Apply the type-conversion adequacy at the identity substitution, in
-- the bottom environment, at the least product code PiCode Bot nil:
-- the validity of the conversion at a product code is a record whose
-- fields are the component conversions of the head-normal forms, and a
-- literal product is its own head-normal form.
--
-- No postulates, no pragmas.
------------------------------------------------------------------------

module ERT.PiInjectivityR where

import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; U0)
open import ERT.Dom.Kernel using (LeCode ; FinMem)
open import ERT.Basic using (Fin ; fzero ; fsuc)
open import ERT.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; EvalRel ; EvalRel-Bot)
open import ERT.Model.EvalSubstitution using (botEnv ; botEnv-Coherent ; lookupEnv-botEnv)
open import ERT.Model.SoundnessLemmas using (Fits)
open import ERT.Model.Selection using (Selection ; sel-nil)
open import ERT.Model.Strip using (strip ; stripCtx)
import ERT.Model.Core as C
open import ERT.RussellSyntax using (Expr ; Pi ; substExpr)
open import ERT.RussellTyping
open import ERT.RussellMeta using (idSub ; substExpr-id ; presup-l-ConvTy ; isType-WfCtx)
open import ERT.RussellReduction using (headred-refl ; HeadRed-unique-Pi)
open import ERT.Adeq.HeadRed
open import ERT.Adeq.Driver using (adqCTy)

------------------------------------------------------------------------
-- The bottom environment fits every context, and the identity
-- substitution is valid in it.
------------------------------------------------------------------------

botEnv-fits : {n : Nat} (G : Ctx n) -> Fits (stripCtx G) (botEnv {n})
botEnv-fits empty        = tt
botEnv-fits (extend G A) = mkSigma (botEnv-fits G) (mkSigma Bot (mkSigma tt (EvalRel-Bot (strip A) botEnv)))

private
  Val2-from-LeBot : {n : Nat} {G : Ctx n} {M A : Expr n}
    (u a : FinEl) -> LeCode u Bot -> Val2 G M A u a
  Val2-from-LeBot Bot          a le = Val2-Bot a
  Val2-from-LeBot (UCode _)    a ()
  Val2-from-LeBot (FunEl _)    a ()
  Val2-from-LeBot (PiCode _ _) a ()

botEnv-validSub2 : {n : Nat} (G : Ctx n) -> ValidSub2 G G idSub (botEnv {n})
botEnv-validSub2 G i u cu le a evA fm =
  Val2-from-LeBot u a (S.Eq-transport (LeCode u) (lookupEnv-botEnv i) le)

------------------------------------------------------------------------
-- A product evaluates to the least product code.
------------------------------------------------------------------------

evalRel-Pi-bot : {n : Nat} (A : C.Expr n) (B : C.Expr (suc n)) (rho : EnvApprox n) ->
  EvalRel (C.Pi A B) rho (PiCode Bot nil)
evalRel-Pi-bot A B rho =
  mkSigma (mkSigma tt tt)
    (mkSigma (EvalRel-Bot A rho)
      (mkSigma Bot (mkSigma (EvalRel-Bot A rho) sel-body)))
  where
    sel-body : (u v : FinEl) -> Selection nil u v ->
      Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x Bot) (EvalRel B (extendEnv rho x) v)))
    sel-body .Bot .Bot sel-nil = mkSigma Bot (mkSigma tt (mkSigma tt (EvalRel-Bot B (extendEnv rho Bot))))

------------------------------------------------------------------------
-- Π-injectivity
------------------------------------------------------------------------

PiInj-R : {n : Nat} {G : Ctx n} {C0 C1 : Expr n} {B0 B1 : Expr (suc n)} ->
  ConvTy G (Pi C0 B0) (Pi C1 B1) ->
  Pair (ConvTy G C0 C1) (ConvTy (extend G C0) B0 B1)
PiInj-R {n} {G} {C0} {C1} {B0} {B1} d =
  let wfG  = isType-WfCtx (presup-l-ConvTy d)
      raw  = adqCTy d idSub botEnv botEnv-Coherent (botEnv-validSub2 G) (botEnv-fits G)
               (idSub-WtSub wfG) wfG (PiCode Bot nil)
               (evalRel-Pi-bot (strip C0) (strip B0) botEnv) (mkSigma tt (mkSigma tt tt))
      ev   = S.Eq-transport (\ X -> EqValTy2 G X (Pi C1 B1) (PiCode Bot nil)) (substExpr-id (Pi C0 B0))
               (S.Eq-transport (\ X -> EqValTy2 G (substExpr idSub (Pi C0 B0)) X (PiCode Bot nil))
                  (substExpr-id (Pi C1 B1)) raw)
      core = un-REqValTyPi ev
      e0   = HeadRed-unique-Pi (Red3.hr (REqValTyPi.redM core)) (headred-refl {M = Pi C0 B0})
      e1   = HeadRed-unique-Pi (Red3.hr (REqValTyPi.redN core)) (headred-refl {M = Pi C1 B1})
  in mkSigma (conv-dom (fst e0) (fst e1) (REqValTyPi.convA core))
             (conv-cod (fst e0) (snd e0) (snd e1) (REqValTyPi.convB core))
  where
    conv-dom : {X X' : Expr n} -> Eq X C0 -> Eq X' C1 -> ConvTy G X X' -> ConvTy G C0 C1
    conv-dom refl refl c = c
    conv-cod : {X : Expr n} {Y Y' : Expr (suc n)} -> Eq X C0 -> Eq Y B0 -> Eq Y' B1 ->
      ConvTy (extend G X) Y Y' -> ConvTy (extend G C0) B0 B1
    conv-cod refl refl refl c = c
