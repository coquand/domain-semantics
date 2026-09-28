{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.PiInjectivityR
--
-- Π-injectivity for the Russell theory T_R, from the adequacy of the
-- domain model (BCDE4.Adeq.Driver), following MIN/PiInjectivity:
--
--   PiInj-R  : Γ ⊢ Π(C0,B0) = Π(C1,B1)
--           -> (Γ ⊢ C0 = C1)  ×  (Γ.C0 ⊢ B0 = B1)
--   LPiInj-R : Γ ⊢ [α]A0 = [α]A1  ->  Γ,α ⊢ A0 = A1
--
-- Apply the type-conversion adequacy at the identity substitution, in
-- the bottom environment, at the least product code PiCode Bot nil:
-- the validity of the conversion at a product code is a record whose
-- fields are the component conversions of the head-normal forms, and a
-- literal product is its own head-normal form.
--
-- No postulates, no pragmas.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.PiInjectivityR (D : LDecAll) where

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; LevTy ; LevEl ; LPiCode ; FinFun ; nil ; U0)
open import BCDE4.Dom.Kernel using (LeCode ; FinMem)
open import BCDE4.Basic using (Fin ; fzero ; fsuc ; inl ; Eq-trans)
open import BCDE4.Model.Eval D using (EnvApprox ; emptyEnv ; extendEnv ; EvalRel ; EvalRel-Bot)
open import BCDE4.Model.EvalSubstitution D using (botEnv ; botEnv-Coherent ; lookupEnv-botEnv)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (Selection ; sel-nil)
open import BCDE4.Model.Strip using (strip ; stripCtx)
import BCDE4.Model.Core as C
open import BCDE4.RussellSyntax using (Expr ; Pi ; LPi ; U ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (idSub ; substExpr-id ; presup-l-ConvTy ; isType-WfCtx)
open import BCDE4.RussellReduction using (headred-refl ; HeadRed-unique-Pi ; HeadRed-unique-LPi ; HeadRed-unique-U)
open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Driver D using (adqCTy0)
open import BCDE4.Dom.Membership using (finMem-LpiU-mk)

open import BCDE4.Levels using (LCtx ; LSub ; lidS ; LoopFree ; LSubOK ; lsubOK-self ; lsubTh-id ;
  LExpr ; Valid ; LDec ; lsubL ; lsubL-id ; v-trans ; v-sym)
open import BCDE4.Model.Eval D using (lcodeT)
open import BCDE4.Valid.Stratified D using (ured ; ucode)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- The bottom environment fits every context, and the identity
-- substitution is valid in it.
------------------------------------------------------------------------

-- (in the ambient level theory of G itself, which must be loop-free)
botEnv-fits : {n : Nat} (G : Ctx n) -> LoopFree (lctx G) -> Fits (stripCtx G) (botEnv {T = lctx G} {θ = lidS} {n = n})
botEnv-fits (empty Th)   lf = mkSigma lf (S.Eq-transport (\ X -> LSubOK X Th lidS) (lsubTh-id Th) (lsubOK-self lidS Th))
botEnv-fits (extend G A) lf = mkSigma (botEnv-fits G lf) (mkSigma Bot (mkSigma tt (EvalRel-Bot (strip A) botEnv)))

private
  Val2-from-LeBot : {n : Nat} {G : Ctx n} {M A : Expr n}
    (u a : FinEl) -> LeCode u Bot -> Val2 G M A u a
  Val2-from-LeBot Bot          a le = Val2-Bot a
  Val2-from-LeBot (UCode _)    a ()
  Val2-from-LeBot (FunEl _)    a ()
  Val2-from-LeBot (PiCode _ _) a ()
  Val2-from-LeBot LevTy        a ()
  Val2-from-LeBot (LevEl _)    a ()
  Val2-from-LeBot (LPiCode _)  a ()

botEnv-validSub2 : {n : Nat} (G : Ctx n) -> ValidSub2 G G idSub (botEnv {T = lctx G} {θ = lidS} {n = n})
botEnv-validSub2 G i u cu le a evA fm =
  Val2-from-LeBot u a (S.Eq-transport (LeCode u) (lookupEnv-botEnv i) le)

------------------------------------------------------------------------
-- A product evaluates to the least product code.
------------------------------------------------------------------------

evalRel-Pi-bot : {n : Nat} (A : C.Expr n) (B : C.Expr (suc n)) (rho : EnvApprox TL θ n) ->
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

-- in every context whose level constraints are loop-free
PiInj-R : {n : Nat} {G : Ctx n} {C0 C1 : Expr n} {B0 B1 : Expr (suc n)} ->
  LoopFree (lctx G) ->
  ConvTy G (Pi C0 B0) (Pi C1 B1) ->
  Pair (ConvTy G C0 C1) (ConvTy (extend G C0) B0 B1)
PiInj-R {n} {G} {C0} {C1} {B0} {B1} lf d =
  let wfG  = isType-WfCtx (presup-l-ConvTy d)
      raw  = adqCTy0 d idSub botEnv botEnv-Coherent (botEnv-validSub2 G) (botEnv-fits G lf)
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

------------------------------------------------------------------------
-- Injectivity of level products
------------------------------------------------------------------------

-- a level product evaluates to the least level-product code
evalRel-LPi-bot : {n : Nat} (A : C.Expr n) (rho : EnvApprox TL θ n) ->
  EvalRel (C.LPi A) rho (LPiCode nil)
evalRel-LPi-bot A rho = mkSigma tt sel-body
  where
    sel-body : (u v : FinEl) -> Selection nil u v -> _
    sel-body .Bot .Bot sel-nil = inl tt

LPiInj-R : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
  LoopFree (lctx G) ->
  ConvTy G (LPi A0) (LPi A1) ->
  ConvTy (addL G) A0 A1
LPiInj-R {n} {G} {A0} {A1} lf d =
  let wfG  = isType-WfCtx (presup-l-ConvTy d)
      raw  = adqCTy0 d idSub botEnv botEnv-Coherent (botEnv-validSub2 G) (botEnv-fits G lf)
               (idSub-WtSub wfG) wfG (LPiCode nil)
               (evalRel-LPi-bot (strip A0) botEnv) (finMem-LpiU-mk nil tt tt)
      ev   = S.Eq-transport (\ X -> EqValTy2 G X (LPi A1) (LPiCode nil)) (substExpr-id (LPi A0))
               (S.Eq-transport (\ X -> EqValTy2 G (substExpr idSub (LPi A0)) X (LPiCode nil))
                  (substExpr-id (LPi A1)) raw)
      core = un-REqValTyLPi ev
      e0   = HeadRed-unique-LPi (Red3.hr (REqValTyLPi.redM core)) (headred-refl {M = LPi A0})
      e1   = HeadRed-unique-LPi (Red3.hr (REqValTyLPi.redN core)) (headred-refl {M = LPi A1})
  in conv (e0) (e1) (REqValTyLPi.convA core)
  where
    conv : {X X' : Expr n} -> Eq X A0 -> Eq X' A1 -> ConvTy (addL G) X X' -> ConvTy (addL G) A0 A1
    conv refl refl c = c

------------------------------------------------------------------------
-- Injectivity of universes:  Γ ⊢ U_l = U_m  ->  l = m  in Γ
--
-- U_l evaluates to the universe code of l; the validity of the
-- conversion at that code says that U_m reduces to a universe whose
-- level has the same code, i.e. (codes being canonical) the same level.
------------------------------------------------------------------------

UInj-R : {n : Nat} {G : Ctx n} {l m : LExpr} ->
  LoopFree (lctx G) ->
  ConvTy G (U l) (U m) ->
  Valid (lctx G) l m
UInj-R {n} {G} {l} {m} lf d =
  let wfG  = isType-WfCtx (presup-l-ConvTy d)
      c    = lcodeT (lctx G) (lsubL lidS l)
      raw  = adqCTy0 d idSub botEnv botEnv-Coherent (botEnv-validSub2 G) (botEnv-fits G lf)
               (idSub-WtSub wfG) wfG (UCode c) (mkSigma tt (S.EqL-refl c)) tt
      rN   = snd raw
      e    = HeadRed-unique-U (Red3.hr (ured rN)) (headred-refl {M = U m})
      k    = S.Eq-transport (\ x -> S.EqL (codeL G x) c) e (ucode rN)
      eq   = Eq-trans (S.EqL-Eq (codeL G m) c k) (S.Eq-cong (LDec.lcode (D (lctx G))) (lsubL-id l))
  in v-trans (v-sym (LDec.ldec-code (D (lctx G)) l))
       (S.Eq-transport (\ x -> Valid (lctx G) (LDec.ldec (D (lctx G)) x) m) eq (LDec.ldec-code (D (lctx G)) m))
