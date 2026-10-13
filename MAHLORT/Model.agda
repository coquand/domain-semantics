{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Model.agda
--
-- The finite-element model of the Tarski theory, THROUGH ERASURE: the
-- denotation of a Tarski expression is that of its erasure in the
-- Russell model of MAHLOINJ/Model, and soundness for the Tarski
-- judgements is soundness of the erased judgements (MAHLORT/EraseDeriv,
-- Lemma 4.6).  This file re-exports the interface used by the logical
-- relation, under the same names, for Tarski syntax.
------------------------------------------------------------------------

module MAHLORT.Model where

open import MAHLO.Basic using (Eq ; refl ; transport ; Eq-sym)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Erasure using (er ; erCtx)
open import MAHLORT.EraseLemmas using (er-wk ; er-subst1 ; er-lookup ; er-subst)
open import MAHLORT.EraseDeriv using (erI ; erH ; erT ; erC)
import MAHLO.Syntax as R
open import MAHLOINJ.Domain.Basic using (FinEl ; Bot ; mkSigma ; fst ; snd) renaming (Sigma to DSigma ; Pair to DPair)
open import MAHLOINJ.Domain.Kernel using (FinMem ; LeCode ; Coherent ; Comp ; Sup)
open import MAHLOINJ.Model.Comb using (Pred ; Ideal ; BodyOK)
open import MAHLOINJ.Model.SemLam using (InvTypP)
open import MAHLOINJ.Model.SoundBase using (InvConvP)
import MAHLOINJ.Model.Eval as E
import MAHLOINJ.Model.EvalSubst as ES
import MAHLOINJ.Model.EvalFwd as EF
import MAHLOINJ.Model.SoundBase as SB
import MAHLOINJ.Model.Soundness as S

open E public using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ; CoherentEnv ; lookupEnv-coh ; EnvLe ; lookupEnv-mon
                    ; EnvLe-refl ; EnvLe-extend ; EnvLe-coh-r)
open EF public using (botEnv ; botEnv-coh ; lookup-botEnv)
open S public using (UT)

EvalRel : {n : Num} -> Expr n -> EnvApprox n -> Pred
EvalRel M rho = E.EvalRel (er M) rho

Fits : {n : Num} -> Ctx n -> EnvApprox n -> Set
Fits G rho = SB.Fits (erCtx G) rho

Fits-coh : {n : Num} (G : Ctx n) (rho : EnvApprox n) -> Fits G rho -> CoherentEnv rho
Fits-coh G = SB.Fits-coh (erCtx G)

Fits-ext : {n : Num} (G : Ctx n) (A : Expr n) (rho : EnvApprox n) (x a : FinEl) ->
  Fits G rho -> FinMem x a -> EvalRel A rho a -> Fits (extend G A) (extendEnv rho x)
Fits-ext G A = SB.Fits-ext (erCtx G) (er A)

Fits-var : {n : Num} (G : Ctx n) (rho : EnvApprox n) -> Fits G rho -> (i : Fin n) ->
  DSigma FinEl (\ a -> DPair (FinMem (lookupEnv i rho) a) (EvalRel (lookup G i) rho a))
Fits-var G rho f i =
  transport (\ X -> DSigma FinEl (\ a -> DPair (FinMem (lookupEnv i rho) a) (E.EvalRel X rho a)))
    (Eq-sym (er-lookup G i)) (SB.Fits-var (erCtx G) rho f i)

-- soundness
sTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A ->
  (rho : EnvApprox n) -> Fits G rho -> InvTypP (EvalRel A rho) UT
sTy d = S.sTy (erI d)

sTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A ->
  (rho : EnvApprox n) -> Fits G rho -> InvTypP (EvalRel t rho) (EvalRel A rho)
sTm d = S.sTm (erH d)

sTE : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B ->
  (rho : EnvApprox n) -> Fits G rho -> InvConvP (EvalRel A rho) (EvalRel B rho) UT
sTE d = S.sTE (erT d)

sCv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
  (rho : EnvApprox n) -> Fits G rho -> InvConvP (EvalRel t rho) (EvalRel u rho) (EvalRel A rho)
sCv d = S.sCv (erC d)

-- weakening and substitution
EvalRel-wk : {n : Num} (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  EvalRel M rho u -> EvalRel (wkExpr M) (extendEnv rho v) u
EvalRel-wk M rho v u e =
  transport (\ X -> E.EvalRel X (extendEnv rho v) u) (Eq-sym (er-wk M)) (ES.EvalRel-wk (er M) rho v u e)

EvalRel-unwk : {n : Num} (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  EvalRel (wkExpr M) (extendEnv rho v) u -> EvalRel M rho u
EvalRel-unwk M rho v u e =
  ES.EvalRel-unwk (er M) rho v u (transport (\ X -> E.EvalRel X (extendEnv rho v) u) (er-wk M) e)

EvalRel-subst1-backward : {n : Num} (B : Expr (suc n)) (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  CoherentEnv rho -> EvalRel M rho v -> EvalRel B (extendEnv rho v) u -> EvalRel (subst1 B M) rho u
EvalRel-subst1-backward B M rho v u c eM eB =
  transport (\ X -> E.EvalRel X rho u) (Eq-sym (er-subst1 B M)) (ES.EvalRel-subst1-backward (er B) (er M) rho v u c eM eB)

EvalRel-subst1-forward : {n : Num} (M : Expr (suc n)) (N : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  CoherentEnv rho -> EvalRel (subst1 M N) rho u ->
  DSigma FinEl (\ v -> DPair (EvalRel N rho v) (EvalRel M (extendEnv rho v) u))
EvalRel-subst1-forward M N rho u c e =
  EF.EvalRel-subst1-forward (er M) (er N) rho u c (transport (\ X -> E.EvalRel X rho u) (er-subst1 M N) e)

MaxSubRel : {h g : Num} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
MaxSubRel sigma rho rho' = ES.MaxSubRel (\ i -> er (sigma i)) rho rho'

EvalRel-subst-fwd-max : {h g : Num} (sigma : Sub h g) (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho -> MaxSubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel (substExpr sigma M) rho u -> EvalRel M rho' u
EvalRel-subst-fwd-max sigma M rho rho' c m u e =
  ES.EvalRel-subst-fwd-max (\ i -> er (sigma i)) (er M) rho rho' c m u
    (transport (\ X -> E.EvalRel X rho u) (er-subst sigma M) e)

-- the interface of MAHLOINJ/Model/Eval, on erasures
module _ {n : Num} (M : Expr n) where
  EvalRel-mon-env : (rho rho' : EnvApprox n) -> EnvLe rho rho' -> (u : FinEl) -> EvalRel M rho u -> EvalRel M rho' u
  EvalRel-mon-env = E.EvalRel-mon-env (er M)
  EvalRel-ideal : (rho : EnvApprox n) -> CoherentEnv rho -> Ideal (EvalRel M rho)
  EvalRel-ideal = E.EvalRel-ideal (er M)
  EvalRel-coh : (rho : EnvApprox n) -> CoherentEnv rho -> (u : FinEl) -> EvalRel M rho u -> Coherent u
  EvalRel-coh = E.EvalRel-coh (er M)
  EvalRel-Bot : (rho : EnvApprox n) -> CoherentEnv rho -> EvalRel M rho Bot
  EvalRel-Bot = E.EvalRel-Bot (er M)
  EvalRel-down : (rho : EnvApprox n) -> CoherentEnv rho ->
    (u u' : FinEl) -> EvalRel M rho u -> Coherent u' -> LeCode u' u -> EvalRel M rho u'
  EvalRel-down = E.EvalRel-down (er M)
  EvalRel-Comp : (rho : EnvApprox n) -> CoherentEnv rho -> (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> Comp u v
  EvalRel-Comp = E.EvalRel-Comp (er M)
  EvalRel-Sup : (rho : EnvApprox n) -> CoherentEnv rho -> (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)
  EvalRel-Sup = E.EvalRel-Sup (er M)

-- generic body families
Body : {n : Num} -> Expr (suc n) -> EnvApprox n -> FinEl -> Pred
Body B rho x = EvalRel B (extendEnv rho x)

bodyOK : {n : Num} (B : Expr (suc n)) (rho : EnvApprox n) -> CoherentEnv rho -> BodyOK (Body B rho)
bodyOK B = SB.bodyOK (er B)
