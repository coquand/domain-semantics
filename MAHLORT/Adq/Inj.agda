{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Inj.agda  (Tarski port of MAHLOINJ/Adq/Inj)
--
-- Pi- and Sigma-injectivity for TyEq, from the fundamental lemma at
-- the identity substitution and the bottom environment.
--
-- The environment for the identity is built by induction on the
-- context: the type relation of a context entry is the fundamental
-- lemma for its own formation derivation, at the shorter context
-- (no weakening of the logical relation is needed).
------------------------------------------------------------------------

module MAHLORT.Adq.Inj where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; PiCode ; SigmaCode ; nil ; mkSigma)
open import MAHLOINJ.Domain.Kernel using (FinMem ; finMem-piU-mk ; finMem-sigU-mk)
open import MAHLORT.Model
open import MAHLORT.Model using (botEnv ; botEnv-coh ; lookup-botEnv)
open import MAHLORT.Model using (EvalRel-unwk)
import MAHLOINJ.Model.NoConf as NC
open import MAHLORT.Erasure using (erCtx)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Wf using (wfTy)
open import MAHLORT.Syntax.Presup using (pTE)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (ShapeOK ; PiOK ; SigOK)
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Fund

botEnv-fits : {n : Num} (G : Ctx n) -> Fits G botEnv
botEnv-fits G = NC.botEnv-fits (erCtx G)

------------------------------------------------------------------------
-- environments for renaming-like substitutions over the bottom
------------------------------------------------------------------------

private
  tail : {m n : Num} -> Sub m (suc n) -> Sub m n
  tail s i = s (fsuc i)

  wkS : {m n : Num} (s : Sub m (suc n)) (T : Expr n) -> Eq (substExpr s (wkExpr T)) (substExpr (tail s) T)
  wkS s T = subst-ren-gen s wkRen (tail s) (\ i -> refl) T

  wsTail : {m n : Num} {H : Ctx m} {G : Ctx n} {A : Expr n} {s : Sub m (suc n)} ->
    WtSub H (extend G A) s -> WtSub H G (tail s)
  wsTail {G = G} {s = s} ws i = trHT refl (wkS s (lookup G i)) (ws (fsuc i))

mutual
  envOf : {n : Num} (G : Ctx n) -> WfCtx G -> {m : Num} {H : Ctx m} -> WfCtx H ->
    (s : Sub m n) -> WtSub H G s -> Env H G s s botEnv
  envOf G wG {H = H} wH s ws = mkEnv (mkSR (reflC wG ws wH) (tyC G wG wH s ws) tmC) (botEnv-fits G) wH wG
    where
      tmC : (i : Fin _) (a : FinEl) -> EvalRel (lookup G i) botEnv a -> FinMem a UCode -> FinMem (lookupEnv i botEnv) a ->
            RTm H (s i) (s i) (substExpr s (lookup G i)) (lookupEnv i botEnv) a
      tmC i a ea aU m = transport (\ z -> RTm H (s i) (s i) (substExpr s (lookup G i)) z a) (Eq-sym (lookup-botEnv i)) tt

  tyC : {n : Num} (G : Ctx n) -> WfCtx G -> {m : Num} {H : Ctx m} -> WfCtx H ->
    (s : Sub m n) -> WtSub H G s ->
    (i : Fin n) (a : FinEl) -> EvalRel (lookup G i) botEnv a -> FinMem a UCode ->
    RTy H (substExpr s (lookup G i)) (substExpr s (lookup G i)) a
  tyC (extend G A) (wf-extend iA) {H = H} wH s ws fzero a ea aU =
    transport2 (\ X Y -> RTy H X Y a) (Eq-sym (wkS s A)) (Eq-sym (wkS s A))
      (AT iA (envOf G (wfTy iA) wH (tail s) (wsTail {A = A} ws)) a (EvalRel-unwk A botEnv Bot a ea) aU)
  tyC (extend G A) (wf-extend iA) {H = H} wH s ws (fsuc i) a ea aU =
    transport2 (\ X Y -> RTy H X Y a) (Eq-sym (wkS s (lookup G i))) (Eq-sym (wkS s (lookup G i)))
      (tyC G (wfTy iA) wH (tail s) (wsTail {A = A} ws) i a (EvalRel-unwk (lookup G i) botEnv Bot a ea) aU)

idWS : {n : Num} {G : Ctx n} -> WfCtx G -> WtSub G G idSub
idWS {G = G} w i = trHT refl (Eq-sym (substExpr-id (lookup G i))) (ty-var w)

idEnv : {n : Num} (G : Ctx n) -> WfCtx G -> Env G G idSub idSub botEnv
idEnv G w = envOf G w w idSub (idWS w)

------------------------------------------------------------------------
-- injectivity
------------------------------------------------------------------------

private
  liftId : {n : Num} (B : Expr (suc n)) -> Eq (substExpr (liftSub idSub) B) B
  liftId B = Eq-trans (substExpr-ext (liftSub idSub) idSub e B) (substExpr-id B)
    where
      e : (i : Fin _) -> Eq (liftSub idSub i) (idSub i)
      e fzero = refl
      e (fsuc i) = refl

  -- reading the components off a related literal shape
  readShape : {n : Num} {G : Ctx n} (S : Shape) -> ShapeOK S -> {A A' : Expr n} {B B' : Expr (suc n)} {b : FinEl} {f : D.FinFun} ->
    CodeTy S RTy RTm G (S (substExpr idSub A) (substExpr (liftSub idSub) B)) (S (substExpr idSub A') (substExpr (liftSub idSub) B')) b f ->
    TyEq G A A' * TyEq (extend G A) B B'
  readShape {G = G} S sok {A} {A'} {B} {B'} r =
    go (ShapeOK.inj sok (HRs-det (CodeTy.rT r) hrs-refl (ShapeOK.nored sok) (ShapeOK.nored sok)))
       (ShapeOK.inj sok (HRs-det (CodeTy.rT' r) hrs-refl (ShapeOK.nored sok) (ShapeOK.nored sok)))
    where
      go : Eq (CodeTy.A r) (substExpr idSub A) * Eq (CodeTy.B r) (substExpr (liftSub idSub) B) ->
           Eq (CodeTy.A' r) (substExpr idSub A') * Eq (CodeTy.B' r) (substExpr (liftSub idSub) B') ->
           TyEq G A A' * TyEq (extend G A) B B'
      go (eA , eB) (eA' , eB') =
        trTE (Eq-trans eA (substExpr-id A)) (Eq-trans eA' (substExpr-id A')) (CodeTy.eA r) ,
        transport (\ X -> TyEq (extend G X) B B') (Eq-trans eA (substExpr-id A))
          (trTE (Eq-trans eB (liftId B)) (Eq-trans eB' (liftId B')) (CodeTy.eB r))

Pi-inj : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  TyEq G (PiB A B) (PiB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
Pi-inj {G = G} {A} {A'} {B} {B'} d =
  readShape PiB PiOK {A} {A'} {B} {B'} (piTyV r)
  where
    w = wfTy (fst (pTE d))
    ea : EvalRel (PiB A B) botEnv (PiCode Bot nil)
    ea = mkSigma (mkSigma tt tt) (mkSigma (EvalRel-Bot A botEnv botEnv-coh) tt)
    r = AE d (idEnv G w) (PiCode Bot nil) ea (finMem-piU-mk Bot nil tt tt tt)

Sig-inj : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  TyEq G (SigmaB A B) (SigmaB A' B') -> TyEq G A A' * TyEq (extend G A) B B'
Sig-inj {G = G} {A} {A'} {B} {B'} d =
  readShape SigmaB SigOK {A} {A'} {B} {B'} (sigTyV r)
  where
    w = wfTy (fst (pTE d))
    ea : EvalRel (SigmaB A B) botEnv (SigmaCode Bot nil)
    ea = mkSigma (mkSigma tt tt) (mkSigma (EvalRel-Bot A botEnv botEnv-coh) tt)
    r = AE d (idEnv G w) (SigmaCode Bot nil) ea (finMem-sigU-mk Bot nil tt tt tt)
