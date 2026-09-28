{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Gap417
--
-- The application case of the paper's proof of Lemma 4.17 does not go
-- through in T_R, because of cumulativity at the END of a derivation.
--
--   f0 = λ(U1, U1, v0) : Π(U1, U1)
--   f1 = λ(U1, U2, v0) : Π(U1, U2)          (body v0 : U1 ≤ U2)
--   u0 = app(U1, U1, f0, U0) : U1 ≤ U2       (last rule: cumulativity)
--   u1 = app(U1, U2, f1, U0) : U2
--
-- strip u0 = strip u1 and A0 = A1 = U2, so the hypotheses of 4.17 hold
-- for (u0, u1).  The proof then applies the induction hypothesis to the
-- functions and concludes Π(C0,B0) = Π(C1,B1); here that is
--   Π(U1,U1) = Π(U1,U2),
-- which is FALSE (Π-injectivity + injectivity of universes, both from
-- the domain model).  The statement itself is not refuted: u0 = u1 : U2
-- does hold (both β-reduce to U0) — it is only this step of the proof.
------------------------------------------------------------------------

module ERT.Gap417 where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta using (isType-U)
open import ERT.PiInjectivityR using (PiInj-R ; botEnv-fits)
open import ERT.Model.Strip using (strip ; stripCtx)
open import ERT.Model.RussellSound using (sound-CTy)
open import ERT.Model.EvalSubstitution using (botEnv)
import ERT.Dom.Basic as D

------------------------------------------------------------------------
-- Injectivity of universes (from soundness of the model)
------------------------------------------------------------------------

U-inj-R : {n : Nat} {G : Ctx n} {m k : Nat} -> ConvTy G (U m) (U k) -> Eq m k
U-inj-R {G = G} {m = m} {k = k} d =
  let fwd = fst (snd (snd (sound-CTy d botEnv (botEnv-fits G))))
      ev  = fwd (D.UCode m) (mkSigma tt (D.EqL-refl m))
  in D.EqL-Eq m k (snd ev)

------------------------------------------------------------------------
-- The two terms
------------------------------------------------------------------------

wf0 : WfCtx empty
wf0 = wf-empty

U1 U2 U0 : Expr zero
U1 = U 1
U2 = U 2
U0 = U 0

wf1 : WfCtx (extend empty U1)
wf1 = wf-extend (isType-U wf0)

f0 f1 u0 u1 : Expr zero
f0 = Lam U1 (U 1) (Var fzero)
f1 = Lam U1 (U 2) (Var fzero)
u0 = App U1 (U 1) f0 U0
u1 = App U1 (U 2) f1 U0

dU0 : HasType empty U0 U1
dU0 = ty-U wf0

df0 : HasType empty f0 (Pi U1 (U 1))
df0 = ty-Lam (isType-U wf0) (isType-U wf1) (ty-var wf1)

df1 : HasType empty f1 (Pi U1 (U 2))
df1 = ty-Lam (isType-U wf0) (isType-U wf1) (ty-cum (ty-var wf1))

du0 : HasType empty u0 U2
du0 = ty-cum (ty-App (isType-U wf0) (isType-U wf1) df0 dU0)

du1 : HasType empty u1 U2
du1 = ty-App (isType-U wf0) (isType-U wf1) df1 dU0

same-strip : Eq (strip u0) (strip u1)
same-strip = refl

-- the conclusion the proof's application case needs is false
no-Pi-conv : ConvTy empty (Pi U1 (U 1)) (Pi U1 (U 2)) -> Empty
no-Pi-conv d with U-inj-R (snd (PiInj-R d))
... | ()

-- (the statement of 4.17 is fine on this instance: both sides are U0)
u0=u1 : ConvTm empty u0 u1 U2
u0=u1 =
  conv-trans (conv-cum (conv-beta (isType-U wf0) (isType-U wf1) (ty-var wf1) dU0))
    (conv-sym (conv-beta (isType-U wf0) (isType-U wf1) (ty-cum (ty-var wf1)) dU0))
