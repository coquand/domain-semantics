{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.SubjectReductionR
--
-- Subject reduction for the β-steps of T_R (ERT.RussellStep), in
-- the strong form: a reduct is CONVERTIBLE to the term, at any type
-- of the term.  The β case needs Π-injectivity (PiInj-R, from the
-- domain model), since the λ's annotations need only be convertible
-- to the application's.
------------------------------------------------------------------------

module ERT.SubjectReductionR where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.RussellMetaCong using (subst1-cong-Ty)
open import ERT.RussellInversion
open import ERT.RussellStep
open import ERT.PiInjectivityR using (PiInj-R)

mutual

  SR-Ty : {n : Nat} {G : Ctx n} {A A' : Expr n} -> IsType G A -> StepR A A' -> ConvTy G A A'
  SR-Ty (is-Ty-from-U d) s = conv-Ty-from-U (SR d s)

  SR : {n : Nat} {G : Ctx n} {u u' T : Expr n} -> HasType G u T -> StepR u u' -> ConvTm G u u' T
  SR d (r-beta {A = A} {A' = A'} {B = B} {B' = B'} {b = b} {a = a}) =
    let i    = inv-App d
        dA   = InvApp.dA i
        dB   = InvApp.dB i
        l    = inv-Lam (InvApp.dc i)
        dA'  = InvLam.dA l
        pinj = PiInj-R (Sub-Pi (InvLam.sub l))          -- A' = A,  B' = B (in Γ.A')
        cAA' = conv-Ty-sym (fst pinj)                   -- A = A'
        db0  = ctx-conv-HasType dA' dA (fst pinj) (ty-conv (InvLam.db l) (snd pinj))
        cBB' = ctx-conv-ConvTy dA' dA (fst pinj) (conv-Ty-sym (snd pinj))
        cLam = conv-cong-Lam-Ty dA dB cAA' cBB' db0      -- λ(A,B,b) = λ(A',B',b) : Π(A,B)
        step = conv-trans (conv-cong-App-fun dA dB (conv-sym cLam) (InvApp.da i))
                          (conv-beta dA dB db0 (InvApp.da i))
    in lift-ConvTm step (InvApp.sub i)
  SR d (r-app-l s) =
    let i = inv-App d
    in lift-ConvTm (conv-cong-App-fun (InvApp.dA i) (InvApp.dB i) (SR (InvApp.dc i) s) (InvApp.da i))
                   (InvApp.sub i)
  SR d (r-app-r s) =
    let i  = inv-App d
        ca = SR (InvApp.da i) s
    in lift-ConvTm (conv-cong-App-arg (InvApp.dA i) (InvApp.dB i) (InvApp.dc i) ca
                      (subst1-cong-Ty ca (InvApp.dA i) (InvApp.dB i)))
                   (InvApp.sub i)
  SR d (r-lam-d s) =
    let l = inv-Lam d
    in lift-ConvTm (conv-cong-Lam-Ty (InvLam.dA l) (InvLam.dB l) (SR-Ty (InvLam.dA l) s)
                      (conv-Ty-refl (InvLam.dB l)) (InvLam.db l))
                   (InvLam.sub l)
  SR d (r-lam-b s) =
    let l = inv-Lam d
    in lift-ConvTm (conv-cong-Lam-body (InvLam.dA l) (InvLam.dB l) (InvLam.db l) (SR (InvLam.db l) s))
                   (InvLam.sub l)
  SR d (r-pi-d s) =
    let p = inv-Pi d
    in lift-ConvTm (conv-cong-Pi (InvPi.dA p) (InvPi.dB p) (SR (InvPi.dA p) s) (conv-refl (InvPi.dB p)))
                   (InvPi.sub p)
  SR d (r-pi-c s) =
    let p = inv-Pi d
    in lift-ConvTm (conv-cong-Pi (InvPi.dA p) (InvPi.dB p) (conv-refl (InvPi.dA p)) (SR (InvPi.dB p) s))
                   (InvPi.sub p)

SR-star : {n : Nat} {G : Ctx n} {u u' T : Expr n} -> HasType G u T -> StarR u u' -> ConvTm G u u' T
SR-star d r-refl        = conv-refl d
SR-star d (r-step s ss) = let c = SR d s in conv-trans c (SR-star (presup-r-ConvTm c) ss)
