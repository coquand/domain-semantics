{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/RNoConf.agda
--
-- The no-confusion facts on the Russell side (MAHLO/Typing) that the
-- Russell/Tarski equivalence needs, beyond MAHLOINJ (U-Pi, U-Sig,
-- U-Nat, V-Pi, V-Sig, V-Nat, Pi-Sig), all hypothesis-free:
--
--   V-only : TyEq G V X -> Eq X V      (syntactic: V is not a term)
--   V-U    : TyEq G V (Ucode f g) -> Empty
--   Pi-Nat, Sig-Nat                   (finite-element model)
--
-- V-only needs no model.  V is never the subject of a typing judgement,
-- hence (presupposition) never a side of a conversion, and so the only
-- type equalities with V on one side are built from reflexivity,
-- symmetry and transitivity.
------------------------------------------------------------------------

module MAHLORT.RNoConf where

import MAHLO.Basic as B
open import MAHLO.Basic using (Eq ; refl ; Eq-sym ; Eq-trans ; Empty ; fst ; snd)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Presup using (pCv)

------------------------------------------------------------------------
-- V is not a term
------------------------------------------------------------------------

noV : {n : Num} {G : Ctx n} {A : Expr n} -> HasType G V A -> Empty
noV (ty-conv h _) = noV h
noV (ty-sub h) = noV h

private
  -- the type equalities of V
  data IsV {n : Num} : Expr n -> Set where
    isV : IsV V

  vEq : {n : Num} {X : Expr n} -> IsV X -> Eq X V
  vEq isV = refl

  mutual
    vR : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> IsV A -> IsV B
    vR (tyeq-refl _) v = v
    vR (tyeq-sym q) v = vL q v
    vR (tyeq-trans q q') v = vR q' (vR q v)
    vR (tyeq-el c) isV = B.Empty-elim (noV (fst (pCv c)))
    vR (tyeq-Pi _ _ _ _ _) ()
    vR (tyeq-Sigma _ _ _ _ _) ()

    vL : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> IsV B -> IsV A
    vL (tyeq-refl _) v = v
    vL (tyeq-sym q) v = vR q v
    vL (tyeq-trans q q') v = vL q (vL q' v)
    vL (tyeq-el c) isV = B.Empty-elim (noV (snd (pCv c)))
    vL (tyeq-Pi _ _ _ _ _) ()
    vL (tyeq-Sigma _ _ _ _ _) ()

V-only : {n : Num} {G : Ctx n} {X : Expr n} -> TyEq G V X -> Eq X V
V-only q = vEq (vR q isV)

V-U : {n : Num} {G : Ctx n} {f g : Expr n} -> TyEq G V (Ucode f g) -> Empty
V-U q with V-only q
... | ()

------------------------------------------------------------------------
-- Nat is not a Pi or a Sigma (finite-element model: Nat has the
-- approximant NatCode, which no Pi- or Sigma-predicate admits)
------------------------------------------------------------------------

private
  open import MAHLOINJ.Domain.Basic as D using (tt ; mkSigma ; NatCode)
  open import MAHLOINJ.Model.Eval using (EvalRel)
  open import MAHLOINJ.Model.EvalFwd using (botEnv)
  open import MAHLOINJ.Model.Soundness using (sTE)
  open import MAHLOINJ.Model.NoConf using (botEnv-fits ; toEmpty)

  Nat-transfer : {n : Num} {G : Ctx n} {X : Expr n} -> TyEq G Nat X -> EvalRel X botEnv NatCode
  Nat-transfer {G = G} e = D.fst (D.snd (D.snd (sTE e botEnv (botEnv-fits G)))) NatCode (mkSigma tt tt)

Nat-Pi : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} -> TyEq G Nat (PiB A B) -> Empty
Nat-Pi e = toEmpty (Nat-transfer e)

Nat-Sig : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} -> TyEq G Nat (SigmaB A B) -> Empty
Nat-Sig e = toEmpty (Nat-transfer e)
