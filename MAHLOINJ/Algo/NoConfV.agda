{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/NoConfV.agda
--
-- V is not convertible to a Pi, a Sigma or Nat (from the finite-element
-- model alone, as U-Pi/U-Sig/U-Nat in Model/NoConf: V and every code
-- U(f,g) denote the atom of UCode).
------------------------------------------------------------------------

module MAHLOINJ.Algo.NoConfV where

import MAHLO.Basic as B
open import MAHLOINJ.Domain.Basic using (tt ; mkSigma ; fst ; snd ; UCode)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalFwd using (botEnv)
open import MAHLOINJ.Model.Soundness using (sTE)
open import MAHLOINJ.Model.NoConf using (botEnv-fits ; toEmpty)
open import MAHLO.Syntax
open import MAHLO.Typing

V-transfer : {n : Num} {G : Ctx n} {X : Expr n} -> TyEq G V X -> EvalRel X botEnv UCode
V-transfer {G = G} e = fst (snd (snd (sTE e botEnv (botEnv-fits G)))) UCode (mkSigma tt tt)

V-Pi : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} -> TyEq G V (PiB A B) -> B.Empty
V-Pi e = toEmpty (V-transfer e)

V-Sig : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} -> TyEq G V (SigmaB A B) -> B.Empty
V-Sig e = toEmpty (V-transfer e)

V-Nat : {n : Num} {G : Ctx n} -> TyEq G V Nat -> B.Empty
V-Nat e = toEmpty (snd (V-transfer e))

-- Pi is not Sigma
Pi-Sig : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} -> TyEq G (PiB A B) (SigmaB A' B') -> B.Empty
Pi-Sig {G = G} {A} e =
  toEmpty (fst (snd (snd (sTE e botEnv (botEnv-fits G)))) (PiCode Bot nil)
             (mkSigma (mkSigma tt tt) (mkSigma (EvalRel-Bot A botEnv botEnv-coh) tt)))
  where
    open import MAHLOINJ.Domain.Basic using (PiCode ; Bot ; nil)
    open import MAHLOINJ.Model.EvalFwd using (botEnv-coh)
