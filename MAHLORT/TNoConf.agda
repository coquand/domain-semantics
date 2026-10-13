{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/TNoConf.agda
--
-- No-confusion of the Tarski type formers V, U_{f,g}, Pi, Sigma, N,
-- hypothesis-free: erase the type equality (MAHLORT/EraseDeriv,
-- Lemma 4.6) and use the Russell facts (MAHLOINJ, MAHLORT/RNoConf),
-- as ERT/Injectivity does.
------------------------------------------------------------------------

module MAHLORT.TNoConf where

open import MAHLO.Basic using (Empty)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.EraseDeriv using (erT)
import MAHLO.Typing as RT
open import MAHLOINJ.Model.NoConf using (U-Pi ; U-Sig ; U-Nat)
open import MAHLOINJ.Algo.NoConfV using (V-Pi ; V-Sig ; V-Nat ; Pi-Sig)
open import MAHLORT.RNoConf using (V-U ; Nat-Pi ; Nat-Sig)

module _ {n : Num} {G : Ctx n} where

  tV-U : {f g : Expr n} -> TyEq G V (TyU f g) -> Empty
  tV-U q = V-U (erT q)

  tV-Pi : {A : Expr n} {B : Expr (suc n)} -> TyEq G V (PiB A B) -> Empty
  tV-Pi q = V-Pi (erT q)

  tV-Sig : {A : Expr n} {B : Expr (suc n)} -> TyEq G V (SigmaB A B) -> Empty
  tV-Sig q = V-Sig (erT q)

  tV-Nat : TyEq G V Nat -> Empty
  tV-Nat q = V-Nat (erT q)

  tU-Pi : {f g A : Expr n} {B : Expr (suc n)} -> TyEq G (TyU f g) (PiB A B) -> Empty
  tU-Pi q = U-Pi (erT q)

  tU-Sig : {f g A : Expr n} {B : Expr (suc n)} -> TyEq G (TyU f g) (SigmaB A B) -> Empty
  tU-Sig q = U-Sig (erT q)

  tU-Nat : {f g : Expr n} -> TyEq G (TyU f g) Nat -> Empty
  tU-Nat q = U-Nat (erT q)

  tPi-Sig : {A A' : Expr n} {B B' : Expr (suc n)} -> TyEq G (PiB A B) (SigmaB A' B') -> Empty
  tPi-Sig q = Pi-Sig (erT q)

  tNat-Pi : {A : Expr n} {B : Expr (suc n)} -> TyEq G Nat (PiB A B) -> Empty
  tNat-Pi q = Nat-Pi (erT q)

  tNat-Sig : {A : Expr n} {B : Expr (suc n)} -> TyEq G Nat (SigmaB A B) -> Empty
  tNat-Sig q = Nat-Sig (erT q)
