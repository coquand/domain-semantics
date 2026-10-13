{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/NoConf.agda
--
-- No-confusion of U(f,g) with Pi, Sigma and Nat, from soundness of the
-- erased model alone: U(f,g) has the approximant UCode, which is not
-- below any Pi-, Sigma- or Nat-code.  (InjHyp fields U-Pi, U-Sig, U-Nat.)
------------------------------------------------------------------------

module MAHLOINJ.Model.NoConf where

import MAHLO.Basic as B
open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalFwd using (botEnv ; botEnv-coh)
open import MAHLOINJ.Model.SoundBase
open import MAHLOINJ.Model.Soundness
open import MAHLO.Syntax
open import MAHLO.Typing

-- the bottom environment fits every context
botEnv-fits : {n : Num} (G : Ctx n) -> Fits G botEnv
botEnv-fits empty = tt
botEnv-fits (extend G A) =
  mkSigma (botEnv-fits G) (mkSigma Bot (mkSigma tt (EvalRel-Bot A botEnv botEnv-coh)))

-- transport of the U-code approximant along a type equality
U-transfer : {n : Num} {G : Ctx n} {f g X : Expr n} -> TyEq G (Ucode f g) X -> EvalRel X botEnv UCode
U-transfer {G = G} e = fst (snd (snd (sTE e botEnv (botEnv-fits G)))) UCode (mkSigma tt tt)

toEmpty : Empty -> B.Empty
toEmpty ()

U-Pi : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} -> TyEq G (Ucode f g) (PiB A B) -> B.Empty
U-Pi e = toEmpty (U-transfer e)

U-Sig : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)} -> TyEq G (Ucode f g) (SigmaB A B) -> B.Empty
U-Sig e = toEmpty (U-transfer e)

U-Nat : {n : Num} {G : Ctx n} {f g : Expr n} -> TyEq G (Ucode f g) Nat -> B.Empty
U-Nat e = toEmpty (snd (U-transfer e))
