{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Injectivity
--
-- Injectivity of universes and no-confusion, for T_R and T_T, proved in
-- the finite-element model (Coquand-Huber; ERT.Model), with no
-- assumption.  A universe U_l denotes the element UCode l of the
-- domain, and the model is sound for conversion (ERT.Model.
-- RussellSound), so convertible universes denote the same element:
-- same level.  Tarski judgements are first erased to Russell ones
-- (ERT.EraseDeriv, paper Lemma 4.6).
--
-- These are the statements formerly postulated in ERT.Postulates
-- that the development actually uses (U-inj-Ty-T), together with the
-- other injectivity / no-confusion facts about universes and codes
-- that follow in the same way.
------------------------------------------------------------------------

module ERT.Injectivity where

open import ERT.Basic
import ERT.RussellSyntax  as R
import ERT.RussellTyping  as RT
import ERT.TarskiSyntax   as T
import ERT.TarskiTyping   as TT
open import ERT.EraseDeriv using (eraseCtx ; erase-ConvTy ; erase-ConvTm)
open import ERT.Dom.Basic using (EqL-refl ; EqL-Eq)
open import ERT.Dom.Basic using (FinEl ; Bot ; UCode)
import ERT.Model.Core as C
open import ERT.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; EvalRel ; EvalRel-Bot)
open import ERT.Model.SoundnessLemmas using (Fits)
open import ERT.Model.Strip using (strip ; stripCtx)
open import ERT.Model.RussellSound using (sound-CTy ; sound-CTm)

------------------------------------------------------------------------
-- The bottom environment fits every context
------------------------------------------------------------------------

botEnv : (n : Nat) -> EnvApprox n
botEnv zero    = emptyEnv
botEnv (suc n) = extendEnv (botEnv n) Bot

fits-bot : {n : Nat} (G : C.Ctx n) -> Fits G (botEnv n)
fits-bot C.empty        = tt
fits-bot (C.extend G A) =
  mkSigma (fits-bot G) (mkSigma Bot (mkSigma tt (EvalRel-Bot A (botEnv _))))

------------------------------------------------------------------------
-- T_R
------------------------------------------------------------------------

-- The element UCode l is in the denotation of U l.
evU : {n : Nat} (rho : EnvApprox n) (l : Nat) -> EvalRel (C.U l) rho (UCode l)
evU rho l = mkSigma tt (EqL-refl l)

U-inj-Ty-R : {n : Nat} {G : RT.Ctx n} {l l' : Nat}
  -> RT.ConvTy G (R.U l) (R.U l') -> Eq l l'
U-inj-Ty-R {n} {G} {l} {l'} d =
  let rho = botEnv n
      fwd = fst (snd (snd (sound-CTy d rho (fits-bot (stripCtx G)))))
  in EqL-Eq l l' (snd (fwd (UCode l) (evU rho l)))

U-Pi-noconf-Ty-R : {n : Nat} {G : RT.Ctx n} {l : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
  -> RT.ConvTy G (R.U l) (R.Pi A B) -> Empty
U-Pi-noconf-Ty-R {n} {G} {l} d =
  let rho = botEnv n
      fwd = fst (snd (snd (sound-CTy d rho (fits-bot (stripCtx G)))))
  in fwd (UCode l) (evU rho l)

-- The same for terms (codes) at any type.
U-inj-Tm-R : {n : Nat} {G : RT.Ctx n} {l l' : Nat} {A : R.Expr n}
  -> RT.ConvTm G (R.U l) (R.U l') A -> Eq l l'
U-inj-Tm-R {n} {G} {l} {l'} d =
  let rho = botEnv n
      fwd = fst (snd (snd (sound-CTm d rho (fits-bot (stripCtx G)))))
  in EqL-Eq l l' (snd (fwd (UCode l) (evU rho l)))

U-Pi-noconf-Tm-R : {n : Nat} {G : RT.Ctx n} {l : Nat} {A : R.Expr n}
  {B : R.Expr (suc n)} {T : R.Expr n}
  -> RT.ConvTm G (R.U l) (R.Pi A B) T -> Empty
U-Pi-noconf-Tm-R {n} {G} {l} d =
  let rho = botEnv n
      fwd = fst (snd (snd (sound-CTm d rho (fits-bot (stripCtx G)))))
  in fwd (UCode l) (evU rho l)

------------------------------------------------------------------------
-- T_T, through the erasure
------------------------------------------------------------------------

U-inj-Ty-T : {n : Nat} {G : TT.Ctx n} {l l' : Nat}
  -> TT.ConvTy G (T.U l) (T.U l') -> Eq l l'
U-inj-Ty-T d = U-inj-Ty-R (erase-ConvTy d)

U-Pi-noconf-Ty-T : {n : Nat} {G : TT.Ctx n} {l : Nat} {A : T.Expr n} {B : T.Expr (suc n)}
  -> TT.ConvTy G (T.U l) (T.Pi A B) -> Empty
U-Pi-noconf-Ty-T d = U-Pi-noconf-Ty-R (erase-ConvTy d)

UCode-inj-T : {n : Nat} {G : TT.Ctx n} {m l l' : Nat}
  -> TT.ConvTm G (T.UCode m l) (T.UCode m l') (T.U m) -> Eq l l'
UCode-inj-T d = U-inj-Tm-R (erase-ConvTm d)

UCode-PiCode-noconf-T : {n : Nat} {G : TT.Ctx n} {m l l' : Nat}
  {a : T.Expr n} {b : T.Expr (suc n)}
  -> TT.ConvTm G (T.UCode m l) (T.PiCode l' a b) (T.U m) -> Empty
UCode-PiCode-noconf-T d = U-Pi-noconf-Tm-R (erase-ConvTm d)
