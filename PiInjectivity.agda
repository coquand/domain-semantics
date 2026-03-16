{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PiInjectivity.agda
--
-- Corollary 6 (paper p.661), part 1: Pi head-reduction extraction.
--
-- If ConvTm G A₀ (Pi B₁ F₁) U, then:
--   (1) HeadRed A₀ (Pi B₀ F₀) for some B₀, F₀
--
-- Parts (2) ConvTm G B₀ B₁ U and (3) ConvTm (extend G B₀) F₀ F₁ U
-- require HasType/ConvTm stored at the leaves of the logical relation.
-- The current Val2/EqVal2 (Validity2.agda) stores Top at leaves,
-- which gives the head reduction but not the ConvTm extraction.
--
-- 0 postulates.
------------------------------------------------------------------------

module PiInjectivity where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons)
open import PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; EvalFun ;
  FinMem ; FinMemFun ; FinMemAllU ;
  FinMem-coh-u ; coh-from-aU)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr)
open import TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import Reduction using (Red ; mkRed ; Red-hr ; HeadRed ;
  headred-refl ; headred-beta ; headred-step ;
  idSub ; substExpr-id)
open import Validity2 using (Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  ValTyPi2 ; EqValTyPi2 ;
  Val2-transport-M ; Val2-transport-A ;
  Val2-Bot)
open import Adequacy2 using (adequacySub2 ; ValidSub2 ; ValidSub2-empty)
open import TypingSemantics using (convSound' ; theorem1)
open import LemmaForTS using (Fits ; Typed ; InvTyp ; InvConv)
open import SubstitutionLemma using (typing-ConvTm)
import Selection

------------------------------------------------------------------------
-- Structural inversion: HasType G (Pi A B) T →
--   HasType G A U × HasType (extend G A) B U
------------------------------------------------------------------------

ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB) = mkSigma dA dB
ty-Pi-invert (ty-conv d _ _) = ty-Pi-invert d

------------------------------------------------------------------------
-- Bot environment: maps all variables to Bot
------------------------------------------------------------------------

botEnv : (n : Nat) -> EnvApprox n
botEnv zero    = emptyEnv
botEnv (suc n) = extendEnv (botEnv n) Bot

botEnv-coherent : (n : Nat) -> CoherentEnv (botEnv n)
botEnv-coherent zero    = tt
botEnv-coherent (suc n) = mkSigma (botEnv-coherent n) tt

botEnv-lookup : {n : Nat} (i : Fin n) -> Eq (lookupEnv i (botEnv n)) Bot
botEnv-lookup fzero    = S.refl
botEnv-lookup (fsuc i) = botEnv-lookup i

------------------------------------------------------------------------
-- Fits G (botEnv n): trivially satisfied with a' = Bot everywhere
------------------------------------------------------------------------

botEnv-fits : {n : Nat} (G : Ctx n) -> Fits G (botEnv n)
botEnv-fits {zero} empty = tt
botEnv-fits {suc n} (extend G A) =
  mkSigma (botEnv-fits G) (mkSigma Bot (mkSigma tt (EvalRel-Bot A (botEnv n))))

------------------------------------------------------------------------
-- ValidSub2 G G idSub (botEnv n): trivial because u = Bot forced
------------------------------------------------------------------------

-- Helper: LeCode u (lookupEnv i (botEnv n)) forces u = Bot
botEnv-le-Bot : {n : Nat} (i : Fin n) (u : FinEl) ->
  LeCode u (lookupEnv i (botEnv n)) -> LeCode u Bot
botEnv-le-Bot i u le = S.Eq-transport (LeCode u) (botEnv-lookup i) le

botEnv-validSub2 : {n : Nat} (G : Ctx n) ->
  ValidSub2 G G idSub (botEnv n)
botEnv-validSub2 {zero}  empty ()
botEnv-validSub2 {suc n} (extend G A) fzero Bot cu le a evA fm = Val2-Bot a
botEnv-validSub2 {suc n} (extend G A) fzero UCode cu () a evA fm
botEnv-validSub2 {suc n} (extend G A) fzero (FunEl _) cu () a evA fm
botEnv-validSub2 {suc n} (extend G A) fzero (PiCode _ _) cu () a evA fm
botEnv-validSub2 {suc n} (extend G A) (fsuc i) Bot cu le a evA fm = Val2-Bot a
botEnv-validSub2 {suc n} (extend G A) (fsuc i) UCode cu le a evA fm =
  RawSemantics.absurd (botEnv-le-Bot i UCode le)
botEnv-validSub2 {suc n} (extend G A) (fsuc i) (FunEl g) cu le a evA fm =
  RawSemantics.absurd (botEnv-le-Bot i (FunEl g) le)
botEnv-validSub2 {suc n} (extend G A) (fsuc i) (PiCode b f) cu le a evA fm =
  RawSemantics.absurd (botEnv-le-Bot i (PiCode b f) le)

------------------------------------------------------------------------
-- EvalRel (Pi A B) rho (PiCode Bot nil): always constructible
------------------------------------------------------------------------

evalRel-Pi-trivial : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) ->
  EvalRel (Pi A B) rho (PiCode Bot nil)
evalRel-Pi-trivial A B rho =
  mkSigma (mkSigma tt tt)                              -- Coherent (PiCode Bot nil)
    (mkSigma (EvalRel-Bot A rho)                        -- EvalRel A rho Bot
      (mkSigma Bot (mkSigma (EvalRel-Bot A rho)         -- a' = Bot, EvalRel A rho Bot
        (\ u v sel -> sel-body u v sel))))               -- body (vacuous for nil)
  where
    -- Selection nil u v has exactly one inhabitant: sel-nil at (Bot, Bot)
    -- The body needs: Sigma FinEl \ x -> ...
    sel-body : (u v : FinEl) ->
      Selection.Selection nil u v ->
      Sigma FinEl (\ x -> Pair (LeCode x u)
        (Pair (FinMem x Bot) (EvalRel B (extendEnv rho x) v)))
    sel-body .Bot .Bot Selection.sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma tt (EvalRel-Bot B (extendEnv rho Bot))))

------------------------------------------------------------------------
-- Pi head-reduction extraction (Corollary 6, output 1)
--
-- From ConvTm G A₀ (Pi B₁ F₁) U, extract HeadRed A₀ (Pi B₀ F₀).
--
-- Strategy:
-- 1. typing-ConvTm → HasType G A₀ U
-- 2. convSound' → eval_bwd: Pi evals to PiCode → A₀ evals to PiCode
-- 3. adequacySub2 with idSub at botEnv → Val2 at (PiCode, UCode)
-- 4. Val2 at (PiCode Bot nil, UCode) = ValTyPi2 → extract Red → HeadRed
------------------------------------------------------------------------

piHeadRed : {n : Nat} {G : Ctx n} {A₀ : Expr n}
  {B₁ : Expr n} {F₁ : Expr (suc n)} ->
  ConvTm G A₀ (Pi B₁ F₁) U ->
  Sigma (Expr n) (\ B₀ -> Sigma (Expr (suc n)) (\ F₀ -> HeadRed A₀ (Pi B₀ F₀)))
piHeadRed {n} {G} {A₀} {B₁} {F₁} d =
  let -- Step 1: Extract HasType G A₀ U from ConvTm
      dA₀ : HasType G A₀ U
      dA₀ = fst (typing-ConvTm d)

      -- Step 2: Use convSound' to get bidirectional evaluation
      rho  = botEnv n
      fits = botEnv-fits G
      ic   = convSound' d rho fits
      -- ic : InvConv G A₀ (Pi B₁ F₁) U rho
      -- eval_bwd : EvalRel (Pi B₁ F₁) rho u → EvalRel A₀ rho u
      eval-bwd = snd (snd (snd ic))

      -- Step 3: Pi B₁ F₁ evaluates to PiCode Bot nil at any rho
      evPi : EvalRel (Pi B₁ F₁) rho (PiCode Bot nil)
      evPi = evalRel-Pi-trivial B₁ F₁ rho

      -- A₀ also evaluates to PiCode Bot nil
      evA₀ : EvalRel A₀ rho (PiCode Bot nil)
      evA₀ = eval-bwd (PiCode Bot nil) evPi

      -- Step 4: EvalRel U rho UCode
      evU : EvalRel U rho UCode
      evU = mkSigma tt (LeCode-refl UCode tt)

      -- FinMem (PiCode Bot nil) UCode
      fmPU : FinMem (PiCode Bot nil) UCode
      fmPU = mkSigma tt (mkSigma tt tt)

      -- Step 5: Apply adequacySub2 with idSub
      crho = botEnv-coherent n
      vs   = botEnv-validSub2 G

      raw : Val2 G (substExpr idSub A₀) (substExpr idSub U) (PiCode Bot nil) UCode
      raw = adequacySub2 dA₀ idSub rho crho vs fits
              (PiCode Bot nil) evA₀ UCode evU fmPU

      -- Transport: substExpr idSub A₀ = A₀, substExpr idSub U = U
      step1 : Val2 G (substExpr idSub A₀) U (PiCode Bot nil) UCode
      step1 = Val2-transport-A {M = substExpr idSub A₀}
               {u = PiCode Bot nil} {a = UCode} (substExpr-id U) raw
      vt : Val2 G A₀ U (PiCode Bot nil) UCode
      vt = Val2-transport-M {A = U}
             {u = PiCode Bot nil} {a = UCode} (substExpr-id A₀) step1

      -- Val2 G A₀ U (PiCode Bot nil) UCode = ValTy2 G A₀ (PiCode Bot nil)
      --                                     = ValTyPi2 G A₀ Bot nil
      -- ValTyPi2 = Sigma Expr \ A → Sigma Expr \ B → Sigma Red \ _ → ...
      -- Extract the Red
      B₀  = fst vt
      F₀  = fst (snd vt)
      red = fst (snd (snd vt))
      hr  = Red-hr red

  in mkSigma B₀ (mkSigma F₀ hr)
