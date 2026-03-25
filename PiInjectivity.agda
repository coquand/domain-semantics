{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PiInjectivity.agda
--
-- Corollary 6 (paper p.661): Pi injectivity.
--
-- If ConvTm G A₀ (Pi B₁ F₁) U, then:
--   (1) HeadRed A₀ (Pi B₀ F₀) for some B₀, F₀
--   (2) ConvTm G B₀ B₁ U         (domain conversion)
--   (3) ConvTm (extend G B₀) F₀ F₁ U  (codomain conversion)
--
-- As a corollary (piInjectivity):
-- If ConvTm G (Pi A₀ B₀) (Pi A₁ B₁) U, then:
--   ConvTm G A₀ A₁ U  and  ConvTm (extend G A₀) B₀ B₁ U
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
  ty-var ; ty-conv ; ty-U ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import Reduction using (Red ; mkRed ; Red-hr ; HeadRed ;
  headred-refl ; headred-beta ; headred-step ;
  idSub ; substExpr-id)
open import Validity2 using (Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  ValTyPi2 ; EqValTyPi2 ;
  Val2-transport-M ; Val2-transport-A ;
  EqVal2-transport-A ;
  Val2-Bot)
open import Validity using (Red-unique-Pi)
open import Adequacy2 using (adequacySub2 ; adequacyEqSub2 ;
  ValidSub2 ; ValidSub2-empty ; idSub-WtSub)
open import TypingSemantics using (convSound' ; theorem1)
open import LemmaForTS using (Fits ; Typed ; InvTyp ; InvConv)
open import SubstitutionLemma using (typing-ConvTm ; typing-WfCtx)
import Selection

------------------------------------------------------------------------
-- Structural inversion: HasType G (Pi A B) T →
--   HasType G A U × HasType (extend G A) B U
------------------------------------------------------------------------

ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB) = mkSigma dA dB
ty-Pi-invert (ty-Pi-Prop dA dB) = mkSigma dA (ty-Prop-U dB)
ty-Pi-invert (ty-Prop-U d) = ty-Pi-invert d
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

-- Val2-from-LeBot: LeCode u Bot forces u = Bot, giving Val2-Bot
Val2-from-LeBot : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u a : FinEl) -> LeCode u Bot -> Val2 G M A u a
Val2-from-LeBot Bot          a le = Val2-Bot a
Val2-from-LeBot UCode        a ()
Val2-from-LeBot (FunEl _)    a ()
Val2-from-LeBot (PiCode _ _) a ()

botEnv-validSub2 : {n : Nat} (G : Ctx n) ->
  ValidSub2 G G idSub (botEnv n)
botEnv-validSub2 {zero}  empty ()
botEnv-validSub2 {suc n} (extend G A) fzero u cu le a evA fm =
  Val2-from-LeBot u a le
botEnv-validSub2 {suc n} (extend G A) (fsuc i) u cu le a evA fm =
  Val2-from-LeBot u a (S.Eq-transport (LeCode u) (botEnv-lookup i) le)

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
-- Pi domain/codomain conversion (Corollary 6, parts 1–3)
--
-- From ConvTm G A₀ (Pi B₁ F₁) U, extract:
--   (2) ConvTm G B₀ B₁ U
--   (3) ConvTm (extend G B₀) F₀ F₁ U
-- where B₀, F₀ are such that HeadRed A₀ (Pi B₀ F₀).
--
-- Strategy:
-- 1. Apply adequacyEqSub2 at botEnv with idSub to get
--    EqVal2 G A₀ (Pi B₁ F₁) U (PiCode Bot nil) UCode
-- 2. This unfolds to EqValTy2 G A₀ (Pi B₁ F₁) (PiCode Bot nil)
--    = Pair (ValTyPi2 G A₀ Bot nil)
--           (Pair (ValTyPi2 G (Pi B₁ F₁) Bot nil)
--                 (EqValTyPi2 G A₀ (Pi B₁ F₁) Bot nil))
-- 3. EqValTyPi2 stores ConvTm G A A' U and ConvTm (extend G A) B B' U
--    where A=B₀, B=F₀ (from Red for A₀) and A'=B₁, B'=F₁ (from Red for Pi B₁ F₁)
------------------------------------------------------------------------

piConv : {n : Nat} {G : Ctx n} {A₀ : Expr n}
  {B₁ : Expr n} {F₁ : Expr (suc n)} ->
  ConvTm G A₀ (Pi B₁ F₁) U ->
  Sigma (Expr n) \ B₀ -> Sigma (Expr (suc n)) \ F₀ ->
  Sigma (HeadRed A₀ (Pi B₀ F₀)) \ _ ->
  Pair (ConvTm G B₀ B₁ U) (ConvTm (extend G B₀) F₀ F₁ U)
piConv {n} {G} {A₀} {B₁} {F₁} d =
  let -- Step 1: Setup
      rho  = botEnv n
      fits = botEnv-fits G
      crho = botEnv-coherent n
      vs   = botEnv-validSub2 G

      -- EvalRel data
      evPi : EvalRel (Pi B₁ F₁) rho (PiCode Bot nil)
      evPi = evalRel-Pi-trivial B₁ F₁ rho

      -- convSound' returns a 4-tuple; extract the transfer function
      mkSigma _ (mkSigma _ (mkSigma _ transfer)) = convSound' d rho fits

      evA₀ : EvalRel A₀ rho (PiCode Bot nil)
      evA₀ = transfer (PiCode Bot nil) evPi

      evU : EvalRel U rho UCode
      evU = mkSigma tt (LeCode-refl UCode tt)

      fmPU : FinMem (PiCode Bot nil) UCode
      fmPU = mkSigma tt (mkSigma tt tt)

      mkSigma htM _ = typing-ConvTm d
      wfG  = typing-WfCtx htM
      wsId = idSub-WtSub wfG

      -- Step 2: Apply adequacyEqSub2
      raw : EqVal2 G (substExpr idSub A₀) (substExpr idSub (Pi B₁ F₁))
                      (substExpr idSub U) (PiCode Bot nil) UCode
      raw = adequacyEqSub2 d idSub rho crho vs fits wsId wfG
              (PiCode Bot nil) evA₀ UCode evU fmPU

      -- Transport: substExpr idSub X = X
      step1 : EqVal2 G (substExpr idSub A₀) (substExpr idSub (Pi B₁ F₁))
                        U (PiCode Bot nil) UCode
      step1 = EqVal2-transport-A {M = substExpr idSub A₀}
                {N = substExpr idSub (Pi B₁ F₁)}
                {u = PiCode Bot nil} {a = UCode} (substExpr-id U) raw

      step2 : EqVal2 G A₀ (substExpr idSub (Pi B₁ F₁))
                        U (PiCode Bot nil) UCode
      step2 = S.Eq-transport
                (\ X -> EqVal2 G X (substExpr idSub (Pi B₁ F₁)) U (PiCode Bot nil) UCode)
                (substExpr-id A₀) step1

      ev2 : EqVal2 G A₀ (Pi B₁ F₁) U (PiCode Bot nil) UCode
      ev2 = S.Eq-transport
              (\ X -> EqVal2 G A₀ X U (PiCode Bot nil) UCode)
              (substExpr-id (Pi B₁ F₁)) step2

      -- EqVal2 at (PiCode Bot nil, UCode) = EqValTy2 at PiCode Bot nil
      -- = Pair (ValTyPi2 G A₀ Bot nil)
      --        (Pair (ValTyPi2 G (Pi B₁ F₁) Bot nil)
      --              (EqValTyPi2 G A₀ (Pi B₁ F₁) Bot nil))
      -- ev2 has this type

      -- Step 3: Extract from EqValTyPi2 via pattern matching
      -- ev2 at (PiCode, UCode) = Pair ValTyPi2_M (Pair ValTyPi2_N EqValTyPi2)
      mkSigma _ (mkSigma _ eqvty) = ev2
      mkSigma _ (mkSigma _ core)  = eqvty
      -- core : EqValTyPi2 G A₀ (Pi B₁ F₁) Bot nil
      --   = Sigma A B A' B' RedM RedN cf fmU ConvDom ConvCod (Pair ...)
      mkSigma B₀ (mkSigma F₀ (mkSigma B₁' (mkSigma F₁'
        (mkSigma redA₀ (mkSigma redPi (mkSigma _ (mkSigma _
          (mkSigma convDom (mkSigma convCod _))))))))) = core

      -- HeadRed from Red
      hrA₀  = Red-hr redA₀

      -- Red for (Pi B₁ F₁) is reflexive: B₁' = B₁, F₁' = F₁
      mkSigma eqB₁ eqF₁ = Red-unique-Pi redPi (mkRed headred-refl)

      -- Transport ConvTm along B₁' = B₁ and F₁' = F₁
      convDom' : ConvTm G B₀ B₁ U
      convDom' = S.Eq-transport (\ X -> ConvTm G B₀ X U) eqB₁ convDom

      convCod' : ConvTm (extend G B₀) F₀ F₁ U
      convCod' = S.Eq-transport (\ X -> ConvTm (extend G B₀) F₀ X U) eqF₁ convCod

  in mkSigma B₀ (mkSigma F₀ (mkSigma hrA₀ (mkSigma convDom' convCod')))

------------------------------------------------------------------------
-- Pi-Pi injectivity (Corollary)
--
-- From ConvTm G (Pi A₀ B₀) (Pi A₁ B₁) U, extract:
--   ConvTm G A₀ A₁ U  and  ConvTm (extend G A₀) B₀ B₁ U
------------------------------------------------------------------------

piInjectivity : {n : Nat} {G : Ctx n}
  {A₀ : Expr n} {B₀ : Expr (suc n)}
  {A₁ : Expr n} {B₁ : Expr (suc n)} ->
  ConvTm G (Pi A₀ B₀) (Pi A₁ B₁) U ->
  Pair (ConvTm G A₀ A₁ U) (ConvTm (extend G A₀) B₀ B₁ U)
piInjectivity {n} {G} {A₀} {B₀} {A₁} {B₁} d =
  let mkSigma B₀' (mkSigma F₀' (mkSigma hr (mkSigma convD convC))) = piConv d

      -- hr : HeadRed (Pi A₀ B₀) (Pi B₀' F₀')
      -- Pi is a normal form, so B₀' = A₀ and F₀' = B₀
      mkSigma eqA eqB = Red-unique-Pi {G = G} {B = B₀'} {F = F₀'}
        (mkRed hr) (mkRed (headred-refl {M = Pi A₀ B₀}))

      -- Transport: ConvTm G B₀' A₁ U  →  ConvTm G A₀ A₁ U
      convD' : ConvTm G A₀ A₁ U
      convD' = S.Eq-transport (\ X -> ConvTm G X A₁ U) eqA convD

      -- Transport: ConvTm (extend G B₀') F₀' B₁ U  →  ConvTm (extend G A₀) B₀ B₁ U
      convC' : ConvTm (extend G A₀) B₀ B₁ U
      convC' = S.Eq-transport (\ X -> ConvTm (extend G A₀) X B₁ U) eqB
                 (S.Eq-transport (\ X -> ConvTm (extend G X) F₀' B₁ U) eqA convC)

  in mkSigma convD' convC'
