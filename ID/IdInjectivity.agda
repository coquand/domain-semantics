{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.IdInjectivity.agda
--
-- Id injectivity for the Validity5/ID.Adequacy system, the exact analog
-- of ID.PiInjectivity for the identity-type former.
--
-- Id conversion (idConv):
-- If ConvTm G A₀ (Id B₁ L₁ R₁) U, then:
--   (1) HeadRed A₀ (Id B₀ L₀ R₀) for some B₀, L₀, R₀
--   (2) ConvTm G B₀ B₁ U
--   (3) ConvTm G L₀ L₁ B₀
--   (4) ConvTm G R₀ R₁ B₀
--
-- Id-Id injectivity (idInjectivity):
-- If ConvTm G (Id A₀ a₀ b₀) (Id A₁ a₁ b₁) U, then:
--   ConvTm G A₀ A₁ U, ConvTm G a₀ a₁ A₀, ConvTm G b₀ b₁ A₀.
--
-- This is what subject reduction of the based-J reduction needs: it lets
-- a `Ref` witness's Id type be inverted so the two endpoints are shown
-- convertible (see ID.SubjectReduction, ty-Ref-endpoints).
--
-- The trivial evaluation / membership pieces (evalRel-Id-trivial, fmIdU)
-- were verified independently against the green modules; the rest is a
-- verbatim transcription of piConv/piInjectivity with Pi ↦ Id.
--
-- 0 postulates.
------------------------------------------------------------------------

module ID.IdInjectivity where

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; FinEl ; Bot ; UCode ; IdCode)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; FinMem)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; EvalRel-Bot)
import ID.Syntax.Raw as RS
open RS using (Expr ; U ; Id ; substExpr)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm)
open import ID.Syntax.Reduction using (HeadRed ; headred-refl ; HeadRed-unique-Id ; idSub ; substExpr-id)
open import ID.Validity.Public using (Val2 ; EqVal2 ; EqValTy2 ; Red3 ; REqValTyId ; un-REqValTyId)
open import ID.Validity.Mono using (Red3-unique-Id)
open import ID.Adequacy.Helpers using (EqVal2-transport-A ; idSub-WtSub)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Adequacy.Value using (adequacyEqSub2)
open import ID.Model.Soundness using (convSound')
open import ID.Syntax.Substitution using (typing-ConvTm ; typing-WfCtx)
-- botEnv / Fits / ValidSub2 infrastructure, reused verbatim from PiInjectivity
open import ID.PiInjectivity using (botEnv ; botEnv-fits ; botEnv-coherent ; botEnv-validSub2)

------------------------------------------------------------------------
-- Trivial evaluation of an Id type to the least Id code, and membership
-- of that code in the universe.  (Both verified against the green
-- modules in isolation.)
------------------------------------------------------------------------

evalRel-Id-trivial : {n : Nat} (A a b : Expr n) (rho : EnvApprox n) ->
  EvalRel (Id A a b) rho (IdCode Bot Bot Bot)
evalRel-Id-trivial A a b rho =
  mkSigma (mkSigma tt (mkSigma tt tt))
    (mkSigma (EvalRel-Bot A rho)
      (mkSigma (EvalRel-Bot a rho) (EvalRel-Bot b rho)))

fmIdU : FinMem (IdCode Bot Bot Bot) UCode
fmIdU = mkSigma tt (mkSigma tt tt)

------------------------------------------------------------------------
-- Id domain/endpoint conversion.
--
-- From ConvTm G A₀ (Id B₁ L₁ R₁) U, extract HeadRed A₀ (Id B₀ L₀ R₀),
-- ConvTm G B₀ B₁ U, ConvTm G L₀ L₁ B₀, ConvTm G R₀ R₁ B₀.
------------------------------------------------------------------------

idConv : {n : Nat} {G : Ctx n} {A₀ : Expr n}
  {B₁ L₁ R₁ : Expr n} ->
  ConvTm G A₀ (Id B₁ L₁ R₁) U ->
  Sigma (Expr n) \ B₀ -> Sigma (Expr n) \ L₀ -> Sigma (Expr n) \ R₀ ->
  Sigma (HeadRed A₀ (Id B₀ L₀ R₀)) \ _ ->
  Pair (ConvTm G B₀ B₁ U) (Pair (ConvTm G L₀ L₁ B₀) (ConvTm G R₀ R₁ B₀))
idConv {n} {G} {A₀} {B₁} {L₁} {R₁} d =
  let rho  = botEnv n
      fits = botEnv-fits G
      crho = botEnv-coherent n
      vs   = botEnv-validSub2 G

      evId : EvalRel (Id B₁ L₁ R₁) rho (IdCode Bot Bot Bot)
      evId = evalRel-Id-trivial B₁ L₁ R₁ rho

      mkSigma _ (mkSigma _ transfer) = convSound' d rho fits

      evA₀ : EvalRel A₀ rho (IdCode Bot Bot Bot)
      evA₀ = snd transfer (IdCode Bot Bot Bot) evId

      evU : EvalRel U rho UCode
      evU = mkSigma tt (LeCode-refl UCode tt)

      mkSigma htM _ = typing-ConvTm d
      wfG  = typing-WfCtx htM
      wsId = idSub-WtSub wfG

      raw : EqVal2 G (substExpr idSub A₀) (substExpr idSub (Id B₁ L₁ R₁))
                      (substExpr idSub U) (IdCode Bot Bot Bot) UCode
      raw = adequacyEqSub2 d idSub rho crho vs fits wsId wfG
              (IdCode Bot Bot Bot) evA₀ UCode evU fmIdU

      step1 : EqVal2 G (substExpr idSub A₀) (substExpr idSub (Id B₁ L₁ R₁))
                        U (IdCode Bot Bot Bot) UCode
      step1 = EqVal2-transport-A {M = substExpr idSub A₀}
                {N = substExpr idSub (Id B₁ L₁ R₁)}
                {u = IdCode Bot Bot Bot} {a = UCode} (substExpr-id U) raw

      step2 : EqVal2 G A₀ (substExpr idSub (Id B₁ L₁ R₁))
                        U (IdCode Bot Bot Bot) UCode
      step2 = S.Eq-transport
                (\ X -> EqVal2 G X (substExpr idSub (Id B₁ L₁ R₁)) U (IdCode Bot Bot Bot) UCode)
                (substExpr-id A₀) step1

      ev2 : EqVal2 G A₀ (Id B₁ L₁ R₁) U (IdCode Bot Bot Bot) UCode
      ev2 = S.Eq-transport
              (\ X -> EqVal2 G A₀ X U (IdCode Bot Bot Bot) UCode)
              (substExpr-id (Id B₁ L₁ R₁)) step2

      -- Extract the REqValTyId core (same projection path as PiCode/UCode).
      mkSigma _ (mkSigma _ eqvty) = ev2
      core = un-REqValTyId (snd eqvty)

      B₀  = REqValTyId.domA core
      L₀  = REqValTyId.lhs core
      R₀  = REqValTyId.rhs core
      B₁' = REqValTyId.domA' core
      L₁' = REqValTyId.lhs' core
      R₁' = REqValTyId.rhs' core
      redA₀ = REqValTyId.redM core
      redId = REqValTyId.redN core
      convDom = REqValTyId.convA core
      convLhs = REqValTyId.convL core
      convRhs = REqValTyId.convR core

      hrA₀ = Red3.hr redA₀

      -- Red for (Id B₁ L₁ R₁) is reflexive: B₁' = B₁, L₁' = L₁, R₁' = R₁.
      mkSigma eqB (mkSigma eqL eqR) =
        HeadRed-unique-Id (Red3.hr redId) (headred-refl {M = Id B₁ L₁ R₁})

      convDom' : ConvTm G B₀ B₁ U
      convDom' = S.Eq-transport (\ X -> ConvTm G B₀ X U) eqB convDom

      convLhs' : ConvTm G L₀ L₁ B₀
      convLhs' = S.Eq-transport (\ X -> ConvTm G L₀ X B₀) eqL convLhs

      convRhs' : ConvTm G R₀ R₁ B₀
      convRhs' = S.Eq-transport (\ X -> ConvTm G R₀ X B₀) eqR convRhs

  in mkSigma B₀ (mkSigma L₀ (mkSigma R₀
       (mkSigma hrA₀ (mkSigma convDom' (mkSigma convLhs' convRhs')))))

------------------------------------------------------------------------
-- Id-Id injectivity.
------------------------------------------------------------------------

idInjectivity : {n : Nat} {G : Ctx n}
  {A₀ a₀ b₀ : Expr n} {A₁ a₁ b₁ : Expr n} ->
  ConvTm G (Id A₀ a₀ b₀) (Id A₁ a₁ b₁) U ->
  Pair (ConvTm G A₀ A₁ U) (Pair (ConvTm G a₀ a₁ A₀) (ConvTm G b₀ b₁ A₀))
idInjectivity {n} {G} {A₀} {a₀} {b₀} {A₁} {a₁} {b₁} d =
  let mkSigma B₀ (mkSigma L₀ (mkSigma R₀
        (mkSigma hr (mkSigma convDom (mkSigma convLhs convRhs))))) = idConv d

      -- Id A₀ a₀ b₀ head-reduces (reflexively) to Id B₀ L₀ R₀, so they agree.
      mkSigma eqA (mkSigma eqa eqb) =
        HeadRed-unique-Id hr (headred-refl {M = Id A₀ a₀ b₀})

      convDom' : ConvTm G A₀ A₁ U
      convDom' = S.Eq-transport (\ X -> ConvTm G X A₁ U) eqA convDom

      convLhs' : ConvTm G a₀ a₁ A₀
      convLhs' = S.Eq-transport (\ X -> ConvTm G a₀ a₁ X) eqA
                   (S.Eq-transport (\ X -> ConvTm G X a₁ B₀) eqa convLhs)

      convRhs' : ConvTm G b₀ b₁ A₀
      convRhs' = S.Eq-transport (\ X -> ConvTm G b₀ b₁ X) eqA
                   (S.Eq-transport (\ X -> ConvTm G X b₁ B₀) eqb convRhs)

  in mkSigma convDom' (mkSigma convLhs' convRhs')
