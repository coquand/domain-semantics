{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Injectivity5.agda
--
-- Pi and Sigma injectivity for the Validity5/Adequacy5 system.
--
-- Pi injectivity (piConv / piInjectivity):
-- If ConvTm G A₀ (Pi B₁ F₁) U, then:
--   (1) HeadRed A₀ (Pi B₀ F₀) for some B₀, F₀
--   (2) ConvTm G B₀ B₁ U
--   (3) ConvTm (extend G B₀) F₀ F₁ U
--
-- Sigma injectivity (sigmaConv / sigmaInjectivity):
-- If ConvTm G A₀ (Sigma B₁ F₁) U, then:
--   (1) HeadRed A₀ (Sigma B₀ F₀) for some B₀, F₀
--   (2) ConvTm G B₀ B₁ U
--   (3) ConvTm (extend G B₀) F₀ F₁ U
--
-- 0 postulates.
------------------------------------------------------------------------

module SigmaProp.Injectivity5 where

import SigmaProp.BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; SigmaCode ;
              PairCode ; PropCode ; FinFun ;
              List ; nil ; cons)
open import SigmaProp.PaperSemanticsSigma using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; EvalFun ;
  FinMem ; FinMemFun ; FinMemAllU ;
  FinMem-coh-u ; coh-from-aU)
open import SigmaProp.RawSemanticsSigma using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe)
import SigmaProp.RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ; MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr)
open import SigmaProp.TypingRulesSigma using (Ctx ; empty ; extend ; lookup ;
  HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-conv ; ty-U ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  ty-Sigma ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Sigma)
open import SigmaProp.ReductionSigma using (Red ; mkRed ; Red-hr ; HeadRed ;
  headred-refl ; headred-beta ; headred-step ;
  idSub ; substExpr-id)
open import SigmaProp.ValiditySigma using (Red-unique-Pi ; Red-unique-Sigma)
open import SigmaProp.Validity5Core using (Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  Val2-Bot ; Red3 ; mkRed3 ; Red3-unique-Pi ; Red3-unique-Sigma ;
  REqValTyPi ; REqValTySigma)
open import SigmaProp.Adequacy5Helpers using (EqVal2-transport-A ;
  ValidSub2 ; ValidSub2-empty ; idSub-WtSub ;
  WtSub)
open import SigmaProp.LemmaForTSSigma using (Fits)
open import SigmaProp.Adequacy5 using (adequacySub2 ; adequacyEqSub2)
open import SigmaProp.TypingSemanticsSigma using (convSound')
open import SigmaProp.SubstitutionLemmaSigma using (typing-ConvTm ; typing-WfCtx)
import SigmaProp.SelectionSigma as SelectionSigma

------------------------------------------------------------------------
-- Structural inversions
------------------------------------------------------------------------

ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB) = mkSigma dA dB
ty-Pi-invert (ty-Pi-Prop dA dB) = mkSigma dA (ty-Prop-U dB)
ty-Pi-invert (ty-Prop-U d) = ty-Pi-invert d
ty-Pi-invert (ty-conv d _ _) = ty-Pi-invert d

ty-Sigma-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (RS.Sigma A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Sigma-invert (ty-Sigma dA dB) = mkSigma dA dB
ty-Sigma-invert (ty-Prop-U d) = ty-Sigma-invert d
ty-Sigma-invert (ty-conv d _ _) = ty-Sigma-invert d

------------------------------------------------------------------------
-- Bot environment
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
-- Fits G (botEnv n)
------------------------------------------------------------------------

botEnv-fits : {n : Nat} (G : Ctx n) -> Fits G (botEnv n)
botEnv-fits {zero} empty = tt
botEnv-fits {suc n} (extend G A) =
  mkSigma (botEnv-fits G) (mkSigma Bot (mkSigma tt (EvalRel-Bot A (botEnv n))))

------------------------------------------------------------------------
-- ValidSub2 G G idSub (botEnv n)
------------------------------------------------------------------------

Val2-from-LeBot : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u a : FinEl) -> LeCode u Bot -> Val2 G M A u a
Val2-from-LeBot Bot              a le = Val2-Bot a
Val2-from-LeBot UCode            a ()
Val2-from-LeBot (FunEl _)        a ()
Val2-from-LeBot (PiCode _ _)     a ()
Val2-from-LeBot PropCode         a ()
Val2-from-LeBot (SigmaCode _ _)  a ()
Val2-from-LeBot (PairCode _ _)   a ()

botEnv-validSub2 : {n : Nat} (G : Ctx n) ->
  ValidSub2 G G idSub (botEnv n)
botEnv-validSub2 {zero}  empty ()
botEnv-validSub2 {suc n} (extend G A) fzero u cu le a evA fm =
  Val2-from-LeBot u a le
botEnv-validSub2 {suc n} (extend G A) (fsuc i) u cu le a evA fm =
  Val2-from-LeBot u a (S.Eq-transport (LeCode u) (botEnv-lookup i) le)

------------------------------------------------------------------------
-- Trivial EvalRel for Pi and Sigma
------------------------------------------------------------------------

evalRel-Pi-trivial : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) ->
  EvalRel (Pi A B) rho (PiCode Bot nil)
evalRel-Pi-trivial A B rho =
  mkSigma (mkSigma tt tt)
    (mkSigma (EvalRel-Bot A rho)
      (mkSigma Bot (mkSigma (EvalRel-Bot A rho)
        (\ u v sel -> sel-body u v sel))))
  where
    sel-body : (u v : FinEl) ->
      SelectionSigma.Selection nil u v ->
      Sigma FinEl (\ x -> Pair (LeCode x u)
        (Pair (FinMem x Bot) (EvalRel B (extendEnv rho x) v)))
    sel-body .Bot .Bot SelectionSigma.sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma tt (EvalRel-Bot B (extendEnv rho Bot))))

evalRel-Sigma-trivial : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) ->
  EvalRel (RS.Sigma A B) rho (SigmaCode Bot nil)
evalRel-Sigma-trivial A B rho =
  mkSigma (mkSigma tt tt)
    (mkSigma (EvalRel-Bot A rho)
      (mkSigma Bot (mkSigma (EvalRel-Bot A rho)
        (\ u v sel -> sel-body u v sel))))
  where
    sel-body : (u v : FinEl) ->
      SelectionSigma.Selection nil u v ->
      Sigma FinEl (\ x -> Pair (LeCode x u)
        (Pair (FinMem x Bot) (EvalRel B (extendEnv rho x) v)))
    sel-body .Bot .Bot SelectionSigma.sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma tt (EvalRel-Bot B (extendEnv rho Bot))))

------------------------------------------------------------------------
-- Pi domain/codomain conversion
--
-- From ConvTm G A₀ (Pi B₁ F₁) U, extract:
--   HeadRed A₀ (Pi B₀ F₀), ConvTm G B₀ B₁ U, ConvTm (extend G B₀) F₀ F₁ U
------------------------------------------------------------------------

piConv : {n : Nat} {G : Ctx n} {A₀ : Expr n}
  {B₁ : Expr n} {F₁ : Expr (suc n)} ->
  ConvTm G A₀ (Pi B₁ F₁) U ->
  Sigma (Expr n) \ B₀ -> Sigma (Expr (suc n)) \ F₀ ->
  Sigma (HeadRed A₀ (Pi B₀ F₀)) \ _ ->
  Pair (ConvTm G B₀ B₁ U) (ConvTm (extend G B₀) F₀ F₁ U)
piConv {n} {G} {A₀} {B₁} {F₁} d =
  let rho  = botEnv n
      fits = botEnv-fits G
      crho = botEnv-coherent n
      vs   = botEnv-validSub2 G

      evPi : EvalRel (Pi B₁ F₁) rho (PiCode Bot nil)
      evPi = evalRel-Pi-trivial B₁ F₁ rho

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

      -- Apply adequacyEqSub2
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

      -- Extract from EqValTyPi
      -- ev2 : Pair (ValTy2 ..) (Pair (ValTy2 ..) (EqValTy2 ..))
      -- EqValTy2 at PiCode = Pair (RValTyPi M ..) (Pair (RValTyPi N ..) (REqValTyPi ..))
      mkSigma _ (mkSigma _ eqvty) = ev2
      core = snd (snd (snd eqvty))

      B₀  = REqValTyPi.domA core
      F₀  = REqValTyPi.codB core
      B₁' = REqValTyPi.domA' core
      F₁' = REqValTyPi.codB' core
      redA₀  = REqValTyPi.redM core
      redPi  = REqValTyPi.redN core
      convDom = REqValTyPi.convA core
      convCod = REqValTyPi.convB core

      hrA₀ = Red3.hr redA₀

      -- Red for (Pi B₁ F₁) is reflexive: B₁' = B₁, F₁' = F₁
      mkSigma eqB₁ eqF₁ = Red-unique-Pi {G = G}
        (mkRed (Red3.hr redPi)) (mkRed (headred-refl {M = Pi B₁ F₁}))

      convDom' : ConvTm G B₀ B₁ U
      convDom' = S.Eq-transport (\ X -> ConvTm G B₀ X U) eqB₁ convDom

      convCod' : ConvTm (extend G B₀) F₀ F₁ U
      convCod' = S.Eq-transport (\ X -> ConvTm (extend G B₀) F₀ X U) eqF₁ convCod

  in mkSigma B₀ (mkSigma F₀ (mkSigma hrA₀ (mkSigma convDom' convCod')))

------------------------------------------------------------------------
-- Pi-Pi injectivity
------------------------------------------------------------------------

piInjectivity : {n : Nat} {G : Ctx n}
  {A₀ : Expr n} {B₀ : Expr (suc n)}
  {A₁ : Expr n} {B₁ : Expr (suc n)} ->
  ConvTm G (Pi A₀ B₀) (Pi A₁ B₁) U ->
  Pair (ConvTm G A₀ A₁ U) (ConvTm (extend G A₀) B₀ B₁ U)
piInjectivity {n} {G} {A₀} {B₀} {A₁} {B₁} d =
  let mkSigma B₀' (mkSigma F₀' (mkSigma hr (mkSigma convD convC))) = piConv d

      mkSigma eqA eqB = Red-unique-Pi {G = G} {B = B₀'} {F = F₀'}
        (mkRed hr) (mkRed (headred-refl {M = Pi A₀ B₀}))

      convD' : ConvTm G A₀ A₁ U
      convD' = S.Eq-transport (\ X -> ConvTm G X A₁ U) eqA convD

      convC' : ConvTm (extend G A₀) B₀ B₁ U
      convC' = S.Eq-transport (\ X -> ConvTm (extend G A₀) X B₁ U) eqB
                 (S.Eq-transport (\ X -> ConvTm (extend G X) F₀' B₁ U) eqA convC)

  in mkSigma convD' convC'

------------------------------------------------------------------------
-- Sigma domain/codomain conversion
--
-- From ConvTm G A₀ (Sigma B₁ F₁) U, extract:
--   HeadRed A₀ (Sigma B₀ F₀), ConvTm G B₀ B₁ U,
--   ConvTm (extend G B₀) F₀ F₁ U
------------------------------------------------------------------------

sigmaConv : {n : Nat} {G : Ctx n} {A₀ : Expr n}
  {B₁ : Expr n} {F₁ : Expr (suc n)} ->
  ConvTm G A₀ (RS.Sigma B₁ F₁) U ->
  Sigma (Expr n) \ B₀ -> Sigma (Expr (suc n)) \ F₀ ->
  Sigma (HeadRed A₀ (RS.Sigma B₀ F₀)) \ _ ->
  Pair (ConvTm G B₀ B₁ U) (ConvTm (extend G B₀) F₀ F₁ U)
sigmaConv {n} {G} {A₀} {B₁} {F₁} d =
  let rho  = botEnv n
      fits = botEnv-fits G
      crho = botEnv-coherent n
      vs   = botEnv-validSub2 G

      evSig : EvalRel (RS.Sigma B₁ F₁) rho (SigmaCode Bot nil)
      evSig = evalRel-Sigma-trivial B₁ F₁ rho

      mkSigma _ (mkSigma _ (mkSigma _ transfer)) = convSound' d rho fits

      evA₀ : EvalRel A₀ rho (SigmaCode Bot nil)
      evA₀ = transfer (SigmaCode Bot nil) evSig

      evU : EvalRel U rho UCode
      evU = mkSigma tt (LeCode-refl UCode tt)

      fmSU : FinMem (SigmaCode Bot nil) UCode
      fmSU = mkSigma tt (mkSigma tt tt)

      mkSigma htM _ = typing-ConvTm d
      wfG  = typing-WfCtx htM
      wsId = idSub-WtSub wfG

      -- Apply adequacyEqSub2
      raw : EqVal2 G (substExpr idSub A₀) (substExpr idSub (RS.Sigma B₁ F₁))
                      (substExpr idSub U) (SigmaCode Bot nil) UCode
      raw = adequacyEqSub2 d idSub rho crho vs fits wsId wfG
              (SigmaCode Bot nil) evA₀ UCode evU fmSU

      step1 : EqVal2 G (substExpr idSub A₀) (substExpr idSub (RS.Sigma B₁ F₁))
                        U (SigmaCode Bot nil) UCode
      step1 = EqVal2-transport-A {M = substExpr idSub A₀}
                {N = substExpr idSub (RS.Sigma B₁ F₁)}
                {u = SigmaCode Bot nil} {a = UCode} (substExpr-id U) raw

      step2 : EqVal2 G A₀ (substExpr idSub (RS.Sigma B₁ F₁))
                        U (SigmaCode Bot nil) UCode
      step2 = S.Eq-transport
                (\ X -> EqVal2 G X (substExpr idSub (RS.Sigma B₁ F₁)) U (SigmaCode Bot nil) UCode)
                (substExpr-id A₀) step1

      ev2 : EqVal2 G A₀ (RS.Sigma B₁ F₁) U (SigmaCode Bot nil) UCode
      ev2 = S.Eq-transport
              (\ X -> EqVal2 G A₀ X U (SigmaCode Bot nil) UCode)
              (substExpr-id (RS.Sigma B₁ F₁)) step2

      -- Extract from EqValTySigma
      -- EqValTy2 at SigmaCode = Pair (RValTySigma M ..) (Pair (RValTySigma N ..) (REqValTySigma ..))
      mkSigma _ (mkSigma _ eqvty) = ev2
      core = snd (snd (snd eqvty))

      B₀  = REqValTySigma.domA core
      F₀  = REqValTySigma.codB core
      B₁' = REqValTySigma.domA' core
      F₁' = REqValTySigma.codB' core
      redA₀  = REqValTySigma.redM core
      redSig = REqValTySigma.redN core
      convDom = REqValTySigma.convA core
      convCod = REqValTySigma.convB core

      hrA₀ = Red3.hr redA₀

      -- Red for (Sigma B₁ F₁) is reflexive: B₁' = B₁, F₁' = F₁
      mkSigma eqB₁ eqF₁ = Red-unique-Sigma {G = G}
        (mkRed (Red3.hr redSig)) (mkRed (headred-refl {M = RS.Sigma B₁ F₁}))

      convDom' : ConvTm G B₀ B₁ U
      convDom' = S.Eq-transport (\ X -> ConvTm G B₀ X U) eqB₁ convDom

      convCod' : ConvTm (extend G B₀) F₀ F₁ U
      convCod' = S.Eq-transport (\ X -> ConvTm (extend G B₀) F₀ X U) eqF₁ convCod

  in mkSigma B₀ (mkSigma F₀ (mkSigma hrA₀ (mkSigma convDom' convCod')))

------------------------------------------------------------------------
-- Sigma-Sigma injectivity
------------------------------------------------------------------------

sigmaInjectivity : {n : Nat} {G : Ctx n}
  {A₀ : Expr n} {B₀ : Expr (suc n)}
  {A₁ : Expr n} {B₁ : Expr (suc n)} ->
  ConvTm G (RS.Sigma A₀ B₀) (RS.Sigma A₁ B₁) U ->
  Pair (ConvTm G A₀ A₁ U) (ConvTm (extend G A₀) B₀ B₁ U)
sigmaInjectivity {n} {G} {A₀} {B₀} {A₁} {B₁} d =
  let mkSigma B₀' (mkSigma F₀' (mkSigma hr (mkSigma convD convC))) = sigmaConv d

      mkSigma eqA eqB = Red-unique-Sigma {G = G}
        (mkRed hr) (mkRed (headred-refl {M = RS.Sigma A₀ B₀}))

      convD' : ConvTm G A₀ A₁ U
      convD' = S.Eq-transport (\ X -> ConvTm G X A₁ U) eqA convD

      convC' : ConvTm (extend G A₀) B₀ B₁ U
      convC' = S.Eq-transport (\ X -> ConvTm (extend G A₀) X B₁ U) eqB
                 (S.Eq-transport (\ X -> ConvTm (extend G X) F₀' B₁ U) eqA convC)

  in mkSigma convD' convC'
