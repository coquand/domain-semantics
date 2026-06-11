{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.AdequacyCastV.agda
--
-- Reusable value-only combinators for the cast rules:
--   adequacyV-ty-cast   : Adq for  cast A B p M : B   (ty-cast value driver,
--                         factored so conv-cast-Pi can use it as IHcast).
-- 0 postulates.
------------------------------------------------------------------------

module CAST.AdequacyCastV where

open import CAST.AdequacyHeadRed
open import CAST.AdequacyPi using (Adq ; AdqConv ; Val2-U-to-ValTy2)
open import CAST.AdequacyCastDriver using (castVal-pub)
open import CAST.AdequacyApp using (adequacySub2-App)
open import CAST.AdequacyBundle using (adequacy-ty-Pi-full)

import CAST.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; UCode ; Eq-cong ; Eq-transport)
open import CAST.RawSyntax using (Expr ; U ; Pi ; App ; Id ; cast ; sym ; pi1 ; pi2 ;
  subst1 ; Sub ; liftSub ; substExpr)
open import CAST.TypingRules using (Ctx ; extend ; HasType ; WfCtx ; ConvTm ;
  ty-Pi ; ty-cast ; conv-refl ; conv-cast-Pi)
open import CAST.Reduction using (HeadRed ; headred-step ; headred-refl ; headred-cast-Pi ; subst-subst1-comm)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ;
  FinMem-a-in-U ; FinMem-coh-u)
open import CAST.RawSemantics using (EnvApprox ; EvalRel ; EvalRel-coh ; CoherentEnv)
open import CAST.TypingSemantics using (theorem1)
open import CAST.LemmaForTS using (Fits)
open import CAST.SubstitutionLemma using (WtSub ; subst-HasType ; subst-ConvTm ; typing-ConvTm)

------------------------------------------------------------------------
-- adequacyV-ty-cast : Adq G (cast A B p M) B
------------------------------------------------------------------------

adequacyV-ty-cast : {g : Nat} {G : Ctx g} {A B p M : Expr g} ->
  HasType G A U -> HasType G B U -> HasType G p (Id A B) -> HasType G M A ->
  Adq G A U -> Adq G B U -> Adq G M A ->
  Adq G (cast A B p M) B
adequacyV-ty-cast {A = A} {B = B} {p = p} {M = M} dA dB dp dM IH-A IH-B IH-M
  sigma rho crho vs fits wtsub wfH u hu a evA fm =
  castVal-pub _ _ _ _ u v' c a le-u-v' fm fm-v'-c cohv'
    (subst-HasType wtsub wfH dA) (subst-HasType wtsub wfH dB)
    (subst-HasType wtsub wfH dp) (subst-HasType wtsub wfH dM)
    valtyA valtyB IH-Mv
  where
    cu     = fst hu
    v      = fst (snd hu)
    le-u-v = fst (snd (snd hu))
    evM-v  = fst (snd (snd (snd hu)))
    typedM = theorem1 dM rho fits v evM-v
    v'      = fst typedM
    c       = fst (snd typedM)
    le-v-v' = fst (snd (snd typedM))
    evM-v'  = fst (snd (snd (snd typedM)))
    fm-v'-c = fst (snd (snd (snd (snd typedM))))
    evA-c   = snd (snd (snd (snd (snd typedM))))
    cohv'   = FinMem-coh-u v' c fm-v'-c
    le-u-v' = LeCode-trans u v v' cu (EvalRel-coh M rho v evM-v) cohv' le-u-v le-v-v'
    cU      = FinMem-a-in-U v' c fm-v'-c
    aU      = FinMem-a-in-U u a fm
    evU     = mkSigma tt (LeCode-refl UCode tt)
    IH-Mv   = IH-M sigma rho crho vs fits wtsub wfH v' evM-v' c evA-c fm-v'-c
    valtyA  = Val2-U-to-ValTy2 c cU (IH-A sigma rho crho vs fits wtsub wfH c evA-c UCode evU cU)
    valtyB  = Val2-U-to-ValTy2 a aU (IH-B sigma rho crho vs fits wtsub wfH a evA UCode evU aU)

------------------------------------------------------------------------
-- adequacyEqSub2-coePi : the conv-cast-Pi head-expansion.
--   App (cast (Pi A B)(Pi C D) p M) N  =  reduct  : subst1 D N
-- reduct = cast (subst1 B N')(subst1 D N) (sym(pi2(sym p)N)) (App M N'),
--   N' = cast C A (pi1(sym p)) N.
-- Build Val2(redex) via adequacySub2-App with IHcast = adequacyV-ty-cast for
-- the literal-Pi cast; contract to the reduct; head-expand the diagonal.
------------------------------------------------------------------------

adequacyEqSub2-coePi : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A C : Expr g} {B D : Expr (suc g)} {p M N : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G C U -> HasType (extend G C) D U ->
  HasType G p (Id (Pi A B) (Pi C D)) -> HasType G M (Pi A B) -> HasType G N C ->
  Adq G A U -> Adq (extend G A) B U -> AdqConv (extend G A) B U ->
  Adq G C U -> Adq (extend G C) D U -> AdqConv (extend G C) D U ->
  Adq G M (Pi A B) -> Adq G N C ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (App (cast (Pi A B) (Pi C D) p M) N) rho u ->
  (a : FinEl) -> EvalRel (subst1 D N) rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma (App (cast (Pi A B) (Pi C D) p M) N))
           (substExpr sigma (cast (subst1 B (cast C A (pi1 (sym p)) N)) (subst1 D N)
                                  (sym (pi2 (sym p) N)) (App M (cast C A (pi1 (sym p)) N))))
           (substExpr sigma (subst1 D N)) u a
adequacyEqSub2-coePi {H = H} {G = G} {A = A} {C = C} {B = B} {D = D} {p = p} {M = M} {N = N}
  dA dB dC dD dp dM dN IH-A IH-B IH-Bc IH-C IH-D IH-Dc IH-M IH-N
  sigma rho crho vs fits wtsub wfH u hu a evA fm =
  EqVal2-headred-expand u a hr headred-refl cv (conv-refl htReduct) eqdiag
  where
    sA = substExpr sigma A ; sC = substExpr sigma C ; sp = substExpr sigma p
    sM = substExpr sigma M ; sN = substExpr sigma N
    sN' = cast sC sA (pi1 (sym sp)) sN
    sq'' = sym (pi2 (sym sp) sN)
    castTy = ty-cast (ty-Pi dA dB) (ty-Pi dC dD) dp dM
    IH-PiAB : Adq G (Pi A B) U
    IH-PiAB {h2} {H2} = adequacy-ty-Pi-full {h = h2} {H = H2} dA dB IH-A IH-B IH-Bc
    IH-PiCD : Adq G (Pi C D) U
    IH-PiCD {h2} {H2} = adequacy-ty-Pi-full {h = h2} {H = H2} dC dD IH-C IH-D IH-Dc
    IHcast = adequacyV-ty-cast (ty-Pi dA dB) (ty-Pi dC dD) dp dM IH-PiAB IH-PiCD IH-M
    Val2redex = adequacySub2-App dC dD castTy dN IHcast IH-N IH-D
                  sigma rho crho vs fits wtsub wfH u
                  (EvalRel-coh (App (cast (Pi A B) (Pi C D) p M) N) rho u hu) hu a evA fm
    -- redex --(headred-cast-Pi)--> RDT;  RDT = substExpr sigma reduct (subst-comm)
    sB = substExpr (liftSub sigma) B
    sD = substExpr (liftSub sigma) D
    e1 = subst-subst1-comm sigma B (cast C A (pi1 (sym p)) N)
    e2 = subst-subst1-comm sigma D N
    eq-RDT = Eq-trans
               (Eq-cong (\ X -> cast X (subst1 sD sN) sq'' (App sM sN')) e1)
               (Eq-cong (\ Y -> cast (substExpr sigma (subst1 B (cast C A (pi1 (sym p)) N))) Y sq'' (App sM sN')) e2)
    cv = subst-ConvTm wtsub wfH (conv-cast-Pi dA dB dC dD dp dM dN)
    hr = Eq-transport (\ X -> HeadRed (App (cast (Pi sA sB) (Pi sC sD) sp sM) sN) X)
           eq-RDT (headred-step headred-cast-Pi headred-refl)
    Val2reduct = Val2-headred-contract u a hr cv Val2redex
    htReduct = snd (typing-ConvTm cv)
    eqdiag = Val2-to-EqVal2 u a Val2reduct
