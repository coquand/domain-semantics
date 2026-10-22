{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MINPROP.Adequacy.Prop
--
-- The Prop combinators of the value-only fundamental theorem
-- (MINPROP.Adequacy.Value).  All are NON-recursive: they take the IHs of
-- the premises as parameters.
--
--   * Prop codes are Bot or Pi codes (IsProp), and validity at PropCode
--     has the same shape as validity at UCode, with ValTy2 Prop PropCode
--     (= Red3 _ Prop U) in place of ValTy2 U UCode.  Hence the transfers
--     Val2-Prop-to-U / Val2-U-to-Prop (and the EqVal2 versions).
--   * ty-Prop-U / conv-Prop-U : an approximant u of A : Prop is a Prop
--     code (soundness, typed-isProp), so u : PropCode and the IH at
--     (u, PropCode) transfers to (u, UCode).
--   * ty-Pi-Prop / conv-Pi-Prop : reuse the Pi-into-U combinators on the
--     U-weakened premises, then transfer U -> Prop.
--   * conv-Prop (proof irrelevance): every approximant of a proof is Bot
--     (proof-Bot, i.e. prop-collapse), and EqVal2 at Bot is trivial.
--
-- No postulates.
------------------------------------------------------------------------

module MINPROP.Adequacy.Prop where

open import MINPROP.Adequacy.HeadRed

import MINPROP.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun)
open import MINPROP.Domain.Kernel using (LeCode ; FinMem ; finMem-prop-U ; finMem-prop-mk)
open import MINPROP.Model.Eval using (EnvApprox ; EvalRel ; CoherentEnv)
open import MINPROP.Syntax.Raw using (Expr ; U ; Prop ; Pi ; Sub ; substExpr)
open import MINPROP.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ;
  ty-U ; ty-Prop ; conv-refl)
open import MINPROP.Syntax.Substitution using (WtSub ; WtConvSub ; typing-ConvTm)
open import MINPROP.Syntax.Reduction using (headred-refl)
open import MINPROP.Model.Soundness using (theorem1)
open import MINPROP.Model.SoundnessLemmas using (Fits)
open import MINPROP.Model.SoundnessProp using (typed-isProp ; proof-Bot)
open import MINPROP.Adequacy.Pi using (Adq ; AdqConv)
open import MINPROP.Adequacy.VE using (AdqE1 ; adequacyV-ty-Pi ; adequacyEqSub2-Pi-core)

------------------------------------------------------------------------
-- Validity at Prop vs U, for Prop codes.
------------------------------------------------------------------------

redU : {h : Nat} {H : Ctx h} -> WfCtx H -> ValTy2 H U UCode
redU wfH = mkRed3 headred-refl (conv-refl (ty-U wfH))

redP : {h : Nat} {H : Ctx h} -> WfCtx H -> ValTy2 H Prop PropCode
redP wfH = mkRed3 headred-refl (conv-refl (ty-Prop wfH))

Val2-Prop-to-U : {h : Nat} {H : Ctx h} {M : Expr h} -> WfCtx H ->
  (u : FinEl) -> FinMem u PropCode -> Val2 H M Prop u PropCode -> Val2 H M U u UCode
Val2-Prop-to-U wfH Bot          fm v = tt
Val2-Prop-to-U wfH UCode        ()
Val2-Prop-to-U wfH PropCode     ()
Val2-Prop-to-U wfH (FunEl g)    ()
Val2-Prop-to-U wfH (PiCode a f) fm v = mkSigma (redU wfH) (snd v)

Val2-U-to-Prop : {h : Nat} {H : Ctx h} {M : Expr h} -> WfCtx H ->
  (u : FinEl) -> FinMem u PropCode -> Val2 H M U u UCode -> Val2 H M Prop u PropCode
Val2-U-to-Prop wfH Bot          fm v = tt
Val2-U-to-Prop wfH UCode        ()
Val2-U-to-Prop wfH PropCode     ()
Val2-U-to-Prop wfH (FunEl g)    ()
Val2-U-to-Prop wfH (PiCode a f) fm v = mkSigma (redP wfH) (snd v)

EqVal2-Prop-to-U : {h : Nat} {H : Ctx h} {M N : Expr h} -> WfCtx H ->
  (u : FinEl) -> FinMem u PropCode -> EqVal2 H M N Prop u PropCode -> EqVal2 H M N U u UCode
EqVal2-Prop-to-U wfH Bot          fm v = tt
EqVal2-Prop-to-U wfH UCode        ()
EqVal2-Prop-to-U wfH PropCode     ()
EqVal2-Prop-to-U wfH (FunEl g)    ()
EqVal2-Prop-to-U wfH (PiCode a f) fm v = mkSigma (redU wfH) (snd v)

EqVal2-U-to-Prop : {h : Nat} {H : Ctx h} {M N : Expr h} -> WfCtx H ->
  (u : FinEl) -> FinMem u PropCode -> EqVal2 H M N U u UCode -> EqVal2 H M N Prop u PropCode
EqVal2-U-to-Prop wfH Bot          fm v = tt
EqVal2-U-to-Prop wfH UCode        ()
EqVal2-U-to-Prop wfH PropCode     ()
EqVal2-U-to-Prop wfH (FunEl g)    ()
EqVal2-U-to-Prop wfH (PiCode a f) fm v = mkSigma (redP wfH) (snd v)

------------------------------------------------------------------------
-- ty-Prop :  Prop : U
------------------------------------------------------------------------

valProp-PU : {h : Nat} {H : Ctx h} -> WfCtx H ->
  (u a : FinEl) -> LeCode u PropCode -> LeCode a UCode -> FinMem u a -> Val2 H Prop U u a
valProp-PU wfH u            Bot          _  _  _ = tt
valProp-PU wfH Bot          UCode        _  _  _ = tt
valProp-PU wfH PropCode     UCode        _  _  _ = mkSigma (redU wfH) (redP wfH)
valProp-PU wfH UCode        UCode        () _  _
valProp-PU wfH (FunEl _)    UCode        () _  _
valProp-PU wfH (PiCode _ _) UCode        () _  _
valProp-PU wfH u            PropCode     _  ()
valProp-PU wfH u            (FunEl _)    _  ()
valProp-PU wfH u            (PiCode _ _) _  ()

------------------------------------------------------------------------
-- Prop <= U  (ty-Prop-U, conv-Prop-U)
------------------------------------------------------------------------

adq-Prop-U : {g : Nat} {G : Ctx g} {A : Expr g} ->
  HasType G A Prop -> Adq G A Prop -> Adq G A U
adq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu Bot          evA fm = tt
adq-Prop-U {A = A} d IH sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
  let fmP = finMem-prop-mk u fm (typed-isProp A rho u (theorem1 d rho fits u hu))
  in Val2-Prop-to-U wfH u fmP (IH sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma tt tt) fmP)
adq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu PropCode     (mkSigma _ ()) fm
adq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu (FunEl _)    (mkSigma _ ()) fm
adq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm

adqconv-Prop-U : {g : Nat} {G : Ctx g} {A : Expr g} ->
  HasType G A Prop -> AdqConv G A Prop -> AdqConv G A U
adqconv-Prop-U d IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
adqconv-Prop-U {A = A} d IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA fm =
  let fmP = finMem-prop-mk u fm (typed-isProp A rho u (theorem1 d rho fits u hu))
  in EqVal2-Prop-to-U wfH u fmP
       (IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode (mkSigma tt tt) fmP)
adqconv-Prop-U d IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode     (mkSigma _ ()) fm
adqconv-Prop-U d IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _)    (mkSigma _ ()) fm
adqconv-Prop-U d IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode _ _) (mkSigma _ ()) fm

adqeq-Prop-U : {g : Nat} {G : Ctx g} {M N : Expr g} ->
  ConvTm G M N Prop -> AdqE1 G M N Prop -> AdqE1 G M N U
adqeq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
adqeq-Prop-U {M = M} d IH sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
  let fmP = finMem-prop-mk u fm (typed-isProp M rho u (theorem1 (fst (typing-ConvTm d)) rho fits u hu))
  in EqVal2-Prop-to-U wfH u fmP (IH sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma tt tt) fmP)
adqeq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu PropCode     (mkSigma _ ()) fm
adqeq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu (FunEl _)    (mkSigma _ ()) fm
adqeq-Prop-U d IH sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm

------------------------------------------------------------------------
-- U -> Prop at a Prop code  (used for ty-Pi-Prop, conv-Pi-Prop)
------------------------------------------------------------------------

adq-U-to-Prop : {g : Nat} {G : Ctx g} {T : Expr g} -> Adq G T U -> Adq G T Prop
adq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
adq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu PropCode evA fm =
  Val2-U-to-Prop wfH u fm
    (IH sigma rho crho vs fits wtsub wfH u hu UCode (mkSigma tt tt) (finMem-prop-U u fm))
adq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu UCode        (mkSigma _ ()) fm
adq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu (FunEl _)    (mkSigma _ ()) fm
adq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm

adqconv-U-to-Prop : {g : Nat} {G : Ctx g} {T : Expr g} -> AdqConv G T U -> AdqConv G T Prop
adqconv-U-to-Prop IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
adqconv-U-to-Prop IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode evA fm =
  EqVal2-U-to-Prop wfH u fm
    (IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode (mkSigma tt tt) (finMem-prop-U u fm))
adqconv-U-to-Prop IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode        (mkSigma _ ()) fm
adqconv-U-to-Prop IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _)    (mkSigma _ ()) fm
adqconv-U-to-Prop IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode _ _) (mkSigma _ ()) fm

adqeq-U-to-Prop : {g : Nat} {G : Ctx g} {M N : Expr g} -> AdqE1 G M N U -> AdqE1 G M N Prop
adqeq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
adqeq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu PropCode evA fm =
  EqVal2-U-to-Prop wfH u fm
    (IH sigma rho crho vs fits wtsub wfH u hu UCode (mkSigma tt tt) (finMem-prop-U u fm))
adqeq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu UCode        (mkSigma _ ()) fm
adqeq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu (FunEl _)    (mkSigma _ ()) fm
adqeq-U-to-Prop IH sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm

------------------------------------------------------------------------
-- The Pi-into-U statements as Adq-shaped functions (the ty-Pi / conv-Pi
-- case splits of the driver, made reusable).
------------------------------------------------------------------------

adqconv-ty-Pi-full : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqConv G A U -> AdqConv (extend G A) B U -> AdqConv G (Pi A B) U
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode    () a evA fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu Bot evA fm = tt
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode evA fm =
  adequacyV-ty-Pi d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f0 hu evA fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu PropCode     (mkSigma _ ()) fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (FunEl _)    (mkSigma _ ()) fm
adqconv-ty-Pi-full d1 d2 IH-A IH-B sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PiCode _ _) (mkSigma _ ()) fm

adqeq-conv-Pi-full : {g : Nat} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  Adq G A U -> AdqE1 G A A' U -> AdqE1 (extend G A) B B' U ->
  AdqConv (extend G A) B U -> AdqConv (extend G A) B' U ->
  AdqE1 G (Pi A B) (Pi A' B') U
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH UCode    () a evA fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH PropCode () a evA fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (PiCode b f) hu Bot evA ()
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (PiCode b f) hu UCode evA fm =
  adequacyEqSub2-Pi-core d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH b f hu evA fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (PiCode b f) hu PropCode     (mkSigma _ ()) fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (PiCode b f) hu (FunEl _)    (mkSigma _ ()) fm
adqeq-conv-Pi-full d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH (PiCode b f) hu (PiCode _ _) (mkSigma _ ()) fm

------------------------------------------------------------------------
-- conv-Prop : definitional proof irrelevance.
------------------------------------------------------------------------

adqeq-conv-Prop : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  HasType G A Prop -> HasType G M A -> AdqE1 G M N A
adqeq-conv-Prop {G = G} {M = M} {N = N} {A = A} dA dM {H = H} sigma rho crho vs fits wtsub wfH u hu a evA fm =
  S.Eq-transport (\ x -> EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) x a)
    (S.Eq-sym (proof-Bot {G = G} {M = M} {A = A} (theorem1 dM rho fits) (theorem1 dA rho fits) u hu))
    (EqVal2-Bot a)
