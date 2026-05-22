{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyBundle.agda  (MIN/ -- PROTOTYPE, phase 2)
--
-- The "bundled validity" adequacy, paper-style (Abel-Oehman-Vezzosi):
-- the fundamental theorem produces, for each judgement, BOTH the term
-- cross-equality AND the validity (two-substitution equality) of its TYPE.
--
--   AdqV2 G M A : HasType -> ... -> Pair (EqVal2 (σM)(σ'M)(σA)) (EqValTy2 (σA)(σ'A))
--   AdqE2 G M N A : ConvTm -> ... -> Pair (EqVal2 (σM)(σ'N)(σA)) (EqValTy2 (σA)(σ'A))
--
-- The type component lets the structural conversion rules (conv-sym /
-- conv-trans / conv-conv) handle GENERAL (non-U) types without touching a
-- presupposition: they read the type's two-sub out of the premise's IH.
--
-- It also requires the substitution validity to carry per-variable TYPE
-- validity (TySub) and type two-sub (TyConvSub), so ty-var can supply the
-- type component from the context.
--
-- No postulates.
------------------------------------------------------------------------

module MIN.AdequacyBundle where

open import MIN.AdequacyHeadRed
open import MIN.AdequacyVE public

import MIN.Basic as S
open S using (Nat ; zero ; suc ; tt ; Pair ; mkSigma ; fst ; snd ; FinEl ; UCode ; Bot ; FunEl ; PiCode)
open import MIN.RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; subst1 ; Fin ; fzero ; fsuc ; Sub ; liftSub ; substExpr ; wkExpr)
open import MIN.RawSemantics using (EnvApprox ; EvalRel ; CoherentEnv ; lookupEnv ; extendEnv ;
  EvalRel-Comp ; EvalRel-mon-env ; EvalRel-down ; EnvLe-refl)
open import MIN.PaperSemantics using (Coherent ; FinMem ; LeCode ; LeCode-refl ; FinMem-a-in-U ;
  finMem-bot-to ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  coh-from-aU ; FinMem-coh-u ; Comp ; Sup ; Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  finMemUCode-Sup ; finMem-upward)
open import MIN.TypingRules using (Ctx ; lookup ; HasType ; ConvTm ; WfCtx ; wf-extend ; ty-var ;
  ty-U ; ty-Pi ; ty-Lam ; ty-conv ; conv-refl ; conv-sym ; conv-conv)
open import MIN.Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode)
open import MIN.AdequacyPi using (EqVal2-U-to-EqValTy2 ; AdqConv ; Adq ; transportVal2' ;
  Val2-U-to-ValTy2 ; sup-transport-EqVal2 ; adequacy-ty-Pi)
open import MIN.Basic using (FinFun)
open import MIN.AdequacyLam using (adequacyV-ty-Lam ; lamTypeTwoSub ; adequacy-ty-Lam)
open import MIN.AdequacyApp using (adequacyV-ty-App ; adequacyV-subst1-cod ; AdSub2Rec ; AdConvSub2Rec)
open import MIN.AdequacyAppInj using (adequacyV-ty-App-inj ; adequacyV-subst1-cod-inj)
open import MIN.AdequacyArgCore using (adequacyEqSub2-App-arg ; AdEqSub2Rec)
open import MIN.AdequacyBeta using (adequacyEqSub2-beta)
open import MIN.AdequacyFunext using (adequacyEqSub2-funext)
open import MIN.AdequacyFunCore using (adequacyEqSub2-App-fun)
open import MIN.Reduction using (headred-refl)
open import MIN.SubstitutionLemma using (WtSub ; WtConvSub ; typing-ConvTm ; subst-HasType ;
  subst-ConvTm ; subst-ConvTm-cross ; liftSub-WtSub ; liftSub-WtConvSub ; ctx-conv-HasType)
open import MIN.LemmaForTS using (Fits)
open import MIN.RawSemantics using (EvalRel-coh)
open import MIN.TypingSemantics using (convSound ; convSound-inv)
open import MIN.Validity using (FinMem-Coherent)
open import MIN.EvalSubstitution using (EvalRel-unwk)
open import MIN.TypingRules using (extend)

------------------------------------------------------------------------
-- Strengthened substitution validity: per-variable TYPE validity / two-sub.
------------------------------------------------------------------------

-- NOTE the `FinMem a UCode` (= "a : U") hypothesis: per popl18 (p.23:19), a
-- reducible substitution into an extended context carries the head's
-- reducibility AT the type's reducibility proof, where the type's code is a
-- U-member BY SUPPOSITION (not derived from the raw EvalRel relation).  This
-- makes the only content-bearing case (PiCode) supplyable: ValTy2 is Top at
-- Bot/FunEl, and at UCode the membership is trivially Top.
TySub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> EnvApprox g -> Set
TySub {h} {g} H G sigma rho =
  (i : Fin g) (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem a UCode ->
  ValTy2 H (substExpr sigma (lookup G i)) a

TyConvSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> EnvApprox g -> Set
TyConvSub {h} {g} H G sigma sigma' rho =
  (i : Fin g) (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem a UCode ->
  EqValTy2 H (substExpr sigma (lookup G i)) (substExpr sigma' (lookup G i)) a

------------------------------------------------------------------------
-- The bundled fundamental-theorem statements.
------------------------------------------------------------------------

AdqV2 : {g : Nat} (G : Ctx g) (M A : Expr g) -> Set
AdqV2 {g} G M A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  TySub H G sigma rho -> TySub H G sigma' rho -> TyConvSub H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u -> (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Pair (EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a)
       (EqValTy2 H (substExpr sigma A) (substExpr sigma' A) a)

AdqE2 : {g : Nat} (G : Ctx g) (M N A : Expr g) -> Set
AdqE2 {g} G M N A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  TySub H G sigma rho -> TySub H G sigma' rho -> TyConvSub H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u -> (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Pair (EqVal2 H (substExpr sigma M) (substExpr sigma' N) (substExpr sigma A) u a)
       (EqValTy2 H (substExpr sigma A) (substExpr sigma' A) a)

------------------------------------------------------------------------
-- ty-var : both components come straight from the (strengthened) context.
------------------------------------------------------------------------

adequacyV2-var : {g : Nat} {G : Ctx g} (i : Fin g) -> AdqV2 G (Var i) (lookup G i)
adequacyV2-var i sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  mkSigma (vcs i u (fst hu) (snd hu) a evA fm) (tycs i a evA (FinMem-a-in-U u a fm))

------------------------------------------------------------------------
-- Reflexivity of the type two-sub: TySub diagonal -> TyConvSub.
------------------------------------------------------------------------

TyConvSub-refl : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g} {rho : EnvApprox g} ->
  TySub H G sigma rho -> TyConvSub H G sigma sigma rho
TyConvSub-refl tyσ i a evA aU = ValTy2-to-EqValTy2 a (tyσ i a evA aU)

------------------------------------------------------------------------
-- conv-sym (the decisive THREADING case).  d : ConvTm G N M A.
-- Built with the FIRST substitution kept = sigma in every recursive call
-- (so the type index stays sigma A and no type-transport is needed
-- between calls), reconstructing M's two-sub from same-first-sub calls.
-- No WtConvSub-sym / ValidConvSub2-sym needed -- only the refl helpers.
------------------------------------------------------------------------

adequacyE2-sym : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  ConvTm G N M A -> AdqE2 G N M A -> AdqE2 G M N A
adequacyE2-sym {G = G} {A = A} d IH-d sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  let huN  = convSound-inv d rho fits u hu        -- EvalRel N rho u
      cu   = FinMem-Coherent u a fm
      ca   = EvalRel-coh A rho a evA
      -- IH-d : AdqE2 G N M A, so IH-d s s' : EqVal2 (s N)(s' M)(s A) ...
      e-ss  = IH-d sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
                tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ (WtConvSub-refl {G = G} wtσ) wfH u huN a evA fm
      e-ss' = IH-d sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u huN a evA fm
      e-s's' = IH-d sigma' sigma' rho crho vsσ' vsσ' (ValidConvSub2-refl {G = G} vsσ')
                tyσ' tyσ' (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') fits wtσ' wtσ' (WtConvSub-refl {G = G} wtσ') wfH u huN a evA fm
      -- X : M's two-sub  (sigma M)(sigma' M)(sigma A)
      X = EqVal2-trans u a cu ca (EqVal2-sym u a cu ca (fst e-ss)) (fst e-ss')
      tyAA' = snd e-ss'                              -- EqValTy2 (sigma A)(sigma' A) a
      tyA'A = EqValTy2-sym a ca tyAA'                -- EqValTy2 (sigma' A)(sigma A) a
      -- Y : (sigma' M)(sigma' N)(sigma A)
      Y' = EqVal2-sym u a cu ca (fst e-s's')         -- (sigma' M)(sigma' N)(sigma' A)
      Y  = EqVal2-type-transport u a tyA'A Y'        -- (sigma' M)(sigma' N)(sigma A)
      val = EqVal2-trans u a cu ca X Y               -- (sigma M)(sigma' N)(sigma A)
  in mkSigma val tyAA'

------------------------------------------------------------------------
-- conv-refl : AdqV2 G M A IS (definitionally) AdqE2 G M M A.
------------------------------------------------------------------------

adequacyE2-refl : {g : Nat} {G : Ctx g} {M A : Expr g} -> AdqV2 G M A -> AdqE2 G M M A
adequacyE2-refl IH-V = IH-V

------------------------------------------------------------------------
-- conv-trans : d1 : M = N : A,  d2 : N = P : A.  Same first-sub trick:
--   (σM)(σ'P) = trans (IH-d1 σ σ' : (σM)(σ'N)) (IH-d2 σ' σ' : (σ'N)(σ'P), retyped to σA).
------------------------------------------------------------------------

adequacyE2-trans : {g : Nat} {G : Ctx g} {M N P A : Expr g} ->
  ConvTm G M N A -> AdqE2 G M N A -> AdqE2 G N P A -> AdqE2 G M P A
adequacyE2-trans {G = G} {A = A} d1 IH-d1 IH-d2 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  let huN  = convSound d1 rho fits u hu             -- EvalRel N rho u
      cu   = FinMem-Coherent u a fm
      ca   = EvalRel-coh A rho a evA
      e1   = IH-d1 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm
             -- : Pair (EqVal2 (σM)(σ'N)(σA)) (EqValTy2 (σA)(σ'A))
      tyAA' = snd e1
      tyA'A = EqValTy2-sym a ca tyAA'
      e2'  = IH-d2 sigma' sigma' rho crho vsσ' vsσ' (ValidConvSub2-refl {G = G} vsσ')
               tyσ' tyσ' (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') fits wtσ' wtσ'
               (WtConvSub-refl {G = G} wtσ') wfH u huN a evA fm
             -- : Pair (EqVal2 (σ'N)(σ'P)(σ'A)) (EqValTy2 (σ'A)(σ'A))
      e2   = EqVal2-type-transport u a tyA'A (fst e2')   -- (σ'N)(σ'P)(σA)
      val  = EqVal2-trans u a cu ca (fst e1) e2          -- (σM)(σ'P)(σA)
  in mkSigma val tyAA'

------------------------------------------------------------------------
-- AdqE2-to-AdqV2-left : the GENERAL-type analogue of AdequacyVE's
-- AdqE-to-AdqConv-left-U.  From a bundled cross IH for  M = N : A  (whose
-- output carries BOTH the term cross AND the type two-sub of A), derive the
-- LEFT endpoint M's SAME-term two-sub  EqVal2 (σM)(σ'M)(σA):
--   trans (E σ σ' : (σM)=(σ'N)@σA)
--         (type-transport (sym (E σ' σ' : (σ'M)=(σ'N)@σ'A)) : (σ'N)=(σ'M)@σA)
-- where the type-transport σ'A→σA uses the type two-sub  EqValTy2 (σA)(σ'A)
-- read out of the SAME IH (its second component).  This is what lets
-- conv-App-fun / conv-Pi obtain a CONVERSION premise's endpoint two-sub from
-- the SUBTERM cross IH, instead of from the typing presupposition.
-- The output type two-sub is unchanged (EqValTy2 (σA)(σ'A)).
------------------------------------------------------------------------

AdqE2-to-AdqV2-left : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  AdqE2 G M N A -> AdqV2 G M A
AdqE2-to-AdqV2-left {G = G} {A = A} IH-E sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  let cu = FinMem-Coherent u a fm
      ca = EvalRel-coh A rho a evA
      e-ss'  = IH-E sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm
      e-s's' = IH-E sigma' sigma' rho crho vsσ' vsσ' (ValidConvSub2-refl {G = G} vsσ')
                 tyσ' tyσ' (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') fits wtσ' wtσ'
                 (WtConvSub-refl {G = G} wtσ') wfH u hu a evA fm
      tyAA' = snd e-ss'                              -- EqValTy2 (σA)(σ'A) a
      tyA'A = EqValTy2-sym a ca tyAA'                -- EqValTy2 (σ'A)(σA) a
      Y'    = EqVal2-sym u a cu ca (fst e-s's')      -- (σ'N)(σ'M)(σ'A)
      Y     = EqVal2-type-transport u a tyA'A Y'     -- (σ'N)(σ'M)(σA)
      val   = EqVal2-trans u a cu ca (fst e-ss') Y   -- (σM)(σ'M)(σA)
  in mkSigma val tyAA'

------------------------------------------------------------------------
-- AdqE2-to-AdqV2-right : the RIGHT endpoint N's same-term two-sub from the
-- bundled cross IH for  M = N : A.  Needs the ConvTm derivation to map
-- EvalRel N rho u back to EvalRel M rho u (convSound-inv).  Keeping the FIRST
-- substitution = sigma in every IH call keeps the type index at σA, so no
-- type-transport is needed:  (σN)(σ'N) = trans (sym (E σ σ : (σM)(σN)))
--                                             (E σ σ' : (σM)(σ'N)).
------------------------------------------------------------------------

AdqE2-to-AdqV2-right : {g : Nat} {G : Ctx g} {M N A : Expr g} ->
  AdqE2 G M N A -> ConvTm G M N A -> AdqV2 G N A
AdqE2-to-AdqV2-right {G = G} {A = A} IH-E dMN sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u huN a evA fm =
  let huM = convSound-inv dMN rho fits u huN          -- EvalRel M rho u
      cu  = FinMem-Coherent u a fm
      ca  = EvalRel-coh A rho a evA
      e-ss  = IH-E sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
                tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ
                (WtConvSub-refl {G = G} wtσ) wfH u huM a evA fm   -- (σM)(σN)(σA)
      e-ss' = IH-E sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u huM a evA fm
                                                                  -- (σM)(σ'N)(σA)
      val   = EqVal2-trans u a cu ca (EqVal2-sym u a cu ca (fst e-ss)) (fst e-ss')  -- (σN)(σ'N)(σA)
  in mkSigma val (snd e-ss')

------------------------------------------------------------------------
-- Strengthened context extension (parallel to ValidSub2-extend).
-- TySub-extend: extend the per-variable TYPE validity with the new
-- variable's type validity.  TyConvSub-extend: likewise for the two-sub.
------------------------------------------------------------------------

TySub-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma : Sub h g) (t : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  TySub H G sigma rho ->
  ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> ValTy2 H (substExpr sigma A) a) ->
  TySub H (extend G A) (extSub sigma t) (extendEnv rho v)
TySub-extend {H = H} {G = G} {A = Asrc} sigma t rho v tyσ hypTy fzero a evA aU =
  let evA' = EvalRel-unwk Asrc rho v a evA
      vt   = hypTy a evA' aU
  in S.Eq-transport (\ T -> ValTy2 H T a) (S.Eq-sym (substExpr-wk sigma Asrc t)) vt
TySub-extend {H = H} {G = G} {A = Asrc} sigma t rho v tyσ hypTy (fsuc i) a evA aU =
  let evA' = EvalRel-unwk (lookup G i) rho v a evA
      vt   = tyσ i a evA' aU
  in S.Eq-transport (\ T -> ValTy2 H T a) (S.Eq-sym (substExpr-wk sigma (lookup G i) t)) vt

TyConvSub-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma sigma' : Sub h g) (t t' : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  TyConvSub H G sigma sigma' rho ->
  ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> EqValTy2 H (substExpr sigma A) (substExpr sigma' A) a) ->
  TyConvSub H (extend G A) (extSub sigma t) (extSub sigma' t') (extendEnv rho v)
TyConvSub-extend {H = H} {G = G} {A = Asrc} sigma sigma' t t' rho v tycs hypTy fzero a evA aU =
  let evA' = EvalRel-unwk Asrc rho v a evA
      eqt  = hypTy a evA' aU
  in S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma' t') (wkExpr Asrc)) a)
       (S.Eq-sym (substExpr-wk sigma Asrc t))
       (S.Eq-transport (\ T -> EqValTy2 H (substExpr sigma Asrc) T a)
         (S.Eq-sym (substExpr-wk sigma' Asrc t')) eqt)
TyConvSub-extend {H = H} {G = G} {A = Asrc} sigma sigma' t t' rho v tycs hypTy (fsuc i) a evA aU =
  let evA' = EvalRel-unwk (lookup G i) rho v a evA
      eqt  = tycs i a evA' aU
  in S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma' t') (wkExpr (lookup G i))) a)
       (S.Eq-sym (substExpr-wk sigma (lookup G i) t))
       (S.Eq-transport (\ T -> EqValTy2 H (substExpr sigma (lookup G i)) T a)
         (S.Eq-sym (substExpr-wk sigma' (lookup G i) t')) eqt)

------------------------------------------------------------------------
-- ty-U : value cross is reflexive (σU = σ'U = U); type two-sub is U≡U.
------------------------------------------------------------------------

valTyU-le : {h : Nat} {H : Ctx h} -> WfCtx H -> (a : FinEl) -> LeCode a UCode -> ValTy2 H U a
valTyU-le wfH Bot          _  = tt
valTyU-le wfH UCode          _  = mkRed3 headred-refl (conv-refl (ty-U wfH))
valTyU-le wfH (FunEl _)    ()
valTyU-le wfH (PiCode _ _)   ()

valU-UU : {h : Nat} {H : Ctx h} -> WfCtx H ->
  (u a : FinEl) -> LeCode u UCode -> LeCode a UCode -> FinMem u a -> Val2 H U U u a
valU-UU wfH u           Bot          _  _  _ = tt
valU-UU wfH Bot       UCode          _  _  _ = tt
valU-UU wfH UCode       UCode          _  _  _ =
  mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH))) (mkRed3 headred-refl (conv-refl (ty-U wfH)))
valU-UU wfH (FunEl _)  UCode         () _  _
valU-UU wfH (PiCode _ _) UCode         () _  _
valU-UU wfH u           (FunEl _)    _  ()
valU-UU wfH u           (PiCode _ _)   _  ()

adequacyV2-U : {g : Nat} {G : Ctx g} -> AdqV2 G U U
adequacyV2-U sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  mkSigma (Val2-to-EqVal2 u a (valU-UU wfH u a (snd hu) (snd evA) fm))
          (ValTy2-to-EqValTy2 a (valTyU-le wfH a (snd evA)))

------------------------------------------------------------------------
-- ty-Pi : the type is U everywhere, so the type two-sub OUTPUT is trivial
-- (valTyU-le pattern, identical to ty-U).  The VALUE cross is delegated to
-- AdequacyVE.adequacyV-ty-Pi, fed the VALUE-ONLY cross IHs (AdqConv) for
-- the domain and codomain -- which the mutual driver supplies from the
-- (total) value-only HasType-cross recursion on the SUBTERMS
-- d1, d2.  No TySub threading is needed here: the codomain edge IHs are
-- value-only.  Case structure mirrors  adequacyConvSub2 (ty-Pi ...).
------------------------------------------------------------------------

adequacyV2-ty-Pi : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqConv G A U -> AdqConv (extend G A) B U ->
  AdqV2 G (Pi A B) U
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH Bot hu a evA fm =
  mkSigma (EqVal2-Bot a) (ValTy2-to-EqValTy2 a (valTyU-le wfH a (snd evA)))
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH UCode () a evA fm
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl _) () a evA fm
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu Bot evA fm =
  mkSigma tt tt
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu (FunEl _) evA ()
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
adequacyV2-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu UCode evA fm =
  mkSigma (adequacyV-ty-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH b f0 hu evA fm)
          (ValTy2-to-EqValTy2 {M = U} UCode (valTyU-le wfH UCode (snd evA)))

------------------------------------------------------------------------
-- ty-Lam : the type is  Pi A B.  VALUE cross is delegated to
-- AdequacyLam.adequacyV-ty-Lam (fed the value-only IHs); the type-two-sub
-- OUTPUT is the Pi-type cross (lamTypeTwoSub), since Lam A M : Pi A B and the
-- Pi-type's two-sub is exactly EqValTy2 (Pi A B)[σ] (Pi A B)[σ'].  Again NO
-- TySub threading: codomain edge IHs are value-only.  Case structure mirrors
-- adequacyConvSub2 (ty-Lam ...) (term value FunEl/Bot, type value PiCode/Bot).
-- IH params: IH-A (Adq G A U, domain single, for Sup-transport),
--   IH-Lam (Adq G (Lam A M)(Pi A B), the Lam's own single-sub, both subs),
--   IH-cA / IH-cB / IH-cM (cross IHs for domain A / codomain TYPE B / body M).
------------------------------------------------------------------------

adequacyV2-ty-Lam : {g : Nat} {G : Ctx g} {A : Expr g} {B M : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U -> HasType (extend G A) M B ->
  Adq G A U -> Adq G (Lam A M) (Pi A B) ->
  AdqConv G A U -> AdqConv (extend G A) B U -> AdqConv (extend G A) M B ->
  AdqV2 G (Lam A M) (Pi A B)
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH Bot hu a evA fm =
  mkSigma (EqVal2-Bot a)
          (lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH a evA (finMem-bot-to a fm))
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH UCode () a evA fm
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode _ _) () a evA fm
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl g0) hu Bot evA fm =
  mkSigma tt tt
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl g0) hu (PiCode b f0) evA fm =
  mkSigma (adequacyV-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
             sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH g0 hu b f0 evA fm)
          (lamTypeTwoSub d1 d2 IH-cA IH-cB sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
             (PiCode b f0) evA (FinMem-a-in-U (FunEl g0) (PiCode b f0) fm))
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl g0) hu UCode () fm
adequacyV2-ty-Lam d1 d2 d3 IH-A IH-Lam IH-cA IH-cB IH-cM
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl g0) hu (FunEl _) () fm

------------------------------------------------------------------------
-- FULL single-substitution Adq wrappers for the Pi / Lam types.  The
-- closure lemmas adequacy-ty-Pi / adequacy-ty-Lam build ONLY the informative
-- value case (PiCode/UCode resp. FunEl/PiCode); these wrappers add the
-- trivial (Bot) and absurd cases so the result is a TOTAL  Adq G _ _  -- which
-- is exactly the shape the mutual driver must supply for  IH-Pi  (inside
-- adequacy-ty-Lam) and  IH-Lam  (inside adequacyV2-ty-Lam / adequacyE2-beta),
-- built from the SUBTERM IHs via the closure lemmas (NOT adequacySub2 of a
-- constructed ty-Pi / ty-Lam node).  Matrix mirrors adequacyV2-ty-Pi/Lam.
------------------------------------------------------------------------

adequacy-ty-Pi-full : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  Adq G A U -> Adq (extend G A) B U -> AdqConv (extend G A) B U ->
  Adq G (Pi A B) U
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (PiCode b f) hu Bot evA fm = tt
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (PiCode b f) hu (FunEl _) evA ()
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (PiCode b f) hu (PiCode _ _) evA ()
adequacy-ty-Pi-full d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH (PiCode b f) hu UCode evA fm =
  adequacy-ty-Pi d1 d2 IH-A IH-B IH-Bc sigma rho crho vs fits wtsub wfH b f hu evA fm

adequacy-ty-Lam-full : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B M : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U -> HasType (extend G A) M B ->
  Adq G A U -> Adq G (Pi A B) U -> Adq (extend G A) M B -> AdqConv (extend G A) M B ->
  Adq G (Lam A M) (Pi A B)
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH Bot hu a evA fm = Val2-Bot a
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH UCode () a evA fm
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu Bot evA fm = tt
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu UCode () fm
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu (FunEl _) () fm
adequacy-ty-Lam-full d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm =
  adequacy-ty-Lam d1 d2 d3 IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm

------------------------------------------------------------------------
-- ty-App : the type is  subst1 B a.  VALUE cross delegates to
-- AdequacyApp.adequacyV-ty-App (which threads the value-only recursors into
-- adequacyConvSub2-App-core-body); the type-two-sub OUTPUT is the cross of
-- the type  subst1 B a  at U, now SUPPLIED (no longer a placeholder) by
-- AdequacyApp.adequacyV-subst1-cod -- the MIN analogue of popl18 Lemma 3.20
-- (Single Substitution, equality part), built from dB+da via the extended
-- substitution.  As ty-Pi/Lam, NO TySub threading (tyσ/tyσ'/tycs unused).
--
-- The recursor parameters are H-polymorphic (AdqV2 binds H internally), and
-- App-core fundamentally needs the full single/cross recursors -- but every
-- recursor call (here and inside adequacyV-subst1-cod / App-core-body) is on a
-- subterm (A/B/f/a), so the eventual driver stays structural.
------------------------------------------------------------------------

adequacyV2-ty-App : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {f a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G f (Pi A B) -> HasType G a A ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdConvSub2Rec H2) ->
  AdqV2 G (App f a) (subst1 B a)
adequacyV2-ty-App dA dB df da adSub2 adConvSub2
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu ac evA fm =
  mkSigma (adequacyV-ty-App-inj dA dB df da adSub2
             sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
             funcross argsingle argcross u hu ac evA fm)
          (EqVal2-U-to-EqValTy2 ac acU
             (adequacyV-subst1-cod-inj dA dB da
                sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
                argsingle argsingle' argcross adConvSub2 ac evA UCode evUU acU))
  where
    acU  = FinMem-a-in-U u ac fm
    evUU = mkSigma tt (LeCode-refl UCode tt)
    funcross = \ ub ap evFb evPab fmFP ->
      adConvSub2 df sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH ub evFb ap evPab fmFP
    argsingle = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma rho crho vsσ fits wtσ wfH u0 evau b0 evAb fmb
    argsingle' = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma' rho crho vsσ' fits wtσ' wfH u0 evau b0 evAb fmb
    argcross = \ u0 b0 evau evAb fmb ->
      adConvSub2 da sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH u0 evau b0 evAb fmb

------------------------------------------------------------------------
-- ty-conv : d1 : HasType M A,  d2 : ConvTm A B U,  dB : HasType B U.
-- The conversion changes the type from A to B (both at U), so:
--   * value M's cross at type sB = its cross at sA (from IH-V1) transported
--     forward along  EqValTy2 (sA)(sB)  (read from the DIAGONAL of IH-E2 at U);
--   * the output type two-sub  EqValTy2 (sB)(s'B)  is B's value cross at U
--     (from IH-VB), since a type's value-cross-at-U IS its type two-sub.
-- A's value (in rho) coincides with B's (convSound-inv d2), so no extra eval.
-- All IHs are on the subterms d1, d2, dB.
------------------------------------------------------------------------

adequacyV2-conv : {g : Nat} {G : Ctx g} {M A B : Expr g} ->
  HasType G M A -> ConvTm G A B U -> HasType G B U ->
  AdqV2 G M A -> AdqE2 G A B U -> AdqV2 G B U -> AdqV2 G M B
adequacyV2-conv {G = G} d1 d2 dB IH-V1 IH-E2 IH-VB
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evB fm =
  let evA   = convSound-inv d2 rho fits a evB             -- EvalRel A rho a
      ca    = EvalRel-coh _ rho a evB                     -- Coherent a
      aU    = FinMem-a-in-U u a fm                        -- FinMem a UCode
      evUU  = mkSigma tt (LeCode-refl UCode tt)           -- EvalRel U rho UCode
      e1    = IH-V1 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm
      eAB   = IH-E2 sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
                tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ
                (WtConvSub-refl {G = G} wtσ) wfH a evA UCode evUU aU
      eqvtyAB = EqVal2-U-to-EqValTy2 a aU (fst eAB)        -- EqValTy2 (sA)(sB) a
      val   = EqVal2-EqValTy2-fwd u a ca eqvtyAB (fst e1)  -- EqVal2 (sM)(s'M)(sB) u a
      eB    = IH-VB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH a evB UCode evUU aU
      eqvtyBB' = EqVal2-U-to-EqValTy2 a aU (fst eB)        -- EqValTy2 (sB)(s'B) a
  in mkSigma val eqvtyBB'

------------------------------------------------------------------------
-- conv-conv : d1 : M = N : A,  d2 : A = B : U,  dB : B : U.  Identical to
-- ty-conv except the term content is the CROSS of M = N (from IH-E1, an
-- AdqE2) rather than a single term's two-sub.
------------------------------------------------------------------------

adequacyE2-conv : {g : Nat} {G : Ctx g} {M N A B : Expr g} ->
  ConvTm G M N A -> ConvTm G A B U -> HasType G B U ->
  AdqE2 G M N A -> AdqE2 G A B U -> AdqV2 G B U -> AdqE2 G M N B
adequacyE2-conv {G = G} d1 d2 dB IH-E1 IH-E2 IH-VB
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evB fm =
  let evA   = convSound-inv d2 rho fits a evB             -- EvalRel A rho a
      ca    = EvalRel-coh _ rho a evB                     -- Coherent a
      aU    = FinMem-a-in-U u a fm                        -- FinMem a UCode
      evUU  = mkSigma tt (LeCode-refl UCode tt)           -- EvalRel U rho UCode
      e1    = IH-E1 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm
      eAB   = IH-E2 sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
                tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ
                (WtConvSub-refl {G = G} wtσ) wfH a evA UCode evUU aU
      eqvtyAB = EqVal2-U-to-EqValTy2 a aU (fst eAB)        -- EqValTy2 (sA)(sB) a
      val   = EqVal2-EqValTy2-fwd u a ca eqvtyAB (fst e1)  -- EqVal2 (sM)(s'N)(sB) u a
      eB    = IH-VB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH a evB UCode evUU aU
      eqvtyBB' = EqVal2-U-to-EqValTy2 a aU (fst eB)        -- EqValTy2 (sB)(s'B) a
  in mkSigma val eqvtyBB'

------------------------------------------------------------------------
-- conv-App-arg : dA : A : U, dB : (extend G A) B : U, df : f : Pi A B,
--   daa' : a = a' : A.  Conclusion  App f a = App f a' : subst1 B a.
-- The bundled COMPOSITION recipe:
--   VALUE = trans X Y, where
--     X = App f a's same-term two-sub  EqVal2 (σ App f a)(σ' App f a)(σ subst1 B a)
--         (= adequacyV-ty-App, with a's typing the daa' presupposition),
--     Y = the single-sub conversion  App f a = App f a' @ σ', type-transported σ'→σ.
--   TYPE-two-sub = subst1 B a's cross at U (= adequacyV-subst1-cod, popl18 Lemma 3.20).
-- Recursors are H-polymorphic (AdqE2 binds H internally).  No TySub threading.
------------------------------------------------------------------------

adequacyE2-App-arg : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G f (Pi A B) -> ConvTm G a a' A ->
  AdqE2 G a a' A ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdConvSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdEqSub2Rec H2) ->
  AdqE2 G (App f a) (App f a') (subst1 B a)
adequacyE2-App-arg {G = G} {A = A} {B = B} {f = f} {a = a} {a' = a'} dA dB df daa' IH-aa' adSub2 adConvSub2 adEqSub2
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu ac evAc fm =
  mkSigma val tyBB'
  where
    da   = fst (typing-ConvTm daa')
    cu   = FinMem-Coherent u ac fm
    cac  = EvalRel-coh (subst1 B a) rho ac evAc
    acU  = FinMem-a-in-U u ac fm
    evUU = mkSigma tt (LeCode-refl UCode tt)
    -- argument's same-term two-sub: from the bundled cross IH on the SUBTERM daa'
    argV2 = AdqE2-to-AdqV2-left {G = G} {M = a} {N = a'} {A = A} IH-aa'
    funcross = \ ub ap evFb evPab fmFP ->
      adConvSub2 df sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH ub evFb ap evPab fmFP
    argsingle = \ u0 b0 evau evAb fmb -> Val2-from-EqVal2-first u0 b0
      (fst (argV2 sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
              tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ
              (WtConvSub-refl {G = G} wtσ) wfH u0 evau b0 evAb fmb))
    argsingle' = \ u0 b0 evau evAb fmb -> Val2-from-EqVal2-first u0 b0
      (fst (argV2 sigma' sigma' rho crho vsσ' vsσ' (ValidConvSub2-refl {G = G} vsσ')
              tyσ' tyσ' (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') fits wtσ' wtσ'
              (WtConvSub-refl {G = G} wtσ') wfH u0 evau b0 evAb fmb))
    argcross = \ u0 b0 evau evAb fmb ->
      fst (argV2 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u0 evau b0 evAb fmb)
    X    = adequacyV-ty-App-inj dA dB df da adSub2
             sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
             funcross argsingle argcross u hu ac evAc fm
    tyBB' = EqVal2-U-to-EqValTy2 ac acU
              (adequacyV-subst1-cod-inj dA dB da
                 sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
                 argsingle argsingle' argcross adConvSub2 ac evAc UCode evUU acU)
    tyB'B = EqValTy2-sym ac cac tyBB'
    Yraw = adequacyEqSub2-App-arg dB df daa' sigma' rho crho vsσ' fits wtσ' wfH
             (\ {h2} {H2} -> adSub2 {h2} {H2} df) (\ {h2} {H2} -> adSub2 {h2} {H2} dB) (\ {h2} {H2} -> adEqSub2 {h2} {H2} daa')
             u hu ac evAc fm
    Y    = EqVal2-type-transport u ac tyB'B Yraw
    val  = EqVal2-trans u ac cu cac X Y

------------------------------------------------------------------------
-- conv-beta : dA : A : U, dB : (extend G A) B : U, dM : (extend G A) M : B,
--   da : a : A.  Conclusion  App (Lam A M) a = subst1 M a : subst1 B a.
-- Same COMPOSITION recipe as conv-App-arg:
--   VALUE = trans X Y,
--     X = App (Lam A M) a's same-term two-sub (= adequacyV-ty-App with the
--         function-typing  ty-Lam dA dB dM, all data from subterms),
--     Y = beta single-sub @ σ', type-transported σ'→σ.
--   TYPE-two-sub = subst1 B a's cross at U (= adequacyV-subst1-cod).
------------------------------------------------------------------------

adequacyE2-beta : {g : Nat} {G : Ctx g} {A : Expr g} {B M : Expr (suc g)} {a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> HasType (extend G A) M B -> HasType G a A ->
  Adq G A U -> Adq G (Lam A M) (Pi A B) ->
  AdqConv G A U -> AdqConv (extend G A) B U -> AdqConv (extend G A) M B ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdConvSub2Rec H2) ->
  AdqE2 G (App (Lam A M) a) (subst1 M a) (subst1 B a)
adequacyE2-beta {A = A} {B = B} {M = M} {a = a} dA dB dM da IH-A IH-Lam IH-cA IH-cB IH-cM adSub2 adConvSub2
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu ac evAc fm =
  mkSigma val tyBB'
  where
    cu   = FinMem-Coherent u ac fm
    cac  = EvalRel-coh (subst1 B a) rho ac evAc
    acU  = FinMem-a-in-U u ac fm
    evUU = mkSigma tt (LeCode-refl UCode tt)
    -- function (Lam A M)'s cross: from the bundled ty-Lam combinator (closure
    -- lemma on the SUBTERMS dA,dB,dM via the Lam validity IHs); handles the
    -- full (ub, ap) value matrix and projects the value component.
    funcross = \ ub ap evLam evPi fmFP -> fst (adequacyV2-ty-Lam dA dB dM IH-A IH-Lam IH-cA IH-cB IH-cM
      sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH ub evLam ap evPi fmFP)
    argsingle = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma rho crho vsσ fits wtσ wfH u0 evau b0 evAb fmb
    argsingle' = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma' rho crho vsσ' fits wtσ' wfH u0 evau b0 evAb fmb
    argcross = \ u0 b0 evau evAb fmb ->
      adConvSub2 da sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH u0 evau b0 evAb fmb
    X    = adequacyV-ty-App-inj dA dB (ty-Lam dA dB dM) da adSub2
             sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
             funcross argsingle argcross u hu ac evAc fm
    tyBB' = EqVal2-U-to-EqValTy2 ac acU
              (adequacyV-subst1-cod-inj dA dB da
                 sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
                 argsingle argsingle' argcross adConvSub2 ac evAc UCode evUU acU)
    tyB'B = EqValTy2-sym ac cac tyBB'
    Yraw = adequacyEqSub2-beta dA dB dM da (\ {h2} {H2} -> adSub2 {h2} {H2} dM) (\ {h2} {H2} -> adSub2 {h2} {H2} da)
             sigma' rho crho vsσ' fits wtσ' wfH u hu ac evAc fm
    Y    = EqVal2-type-transport u ac tyB'B Yraw
    val  = EqVal2-trans u ac cu cac X Y

------------------------------------------------------------------------
-- conv-funext : dA : A : U, d : (App (wk f) v0) = (App (wk g') v0) : B over
--   (extend G A), df : f : Pi A B, dg : g' : Pi A B.  Conclusion  f = g' : Pi A B.
-- COMPOSITION recipe with the type now = Pi A B:
--   VALUE = trans X Y,
--     X = f's same-term two-sub  EqVal2 (σf)(σ'f)(σ Pi A B)  (= IH-cf, f a subterm),
--     Y = funext single-sub @ σ', type-transported σ'→σ.
--   TYPE-two-sub = the Pi A B cross  EqValTy2 (σ Pi A B)(σ' Pi A B)  (= lamTypeTwoSub,
--     from dA's and B's crosses).  IH-A for the single-sub core = V-to-diag IH-cA.
------------------------------------------------------------------------

-- The type-two-sub is the Pi A B same-term two-sub  EqValTy2 (σ Pi A B)(σ' Pi A B);
-- since the funext type IS Pi A B and f : Pi A B, this is EXACTLY the type-two-sub
-- component of f's BUNDLED validity  BVf : AdqV2 G f (Pi A B)  (snd of its output),
-- and the value part X = f's same-term two-sub is its fst.  So no value-only
-- adequacyV-ty-Pi / lamTypeTwoSub / Pi-validity-inversion is needed: the codomain
-- type's validity comes from f's typing premise's validity (popl18 Property 7 / FT
-- 3.21).  BVf is the driver's  adequacyV2 df  on the SUBTERM df.
adequacyE2-funext : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
  HasType G A U ->
  ConvTm (extend G A) (App (wkExpr f) (Var fzero)) (App (wkExpr g') (Var fzero)) B ->
  HasType G f (Pi A B) -> HasType G g' (Pi A B) ->
  AdqV2 G f (Pi A B) -> AdqConv G A U ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdEqSub2Rec H2) ->
  AdqE2 G f g' (Pi A B)
adequacyE2-funext {A = A} {B = B} {f = f} {g' = g'} dA d df dg BVf IH-cA adSub2 adEqSub2
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm =
  mkSigma val tyPiPi'
  where
    ca   = EvalRel-coh (Pi A B) rho a evA
    cu   = FinMem-Coherent u a fm
    bvf  = BVf sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu a evA fm
    X    = fst bvf                                 -- EqVal2 (σf)(σ'f)(σ Pi A B) u a
    tyPiPi' = snd bvf                              -- EqValTy2 (σ Pi A B)(σ' Pi A B) a
    tyPi'Pi = EqValTy2-sym a ca tyPiPi'
    Yraw = adequacyEqSub2-funext dA d df dg sigma' rho crho vsσ' fits wtσ' wfH
             (\ {h2} {H2} -> adSub2 {h2} {H2} df) (\ {h2} {H2} -> adSub2 {h2} {H2} dg) (\ {h2} {H2} -> adEqSub2 {h2} {H2} d)
             (V-to-diag {M = A} {A = U} IH-cA) u hu a evA fm
    Y    = EqVal2-type-transport u a tyPi'Pi Yraw
    val  = EqVal2-trans u a cu ca X Y

------------------------------------------------------------------------
-- conv-App-fun : dA : A : U, dB : (extend G A) B : U, dff' : f = f' : Pi A B,
--   da : a : A.  Conclusion  App f a = App f' a : subst1 B a.
-- Structurally the MIRROR of conv-App-arg (function varies, argument fixed):
--   VALUE = trans X Y,
--     X = App f a's same-term two-sub (= adequacyV-ty-App; here f's typing is
--         the dff' presupposition fst (typing-ConvTm dff') -- the driver-faithful
--         route obtains f's two-sub from the SUBTERM cross IH via the general
--         AdqE2-to-AdqV2-left helper, avoiding the presupposition recursion),
--     Y = App-fun single-sub @ σ', type-transported σ'→σ.
--   TYPE-two-sub = subst1 B a's cross at U (= adequacyV-subst1-cod).
------------------------------------------------------------------------

adequacyE2-App-fun : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
  HasType G A U -> HasType (extend G A) B U -> ConvTm G f f' (Pi A B) -> HasType G a A ->
  AdqE2 G f f' (Pi A B) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdConvSub2Rec H2) ->
  ({h2 : Nat} {H2 : Ctx h2} -> AdEqSub2Rec H2) ->
  AdqE2 G (App f a) (App f' a) (subst1 B a)
adequacyE2-App-fun {G = G} {A = A} {B = B} {f = f} {f' = f'} {a = a} dA dB dff' da IH-ff' adSub2 adConvSub2 adEqSub2
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH u hu ac evAc fm =
  mkSigma val tyBB'
  where
    df   = fst (typing-ConvTm dff')
    cu   = FinMem-Coherent u ac fm
    cac  = EvalRel-coh (subst1 B a) rho ac evAc
    acU  = FinMem-a-in-U u ac fm
    evUU = mkSigma tt (LeCode-refl UCode tt)
    -- function f's same-term two-sub: from the bundled cross IH on the SUBTERM dff'
    funV2 = AdqE2-to-AdqV2-left {G = G} {M = f} {N = f'} {A = Pi A B} IH-ff'
    funcross = \ ub ap evFb evPab fmFP ->
      fst (funV2 sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH ub evFb ap evPab fmFP)
    argsingle = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma rho crho vsσ fits wtσ wfH u0 evau b0 evAb fmb
    argsingle' = \ u0 b0 evau evAb fmb ->
      adSub2 da sigma' rho crho vsσ' fits wtσ' wfH u0 evau b0 evAb fmb
    argcross = \ u0 b0 evau evAb fmb ->
      adConvSub2 da sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH u0 evau b0 evAb fmb
    X    = adequacyV-ty-App-inj dA dB df da adSub2
             sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
             funcross argsingle argcross u hu ac evAc fm
    tyBB' = EqVal2-U-to-EqValTy2 ac acU
              (adequacyV-subst1-cod-inj dA dB da
                 sigma sigma' rho crho vsσ vsσ' vcs fits wtσ wtσ' wtcs wfH
                 argsingle argsingle' argcross adConvSub2 ac evAc UCode evUU acU)
    tyB'B = EqValTy2-sym ac cac tyBB'
    Yraw = adequacyEqSub2-App-fun dB dff' da sigma' rho crho vsσ' fits wtσ' wfH
             (\ {h2} {H2} -> adSub2 {h2} {H2} da) (\ {h2} {H2} -> adSub2 {h2} {H2} dB) (\ {h2} {H2} -> adEqSub2 {h2} {H2} dff')
             u hu ac evAc fm
    Y    = EqVal2-type-transport u ac tyB'B Yraw
    val  = EqVal2-trans u ac cu cac X Y

------------------------------------------------------------------------
-- transportEqVal2-tyval : the Sup-transport along the domain, taking the
-- type's validity-at-σ DIRECTLY (with the `c : U` supposition) instead of a
-- value-only Adq G A U.  This is the specialisation of AdequacyPi.transportEqVal2'
-- that the bundled conv-Pi needs (the domain IH is now bundled AdqE2, from
-- which only the type-validity-at-σ is projected, not a full Adq at all subs).
------------------------------------------------------------------------

transportEqVal2-tyval : {h g : Nat} {H : Ctx h} {A : Expr g} {N1 N2 : Expr h}
  (sigma : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ((c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> ValTy2 H (substExpr sigma A) c) ->
  (b : FinEl) -> FinMem b UCode -> EvalRel A rho b ->
  (u0 : FinEl) -> FinMem u0 b ->
  EqVal2 H N1 N2 (substExpr sigma A) u0 b ->
  (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
  (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
  EqVal2 H N1 N2 (substExpr sigma A) u' a_arg
transportEqVal2-tyval {A = A} sigma rho crho tyvalA b bU evAb u0 fm_u0_b eqN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
  let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
      a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
      vtA_b    = tyvalA b evAb bU
      vtA_a    = tyvalA a_arg evA_arg a_argU
  in sup-transport-EqVal2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN

------------------------------------------------------------------------
-- convPi2 : the bundled (driver-ready) SINGLE-substitution conv-Pi, the "Y"
-- of the conv-Pi composition.  Faithful re-do of AdequacyVE.convPi-single,
-- BUT the two ConvTm-cross IHs are now the BUNDLED AdqE2 (= popl18's valid
-- equality `Γ ⊩ᵛ A = A'`/`Γ,A ⊩ᵛ B = B'`, total), and a TySub `tyσ` for the
-- ambient context is threaded -- the codomain edges build TySub-extend /
-- TyConvSub-extend (from tyσ + A's type-validity at σ, projected from IH-E-A's
-- diagonal) so the bundled codomain IH can be applied at the extended subs.
-- The domain endpoint two-subs come from AdqE2-to-AdqV2-left / -right; the
-- domain type-validity (for transport / TySub-extend) is A-tyval.
------------------------------------------------------------------------

convPi2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  AdqE2 G A A' U -> AdqE2 (extend G A) B B' U ->
  (sigma : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> TySub H G sigma rho -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) -> EvalRel U rho UCode -> FinMem (PiCode b f) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma (Pi A' B')) U (PiCode b f) UCode
convPi2 {h = h} {g = g} {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 IH-E-A IH-E-B sigma rho crho vs fits wtsub tyσ wfH b f hu evU fm =
  mkSigma valTyU (mkSigma valTyPiAB (mkSigma valTyPiA'B' eqValTyPi))
  where
    sA   = substExpr sigma A
    sA'  = substExpr sigma A'
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma) B'
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evUU = mkSigma tt (LeCode-refl UCode tt)
    evAb = fst (snd hu)
    a'pi = fst (snd (snd hu))
    bodyPi = snd (snd (snd (snd hu)))

    valTyU : ValTy2 H U UCode
    valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))

    IA-diag : (u : FinEl) -> EvalRel A rho u -> (a : FinEl) -> EvalRel U rho a -> FinMem u a ->
      EqVal2 H sA sA' (substExpr sigma U) u a
    IA-diag u hu0 a evA fm0 =
      fst (IH-E-A sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs)
             tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtsub wtsub
             (WtConvSub-refl {G = G} wtsub) wfH u hu0 a evA fm0)

    A-tyval : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> ValTy2 H sA c
    A-tyval c evAc cU = Val2-U-to-ValTy2 c cU (Val2-from-EqVal2-first c UCode (IA-diag c evAc UCode evUU cU))

    A-eqtyval : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqValTy2 H sA sA c
    A-eqtyval c evAc cU = ValTy2-to-EqValTy2 c (A-tyval c evAc cU)

    eqD1 = IA-diag b evAb UCode evUU bU
    valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
    valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
    eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
    eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

    trVal : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr h) -> Val2 H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val2 H N sA u' a_arg
    trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                       (IA-diag a_arg evA_arg UCode evUU a_argU)
          vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
          val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3

    tyExtB : (N : Expr h) (u0 : FinEl) -> TySub H (extend G A) (extSub sigma N) (extendEnv rho u0)
    tyExtB N u0 = TySub-extend {A = A} sigma N rho u0 tyσ A-tyval

    tyConvExtB : (N1 N2 : Expr h) (u0 : FinEl) ->
      TyConvSub H (extend G A) (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
    tyConvExtB N1 N2 u0 =
      TyConvSub-extend {A = A} sigma sigma N1 N2 rho u0 (TyConvSub-refl {G = G} {sigma = sigma} tyσ) A-eqtyval

    buildEdgeValB2 : PiEdgeVal2 H sA sB b f
    buildEdgeValB2 u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
          ih       = fst (IH-E-B (extSub sigma N) (extSub sigma N) (extendEnv rho u0)
                       crho' vs' vs' (ValidConvSub2-refl {G = extend G A} vs')
                       (tyExtB N u0) (tyExtB N u0)
                       (TyConvSub-refl {G = extend G A} {sigma = extSub sigma N} (tyExtB N u0))
                       fits' wtsub' wtsub' (WtConvSub-refl {G = extend G A} wtsub') wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U)
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
           (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

    buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
    buildEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2-tyval sigma rho crho A-tyval b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
          raw      = fst ((AdqE2-to-AdqV2-left {M = B} {N = B'} {A = U} IH-E-B) (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext (tyExtB N1 u0) (tyExtB N2 u0) (tyConvExtB N1 N2 u0)
                       fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH v0 evB_u0_v0 UCode evUU fm_v0_U)
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
    buildEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
      let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
          ih       = fst (IH-E-B (extSub sigma N) (extSub sigma N) (extendEnv rho u0)
                       crho' vs' vs' (ValidConvSub2-refl {G = extend G A} vs')
                       (tyExtB N u0) (tyExtB N u0)
                       (TyConvSub-refl {G = extend G A} {sigma = extSub sigma N} (tyExtB N u0))
                       fits' wtsub' wtsub' (WtConvSub-refl {G = extend G A} wtsub') wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U)
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
           (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

    buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
    buildEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          htA_loc  = subst-HasType wtsub wfH dA_conv
          convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
          htN1_A   = ty-conv htN1_A' convA'A htA_loc
          htN2_A   = ty-conv htN2_A' convA'A htA_loc
          cvN_A    = conv-conv cvN_A' convA'A htA_loc
          eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
          valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
          valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
          evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2-tyval sigma rho crho A-tyval b bU evAb u0 fm_u0_b eqvalN_A)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
          raw      = fst ((AdqE2-to-AdqV2-right {M = B} {N = B'} {A = U} IH-E-B d2) (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext (tyExtB N1 u0) (tyExtB N2 u0) (tyConvExtB N1 N2 u0)
                       fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH v0 evB'_u0_v0 UCode evUU fm_v0_U)
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
    buildEdgeEqTyBB'2 u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
          ih       = fst (IH-E-B (extSub sigma P) (extSub sigma P) (extendEnv rho u0)
                       crho' vs' vs' (ValidConvSub2-refl {G = extend G A} vs')
                       (tyExtB P u0) (tyExtB P u0)
                       (TyConvSub-refl {G = extend G A} {sigma = extSub sigma P} (tyExtB P u0))
                       fits' wtsub' wtsub' (WtConvSub-refl {G = extend G A} wtsub') wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U)
          eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                       (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                         (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
      in eqvt

    htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
    htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

    valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
    valTyPiAB = mk-ValTyPi (record
      { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; cohF = cf ; fmAllU = allU ; htA = htA_AB ; htB = htB_AB
      ; valA = valTyA ; edgeV = buildEdgeValB2 ; edgeE = buildEdgeEqB2 })

    htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
    htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
    htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

    valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
    valTyPiA'B' = mk-ValTyPi (record
      { domA = sA' ; codB = sB' ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU ; htA = htA_A'B' ; htB = htB_A'B'
      ; valA = valTyA' ; edgeV = buildEdgeValB'2 ; edgeE = buildEdgeEqB'2 })

    convA_sub  = subst-ConvTm wtsub wfH d1
    convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

    eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
    eqValTyPi = mk-EqValTyPi valTyPiAB valTyPiA'B' (record
      { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
      ; redM = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU
      ; convA = convA_sub ; convB = convB_sub
      ; eqA = eqValTyAA' ; edgeET = buildEdgeEqTyBB'2 })

------------------------------------------------------------------------
-- piTwoSub2 : the Π SAME-TERM two-substitution  (Pi A B)[σ] = (Pi A B)[σ'],
-- built from the BUNDLED domain/codomain validities  BVA : AdqV2 G A U  and
-- BVB : AdqV2 (extend G A) B U  (which conv-Pi obtains from the bundled
-- conversion IHs via AdqE2-to-AdqV2-left, on the SUBTERMS).  This is the
-- bundled, driver-ready replacement for the value-only X-part adequacyV-ty-Pi:
-- the codomain validity BVB is applied at the EXTENDED reducible substitutions
-- (extSub σ P)/(extSub σ' P), with TySub-extend threaded from the domain's
-- type validity A-tyval (popl18 §3.4: the extended reducible sub carries the
-- domain's type reducibility).  Same term A,B on both sides ⇒ NO A→A' retyping.
-- dA/dB are used ONLY for syntactic typing fields (subst-HasType/conv-refl/
-- ty-Pi), never an adequacy recursor.
------------------------------------------------------------------------

piTwoSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqV2 G A U -> AdqV2 (extend G A) B U ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho -> ValidConvSub2 H G sigma sigma' rho ->
  TySub H G sigma rho -> TySub H G sigma' rho -> TyConvSub H G sigma sigma' rho ->
  Fits G rho -> WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) -> EvalRel U rho UCode -> FinMem (PiCode b f) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma' (Pi A B)) U (PiCode b f) UCode
piTwoSub2 {h = h} {g = g} {H = H} {G = G} {A = A} {B = B}
    dA dB BVA BVB sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH b f hu evU fm =
  mkSigma valTyU (mkSigma valTyPiL (mkSigma valTyPiR eqValTyPi))
  where
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    tA   = substExpr sigma' A
    tB   = substExpr (liftSub sigma') B
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evUU = mkSigma tt (LeCode-refl UCode tt)
    evAb = fst (snd hu)
    a'pi = fst (snd (snd hu))
    bodyPi = snd (snd (snd (snd hu)))

    valTyU : ValTy2 H U UCode
    valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))

    -- domain A's data from BVA: σ-diagonal, σ'-diagonal, and the (σ,σ') cross.
    Aval-σ : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqVal2 H sA sA U c UCode
    Aval-σ c evAc cU = fst (BVA sigma sigma rho crho vsσ vsσ (ValidConvSub2-refl {G = G} vsσ)
      tyσ tyσ (TyConvSub-refl {G = G} {sigma = sigma} tyσ) fits wtσ wtσ (WtConvSub-refl {G = G} wtσ) wfH c evAc UCode evUU cU)
    Aval-σ' : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqVal2 H tA tA U c UCode
    Aval-σ' c evAc cU = fst (BVA sigma' sigma' rho crho vsσ' vsσ' (ValidConvSub2-refl {G = G} vsσ')
      tyσ' tyσ' (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') fits wtσ' wtσ' (WtConvSub-refl {G = G} wtσ') wfH c evAc UCode evUU cU)
    Across : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqVal2 H sA tA U c UCode
    Across c evAc cU = fst (BVA sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH c evAc UCode evUU cU)

    A-tyval-σ : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> ValTy2 H sA c
    A-tyval-σ c evAc cU = Val2-U-to-ValTy2 c cU (Val2-from-EqVal2-first c UCode (Aval-σ c evAc cU))
    A-tyval-σ' : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> ValTy2 H tA c
    A-tyval-σ' c evAc cU = Val2-U-to-ValTy2 c cU (Val2-from-EqVal2-first c UCode (Aval-σ' c evAc cU))
    A-eqtyval-σ : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqValTy2 H sA sA c
    A-eqtyval-σ c evAc cU = ValTy2-to-EqValTy2 c (A-tyval-σ c evAc cU)
    A-eqtyval-σ' : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqValTy2 H tA tA c
    A-eqtyval-σ' c evAc cU = ValTy2-to-EqValTy2 c (A-tyval-σ' c evAc cU)
    A-cross-eqty : (c : FinEl) -> EvalRel A rho c -> FinMem c UCode -> EqValTy2 H sA tA c
    A-cross-eqty c evAc cU = EqVal2-U-to-EqValTy2 c cU (Across c evAc cU)

    valTyA-σ  = A-tyval-σ b evAb bU
    valTyA-σ' = A-tyval-σ' b evAb bU
    eqValTyAtA = A-cross-eqty b evAb bU            -- EqValTy2 sA tA b
    eqValTytAA = EqValTy2-sym b cb eqValTyAtA      -- EqValTy2 tA sA b

    -- Sup-transport of a Val2 N along the domain at σ (resp. σ').
    trVal-σ : (u0 : FinEl) -> FinMem u0 b -> (N : Expr h) -> Val2 H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg -> Val2 H N sA u' a_arg
    trVal-σ u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          vtA_a    = A-tyval-σ a_arg evA_arg a_argU
          vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA-σ vtA_a
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
          val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3
    trVal-σ' : (u0 : FinEl) -> FinMem u0 b -> (N : Expr h) -> Val2 H N tA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg -> Val2 H N tA u' a_arg
    trVal-σ' u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          vtA_a    = A-tyval-σ' a_arg evA_arg a_argU
          vtA_sup  = ValTy2-Sup H tA b a_arg comp_b_a bU a_argU valTyA-σ' vtA_a
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          val1     = upVal2 H N tA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
          val2     = restrictVal2 H N tA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal2 H N tA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3

    tyExtB-σ : (N : Expr h) (u0 : FinEl) -> TySub H (extend G A) (extSub sigma N) (extendEnv rho u0)
    tyExtB-σ N u0 = TySub-extend {A = A} sigma N rho u0 tyσ A-tyval-σ
    tyExtB-σ' : (N : Expr h) (u0 : FinEl) -> TySub H (extend G A) (extSub sigma' N) (extendEnv rho u0)
    tyExtB-σ' N u0 = TySub-extend {A = A} sigma' N rho u0 tyσ' A-tyval-σ'
    tyConvExtB-σ : (N1 N2 : Expr h) (u0 : FinEl) ->
      TyConvSub H (extend G A) (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
    tyConvExtB-σ N1 N2 u0 =
      TyConvSub-extend {A = A} sigma sigma N1 N2 rho u0 (TyConvSub-refl {G = G} {sigma = sigma} tyσ) A-eqtyval-σ
    tyConvExtB-σ' : (N1 N2 : Expr h) (u0 : FinEl) ->
      TyConvSub H (extend G A) (extSub sigma' N1) (extSub sigma' N2) (extendEnv rho u0)
    tyConvExtB-σ' N1 N2 u0 =
      TyConvSub-extend {A = A} sigma' sigma' N1 N2 rho u0 (TyConvSub-refl {G = G} {sigma = sigma'} tyσ') A-eqtyval-σ'
    tyConvExtB-cross : (N1 N2 : Expr h) (u0 : FinEl) ->
      TyConvSub H (extend G A) (extSub sigma N1) (extSub sigma' N2) (extendEnv rho u0)
    tyConvExtB-cross N1 N2 u0 =
      TyConvSub-extend {A = A} sigma sigma' N1 N2 rho u0 tycs A-cross-eqty

    buildEdgeVal-σ : PiEdgeVal2 H sA sB b f
    buildEdgeVal-σ u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vsσ hyp0
          wtsub'   = extSub-WtSub wtσ wfH dA htN
          ih       = fst (BVB (extSub sigma N) (extSub sigma N) (extendEnv rho u0)
                       crho' vs' vs' (ValidConvSub2-refl {G = extend G A} vs')
                       (tyExtB-σ N u0) (tyExtB-σ N u0)
                       (TyConvSub-refl {G = extend G A} {sigma = extSub sigma N} (tyExtB-σ N u0))
                       fits' wtsub' wtsub' (WtConvSub-refl {G = extend G A} wtsub') wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U)
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
           (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

    buildEdgeEq-σ : PiEdgeEq2 H sA sB b f
    buildEdgeEq-σ u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vsσ hyp0_N1
          wtsub'_N1 = extSub-WtSub wtσ wfH dA htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vsσ hyp0_N2
          wtsub'_N2 = extSub-WtSub wtσ wfH dA htN2
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vsσ)
                       (transportEqVal2-tyval sigma rho crho A-tyval-σ b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtσ (WtConvSub-refl {G = G} wtσ) wfH dA cvN
          raw      = fst (BVB (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext (tyExtB-σ N1 u0) (tyExtB-σ N2 u0) (tyConvExtB-σ N1 N2 u0)
                       fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH v0 evB_u0_v0 UCode evUU fm_v0_U)
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeVal-σ' : PiEdgeVal2 H tA tB b f
    buildEdgeVal-σ' u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ' u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma' N rho u0 vsσ' hyp0
          wtsub'   = extSub-WtSub wtσ' wfH dA htN
          ih       = fst (BVB (extSub sigma' N) (extSub sigma' N) (extendEnv rho u0)
                       crho' vs' vs' (ValidConvSub2-refl {G = extend G A} vs')
                       (tyExtB-σ' N u0) (tyExtB-σ' N u0)
                       (TyConvSub-refl {G = extend G A} {sigma = extSub sigma' N} (tyExtB-σ' N u0))
                       fits' wtsub' wtsub' (WtConvSub-refl {G = extend G A} wtsub') wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U)
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma' B N))
           (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

    buildEdgeEq-σ' : PiEdgeEq2 H tA tB b f
    buildEdgeEq-σ' u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ' u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma' N1 rho u0 vsσ' hyp0_N1
          wtsub'_N1 = extSub-WtSub wtσ' wfH dA htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ' u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma' N2 rho u0 vsσ' hyp0_N2
          wtsub'_N2 = extSub-WtSub wtσ' wfH dA htN2
          vcs_ext  = ValidConvSub2-extend sigma' sigma' N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vsσ')
                       (transportEqVal2-tyval sigma' rho crho A-tyval-σ' b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtσ' (WtConvSub-refl {G = G} wtσ') wfH dA cvN
          raw      = fst (BVB (extSub sigma' N1) (extSub sigma' N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext (tyExtB-σ' N1 u0) (tyExtB-σ' N2 u0) (tyConvExtB-σ' N1 N2 u0)
                       fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH v0 evB_u0_v0 UCode evUU fm_v0_U)
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 tB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma' B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma' B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    -- the CROSS codomain type-edge: B[extSub σ P] = B[extSub σ' P] at v0.
    buildEdgeCrossTy : PiEdgeEqTy2 H sA sB tB b f
    buildEdgeCrossTy u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          convA-cross = subst-ConvTm-cross dA wtσ wtσ' wtcs wfH        -- ConvTm H sA tA U
          htP-σ'   = ty-conv htP convA-cross (subst-HasType wtσ' wfH dA)  -- HasType H P tA
          valP-σ'  = Val2-EqValTy2-fwd u0 b cb eqValTyAtA valP            -- Val2 H P tA u0 b
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma P rho u0 vsσ hyp0
          hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a -> trVal-σ' u0 fm_u0_b P valP-σ' u' cu' le_u' a_arg evA_arg fm_u'_a
          vs''     = ValidSub2-extend sigma' P rho u0 vsσ' hyp0'
          vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs
                       (transportEqVal2-tyval sigma rho crho A-tyval-σ b bU evAb u0 fm_u0_b
                         (Val2-to-EqVal2 u0 b valP))
          wtsub-P  = extSub-WtSub wtσ wfH dA htP
          wtsub'-P = extSub-WtSub wtσ' wfH dA htP-σ'
          wcs-cross = extSub-WtConvSub wtσ wtcs wfH dA (conv-refl htP)
          raw      = fst (BVB (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                       crho' vs' vs'' vcs_ext (tyExtB-σ P u0) (tyExtB-σ' P u0) (tyConvExtB-cross P P u0)
                       fits' wtsub-P wtsub'-P wcs-cross wfH v0 evB_u0_v0 UCode evUU fm_v0_U)
          eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma' B P))
                       (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma' P) B) v0) (S.Eq-sym (substExpr-comp sigma B P))
                         (EqVal2-U-to-EqValTy2 v0 fm_v0_U raw))
      in eqvt

    htA-σ  = subst-HasType wtσ wfH dA
    htB-σ  = subst-HasType (liftSub-WtSub wtσ wfH dA) (wf-extend htA-σ) dB
    htA-σ' = subst-HasType wtσ' wfH dA
    htB-σ' = subst-HasType (liftSub-WtSub wtσ' wfH dA) (wf-extend htA-σ') dB

    valTyPiL : ValTy2 H (Pi sA sB) (PiCode b f)
    valTyPiL = mk-ValTyPi (record
      { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA-σ htB-σ))
      ; cohF = cf ; fmAllU = allU ; htA = htA-σ ; htB = htB-σ
      ; valA = valTyA-σ ; edgeV = buildEdgeVal-σ ; edgeE = buildEdgeEq-σ })

    valTyPiR : ValTy2 H (Pi tA tB) (PiCode b f)
    valTyPiR = mk-ValTyPi (record
      { domA = tA ; codB = tB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA-σ' htB-σ'))
      ; cohF = cf ; fmAllU = allU ; htA = htA-σ' ; htB = htB-σ'
      ; valA = valTyA-σ' ; edgeV = buildEdgeVal-σ' ; edgeE = buildEdgeEq-σ' })

    -- the cross conversion fields: convA = ConvTm sA tA U (same term A, two
    -- subs); convB = ConvTm sB tB U over extend H sA, with the σ' codomain
    -- lift RETYPED into the σ-domain context via convA (as adequacyV-ty-Pi).
    convA-cross-fld = subst-ConvTm-cross dA wtσ wtσ' wtcs wfH
    wtsubB-σ      = liftSub-WtSub wtσ wfH dA
    wtsubB-σ'-raw = liftSub-WtSub wtσ' wfH dA
    wtsubB-σ' : WtSub (extend H sA) (extend G A) (liftSub sigma')
    wtsubB-σ' = \ i -> ctx-conv-HasType htA-σ' htA-σ (conv-sym convA-cross-fld) (wtsubB-σ'-raw i)
    wcsB-lift     = liftSub-WtConvSub wtσ wtcs wfH dA
    convB-cross-fld = subst-ConvTm-cross dB wtsubB-σ wtsubB-σ' wcsB-lift (wf-extend htA-σ)

    eqValTyPi : EqValTy2 H (Pi sA sB) (Pi tA tB) (PiCode b f)
    eqValTyPi = mk-EqValTyPi valTyPiL valTyPiR (record
      { domA = sA ; codB = sB ; domA' = tA ; codB' = tB
      ; redM = mkRed3 headred-refl (conv-refl (ty-Pi htA-σ htB-σ))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Pi htA-σ' htB-σ'))
      ; cohF = cf ; fmAllU = allU
      ; convA = convA-cross-fld ; convB = convB-cross-fld
      ; eqA = eqValTyAtA ; edgeET = buildEdgeCrossTy })

------------------------------------------------------------------------
-- conv-Pi : d1 : A = A' : U, d2 : (extend G A) B = B' : U.
--   Conclusion  Pi A B = Pi A' B' : U.   Type U everywhere, so the type
-- two-sub OUTPUT is trivial (valTyU-le, like ty-U).  VALUE = trans X Y:
--   X = (Pi A B)[σ]=(Pi A B)[σ']  (piTwoSub2, the BUNDLED same-term two-sub;
--       its domain/codomain validities BVA/BVB come from AdqE2-to-AdqV2-left
--       on the SUBTERM bundled conversion IHs IH-E-A/IH-E-B -- no presupposition
--       recursion, no value-only adequacyV-ty-Pi),
--   Y = (Pi A B)[σ']=(Pi A' B')[σ']  (convPi2 @ σ', the BUNDLED, driver-ready
--       single-sub conv-Pi -- its domain/codomain IHs are the bundled AdqE2).
-- Case structure mirrors adequacyV2-ty-Pi (term Bot/PiCode, type Bot/UCode).
------------------------------------------------------------------------

adequacyE2-Pi : {g : Nat} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  AdqE2 G A A' U -> AdqE2 (extend G A) B B' U ->
  AdqE2 G (Pi A B) (Pi A' B') U
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH Bot hu a evA fm =
  mkSigma (EqVal2-Bot a) (ValTy2-to-EqValTy2 a (valTyU-le wfH a (snd evA)))
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH UCode () a evA fm
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (FunEl _) () a evA fm
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu Bot evA fm =
  mkSigma tt tt
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu (FunEl _) evA ()
adequacyE2-Pi d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
adequacyE2-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH (PiCode b f0) hu UCode evA fm =
  let c_pi = FinMem-Coherent (PiCode b f0) UCode fm
      c_U  = EvalRel-coh U rho UCode evA
      BVA  = AdqE2-to-AdqV2-left {G = G} {M = A} {N = A'} {A = U} IH-E-A
      BVB  = AdqE2-to-AdqV2-left {G = extend G A} {M = B} {N = B'} {A = U} IH-E-B
      X = piTwoSub2 (fst (typing-ConvTm d1)) (fst (typing-ConvTm d2)) BVA BVB
            sigma sigma' rho crho vsσ vsσ' vcs tyσ tyσ' tycs fits wtσ wtσ' wtcs wfH b f0 hu evA fm
      Y = convPi2 d1 d2 IH-E-A IH-E-B sigma' rho crho vsσ' fits wtσ' tyσ' wfH b f0 hu evA fm
  in mkSigma (EqVal2-trans (PiCode b f0) UCode c_pi c_U X Y)
             (ValTy2-to-EqValTy2 {M = U} UCode (valTyU-le wfH UCode (snd evA)))
