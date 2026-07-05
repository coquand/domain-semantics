{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyFunext.agda  (MIN/ -- PROTOTYPE)
--
-- Standalone, recursor-parameterised SINGLE-substitution combinator for
-- the conv-funext extensionality rule, factored out of Adequacy.agda's
-- mutual block.
--
--   adequacyEqSub2-funext : the single-sub conversion  f = g' : Pi A B
--   (the "Y" piece of the bundled conv-funext recipe).
--
-- The original recurses on adequacySub2 (df, dg), adequacyEqSub2 (the body
-- conversion d), and transportVal2 (dA, ...).  Here those become the
-- params adSub2 / adEqSub2 / IH-A (= Adq G A U, fed to transportVal2').
-- Non-recursive: no postulate.
------------------------------------------------------------------------

module ID.Adequacy.Funext where
open import ID.Adequacy.HeadRed

open import ID.Adequacy.App using (AdSub2Rec)
open import ID.Adequacy.ArgCore using (AdEqSub2Rec)
open import ID.Adequacy.Pi using (Adq ; transportVal2')
open import ID.Adequacy.VE using (AdqE1)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ; nil ; cons)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; EvalFun ; FinMem ;
  coh-from-aU ; FinMem-coh-u ; cft-from-cf ; LeFunCode-refl ; mkCFT ; NotBot ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ;
  EvalRel-down ; EvalRel-mon-env ; EnvLe-refl)
open import ID.Syntax.Raw using (Expr ; Var ; U ; Pi ; Lam ; App ; fzero ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-Pi ; conv-refl ; conv-funext)
open import ID.Syntax.Reduction using (headred-refl)
open import ID.Syntax.Substitution using (WtSub ; subst-HasType ; liftSub-WtSub)
open import ID.Model.Soundness using (convSound)
open import ID.Model.EvalSubstitution using (EvalRel-Pi-body ; EvalRel-wk)
open import ID.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val ;
  Selection-le-EvalFun)
open import ID.Model.Selection using (FinMem-Selection ; FinMem-Selection-codomain)
open import ID.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- adequacyEqSub2-funext : full (u, a) version.
-- Faithful port of Adequacy.agda's adequacyEqSub2-funext, with
--   adequacySub2 df / dg   -> adSub2 df / dg
--   adequacyEqSub2 d       -> adEqSub2 d
--   transportVal2 dA htBU' -> transportVal2' IH-A
------------------------------------------------------------------------

adequacyEqSub2-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
  HasType G A U ->
  ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                       (App (wkExpr g') (Var fzero)) B ->
  HasType G f (Pi A B) ->
  HasType G g' (Pi A B) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  Adq G f (Pi A B) -> Adq G g' (Pi A B) ->
  AdqE1 (extend G A) (App (wkExpr f) (Var fzero)) (App (wkExpr g') (Var fzero)) B ->
  Adq G A U ->
  (u : FinEl) -> EvalRel f rho u ->
  (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma f) (substExpr sigma g')
          (substExpr sigma (Pi A B)) u a
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A u hu Bot evA fm = tt
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A u hu UCode () fm
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A u hu (FunEl _) () fm
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A Bot hu (PiCode b f0) evA fm = tt
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A UCode hu (PiCode b f0) evA ()
adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A (PiCode _ _) hu (PiCode b f0) evA ()
adequacyEqSub2-funext {H = H} {G = G} {A = A} {B = B} {f = f} {g' = g'} dA d df dg sigma rho crho vs fits wtsub wfH IHfv IHgv IHbe IH-A (FunEl g0) hu (PiCode b f0) evA fm =
  let val_sf = IHfv sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
      evG    = convSound (conv-funext dA d df dg) rho fits (FunEl g0) hu
      val_sg = IHgv sigma rho crho vs fits wtsub wfH (FunEl g0) evG (PiCode b f0) evA fm
      valTyPi = valPi-ty val_sf
      valPi_sf = un-ValPi val_sf
      valPi_sg = un-ValPi val_sg
  in mk-EqValPi valTyPi valPi_sf valPi_sg
       (record { domA0 = substExpr sigma A
               ; codB0 = substExpr (liftSub sigma) B
               ; red = mkRed3 headred-refl (conv-refl (ty-Pi (subst-HasType wtsub wfH dA) (subst-HasType (liftSub-WtSub wtsub wfH dA) (wf-extend (subst-HasType wtsub wfH dA)) (typing-Pi-codomain dA df))))
               ; cohG = RValPi.cohG valPi_sf
               ; fmG = RValPi.fmG valPi_sf
               ; appEV = buildEqBody valPi_sf })
  where
    sA'   = substExpr sigma A
    sB'   = substExpr (liftSub sigma) B
    htBU' = typing-Pi-codomain dA df
    fmg'  = finMem-funel-fun g0 b f0 fm
    cg'   = finMem-funel-coh g0 b f0 fm
    pU'   = finMem-funel-wf g0 b f0 fm
    bU'   = finMem-piU-dom b f0 pU'
    allU' = finMem-piU-allU b f0 pU'
    cf0'  = finMem-piU-cft b f0 pU'
    cb'   = coh-from-aU b bU'
    evAb' = fst (snd evA)
    ctg0' = cft-from-cf g0 cg'

    buildEqBodyCore : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
      Coherent u0 ->
      EvalRel (App (wkExpr f) (Var fzero)) (extendEnv rho u0) v0 ->
      (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
      EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
    buildEqBodyCore u0 v0 sel cu0 ev_app P htP valP =
      let fm_u0_b   = FinMem-Selection b f0 sel fmg' ctg0' cb' bU'
          fm_v0_ef  = FinMem-Selection-codomain b f0 sel fmg' ctg0' cf0' allU'
          evB_ef    = EvalRel-Pi-body A B rho b f0 u0 crho cu0 evA
          fits'     = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb'))
          crho'     = mkSigma crho cu0
          hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                        transportVal2' {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU' evAb' u0 fm_u0_b P valP u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'       = ValidSub2-extend sigma P rho u0 vs hyp0
          wtsub'    = extSub-WtSub wtsub wfH dA htP
          raw       = IHbe (extSub sigma P) (extendEnv rho u0) crho' vs' fits' wtsub' wfH
                        v0 ev_app (EvalFun f0 u0) evB_ef fm_v0_ef
          eq_f_wk   = substExpr-wk sigma f P
          eq_g_wk   = substExpr-wk sigma g' P
          eq_B_comp = S.Eq-sym (substExpr-comp sigma B P)
          raw'      = S.Eq-transport (\ T -> EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) T v0 (EvalFun f0 u0)) eq_B_comp
                        (S.Eq-transport (\ X -> EqVal2 H (App (substExpr sigma f) P) (App X P) (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_g_wk
                          (S.Eq-transport (\ X -> EqVal2 H (App X P) _ (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_f_wk raw))
      in raw'

    mkSingEvApp : (u0 : FinEl) (v0 : FinEl) -> Coherent u0 -> Coherent v0 -> NotBot v0 ->
      LeCode v0 (EvalFun g0 u0) ->
      EvalRel f rho (FunEl (cons (mkSigma u0 v0) nil))
    mkSingEvApp u0 v0 cu0 cv0 nbv0 le_v0 =
      let c_sing    = mkCFT cu0 cv0 nbv0 tt tt
      in EvalRel-down f rho (FunEl g0) (FunEl (cons (mkSigma u0 v0) nil))
                        crho c_sing hu (mkSigma le_v0 tt)

    buildEqBody : _ -> (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
      (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
      EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
    buildEqBody _ u0 Bot sel P htP valP = EqVal2-Bot (EvalFun f0 u0)
    buildEqBody vps u0 UCode sel P htP valP =
      let cu0 = Coherent-Selection sel ctg0'
          le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
          ev_f_sing = mkSingEvApp u0 UCode cu0 tt tt le
          ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 UCode) nil)) ev_f_sing
          ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
          ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
      in buildEqBodyCore u0 UCode sel cu0 ev_app P htP valP
    buildEqBody vps u0 (FunEl g1) sel P htP valP =
      let cu0 = Coherent-Selection sel ctg0'
          cv0 = Coherent-Selection-val sel ctg0'
          le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
          ev_f_sing = mkSingEvApp u0 (FunEl g1) cu0 cv0 tt le
          ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (FunEl g1)) nil)) ev_f_sing
          ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
          ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
      in buildEqBodyCore u0 (FunEl g1) sel cu0 ev_app P htP valP
    buildEqBody vps u0 (PiCode a1 f1) sel P htP valP =
      let cu0 = Coherent-Selection sel ctg0'
          cv0 = Coherent-Selection-val sel ctg0'
          le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
          ev_f_sing = mkSingEvApp u0 (PiCode a1 f1) cu0 cv0 tt le
          ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (PiCode a1 f1)) nil)) ev_f_sing
          ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
          ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
      in buildEqBodyCore u0 (PiCode a1 f1) sel cu0 ev_app P htP valP
    buildEqBody vps u0 (IdCode t1 u1 v1) sel P htP valP =
      let cu0 = Coherent-Selection sel ctg0'
          cv0 = Coherent-Selection-val sel ctg0'
          le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
          ev_f_sing = mkSingEvApp u0 (IdCode t1 u1 v1) cu0 cv0 tt le
          ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (IdCode t1 u1 v1)) nil)) ev_f_sing
          ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
          ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
      in buildEqBodyCore u0 (IdCode t1 u1 v1) sel cu0 ev_app P htP valP
    buildEqBody vps u0 (RefEl w1) sel P htP valP =
      let cu0 = Coherent-Selection sel ctg0'
          cv0 = Coherent-Selection-val sel ctg0'
          le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
          ev_f_sing = mkSingEvApp u0 (RefEl w1) cu0 cv0 tt le
          ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (RefEl w1)) nil)) ev_f_sing
          ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
          ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
      in buildEqBodyCore u0 (RefEl w1) sel cu0 ev_app P htP valP
