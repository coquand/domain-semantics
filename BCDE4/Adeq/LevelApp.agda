{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.LevelApp
--
-- The adequacy combinators for level application t l:
--
--   Adq-LApp, AdqConv-LApp, AdqE1-LApp-fun   (typing, two substitutions,
--                                             conv-cong-LApp-fun / -Ty);
--   AdqE1-LApp-beta                          (conv-LApp-beta);
--   AdqE1-LApp-eta                           (conv-LApp-eta).
--
-- Application: the singleton graph of t at the key LevEl (code l) is
-- enlarged by soundness, a selection edge below the key is chosen, the
-- record clause of the function (appEV of its two-sided record) is used
-- there — the key is admissible for l — and the result is transported
-- to the given pair of codes along their Sup (app-transport-EqVal2).
-- The transport needs the codomain type lsub1 A l to be valid at the
-- given code: the instance family of A is an extra hypothesis.
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.LevelApp (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D
open import BCDE4.Adeq.Pi D using (app-transport-EqVal2)
open import BCDE4.Adeq.Level D using (lsh ; EqVal2-tr3 ; Val2-tr2 ; eqc ; evInst)

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0 ; nil ; cons ;
              LevTy ; LevEl ; LPiCode)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; FinMem ; EvalFun ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon-arg ; EvalFun-in-UCode ; FinMem-a-in-U ;
  finMem-LpiU-allU ; finMem-LpiU-cft ;
  finMem-Lfunel-fun ; finMem-Lfunel-coh ; finMem-Lfunel-wf)
open import BCDE4.Model.Eval D using (EnvApprox ; EvalRel ; CoherentEnv ; EvalRel-down ;
  EvalRel-Comp ; lcodeT)
open import BCDE4.Model.SoundnessLevel D using (LPi-app-type)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (Selection ; selectionBelow ; Coherent-Selection ;
  FinMem-Selection-codomain)
open import BCDE4.Model.Strip using (strip ; stripCtx)
import BCDE4.Model.Core as C
open import BCDE4.RussellSyntax using (Expr ; U ; LPi ; LLam ; LApp ; lsub1 ; lshiftE ; lsubE ;
  lsubE-comp ; lsubE-ext ; lsubE-id ; Eq-trans ; Sub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  WtSub-addL ; wkL-WfCtx ; isType-LPi ; subst-lsub1 ; subst-lshift ; subst-lshift2 ; typing-ConvTm)
open import BCDE4.RussellReduction using (HeadRed ; headred-refl ; headred-step ; headred-lbeta ;
  HeadRed-unique-LPi)

open import BCDE4.Levels using (LCtx ; LSub ; LExpr ; lidS ; lsubL ; lsub1S ; lwkS ; lvar ; liftL ;
  Valid ; valid-ent ; v-sym ; v-refl)
open import BCDE4.Basic using (Eq-cong2)
open import BCDE4.RussellMetaCong using (subst-cong-IsType ; ConvTmSub-addL)
open import BCDE4.RussellMeta using (wtE)
open import BCDE4.RussellLeq using (lsub1-cong)

------------------------------------------------------------------------
-- The application core, for a pair of functions (σt, M2) whose
-- two-sided validity at the product is given (IHf).
------------------------------------------------------------------------

private
  appCore : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} (M2 : Expr h) ->
    IsType (addL G) A -> HasType G t (LPi A) -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    ((ub ap : FinEl) -> EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
      EqVal2 H (substExpr sigma t) M2 (LPi (substExpr (lsh sigma) A)) ub ap) ->
    {A1 A2 : Expr h} -> LAnn H (substExpr (lsh sigma) A) A1 -> LAnn H (substExpr (lsh sigma) A) A2 ->
    (l : LExpr) (u1 : FinEl) ->
    EvalRel (strip t) rho (FunEl (cons (mkSigma (LevEl (lcodeT (lctx H) (lsubL lidS l))) u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (strip (lsub1 A l)) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (LApp A1 (substExpr sigma t) l) (LApp A2 M2 l) (lsub1 (substExpr (lsh sigma) A) l) u1 ac1
  appCore {H = H} {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf {A1} {A2} an1 an2 l u1 evF ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big (IHf u_big a_pi evF_big evPi fm_big)
    where
      st   = substExpr sigma t
      sA   = substExpr (lsh sigma) A
      c    = lcodeT (lctx H) (lsubL lidS l)
      sing = cons (mkSigma (LevEl c) u1) nil
      typed_f = typedVal dt rho fits (FunEl sing) evF
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))

      vtAt : (w : FinEl) -> EvalRel (strip (lsub1 A l)) rho w -> FinMem w U0 -> ValTy2 H (lsub1 sA l) w
      vtAt w ev wU = ValTy2-transport (subst-lsub1 sigma A l) (IHA l sigma rho crho vs fits wt wfH w ev wU)

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
        EqVal2 H st M2 (LPi sA) ub ap ->
        EqVal2 H (LApp A1 st l) (LApp A2 M2 l) (lsub1 sA l) u1 ac1
      dispatch Bot           ap           () evFb evPab fmba eqvba
      dispatch (UCode _)     ap           () evFb evPab fmba eqvba
      dispatch LevTy         ap           () evFb evPab fmba eqvba
      dispatch (LevEl _)     ap           () evFb evPab fmba eqvba
      dispatch (PiCode _ _)  ap           () evFb evPab fmba eqvba
      dispatch (LPiCode _)   ap           () evFb evPab fmba eqvba
      dispatch (FunEl g_big) Bot          lf evFb evPab () eqvba
      dispatch (FunEl g_big) (UCode _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) LevTy        lf evFb () fmba eqvba
      dispatch (FunEl g_big) (LevEl _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) (FunEl _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) (PiCode _ _) lf evFb () fmba eqvba
      dispatch (FunEl g_big) (LPiCode f_pi) lf evFb evPab fmba eqvba =
        let le_u1_vsel = fst lf
            fmg      = finMem-Lfunel-fun g_big f_pi fmba
            cg       = finMem-Lfunel-coh g_big f_pi fmba
            ctg      = cft-from-cf g_big cg
            piU      = finMem-Lfunel-wf g_big f_pi fmba
            allU     = finMem-LpiU-allU f_pi piU
            cf       = finMem-LpiU-cft f_pi piU
            sb       = selectionBelow g_big (LevEl c) ctg tt
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big ctg
            lel      = S.Eq-transport (\ k -> LeCode u_sel (LevEl k)) (eqc H l) le_usel
            rE       = un-REqValLPi eqvba
            uq       = HeadRed-unique-LPi headred-refl (Red3.hr (REqValLPi.red rE))
            eq_app   = EqVal2-transport-A (S.Eq-cong (\ X -> lsub1 X l) (S.Eq-sym uq))
                         (REqValLPi.appEV rE u_sel v_sel sel_big
                            (S.Eq-transport (\ X -> LAnn H X A1) uq an1)
                            (S.Eq-transport (\ X -> LAnn H X A2) uq an2) l lel)
            ef       = EvalFun f_pi u_sel
            c_ef     = Coherent-EvalFun f_pi u_sel cf cu_sel
            evT      = evInst {H = H} A l rho ef
                         (EvalRel-down (C.lsub1 (strip A) l) rho (EvalFun f_pi (LevEl c)) ef crho c_ef
                            (LPi-app-type (strip A) l rho f_pi evPab)
                            (EvalFun-mon-arg f_pi u_sel (LevEl c) le_usel cf cu_sel tt))
            comp     = EvalRel-Comp (strip (lsub1 A l)) rho crho ac1 ef evAc1 evT
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_U     = EvalFun-in-UCode f_pi u_sel LevTy cf cu_sel allU
            fm_vsel_ef = FinMem-Selection-codomain LevTy f_pi sel_big fmg ctg cf allU
        in app-transport-EqVal2 ac1 ef comp ac1_U ef_U v_sel u1 fm_vsel_ef fm1 le_u1_vsel'
             (vtAt ac1 evAc1 ac1_U) (vtAt ef evT ef_U) eq_app

  -- dispatch over the value of the application (⊥, or a singleton graph)
  appGo : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} (M2 : Expr h) ->
    IsType (addL G) A -> HasType G t (LPi A) -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    ((ub ap : FinEl) -> EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
      EqVal2 H (substExpr sigma t) M2 (LPi (substExpr (lsh sigma) A)) ub ap) ->
    {A1 A2 : Expr h} -> LAnn H (substExpr (lsh sigma) A) A1 -> LAnn H (substExpr (lsh sigma) A) A2 ->
    (l : LExpr) (u : FinEl) -> EvalRel (strip (LApp A t l)) rho u ->
    (ac : FinEl) -> EvalRel (strip (lsub1 A l)) rho ac -> FinMem u ac ->
    EqVal2 H (LApp A1 (substExpr sigma t) l) (LApp A2 M2 l) (lsub1 (substExpr (lsh sigma) A) l) u ac
  appGo M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l Bot          hu ac evA fm = EqVal2-Bot ac
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (UCode k) hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (UCode k) hu ac evA fm
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l LevTy hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l LevTy hu ac evA fm
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (LevEl k) hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (LevEl k) hu ac evA fm
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (FunEl g) hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (FunEl g) hu ac evA fm
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (PiCode b f) hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (PiCode b f) hu ac evA fm
  appGo {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (LPiCode f) hu ac evA fm =
    appCore {A = A} {t = t} M2 d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l (LPiCode f) hu ac evA fm

  appCoreLvl : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} ->
    IsType (addL G) A -> HasType G t (LPi A) -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    ((ub ap : FinEl) -> EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
      Val2 H (substExpr sigma t) (LPi (substExpr (lsh sigma) A)) ub ap) ->
    {A1 A2 : Expr h} -> LAnn H (substExpr (lsh sigma) A) A1 -> LAnn H (substExpr (lsh sigma) A) A2 ->
    (l l' : LExpr) -> Valid (lctx H) l l' -> (u1 : FinEl) ->
    EvalRel (strip t) rho (FunEl (cons (mkSigma (LevEl (lcodeT (lctx H) (lsubL lidS l))) u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (strip (lsub1 A l)) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (LApp A1 (substExpr sigma t) l) (LApp A2 (substExpr sigma t) l') (lsub1 (substExpr (lsh sigma) A) l) u1 ac1
  appCoreLvl {H = H} {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf {A1} {A2} an1 an2 l l' e u1 evF ac1 evAc1 fm1 =
    dispatch u_big a_pi le_sing evF_big evPi fm_big (IHf u_big a_pi evF_big evPi fm_big)
    where
      st   = substExpr sigma t
      sA   = substExpr (lsh sigma) A
      c    = lcodeT (lctx H) (lsubL lidS l)
      sing = cons (mkSigma (LevEl c) u1) nil
      typed_f = typedVal dt rho fits (FunEl sing) evF
      u_big   = fst typed_f
      a_pi    = fst (snd typed_f)
      le_sing = fst (snd (snd typed_f))
      evF_big = fst (snd (snd (snd typed_f)))
      fm_big  = fst (snd (snd (snd (snd typed_f))))
      evPi    = snd (snd (snd (snd (snd typed_f))))

      vtAt : (w : FinEl) -> EvalRel (strip (lsub1 A l)) rho w -> FinMem w U0 -> ValTy2 H (lsub1 sA l) w
      vtAt w ev wU = ValTy2-transport (subst-lsub1 sigma A l) (IHA l sigma rho crho vs fits wt wfH w ev wU)

      dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
        EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
        Val2 H st (LPi sA) ub ap ->
        EqVal2 H (LApp A1 st l) (LApp A2 st l') (lsub1 sA l) u1 ac1
      dispatch Bot           ap           () evFb evPab fmba eqvba
      dispatch (UCode _)     ap           () evFb evPab fmba eqvba
      dispatch LevTy         ap           () evFb evPab fmba eqvba
      dispatch (LevEl _)     ap           () evFb evPab fmba eqvba
      dispatch (PiCode _ _)  ap           () evFb evPab fmba eqvba
      dispatch (LPiCode _)   ap           () evFb evPab fmba eqvba
      dispatch (FunEl g_big) Bot          lf evFb evPab () eqvba
      dispatch (FunEl g_big) (UCode _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) LevTy        lf evFb () fmba eqvba
      dispatch (FunEl g_big) (LevEl _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) (FunEl _)    lf evFb () fmba eqvba
      dispatch (FunEl g_big) (PiCode _ _) lf evFb () fmba eqvba
      dispatch (FunEl g_big) (LPiCode f_pi) lf evFb evPab fmba eqvba =
        let le_u1_vsel = fst lf
            fmg      = finMem-Lfunel-fun g_big f_pi fmba
            cg       = finMem-Lfunel-coh g_big f_pi fmba
            ctg      = cft-from-cf g_big cg
            piU      = finMem-Lfunel-wf g_big f_pi fmba
            allU     = finMem-LpiU-allU f_pi piU
            cf       = finMem-LpiU-cft f_pi piU
            sb       = selectionBelow g_big (LevEl c) ctg tt
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big ctg
            lel      = S.Eq-transport (\ k -> LeCode u_sel (LevEl k)) (eqc H l) le_usel
            rV       = un-ValLPi eqvba
            uq       = HeadRed-unique-LPi headred-refl (Red3.hr (RValLPi.red rV))
            eq_app   = EqVal2-transport-A (S.Eq-cong (\ X -> lsub1 X l) (S.Eq-sym uq))
                         (RValLPi.appLE rV u_sel v_sel sel_big
                            (S.Eq-transport (\ X -> LAnn H X A1) uq an1)
                            (S.Eq-transport (\ X -> LAnn H X A2) uq an2) l l' e lel)
            ef       = EvalFun f_pi u_sel
            c_ef     = Coherent-EvalFun f_pi u_sel cf cu_sel
            evT      = evInst {H = H} A l rho ef
                         (EvalRel-down (C.lsub1 (strip A) l) rho (EvalFun f_pi (LevEl c)) ef crho c_ef
                            (LPi-app-type (strip A) l rho f_pi evPab)
                            (EvalFun-mon-arg f_pi u_sel (LevEl c) le_usel cf cu_sel tt))
            comp     = EvalRel-Comp (strip (lsub1 A l)) rho crho ac1 ef evAc1 evT
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_U     = EvalFun-in-UCode f_pi u_sel LevTy cf cu_sel allU
            fm_vsel_ef = FinMem-Selection-codomain LevTy f_pi sel_big fmg ctg cf allU
        in app-transport-EqVal2 ac1 ef comp ac1_U ef_U v_sel u1 fm_vsel_ef fm1 le_u1_vsel'
             (vtAt ac1 evAc1 ac1_U) (vtAt ef evT ef_U) eq_app

  -- the same, for the level variation of one function
  appGoLvl : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} ->
    IsType (addL G) A -> HasType G t (LPi A) -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    ((ub ap : FinEl) -> EvalRel (strip t) rho ub -> EvalRel (strip (LPi A)) rho ap -> FinMem ub ap ->
      Val2 H (substExpr sigma t) (LPi (substExpr (lsh sigma) A)) ub ap) ->
    {A1 A2 : Expr h} -> LAnn H (substExpr (lsh sigma) A) A1 -> LAnn H (substExpr (lsh sigma) A) A2 ->
    (l l' : LExpr) -> Valid (lctx H) l l' -> (u : FinEl) -> EvalRel (strip (LApp A t l)) rho u ->
    (ac : FinEl) -> EvalRel (strip (lsub1 A l)) rho ac -> FinMem u ac ->
    EqVal2 H (LApp A1 (substExpr sigma t) l) (LApp A2 (substExpr sigma t) l') (lsub1 (substExpr (lsh sigma) A) l) u ac
  appGoLvl d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e Bot          hu ac evA fm = EqVal2-Bot ac
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (UCode k) hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (UCode k) hu ac evA fm
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e LevTy hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e LevTy hu ac evA fm
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (LevEl k) hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (LevEl k) hu ac evA fm
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (FunEl g) hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (FunEl g) hu ac evA fm
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (PiCode b f) hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (PiCode b f) hu ac evA fm
  appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (LPiCode f) hu ac evA fm =
    appCoreLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH IHf an1 an2 l l' e (LPiCode f) hu ac evA fm

------------------------------------------------------------------------
-- Level application: one substitution, two substitutions, congruence
------------------------------------------------------------------------

Adq-LApp : {g : Nat} {G : Ctx g} {A t : Expr g} ->
  IsType (addL G) A -> HasType G t (LPi A) -> Adq G t (LPi A) ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
  (l : LExpr) -> Adq G (LApp A t l) (lsub1 A l)
Adq-LApp {A = A} {t = t} d1 dt IH IHA l sigma rho crho vs fits wt wfH u hu ac evA fm =
  Val2-transport-A (S.Eq-sym (subst-lsub1 sigma A l))
    (Val2-from-EqVal2-first u ac
      (appGo {A = A} {t = t} (substExpr sigma t) d1 dt IHA sigma rho crho vs fits wt wfH
         (\ ub ap evub evap fmub -> Val2-to-EqVal2 ub ap (IH sigma rho crho vs fits wt wfH ub evub ap evap fmub))
         cR cR l u hu ac evA fm))
  where cR = conv-Ty-refl (subst-IsType (WtSub-addL wt) (wkL-WfCtx wfH) d1)

AdqConv-LApp : {g : Nat} {G : Ctx g} {A t : Expr g} ->
  IsType (addL G) A -> HasType G t (LPi A) -> AdqConv G t (LPi A) ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
  (l : LExpr) -> AdqConv G (LApp A t l) (lsub1 A l)
AdqConv-LApp {A = A} {t = t} d1 dt IH IHA l
    sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu ac evA fm =
  EqVal2-transport-A (S.Eq-sym (subst-lsub1 sigma A l))
    (appGo {A = A} {t = t} (substExpr sigma' t) d1 dt IHA sigma rho crho vs fits wt wfH
       (\ ub ap evub evap fmub -> IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH ub evub ap evap fmub)
       (conv-Ty-refl (subst-IsType (WtSub-addL wt) wfL d1))
       (conv-Ty-sym (subst-cong-IsType (ConvTmSub-addL wcs) wfL d1)) l u hu ac evA fm)
  where wfL = wkL-WfCtx wfH

-- (the annotation may change along: t l = t' l for [α]A = [α]A')
AdqE1-LApp-fun : {g : Nat} {G : Ctx g} {A A' t t' : Expr g} ->
  IsType (addL G) A -> ConvTy (addL G) A A' -> ConvTm G t t' (LPi A) -> AdqE1 G t t' (LPi A) ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
  (l : LExpr) -> AdqE1 G (LApp A t l) (LApp A' t' l) (lsub1 A l)
AdqE1-LApp-fun {A = A} {t = t} {t' = t'} d1 cAA' ctt IH IHA l sigma rho crho vs fits wt wfH u hu ac evA fm =
  EqVal2-transport-A (S.Eq-sym (subst-lsub1 sigma A l))
    (appGo {A = A} {t = t} (substExpr sigma t') d1 (fst (typing-ConvTm ctt)) IHA sigma rho crho vs fits wt wfH
       (\ ub ap evub evap fmub -> IH sigma rho crho vs fits wt wfH ub evub ap evap fmub)
       (conv-Ty-refl (subst-IsType (WtSub-addL wt) wfL d1))
       (conv-Ty-sym (subst-ConvTy (WtSub-addL wt) wfL cAA')) l u hu ac evA fm)
  where wfL = wkL-WfCtx wfH

-- t l = t l'  for  l = l'
AdqE1-LApp-lvl : {g : Nat} {G : Ctx g} {A t : Expr g} {l l' : LExpr} ->
  IsType (addL G) A -> HasType G t (LPi A) -> Valid (lctx G) l l' -> Adq G t (LPi A) ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
  AdqE1 G (LApp A t l) (LApp A t l') (lsub1 A l)
AdqE1-LApp-lvl {A = A} {t = t} {l} {l'} d1 dt e IH IHA sigma rho crho vs fits wt wfH u hu ac evA fm =
  EqVal2-transport-A (S.Eq-sym (subst-lsub1 sigma A l))
    (appGoLvl {A = A} {t = t} d1 dt IHA sigma rho crho vs fits wt wfH
       (\ ub ap evub evap fmub -> IH sigma rho crho vs fits wt wfH ub evub ap evap fmub)
       cR cR l l' (valid-ent (wtE wt) e) u hu ac evA fm)
  where cR = conv-Ty-refl (subst-IsType (WtSub-addL wt) (wkL-WfCtx wfH) d1)

------------------------------------------------------------------------
-- β:  (⟨α⟩u) l = u[l/α], by head expansion of the contractum's validity
------------------------------------------------------------------------

AdqE1-LApp-beta : {g : Nat} {G : Ctx g} {A u : Expr g} ->
  IsType (addL G) A -> HasType (addL G) u A -> (l : LExpr) ->
  Adq G (lsub1 u l) (lsub1 A l) ->
  AdqE1 G (LApp A (LLam A u) l) (lsub1 u l) (lsub1 A l)
AdqE1-LApp-beta {A = A} {u = u} d1 d2 l IH {H = H} sigma rho crho vs fits wt wfH x hu a evA fm =
  EqVal2-tr3 refl (S.Eq-sym (subst-lsub1 sigma u l)) (S.Eq-sym (subst-lsub1 sigma A l))
    (EqVal2-headred-expand x a (headred-step headred-lbeta headred-refl) headred-refl cvb
       (conv-refl (snd (typing-ConvTm cvb)))
       (Val2-to-EqVal2 x a
          (Val2-tr2 (subst-lsub1 sigma u l) (subst-lsub1 sigma A l)
             (IH sigma rho crho vs fits wt wfH x (evFwd-Tm (conv-LApp-beta d1 d2) rho fits x hu) a evA fm))))
  where
    wtL = WtSub-addL wt
    wfL = wkL-WfCtx wfH
    cvb : ConvTm H (LApp (substExpr (lsh sigma) A) (LLam (substExpr (lsh sigma) A) (substExpr (lsh sigma) u)) l)
                   (lsub1 (substExpr (lsh sigma) u) l)
                   (lsub1 (substExpr (lsh sigma) A) l)
    cvb = conv-LApp-beta (subst-IsType wtL wfL d1) (subst-HasType wtL wfL d2)

------------------------------------------------------------------------
-- η:  t = ⟨α⟩(t↑ α)
------------------------------------------------------------------------

private
  lsub1-lshiftE : {n : Nat} (M : Expr n) (l : LExpr) -> Eq (lsubE (lsub1S l) (lshiftE M)) M
  lsub1-lshiftE M l =
    Eq-trans (lsubE-comp (lsub1S l) lwkS M) (Eq-trans (lsubE-ext _ _ (\ i -> refl) M) (lsubE-id M))

  -- an annotation lifted over the shift, instantiated under the binder
  lift-inst : {n : Nat} (M : Expr n) (l : LExpr) -> Eq (lsubE (liftL (lsub1S l)) (lsubE (liftL lwkS) M)) M
  lift-inst M l =
    Eq-trans (lsubE-comp (liftL (lsub1S l)) (liftL lwkS) M) (Eq-trans (lsubE-ext _ _ pt M) (lsubE-id M))
    where
      pt : (i : Nat) -> Eq (lsubL (liftL (lsub1S l)) (liftL lwkS i)) (lidS i)
      pt zero    = refl
      pt (suc i) = refl

  eta-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} ->
    IsType (addL G) A -> HasType G t (LPi A) -> Adq G t (LPi A) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) -> EvalRel (strip t) rho (FunEl g0) ->
    (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem (FunEl g0) (LPiCode f) ->
    EqVal2 H (substExpr sigma t)
             (LLam (substExpr (lsh sigma) A)
                (LApp (lsubE (liftL lwkS) (substExpr (lsh sigma) A)) (lshiftE (substExpr sigma t)) (lvar zero)))
             (LPi (substExpr (lsh sigma) A)) (FunEl g0) (LPiCode f)
  eta-core {H = H} {A = A} {t = t} d1 dt IH sigma rho crho vs fits wt wfH g0 hu f evA fm =
    mk-EqValLPi vtA rvc' rL rE
    where
      st   = substExpr sigma t
      sA   = substExpr (lsh sigma) A
      L    = LLam sA (LApp (lsubE (liftL lwkS) sA) (lshiftE st) (lvar zero))
      htA  = subst-IsType (WtSub-addL wt) (wkL-WfCtx wfH) d1
      cR   = conv-Ty-refl htA
      hst  = subst-HasType wt wfH dt
      deta : ConvTm H st L (LPi sA)
      deta = conv-LApp-eta htA hst
      valc = IH sigma rho crho vs fits wt wfH (FunEl g0) hu (LPiCode f) evA fm
      rvc  = un-ValLPi valc
      vtA  = valLPi-ty valc
      redA = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA))
      uq   = HeadRed-unique-LPi headred-refl (Red3.hr (RValLPi.red rvc))

      avc : (u v : FinEl) -> Selection g0 u v -> {A1 : Expr _} -> LAnn H sA A1 ->
        (l : LExpr) -> LeCode u (LevEl (codeL H l)) ->
        Val2 H (LApp A1 st l) (lsub1 sA l) v (EvalFun f u)
      avc u v sel {A1} an l lel =
        Val2-transport-A (S.Eq-cong (\ X -> lsub1 X l) (S.Eq-sym uq))
          (RValLPi.appV rvc u v sel (S.Eq-transport (\ X -> LAnn H X A1) uq an) l lel)

      -- the contractum's annotation is sA again
      hrL : (l : LExpr) {A1 : Expr _} -> HeadRed (LApp A1 L l) (LApp sA st l)
      hrL l {A1} = S.Eq-transport (\ X -> HeadRed (LApp A1 L l) X)
                (Eq-cong2 (\ Y X -> LApp Y X l) (lift-inst sA l) (lsub1-lshiftE st l))
                (headred-step headred-lbeta headred-refl)

      cvL : (l : LExpr) {A1 : Expr _} -> LAnn H sA A1 -> ConvTm H (LApp A1 L l) (LApp sA st l) (lsub1 sA l)
      cvL l an = conv-trans (lann-LApp-fun htA an (conv-sym deta)) (lann-LApp-ann htA an hst)

      alev : (u v : FinEl) -> Selection g0 u v -> {A1 A2 : Expr _} -> LAnn H sA A1 -> LAnn H sA A2 ->
        (l l' : LExpr) -> Valid (lctx H) l l' ->
        LeCode u (LevEl (codeL H l)) ->
        EqVal2 H (LApp A1 st l) (LApp A2 st l') (lsub1 sA l) v (EvalFun f u)
      alev u v sel {A1} {A2} an1 an2 l l' e lel =
        EqVal2-transport-A (S.Eq-cong (\ X -> lsub1 X l) (S.Eq-sym uq))
          (RValLPi.appLE rvc u v sel (S.Eq-transport (\ X -> LAnn H X A1) uq an1)
             (S.Eq-transport (\ X -> LAnn H X A2) uq an2) l l' e lel)

      rvc' : RValLPi H st (LPi sA) g0 f
      rvc' = record { domA0 = sA ; red = redA ; cohG = RValLPi.cohG rvc ; fmG = RValLPi.fmG rvc
                    ; appV = avc ; appLE = alev }

      rL : RValLPi H L (LPi sA) g0 f
      rL = record { domA0 = sA ; red = redA ; cohG = RValLPi.cohG rvc ; fmG = RValLPi.fmG rvc
                  ; appV = \ u v sel an l lel ->
                      Val2-beta-expand v (EvalFun f u) (hrL l) (cvL l an) (avc u v sel cR l lel)
                  ; appLE = \ u v sel an1 an2 l l' e lel ->
                      EqVal2-headred-expand v (EvalFun f u) (hrL l) (hrL l')
                        (cvL l an1) (conv-conv (cvL l' an2) (lsub1-cong htA (v-sym e)))
                        (alev u v sel cR cR l l' e lel) }

      rE : REqValLPi H st L (LPi sA) g0 f
      rE = record { domA0 = sA ; red = redA ; cohG = RValLPi.cohG rvc ; fmG = RValLPi.fmG rvc
                  ; appEV = \ u v sel an1 an2 l lel ->
                      EqVal2-headred-expand v (EvalFun f u) headred-refl (hrL l)
                        (conv-refl (lann-LApp-ty htA an1 hst)) (cvL l an2)
                        (alev u v sel an1 cR l l v-refl lel) }

  etaAt : {h g : Nat} {H : Ctx h} {G : Ctx g} {A t : Expr g} ->
    IsType (addL G) A -> HasType G t (LPi A) -> Adq G t (LPi A) ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (x : FinEl) -> EvalRel (strip t) rho x ->
    (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem x (LPiCode f) ->
    EqVal2 H (substExpr sigma t)
             (LLam (substExpr (lsh sigma) A)
                (LApp (lsubE (liftL lwkS) (substExpr (lsh sigma) A)) (lshiftE (substExpr sigma t)) (lvar zero)))
             (LPi (substExpr (lsh sigma) A)) x (LPiCode f)
  etaAt d1 dt IH sigma rho crho vs fits wt wfH Bot          hu f evA fm = tt
  etaAt d1 dt IH sigma rho crho vs fits wt wfH (UCode _)    hu f evA fm = tt
  etaAt d1 dt IH sigma rho crho vs fits wt wfH LevTy        hu f evA fm = tt
  etaAt d1 dt IH sigma rho crho vs fits wt wfH (LevEl _)    hu f evA fm = tt
  etaAt d1 dt IH sigma rho crho vs fits wt wfH (PiCode _ _) hu f evA fm = tt
  etaAt d1 dt IH sigma rho crho vs fits wt wfH (LPiCode _)  hu f evA fm = tt
  etaAt {A = A} {t = t} d1 dt IH sigma rho crho vs fits wt wfH (FunEl g0) hu f evA fm =
    eta-core {A = A} {t = t} d1 dt IH sigma rho crho vs fits wt wfH g0 hu f evA fm

AdqE1-LApp-eta : {g : Nat} {G : Ctx g} {A t : Expr g} ->
  IsType (addL G) A -> HasType G t (LPi A) -> Adq G t (LPi A) ->
  AdqE1 G t (LLam A (LApp (lsubE (liftL lwkS) A) (lshiftE t) (lvar zero))) (LPi A)
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu Bot          evA fm = tt
AdqE1-LApp-eta {A = A} {t = t} d1 dt IH {H = H} sigma rho crho vs fits wt wfH x hu (LPiCode f) evA fm =
  EqVal2-tr3 refl (Eq-cong2 (\ Y X -> LLam (substExpr (lsh sigma) A) (LApp Y X (lvar zero)))
                     (subst-lshift2 sigma A) (S.Eq-sym (subst-lshift sigma t))) refl
    (etaAt {A = A} {t = t} d1 dt IH sigma rho crho vs fits wt wfH x hu f evA fm)
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu (UCode _)    () fm
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu LevTy        () fm
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu (LevEl _)    () fm
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu (FunEl _)    () fm
AdqE1-LApp-eta d1 dt IH sigma rho crho vs fits wt wfH x hu (PiCode _ _) () fm
