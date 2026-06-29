{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Adequacy.YCore.agda
--
-- Value-only adequacy for the fixpoint  Y g : A   (with  g : Π(x:A)A,
-- B = wk A non-dependent).  Two pieces:
--
--   adequacyV-Y-App-core : Val2 of the CONTRACTUM  App g (Y g) : A,
--     mirroring  adequacySub2-App-core-body  but
--       * Site 1 (argument application) uses the inner Kleene-stage-j
--         recursor IHy on the down-closed Approx (index-preserving), and
--       * the codomain ValTy2 block COLLAPSES (B = wk A ⇒ type is the
--         fixed A) to two direct  adequacySub2 aU  calls.
--
--   adequacyV-Y-approx : Val2 of  Y g  itself, by STRUCTURAL recursion on
--     the Kleene index n; n=0 ↦ Val2-Bot-pub; n=suc j ↦ App-core on the
--     edge g[v0↦u] + head-expansion along headred-Y / conv-Y.
--
-- 0 postulates, 0 TERMINATING.
------------------------------------------------------------------------

module NAT.Adequacy.YCore where

open import NAT.Adequacy.HeadRed
open import NAT.Adequacy.Pi using (Adq ; Val2-U-to-ValTy2)
open import NAT.Adequacy.App using (app-transport-Val2)

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ; List ; nil ; cons)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; CoherentFun ; CoherentFunTail ;
  EvalFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ;
  finMemUCode-Sup ; finMem-upward ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; NotBot ; absurdEl ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-funel-fun ; finMem-funel-coh ;
  finMem-funel-wf)
open import NAT.Syntax.Reduction using (Red ; mkRed ; Red-refl ; HeadRed ; headred-step ; headred-refl ;
  headred-Y ; subst-subst1-comm)
open import NAT.Domain.Membership using (finMem-bot-from)
open import NAT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ; CoherentEnv ;
  EvalRel-Comp ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ; Approx)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; Lam ; App ; Y ; Fin ; fzero ; fsuc ; wkExpr ;
  subst1 ; Sub ; liftSub ; substExpr)
open import NAT.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Y ; conv-refl ; conv-sym ; conv-conv ; conv-Y)
open import NAT.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val ;
  FinMem-Coherent)
open import NAT.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import NAT.Model.Selection using (FinMemAllU-Selection ; selectionBelow ; FinMem-Selection ;
  FinMem-Selection-codomain)
open import NAT.Model.EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-body-EvalFun ;
  EvalRel-Pi-app-type ; EvalRel-subst1-forward)
open import NAT.Model.Soundness using (convSound' ; theorem1)
open import NAT.Syntax.Substitution using (typing-ConvTm ; WtSub ; subst-HasType ; subst-ConvTm ;
  liftSub-WtSub ; typing-WfCtx ; typing-type ; wk-HasType ; subst1-wk)
open import NAT.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- adequacyV-Y-App-core
------------------------------------------------------------------------

adequacyV-Y-App-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u1 : FinEl) -> Coherent u1 ->
  (v0 : FinEl) -> (j : Nat) ->
  Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) j v0 ->
  EvalRel gg rho (FunEl (cons (mkSigma v0 u1) nil)) ->
  (ac1 : FinEl) -> EvalRel A rho ac1 -> FinMem u1 ac1 ->
  -- IH VALUES: adequacySub2 dg (function) + adequacySub2 aU (codomain type) +
  -- the Kleene-stage-j argument recursor (adequacyV-Y-approx … j).
  Adq G gg (Pi A (wkExpr A)) -> Adq G A U ->
  ((u' : FinEl) ->
    Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) j u' ->
    (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' ->
    Val2 H (substExpr sigma (Y gg)) (substExpr sigma A) u' a') ->
  Val2 H (App (substExpr sigma gg) (substExpr sigma (Y gg))) (substExpr sigma A) u1 ac1
adequacyV-Y-App-core {H = H} {A = A} {gg = gg}
  aU dg sigma rho crho vs fits wtsub wfH u1 cu1 v0 j apj evF_sing ac1 evA_ac1 fm1
  IHg IHA IHy =
  S.Eq-transport (\ T -> Val2 H (App sf sa) T u1 ac1) eq-sBA-sA
    (S.Eq-transport (\ T -> Val2 H (App sf sa) T u1 ac1) (S.Eq-sym eq-sBA) transported)
  where
    sf  = substExpr sigma gg
    sa  = substExpr sigma (Y gg)
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) (wkExpr A)
    sBA = substExpr sigma (subst1 (wkExpr A) (Y gg))
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma (wkExpr A) (Y gg))
    eq-sBA-sA : Eq sBA sA
    eq-sBA-sA = S.Eq-cong (substExpr sigma) (subst1-wk A (Y gg))
    -- the contractum's substituted codomain  subst1 sB sa  equals  sA
    eq-sBsa-sA : Eq (subst1 sB sa) sA
    eq-sBsa-sA = Eq-trans (S.Eq-sym eq-sBA) eq-sBA-sA

    evA_v0 : EvalRel (Y gg) rho v0
    evA_v0 = mkSigma j apj

    -- Argument Val2 at a down-closed value u' ≤ v0, via the inner stage-j
    -- recursor.  Case-splitting the (concrete) target makes EvalRel-down (Y gg)
    -- reduce, exposing the SAME Kleene index j; the Bot target is Val2-Bot-pub.
    yArgVal : (u' : FinEl) -> Coherent u' -> LeCode u' v0 ->
      (a' : FinEl) -> EvalRel A rho a' -> FinMem u' a' ->
      Val2 H sa sA u' a'
    yArgVal Bot cu' le' a' evA' fm' = Val2-Bot a'
    yArgVal UCode cu' le' a' evA' fm' =
      IHy UCode (snd (EvalRel-down (Y gg) rho v0 UCode crho cu' evA_v0 le')) a' evA' fm'
    yArgVal (FunEl g0) cu' le' a' evA' fm' =
      IHy (FunEl g0) (snd (EvalRel-down (Y gg) rho v0 (FunEl g0) crho cu' evA_v0 le')) a' evA' fm'
    yArgVal (PiCode a0 f0) cu' le' a' evA' fm' =
      IHy (PiCode a0 f0) (snd (EvalRel-down (Y gg) rho v0 (PiCode a0 f0) crho cu' evA_v0 le')) a' evA' fm'
    yArgVal NatCode cu' le' a' evA' fm' =
      IHy NatCode (snd (EvalRel-down (Y gg) rho v0 NatCode crho cu' evA_v0 le')) a' evA' fm'
    yArgVal ZeroEl cu' le' a' evA' fm' =
      IHy ZeroEl (snd (EvalRel-down (Y gg) rho v0 ZeroEl crho cu' evA_v0 le')) a' evA' fm'
    yArgVal (SucEl w0) cu' le' a' evA' fm' =
      IHy (SucEl w0) (snd (EvalRel-down (Y gg) rho v0 (SucEl w0) crho cu' evA_v0 le')) a' evA' fm'
    -- internal form of ac1's evaluation, at  subst1 (wk A) (Y gg) = A
    evAc1 : EvalRel (subst1 (wkExpr A) (Y gg)) rho ac1
    evAc1 = S.Eq-transport (\ T -> EvalRel T rho ac1) (S.Eq-sym (subst1-wk A (Y gg))) evA_ac1

    sing     = cons (mkSigma v0 u1) nil
    cv0      = EvalRel-coh (Y gg) rho v0 evA_v0

    typed_f  = theorem1 dg rho fits (FunEl sing) evF_sing
    u_big    = fst typed_f
    a_pi     = fst (snd typed_f)
    le_sing  = fst (snd (snd typed_f))
    evF_big  = fst (snd (snd (snd typed_f)))
    fm_big   = fst (snd (snd (snd (snd typed_f))))
    evPi     = snd (snd (snd (snd (snd typed_f))))

    val_fun  = IHg sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

    appVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel gg rho ub -> EvalRel (Pi A (wkExpr A)) rho ap ->
      FinMem ub ap ->
      Val2 H sf (Pi sA sB) ub ap ->
      Val2 H (App sf sa) (subst1 sB sa) u1 ac1
    appVal-dispatch Bot          ap    () evFb evPab fmba valba
    appVal-dispatch UCode        ap    () evFb evPab fmba valba
    appVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
    appVal-dispatch NatCode      ap    () evFb evPab fmba valba
    appVal-dispatch ZeroEl       ap    () evFb evPab fmba valba
    appVal-dispatch (SucEl _)    ap    () evFb evPab fmba valba
    appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
    appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
    appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
    appVal-dispatch (FunEl g_big) NatCode      lf evFb ()
    appVal-dispatch (FunEl g_big) ZeroEl       lf evFb ()
    appVal-dispatch (FunEl g_big) (SucEl _)    lf evFb ()
    appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
      let le_u1_vsel = fst lf
          fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
          piU      = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU    = finMem-piU-dom b_pi f_pi piU
          allU_fpi = finMem-piU-allU b_pi f_pi piU
          cf_pi    = finMem-piU-cft b_pi f_pi piU
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sb
          v_sel    = fst (snd sb)
          sel_big  = fst (snd (snd sb))
          le_usel  = fst (snd (snd (snd sb)))
          eq_vsel  = snd (snd (snd (snd sb)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

          -- Argument Val2 (Site 1): inner Kleene-stage-j recursor on the
          -- down-closed Approx j u_sel (index-preserving down-closure).
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = yArgVal u_sel cu_sel le_usel b_pi evA_bpi fm_usel_bpi

          vpi_fun  = un-ValPi valba
          red_fun  = RValPi.red vpi_fun
          uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA sB} {A = U}) (mkRed (Red3.hr red_fun))
          eqA_fun  = fst uniq_fun
          eqB_fun  = snd uniq_fun
          pav_fun  = RValPi.appV vpi_fun

          val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_fun val_arg
          ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH (ty-Y aU dg))

          val_app_raw = pav_fun u_sel v_sel sel_big sa ht_sa_A0 val_arg'
          val_app : Val2 H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
          val_app = S.Eq-transport
            (\ X -> Val2 H (App sf sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
            (S.Eq-sym eqB_fun) val_app_raw

          ef_usel  = EvalFun f_pi u_sel
          cft_fpi  = cf_pi
          le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
          evBa_efv = EvalRel-Pi-app-type A (wkExpr A) (Y gg) rho b_pi f_pi v0 crho evPab evA_v0
          c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
          c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
          evBa_efusel = EvalRel-down (subst1 (wkExpr A) (Y gg)) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
          comp_ac_ef = EvalRel-Comp (subst1 (wkExpr A) (Y gg)) rho crho ac1 ef_usel evAc1 evBa_efusel

          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi

          -- ValTy2 at ac1 / ef_usel (COLLAPSED: type is the fixed A).
          evU      = mkSigma tt (LeCode-refl UCode tt)
          evA_efusel = S.Eq-transport (\ T -> EvalRel T rho ef_usel) (subst1-wk A (Y gg)) evBa_efusel
          vtA_ac   = Val2-U-to-ValTy2 ac1 ac1_U
                       (IHA sigma rho crho vs fits wtsub wfH ac1 evA_ac1 UCode evU ac1_U)
          vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) (S.Eq-sym eq-sBsa-sA) vtA_ac
          vtA_ef   = Val2-U-to-ValTy2 ef_usel ef_uselU
                       (IHA sigma rho crho vs fits wtsub wfH ef_usel evA_efusel UCode evU ef_uselU)
          vt_ef    = S.Eq-transport (\ T -> ValTy2 H T ef_usel) (S.Eq-sym eq-sBsa-sA) vtA_ef

      in app-transport-Val2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app

    transported : Val2 H (App sf sa) (subst1 sB sa) u1 ac1
    transported = appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

------------------------------------------------------------------------
-- adequacyV-Y-approx : Val2 of  Y gg  by STRUCTURAL recursion on the
-- Kleene index n.
------------------------------------------------------------------------

adequacyV-Y-approx : {h g : Nat} {H : Ctx h} {G : Ctx g} {A gg : Expr g} ->
  HasType G A U -> HasType G gg (Pi A (wkExpr A)) ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  Adq G gg (Pi A (wkExpr A)) -> Adq G A U ->
  (n : Nat) -> (u : FinEl) ->
  Approx (\ p w -> EvalRel gg rho (FunEl (cons (mkSigma p w) nil))) n u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val2 H (substExpr sigma (Y gg)) (substExpr sigma A) u a
adequacyV-Y-approx {H = H} {A = A} {gg = gg} aU dg sigma rho crho vs fits wtsub wfH IHg IHA
  zero u ap a evA fm =
  restrictVal2 H (substExpr sigma (Y gg)) (substExpr sigma A) Bot u a
    (snd ap) fm (finMem-bot-from a (FinMem-a-in-U u a fm)) (Val2-Bot a)
adequacyV-Y-approx {H = H} {A = A} {gg = gg} aU dg sigma rho crho vs fits wtsub wfH IHg IHA
  (suc j) u ap a evA fm =
  let v0   = fst ap
      apj  = fst (snd ap)
      edge = snd (snd ap)
      cu   = FinMem-Coherent u a fm
      valApp = adequacyV-Y-App-core aU dg sigma rho crho vs fits wtsub wfH u cu v0 j apj edge
                 a evA fm IHg IHA
                 (adequacyV-Y-approx aU dg sigma rho crho vs fits wtsub wfH IHg IHA j)
  in Val2-beta-expand u a (headred-step headred-Y headred-refl)
       (subst-ConvTm wtsub wfH (conv-Y aU dg)) valApp
