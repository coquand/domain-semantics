{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LemmaForA2.agda
--
-- Helper lemmas for Adequacy2.  These are pure (non-recursive)
-- functions that can be checked once outside the mutual block,
-- reducing the amount of code Agda must elaborate simultaneously.
------------------------------------------------------------------------

module LemmaForA2 where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun)
open import PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ;
  LeCode-Bot ;
  Coherent ; Comp ; Sup ; Coherent-Sup ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  FinMem ; FinMem-a-in-U ; finMem-upward ; finMemUCode-Sup ;
  coh-from-aU ;
  EvalFun ; EvalFun-mon-arg ; EvalFun-in-UCode ;
  Coherent-EvalFun ;
  CoherentFunTail ; cft-from-cf ;
  FinMemAllU)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc)
open import TypingRules using (Ctx ; extend ; HasType ; ConvTm)
open import Validity2 using (
  Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  ValTy2-Sup ; EqValTy2-Sup ;
  upVal2 ; downVal2 ; restrictVal2 ;
  upEqVal2 ; downEqVal2 ; restrictEqVal2)

------------------------------------------------------------------------
-- 1. Val2/EqVal2 at UCode: pure case-split extractors
--
-- These are in the mutual block of Adequacy2 only because Agda needs
-- to see them there for scope, but they make zero recursive calls.
------------------------------------------------------------------------

Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
  (b : FinEl) -> FinMem b UCode ->
  Val2 G M U b UCode -> ValTy2 G M b
Val2-U-to-ValTy2 Bot            fm v = v
Val2-U-to-ValTy2 UCode          fm v = v
Val2-U-to-ValTy2 (FunEl g)      fm v = v
Val2-U-to-ValTy2 (PiCode a f)   fm v = v

EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N : Expr n}
  (v0 : FinEl) -> FinMem v0 UCode ->
  EqVal2 G M N U v0 UCode -> ValTy2 G M v0
EqVal2-U-to-ValTy2-fst Bot            fm ev = tt
EqVal2-U-to-ValTy2-fst UCode          fm ev = fst ev
EqVal2-U-to-ValTy2-fst (FunEl g)      fm ev = fst ev
EqVal2-U-to-ValTy2-fst (PiCode a' f') fm ev = fst ev

EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N : Expr n}
  (v0 : FinEl) -> FinMem v0 UCode ->
  EqVal2 G M N U v0 UCode -> ValTy2 G N v0
EqVal2-U-to-ValTy2-snd Bot            fm ev = tt
EqVal2-U-to-ValTy2-snd UCode          fm ev = fst (snd ev)
EqVal2-U-to-ValTy2-snd (FunEl g)      fm ev = fst (snd ev)
EqVal2-U-to-ValTy2-snd (PiCode a' f') fm ev = fst (snd ev)

EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N : Expr n}
  (v0 : FinEl) -> FinMem v0 UCode ->
  EqVal2 G M N U v0 UCode -> EqValTy2 G M N v0
EqVal2-U-to-EqValTy2 Bot            fm ev = tt
EqVal2-U-to-EqValTy2 UCode          fm ev = snd (snd ev)
EqVal2-U-to-EqValTy2 (FunEl g)      fm ev = snd (snd ev)
EqVal2-U-to-EqValTy2 (PiCode a' f') fm ev = snd (snd ev)

------------------------------------------------------------------------
-- 2. tyU2-helper: Val2 for the ty-U case
--
-- Pure case analysis on (u, a) both ≤ UCode.
------------------------------------------------------------------------

tyU2-helper : {n : Nat} {H : Ctx n}
  (u0 a0 : FinEl) -> LeCode u0 UCode -> LeCode a0 UCode ->
  FinMem u0 a0 -> Val2 H U U u0 a0
tyU2-helper u0 Bot          _  _  _   = tt
tyU2-helper Bot UCode        _  _  _   = tt
tyU2-helper UCode UCode       _  _  _   = tt
tyU2-helper (FunEl _)    UCode () _  _
tyU2-helper (PiCode _ _) UCode () _  _
tyU2-helper u0 (FunEl _)    _  () _
tyU2-helper u0 (PiCode _ _) _  () _

------------------------------------------------------------------------
-- 3. sup-transport-Val2
--
-- The "up → restrict → down" transport chain for Val2.
-- Given Val2 H N A u0 b, transport to Val2 H N A u' a_arg
-- where u' ≤ u0, using ValTy2 at both endpoints.
--
-- This pattern appears in:
--   transportVal2      (Adequacy2, line ~763)
--   appVal-dispatch    (Adequacy2, line ~1294)
------------------------------------------------------------------------

sup-transport-Val2 : {n : Nat} {H : Ctx n} {N A : Expr n}
  (b a_arg : FinEl) ->
  Comp b a_arg ->
  FinMem b UCode -> FinMem a_arg UCode ->
  (u0 u' : FinEl) ->
  FinMem u0 b -> Coherent u' -> LeCode u' u0 ->
  FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg ->
  Val2 H N A u0 b ->
  Val2 H N A u' a_arg
sup-transport-Val2 {H = H} {N = N} {A = A} b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN =
  let cb       = coh-from-aU b bU
      ca_arg   = coh-from-aU a_arg a_argU
      sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
      c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
      le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
      le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
      fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
      vtA_sup  = ValTy2-Sup H A b a_arg comp_b_a bU a_argU vtA_b vtA_a
      val1     = upVal2 H N A u0 b (Sup b a_arg)
                   le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      val2     = restrictVal2 H N A u0 u' (Sup b a_arg)
                   le_u'_u0 fm_u'_sup fm_u_sup val1
      val3     = downVal2 H N A u'
                   a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
  in val3

------------------------------------------------------------------------
-- 4. sup-transport-EqVal2
--
-- Same transport chain for EqVal2.
--
-- This pattern appears in:
--   transportEqVal2    (Adequacy2, line ~801)
------------------------------------------------------------------------

sup-transport-EqVal2 : {n : Nat} {H : Ctx n} {N1 N2 A : Expr n}
  (b a_arg : FinEl) ->
  Comp b a_arg ->
  FinMem b UCode -> FinMem a_arg UCode ->
  (u0 u' : FinEl) ->
  FinMem u0 b -> Coherent u' -> LeCode u' u0 ->
  FinMem u' a_arg ->
  ValTy2 H A b -> ValTy2 H A a_arg ->
  EqVal2 H N1 N2 A u0 b ->
  EqVal2 H N1 N2 A u' a_arg
sup-transport-EqVal2 {H = H} {N1 = N1} {N2 = N2} {A = A} b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN =
  let cb       = coh-from-aU b bU
      ca_arg   = coh-from-aU a_arg a_argU
      sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
      c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
      le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
      le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
      fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
      vtA_sup  = ValTy2-Sup H A b a_arg comp_b_a bU a_argU vtA_b vtA_a
      eq1      = upEqVal2 H N1 N2 A u0 b (Sup b a_arg)
                   le_b_sup fm_u0_b fm_u0_sup cb c_sup eqN vtA_sup
      fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
      eq2      = restrictEqVal2 H N1 N2 A u0 u' (Sup b a_arg)
                   le_u'_u0 fm_u'_sup fm_u_sup eq1
      eq3      = downEqVal2 H N1 N2 A u' a_arg (Sup b a_arg)
                   le_a_sup fm_u'_a ca_arg sup_bU eq2
  in eq3

------------------------------------------------------------------------
-- 5. app-transport-Val2
--
-- Transport for the App case: move Val2 from (v_sel, ef_usel)
-- to (u1, ac1) via a Sup, given ValTy2 at both.
-- This is the final assembly step in appVal-dispatch.
------------------------------------------------------------------------

app-transport-Val2 : {n : Nat} {H : Ctx n} {M A : Expr n}
  (ac1 ef_usel : FinEl) ->
  Comp ac1 ef_usel ->
  FinMem ac1 UCode -> FinMem ef_usel UCode ->
  (v_sel u1 : FinEl) ->
  FinMem v_sel ef_usel -> FinMem u1 ac1 ->
  LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  Val2 H M A v_sel ef_usel ->
  Val2 H M A u1 ac1
app-transport-Val2 {H = H} {M = M} {A = A}
  ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
  fm_vsel_ef fm_u1_ac le_u1_vsel vt_ac vt_ef val_app =
  let c_ac     = coh-from-aU ac1 ac1_U
      c_ef     = coh-from-aU ef_usel ef_uselU
      sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
      c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_ef
      fm_u1_sup = finMem-upward u1 ac1 (Sup ac1 ef_usel) le_ac_sup c_ac c_sup fm_u1_ac sup_U
      fm_vsel_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      vt_sup   = ValTy2-Sup H A ac1 ef_usel comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
      val_up   = upVal2 H M A v_sel ef_usel (Sup ac1 ef_usel)
                   le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup val_app vt_sup
      val_res  = restrictVal2 H M A v_sel u1 (Sup ac1 ef_usel)
                   le_u1_vsel fm_u1_sup fm_vsel_sup val_up
      val_down = downVal2 H M A u1
                   ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U val_res
  in val_down

------------------------------------------------------------------------
-- 6. app-transport-EqVal2
--
-- Same pattern for EqVal2 in the App conversion cases.
------------------------------------------------------------------------

app-transport-EqVal2 : {n : Nat} {H : Ctx n} {M1 M2 A : Expr n}
  (ac1 ef_usel : FinEl) ->
  Comp ac1 ef_usel ->
  FinMem ac1 UCode -> FinMem ef_usel UCode ->
  (v_sel u1 : FinEl) ->
  FinMem v_sel ef_usel -> FinMem u1 ac1 ->
  LeCode u1 v_sel ->
  ValTy2 H A ac1 -> ValTy2 H A ef_usel ->
  EqVal2 H M1 M2 A v_sel ef_usel ->
  EqVal2 H M1 M2 A u1 ac1
app-transport-EqVal2 {H = H} {M1 = M1} {M2 = M2} {A = A}
  ac1 ef_usel comp_ac_ef ac1_U ef_uselU v_sel u1
  fm_vsel_ef fm_u1_ac le_u1_vsel vt_ac vt_ef eq_app =
  let c_ac     = coh-from-aU ac1 ac1_U
      c_ef     = coh-from-aU ef_usel ef_uselU
      sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
      c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_ef
      le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_ef
      fm_u1_sup = finMem-upward u1 ac1 (Sup ac1 ef_usel) le_ac_sup c_ac c_sup fm_u1_ac sup_U
      fm_vsel_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      vt_sup   = ValTy2-Sup H A ac1 ef_usel comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
      eq_up    = upEqVal2 H M1 M2 A v_sel ef_usel (Sup ac1 ef_usel)
                   le_ef_sup fm_vsel_ef fm_vsel_sup c_ef c_sup eq_app vt_sup
      fm_v_sup = finMem-upward v_sel ef_usel (Sup ac1 ef_usel) le_ef_sup c_ef c_sup fm_vsel_ef sup_U
      eq_res   = restrictEqVal2 H M1 M2 A v_sel u1 (Sup ac1 ef_usel)
                   le_u1_vsel fm_u1_sup fm_v_sup eq_up
      eq_down  = downEqVal2 H M1 M2 A u1
                   ac1 (Sup ac1 ef_usel) le_ac_sup fm_u1_ac c_ac sup_U eq_res
  in eq_down
