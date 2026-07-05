{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JTypeEq.agda
--
-- The MODULAR motive-endpoint type-equality lemma for based-J adequacy.
--
--   jTypeEq :  EqValTy2 H (App³ sC wit0 wit0 (Ref wit0))
--                          (App³ sC sa   sb   (Ref wit0)) at
--
-- i.e. the two motive instances -- at the witness (wit0,wit0) and at the real
-- endpoints (sa,sb) -- are EQUAL AS TYPES in the logical relation.  This is the
-- single shared obligation behind all three J/conv-J holes of Theorem 2
-- (Value.agda @113/@186/@265): refCore feeds it to `Val2-EqValTy2-fwd` to move
-- the base branch `d Q`'s validity from `C Q Q (Ref Q)` onto the goal type
-- `C M N (Ref Q)`, then `Val2-beta-expand` lifts back to `J`.
--
-- Route-2 ownership (Coquand, 2026-07-05): built here as a standalone lemma so
-- the parallel terminal consumes `jTypeEq` instead of re-instantiating the
-- endpoint congruence in each hole.  Internally reuses the GREEN cross
-- combinator `JEndpoint.adqEq-motiveApp3` (3× App congruence) instantiated at
-- the triple-extended context, per NEXT_SESSION_ID.md session-16 recipe.
--
-- No postulates.  COMPLETE (2026-07-05): jTypeEq green, 0 holes.  Providers:
-- idTyValH/idTyValHgen (H-level Id validity), provDown/provDownEq (slots 0/1),
-- refLeftVal/refRightVal (slot-2 Ref-adequacy dispatch), assembled through
-- ValidSub2-extend×3 + fits³ + JRef.jEnd-instantiate.
------------------------------------------------------------------------

module ID.Adequacy.JTypeEq where

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; Bot ; UCode ; RefEl ; IdCode)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; App ; Id ; Ref ; Var ; fzero ; fsuc ;
  wkExpr ; Sub ; substExpr ; subst1 ; motiveTy ; baseTy)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; Comp ; FinMem ; FinMem-a-in-U)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ;
  ty-U ; ty-Id ; ty-Ref ; ty-var ; ty-conv ; wf-extend ; conv-refl ; conv-conv ; conv-sym ; conv-Id)
open import ID.Model.Eval using (EnvApprox ; EvalRel ; CoherentEnv ; extendEnv ; EvalRel-Comp ; EvalRel-down)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Adequacy.Pi using (Adq ; AdqConv ; EqVal2-U-to-EqValTy2 ; Val2-U-to-ValTy2)
open import ID.Adequacy.Helpers using (ValidSub2 ; ValidConvSub2 ; extSub ;
  ValidSub2-extend ; ValidConvSub2-extend ; ValidConvSub2-refl ; extSub-WtSub ; extSub-WtConvSub ;
  substExpr-wk ; Eq-trans)
open import ID.Adequacy.HeadRed
open import ID.Adequacy.JEndpoint using (adqEq-motiveApp3)
open import ID.Adequacy.JRef using (jEnd-instantiate ; epTransportVal2 ; epTransportEqVal2)
open import ID.Adequacy.Records using (mk-ValId ; mk-ValTyId ; mk-EqValId)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; wk-HasType ; typing-ConvTm)
open import ID.Syntax.Reduction using (headred-refl)
open import ID.Domain.Basic using (Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong)
open import ID.Domain.Kernel using (FinMem-coh-u ; coh-from-aU ; finMem-idU-dom ;
  finMem-idU-lhs ; finMem-idU-rhs ; LeCode-refl)
open import ID.Domain.Membership using (finMem-ref-wit ; finMem-ref-mk)
open import ID.Model.Eval using (lookupEnv)
open import ID.Model.EvalSubstitution using (EvalRel-unwk ; EvalRel-wk)

------------------------------------------------------------------------
-- idTyValH : the H-level  Id sA wit0 wit0 : U  type-validity at (IdCode t w w),
-- from the witness's own Val2 at (w,t).  (adequacy-ty-Id-core only builds this
-- for a SUBSTITUTED G-level endpoint; the J witness wit0 is a free H-term, so
-- we assemble the RValTyIdP record directly -- both endpoints wit0, reflexive.)
------------------------------------------------------------------------

idTyValH : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 : Expr h) -> HasType H wit0 (substExpr sigma A) ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H wit0 (substExpr sigma A) w t ->
  ValTy2 H (Id (substExpr sigma A) wit0 wit0) (IdCode t w w)
idTyValH {H = H} {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0 =
  mk-ValTyId (record
    { domA = substExpr sigma A ; lhs = wit0 ; rhs = wit0
    ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htWit0 htWit0))
    ; htA = htsA ; htL = htWit0 ; htR = htWit0
    ; valA = vtA ; valL = fm_w_t ; valR = fm_w_t
    ; valLlog = valWit0 ; valRlog = valWit0 })
  where
    htsA = subst-HasType wtsub wfH dA
    evU  = mkSigma tt (LeCode-refl UCode tt)
    vtA  = Val2-U-to-ValTy2 t fm_t_U
             (IHA sigma rho crho vs fits wtsub wfH t evT UCode evU fm_t_U)

------------------------------------------------------------------------
-- provDown / provDownEq : turn a FIXED endpoint value/equality at (w, t)
-- into the ValidSub2 / ValidConvSub2 slot provider over the domain A, moving
-- the type-value  t -> a'  (both evals of A in rho, hence Comp) via the JRef
-- epTransport primitives.
------------------------------------------------------------------------

provDown : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {M : Expr h} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H M (substExpr sigma A) w t ->
  (u' a' : FinEl) -> Coherent u' -> LeCode u' w ->
  EvalRel A rho a' -> FinMem u' a' ->
  Val2 H M (substExpr sigma A) u' a'
provDown {A = A} {M = M} dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valwt u' a' cu' le evA' fm' =
  epTransportVal2 w t valwt fm_w_t fm_t_U u' a' le comp fmA'U vtA' vtT fm'
  where
    evU  = mkSigma tt (LeCode-refl UCode tt)
    comp = EvalRel-Comp A rho crho a' t evA' evT
    fmA'U = FinMem-a-in-U u' a' fm'
    vtA' = Val2-U-to-ValTy2 a' fmA'U (IHA sigma rho crho vs fits wtsub wfH a' evA' UCode evU fmA'U)
    vtT  = Val2-U-to-ValTy2 t fm_t_U (IHA sigma rho crho vs fits wtsub wfH t evT UCode evU fm_t_U)

provDownEq : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {M N : Expr h} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  EqVal2 H M N (substExpr sigma A) w t ->
  (u' a' : FinEl) -> Coherent u' -> LeCode u' w ->
  EvalRel A rho a' -> FinMem u' a' ->
  EqVal2 H M N (substExpr sigma A) u' a'
provDownEq {A = A} {M = M} {N = N} dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U eqwt u' a' cu' le evA' fm' =
  epTransportEqVal2 w t eqwt fm_w_t fm_t_U u' a' le comp fmA'U vtA' vtT fm'
  where
    evU  = mkSigma tt (LeCode-refl UCode tt)
    comp = EvalRel-Comp A rho crho a' t evA' evT
    fmA'U = FinMem-a-in-U u' a' fm'
    vtA' = Val2-U-to-ValTy2 a' fmA'U (IHA sigma rho crho vs fits wtsub wfH a' evA' UCode evU fmA'U)
    vtT  = Val2-U-to-ValTy2 t fm_t_U (IHA sigma rho crho vs fits wtsub wfH t evT UCode evU fm_t_U)

------------------------------------------------------------------------
-- Triple-extension scaffolding: the endpoint congruence lives in the
-- context `extend³ G (A, A↑, Id A↑↑ Var1 Var0)` with the two substitutions
-- σ'' = extSub³ σ wit0 wit0 (Ref wit0)  and  σ''' = extSub³ σ sa sb (Ref wit0),
-- and env ρ'' = extendEnv³ ρ w w (RefEl w) (the SMALLER witness value w, so
-- both σ-sides' slot providers cap at it).
------------------------------------------------------------------------

extSub3 : {h g : Nat} -> Sub h g -> Expr h -> Expr h -> Expr h -> Sub h (suc (suc (suc g)))
extSub3 sigma x y z = extSub (extSub (extSub sigma x) y) z

extendEnv3 : {g : Nat} -> EnvApprox g -> FinEl -> FinEl -> FinEl -> EnvApprox (suc (suc (suc g)))
extendEnv3 rho x y z = extendEnv (extendEnv (extendEnv rho x) y) z

------------------------------------------------------------------------
-- idTyValHgen : the reflexive H-level Id validity at a GENERAL code
-- (IdCode t' l' r'), the endpoint validities supplied by provDown of the
-- witness Val2 (both endpoints are wit0).
------------------------------------------------------------------------

idTyValHgen : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (lhs rhs : Expr h) -> HasType H lhs (substExpr sigma A) -> HasType H rhs (substExpr sigma A) ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H lhs (substExpr sigma A) w t -> Val2 H rhs (substExpr sigma A) w t ->
  (t' l' r' : FinEl) -> EvalRel A rho t' -> FinMem t' UCode ->
  Coherent l' -> Coherent r' -> LeCode l' w -> LeCode r' w -> FinMem l' t' -> FinMem r' t' ->
  ValTy2 H (Id (substExpr sigma A) lhs rhs) (IdCode t' l' r')
idTyValHgen {A = A} dA IHA sigma rho crho vs fits wtsub wfH lhs rhs htL htR w t evT fm_w_t fm_t_U valLwt valRwt
  t' l' r' evT' fm_t'_U cohL' cohR' leL leR fm_l'_t' fm_r'_t' =
  mk-ValTyId (record
    { domA = substExpr sigma A ; lhs = lhs ; rhs = rhs
    ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htL htR))
    ; htA = htsA ; htL = htL ; htR = htR
    ; valA = vtA' ; valL = fm_l'_t' ; valR = fm_r'_t'
    ; valLlog = provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valLwt l' t' cohL' leL evT' fm_l'_t'
    ; valRlog = provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valRwt r' t' cohR' leR evT' fm_r'_t' })
  where
    htsA = subst-HasType wtsub wfH dA
    evU  = mkSigma tt (LeCode-refl UCode tt)
    vtA' = Val2-U-to-ValTy2 t' fm_t'_U (IHA sigma rho crho vs fits wtsub wfH t' evT' UCode evU fm_t'_U)

------------------------------------------------------------------------
-- refLeftVal : Val2 H (Ref wit0)(Id sA wit0 wit0) provider for the LEFT
-- σ'' slot-2.  Mirrors RefCase.adequacy-ty-Ref-full's dispatch (value u' and
-- type-code a'), the reflexive Id validity from idTyValHgen and the Val2
-- record built from the witness Val2 (endpoints wit0, reflexive endEqs).
-- The type-value a' is an eval of the slot domain in the doubly-extended env,
-- so its lhs/rhs bounds l',r' <= w come from the Var evaluations.
------------------------------------------------------------------------

refLeftVal : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 : Expr h) -> HasType H wit0 (substExpr sigma A) ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H wit0 (substExpr sigma A) w t ->
  (u' : FinEl) -> Coherent u' -> LeCode u' (RefEl w) ->
  (a' : FinEl) ->
  EvalRel (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero))
          (extendEnv (extendEnv rho w) w) a' ->
  FinMem u' a' ->
  Val2 H (Ref wit0) (Id (substExpr sigma A) wit0 wit0) u' a'
refLeftVal {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0
  Bot cu' le a' evId fm = Val2-Bot a'
refLeftVal dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0
  (RefEl w'') cu' le Bot evId fm = tt
refLeftVal {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0
  (RefEl w'') cu' le (IdCode t' l' r') evId fm =
  mk-ValId (idTyValHgen dA IHA sigma rho crho vs fits wtsub wfH wit0 wit0 htWit0 htWit0 w t evT fm_w_t fm_t_U valWit0 valWit0
              t' l' r' evT' fm_t'_U cohL' cohR' leL leR fm_l'_t' fm_r'_t')
    (record { domA0 = substExpr sigma A ; lhs0 = wit0 ; rhs0 = wit0
            ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htWit0 htWit0))
            ; wit0 = wit0 ; redTm = mkRed3 headred-refl (conv-refl (ty-Ref htsA htWit0))
            ; refConvL = conv-refl htWit0 ; refConvR = conv-refl htWit0 ; refMem = fm
            ; endEqL = endEqd ; endEqR = endEqd })
  where
    htsA = subst-HasType wtsub wfH dA
    leW'' = le              -- LeCode (RefEl w'') (RefEl w)  ==  LeCode w'' w
    evT' = EvalRel-unwk A rho w t'
             (EvalRel-unwk (wkExpr A) (extendEnv rho w) w t' (fst (snd evId)))
    leL   = snd (fst (snd (snd evId)))          -- LeCode l' w
    leR   = snd (snd (snd (snd evId)))          -- LeCode r' w
    fm_IdU   = FinMem-a-in-U (RefEl w'') (IdCode t' l' r') fm
    fm_t'_U  = finMem-idU-dom t' l' r' fm_IdU
    fm_l'_t' = finMem-idU-lhs t' l' r' fm_IdU
    fm_r'_t' = finMem-idU-rhs t' l' r' fm_IdU
    cohL' = FinMem-coh-u l' t' fm_l'_t'
    cohR' = FinMem-coh-u r' t' fm_r'_t'
    fm_w''_t' = finMem-ref-wit w'' t' l' r' fm
    valW''  = provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0
                w'' t' (FinMem-coh-u w'' t' fm_w''_t') leW'' evT' fm_w''_t'
    endEqd  = Val2-to-EqVal2 w'' t' valW''

------------------------------------------------------------------------
-- refRightVal : Val2 H (Ref wit0)(Id sA sa sb) provider for the RIGHT σ'''
-- slot-2.  Same reflexive value Ref wit0, but retyped from its natural type
-- Id sA wit0 wit0 to the endpoint type Id sA sa sb via the endpoint
-- conversions refConvL/refConvR (wit0 ~ sa, wit0 ~ sb) -- the RefCase rN
-- pattern.  Type validity: idTyValHgen with the asymmetric endpoints sa,sb.
------------------------------------------------------------------------

refRightVal : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 sa sb : Expr h) ->
  HasType H wit0 (substExpr sigma A) -> HasType H sa (substExpr sigma A) -> HasType H sb (substExpr sigma A) ->
  ConvTm H wit0 sa (substExpr sigma A) -> ConvTm H wit0 sb (substExpr sigma A) ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H sa (substExpr sigma A) w t -> Val2 H sb (substExpr sigma A) w t ->
  EqVal2 H wit0 sa (substExpr sigma A) w t -> EqVal2 H wit0 sb (substExpr sigma A) w t ->
  (u' : FinEl) -> Coherent u' -> LeCode u' (RefEl w) ->
  (a' : FinEl) ->
  EvalRel (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero))
          (extendEnv (extendEnv rho w) w) a' ->
  FinMem u' a' ->
  Val2 H (Ref wit0) (Id (substExpr sigma A) sa sb) u' a'
refRightVal {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 sa sb htWit0 htSa htSb refConvL refConvR
  w t evT fm_w_t fm_t_U valSaWt valSbWt endEqL endEqR
  Bot cu' le a' evId fm = Val2-Bot a'
refRightVal dA IHA sigma rho crho vs fits wtsub wfH wit0 sa sb htWit0 htSa htSb refConvL refConvR
  w t evT fm_w_t fm_t_U valSaWt valSbWt endEqL endEqR
  (RefEl w'') cu' le Bot evId fm = tt
refRightVal {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 sa sb htWit0 htSa htSb refConvL refConvR
  w t evT fm_w_t fm_t_U valSaWt valSbWt endEqL endEqR
  (RefEl w'') cu' le (IdCode t' l' r') evId fm =
  mk-ValId (idTyValHgen dA IHA sigma rho crho vs fits wtsub wfH sa sb htSa htSb w t evT fm_w_t fm_t_U valSaWt valSbWt
              t' l' r' evT' fm_t'_U cohL' cohR' leL leR fm_l'_t' fm_r'_t')
    (record { domA0 = substExpr sigma A ; lhs0 = sa ; rhs0 = sb
            ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htSa htSb))
            ; wit0 = wit0
            ; redTm = mkRed3 headred-refl (conv-conv (conv-refl (ty-Ref htsA htWit0)) cIdFwd (ty-Id htsA htSa htSb))
            ; refConvL = refConvL ; refConvR = refConvR ; refMem = fm
            ; endEqL = endEqLd ; endEqR = endEqRd })
  where
    htsA = subst-HasType wtsub wfH dA
    leW'' = le
    cIdFwd = conv-Id htsA htWit0 htWit0 (conv-refl htsA) refConvL refConvR
    evT' = EvalRel-unwk A rho w t'
             (EvalRel-unwk (wkExpr A) (extendEnv rho w) w t' (fst (snd evId)))
    leL   = snd (fst (snd (snd evId)))
    leR   = snd (snd (snd (snd evId)))
    fm_IdU   = FinMem-a-in-U (RefEl w'') (IdCode t' l' r') fm
    fm_t'_U  = finMem-idU-dom t' l' r' fm_IdU
    fm_l'_t' = finMem-idU-lhs t' l' r' fm_IdU
    fm_r'_t' = finMem-idU-rhs t' l' r' fm_IdU
    cohL' = FinMem-coh-u l' t' fm_l'_t'
    cohR' = FinMem-coh-u r' t' fm_r'_t'
    fm_w''_t' = finMem-ref-wit w'' t' l' r' fm
    cohW'' = FinMem-coh-u w'' t' fm_w''_t'
    endEqLd = provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqL w'' t' cohW'' leW'' evT' fm_w''_t'
    endEqRd = provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqR w'' t' cohW'' leW'' evT' fm_w''_t'

------------------------------------------------------------------------
-- jTypeEq : the modular motive-endpoint type equality.  Assembles the two
-- 3-slot extended substitutions (LEFT wit0,wit0,Ref wit0 ; RIGHT sa,sb,Ref wit0)
-- from the endpoint equalities, then calls JRef.jEnd-instantiate.  The App³
-- evaluation `ac` in the extended env is supplied by the caller (refCore).
------------------------------------------------------------------------

jTypeEq : {h g : Nat} {H : Ctx h} {G : Ctx g} {A C a b : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) -> HasType G a A -> HasType G b A ->
  Adq G A U -> AdqConv G A U -> AdqConv G C (motiveTy A) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 : Expr h) -> (w t : FinEl) -> Coherent w ->
  EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  EqVal2 H wit0 (substExpr sigma a) (substExpr sigma A) w t ->
  EqVal2 H wit0 (substExpr sigma b) (substExpr sigma A) w t ->
  ConvTm H wit0 (substExpr sigma a) (substExpr sigma A) ->
  ConvTm H wit0 (substExpr sigma b) (substExpr sigma A) ->
  (ac : FinEl) ->
  EvalRel (App (App (App (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero)))) (Var (fsuc fzero))) (Var fzero))
          (extendEnv (extendEnv (extendEnv rho w) w) (RefEl w)) ac ->
  FinMem ac UCode ->
  EqValTy2 H (App (App (App (substExpr sigma C) wit0) wit0) (Ref wit0))
             (App (App (App (substExpr sigma C) (substExpr sigma a)) (substExpr sigma b)) (Ref wit0)) ac
jTypeEq {H = H} {G = G} {A = A} {C = C} {a = a} {b = b}
  dA dC da db IHA IHcA IHcC sigma rho crho vs fits wtsub wfH wit0 w t cW evT fm_w_t fm_t_U
  endEqL endEqR refConvL refConvR ac evApp3 acU =
  jEnd-instantiate dA dC IHA IHcA IHcC sigma wit0 wit0 (Ref wit0) sa sb (Ref wit0) rho w w (RefEl w)
    crho3 vsL vsR vcs fits3 wtL wtR wcs wfH ac evApp3 acU
  where
    sA = substExpr sigma A ; sa = substExpr sigma a ; sb = substExpr sigma b
    htsA = subst-HasType wtsub wfH dA
    htSa = subst-HasType wtsub wfH da
    htSb = subst-HasType wtsub wfH db
    htWit0 = fst (typing-ConvTm refConvL)
    valWit0 = Val2-from-EqVal2-first w t endEqL
    valSa = Val2-from-EqVal2-second w t endEqL
    valSb = Val2-from-EqVal2-second w t endEqR
    cohT = coh-from-aU t fm_t_U
    -- weakened A typings for the Id-slot domain
    dwkA1 = wk-HasType dA dA
    dwkA2 = wk-HasType dwkA1 dwkA1
    dIdSlot = ty-Id dwkA2 (ty-var {i = fsuc fzero} (wf-extend dwkA1)) (ty-var {i = fzero} (wf-extend dwkA1))
    -- substExpr collapse eqs (peel weakenings under the 2-slot extended subs)
    wk2eqL : Eq (substExpr (extSub (extSub sigma wit0) wit0) (wkExpr (wkExpr A))) sA
    wk2eqL = Eq-trans (substExpr-wk (extSub sigma wit0) (wkExpr A) wit0) (substExpr-wk sigma A wit0)
    wk2eqR : Eq (substExpr (extSub (extSub sigma sa) sb) (wkExpr (wkExpr A))) sA
    wk2eqR = Eq-trans (substExpr-wk (extSub sigma sa) (wkExpr A) sb) (substExpr-wk sigma A sa)
    wk1eqL : Eq (substExpr (extSub sigma wit0) (wkExpr A)) sA
    wk1eqL = substExpr-wk sigma A wit0
    wk1eqR : Eq (substExpr (extSub sigma sa) (wkExpr A)) sA
    wk1eqR = substExpr-wk sigma A sa
    -- providers, LEFT sub
    provL0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0 u aa cu le ev fm
    provL1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H wit0 X u aa) (Eq-sym wk1eqL)
        (provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0 u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provL2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H (Ref wit0) (Id X wit0 wit0) u aa) (Eq-sym wk2eqL)
        (refLeftVal dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0 u cu le aa ev fm)
    vsL0 = ValidSub2-extend {A = A} sigma wit0 rho w vs provL0
    vsL1 = ValidSub2-extend {A = wkExpr A} (extSub sigma wit0) wit0 (extendEnv rho w) w vsL0 provL1
    vsL  = ValidSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma wit0) wit0) (Ref wit0) (extendEnv (extendEnv rho w) w) (RefEl w) vsL1 provL2
    -- providers, RIGHT sub
    provR0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valSa u aa cu le ev fm
    provR1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H sb X u aa) (Eq-sym wk1eqR)
        (provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valSb u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provR2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H (Ref wit0) (Id X sa sb) u aa) (Eq-sym wk2eqR)
        (refRightVal dA IHA sigma rho crho vs fits wtsub wfH wit0 sa sb htWit0 htSa htSb refConvL refConvR
          w t evT fm_w_t fm_t_U valSa valSb endEqL endEqR u cu le aa ev fm)
    vsR0 = ValidSub2-extend {A = A} sigma sa rho w vs provR0
    vsR1 = ValidSub2-extend {A = wkExpr A} (extSub sigma sa) sb (extendEnv rho w) w vsR0 provR1
    vsR  = ValidSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma sa) sb) (Ref wit0) (extendEnv (extendEnv rho w) w) (RefEl w) vsR1 provR2
    -- cross providers
    provX0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqL u aa cu le ev fm
    provX1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> EqVal2 H wit0 sb X u aa) (Eq-sym wk1eqL)
        (provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqR u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provX2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Val2-to-EqVal2 u aa
        (Eq-transport (\ X -> Val2 H (Ref wit0) (Id X wit0 wit0) u aa) (Eq-sym wk2eqL)
          (refLeftVal dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0 u cu le aa ev fm))
    vcs0 = ValidConvSub2-extend {A = A} sigma sigma wit0 sa rho w (ValidConvSub2-refl {G = G} vs) provX0
    vcs1 = ValidConvSub2-extend {A = wkExpr A} (extSub sigma wit0) (extSub sigma sa) wit0 sb (extendEnv rho w) w vcs0 provX1
    vcs  = ValidConvSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma wit0) wit0) (extSub (extSub sigma sa) sb) (Ref wit0) (Ref wit0)
             (extendEnv (extendEnv rho w) w) (RefEl w) vcs1 provX2
    -- fits / coherence
    lerefl = LeCode-refl w cW
    evT-wk1 = EvalRel-wk A rho w t evT
    evT-wk2 = EvalRel-wk (wkExpr A) (extendEnv rho w) w t evT-wk1
    fm_RefW = finMem-ref-mk w t w w cW fm_w_t lerefl lerefl fm_t_U fm_w_t fm_w_t
    evIdSlot = mkSigma (mkSigma cohT (mkSigma cW cW))
                 (mkSigma evT-wk2 (mkSigma (mkSigma cW lerefl) (mkSigma cW lerefl)))
    fits3 = mkSigma (mkSigma (mkSigma fits (mkSigma t (mkSigma fm_w_t evT)))
                             (mkSigma t (mkSigma fm_w_t evT-wk1)))
                    (mkSigma (IdCode t w w) (mkSigma fm_RefW evIdSlot))
    crho3 = mkSigma (mkSigma (mkSigma crho cW) cW) cW
    -- well-typed subs (LEFT)
    htWit0-1 = Eq-transport (\ X -> HasType H wit0 X) (Eq-sym wk1eqL) htWit0
    htRefWit0L = ty-Ref (Eq-transport (\ X -> HasType H X U) (Eq-sym wk2eqL) htsA)
                        (Eq-transport (\ X -> HasType H wit0 X) (Eq-sym wk2eqL) htWit0)
    wtL0 = extSub-WtSub wtsub wfH dA htWit0
    wtL1 = extSub-WtSub wtL0 wfH dwkA1 htWit0-1
    wtL  = extSub-WtSub wtL1 wfH dIdSlot htRefWit0L
    -- well-typed subs (RIGHT)
    htSa-1 = Eq-transport (\ X -> HasType H sa X) (Eq-sym wk1eqR) htSa
    htSb-1 = Eq-transport (\ X -> HasType H sb X) (Eq-sym wk1eqR) htSb
    cIdFwd = conv-Id htsA htWit0 htWit0 (conv-refl htsA) refConvL refConvR
    htRefWit0R = Eq-transport (\ X -> HasType H (Ref wit0) (Id X sa sb)) (Eq-sym wk2eqR)
                   (ty-conv (ty-Ref htsA htWit0) cIdFwd (ty-Id htsA htSa htSb))
    wtR0 = extSub-WtSub wtsub wfH dA htSa
    wtR1 = extSub-WtSub wtR0 wfH dwkA1 htSb-1
    wtR  = extSub-WtSub wtR1 wfH dIdSlot htRefWit0R
    -- well-typed conversion sub
    cvWit0-1 = Eq-transport (\ X -> ConvTm H wit0 sa X) (Eq-sym wk1eqL) refConvL
    cvRef = conv-refl htRefWit0L
    wcs0 = extSub-WtConvSub wtsub (\ i -> conv-refl (wtsub i)) wfH dA refConvL
    wcs1 = extSub-WtConvSub wtL0 wcs0 wfH dwkA1 (Eq-transport (\ X -> ConvTm H wit0 sb X) (Eq-sym wk1eqL) refConvR)
    wcs  = extSub-WtConvSub wtL1 wcs1 wfH dIdSlot cvRef

------------------------------------------------------------------------
-- refSpCross : the CROSS provider (Ref wit0 ~ sp) at the LEFT slot-2 domain
-- Id sA wit0 wit0, for the proof-slot-general endpoint bridge jTypeEqSp.
-- LEFT term = Ref wit0 (reflexive record, as refLeftVal); RIGHT term = the
-- general proof sp, which head-reduces to Ref wit0 (redTm) -- so both records
-- carry the witness's reflexive endEqs and mk-EqValId glues them.
------------------------------------------------------------------------

refSpCross : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  HasType G A U -> Adq G A U ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 sp : Expr h) -> HasType H wit0 (substExpr sigma A) ->
  Red3 H sp (Ref wit0) (Id (substExpr sigma A) wit0 wit0) ->
  (w t : FinEl) -> EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  Val2 H wit0 (substExpr sigma A) w t ->
  (u' : FinEl) -> Coherent u' -> LeCode u' (RefEl w) ->
  (a' : FinEl) ->
  EvalRel (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero))
          (extendEnv (extendEnv rho w) w) a' ->
  FinMem u' a' ->
  EqVal2 H (Ref wit0) sp (Id (substExpr sigma A) wit0 wit0) u' a'
refSpCross {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 sp htWit0 redSp w t evT fm_w_t fm_t_U valWit0
  Bot cu' le a' evId fm = EqVal2-Bot a'
refSpCross dA IHA sigma rho crho vs fits wtsub wfH wit0 sp htWit0 redSp w t evT fm_w_t fm_t_U valWit0
  (RefEl w'') cu' le Bot evId fm = tt
refSpCross {A = A} dA IHA sigma rho crho vs fits wtsub wfH wit0 sp htWit0 redSp w t evT fm_w_t fm_t_U valWit0
  (RefEl w'') cu' le (IdCode t' l' r') evId fm =
  mk-EqValId (idTyValHgen dA IHA sigma rho crho vs fits wtsub wfH wit0 wit0 htWit0 htWit0 w t evT fm_w_t fm_t_U valWit0 valWit0
                t' l' r' evT' fm_t'_U cohL' cohR' leL leR fm_l'_t' fm_r'_t')
    rM rN rEq
  where
    htsA = subst-HasType wtsub wfH dA
    leW'' = le
    evT' = EvalRel-unwk A rho w t'
             (EvalRel-unwk (wkExpr A) (extendEnv rho w) w t' (fst (snd evId)))
    leL   = snd (fst (snd (snd evId)))
    leR   = snd (snd (snd (snd evId)))
    fm_IdU   = FinMem-a-in-U (RefEl w'') (IdCode t' l' r') fm
    fm_t'_U  = finMem-idU-dom t' l' r' fm_IdU
    fm_l'_t' = finMem-idU-lhs t' l' r' fm_IdU
    fm_r'_t' = finMem-idU-rhs t' l' r' fm_IdU
    cohL' = FinMem-coh-u l' t' fm_l'_t'
    cohR' = FinMem-coh-u r' t' fm_r'_t'
    fm_w''_t' = finMem-ref-wit w'' t' l' r' fm
    valW''  = provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0
                w'' t' (FinMem-coh-u w'' t' fm_w''_t') leW'' evT' fm_w''_t'
    endEqd  = Val2-to-EqVal2 w'' t' valW''
    redRef  = mkRed3 headred-refl (conv-refl (ty-Ref htsA htWit0))
    rM  = record { domA0 = substExpr sigma A ; lhs0 = wit0 ; rhs0 = wit0
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htWit0 htWit0))
                 ; wit0 = wit0 ; redTm = redRef ; refConvL = conv-refl htWit0 ; refConvR = conv-refl htWit0 ; refMem = fm
                 ; endEqL = endEqd ; endEqR = endEqd }
    rN  = record { domA0 = substExpr sigma A ; lhs0 = wit0 ; rhs0 = wit0
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htWit0 htWit0))
                 ; wit0 = wit0 ; redTm = redSp ; refConvL = conv-refl htWit0 ; refConvR = conv-refl htWit0 ; refMem = fm
                 ; endEqL = endEqd ; endEqR = endEqd }
    rEq = record { domA0 = substExpr sigma A ; lhs0 = wit0 ; rhs0 = wit0
                 ; red = mkRed3 headred-refl (conv-refl (ty-Id htsA htWit0 htWit0))
                 ; wit0M = wit0 ; wit0N = wit0 ; redTmM = redRef ; redTmN = redSp ; refMem = fm
                 ; endEqLM = endEqd ; endEqRM = endEqd ; endEqLN = endEqd ; endEqRN = endEqd }

------------------------------------------------------------------------
-- jTypeEqSp : the motive-endpoint type equality with a GENERAL proof term
-- sp in the RIGHT proof slot (jTypeEq fixes it to Ref wit0).  refCore's goal
-- type is App³ sC sa sb sp (the substituted proof), so this is the version it
-- actually consumes.  Identical to jTypeEq except:
--   * RIGHT slot-2 term = sp (reduces to Ref wit0 via redTm), its Val2
--     provider = Val2-beta-expand of refRightVal along redTm;
--   * CROSS slot-2 = refSpCross (Ref wit0 ~ sp);
--   * WtSub/WtConvSub slot-2 use sp's typing / (Ref wit0 ~ sp) conversion.
------------------------------------------------------------------------

jTypeEqSp : {h g : Nat} {H : Ctx h} {G : Ctx g} {A C a b : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) -> HasType G a A -> HasType G b A ->
  Adq G A U -> AdqConv G A U -> AdqConv G C (motiveTy A) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (wit0 : Expr h) -> (w t : FinEl) -> Coherent w ->
  EvalRel A rho t -> FinMem w t -> FinMem t UCode ->
  EqVal2 H wit0 (substExpr sigma a) (substExpr sigma A) w t ->
  EqVal2 H wit0 (substExpr sigma b) (substExpr sigma A) w t ->
  ConvTm H wit0 (substExpr sigma a) (substExpr sigma A) ->
  ConvTm H wit0 (substExpr sigma b) (substExpr sigma A) ->
  (sp : Expr h) ->
  Red3 H sp (Ref wit0) (Id (substExpr sigma A) (substExpr sigma a) (substExpr sigma b)) ->
  (ac : FinEl) ->
  EvalRel (App (App (App (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero)))) (Var (fsuc fzero))) (Var fzero))
          (extendEnv (extendEnv (extendEnv rho w) w) (RefEl w)) ac ->
  FinMem ac UCode ->
  EqValTy2 H (App (App (App (substExpr sigma C) wit0) wit0) (Ref wit0))
             (App (App (App (substExpr sigma C) (substExpr sigma a)) (substExpr sigma b)) sp) ac
jTypeEqSp {H = H} {G = G} {A = A} {C = C} {a = a} {b = b}
  dA dC da db IHA IHcA IHcC sigma rho crho vs fits wtsub wfH wit0 w t cW evT fm_w_t fm_t_U
  endEqL endEqR refConvL refConvR sp redTm ac evApp3 acU =
  jEnd-instantiate dA dC IHA IHcA IHcC sigma wit0 wit0 (Ref wit0) sa sb sp rho w w (RefEl w)
    crho3 vsL vsR vcs fits3 wtL wtR wcs wfH ac evApp3 acU
  where
    sA = substExpr sigma A ; sa = substExpr sigma a ; sb = substExpr sigma b
    htsA = subst-HasType wtsub wfH dA
    htSa = subst-HasType wtsub wfH da
    htSb = subst-HasType wtsub wfH db
    htWit0 = fst (typing-ConvTm refConvL)
    htSp   = fst (typing-ConvTm (Red3.ct redTm))
    valWit0 = Val2-from-EqVal2-first w t endEqL
    valSa = Val2-from-EqVal2-second w t endEqL
    valSb = Val2-from-EqVal2-second w t endEqR
    cohT = coh-from-aU t fm_t_U
    dwkA1 = wk-HasType dA dA
    dwkA2 = wk-HasType dwkA1 dwkA1
    dIdSlot = ty-Id dwkA2 (ty-var {i = fsuc fzero} (wf-extend dwkA1)) (ty-var {i = fzero} (wf-extend dwkA1))
    wk2eqL : Eq (substExpr (extSub (extSub sigma wit0) wit0) (wkExpr (wkExpr A))) sA
    wk2eqL = Eq-trans (substExpr-wk (extSub sigma wit0) (wkExpr A) wit0) (substExpr-wk sigma A wit0)
    wk2eqR : Eq (substExpr (extSub (extSub sigma sa) sb) (wkExpr (wkExpr A))) sA
    wk2eqR = Eq-trans (substExpr-wk (extSub sigma sa) (wkExpr A) sb) (substExpr-wk sigma A sa)
    wk1eqL : Eq (substExpr (extSub sigma wit0) (wkExpr A)) sA
    wk1eqL = substExpr-wk sigma A wit0
    wk1eqR : Eq (substExpr (extSub sigma sa) (wkExpr A)) sA
    wk1eqR = substExpr-wk sigma A sa
    -- redTm retyped to the reflexive Id sA wit0 wit0 (for refSpCross / cross conv)
    cIdBack = conv-Id htsA htSa htSb (conv-refl htsA) (conv-sym refConvL) (conv-sym refConvR)
    redTmW  = mkRed3 (Red3.hr redTm) (conv-conv (Red3.ct redTm) cIdBack (ty-Id htsA htWit0 htWit0))
    -- providers, LEFT sub (identical to jTypeEq)
    provL0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0 u aa cu le ev fm
    provL1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H wit0 X u aa) (Eq-sym wk1eqL)
        (provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valWit0 u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provL2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H (Ref wit0) (Id X wit0 wit0) u aa) (Eq-sym wk2eqL)
        (refLeftVal dA IHA sigma rho crho vs fits wtsub wfH wit0 htWit0 w t evT fm_w_t fm_t_U valWit0 u cu le aa ev fm)
    vsL0 = ValidSub2-extend {A = A} sigma wit0 rho w vs provL0
    vsL1 = ValidSub2-extend {A = wkExpr A} (extSub sigma wit0) wit0 (extendEnv rho w) w vsL0 provL1
    vsL  = ValidSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma wit0) wit0) (Ref wit0) (extendEnv (extendEnv rho w) w) (RefEl w) vsL1 provL2
    -- providers, RIGHT sub (slot-2 = sp via head-expand of refRightVal)
    provR0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valSa u aa cu le ev fm
    provR1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H sb X u aa) (Eq-sym wk1eqR)
        (provDown dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U valSb u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provR2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> Val2 H sp (Id X sa sb) u aa) (Eq-sym wk2eqR)
        (Val2-beta-expand u aa (Red3.hr redTm) (Red3.ct redTm)
          (refRightVal dA IHA sigma rho crho vs fits wtsub wfH wit0 sa sb htWit0 htSa htSb refConvL refConvR
            w t evT fm_w_t fm_t_U valSa valSb endEqL endEqR u cu le aa ev fm))
    vsR0 = ValidSub2-extend {A = A} sigma sa rho w vs provR0
    vsR1 = ValidSub2-extend {A = wkExpr A} (extSub sigma sa) sb (extendEnv rho w) w vsR0 provR1
    vsR  = ValidSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma sa) sb) sp (extendEnv (extendEnv rho w) w) (RefEl w) vsR1 provR2
    -- cross providers (slot-2 = refSpCross : Ref wit0 ~ sp)
    provX0 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqL u aa cu le ev fm
    provX1 = \ (u : FinEl) cu (le : LeCode u w) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> EqVal2 H wit0 sb X u aa) (Eq-sym wk1eqL)
        (provDownEq dA IHA sigma rho crho vs fits wtsub wfH w t evT fm_w_t fm_t_U endEqR u aa cu le
          (EvalRel-unwk A rho w aa ev) fm)
    provX2 = \ (u : FinEl) cu (le : LeCode u (RefEl w)) (aa : FinEl) ev fm ->
      Eq-transport (\ X -> EqVal2 H (Ref wit0) sp (Id X wit0 wit0) u aa) (Eq-sym wk2eqL)
        (refSpCross dA IHA sigma rho crho vs fits wtsub wfH wit0 sp htWit0 redTmW
          w t evT fm_w_t fm_t_U valWit0 u cu le aa ev fm)
    vcs0 = ValidConvSub2-extend {A = A} sigma sigma wit0 sa rho w (ValidConvSub2-refl {G = G} vs) provX0
    vcs1 = ValidConvSub2-extend {A = wkExpr A} (extSub sigma wit0) (extSub sigma sa) wit0 sb (extendEnv rho w) w vcs0 provX1
    vcs  = ValidConvSub2-extend {A = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)}
             (extSub (extSub sigma wit0) wit0) (extSub (extSub sigma sa) sb) (Ref wit0) sp
             (extendEnv (extendEnv rho w) w) (RefEl w) vcs1 provX2
    -- fits / coherence (identical to jTypeEq)
    lerefl = LeCode-refl w cW
    evT-wk1 = EvalRel-wk A rho w t evT
    evT-wk2 = EvalRel-wk (wkExpr A) (extendEnv rho w) w t evT-wk1
    fm_RefW = finMem-ref-mk w t w w cW fm_w_t lerefl lerefl fm_t_U fm_w_t fm_w_t
    evIdSlot = mkSigma (mkSigma cohT (mkSigma cW cW))
                 (mkSigma evT-wk2 (mkSigma (mkSigma cW lerefl) (mkSigma cW lerefl)))
    fits3 = mkSigma (mkSigma (mkSigma fits (mkSigma t (mkSigma fm_w_t evT)))
                             (mkSigma t (mkSigma fm_w_t evT-wk1)))
                    (mkSigma (IdCode t w w) (mkSigma fm_RefW evIdSlot))
    crho3 = mkSigma (mkSigma (mkSigma crho cW) cW) cW
    -- well-typed subs (LEFT, identical to jTypeEq)
    htWit0-1 = Eq-transport (\ X -> HasType H wit0 X) (Eq-sym wk1eqL) htWit0
    htRefWit0L = ty-Ref (Eq-transport (\ X -> HasType H X U) (Eq-sym wk2eqL) htsA)
                        (Eq-transport (\ X -> HasType H wit0 X) (Eq-sym wk2eqL) htWit0)
    wtL0 = extSub-WtSub wtsub wfH dA htWit0
    wtL1 = extSub-WtSub wtL0 wfH dwkA1 htWit0-1
    wtL  = extSub-WtSub wtL1 wfH dIdSlot htRefWit0L
    -- well-typed subs (RIGHT, slot-2 = sp : Id sA sa sb)
    htSa-1 = Eq-transport (\ X -> HasType H sa X) (Eq-sym wk1eqR) htSa
    htSb-1 = Eq-transport (\ X -> HasType H sb X) (Eq-sym wk1eqR) htSb
    htSp-2 = Eq-transport (\ X -> HasType H sp (Id X sa sb)) (Eq-sym wk2eqR) htSp
    wtR0 = extSub-WtSub wtsub wfH dA htSa
    wtR1 = extSub-WtSub wtR0 wfH dwkA1 htSb-1
    wtR  = extSub-WtSub wtR1 wfH dIdSlot htSp-2
    -- well-typed conversion sub (slot-2 = Ref wit0 ~ sp)
    cvRefSp = Eq-transport (\ X -> ConvTm H (Ref wit0) sp (Id X wit0 wit0)) (Eq-sym wk2eqL)
                (conv-sym (Red3.ct redTmW))
    wcs0 = extSub-WtConvSub wtsub (\ i -> conv-refl (wtsub i)) wfH dA refConvL
    wcs1 = extSub-WtConvSub wtL0 wcs0 wfH dwkA1 (Eq-transport (\ X -> ConvTm H wit0 sb X) (Eq-sym wk1eqL) refConvR)
    wcs  = extSub-WtConvSub wtL1 wcs1 wfH dIdSlot cvRefSp
