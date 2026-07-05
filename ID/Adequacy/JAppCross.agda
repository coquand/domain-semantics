{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JAppCross.agda
--
-- The based-J CROSS driver (adequacyVE-ty-J), the ty-J case of Theorem 2's
-- adequacyConvSub2 (two substitutions sigma, sigma').  EqVal2 mirror of
-- Adequacy.JApp.adequacyV-ty-J: the proof record now yields TWO witnesses
-- wit0M (from sigma p) and wit0N (from sigma' p); each side head-reduces
-- (J .. sp ->* App sd wit0M ; J .. sp' ->* App sd' wit0N) and the contracta
-- EqVal2 is closed by EqVal2-headred-expand.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JAppCross where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import ID.Adequacy.App using (app-transport-Val2 ; app-transport-EqVal2)
open import ID.Adequacy.JMotive using (adq-motiveApp3)
open import ID.Adequacy.JTypeEq using (jTypeEqSp)
open import ID.Adequacy.JApp using (adequacyV-ty-J ; conv-App3-endpoints)
open import ID.Adequacy.Records using (RValPiP ; un-ValPi ; RValIdP ; un-ValId ;
  REqValPiP ; un-REqValPi ; eqvalPi-snd ; REqValIdP ; un-EqValId)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; Sigma ; Pair ; nil ; cons ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ;
  Eq ; refl ; Eq-cong ; Eq-transport ; Eq-sym)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ; FinMem-coh-u ;
  FinMem-a-in-U ; Coherent ; coh-from-aU ; finMem-bot-from ; cft-from-cf ;
  EvalFun ; EvalFun-in-UCode ; Coherent-EvalFun ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ; finMem-ref-wit ;
  finMem-ref-le1 ; finMem-ref-le2)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; lookupEnv ; EvalRel ; EvalRel-coh ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe-refl ; EvalRel-Comp ; CoherentEnv ; JBranch)
open import ID.Model.EvalSubstitution using (EvalRel-wk ; EvalRel-unwk ; EvalRel-Pi-body ;
  EvalRel-subst1-backward)
open import ID.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val)
open import ID.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import ID.Model.Selection using (selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; App ; Id ; Ref ; J ; Var ; fzero ; fsuc ;
  Sub ; liftSub ; substExpr ; subst1 ; subst1Sub ; wkExpr ; wkRen ;
  motiveTy ; baseTy ; subst-motiveTy ; subst-baseTy ; subst-wk-comm ;
  Eq-cong ; Eq-cong2-Expr ; Eq-cong3-Expr)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-U ; ty-var ; ty-Ref ; ty-App ; ty-Id ; ty-Pi ; ty-J ; ty-conv ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Id ; conv-Pi ; conv-App-fun ; conv-App-arg ;
  conv-Ref ; conv-J ; conv-J-beta)
open import ID.Syntax.Reduction using (HeadRed ; headred-refl ; headred-step ; headred-J ;
  HeadRed-trans ; HeadRed-J ; HeadRed-Id-refl ; Red ; mkRed ; Red-refl)
open import ID.Model.Soundness using (theorem1)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm ;
  typing-ConvTm ; typing-WfCtx ; typing-type ; wk-HasType ; wk-ConvTm ; subst1-wk ;
  motiveTail-formation ; conv-motiveApp3 ; subst-ConvTm-cross)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Validity.Stratified using (Red3 ; mkRed3)
open import ID.Validity.Public using (EqVal2-trans)

------------------------------------------------------------------------
-- jHeadConv : the per-substitution head-expansion conversion for based J.
-- H-level (substitution-agnostic) copy of Adequacy.JApp.adequacyV-ty-J's
-- `ctJ`: given the substituted typings of A/a/b/C/d/p at H, a witness wit0
-- with wit0 ~ sa ~ sb : sA and the proof reduction sp ~ Ref wit0, produces
--   ConvTm (J sC sd sp) (App sd wit0) (App (App (App sC sa) sb) sp).
-- Used TWICE below (LEFT with sigma, RIGHT with sigma').
------------------------------------------------------------------------

jHeadConv : {h : Nat} {H : Ctx h} {sA sa sb sC sd sp : Expr h} ->
  HasType H sA U -> HasType H sa sA -> HasType H sb sA ->
  HasType H sC (motiveTy sA) -> HasType H sd (baseTy sA sC) -> HasType H sp (Id sA sa sb) ->
  (wit0 : Expr h) -> HasType H wit0 sA ->
  ConvTm H sp (Ref wit0) (Id sA sa sb) ->
  ConvTm H wit0 sa sA -> ConvTm H wit0 sb sA ->
  ConvTm H (J sC sd sp) (App sd wit0) (App (App (App sC sa) sb) sp)
jHeadConv {H = H} {sA = sA} {sa = sa} {sb = sb} {sC = sC} {sd = sd} {sp = sp}
  htsA htSa htSb htsC htsd htSp wit0 htWit0 cvSpRef refConvL refConvR =
  conv-trans
    (conv-J htsA htSa htSb htsC htsd htSp (conv-refl htsC) (conv-refl htsd) cvSpRef)
    (conv-conv jbetaConv typeConv typedGoal)
  where
    jbetaConv : ConvTm H (J sC sd (Ref wit0)) (App sd wit0)
                  (App (App (App sC wit0) wit0) (Ref wit0))
    jbetaConv = conv-J-beta htsA htWit0 htsC htsd
    typedGoal : HasType H (App (App (App sC sa) sb) sp) U
    typedGoal = typing-type (ty-J htsA htSa htSb htsC htsd htSp)
    typeConv : ConvTm H (App (App (App sC wit0) wit0) (Ref wit0))
                        (App (App (App sC sa) sb) sp) U
    typeConv = conv-trans partP partAB
      where
        cIdBack : ConvTm H (Id sA sa sb) (Id sA wit0 wit0) U
        cIdBack = conv-Id htsA htSa htSb (conv-refl htsA) (conv-sym refConvL) (conv-sym refConvR)
        convP-in : ConvTm H (Ref wit0) sp (Id sA wit0 wit0)
        convP-in = conv-sym (conv-conv cvSpRef cIdBack (ty-Id htsA htWit0 htWit0))
        partP : ConvTm H (App (App (App sC wit0) wit0) (Ref wit0))
                         (App (App (App sC wit0) wit0) sp) U
        partP = conv-motiveApp3 htsA htsC htsC (conv-refl htsC) htWit0 htWit0
                  (ty-Ref htsA htWit0) convP-in
        dpSp : HasType H sp (Id sA wit0 wit0)
        dpSp = ty-conv htSp cIdBack (ty-Id htsA htWit0 htWit0)
        partAB : ConvTm H (App (App (App sC wit0) wit0) sp)
                          (App (App (App sC sa) sb) sp) U
        partAB = conv-App3-endpoints htsA htsC htWit0 htSa htWit0 htSb dpSp refConvL refConvR

------------------------------------------------------------------------
-- adequacyVE-ty-J
------------------------------------------------------------------------

adequacyVE-ty-J : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b C d p : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> HasType G C (motiveTy A) ->
  HasType G d (baseTy A C) -> HasType G p (Id A a b) ->
  Adq G A U -> AdqConv G A U -> Adq G a A -> Adq G b A ->
  Adq G C (motiveTy A) -> AdqConv G C (motiveTy A) ->
  Adq G d (baseTy A C) -> AdqConv G d (baseTy A C) ->
  Adq G p (Id A a b) -> AdqConv G p (Id A a b) ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (J C d p) rho u ->
  (at : FinEl) -> EvalRel (App (App (App C a) b) p) rho at -> FinMem u at ->
  EqVal2 H (substExpr sigma (J C d p))
           (substExpr sigma' (J C d p))
           (substExpr sigma (App (App (App C a) b) p)) u at
-- IMPLEMENTATION PLAN (interface above is VALIDATED — compiles as a stub).
-- Mirror Adequacy.JApp.adequacyV-ty-J shell (branch / dispatchId / branchBot),
-- upgraded Val2 -> EqVal2:
--   * proof record: valP0 = IHp .. -> un-ValId gives ONE witness; but for the
--     cross use the PROOF CROSS `IHcp sigma sigma' .. (RefEl w'') evP' (IdCode
--     t' l' r') evId fm_w'` -> `un-EqValId` -> REqValIdP with TWO witnesses
--     wit0M (sigma p side), wit0N (sigma' p side), redTmM/redTmN, and the four
--     endEqs endEqLM/RM/LN/RN.  HeadRed-Id-refl on `red` strips (sA,sa,sb).
--   * two head reductions hrJ-L : HeadRed (sigma J..) (App sd wit0M),
--     hrJ-R : HeadRed (sigma' J..) (App sd' wit0N)  (redTmM / redTmN).
--   * two conversions ctJ-L / ctJ-R : each a copy of JApp's ctJ (conv-J +
--     conv-conv jbeta typeConv typedGoal) on its own witness; the RIGHT one
--     also needs the CROSS type conversion sigma'(App3) ~ sigma(App3) via
--     `subst-ConvTm-cross` on ty-J's result type (mirror NAT cvTypeRL).
--   * cross d-edge (THE CRUX ~100 lines, port NAT adequacyVE-app-Nat-dep
--     appEqVal-dispatch): NL:=wit0M, NR:=wit0N, sf:=sd, FR:=sd'.
--       - fun-variation  EqVal2 (App sd wit0M)(App sd' wit0M) via un-REqValPi
--         (IHcd d-edge) . appEV @ P=wit0M ;
--       - arg-variation  EqVal2 (App sd' wit0M)(App sd' wit0N) via
--         eqvalPi-snd (N-side RValPiP) . appE @ (wit0M,wit0N) ;
--       - combine with EqVal2-trans ; then jTypeEqSp type-transport
--         (reuse the workerA/workerC reshape from JApp — factor them out or
--         re-derive) + app-transport-EqVal2 (v_sel,ef_usel -> u,at).
--         argEq (EqVal2 wit0M wit0N sA) = EqVal2-trans endEqLM (sym endEqLN);
--         cvNLNR (ConvTm wit0M wit0N sA) from the endEqs' conversions.
--   * close with EqVal2-headred-expand u at hrJ-L hrJ-R ctJ-L ctJ-R (d-edge).
--   * Bot branch: restrictEqVal2 + EqVal2-Bot (mirror branchBot).
adequacyVE-ty-J {H = H} {G = G} {A = A} {a = a} {b = b} {C = C} {d = d} {p = p}
  dA da db dC dd dp IHA IHcA IHa IHb IHC IHcC IHd IHcd IHp IHcp
  sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu at evA fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sC = substExpr sigma C ; sd = substExpr sigma d ; sp = substExpr sigma p
    sC' = substExpr sigma' C ; sd' = substExpr sigma' d ; sp' = substExpr sigma' p
    sA = substExpr sigma A ; sa = substExpr sigma a ; sb = substExpr sigma b
    sA' = substExpr sigma' A ; sa' = substExpr sigma' a ; sb' = substExpr sigma' b
    at_U = FinMem-a-in-U u at fm
    wfG  = typing-WfCtx dp
    htsA = subst-HasType wtsub wfH dA
    htSa = subst-HasType wtsub wfH da
    htSb = subst-HasType wtsub wfH db
    htsC = Eq-transport (\ T -> HasType H sC T) (subst-motiveTy sigma A) (subst-HasType wtsub wfH dC)
    htsd = Eq-transport (\ T -> HasType H sd T) (subst-baseTy sigma A C) (subst-HasType wtsub wfH dd)
    htSp = subst-HasType wtsub wfH dp
    -- RIGHT (sigma') typings
    htsA' = subst-HasType wtsub' wfH dA
    htSa' = subst-HasType wtsub' wfH da
    htSb' = subst-HasType wtsub' wfH db
    htsC' = Eq-transport (\ T -> HasType H sC' T) (subst-motiveTy sigma' A) (subst-HasType wtsub' wfH dC)
    htsd' = Eq-transport (\ T -> HasType H sd' T) (subst-baseTy sigma' A C) (subst-HasType wtsub' wfH dd)
    htSp' = subst-HasType wtsub' wfH dp
    evU  = mkSigma tt (LeCode-refl UCode tt)
    typedGoalσ : HasType H (App (App (App sC sa) sb) sp) U
    typedGoalσ = subst-HasType wtsub wfH (typing-type (ty-J dA da db dC dd dp))
    -- cross type conversion  App³ sC' sa' sb' sp' ~ App³ sC sa sb sp : U
    cvTypeRL : ConvTm H (App (App (App sC' sa') sb') sp') (App (App (App sC sa) sb) sp) U
    cvTypeRL = conv-sym (subst-ConvTm-cross (typing-type (ty-J dA da db dC dd dp)) wtsub wtsub' wcs wfH)

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      EqVal2 H (J sC sd sp) (J sC' sd' sp') (App (App (App sC sa) sb) sp) u at
    branchBot jb =
      restrictEqVal2 H (J sC sd sp) (J sC' sd' sp') (App (App (App sC sa) sb) sp) Bot u at (snd jb) fm
        (finMem-bot-from at at_U) (EqVal2-Bot at)

    refCore : (wit : FinEl) -> EvalRel p rho (RefEl wit) ->
      EvalRel d rho (FunEl (cons (mkSigma wit u) nil)) ->
      EqVal2 H (J sC sd sp) (J sC' sd' sp') (App (App (App sC sa) sb) sp) u at
    refCore wit evP jb =
      dispatchId (fst typed_p) (fst (snd typed_p)) (fst (snd (snd typed_p)))
                 (fst (snd (snd (snd typed_p)))) (fst (snd (snd (snd (snd typed_p)))))
                 (snd (snd (snd (snd (snd typed_p)))))
      where
        typed_p = theorem1 dp rho fits (RefEl wit) evP
        cohWit = EvalRel-coh p rho (RefEl wit) evP   -- Coherent (RefEl wit) = Coherent wit

        dispatchId : (w' a_id : FinEl) -> LeCode (RefEl wit) w' -> EvalRel p rho w' ->
          FinMem w' a_id -> EvalRel (Id A a b) rho a_id ->
          EqVal2 H (J sC sd sp) (J sC' sd' sp') (App (App (App sC sa) sb) sp) u at
        dispatchId (RefEl w'') (IdCode t' l' r') le_rw evP' fm_w' evId =
          EqVal2-headred-expand u at hrJ-L hrJ-R ctJ-L ctJ-R dEdge
          where
            le_wit_w'' = le_rw
            fm_w''_t' = finMem-ref-wit w'' t' l' r' fm_w'
            cohW''    = FinMem-coh-u w'' t' fm_w''_t'
            cW''      = cohW''
            fm_t'_U   = FinMem-a-in-U w'' t' fm_w''_t'
            cohT'     = coh-from-aU t' fm_t'_U
            evT'      = fst (snd evId)              -- EvalRel A rho t'
            ev_a_l'   = fst (snd (snd evId))        -- EvalRel a rho l'
            ev_b_r'   = snd (snd (snd evId))        -- EvalRel b rho r'
            cohl'     = EvalRel-coh a rho l' ev_a_l'
            cohr'     = EvalRel-coh b rho r' ev_b_r'
            le_w''_l' = finMem-ref-le1 w'' t' l' r' fm_w'
            le_w''_r' = finMem-ref-le2 w'' t' l' r' fm_w'

            -- proof CROSS at (w'', t'); LEFT/RIGHT value records.
            eqvalP0 = IHcp sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                        (RefEl w'') evP' (IdCode t' l' r') evId fm_w'
            valP0L = Val2-from-EqVal2-first  (RefEl w'') (IdCode t' l' r') eqvalP0
            valP0R = Val2-from-EqVal2-second (RefEl w'') (IdCode t' l' r') eqvalP0
            ridL = un-ValId {w = w''} {t = t'} {u = l'} {v = r'} valP0L
            ridR = un-ValId {w = w''} {t = t'} {u = l'} {v = r'} valP0R

            -- LEFT witness data (as JApp.adequacyV-ty-J)
            wit0L = RValIdP.wit0 ridL
            redTmL = RValIdP.redTm ridL
            sIdL  = HeadRed-Id-refl (Red3.hr (RValIdP.red ridL))
            eqA0L = fst sIdL ; eqL0L = fst (snd sIdL) ; eqR0L = snd (snd sIdL)
            endEqL-L : EqVal2 H wit0L sa sA w'' t'
            endEqL-L = Eq-transport (\ X -> EqVal2 H wit0L sa X w'' t') (Eq-sym eqA0L)
                         (Eq-transport (\ Y -> EqVal2 H wit0L Y (RValIdP.domA0 ridL) w'' t') (Eq-sym eqL0L)
                           (RValIdP.endEqL ridL))
            endEqR-L : EqVal2 H wit0L sb sA w'' t'
            endEqR-L = Eq-transport (\ X -> EqVal2 H wit0L sb X w'' t') (Eq-sym eqA0L)
                         (Eq-transport (\ Y -> EqVal2 H wit0L Y (RValIdP.domA0 ridL) w'' t') (Eq-sym eqR0L)
                           (RValIdP.endEqR ridL))
            refConvL-L : ConvTm H wit0L sa sA
            refConvL-L = Eq-transport (\ X -> ConvTm H wit0L sa X) (Eq-sym eqA0L)
                           (Eq-transport (\ Y -> ConvTm H wit0L Y (RValIdP.domA0 ridL)) (Eq-sym eqL0L)
                             (RValIdP.refConvL ridL))
            refConvR-L : ConvTm H wit0L sb sA
            refConvR-L = Eq-transport (\ X -> ConvTm H wit0L sb X) (Eq-sym eqA0L)
                           (Eq-transport (\ Y -> ConvTm H wit0L Y (RValIdP.domA0 ridL)) (Eq-sym eqR0L)
                             (RValIdP.refConvR ridL))
            htWit0L = fst (typing-ConvTm refConvL-L)

            -- RIGHT witness data
            wit0R = RValIdP.wit0 ridR
            redTmR = RValIdP.redTm ridR
            sIdR  = HeadRed-Id-refl (Red3.hr (RValIdP.red ridR))
            eqA0R = fst sIdR ; eqL0R = fst (snd sIdR)
            endEqL-R : EqVal2 H wit0R sa sA w'' t'
            endEqL-R = Eq-transport (\ X -> EqVal2 H wit0R sa X w'' t') (Eq-sym eqA0R)
                         (Eq-transport (\ Y -> EqVal2 H wit0R Y (RValIdP.domA0 ridR) w'' t') (Eq-sym eqL0R)
                           (RValIdP.endEqL ridR))
            refConvL-R : ConvTm H wit0R sa sA
            refConvL-R = Eq-transport (\ X -> ConvTm H wit0R sa X) (Eq-sym eqA0R)
                           (Eq-transport (\ Y -> ConvTm H wit0R Y (RValIdP.domA0 ridR)) (Eq-sym eqL0R)
                             (RValIdP.refConvL ridR))
            htWit0R = fst (typing-ConvTm refConvL-R)

            -- bridge LEFT witness -> RIGHT witness
            cv-LR : ConvTm H wit0L wit0R sA
            cv-LR = conv-trans refConvL-L (conv-sym refConvL-R)
            eqWit0LR : EqVal2 H wit0L wit0R sA w'' t'
            eqWit0LR = EqVal2-trans w'' t' cW'' cohT' endEqL-L (EqVal2-sym w'' t' cW'' cohT' endEqL-R)

            valWit0L = Val2-from-EqVal2-first w'' t' endEqL-L   -- Val2 wit0L sA w'' t'

            -- witness argument Val2 (fun-variation P)
            argVal : (u' a' : FinEl) -> EvalRel A rho a' -> LeCode u' wit -> Coherent u' -> FinMem u' a' ->
              Val2 H wit0L sA u' a'
            argVal u' a' evA' le cu' fm' =
              app-transport-Val2 a' t' (EvalRel-Comp A rho crho a' t' evA' evT')
                (FinMem-a-in-U u' a' fm') fm_t'_U w'' u'
                fm_w''_t' fm' (LeCode-trans u' wit w'' cu' cohWit cW'' le le_wit_w'')
                (Val2-U-to-ValTy2 a' (FinMem-a-in-U u' a' fm')
                  (IHA sigma rho crho vs fits wtsub wfH a' evA' UCode evU (FinMem-a-in-U u' a' fm')))
                (Val2-U-to-ValTy2 t' fm_t'_U
                  (IHA sigma rho crho vs fits wtsub wfH t' evT' UCode evU fm_t'_U))
                valWit0L

            -- witness argument EqVal2 (arg-variation wit0L -> wit0R)
            argEq : (u' a' : FinEl) -> EvalRel A rho a' -> LeCode u' wit -> Coherent u' -> FinMem u' a' ->
              EqVal2 H wit0L wit0R sA u' a'
            argEq u' a' evA' le cu' fm' =
              app-transport-EqVal2 a' t' (EvalRel-Comp A rho crho a' t' evA' evT')
                (FinMem-a-in-U u' a' fm') fm_t'_U w'' u'
                fm_w''_t' fm' (LeCode-trans u' wit w'' cu' cohWit cW'' le le_wit_w'')
                (Val2-U-to-ValTy2 a' (FinMem-a-in-U u' a' fm')
                  (IHA sigma rho crho vs fits wtsub wfH a' evA' UCode evU (FinMem-a-in-U u' a' fm')))
                (Val2-U-to-ValTy2 t' fm_t'_U
                  (IHA sigma rho crho vs fits wtsub wfH t' evT' UCode evU fm_t'_U))
                eqWit0LR

            -- head reductions and conversions
            hrJ-L : HeadRed (J sC sd sp) (App sd wit0L)
            hrJ-L = HeadRed-trans (HeadRed-J (Red3.hr redTmL)) (headred-step headred-J headred-refl)
            hrJ-R : HeadRed (J sC' sd' sp') (App sd' wit0R)
            hrJ-R = HeadRed-trans (HeadRed-J (Red3.hr redTmR)) (headred-step headred-J headred-refl)
            ctJ-L : ConvTm H (J sC sd sp) (App sd wit0L) (App (App (App sC sa) sb) sp)
            ctJ-L = jHeadConv htsA htSa htSb htsC htsd htSp wit0L htWit0L (Red3.ct redTmL) refConvL-L refConvR-L
            refConvR-R : ConvTm H wit0R sb sA
            refConvR-R = Eq-transport (\ X -> ConvTm H wit0R sb X) (Eq-sym eqA0R)
                           (Eq-transport (\ Y -> ConvTm H wit0R Y (RValIdP.domA0 ridR)) (Eq-sym (snd (snd sIdR)))
                             (RValIdP.refConvR ridR))
            -- ctJ-R : reduce the witness-at-LEFT-type wit0R data to the RIGHT
            -- base type sA' (cross conversions), build the RIGHT-natural head
            -- conversion via jHeadConv, then bridge to the goal type via cvTypeRL.
            ctJ-R : ConvTm H (J sC' sd' sp') (App sd' wit0R) (App (App (App sC sa) sb) sp)
            ctJ-R = conv-conv rightNat cvTypeRL typedGoalσ
              where
                cAA' = subst-ConvTm-cross dA wtsub wtsub' wcs wfH        -- ConvTm sA sA' U
                caa' = subst-ConvTm-cross da wtsub wtsub' wcs wfH        -- ConvTm sa sa' sA
                cbb' = subst-ConvTm-cross db wtsub wtsub' wcs wfH        -- ConvTm sb sb' sA
                cIdCross = subst-ConvTm-cross (ty-Id dA da db) wtsub wtsub' wcs wfH  -- Id sA sa sb ~ Id sA' sa' sb' : U
                htId' = ty-Id htsA' htSa' htSb'
                htWit0R' : HasType H wit0R sA'
                htWit0R' = ty-conv htWit0R cAA' htsA'
                rcL' : ConvTm H wit0R sa' sA'
                rcL' = conv-conv (conv-trans refConvL-R caa') cAA' htsA'
                rcR' : ConvTm H wit0R sb' sA'
                rcR' = conv-conv (conv-trans refConvR-R cbb') cAA' htsA'
                ctSp'R : ConvTm H sp' (Ref wit0R) (Id sA' sa' sb')
                ctSp'R = conv-conv (Red3.ct redTmR) cIdCross htId'
                rightNat : ConvTm H (J sC' sd' sp') (App sd' wit0R) (App (App (App sC' sa') sb') sp')
                rightNat = jHeadConv htsA' htSa' htSb' htsC' htsd' htSp' wit0R htWit0R' ctSp'R rcL' rcR'

            -- the cross d-edge, at (u, at).
            dEdge : EqVal2 H (App sd wit0L) (App sd' wit0R) (App (App (App sC sa) sb) sp) u at
            dEdge =
              let typed_d = theorem1 dd rho fits (FunEl sing) jb
                  u_big   = fst typed_d
                  a_pi    = fst (snd typed_d)
                  le_sing = fst (snd (snd typed_d))
                  evF_big = fst (snd (snd (snd typed_d)))
                  fm_big  = fst (snd (snd (snd (snd typed_d))))
                  evPi    = snd (snd (snd (snd (snd typed_d))))
                  eqval_d = Eq-transport (\ T -> EqVal2 H sd sd' T u_big a_pi) (subst-baseTy sigma A C)
                              (IHcd sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                                 u_big evF_big a_pi evPi fm_big)
              in dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_d
              where
                sing = cons (mkSigma wit u) nil
                codB0 = App (App (App (wkExpr sC) (Var fzero)) (Var fzero)) (Ref (Var fzero))
                eq-cod : Eq (subst1 codB0 wit0L) (App (App (App sC wit0L) wit0L) (Ref wit0L))
                eq-cod = Eq-cong2-Expr App (Eq-cong2-Expr App (Eq-cong2-Expr App (subst1-wk sC wit0L) refl) refl) refl
                adqType = adq-motiveApp3 dA dC da db dp IHA IHcA IHC IHa IHb IHp
                dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
                  EvalRel d rho ub -> EvalRel (baseTy A C) rho ap -> FinMem ub ap ->
                  EqVal2 H sd sd' (Pi sA codB0) ub ap ->
                  EqVal2 H (App sd wit0L) (App sd' wit0R) (App (App (App sC sa) sb) sp) u at
                dispatch Bot          ap () evFb evPab fmba eqvba
                dispatch UCode        ap () evFb evPab fmba eqvba
                dispatch (PiCode _ _) ap () evFb evPab fmba eqvba
                dispatch (IdCode _ _ _) ap () evFb evPab fmba eqvba
                dispatch (RefEl _)    ap () evFb evPab fmba eqvba
                dispatch (FunEl g_big) Bot          lf evFb evPab () eqvba
                dispatch (FunEl g_big) UCode        lf evFb evPab () eqvba
                dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () eqvba
                dispatch (FunEl g_big) (IdCode _ _ _) lf evFb evPab () eqvba
                dispatch (FunEl g_big) (RefEl _)    lf evFb evPab () eqvba
                dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
                  let le_u_vsel = fst lf
                      fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
                      cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
                      piU      = finMem-funel-wf g_big b_pi f_pi fmba
                      b_piU    = finMem-piU-dom b_pi f_pi piU
                      allU_fpi = finMem-piU-allU b_pi f_pi piU
                      cf_pi    = finMem-piU-cft b_pi f_pi piU
                      cb_pi    = coh-from-aU b_pi b_piU
                      evA_bpi  = fst (snd evPab)
                      sbel     = selectionBelow g_big wit (cft-from-cf g_big cg_big) cohWit
                      u_sel    = fst sbel
                      v_sel    = fst (snd sbel)
                      sel_big  = fst (snd (snd sbel))
                      le_usel  = fst (snd (snd (snd sbel)))
                      eq_vsel  = snd (snd (snd (snd sbel)))
                      le_u_vsel' = S.Eq-transport (LeCode u) eq_vsel le_u_vsel
                      cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
                      cv_sel   = Coherent-Selection-val sel_big (cft-from-cf g_big cg_big)
                      le_usel_w'' = LeCode-trans u_sel wit w'' cu_sel cohWit cW'' le_usel le_wit_w''
                      fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
                      c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
                      ef_usel  = EvalFun f_pi u_sel
                      ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
                      evBase   = EvalRel-Pi-body A
                                   (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero)))
                                   rho b_pi f_pi u_sel crho cu_sel evPab
                      -- FUNCTION VARIATION : App sd wit0L vs App sd' wit0L
                      eqvpi_fun = un-REqValPi eqvba
                      uniq_fun  = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA codB0} {A = U})
                                    (mkRed (Red3.hr (REqValPiP.red eqvpi_fun)))
                      eqA_ef    = fst uniq_fun
                      eqB_ef    = snd uniq_fun
                      paeqv     = REqValPiP.appEV eqvpi_fun
                      val_wit0L = argVal u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
                      val_wit0L_A0 = S.Eq-transport (\ X -> Val2 H wit0L X u_sel b_pi) eqA_ef val_wit0L
                      htWit0L_A0 = S.Eq-transport (\ X -> HasType H wit0L X) eqA_ef htWit0L
                      eqval_fun_raw = paeqv u_sel v_sel sel_big wit0L htWit0L_A0 val_wit0L_A0
                      eqval_fun_var : EqVal2 H (App sd wit0L) (App sd' wit0L) (subst1 codB0 wit0L) v_sel ef_usel
                      eqval_fun_var = S.Eq-transport
                        (\ X -> EqVal2 H (App sd wit0L) (App sd' wit0L) (subst1 X wit0L) v_sel ef_usel)
                        (S.Eq-sym eqB_ef) eqval_fun_raw
                      -- ARGUMENT VARIATION : App sd' wit0L vs App sd' wit0R
                      vpi_sd'   = eqvalPi-snd eqvba
                      uniq_sd'  = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA codB0} {A = U})
                                    (mkRed (Red3.hr (RValPiP.red vpi_sd')))
                      eqA_FR    = fst uniq_sd'
                      eqB_FR    = snd uniq_sd'
                      pae_FR    = RValPiP.appE vpi_sd'
                      htWit0L_AFR = S.Eq-transport (\ X -> HasType H wit0L X) eqA_FR htWit0L
                      htWit0R_AFR = S.Eq-transport (\ X -> HasType H wit0R X) eqA_FR htWit0R
                      cv_LR_AFR   = S.Eq-transport (\ X -> ConvTm H wit0L wit0R X) eqA_FR cv-LR
                      eqval_arg    = argEq u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
                      eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H wit0L wit0R X u_sel b_pi) eqA_FR eqval_arg
                      eqval_arg_raw = pae_FR u_sel v_sel sel_big wit0L wit0R htWit0L_AFR htWit0R_AFR cv_LR_AFR eqval_arg_A0
                      eqval_arg_var : EqVal2 H (App sd' wit0L) (App sd' wit0R) (subst1 codB0 wit0L) v_sel ef_usel
                      eqval_arg_var = S.Eq-transport
                        (\ X -> EqVal2 H (App sd' wit0L) (App sd' wit0R) (subst1 X wit0L) v_sel ef_usel)
                        (S.Eq-sym eqB_FR) eqval_arg_raw
                      -- COMBINE
                      eqval_combined = EqVal2-trans v_sel ef_usel cv_sel c_efusel eqval_fun_var eqval_arg_var
                      -- TYPE TRANSPORT via jTypeEqSp (LEFT witness wit0L)
                      evApp3 : EvalRel (App (App (App (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero)))) (Var (fsuc fzero))) (Var fzero))
                                       (extendEnv (extendEnv (extendEnv rho w'') w'') (RefEl w'')) ef_usel
                      evApp3 = reshapeApp3 u_sel cu_sel le_usel_w'' ef_usel evBase
                      eqvty = jTypeEqSp dA dC da db IHA IHcA IHcC sigma rho crho vs fits wtsub wfH
                                wit0L w'' t' cW'' evT' fm_w''_t' fm_t'_U endEqL-L endEqR-L refConvL-L refConvR-L
                                sp redTmL ef_usel evApp3 ef_uselU
                      eqval1 : EqVal2 H (App sd wit0L) (App sd' wit0R) (App (App (App sC wit0L) wit0L) (Ref wit0L)) v_sel ef_usel
                      eqval1 = S.Eq-transport (\ T -> EqVal2 H (App sd wit0L) (App sd' wit0R) T v_sel ef_usel) eq-cod eqval_combined
                      eqvalGoal : EqVal2 H (App sd wit0L) (App sd' wit0R) (App (App (App sC sa) sb) sp) v_sel ef_usel
                      eqvalGoal = EqVal2-EqValTy2-fwd v_sel ef_usel c_efusel eqvty eqval1
                      -- app-transport down to (u, at)
                      evC_ef   = mkEvC u_sel cu_sel le_usel_w'' ef_usel evBase
                      vt_at    = Val2-U-to-ValTy2 at at_U
                                   (adqType sigma rho crho vs fits wtsub wfH at evA UCode evU at_U)
                      vt_ef    = Val2-U-to-ValTy2 ef_usel ef_uselU
                                   (adqType sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
                      comp_at_ef = EvalRel-Comp (App (App (App C a) b) p) rho crho at ef_usel evA evC_ef
                      fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big
                                     (cft-from-cf g_big cg_big) cf_pi allU_fpi
                  in app-transport-EqVal2 at ef_usel comp_at_ef at_U ef_uselU v_sel u
                       fm_vsel_ef fm le_u_vsel' vt_at vt_ef eqvalGoal
                  where
                    rho3w = extendEnv (extendEnv (extendEnv rho w'') w'') (RefEl w'')

                    le-ref-arg : (uS x : FinEl) ->
                      EvalRel (Ref (Var fzero)) (extendEnv rho uS) x -> LeCode x (RefEl uS)
                    le-ref-arg uS Bot            _  = tt
                    le-ref-arg uS UCode          ()
                    le-ref-arg uS (FunEl _)      ()
                    le-ref-arg uS (PiCode _ _)   ()
                    le-ref-arg uS (IdCode _ _ _) ()
                    le-ref-arg uS (RefEl w3)     ev = snd ev

                    BaseSig : FinEl -> FinEl -> Set
                    BaseSig uS c =
                      Sigma FinEl (\ v3 -> Pair (EvalRel (Ref (Var fzero)) (extendEnv rho uS) v3)
                        (Sigma FinEl (\ v2 -> Pair (EvalRel (Var fzero) (extendEnv rho uS) v2)
                          (Sigma FinEl (\ v1 -> Pair (EvalRel (Var fzero) (extendEnv rho uS) v1)
                            (EvalRel (wkExpr C) (extendEnv rho uS)
                              (FunEl (cons (mkSigma v1 (FunEl (cons (mkSigma v2 (FunEl (cons (mkSigma v3 c) nil))) nil))) nil))))))))

                    workerA : (uS : FinEl) -> Coherent uS -> LeCode uS w'' -> (c : FinEl) ->
                      BaseSig uS c ->
                      Sigma FinEl (\ v3 -> Pair (EvalRel (Var fzero) rho3w v3)
                        (Sigma FinEl (\ v2 -> Pair (EvalRel (Var (fsuc fzero)) rho3w v2)
                          (Sigma FinEl (\ v1 -> Pair (EvalRel (Var (fsuc (fsuc fzero))) rho3w v1)
                            (EvalRel (wkExpr (wkExpr (wkExpr C))) rho3w
                              (FunEl (cons (mkSigma v1 (FunEl (cons (mkSigma v2 (FunEl (cons (mkSigma v3 c) nil))) nil))) nil))))))))
                    workerA uS cuS leSW c eb =
                      let v3 = fst eb ; evRef3 = fst (snd eb) ; r3 = snd (snd eb)
                          v2 = fst r3 ; evV2 = fst (snd r3) ; r2 = snd (snd r3)
                          v1 = fst r2 ; evV1 = fst (snd r2) ; evC1 = snd (snd r2)
                          cohv1 = fst evV1 ; cohv2 = fst evV2
                          cohv3 = EvalRel-coh (Ref (Var fzero)) (extendEnv rho uS) v3 evRef3
                          le1 = LeCode-trans v1 uS w'' cohv1 cuS cW'' (snd evV1) leSW
                          le2 = LeCode-trans v2 uS w'' cohv2 cuS cW'' (snd evV2) leSW
                          le3 = LeCode-trans v3 (RefEl uS) (RefEl w'') cohv3 cuS cW'' (le-ref-arg uS v3 evRef3) leSW
                          evC0 = EvalRel-unwk C rho uS _ evC1
                          w1 = EvalRel-wk C rho w'' _ evC0
                          w2 = EvalRel-wk (wkExpr C) (extendEnv rho w'') w'' _ w1
                          w3 = EvalRel-wk (wkExpr (wkExpr C)) (extendEnv (extendEnv rho w'') w'') (RefEl w'') _ w2
                      in mkSigma v3 (mkSigma (mkSigma cohv3 le3)
                           (mkSigma v2 (mkSigma (mkSigma cohv2 le2)
                             (mkSigma v1 (mkSigma (mkSigma cohv1 le1) w3)))))

                    reshapeApp3 : (uS : FinEl) -> Coherent uS -> LeCode uS w'' -> (c : FinEl) ->
                      EvalRel (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero)))
                              (extendEnv rho uS) c ->
                      EvalRel (App (App (App (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero)))) (Var (fsuc fzero))) (Var fzero))
                              rho3w c
                    reshapeApp3 uS cuS leSW Bot              eb = tt
                    reshapeApp3 uS cuS leSW UCode            eb = workerA uS cuS leSW UCode eb
                    reshapeApp3 uS cuS leSW (FunEl g')       eb = workerA uS cuS leSW (FunEl g') eb
                    reshapeApp3 uS cuS leSW (PiCode a2 f2)   eb = workerA uS cuS leSW (PiCode a2 f2) eb
                    reshapeApp3 uS cuS leSW (IdCode t2 u2 v2) eb = workerA uS cuS leSW (IdCode t2 u2 v2) eb
                    reshapeApp3 uS cuS leSW (RefEl w2)       eb = workerA uS cuS leSW (RefEl w2) eb

                    workerC : (uS : FinEl) -> Coherent uS -> LeCode uS w'' -> (c : FinEl) ->
                      BaseSig uS c ->
                      Sigma FinEl (\ v3 -> Pair (EvalRel p rho v3)
                        (Sigma FinEl (\ v2 -> Pair (EvalRel b rho v2)
                          (Sigma FinEl (\ v1 -> Pair (EvalRel a rho v1)
                            (EvalRel C rho
                              (FunEl (cons (mkSigma v1 (FunEl (cons (mkSigma v2 (FunEl (cons (mkSigma v3 c) nil))) nil))) nil))))))))
                    workerC uS cuS leSW c eb =
                      let v3 = fst eb ; evRef3 = fst (snd eb) ; r3 = snd (snd eb)
                          v2 = fst r3 ; evV2 = fst (snd r3) ; r2 = snd (snd r3)
                          v1 = fst r2 ; evV1 = fst (snd r2) ; evC1 = snd (snd r2)
                          cohv1 = fst evV1 ; cohv2 = fst evV2
                          cohv3 = EvalRel-coh (Ref (Var fzero)) (extendEnv rho uS) v3 evRef3
                          le1w = LeCode-trans v1 uS w'' cohv1 cuS cW'' (snd evV1) leSW
                          le2w = LeCode-trans v2 uS w'' cohv2 cuS cW'' (snd evV2) leSW
                          le3w = LeCode-trans v3 (RefEl uS) (RefEl w'') cohv3 cuS cW'' (le-ref-arg uS v3 evRef3) leSW
                          le_v1_l' = LeCode-trans v1 w'' l' cohv1 cW'' cohl' le1w le_w''_l'
                          le_v2_r' = LeCode-trans v2 w'' r' cohv2 cW'' cohr' le2w le_w''_r'
                          eva = EvalRel-down a rho l' v1 crho cohv1 ev_a_l' le_v1_l'
                          evb = EvalRel-down b rho r' v2 crho cohv2 ev_b_r' le_v2_r'
                          evp = EvalRel-down p rho (RefEl w'') v3 crho cohv3 evP' le3w
                          evC0 = EvalRel-unwk C rho uS _ evC1
                      in mkSigma v3 (mkSigma evp
                           (mkSigma v2 (mkSigma evb
                             (mkSigma v1 (mkSigma eva evC0)))))

                    mkEvC : (uS : FinEl) -> Coherent uS -> LeCode uS w'' -> (c : FinEl) ->
                      EvalRel (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero)))
                              (extendEnv rho uS) c ->
                      EvalRel (App (App (App C a) b) p) rho c
                    mkEvC uS cuS leSW Bot              eb = tt
                    mkEvC uS cuS leSW UCode            eb = workerC uS cuS leSW UCode eb
                    mkEvC uS cuS leSW (FunEl g')       eb = workerC uS cuS leSW (FunEl g') eb
                    mkEvC uS cuS leSW (PiCode a2 f2)   eb = workerC uS cuS leSW (PiCode a2 f2) eb
                    mkEvC uS cuS leSW (IdCode t2 u2 v2) eb = workerC uS cuS leSW (IdCode t2 u2 v2) eb
                    mkEvC uS cuS leSW (RefEl w2)       eb = workerC uS cuS leSW (RefEl w2) eb

        -- absurd shapes for the proof value / Id type-value
        dispatchId Bot           a_id le evP' fm' evId = absurdBot le
          where absurdBot : LeCode (RefEl wit) Bot -> _
                absurdBot ()
        dispatchId UCode         a_id () evP' fm' evId
        dispatchId (FunEl _)     a_id () evP' fm' evId
        dispatchId (PiCode _ _)  a_id () evP' fm' evId
        dispatchId (IdCode _ _ _) a_id () evP' fm' evId
        dispatchId (RefEl w'') Bot           le evP' fm' evId = absurdBotT fm'
          where absurdBotT : FinMem (RefEl w'') Bot -> _
                absurdBotT ()
        dispatchId (RefEl w'') UCode         le evP' () evId
        dispatchId (RefEl w'') (FunEl _)     le evP' () evId
        dispatchId (RefEl w'') (PiCode _ _)  le evP' () evId
        dispatchId (RefEl w'') (RefEl _)     le evP' () evId

    branch : (w : FinEl) -> EvalRel p rho w -> JBranch C d rho u w ->
      EqVal2 H (J sC sd sp) (J sC' sd' sp') (App (App (App sC sa) sb) sp) u at
    branch Bot            evP jb = branchBot jb
    branch UCode          evP ()
    branch (FunEl _)      evP ()
    branch (PiCode _ _)   evP ()
    branch (IdCode _ _ _) evP ()
    branch (RefEl wit)    evP jb = refCore wit evP jb
