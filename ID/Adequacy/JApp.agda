{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JApp.agda
--
-- The based-J VALUE driver (adequacyV-ty-J), the ty-J case of Theorem 2's
-- adequacySub2.  Follows Coquand's sketch:
--
--   J M N P D  ->*  D Q   (P ->* Ref Q, Q conv M/N)
--   Val (D Q) (C Q Q (Ref Q)) (d w) (C w w (Ref w))         [d-edge at witness]
--   -> monotonicity of the type-value  (w<=u, w<=v)         [app-transport-Val2]
--   -> syntactic type  C Q Q (Ref Q) ~ C M N P              [jTypeEqSp]
--   -> head-beta expand  J M N P D <- D Q                   [Val2-beta-expand]
--
-- Parameterised by the mutual recursors (as Adq / AdqConv IH values), so it
-- is a standalone combinator wired into Value.agda's ty-J hole.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JApp where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import ID.Adequacy.App using (app-transport-Val2)
open import ID.Adequacy.JMotive using (adq-motiveApp3)
open import ID.Adequacy.JTypeEq using (jTypeEqSp)
open import ID.Adequacy.Records using (RValPiP ; un-ValPi ; RValIdP ; un-ValId)

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
  motiveTail-formation ; conv-motiveApp3)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Validity.Stratified using (Red3 ; mkRed3)

------------------------------------------------------------------------
-- conv-App3-endpoints : the App³-motive congruence varying the two
-- ENDPOINTS a->a', b->b' (C and the proof p FIXED; p : Id A a b typed on the
-- LEFT).  Complements Substitution.conv-motiveApp3 (which varies C, p).  Since
-- p is the same term on both sides, the outer application is a single
-- conv-App-fun; only the inner App C a' must be retyped P1(a') -> P1(a).
------------------------------------------------------------------------

conv-App3-endpoints : {n : Nat} {G : Ctx n} {A C a a' b b' p : Expr n} ->
  HasType G A U -> HasType G C (motiveTy A) ->
  HasType G a A -> HasType G a' A -> HasType G b A -> HasType G b' A ->
  HasType G p (Id A a b) ->
  ConvTm G a a' A -> ConvTm G b b' A ->
  ConvTm G (App (App (App C a) b) p) (App (App (App C a') b') p) U
conv-App3-endpoints {n = n} {G = G} {A = A} {C = C} {a = a} {a' = a'} {b = b} {b' = b'} {p = p}
  dA dC da da' db db' dp conva convb =
  conv-App-fun dId (ty-U (wf-extend dId)) cCab dp
  where
    MTF = motiveTail-formation dA
    dId = ty-Id dA da db
    -- P1 body typing:  dX2 x  :  Pi (Id (wkA)(wk x)(Var0)) U : U
    dIdBody : (x : Expr n) -> HasType G x A ->
      HasType (extend G A) (Id (wkExpr A) (wkExpr x) (Var fzero)) U
    dIdBody x dx = ty-Id (wk-HasType dA dA) (wk-HasType dA dx) (ty-var {i = fzero} (wf-extend dA))
    dX2 : (x : Expr n) -> HasType G x A ->
      HasType (extend G A) (Pi (Id (wkExpr A) (wkExpr x) (Var fzero)) U) U
    dX2 x dx = ty-Pi (dIdBody x dx) (ty-U (wf-extend (dIdBody x dx)))
    lem1 : (x : Expr n) ->
      Eq (subst1 (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U)) x)
         (Pi A (Pi (Id (wkExpr A) (wkExpr x) (Var fzero)) U))
    lem1 x = Eq-cong2-Expr Pi (subst1-wk A x)
               (Eq-cong2-Expr Pi
                 (Eq-cong3-Expr Id
                    (Eq-trans (subst-wk-comm (subst1Sub x) (wkExpr A)) (Eq-cong wkExpr (subst1-wk A x)))
                    refl refl)
                 refl)
    lem2 : (x y : Expr n) ->
      Eq (subst1 (Pi (Id (wkExpr A) (wkExpr x) (Var fzero)) U) y) (Pi (Id A x y) U)
    lem2 x y = Eq-cong2-Expr Pi (Eq-cong3-Expr Id (subst1-wk A y) (subst1-wk x y) refl) refl
    -- P1(a') ~ P1(a) : U  (only the Id middle changes wk a' -> wk a)
    convP1 : ConvTm G (Pi A (Pi (Id (wkExpr A) (wkExpr a') (Var fzero)) U))
                      (Pi A (Pi (Id (wkExpr A) (wkExpr a ) (Var fzero)) U)) U
    convP1 = conv-Pi dA (dX2 a' da') (dX2 a da) (conv-refl dA)
               (conv-Pi (dIdBody a' da') (ty-U (wf-extend (dIdBody a' da'))) (ty-U (wf-extend (dIdBody a' da')))
                  (conv-Id (wk-HasType dA dA) (wk-HasType dA da') (ty-var {i = fzero} (wf-extend dA))
                     (conv-refl (wk-HasType dA dA)) (wk-ConvTm dA (conv-sym conva))
                     (conv-refl (ty-var {i = fzero} (wf-extend dA))))
                  (conv-refl (ty-U (wf-extend (dIdBody a' da')))))
    -- App C a ~ App C a' : P1(a)
    cCa = Eq-transport (\ T -> ConvTm G (App C a) (App C a') T) (lem1 a)
            (conv-App-arg dA MTF dC conva)
    -- App C a' retyped from P1(a') to P1(a)
    htCa'-Pa : HasType G (App C a') (Pi A (Pi (Id (wkExpr A) (wkExpr a) (Var fzero)) U))
    htCa'-Pa = ty-conv (Eq-transport (\ T -> HasType G (App C a') T) (lem1 a') (ty-App dA MTF dC da'))
                 convP1
                 (ty-Pi dA (dX2 a da))
    -- App(App C a) b ~ App(App C a') b : P2(a,b)
    cCab1 = Eq-transport (\ T -> ConvTm G (App (App C a) b) (App (App C a') b) T) (lem2 a b)
              (conv-App-fun dA (dX2 a da) cCa db)
    -- App(App C a') b ~ App(App C a') b' : P2(a,b)
    cCab2 = Eq-transport (\ T -> ConvTm G (App (App C a') b) (App (App C a') b') T) (lem2 a b)
              (conv-App-arg dA (dX2 a da) htCa'-Pa convb)
    cCab = conv-trans cCab1 cCab2

------------------------------------------------------------------------
-- adequacyV-ty-J
------------------------------------------------------------------------

adequacyV-ty-J : {h g : Nat} {H : Ctx h} {G : Ctx g} {A a b C d p : Expr g} ->
  HasType G A U -> HasType G a A -> HasType G b A -> HasType G C (motiveTy A) ->
  HasType G d (baseTy A C) -> HasType G p (Id A a b) ->
  Adq G A U -> AdqConv G A U -> Adq G a A -> Adq G b A ->
  Adq G C (motiveTy A) -> AdqConv G C (motiveTy A) ->
  Adq G d (baseTy A C) -> Adq G p (Id A a b) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (J C d p) rho u ->
  (at : FinEl) -> EvalRel (App (App (App C a) b) p) rho at -> FinMem u at ->
  Val2 H (substExpr sigma (J C d p))
         (substExpr sigma (App (App (App C a) b) p)) u at
adequacyV-ty-J {H = H} {G = G} {A = A} {a = a} {b = b} {C = C} {d = d} {p = p}
  dA da db dC dd dp IHA IHcA IHa IHb IHC IHcC IHd IHp sigma rho crho vs fits wtsub wfH u hu at evA fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sC = substExpr sigma C ; sd = substExpr sigma d ; sp = substExpr sigma p
    sA = substExpr sigma A ; sa = substExpr sigma a ; sb = substExpr sigma b
    at_U = FinMem-a-in-U u at fm
    wfG  = typing-WfCtx dp
    htsA = subst-HasType wtsub wfH dA
    htSa = subst-HasType wtsub wfH da
    htSb = subst-HasType wtsub wfH db
    htsC = Eq-transport (\ T -> HasType H sC T) (subst-motiveTy sigma A) (subst-HasType wtsub wfH dC)
    htsd = Eq-transport (\ T -> HasType H sd T) (subst-baseTy sigma A C) (subst-HasType wtsub wfH dd)
    evU  = mkSigma tt (LeCode-refl UCode tt)

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    branchBot jb =
      restrictVal2 H (J sC sd sp) (App (App (App sC sa) sb) sp) Bot u at (snd jb) fm
        (finMem-bot-from at at_U) (Val2-Bot at)

    -- refCore : the genuine RefEl-proof case.  wit = proof witness value,
    -- jb : d maps wit -> u.
    refCore : (wit : FinEl) -> EvalRel p rho (RefEl wit) ->
      EvalRel d rho (FunEl (cons (mkSigma wit u) nil)) ->
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    refCore wit evP jb =
      dispatchId (fst typed_p) (fst (snd typed_p)) (fst (snd (snd typed_p)))
                 (fst (snd (snd (snd typed_p)))) (fst (snd (snd (snd (snd typed_p)))))
                 (snd (snd (snd (snd (snd typed_p)))))
      where
        typed_p = theorem1 dp rho fits (RefEl wit) evP
        cohWit = EvalRel-coh p rho (RefEl wit) evP   -- Coherent (RefEl wit) = Coherent wit

        -- Once the proof record is in hand (witness value w'' >= wit, Id
        -- type-value IdCode t' l' r'), do the d-edge + monotonicity + head-expand.
        dispatchId : (w' a_id : FinEl) -> LeCode (RefEl wit) w' -> EvalRel p rho w' ->
          FinMem w' a_id -> EvalRel (Id A a b) rho a_id ->
          Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
        dispatchId (RefEl w'') (IdCode t' l' r') le_rw evP' fm_w' evId =
          Val2-beta-expand u at hrJ ctJ appVal
          where
            le_wit_w'' = le_rw          -- LeCode (RefEl wit)(RefEl w'') = LeCode wit w''
            -- proof record at (w'', t')
            valP0 = IHp sigma rho crho vs fits wtsub wfH (RefEl w'') evP' (IdCode t' l' r') evId fm_w'
            rid   = un-ValId {w = w''} {t = t'} {u = l'} {v = r'} valP0
            wit0  = RValIdP.wit0 rid
            redTm = RValIdP.redTm rid          -- Red3 sp (Ref wit0) (Id sA sa sb)
            -- strip the record's canonical Id components to the literal (sA, sa, sb)
            sId   = HeadRed-Id-refl (Red3.hr (RValIdP.red rid))
            eqA0  = fst sId                    -- Eq sA (domA0 rid)
            eqL0  = fst (snd sId)              -- Eq sa (lhs0 rid)
            eqR0  = snd (snd sId)              -- Eq sb (rhs0 rid)
            endEqL : EqVal2 H wit0 sa sA w'' t'
            endEqL = Eq-transport (\ X -> EqVal2 H wit0 sa X w'' t') (Eq-sym eqA0)
                       (Eq-transport (\ Y -> EqVal2 H wit0 Y (RValIdP.domA0 rid) w'' t') (Eq-sym eqL0)
                         (RValIdP.endEqL rid))
            endEqR : EqVal2 H wit0 sb sA w'' t'
            endEqR = Eq-transport (\ X -> EqVal2 H wit0 sb X w'' t') (Eq-sym eqA0)
                       (Eq-transport (\ Y -> EqVal2 H wit0 Y (RValIdP.domA0 rid) w'' t') (Eq-sym eqR0)
                         (RValIdP.endEqR rid))
            refConvL : ConvTm H wit0 sa sA
            refConvL = Eq-transport (\ X -> ConvTm H wit0 sa X) (Eq-sym eqA0)
                         (Eq-transport (\ Y -> ConvTm H wit0 Y (RValIdP.domA0 rid)) (Eq-sym eqL0)
                           (RValIdP.refConvL rid))
            refConvR : ConvTm H wit0 sb sA
            refConvR = Eq-transport (\ X -> ConvTm H wit0 sb X) (Eq-sym eqA0)
                         (Eq-transport (\ Y -> ConvTm H wit0 Y (RValIdP.domA0 rid)) (Eq-sym eqR0)
                           (RValIdP.refConvR rid))
            htWit0 = fst (typing-ConvTm refConvL)
            fm_w''_t' = finMem-ref-wit w'' t' l' r' fm_w'
            cohW'' = FinMem-coh-u w'' t' fm_w''_t'
            cW''   = cohW''
            fm_t'_U = FinMem-a-in-U w'' t' fm_w''_t'
            evT'   = fst (snd evId)            -- EvalRel A rho t'
            valWit0 = Val2-from-EqVal2-first w'' t' endEqL   -- Val2 wit0 sA w'' t'

            -- witness argument validity: Val2 wit0 sA at values <= wit, any sA-eval
            argVal : (u' a' : FinEl) -> EvalRel A rho a' -> LeCode u' wit -> Coherent u' -> FinMem u' a' ->
              Val2 H wit0 sA u' a'
            argVal u' a' evA' le cu' fm' =
              app-transport-Val2 a' t' (EvalRel-Comp A rho crho a' t' evA' evT')
                (FinMem-a-in-U u' a' fm') fm_t'_U w'' u'
                fm_w''_t' fm' (LeCode-trans u' wit w'' cu' cohWit cW'' le le_wit_w'')
                (Val2-U-to-ValTy2 a' (FinMem-a-in-U u' a' fm')
                  (IHA sigma rho crho vs fits wtsub wfH a' evA' UCode evU (FinMem-a-in-U u' a' fm')))
                (Val2-U-to-ValTy2 t' fm_t'_U
                  (IHA sigma rho crho vs fits wtsub wfH t' evT' UCode evU fm_t'_U))
                valWit0

            -- head reduction J sC sd sp  ->*  App sd wit0
            hrJ : HeadRed (J sC sd sp) (App sd wit0)
            hrJ = HeadRed-trans (HeadRed-J (Red3.hr redTm)) (headred-step headred-J headred-refl)
            -- conversion carrying the syntactic type C Q Q (Ref Q) -> C M N P
            cvSpRef : ConvTm H sp (Ref wit0) (Id sA sa sb)
            cvSpRef = Red3.ct redTm
            ctJ : ConvTm H (J sC sd sp) (App sd wit0) (App (App (App sC sa) sb) sp)
            ctJ = conv-trans
                    (conv-J htsA htSa htSb htsC htsd
                       (subst-HasType wtsub wfH dp)
                       (conv-refl htsC) (conv-refl htsd) cvSpRef)
                    (conv-conv jbetaConv typeConv typedGoal)
              where
                htRefWit0 : HasType H (Ref wit0) (Id sA sa sb)
                htRefWit0 = snd (typing-ConvTm cvSpRef)
                -- J sC sd (Ref wit0) = App sd wit0 : C wit0 wit0 (Ref wit0)
                jbetaConv : ConvTm H (J sC sd (Ref wit0)) (App sd wit0)
                              (App (App (App sC wit0) wit0) (Ref wit0))
                jbetaConv = conv-J-beta htsA htWit0 htsC htsd
                -- retype: C wit0 wit0 (Ref wit0) ~ C M N P  (endpoints wit0~sa, wit0~sb; Ref wit0 ~ sp)
                -- HOLE 1 (typeConv): the syntactic App³ congruence varying the two
                -- endpoints (refConvL/refConvR) AND the proof (conv-sym cvSpRef).
                -- conv-motiveApp3 (Substitution) varies only C,p; this needs a,b too,
                -- which retypes the proof slot (Id sA wit0 wit0 -> Id sA sa sb).  Build
                -- a `conv-App3-endpoints` helper (mirror conv-motiveApp3, add conv-App-arg
                -- on each endpoint using motiveTail-formation + lem1/lem2) or compose:
                --   App³ sC wit0 wit0 (Ref wit0) ~ App³ sC wit0 wit0 sp  [conv-motiveApp3, p]
                --   ~ App³ sC sa sb sp                                    [endpoints, retype p].
                typeConv : ConvTm H (App (App (App sC wit0) wit0) (Ref wit0))
                                    (App (App (App sC sa) sb) sp) U
                typeConv = conv-trans partP partAB
                  where
                    htSp' = fst (typing-ConvTm cvSpRef)     -- HasType sp (Id sA sa sb)
                    cIdBack : ConvTm H (Id sA sa sb) (Id sA wit0 wit0) U
                    cIdBack = conv-Id htsA htSa htSb (conv-refl htsA) (conv-sym refConvL) (conv-sym refConvR)
                    convP-in : ConvTm H (Ref wit0) sp (Id sA wit0 wit0)
                    convP-in = conv-sym (conv-conv cvSpRef cIdBack (ty-Id htsA htWit0 htWit0))
                    partP : ConvTm H (App (App (App sC wit0) wit0) (Ref wit0))
                                     (App (App (App sC wit0) wit0) sp) U
                    partP = conv-motiveApp3 htsA htsC htsC (conv-refl htsC) htWit0 htWit0
                              (ty-Ref htsA htWit0) convP-in
                    dpSp : HasType H sp (Id sA wit0 wit0)
                    dpSp = ty-conv htSp' cIdBack (ty-Id htsA htWit0 htWit0)
                    partAB : ConvTm H (App (App (App sC wit0) wit0) sp)
                                      (App (App (App sC sa) sb) sp) U
                    partAB = conv-App3-endpoints htsA htsC htWit0 htSa htWit0 htSb dpSp refConvL refConvR
                typedGoal : HasType H (App (App (App sC sa) sb) sp) U
                typedGoal = subst-HasType wtsub wfH (typing-type (ty-J dA da db dC dd dp))

            -- the d-edge value already at the goal type, at (u, at).
            -- HOLE 2 (dEdge): faithful port of NAT.Adequacy.NatCaseDep
            -- adequacyV-app-Nat-dep `appVal-dispatch` [d <-> b, wit0 <-> N,
            -- RefEl wit <-> SucEl v'', jb <-> evF_sing, argVal above <-> nat-argVal].
            -- theorem1 dd rho fits (FunEl(cons(wit,u)nil)) jb -> IHd -> un-ValPi ->
            -- selectionBelow -> appV at (v_sel, ef_usel), type subst1 codB0 wit0
            -- =(eq-cod: subst1-wk)= App³ sC wit0 wit0 (Ref wit0); then jTypeEqSp at
            -- ef_usel (env-bridge evApp3 below) via Val2-EqValTy2-fwd; then
            -- app-transport-Val2 (v_sel,ef_usel -> u,at).
            -- env-bridge evApp3 : EvalRel-Pi-body A baseBody rho b_pi f_pi u_sel ...
            -- -> extract innermost EvalRel C rho (nested FunEl edge) (EvalRel-unwk x3)
            -- -> rebuild EvalRel(App³(wk³C)Var2 Var1 Var0)(extendEnv³ rho u_sel u_sel
            --    (RefEl u_sel)) ef_usel (EvalRel-wk x3 + Var evals) -> EvalRel-mon-env
            --    up u_sel -> w''.
            appVal : Val2 H (App sd wit0) (App (App (App sC sa) sb) sp) u at
            appVal =
              let typed_d = theorem1 dd rho fits (FunEl sing) jb
                  u_big   = fst typed_d
                  a_pi    = fst (snd typed_d)
                  le_sing = fst (snd (snd typed_d))
                  evF_big = fst (snd (snd (snd typed_d)))
                  fm_big  = fst (snd (snd (snd (snd typed_d))))
                  evPi    = snd (snd (snd (snd (snd typed_d))))
                  val_fun = Eq-transport (\ T -> Val2 H sd T u_big a_pi) (subst-baseTy sigma A C)
                              (IHd sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big)
              in dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun
              where
                sing = cons (mkSigma wit u) nil
                codB0 = App (App (App (wkExpr sC) (Var fzero)) (Var fzero)) (Ref (Var fzero))
                eq-cod : Eq (subst1 codB0 wit0) (App (App (App sC wit0) wit0) (Ref wit0))
                eq-cod = Eq-cong2-Expr App (Eq-cong2-Expr App (Eq-cong2-Expr App (subst1-wk sC wit0) refl) refl) refl
                adqType = adq-motiveApp3 dA dC da db dp IHA IHcA IHC IHa IHb IHp
                dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
                  EvalRel d rho ub -> EvalRel (baseTy A C) rho ap -> FinMem ub ap ->
                  Val2 H sd (Pi sA codB0) ub ap ->
                  Val2 H (App sd wit0) (App (App (App sC sa) sb) sp) u at
                dispatch Bot          ap () evFb evPab fmba valba
                dispatch UCode        ap () evFb evPab fmba valba
                dispatch (PiCode _ _) ap () evFb evPab fmba valba
                dispatch (IdCode _ _ _) ap () evFb evPab fmba valba
                dispatch (RefEl _)    ap () evFb evPab fmba valba
                dispatch (FunEl g_big) Bot          lf evFb evPab () valba
                dispatch (FunEl g_big) UCode        lf evFb evPab () valba
                dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () valba
                dispatch (FunEl g_big) (IdCode _ _ _) lf evFb evPab () valba
                dispatch (FunEl g_big) (RefEl _)    lf evFb evPab () valba
                dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
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
                      le_usel_w'' = LeCode-trans u_sel wit w'' cu_sel cohWit cW'' le_usel le_wit_w''
                      fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
                      val_arg  = argVal u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
                      vpi_fun  = un-ValPi valba
                      red_fun  = RValPiP.red vpi_fun
                      uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi sA codB0} {A = U}) (mkRed (Red3.hr red_fun))
                      eqA_fun  = fst uniq_fun
                      eqB_fun  = snd uniq_fun
                      pav_fun  = RValPiP.appV vpi_fun
                      val_arg' = S.Eq-transport (\ X -> Val2 H wit0 X u_sel b_pi) eqA_fun val_arg
                      ht_wit0_A0 = S.Eq-transport (\ X -> HasType H wit0 X) eqA_fun htWit0
                      val_app_raw = pav_fun u_sel v_sel sel_big wit0 ht_wit0_A0 val_arg'
                      ef_usel  = EvalFun f_pi u_sel
                      evBase   = EvalRel-Pi-body A
                                   (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero)))
                                   rho b_pi f_pi u_sel crho cu_sel evPab
                      val_app : Val2 H (App sd wit0) (subst1 (RValPiP.codB0 vpi_fun) wit0) v_sel ef_usel
                      val_app = val_app_raw
                      val_appCod : Val2 H (App sd wit0) (subst1 codB0 wit0) v_sel ef_usel
                      val_appCod = S.Eq-transport (\ X -> Val2 H (App sd wit0) (subst1 X wit0) v_sel ef_usel)
                                     (S.Eq-sym eqB_fun) val_app
                      val_appBase : Val2 H (App sd wit0) (App (App (App sC wit0) wit0) (Ref wit0)) v_sel ef_usel
                      val_appBase = S.Eq-transport (\ T -> Val2 H (App sd wit0) T v_sel ef_usel) eq-cod val_appCod
                      c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
                      ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
                      -- env-bridge: SUB-HOLE (A) -- reshape EvalRel-Pi-body output to the
                      -- triple-extended abstract App³ eval at ef_usel, then mon-env u_sel -> w''.
                      evApp3 : EvalRel (App (App (App (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero)))) (Var (fsuc fzero))) (Var fzero))
                                       (extendEnv (extendEnv (extendEnv rho w'') w'') (RefEl w'')) ef_usel
                      evApp3 = reshapeApp3 u_sel cu_sel le_usel_w'' ef_usel evBase
                      eqvty = jTypeEqSp dA dC da db IHA IHcA IHcC sigma rho crho vs fits wtsub wfH
                                wit0 w'' t' cW'' evT' fm_w''_t' fm_t'_U endEqL endEqR refConvL refConvR
                                sp redTm ef_usel evApp3 ef_uselU
                      val_appGoal : Val2 H (App sd wit0) (App (App (App sC sa) sb) sp) v_sel ef_usel
                      val_appGoal = Val2-EqValTy2-fwd v_sel ef_usel c_efusel eqvty val_appBase
                      -- final transport (v_sel, ef_usel) -> (u, at) via app-transport-Val2.
                      -- Reduced to the single atomic monotonicity SUB-HOLE (B):
                      --   LeCode ef_usel at  (C at the selected witness <= C at the endpoints).
                      at_U     = FinMem-a-in-U u at fm
                      vt_at    = Val2-U-to-ValTy2 at at_U
                                   (adqType sigma rho crho vs fits wtsub wfH at evA UCode evU at_U)
                      fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big
                                     (cft-from-cf g_big cg_big) cf_pi allU_fpi
                      -- SUB-HOLE (B): LeCode ef_usel at.  ef_usel = C(u_sel,u_sel,RefEl u_sel)
                      -- (d's codomain at the selected witness), at = C(val a,val b,RefEl wit).
                      -- Holds by C-monotonicity since u_sel<=wit<=(val a,val b) [wit<=val a,val b
                      -- from the proof's Id-membership: RefEl wit in IdCode _ (val a)(val b)].
                      -- CLEANER ALTERNATIVE (NatCaseDep evC_ef route, avoids this LeCode): build
                      -- evC_ef directly = evaluate a,b,p DOWN to (u_sel,u_sel,RefEl u_sel) via
                      -- EvalRel-down (le from wit<=val a,val b) + reshape the C-edge (shared with
                      -- SUB-HOLE A), giving Comp without LeCode ef_usel at.
                      evC_ef   = mkEvC u_sel cu_sel le_usel_w'' ef_usel evBase
                      vt_ef    = Val2-U-to-ValTy2 ef_usel ef_uselU
                                   (adqType sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
                      comp_at_ef = EvalRel-Comp (App (App (App C a) b) p) rho crho at ef_usel evA evC_ef
                      finalVal : Val2 H (App sd wit0) (App (App (App sC sa) sb) sp) u at
                      finalVal = app-transport-Val2 at ef_usel comp_at_ef at_U ef_uselU v_sel u
                                   fm_vsel_ef fm le_u_vsel' vt_at vt_ef val_appGoal
                  in finalVal
                  where
                    rho3w = extendEnv (extendEnv (extendEnv rho w'') w'') (RefEl w'')
                    -- the head C-edge shared by both reshapes (unwk of evBase's head)
                    -- membership-derived witness bounds:  w'' <= l', w'' <= r'
                    le_w''_l' = finMem-ref-le1 w'' t' l' r' fm_w'
                    le_w''_r' = finMem-ref-le2 w'' t' l' r' fm_w'
                    ev_a_l' = fst (snd (snd evId))          -- EvalRel a rho l'
                    ev_b_r' = snd (snd (snd evId))          -- EvalRel b rho r'
                    cohl' = EvalRel-coh a rho l' ev_a_l'
                    cohr' = EvalRel-coh b rho r' ev_b_r'

                    -- LeCode of the outer (Ref) argument value against RefEl uS
                    le-ref-arg : (uS x : FinEl) ->
                      EvalRel (Ref (Var fzero)) (extendEnv rho uS) x -> LeCode x (RefEl uS)
                    le-ref-arg uS Bot            _  = tt
                    le-ref-arg uS UCode          ()
                    le-ref-arg uS (FunEl _)      ()
                    le-ref-arg uS (PiCode _ _)   ()
                    le-ref-arg uS (IdCode _ _ _) ()
                    le-ref-arg uS (RefEl w3)     ev = snd ev

                    -- Sigma-form of the branch codomain (baseBody) evaluated at
                    -- (extendEnv rho uS), for a fixed result code c.
                    BaseSig : FinEl -> FinEl -> Set
                    BaseSig uS c =
                      Sigma FinEl (\ v3 -> Pair (EvalRel (Ref (Var fzero)) (extendEnv rho uS) v3)
                        (Sigma FinEl (\ v2 -> Pair (EvalRel (Var fzero) (extendEnv rho uS) v2)
                          (Sigma FinEl (\ v1 -> Pair (EvalRel (Var fzero) (extendEnv rho uS) v1)
                            (EvalRel (wkExpr C) (extendEnv rho uS)
                              (FunEl (cons (mkSigma v1 (FunEl (cons (mkSigma v2 (FunEl (cons (mkSigma v3 c) nil))) nil))) nil))))))))

                    -- reshape to the abstract triple-extended App³ at w''
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

                    -- reshape to the REAL App³ C a b p at rho, evaluating a,b,p
                    -- DOWN to the selection witness values (skips LeCode ef_usel at).
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
      Val2 H (J sC sd sp) (App (App (App sC sa) sb) sp) u at
    branch Bot            evP jb = branchBot jb
    branch UCode          evP ()
    branch (FunEl _)      evP ()
    branch (PiCode _ _)   evP ()
    branch (IdCode _ _ _) evP ()
    branch (RefEl wit)    evP jb = refCore wit evP jb
