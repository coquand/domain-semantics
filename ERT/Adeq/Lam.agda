{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Adeq.Lam  (T_R version of MIN/Adequacy/Lam.agda, single sub)
--
-- A λ-abstraction is valid at its product type.  The combinator is
-- stated for λ(A',B',b) with annotations CONVERTIBLE to the product's
-- (A,B): the model ignores the codomain annotation and evaluates the
-- domain one only through its code, and β ignores annotations, so the
-- annotations enter only through the syntactic β-conversion
-- (beta-ann-conv).  This one combinator serves ty-Lam (A' = A, B' = B)
-- and the congruences conv-cong-Lam-Ty / conv-cong-Lam-body.
--
-- No postulates.
------------------------------------------------------------------------

module ERT.Adeq.Lam where

open import ERT.Adeq.HeadRed
open import ERT.Adeq.Stmt
open import ERT.Adeq.Pi using (transportVal2' ; transportEqVal2')

import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import ERT.Dom.Kernel using (LeCode ; Coherent ; coh-from-aU ; EvalFun ;
  FinMem ; FinMem-coh-u ; cft-from-cf ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open import ERT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv ;
  EvalRel-mon-env ; EnvLe-refl)
open import ERT.Model.EvalSubstitution using (EvalRel-Pi-body)
open import ERT.Model.SoundnessLemmas using (Fits)
open import ERT.Model.Selection using (Selection ; FinMem-Selection ; FinMem-Selection-codomain ; Coherent-Selection)
open import ERT.Model.Strip using (strip ; stripCtx)
open import ERT.RussellSyntax using (Expr ; U ; Pi ; Lam ; App ; subst1 ; Sub ; liftSub ; substExpr)
open import ERT.RussellTyping
open import ERT.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ;
  liftSub-WtSub ; isType-Pi ; subst1-WtSub ; isType-WfCtx)
open import ERT.RussellMetaCong using (subst1-cong-Ty)
open import ERT.RussellReduction using (headred-refl ; headred-step ; headred-beta)

------------------------------------------------------------------------
-- β with annotations: an application of λ(A',B',b), with any
-- annotations convertible to the product (A,B), converts to b[N].
------------------------------------------------------------------------

beta-ann : {n : Nat} {G : Ctx n} {A A1 N : Expr n} {B B1 b : Expr (suc n)} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
  Ann G A B A1 B1 -> HasType G N A ->
  ConvTm G (App A1 B1 (Lam A B b) N) (subst1 b N) (subst1 B N)
beta-ann dA dB db an dN =
  conv-trans
    (conv-sym (conv-cong-App-Ty dA dB (conv-Ty-sym (Ann.annA an)) (conv-Ty-sym (Ann.annB an))
                                (ty-Lam dA dB db) dN))
    (conv-beta dA dB db dN)

beta-ann-conv : {n : Nat} {G : Ctx n} {A A' A1 N : Expr n} {B B' B1 b : Expr (suc n)} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
  ConvTy G A A' -> ConvTy (extend G A) B B' ->
  Ann G A B A1 B1 -> HasType G N A ->
  ConvTm G (App A1 B1 (Lam A' B' b) N) (subst1 b N) (subst1 B N)
beta-ann-conv dA dB db cA cB an dN =
  conv-trans
    (ann-App-fun dA an (conv-sym (conv-cong-Lam-Ty dA dB cA cB db)) dN)
    (beta-ann dA dB db an dN)

------------------------------------------------------------------------
-- The λ combinator (informative case)
------------------------------------------------------------------------

adequacy-ty-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' b : Expr (suc g)} ->
    IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
    ConvTy G A A' -> ConvTy (extend G A) B B' ->
    AdqTy G A -> AdqTy G (Pi A B) -> Adq (extend G A) b B -> AdqConv (extend G A) b B ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) ->
    EvalRel (strip (Lam A' B' b)) rho (FunEl g0) ->
    (b0 : FinEl) -> (f0 : FinFun) ->
    EvalRel (strip (Pi A B)) rho (PiCode b0 f0) ->
    FinMem (FunEl g0) (PiCode b0 f0) ->
    Val2 H (substExpr sigma (Lam A' B' b)) (substExpr sigma (Pi A B)) (FunEl g0) (PiCode b0 f0)
adequacy-ty-Lam {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'} {b = M} d1 d2 d3 cA cB
    IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
  mk-ValPi valTyPi (record
    { domA0 = sA ; codB0 = sB
    ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
    ; cohG = cg ; fmG = fmg ; appV = piAppVal ; appE = piAppEq })
  where
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sM   = substExpr (liftSub sigma) M
    sLam = substExpr sigma (Lam A' B' M)
    fmg  = finMem-funel-fun g0 b f0 fm
    cg   = finMem-funel-coh g0 b f0 fm
    pU   = finMem-funel-wf g0 b f0 fm
    bU   = finMem-piU-dom b f0 pU
    allU = finMem-piU-allU b f0 pU
    cf0  = finMem-piU-cft b f0 pU
    cb   = coh-from-aU b bU
    evAb = fst (snd evA)
    a_lam = fst hu
    bodyLam = snd (snd (snd (snd hu)))
    wsL  = liftSub-WtSub wtsub wfH d1
    htA  = subst-IsType wtsub wfH d1
    htB  = subst-IsType wsL (wf-extend htA) d2
    htM  = subst-HasType wsL (wf-extend htA) d3
    scA  = subst-ConvTy wtsub wfH cA
    scB  = subst-ConvTy wsL (wf-extend htA) cB
    valTyPi = IH-Pi sigma rho crho vs fits wtsub wfH (PiCode b f0) evA pU

    -- the pieces common to both clauses, at a selected pair (u', v')
    module At (u' v' : FinEl) (sel : Selection g0 u' v') where
      ctg       = cft-from-cf g0 cg
      cu'       = Coherent-Selection sel ctg
      fm_u'_b   = FinMem-Selection b f0 sel fmg ctg cb bU
      fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg ctg cf0 allU
      w         = bodyLam u' v' sel
      x         = fst w
      le_x_u'   = fst (snd w)
      fm_x_al   = fst (snd (snd w))
      evM_x_v'  = snd (snd (snd w))
      cx        = FinMem-coh-u x a_lam fm_x_al
      envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
      evM       = EvalRel-mon-env (strip M) (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
      evB       = EvalRel-Pi-body (strip A) (strip B) rho b f0 u' crho cu' evA
      fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
      crho'     = mkSigma crho cu'

    piAppVal : PiAppVal2 H sLam sA sB b f0 g0
    piAppVal u' v' sel {A1} {B1} an N htN valN =
      let open At u' v' sel
          hyp0 = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                   transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'  = ValidSub2-extend sigma N rho u' vs hyp0
          ih   = IH-M (extSub sigma N) (extendEnv rho u') crho' vs' fits' (extSub-WtSub {A = A} wtsub htN) wfH
                   v' evM (EvalFun f0 u') evB fm_v'_ef
          ih'  = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u'))
                   (S.Eq-sym (substExpr-comp sigma B N)) ih
          ih'' = S.Eq-transport (\ E -> Val2 H E (subst1 sB N) v' (EvalFun f0 u'))
                   (S.Eq-sym (substExpr-comp sigma M N)) ih'
      in Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl)
           (beta-ann-conv htA htB htM scA scB an htN) ih''

    piAppEq : PiAppEq2 H sLam sA sB b f0 g0
    piAppEq u' v' sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqvalN =
      let open At u' v' sel
          valN1   = Val2-from-EqVal2-first u' b eqvalN
          valN2   = Val2-from-EqVal2-second u' b eqvalN
          hyp0_N1 = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                      transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          hyp0_N2 = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                      transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'_N1  = ValidSub2-extend sigma N1 rho u' vs hyp0_N1
          vs'_N2  = ValidSub2-extend sigma N2 rho u' vs hyp0_N2
          vcs_ext = ValidConvSub2-extend sigma sigma N1 N2 rho u'
                      (ValidConvSub2-refl {G = G} vs)
                      (transportEqVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b eqvalN)
          wcs_ext = extSub-WtConvSub {A = A} (WtConvSub-refl {G = G} wtsub) cvN
          raw     = IH-cM (extSub sigma N1) (extSub sigma N2) (extendEnv rho u')
                      crho' vs'_N1 vs'_N2 vcs_ext fits'
                      (extSub-WtSub {A = A} wtsub htN1) (extSub-WtSub {A = A} wtsub htN2) wcs_ext wfH
                      v' evM (EvalFun f0 u') evB fm_v'_ef
          raw'    = S.Eq-transport (\ T -> EqVal2 H (subst1 sM N1) T (subst1 sB N1) v' (EvalFun f0 u'))
                      (S.Eq-sym (substExpr-comp sigma M N2))
                      (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) M) (subst1 sB N1) v' (EvalFun f0 u'))
                         (S.Eq-sym (substExpr-comp sigma M N1))
                         (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u'))
                            (S.Eq-sym (substExpr-comp sigma B N1)) raw))
          cvB21   = subst1-cong-Ty (conv-sym cvN) htA htB
          cv2     = conv-conv (beta-ann-conv htA htB htM scA scB an2 htN2) cvB21
      in EqVal2-headred-expand v' (EvalFun f0 u')
           (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl)
           (beta-ann-conv htA htB htM scA scB an1 htN1) cv2 raw'

------------------------------------------------------------------------
-- The full statement
------------------------------------------------------------------------

Adq-Lam : {g : Nat} {G : Ctx g} {A A' : Expr g} {B B' b : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B ->
  ConvTy G A A' -> ConvTy (extend G A) B B' ->
  AdqTy G A -> AdqTy G (Pi A B) -> Adq (extend G A) b B -> AdqConv (extend G A) b B ->
  Adq G (Lam A' B' b) (Pi A B)
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH Bot          hu a evA fm = Val2-Bot a
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (UCode _)    () a evA fm
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu Bot evA fm = tt
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu (UCode _) () fm
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu (FunEl _) () fm
Adq-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm =
  adequacy-ty-Lam d1 d2 d3 cA cB IH-A IH-Pi IH-M IH-cM sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm

------------------------------------------------------------------------
-- The body of a λ at a selected pair (u', v') of its graph, with the
-- argument N valid at the domain: the data needed to apply a body IH at
-- the extended substitution and environment.
------------------------------------------------------------------------

record LamSel {h g : Nat} (H : Ctx h) (G : Ctx g) (A : Expr g) (B M : Expr (suc g))
              (sigma : Sub h g) (rho : EnvApprox g) (N : Expr h)
              (f0 : FinFun) (u' v' : FinEl) : Set where
  field
    crho' : CoherentEnv (extendEnv rho u')
    vs'   : ValidSub2 H (extend G A) (extSub sigma N) (extendEnv rho u')
    fits' : Fits (stripCtx (extend G A)) (extendEnv rho u')
    wt'   : WtSub H (extend G A) (extSub sigma N)
    evM   : EvalRel (strip M) (extendEnv rho u') v'
    evB   : EvalRel (strip B) (extendEnv rho u') (EvalFun f0 u')
    fmv   : FinMem v' (EvalFun f0 u')

lamSel : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' M : Expr (suc g)} ->
  AdqTy G A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (g0 : FinFun) -> EvalRel (strip (Lam A' B' M)) rho (FunEl g0) ->
  (b : FinEl) -> (f0 : FinFun) -> EvalRel (strip (Pi A B)) rho (PiCode b f0) ->
  FinMem (FunEl g0) (PiCode b f0) ->
  (u' v' : FinEl) -> Selection g0 u' v' ->
  (N : Expr h) -> HasType H N (substExpr sigma A) -> Val2 H N (substExpr sigma A) u' b ->
  LamSel H G A B M sigma rho N f0 u' v'
lamSel {A = A} {B = B} {M = M} IH-A sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm u' v' sel N htN valN =
  record { crho' = mkSigma crho cu' ; vs' = ValidSub2-extend sigma N rho u' vs hyp0
         ; fits' = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
         ; wt' = extSub-WtSub {A = A} wtsub htN
         ; evM = EvalRel-mon-env (strip M) (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
         ; evB = EvalRel-Pi-body (strip A) (strip B) rho b f0 u' crho cu' evA
         ; fmv = FinMem-Selection-codomain b f0 sel fmg ctg cf0 allU }
  where
    fmg  = finMem-funel-fun g0 b f0 fm
    cg   = finMem-funel-coh g0 b f0 fm
    pU   = finMem-funel-wf g0 b f0 fm
    bU   = finMem-piU-dom b f0 pU
    allU = finMem-piU-allU b f0 pU
    cf0  = finMem-piU-cft b f0 pU
    cb   = coh-from-aU b bU
    evAb = fst (snd evA)
    ctg  = cft-from-cf g0 cg
    cu'  = Coherent-Selection sel ctg
    fm_u'_b = FinMem-Selection b f0 sel fmg ctg cb bU
    w    = snd (snd (snd (snd hu))) u' v' sel
    x    = fst w
    le_x_u' = fst (snd w)
    evM_x_v' = snd (snd (snd w))
    cx   = FinMem-coh-u x (fst hu) (fst (snd (snd w)))
    envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
    hyp0 = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
             transportVal2' IH-A sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
