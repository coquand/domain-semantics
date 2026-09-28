{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.PiConv  (T_R version of the Π parts of MIN/Adequacy/VE.agda)
--
-- Two combinators, in type form:
--
--   AdqConvTy-Pi : two-substitution validity of Π(A,B)
--                  (from the two-substitution IHs of A and B);
--   AdqETy-Pi    : validity of the type conversion Π(A,B) = Π(A',B')
--                  (conv-Ty-Pi), from the IHs of A = A', B = B' and the
--                  two-substitution IHs of A and B.
--
-- conv-Ty-Pi has no typing premise for B'.  The edges of the right-hand
-- product are therefore obtained at the type level:
--   B'[N1] = B[N1] = B[N2] = B'[N2],
-- from the conversion IH (at N1, N2) and the two-substitution IH of B.
--
-- Non-recursive: all IHs are parameters.  No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.PiConv (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D
open import BCDE4.Adeq.Pi D using (adequacy-ty-Pi ; transportVal2' ; transportEqVal2')

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0 ;
              LevTy ; LevEl ; LPiCode)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; FinMem ;
  coh-from-aU ; FinMem-coh-u ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft)
open import BCDE4.Model.Eval D using (EnvApprox ; extendEnv ; EvalRel ;
  CoherentEnv ; EvalRel-mon-env ; EnvLe-refl)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (Selection ; FinMemAllU-Selection ; FinMem-Selection-UCode)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; subst1 ; Sub ; liftSub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-ConvTy ; liftSub-WtSub ;
  isType-Pi ; presup-r-ConvTy ; ctx-conv-IsType)
open import BCDE4.RussellMetaCong using (subst-cong-IsType ; liftSub-ConvTmSub)
open import BCDE4.RussellReduction using (headred-refl)

open import BCDE4.Levels using (LCtx ; LSub ; lidS)
private variable
  TL : LCtx
  θ : LSub

private
  -- second component of a type equality
  EqValTy2-snd : {h : Nat} {H : Ctx h} {M N : Expr h} (a : FinEl) ->
    EqValTy2 H M N a -> ValTy2 H N a
  EqValTy2-snd Bot          e = tt
  EqValTy2-snd (UCode _)    e = snd e
  EqValTy2-snd (FunEl _)    e = tt
  EqValTy2-snd (PiCode _ _) e = fst (snd e)
  EqValTy2-snd LevTy        e = tt
  EqValTy2-snd (LevEl _)    e = tt
  EqValTy2-snd (LPiCode _)  e = fst (snd e)

------------------------------------------------------------------------
-- Two-substitution validity of a product
------------------------------------------------------------------------

adequacy-conv-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B ->
  AdqConvTy G A -> AdqConvTy (extend G A) B ->
  (sigma sigma' : Sub h g) (rho : EnvApprox (lctx H) lidS g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (strip (Pi A B)) rho (PiCode b f) -> FinMem (PiCode b f) U0 ->
  EqValTy2 H (substExpr sigma (Pi A B)) (substExpr sigma' (Pi A B)) (PiCode b f)
adequacy-conv-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 IH-cA IH-cB
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f hu fm =
  mk-EqValTyPi valTyPi_s valTyPi_s' (record
    { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
    ; redM = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
    ; redN = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA' htB'))
    ; cohF = cf ; fmAllU = allU
    ; convA = convA ; convB = convB
    ; eqA = eqAA' ; edgeET = buildEdgeET })
  where
    IH-A = AdqConvTy-to-AdqTy {G = G} {A = A} IH-cA
    IH-B = AdqConvTy-to-AdqTy {G = extend G A} {A = B} IH-cB
    sA   = substExpr sigma A
    sA'  = substExpr sigma' A
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma') B
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evAb = fst (snd hu)
    bodyPi = snd (snd (snd (snd hu)))

    valTyPi_s  = adequacy-ty-Pi d1 d2 IH-A IH-B IH-cB sigma rho crho vs fits wtsub wfH b f hu fm
    valTyPi_s' = adequacy-ty-Pi d1 d2 IH-A IH-B IH-cB sigma' rho crho vs' fits wtsub' wfH b f hu fm

    eqAA' = IH-cA sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb bU

    htA   = subst-IsType wtsub wfH d1
    htA'  = subst-IsType wtsub' wfH d1
    htB   = subst-IsType (liftSub-WtSub wtsub wfH d1) (wf-extend htA) d2
    htB'  = subst-IsType (liftSub-WtSub wtsub' wfH d1) (wf-extend htA') d2
    convA = subst-cong-IsType wcs wfH d1
    convB = subst-cong-IsType (liftSub-ConvTmSub wcs wfH d1) (wf-extend htA) d2

    buildEdgeET : PiEdgeEqTy2 H sA sB sB' b f
    buildEdgeET u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          cx       = FinMem-coh-u x (fst (snd (snd hu))) (fst (snd (snd w)))
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 (fst (snd w))))
          evB      = EvalRel-mon-env (strip B) (extendEnv rho x) (extendEnv rho u0) v0 (snd (snd (snd w))) envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le a1 evA1 fm1 ->
                       transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le a1 evA1 fm1
          vs_ext   = ValidSub2-extend {A = A} sigma P rho u0 vs hyp0
          valP'    = Val2-EqValTy2-fwd u0 b cb eqAA' valP
          hyp0'    = \ u' cu' le a1 evA1 fm1 ->
                       transportVal2' {G = G} {A = A} IH-A sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le a1 evA1 fm1
          vs_ext'  = ValidSub2-extend {A = A} sigma' P rho u0 vs' hyp0'
          hyp0_eq  = \ u' cu' le a1 evA1 fm1 -> Val2-to-EqVal2 u' a1 (hyp0 u' cu' le a1 evA1 fm1)
          vcs_ext  = ValidConvSub2-extend {A = A} sigma sigma' P P rho u0 vcs hyp0_eq
          wt_ext   = extSub-WtSub {A = A} wtsub htP
          wt_ext'  = extSub-WtSub {A = A} wtsub' (ty-conv htP convA)
          wcs_ext  = extSub-WtConvSub {A = A} wcs (conv-refl htP)
          raw      = IH-cB (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                       crho' vs_ext vs_ext' vcs_ext fits' wt_ext wt_ext' wcs_ext wfH
                       v0 evB fm_v0_U
      in S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma' B P))
           (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma' P) B) v0)
              (S.Eq-sym (substExpr-comp sigma B P)) raw)

AdqConvTy-Pi : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B ->
  AdqConvTy G A -> AdqConvTy (extend G A) B ->
  AdqConvTy G (Pi A B)
AdqConvTy-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH Bot          hu fm = tt
AdqConvTy-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (UCode _)    () fm
AdqConvTy-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl _)    () fm
AdqConvTy-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (PiCode b f) hu fm =
  adequacy-conv-Pi d1 d2 IH-cA IH-cB sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH b f hu fm

------------------------------------------------------------------------
-- Validity of a conversion of products (conv-Ty-Pi)
------------------------------------------------------------------------

adequacy-eq-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' ->
  AdqConvTy G A -> AdqConvTy (extend G A) B -> AdqETy G A A' -> AdqETy (extend G A) B B' ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits (stripCtx G) rho -> WtSub H G sigma -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (strip (Pi A B)) rho (PiCode b f) -> FinMem (PiCode b f) U0 ->
  EqValTy2 H (substExpr sigma (Pi A B)) (substExpr sigma (Pi A' B')) (PiCode b f)
adequacy-eq-Pi {h = h} {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wtsub wfH b f hu fm =
  mk-EqValTyPi valTyPiAB valTyPiA'B' (record
    { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
    ; redM = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
    ; redN = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA' htB'))
    ; cohF = cf ; fmAllU = allU
    ; convA = convA_s ; convB = convB_s
    ; eqA = eqAA' ; edgeET = buildEdgeET })
  where
    IH-A = AdqConvTy-to-AdqTy {G = G} {A = A} IH-cA
    IH-B = AdqConvTy-to-AdqTy {G = extend G A} {A = B} IH-cB
    sA   = substExpr sigma A
    sA'  = substExpr sigma A'
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma) B'
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evAb = fst (snd hu)
    bodyPi = snd (snd (snd (snd hu)))

    valTyPiAB = adequacy-ty-Pi d1 d2 IH-A IH-B IH-cB sigma rho crho vs fits wtsub wfH b f hu fm

    eqAA'  = IH-eA sigma rho crho vs fits wtsub wfH b evAb bU
    eqA'A  = EqValTy2-sym b cb eqAA'

    htA     = subst-IsType wtsub wfH d1
    htB     = subst-IsType (liftSub-WtSub wtsub wfH d1) (wf-extend htA) d2
    convA_s = subst-ConvTy wtsub wfH cA
    convB_s = subst-ConvTy (liftSub-WtSub wtsub wfH d1) (wf-extend htA) cB
    htA'    = presup-r-ConvTy convA_s
    htB'    = ctx-conv-IsType htA htA' convA_s (presup-r-ConvTy convB_s)
    convA'A = conv-Ty-sym convA_s

    -- the codomain data at a selected edge (u0, v0)
    fmU0 : {u0 v0 : FinEl} -> Selection f u0 v0 -> FinMem u0 b
    fmU0 sel = FinMemAllU-Selection b sel allU cf cb bU

    fmV0 : {u0 v0 : FinEl} -> Selection f u0 v0 -> FinMem v0 U0
    fmV0 sel = FinMem-Selection-UCode b sel allU cf

    evB : (u0 v0 : FinEl) -> Selection f u0 v0 -> EvalRel (strip B) (extendEnv rho u0) v0
    evB u0 v0 sel =
      let w        = bodyPi u0 v0 sel
          x        = fst w
          cx       = FinMem-coh-u x (fst (snd (snd hu))) (fst (snd (snd w)))
          cu0      = FinMem-coh-u u0 b (fmU0 sel)
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 (fst (snd w))))
      in EvalRel-mon-env (strip B) (extendEnv rho x) (extendEnv rho u0) v0 (snd (snd (snd w))) envle_xu

    -- the conversion IH of B = B' at an argument N valid at sA
    IHeB-at : (u0 v0 : FinEl) -> Selection f u0 v0 ->
      (N : Expr h) -> HasType H N sA -> Val2 H N sA u0 b ->
      EqValTy2 H (subst1 sB N) (subst1 sB' N) v0
    IHeB-at u0 v0 sel N htN valN =
      let fm_u0_b = fmU0 sel
          cu0     = FinMem-coh-u u0 b fm_u0_b
          fits'   = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          hyp0    = \ u' cu' le a1 evA1 fm1 ->
                      transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le a1 evA1 fm1
          vs'     = ValidSub2-extend {A = A} sigma N rho u0 vs hyp0
          wt'     = extSub-WtSub {A = A} wtsub htN
          raw     = IH-eB (extSub sigma N) (extendEnv rho u0) (mkSigma crho cu0) vs' fits' wt' wfH
                      v0 (evB u0 v0 sel) (fmV0 sel)
      in S.Eq-transport (\ T -> EqValTy2 H (subst1 sB N) T v0) (S.Eq-sym (substExpr-comp sigma B' N))
           (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma N) B') v0)
              (S.Eq-sym (substExpr-comp sigma B N)) raw)

    -- the two-substitution IH of B at a pair of convertible arguments
    IHcB-at : (u0 v0 : FinEl) -> Selection f u0 v0 ->
      (N1 N2 : Expr h) -> HasType H N1 sA -> HasType H N2 sA ->
      ConvTm H N1 N2 sA -> EqVal2 H N1 N2 sA u0 b ->
      EqValTy2 H (subst1 sB N1) (subst1 sB N2) v0
    IHcB-at u0 v0 sel N1 N2 htN1 htN2 cvN eqN =
      let fm_u0_b = fmU0 sel
          cu0     = FinMem-coh-u u0 b fm_u0_b
          fits'   = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          valN1   = Val2-from-EqVal2-first u0 b eqN
          valN2   = Val2-from-EqVal2-second u0 b eqN
          hyp1    = \ u' cu' le a1 evA1 fm1 ->
                      transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le a1 evA1 fm1
          hyp2    = \ u' cu' le a1 evA1 fm1 ->
                      transportVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le a1 evA1 fm1
          vcs_ext = ValidConvSub2-extend {A = A} sigma sigma N1 N2 rho u0
                      (ValidConvSub2-refl {G = G} vs)
                      (transportEqVal2' {G = G} {A = A} IH-A sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqN)
          raw     = IH-cB (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0) (mkSigma crho cu0)
                      (ValidSub2-extend {A = A} sigma N1 rho u0 vs hyp1) (ValidSub2-extend {A = A} sigma N2 rho u0 vs hyp2)
                      vcs_ext fits' (extSub-WtSub {A = A} wtsub htN1) (extSub-WtSub {A = A} wtsub htN2)
                      (extSub-WtConvSub {A = A} (WtConvSub-refl {G = G} wtsub) cvN) wfH
                      v0 (evB u0 v0 sel) (fmV0 sel)
      in S.Eq-transport (\ T -> EqValTy2 H (subst1 sB N1) T v0) (S.Eq-sym (substExpr-comp sigma B N2))
           (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma N2) B) v0)
              (S.Eq-sym (substExpr-comp sigma B N1)) raw)

    edgeV' : PiEdgeVal2 H sA' sB' b f
    edgeV' u0 v0 sel N htN valN =
      EqValTy2-snd v0
        (IHeB-at u0 v0 sel N (ty-conv htN convA'A) (Val2-EqValTy2-fwd u0 b cb eqA'A valN))

    edgeE' : PiEdgeEq2 H sA' sB' b f
    edgeE' u0 v0 sel N1 N2 htN1 htN2 cvN eqN =
      let cv0    = coh-from-aU v0 (fmV0 sel)
          htN1_A = ty-conv htN1 convA'A
          htN2_A = ty-conv htN2 convA'A
          eqN_A  = EqVal2-EqValTy2-fwd u0 b cb eqA'A eqN
          valN1  = Val2-from-EqVal2-first u0 b eqN_A
          valN2  = Val2-from-EqVal2-second u0 b eqN_A
          e1     = EqValTy2-sym v0 cv0 (IHeB-at u0 v0 sel N1 htN1_A valN1)
          e2     = IHcB-at u0 v0 sel N1 N2 htN1_A htN2_A (conv-conv cvN convA'A) eqN_A
          e3     = IHeB-at u0 v0 sel N2 htN2_A valN2
      in EqValTy2-trans v0 cv0 e1 (EqValTy2-trans v0 cv0 e2 e3)

    valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
    valTyPiA'B' = mk-ValTyPi (record
      { domA = sA' ; codB = sB'
      ; red = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA' htB'))
      ; cohF = cf ; fmAllU = allU ; htA = htA' ; htB = htB'
      ; valA = EqValTy2-snd b eqAA' ; edgeV = edgeV' ; edgeE = edgeE' })

    buildEdgeET : PiEdgeEqTy2 H sA sB sB' b f
    buildEdgeET u0 v0 sel P htP valP = IHeB-at u0 v0 sel P htP valP

AdqETy-Pi : {g : Nat} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  IsType G A -> IsType (extend G A) B -> ConvTy G A A' -> ConvTy (extend G A) B B' ->
  AdqConvTy G A -> AdqConvTy (extend G A) B -> AdqETy G A A' -> AdqETy (extend G A) B B' ->
  AdqETy G (Pi A B) (Pi A' B')
AdqETy-Pi d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wt wfH Bot          hu fm = tt
AdqETy-Pi d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wt wfH (UCode _)    () fm
AdqETy-Pi d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wt wfH (FunEl _)    () fm
AdqETy-Pi d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wt wfH (PiCode b f) hu fm =
  adequacy-eq-Pi d1 d2 cA cB IH-cA IH-cB IH-eA IH-eB sigma rho crho vs fits wt wfH b f hu fm
