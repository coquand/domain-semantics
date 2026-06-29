{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Adequacy.NatCaseDep.agda
--
-- Per-rule adequacy combinators for the DEPENDENT caseNat eliminator
-- (ty-Case-dep and the conv-case-zero-dep/-suc-dep/conv-Case-dep
-- conversions).  Parallels NAT.Adequacy.NatCase, threading the motive
-- C : Nat -> U exactly like the dependent-App codomain B.
--
-- No postulates.
------------------------------------------------------------------------

module NAT.Adequacy.NatCaseDep where

open import NAT.Adequacy.HeadRed
open import NAT.Adequacy.Pi using (Adq ; AdqConv ; Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2)
open import NAT.Adequacy.Helpers using (substExpr-comp)
open import NAT.Adequacy.App using (adequacySub2-App ; adequacyV-ty-App ;
  app-transport-Val2 ; app-transport-EqVal2)
open import NAT.Adequacy.VE using (AdqE ; AdqE1)
open import NAT.Adequacy.NatApp using (adequacyV-app-Nat ; adequacyVE-app-Nat)
open import NAT.Adequacy.NatCase using (relevelVal2-Nat ; relevelEqVal2-Nat ;
  unrelevelVal2-Nat ; unrelevelEqVal2-Nat ; valZero-Nat ; max-zero-r ; nat-argVal ; nat-argEq)
open import NAT.Adequacy.Records using (RValPiP ; un-ValPi ; REqValPiP ; un-REqValPi ; eqvalPi-snd)

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; max ; tt ; mkSigma ; fst ; snd ; Sigma ; Pair ; nil ; cons ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
  NatCode ; ZeroEl ; SucEl ; Eq ; refl ; Eq-cong ; Eq-transport ; Eq-sym)
open import NAT.Domain.Rank using (RANK)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ; FinMem-coh-u ;
  FinMem-a-in-U ; Coherent ; CoherentFunTail ; CFTcons ; sucNat-to ; sucNat-from ; finMem-bot-from ;
  finMem-upward ; Comp ; Sup ; EvalFun ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ;
  coh-from-aU ; cft-from-cf ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf)
open CFTcons
open import NAT.Model.Eval using (EnvApprox ; extendEnv ; lookupEnv ; EvalRel ; EvalRel-coh ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe-refl ; EvalRel-Comp ; EvalRel-Sup ; CaseBranch ; CoherentEnv)
open import NAT.Model.EvalSubstitution using (EvalRel-wk ; EvalRel-unwk ;
  EvalRel-subst1-forward ; EvalRel-subst1-backward ; EvalRel-Pi-body)
open import NAT.Model.SoundnessLemmas using (Fits ; EvalRel-subSucC-fwd)
open import NAT.Validity.Core using (Selection ; Coherent-Selection ; Coherent-Selection-val)
open import NAT.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import NAT.Model.Selection using (selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; App ; NatT ; Zero ; Suc ; Case ; Fin ; fzero ; fsuc ;
  Sub ; liftSub ; substExpr ; subst1 ; subst1Sub ; subSucC ; sucSub ; subSucC-subst1 ; subSucC-subst ; wkExpr ;
  subst-wk-comm ; subst-ren ; subst-subst ; wkRen)
open import NAT.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-U ; ty-NatT ; ty-Zero ; ty-Suc ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-case-zero-dep ; conv-case-suc-dep ; conv-Case-dep)
open import NAT.Syntax.Reduction using (HeadRed ; HeadRed1 ; headred-refl ; headred-step ;
  headred-case-zero ; headred-case-suc ; HeadRed-trans ; HeadRed-Case ;
  Red ; mkRed ; Red-refl ; subst-subst1-comm)
open import NAT.Model.Soundness using (theorem1)
open import NAT.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm ;
  subst-ConvTm-cross ; subst1-wk ; wk-HasType ; codSubSucC ; ty-subst1-motive ;
  subst1-cong-ConvTm ; liftSub-WtSub-NatT ;
  typing-WfCtx ; typing-ConvTm)
open import NAT.Model.Soundness using (convSound)
open import NAT.Validity.Stratified using (Red3 ; mkRed3 ; Bundle ; Stage)

------------------------------------------------------------------------
-- conv-case-zero-dep : Case Zero a b = a : C[0]   (head-expand to the zero
-- branch; the scrutinee is the literal Zero, so the result type C[0] is the
-- same as the branch type -- no motive transport needed, identical to the
-- non-dependent conv-case-zero).
------------------------------------------------------------------------

adequacyEqSub2-case-zero-dep : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {C : Expr (suc g)} {a b : Expr g} ->
  HasType (extend G NatT) C U -> HasType G a (subst1 C Zero) ->
  HasType G b (Pi NatT (subSucC C)) ->
  Adq G a (subst1 C Zero) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case Zero a b) rho u ->
  (ac : FinEl) -> EvalRel (subst1 C Zero) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case Zero a b)) (substExpr sigma a)
           (substExpr sigma (subst1 C Zero)) u ac
adequacyEqSub2-case-zero-dep dC da db IHa sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let hu_c  = convSound (conv-case-zero-dep dC da db) rho fits u hu
      val_a = IHa sigma rho crho vs fits wtsub wfH u hu_c ac evAc fm
      hr    = headred-step headred-case-zero headred-refl
      cv    = subst-ConvTm wtsub wfH (conv-case-zero-dep dC da db)
      hta   = subst-HasType wtsub wfH da
  in EqVal2-headred-expand u ac hr headred-refl cv (conv-refl hta)
       (Val2-to-EqVal2 u ac val_a)

------------------------------------------------------------------------
-- valSuc-direct : the Suc value record built from a predecessor-validity
-- provider for the (free, H-level) predecessor term N.  Mirrors
-- adequacyV-ty-Suc's SucEl/NatCode body, decoupled from a G-level term.
------------------------------------------------------------------------

valSuc-direct : {h : Nat} {H : Ctx h} (N : Expr h) (z : FinEl) ->
  WfCtx H -> HasType H N NatT ->
  ((v' : FinEl) -> Coherent v' -> LeCode v' z -> FinMem v' NatCode ->
     Val2 H N NatT v' NatCode) ->
  (u a : FinEl) -> LeCode u (SucEl z) -> Coherent u -> LeCode a NatCode -> FinMem u a ->
  Val2 H (Suc N) NatT u a
valSuc-direct N z wfH htN prov u Bot          le cu nac fm = tt
valSuc-direct N z wfH htN prov u UCode        le cu ()
valSuc-direct N z wfH htN prov u (FunEl _)    le cu ()
valSuc-direct N z wfH htN prov u (PiCode _ _) le cu ()
valSuc-direct N z wfH htN prov u ZeroEl       le cu ()
valSuc-direct N z wfH htN prov u (SucEl _)    le cu ()
valSuc-direct N z wfH htN prov Bot          NatCode le cu nac fm = tt
valSuc-direct N z wfH htN prov UCode        NatCode () cu nac fm
valSuc-direct N z wfH htN prov (FunEl _)    NatCode () cu nac fm
valSuc-direct N z wfH htN prov (PiCode _ _) NatCode () cu nac fm
valSuc-direct N z wfH htN prov NatCode      NatCode () cu nac fm
valSuc-direct N z wfH htN prov ZeroEl       NatCode () cu nac fm
valSuc-direct {H = H} N z wfH htN prov (SucEl v') NatCode le cu nac fm =
  let fm_v'   = sucNat-to v' fm
      valP_v' = prov v' cu le fm_v'
      valP    = relevelVal2-Nat v' valP_v'
  in mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
       (record { pred = N
               ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htN))
               ; htP  = htN ; valP = valP })

------------------------------------------------------------------------
-- adq-subSucC : the motive codomain validity.  From the validity of the
-- motive C (in extend G NatT), produce the validity of subSucC C = C[x:=S x]
-- by instantiating C's IH at the composite substitution σ∘sucSub and the
-- env whose head is SucEl z (z = the original head value).  This is the
-- IHB that the App combinators need for the dependent succ branch.
------------------------------------------------------------------------

adq-subSucC : {g : Nat} {G : Ctx g} {C : Expr (suc g)} ->
  Adq (extend G NatT) C U -> Adq (extend G NatT) (subSucC C) U
adq-subSucC {g} {G} {C} IHC {h} {H} sigma (extendEnv rho0 z) crho vs fits wtsub wfH u hu a evA fm =
  Eq-transport (\ T -> Val2 H T U u a) (Eq-sym eqterm) result
  where
    sg'' : Sub h (suc g)
    sg'' = extSub (\ j -> sigma (fsuc j)) (Suc (sigma fzero))
    rho'' : EnvApprox (suc g)
    rho'' = extendEnv rho0 (SucEl z)
    eqterm : Eq (substExpr sigma (subSucC C)) (substExpr sg'' C)
    eqterm = Eq-trans (subst-subst sigma sucSub C)
               (substExpr-ext _ sg'' (\ { fzero -> refl ; (fsuc k) -> refl }) C)
    hu'' : EvalRel C rho'' u
    hu'' = EvalRel-subSucC-fwd C rho0 z u (fst crho) (snd crho) hu
    prov0 : (v' : FinEl) -> Coherent v' -> LeCode v' z -> FinMem v' NatCode ->
            Val2 H (sigma fzero) NatT v' NatCode
    prov0 v' cv' lv' fmv' = vs fzero v' cv' lv' NatCode (mkSigma tt (LeCode-refl NatCode tt)) fmv'
    vs-tail : ValidSub2 H G (\ j -> sigma (fsuc j)) rho0
    vs-tail j u' cu' le' a' evA' fm' =
      Val2-transport-A {u = u'} {a = a'} (subst-ren sigma wkRen (lookup G j))
        (vs (fsuc j) u' cu' le' a' (EvalRel-wk (lookup G j) rho0 z a' evA') fm')
    hyp : (u' : FinEl) -> Coherent u' -> LeCode u' (SucEl z) ->
          (a' : FinEl) -> EvalRel NatT rho0 a' -> FinMem u' a' ->
          Val2 H (Suc (sigma fzero)) NatT u' a'
    hyp u' cu' le' a' evA' fm' =
      valSuc-direct (sigma fzero) z wfH (wtsub fzero) prov0 u' a' le' cu' (snd evA') fm'
    vs'' : ValidSub2 H (extend G NatT) sg'' rho''
    vs'' = ValidSub2-extend (\ j -> sigma (fsuc j)) (Suc (sigma fzero)) rho0 (SucEl z) vs-tail hyp
    fmz : FinMem z NatCode
    fmz = finMem-upward z (fst (snd fits)) NatCode
            (snd (snd (snd (snd fits)))) (fst (snd (snd (snd fits)))) tt
            (fst (snd (snd fits))) tt
    fits'' : Fits (extend G NatT) rho''
    fits'' = mkSigma (fst fits)
               (mkSigma NatCode (mkSigma (sucNat-from z fmz) (mkSigma tt (LeCode-refl NatCode tt))))
    wtsub'' : WtSub H (extend G NatT) sg''
    wtsub'' fzero = ty-Suc (wtsub fzero)
    wtsub'' (fsuc j) =
      Eq-transport (\ T -> HasType H (sigma (fsuc j)) T)
        (Eq-trans (subst-ren sigma wkRen (lookup G j)) (Eq-sym (subst-ren sg'' wkRen (lookup G j))))
        (wtsub (fsuc j))
    result : Val2 H (substExpr sg'' C) U u a
    result = IHC sg'' rho'' crho vs'' fits'' wtsub'' wfH u hu'' a evA fm

------------------------------------------------------------------------
-- conv-case-suc-dep : Case (Suc m) a b = App b m : C[S m]   (head-expand
-- to the contractum App b m, whose Val2 is the standard application of b
-- to m, built by adequacySub2-App with the dependent codomain subSucC C
-- (its validity supplied by adq-subSucC).  The result type subst1 (subSucC C) m
-- = subst1 C (Suc m) lines up by subSucC-subst1.
------------------------------------------------------------------------

adequacyEqSub2-case-suc-dep : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {C : Expr (suc g)} {m a b : Expr g} ->
  HasType (extend G NatT) C U -> HasType G m NatT -> HasType G a (subst1 C Zero) ->
  HasType G b (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> Adq G m NatT -> Adq G b (Pi NatT (subSucC C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case (Suc m) a b) rho u ->
  (ac : FinEl) -> EvalRel (subst1 C (Suc m)) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case (Suc m) a b)) (substExpr sigma (App b m))
           (substExpr sigma (subst1 C (Suc m))) u ac
adequacyEqSub2-case-suc-dep {H = H} {C = C} {m = m} {b = b}
  dC dm da db IHC IHm IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let wfG    = typing-WfCtx dm
      hu_app = convSound (conv-case-suc-dep dC dm da db) rho fits u hu
      cu     = EvalRel-coh (App b m) rho u hu_app
      evAc'  = Eq-transport (\ T -> EvalRel T rho ac) (Eq-sym (subSucC-subst1 C m)) evAc
      val0   = adequacySub2-App (ty-NatT wfG) (codSubSucC dC) db dm IHb IHm (adq-subSucC IHC)
                 sigma rho crho vs fits wtsub wfH u cu hu_app ac evAc' fm
      val_app = Eq-transport (\ T -> Val2 H (substExpr sigma (App b m)) T u ac)
                  (Eq-cong (substExpr sigma) (subSucC-subst1 C m)) val0
      hr     = headred-step headred-case-suc headred-refl
      cv     = subst-ConvTm wtsub wfH (conv-case-suc-dep dC dm da db)
      htAp   = snd (typing-ConvTm cv)
  in EqVal2-headred-expand u ac hr headred-refl cv (conv-refl htAp)
       (Val2-to-EqVal2 u ac val_app)

------------------------------------------------------------------------
-- motiveEqValTy2 : the semantic motive type-transport.  Given two H-terms
-- tX, tM that are cross-valid as Nat values at the scrutinee value vM
-- (e.g. tX = Zero or Suc pred, tM = σM, when σM ↠ tX), produce
--   EqValTy2 H (subst1 sC tX) (subst1 sC tM) ac
-- by running the motive's CROSS adequacy at the two extended substitutions
-- (extSub σ tX) vs (extSub σ tM).  (Mirrors App.adequacyV-subst1-cod, but the
-- two substitutions share the outer σ and differ only in the last component.)
------------------------------------------------------------------------

motiveEqValTy2 : {h g : Nat} {H : Ctx h} {G : Ctx g} {C : Expr (suc g)} ->
  WfCtx G -> AdqConv (extend G NatT) C U ->
  (sigma : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (tX tM : Expr h) -> HasType H tX NatT -> HasType H tM NatT -> ConvTm H tX tM NatT ->
  (vM : FinEl) -> Coherent vM -> FinMem vM NatCode ->
  ((u' a' : FinEl) -> LeCode u' vM -> Coherent u' -> EvalRel NatT rho a' -> FinMem u' a' ->
     Val2 H tX NatT u' a') ->
  ((u' a' : FinEl) -> LeCode u' vM -> Coherent u' -> EvalRel NatT rho a' -> FinMem u' a' ->
     Val2 H tM NatT u' a') ->
  ((u' a' : FinEl) -> LeCode u' vM -> Coherent u' -> EvalRel NatT rho a' -> FinMem u' a' ->
     EqVal2 H tX tM NatT u' a') ->
  (ac : FinEl) -> EvalRel C (extendEnv rho vM) ac -> FinMem ac UCode ->
  EqValTy2 H (subst1 (substExpr (liftSub sigma) C) tX)
             (subst1 (substExpr (liftSub sigma) C) tM) ac
motiveEqValTy2 {H = H} {C = C} wfG IHCc sigma rho crho vs fits wtsub wfH
  tX tM htX htM cvXM vM cvM fmvM provX provM provXM ac evC fmac =
  let sg1 = extSub sigma tX
      sg2 = extSub sigma tM
      crho-ext = mkSigma crho cvM
      fits-ext = mkSigma fits (mkSigma NatCode (mkSigma fmvM (mkSigma tt (LeCode-refl NatCode tt))))
      vs1 = ValidSub2-extend sigma tX rho vM vs
              (\ u' cu' le' a' evA' fm' -> provX u' a' le' cu' evA' fm')
      vs2 = ValidSub2-extend sigma tM rho vM vs
              (\ u' cu' le' a' evA' fm' -> provM u' a' le' cu' evA' fm')
      vcs = ValidConvSub2-extend {A = NatT} sigma sigma tX tM rho vM
              (\ i u' cu' le' a' evA' fm' -> Val2-to-EqVal2 u' a' (vs i u' cu' le' a' evA' fm'))
              (\ u' cu' le' a' evA' fm' -> provXM u' a' le' cu' evA' fm')
      wt1 = extSub-WtSub wtsub wfH (ty-NatT wfG) htX
      wt2 = extSub-WtSub wtsub wfH (ty-NatT wfG) htM
      wcs = extSub-WtConvSub wtsub (\ i -> conv-refl (wtsub i)) wfH (ty-NatT wfG) cvXM
      evU = mkSigma tt (LeCode-refl UCode tt)
      raw = IHCc sg1 sg2 (extendEnv rho vM) crho-ext vs1 vs2 vcs fits-ext wt1 wt2 wcs wfH
              ac evC UCode evU fmac
      r1 = Eq-transport (\ T -> EqVal2 H T (substExpr sg2 C) U ac UCode)
             (Eq-sym (substExpr-comp sigma C tX)) raw
      r2 = Eq-transport (\ T -> EqVal2 H (subst1 (substExpr (liftSub sigma) C) tX) T U ac UCode)
             (Eq-sym (substExpr-comp sigma C tM)) r1
  in EqVal2-U-to-EqValTy2 ac fmac r2

------------------------------------------------------------------------
-- Coherence: two values of the same scrutinee M are compatible (Comp), and
-- for Nat values Comp pins the shape -- so the type's M-value vM is forced
-- ≤ the term's scrutinee value when the latter is ZeroEl / shares shape on
-- SucEl.  (This is why the dependent case's term/type values stay aligned.)
------------------------------------------------------------------------

comp-Zero-le : (x : FinEl) -> Comp ZeroEl x -> LeCode x ZeroEl
comp-Zero-le Bot          c = tt
comp-Zero-le UCode        ()
comp-Zero-le (FunEl _)    ()
comp-Zero-le (PiCode _ _) ()
comp-Zero-le NatCode      ()
comp-Zero-le ZeroEl       c = tt
comp-Zero-le (SucEl _)    ()

------------------------------------------------------------------------
-- adq-subst1-CM : the SINGLE-substitution analogue of the App codomain's
-- subst1 validity (App.adequacyV-subst1-cod is the cross version).  From the
-- motive's single-sub IH and the scrutinee's single-sub IH, produce the
-- validity of the (dependent) result type subst1 C M : U as a single-sub
-- Adq.  Used to supply vt_ac / vt_ef at the result type for the SucEl branch's
-- application transport, and the type validity directly elsewhere.
------------------------------------------------------------------------

adq-subst1-CM : {g : Nat} {G : Ctx g} {C : Expr (suc g)} {M : Expr g} ->
  HasType (extend G NatT) C U -> HasType G M NatT ->
  Adq (extend G NatT) C U -> Adq G M NatT ->
  Adq G (subst1 C M) U
adq-subst1-CM {g} {G} {C} {M} dC dM IHC IHM {h} {H} sigma rho crho vs fits wtsub wfH u hu ac evU fm =
  Eq-transport (\ T -> Val2 H T U u ac) (subst-subst1-comm sigma C M) r1
  where
    wfG  = typing-WfCtx dM
    sM   = substExpr sigma M
    fwd  = EvalRel-subst1-forward C M rho u crho hu
    vF   = fst fwd
    evM_vF = fst (snd fwd)
    evC_vF = snd (snd fwd)
    typed = theorem1 dM rho fits vF evM_vF
    vF'  = fst typed
    aFit = fst (snd typed)
    leF  = fst (snd (snd typed))
    evM_vF' = fst (snd (snd (snd typed)))
    fmF' = fst (snd (snd (snd (snd typed))))
    evN_aFit = snd (snd (snd (snd (snd typed))))
    cvF' = FinMem-coh-u vF' aFit fmF'
    cvF  = EvalRel-coh M rho vF evM_vF
    envle = mkSigma (EnvLe-refl rho crho) (mkSigma cvF (mkSigma cvF' leF))
    evC_vF' = EvalRel-mon-env C (extendEnv rho vF) (extendEnv rho vF') u evC_vF envle
    crho-ext = mkSigma crho cvF'
    fits-ext = mkSigma fits (mkSigma aFit (mkSigma fmF' evN_aFit))
    hyp = \ u' cu' le' a' evA' fm' ->
      let evM_u' = EvalRel-down M rho vF' u' crho cu' evM_vF' le'
      in IHM sigma rho crho vs fits wtsub wfH u' evM_u' a' evA' fm'
    vs-ext = ValidSub2-extend sigma sM rho vF' vs hyp
    htSM = subst-HasType wtsub wfH dM
    wtsub-ext = extSub-WtSub wtsub wfH (ty-NatT wfG) htSM
    raw = IHC (extSub sigma sM) (extendEnv rho vF') crho-ext vs-ext fits-ext wtsub-ext wfH u evC_vF' ac evU fm
    r1 = Eq-transport (\ T -> Val2 H T U u ac) (Eq-sym (substExpr-comp sigma C sM)) raw

------------------------------------------------------------------------
-- eqZero-cross : the Zero-vs-(reduces-to-Zero) cross EqVal2 at NatT, the
-- provXM provider fed to motiveEqValTy2 in the ZeroEl branch.  N ↠ Zero.
-- Mirrors valZero-Nat's clause structure (the second term differs only in
-- its Red3 witness, supplied as redN).
------------------------------------------------------------------------

eqZero-cross : {h : Nat} {H : Ctx h} (N : Expr h) -> WfCtx H ->
  Red3 H N Zero NatT ->
  (u a : FinEl) -> LeCode u ZeroEl -> Coherent u -> LeCode a NatCode -> FinMem u a ->
  EqVal2 H Zero N NatT u a
eqZero-cross N wfH redN u           Bot          _  _  _  _ = tt
eqZero-cross N wfH redN Bot         NatCode      _  _  _  _ = tt
eqZero-cross N wfH redN UCode       NatCode      () _  _  _
eqZero-cross N wfH redN (FunEl _)   NatCode      () _  _  _
eqZero-cross N wfH redN (PiCode _ _) NatCode     () _  _  _
eqZero-cross N wfH redN NatCode     NatCode      () _  _  _
eqZero-cross {H = H} N wfH redN ZeroEl NatCode   _  _  _  _ =
  mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
          (mkSigma (mkRed3 headred-refl (conv-refl (ty-Zero wfH))) redN)
eqZero-cross N wfH redN (SucEl _)   NatCode      () _  _  _
eqZero-cross N wfH redN u           UCode        _  _  () _
eqZero-cross N wfH redN u           (FunEl _)    _  _  () _
eqZero-cross N wfH redN u           (PiCode _ _) _  _  () _
eqZero-cross N wfH redN u           ZeroEl       _  _  () _
eqZero-cross N wfH redN u           (SucEl _)    _  _  () _

------------------------------------------------------------------------
-- eqSuc-cross : the (Suc P)-vs-(reduces-to-Suc-P) cross EqVal2 at NatT, the
-- provXM provider for the SucEl branch.  N ↠ Suc P, both predecessors are the
-- SAME term P, so the cross is reflexive on P.  Mirrors valSuc-direct.
------------------------------------------------------------------------

eqSuc-cross : {h : Nat} {H : Ctx h} (N P : Expr h) (z : FinEl) ->
  WfCtx H -> HasType H P NatT -> Red3 H N (Suc P) NatT ->
  ((v' : FinEl) -> Coherent v' -> LeCode v' z -> FinMem v' NatCode ->
     Val2 H P NatT v' NatCode) ->
  (u a : FinEl) -> LeCode u (SucEl z) -> Coherent u -> LeCode a NatCode -> FinMem u a ->
  EqVal2 H (Suc P) N NatT u a
eqSuc-cross N P z wfH htP redN prov u           Bot          le cu nac fm = tt
eqSuc-cross N P z wfH htP redN prov u           UCode        le cu ()
eqSuc-cross N P z wfH htP redN prov u           (FunEl _)    le cu ()
eqSuc-cross N P z wfH htP redN prov u           (PiCode _ _) le cu ()
eqSuc-cross N P z wfH htP redN prov u           ZeroEl       le cu ()
eqSuc-cross N P z wfH htP redN prov u           (SucEl _)    le cu ()
eqSuc-cross N P z wfH htP redN prov Bot         NatCode      le cu nac fm = tt
eqSuc-cross N P z wfH htP redN prov UCode       NatCode      () cu nac fm
eqSuc-cross N P z wfH htP redN prov (FunEl _)   NatCode      () cu nac fm
eqSuc-cross N P z wfH htP redN prov (PiCode _ _) NatCode     () cu nac fm
eqSuc-cross N P z wfH htP redN prov NatCode     NatCode      () cu nac fm
eqSuc-cross N P z wfH htP redN prov ZeroEl      NatCode      () cu nac fm
eqSuc-cross {H = H} N P z wfH htP redN prov (SucEl v') NatCode le cu nac fm =
  let fm_v'   = sucNat-to v' fm
      valP_v' = prov v' cu le fm_v'
      valP    = relevelVal2-Nat v' valP_v'
      eqP     = relevelEqVal2-Nat v' (Val2-to-EqVal2 v' NatCode valP_v')
      redSP   = mkRed3 headred-refl (conv-refl (ty-Suc htP))
  in mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
       (mkSigma (record { pred = P ; red = redSP ; htP = htP ; valP = valP })
         (mkSigma (record { pred = P ; red = redN ; htP = htP ; valP = valP })
           (record { predM = P ; predN = P ; redM = redSP ; redN = redN
                   ; htM = htP ; htN = htP ; cvP = conv-refl htP ; eqP = eqP })))

------------------------------------------------------------------------
-- adequacyV-app-Nat-dep : the value-level application core for the SucEl
-- branch of the DEPENDENT eliminator.  Like NatApp.adequacyV-app-Nat (free
-- H-level argument N + value provider), but the succ-branch function b has
-- the DEPENDENT codomain subSucC C, so the result type subst1 sCD N is only
-- EqValTy2-equal (not Eq-equal) to the dependent case type subst1 C M.  The
-- application value is therefore type-transported at the selected codomain
-- code ef_usel (motiveEqValTy2 at tX = Suc N, tM = sM) before app-transport.
-- The codomain / scrutinee values stay aligned through v'' (M ↠ SucEl v'',
-- the function edge arg v ≤ v''); the predecessor's validity valP at v''
-- supplies both the application argument and the motive providers.
------------------------------------------------------------------------

adequacyV-app-Nat-dep : {h g : Nat} {H : Ctx h} {G : Ctx g} {C : Expr (suc g)} {M b : Expr g} ->
  HasType (extend G NatT) C U -> HasType G M NatT -> HasType G b (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> AdqConv (extend G NatT) C U -> Adq G M NatT ->
  Adq G b (Pi NatT (subSucC C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (v v'' u1 : FinEl) -> LeCode v v'' -> Coherent v -> Coherent v'' -> FinMem v'' NatCode ->
  EvalRel M rho (SucEl v'') ->
  EvalRel b rho (FunEl (cons (mkSigma v u1) nil)) ->
  (N : Expr h) -> HasType H N NatT -> Red3 H (substExpr sigma M) (Suc N) NatT ->
  Val2 H N NatT v'' NatCode ->
  (ac1 : FinEl) -> EvalRel (subst1 C M) rho ac1 -> FinMem u1 ac1 ->
  Val2 H (App (substExpr sigma b) N) (substExpr sigma (subst1 C M)) u1 ac1
adequacyV-app-Nat-dep {H = H} {G = G} {C = C} {M = M} {b = b}
  dC dM db IHC IHCc IHM IHb sigma rho crho vs fits wtsub wfH
  v v'' u1 le_v_v'' cohv cv'' fm_v'' evM_scrut evF_sing N htN redSM valP_v'' ac1 evAc1 fm1 =
  transported
  where
    wfG  = typing-WfCtx dM
    sf   = substExpr sigma b
    sM   = substExpr sigma M
    sC   = substExpr (liftSub sigma) C
    sCD  = substExpr (liftSub sigma) (subSucC C)
    RT   = substExpr sigma (subst1 C M)
    sing = cons (mkSigma v u1) nil
    cv0  = key-coh (EvalRel-coh b rho (FunEl sing) evF_sing)
    htsM = subst-HasType wtsub wfH dM
    cvSucN-sM = conv-sym (Red3.ct redSM)
    evU  = mkSigma tt (LeCode-refl UCode tt)

    eq-cod : Eq (subst1 sCD N) (subst1 sC (Suc N))
    eq-cod = Eq-trans (Eq-cong (\ X -> subst1 X N) (subSucC-subst sigma C)) (subSucC-subst1 sC N)

    argVal : (u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
      Val2 H N NatT u' a'
    argVal = nat-argVal N rho v v'' cohv cv'' fm_v'' le_v_v'' valP_v''

    predProv : (w : FinEl) -> Coherent w -> LeCode w v'' -> FinMem w NatCode -> Val2 H N NatT w NatCode
    predProv w cw lew fmw = restrictVal2 H N NatT v'' w NatCode lew fmw fm_v'' valP_v''

    appVal-dispatch : (ub ap : FinEl) ->
      LeCode (FunEl sing) ub ->
      EvalRel b rho ub -> EvalRel (Pi NatT (subSucC C)) rho ap ->
      FinMem ub ap ->
      Val2 H sf (Pi NatT sCD) ub ap ->
      Val2 H (App sf N) RT u1 ac1
    appVal-dispatch Bot          ap () evFb evPab fmba valba
    appVal-dispatch UCode        ap () evFb evPab fmba valba
    appVal-dispatch (PiCode _ _) ap () evFb evPab fmba valba
    appVal-dispatch (FunEl g_big) Bot          lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) UCode        lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) NatCode      lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) ZeroEl       lf evFb evPab () valba
    appVal-dispatch (FunEl g_big) (SucEl _)    lf evFb evPab () valba
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
          sbel     = selectionBelow g_big v (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sbel
          v_sel    = fst (snd sbel)
          sel_big  = fst (snd (snd sbel))
          le_usel  = fst (snd (snd (snd sbel)))
          eq_vsel  = snd (snd (snd (snd sbel)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          le_usel_v'' = LeCode-trans u_sel v v'' cu_sel cohv cv'' le_usel le_v_v''
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          val_arg  = argVal u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          vpi_fun  = un-ValPi valba
          B0_fun   = RValPiP.codB0 vpi_fun
          red_fun  = RValPiP.red vpi_fun
          uniq_fun = Red-unique-Pi2 (Red-refl {G = H} {M = Pi NatT sCD} {A = U}) (mkRed (Red3.hr red_fun))
          eqA_fun  = fst uniq_fun
          eqB_fun  = snd uniq_fun
          pav_fun  = RValPiP.appV vpi_fun
          val_arg' = S.Eq-transport (\ X -> Val2 H N X u_sel b_pi) eqA_fun val_arg
          ht_N_A0  = S.Eq-transport (\ X -> HasType H N X) eqA_fun htN
          val_app_raw = pav_fun u_sel v_sel sel_big N ht_N_A0 val_arg'
          ef_usel  = EvalFun f_pi u_sel
          val_app : Val2 H (App sf N) (subst1 sCD N) v_sel ef_usel
          val_app = S.Eq-transport
            (\ X -> Val2 H (App sf N) (subst1 X N) v_sel ef_usel)
            (S.Eq-sym eqB_fun) val_app_raw
          -- codomain eval at the selected arg, bridged through the scrutinee
          evCod_ef = EvalRel-Pi-body NatT (subSucC C) rho b_pi f_pi u_sel crho cu_sel evPab
          evC_suc  = EvalRel-subSucC-fwd C rho u_sel ef_usel crho cu_sel evCod_ef
          evM_su_sel = EvalRel-down M rho (SucEl v'') (SucEl u_sel) crho cu_sel evM_scrut le_usel_v''
          evC_ef   = EvalRel-subst1-backward C M rho (SucEl u_sel) ef_usel crho evM_su_sel evC_suc
          comp_ac_ef = EvalRel-Comp (subst1 C M) rho crho ac1 ef_usel evAc1 evC_ef
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          -- type validity at the result type subst1 C M (single-sub)
          vt_ac = Val2-U-to-ValTy2 ac1 ac1_U
                    (adq-subst1-CM dC dM IHC IHM sigma rho crho vs fits wtsub wfH ac1 evAc1 UCode evU ac1_U)
          vt_ef = Val2-U-to-ValTy2 ef_usel ef_uselU
                    (adq-subst1-CM dC dM IHC IHM sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
          -- motive transport of the application value subst1 sC (Suc N) -> subst1 sC sM at ef_usel
          fm_svsel = sucNat-from v'' fm_v''
          envle_up = mkSigma (EnvLe-refl rho crho) (mkSigma cu_sel (mkSigma cv'' le_usel_v''))
          evC_sv'' = EvalRel-mon-env C (extendEnv rho (SucEl u_sel)) (extendEnv rho (SucEl v''))
                       ef_usel evC_suc envle_up
          provX = \ u' a' le cu' evNa' fm' ->
            valSuc-direct N v'' wfH htN predProv u' a' le cu' (snd evNa') fm'
          provM = \ u' a' le cu' evNa' fm' ->
            IHM sigma rho crho vs fits wtsub wfH u'
              (EvalRel-down M rho (SucEl v'') u' crho cu' evM_scrut le) a' evNa' fm'
          provXM = \ u' a' le cu' evNa' fm' ->
            eqSuc-cross sM N v'' wfH htN redSM predProv u' a' le cu' (snd evNa') fm'
          eqvty_ef = motiveEqValTy2 wfG IHCc sigma rho crho vs fits wtsub wfH
                       (Suc N) sM (ty-Suc htN) htsM cvSucN-sM (SucEl v'') cv'' fm_svsel
                       provX provM provXM ef_usel evC_sv'' ef_uselU
          val_app1 : Val2 H (App sf N) (subst1 sC (Suc N)) v_sel ef_usel
          val_app1 = S.Eq-transport (\ T -> Val2 H (App sf N) T v_sel ef_usel) eq-cod val_app
          val_appX : Val2 H (App sf N) (subst1 sC sM) v_sel ef_usel
          val_appX = Val2-EqValTy2-fwd v_sel ef_usel c_efusel eqvty_ef val_app1
          val_app2 : Val2 H (App sf N) RT v_sel ef_usel
          val_app2 = S.Eq-transport (\ T -> Val2 H (App sf N) T v_sel ef_usel)
                       (subst-subst1-comm sigma C M) val_appX
      in app-transport-Val2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app2

    transported : Val2 H (App sf N) RT u1 ac1
    transported =
      let typed_f = theorem1 db rho fits (FunEl sing) evF_sing
          u_big   = fst typed_f
          a_pi    = fst (snd typed_f)
          le_sing = fst (snd (snd typed_f))
          evF_big = fst (snd (snd (snd typed_f)))
          fm_big  = fst (snd (snd (snd (snd typed_f))))
          evPi    = snd (snd (snd (snd (snd typed_f))))
          val_fun = IHb sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big
      in appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

------------------------------------------------------------------------
-- adequacyV-ty-Case-dep : the single-substitution value combinator for
-- ty-Case-dep.  Dispatches on the scrutinee value w; the result type is the
-- DEPENDENT subst1 C M, so each non-Bot branch type-transports (ZeroEl via
-- motiveEqValTy2 at tX=Zero; SucEl via the dependent app core, which transports
-- internally) and head-expands with the dependent conv-Case-dep + conv-case-*-dep
-- conversions (conv-conv'd from subst1 C (branch) to subst1 C M).
------------------------------------------------------------------------

adequacyV-ty-Case-dep : {h g : Nat} {H : Ctx h} {G : Ctx g} {C : Expr (suc g)} {M a b : Expr g} ->
  HasType (extend G NatT) C U -> HasType G M NatT ->
  HasType G a (subst1 C Zero) -> HasType G b (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> AdqConv (extend G NatT) C U -> Adq G M NatT ->
  Adq G a (subst1 C Zero) -> Adq G b (Pi NatT (subSucC C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel (subst1 C M) rho ac -> FinMem u ac ->
  Val2 H (Case (substExpr sigma M) (substExpr sigma a) (substExpr sigma b))
         (substExpr sigma (subst1 C M)) u ac
adequacyV-ty-Case-dep {H = H} {C = C} {M = M} {a = a} {b = b}
  dC dM da db IHC IHCc IHM IHa IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  Eq-transport (\ T -> Val2 H (Case sM sa sb) T u ac) (subst-subst1-comm sigma C M)
    (branch (fst hu) (fst (snd hu)) (snd (snd hu)))
  where
    sM = substExpr sigma M ; sa = substExpr sigma a
    sb = substExpr sigma b ; sC = substExpr (liftSub sigma) C
    wfG  = typing-WfCtx dM
    htsM = subst-HasType wtsub wfH dM
    htCdep : HasType (extend H NatT) sC U
    htCdep = subst-HasType (liftSub-WtSub-NatT wtsub wfH) (wf-extend (ty-NatT wfH)) dC
    htaZ : HasType H sa (subst1 sC Zero)
    htaZ = Eq-transport (\ T -> HasType H sa T) (Eq-sym (subst-subst1-comm sigma C Zero))
             (subst-HasType wtsub wfH da)
    htb-suc : HasType H sb (Pi NatT (subSucC sC))
    htb-suc = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subSucC-subst sigma C)
                (subst-HasType wtsub wfH db)
    typed : HasType H (subst1 sC sM) U
    typed = ty-subst1-motive htCdep htsM
    ac_U = FinMem-a-in-U u ac fm
    coh-ac = coh-from-aU ac ac_U

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      Val2 H (Case sM sa sb) (subst1 sC sM) u ac
    branchBot cb =
      restrictVal2 H (Case sM sa sb) (subst1 sC sM) Bot u ac (snd cb) fm
        (finMem-bot-from ac ac_U) (Val2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      Val2 H (Case sM sa sb) (subst1 sC sM) u ac
    branchZero evM cb =
      let valM    = IHM sigma rho crho vs fits wtsub wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          redZero = snd valM
          ctZero  = Red3.ct redZero
          -- bridge ac : subst1 C M  ->  subst1 C Zero
          fwd     = EvalRel-subst1-forward C M rho ac crho evAc
          vMf     = fst fwd
          evM_vMf = fst (snd fwd)
          evC_vMf = snd (snd fwd)
          cvMf    = EvalRel-coh M rho vMf evM_vMf
          le_vMf  = comp-Zero-le vMf (EvalRel-Comp M rho crho ZeroEl vMf evM evM_vMf)
          envle0  = mkSigma (EnvLe-refl rho crho) (mkSigma cvMf (mkSigma tt le_vMf))
          evC_Zero = EvalRel-mon-env C (extendEnv rho vMf) (extendEnv rho ZeroEl) ac evC_vMf envle0
          evAc_Z  = EvalRel-subst1-backward C Zero rho ZeroEl ac crho
                      (mkSigma tt (LeCode-refl ZeroEl tt)) evC_Zero
          val_a   = IHa sigma rho crho vs fits wtsub wfH u cb ac evAc_Z fm
          val_a_cz = Eq-transport (\ T -> Val2 H sa T u ac) (Eq-sym (subst-subst1-comm sigma C Zero)) val_a
          provX = \ u' a' le cu' evNa' fm' -> valZero-Nat wfH u' a' le (snd evNa') fm'
          provM = \ u' a' le cu' evNa' fm' ->
            IHM sigma rho crho vs fits wtsub wfH u' (EvalRel-down M rho ZeroEl u' crho cu' evM le) a' evNa' fm'
          provXM = \ u' a' le cu' evNa' fm' ->
            eqZero-cross sM wfH redZero u' a' le cu' (snd evNa') fm'
          eqvty = motiveEqValTy2 wfG IHCc sigma rho crho vs fits wtsub wfH
                    Zero sM (ty-Zero wfH) htsM (conv-sym ctZero) ZeroEl tt tt
                    provX provM provXM ac evC_Zero ac_U
          val_a_sm = Val2-EqValTy2-fwd u ac coh-ac eqvty val_a_cz
          hrCase = HeadRed-trans (HeadRed-Case (Red3.hr redZero)) (headred-step headred-case-zero headred-refl)
          cvTypeZM = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Zero wfH) htsM (conv-sym ctZero)
          cvCase = conv-trans (conv-Case-dep htCdep ctZero (conv-refl htaZ) (conv-refl htb-suc))
                     (conv-conv (conv-case-zero-dep htCdep htaZ htb-suc) cvTypeZM typed)
      in Val2-beta-expand u ac hrCase cvCase val_a_sm

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      Val2 H (Case sM sa sb) (subst1 sC sM) u ac
    sucW v Bot          a'' () evM' fm_w' evNat cb
    sucW v UCode        a'' () evM' fm_w' evNat cb
    sucW v (FunEl _)    a'' () evM' fm_w' evNat cb
    sucW v (PiCode _ _) a'' () evM' fm_w' evNat cb
    sucW v NatCode      a'' () evM' fm_w' evNat cb
    sucW v ZeroEl       a'' () evM' fm_w' evNat cb
    sucW v (SucEl v'') a'' le evM' fm_w' evNat cb =
      let fm_sv'' = finMem-upward (SucEl v'') a'' NatCode (snd evNat) (fst evNat) tt fm_w' tt
          valM    = IHM sigma rho crho vs fits wtsub wfH (SucEl v'') evM' NatCode (mkSigma tt tt) fm_sv''
          cv''    = FinMem-coh-u (SucEl v'') a'' fm_w'
          fm_v''  = sucNat-to v'' fm_sv''
          cohv    = key-coh (EvalRel-coh b rho (FunEl (cons (mkSigma v u) nil)) cb)
          record { pred = pmM ; red = redS ; htP = htP ; valP = valP0 } = snd valM
          valP    = unrelevelVal2-Nat v'' valP0
          val_app = adequacyV-app-Nat-dep dC dM db IHC IHCc IHM IHb sigma rho crho vs fits wtsub wfH
                      v v'' u le cohv cv'' fm_v'' evM' cb pmM htP redS valP ac evAc fm
          val_app_sm = Eq-transport (\ T -> Val2 H (App sb pmM) T u ac)
                         (Eq-sym (subst-subst1-comm sigma C M)) val_app
          hrCase = HeadRed-trans (HeadRed-Case (Red3.hr redS)) (headred-step headred-case-suc headred-refl)
          cvTypeSM = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Suc htP) htsM (conv-sym (Red3.ct redS))
          cvCase = conv-trans (conv-Case-dep htCdep (Red3.ct redS) (conv-refl htaZ) (conv-refl htb-suc))
                     (conv-conv (conv-case-suc-dep htCdep htP htaZ htb-suc) cvTypeSM typed)
      in Val2-beta-expand u ac hrCase cvCase val_app_sm

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      Val2 H (Case sM sa sb) (subst1 sC sM) u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed0 = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed0) (fst (snd typed0)) (fst (snd (snd typed0)))
              (fst (snd (snd (snd typed0)))) (fst (snd (snd (snd (snd typed0)))))
              (snd (snd (snd (snd (snd typed0))))) cb

------------------------------------------------------------------------
-- adequacyVE-app-Nat-dep : the EqVal2 (cross) dependent application core for
-- the SucEl branch.  Combines the function variation (App sb NL vs App FR NL)
-- and the argument variation (App FR NL vs App FR NR) -- exactly as
-- NatApp.adequacyVE-app-Nat -- then type-transports the combined eqval at the
-- selected codomain code ef_usel along the LEFT motive (Suc NL ~ sM) before
-- app-transport.  Arguments / predecessor validity are supplied at v''.
------------------------------------------------------------------------

adequacyVE-app-Nat-dep : {h g : Nat} {H : Ctx h} {G : Ctx g} {C : Expr (suc g)} {M b : Expr g}
  {FR NL NR : Expr h} ->
  HasType (extend G NatT) C U -> HasType G M NatT -> HasType G b (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> AdqConv (extend G NatT) C U -> Adq G M NatT ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (v v'' u1 : FinEl) -> LeCode v v'' -> Coherent v -> Coherent v'' -> FinMem v'' NatCode ->
  EvalRel M rho (SucEl v'') ->
  EvalRel b rho (FunEl (cons (mkSigma v u1) nil)) ->
  ((ub ap : FinEl) -> EvalRel b rho ub -> EvalRel (Pi NatT (subSucC C)) rho ap -> FinMem ub ap ->
    EqVal2 H (substExpr sigma b) FR (substExpr sigma (Pi NatT (subSucC C))) ub ap) ->
  HasType H NL NatT -> HasType H NR NatT -> ConvTm H NL NR NatT ->
  Red3 H (substExpr sigma M) (Suc NL) NatT ->
  EqVal2 H NL NR NatT v'' NatCode ->
  (ac1 : FinEl) -> EvalRel (subst1 C M) rho ac1 -> FinMem u1 ac1 ->
  EqVal2 H (App (substExpr sigma b) NL) (App FR NR) (substExpr sigma (subst1 C M)) u1 ac1
adequacyVE-app-Nat-dep {H = H} {G = G} {C = C} {M = M} {b = b} {FR = FR} {NL = NL} {NR = NR}
  dC dM db IHC IHCc IHM sigma rho crho vs fits wtsub wfH
  v v'' u1 le_v_v'' cohv cv'' fm_v'' evM_scrut evF_sing funcross
  htNL htNR cvNLNR redSM eqP_v'' ac1 evAc1 fm1 =
  transported
  where
    wfG  = typing-WfCtx dM
    sf   = substExpr sigma b
    sM   = substExpr sigma M
    sC   = substExpr (liftSub sigma) C
    sCD  = substExpr (liftSub sigma) (subSucC C)
    RT   = substExpr sigma (subst1 C M)
    sing = cons (mkSigma v u1) nil
    cv0  = key-coh (EvalRel-coh b rho (FunEl sing) evF_sing)
    htsM = subst-HasType wtsub wfH dM
    cvSucN-sM = conv-sym (Red3.ct redSM)
    evU  = mkSigma tt (LeCode-refl UCode tt)
    valP_NL = Val2-from-EqVal2-first v'' NatCode eqP_v''

    eq-cod : Eq (subst1 sCD NL) (subst1 sC (Suc NL))
    eq-cod = Eq-trans (Eq-cong (\ X -> subst1 X NL) (subSucC-subst sigma C)) (subSucC-subst1 sC NL)

    argValL : (u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
      Val2 H NL NatT u' a'
    argValL = nat-argVal NL rho v v'' cohv cv'' fm_v'' le_v_v'' valP_NL

    argEq : (u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
      EqVal2 H NL NR NatT u' a'
    argEq = nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le_v_v'' eqP_v''

    predProv : (w : FinEl) -> Coherent w -> LeCode w v'' -> FinMem w NatCode -> Val2 H NL NatT w NatCode
    predProv w cw lew fmw = restrictVal2 H NL NatT v'' w NatCode lew fmw fm_v'' valP_NL

    appEqVal-dispatch : (ub ap : FinEl) -> LeCode (FunEl sing) ub ->
      EvalRel b rho ub -> EvalRel (Pi NatT (subSucC C)) rho ap -> FinMem ub ap ->
      EqVal2 H sf FR (Pi NatT sCD) ub ap ->
      EqVal2 H (App sf NL) (App FR NR) RT u1 ac1
    appEqVal-dispatch Bot          ap () evFb evPab fmba eqvba
    appEqVal-dispatch UCode        ap () evFb evPab fmba eqvba
    appEqVal-dispatch (PiCode _ _) ap () evFb evPab fmba eqvba
    appEqVal-dispatch (FunEl g_big) Bot         lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) UCode       lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (FunEl _)   lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) NatCode     lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) ZeroEl      lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (SucEl _)   lf evFb evPab () eqvba
    appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
      let le_u1_vsel = fst lf
          fmg_big  = finMem-funel-fun g_big b_pi f_pi fmba
          cg_big   = finMem-funel-coh g_big b_pi f_pi fmba
          piU      = finMem-funel-wf g_big b_pi f_pi fmba
          b_piU    = finMem-piU-dom b_pi f_pi piU
          allU_fpi = finMem-piU-allU b_pi f_pi piU
          cf_pi    = finMem-piU-cft b_pi f_pi piU
          cb_pi    = coh-from-aU b_pi b_piU
          evA_bpi  = fst (snd evPab)
          sbel     = selectionBelow g_big v (cft-from-cf g_big cg_big) cv0
          u_sel    = fst sbel
          v_sel    = fst (snd sbel)
          sel_big  = fst (snd (snd sbel))
          le_usel  = fst (snd (snd (snd sbel)))
          eq_vsel  = snd (snd (snd (snd sbel)))
          le_u1_vsel' : LeCode u1 v_sel
          le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
          cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
          cv_sel   = Coherent-Selection-val sel_big (cft-from-cf g_big cg_big)
          le_usel_v'' = LeCode-trans u_sel v v'' cu_sel cohv cv'' le_usel le_v_v''
          fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
          c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel
          -- function variation: App sf NL vs App FR NL
          eqvpi_fun = un-REqValPi eqvba
          eqA_ef   = fst (Red-unique-Pi2 (Red-refl {G = H} {M = Pi NatT sCD} {A = U}) (mkRed (Red3.hr (REqValPiP.red eqvpi_fun))))
          eqB_ef   = snd (Red-unique-Pi2 (Red-refl {G = H} {M = Pi NatT sCD} {A = U}) (mkRed (Red3.hr (REqValPiP.red eqvpi_fun))))
          paeqv    = REqValPiP.appEV eqvpi_fun
          val_NL   = argValL u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          val_NL_A0 = S.Eq-transport (\ X -> Val2 H NL X u_sel b_pi) eqA_ef val_NL
          htNL_A0  = S.Eq-transport (\ X -> HasType H NL X) eqA_ef htNL
          eqval_fun_raw = paeqv u_sel v_sel sel_big NL htNL_A0 val_NL_A0
          ef_usel  = EvalFun f_pi u_sel
          eqval_fun_var : EqVal2 H (App sf NL) (App FR NL) (subst1 sCD NL) v_sel ef_usel
          eqval_fun_var = S.Eq-transport
            (\ X -> EqVal2 H (App sf NL) (App FR NL) (subst1 X NL) v_sel ef_usel)
            (S.Eq-sym eqB_ef) eqval_fun_raw
          -- argument variation: App FR NL vs App FR NR
          vpi_FR   = eqvalPi-snd eqvba
          eqA_FR   = fst (Red-unique-Pi2 (Red-refl {G = H} {M = Pi NatT sCD} {A = U}) (mkRed (Red3.hr (RValPiP.red vpi_FR))))
          eqB_FR   = snd (Red-unique-Pi2 (Red-refl {G = H} {M = Pi NatT sCD} {A = U}) (mkRed (Red3.hr (RValPiP.red vpi_FR))))
          pae_FR   = RValPiP.appE vpi_FR
          htNL_AFR = S.Eq-transport (\ X -> HasType H NL X) eqA_FR htNL
          htNR_AFR = S.Eq-transport (\ X -> HasType H NR X) eqA_FR htNR
          cvNLNR_AFR = S.Eq-transport (\ X -> ConvTm H NL NR X) eqA_FR cvNLNR
          eqval_arg = argEq u_sel b_pi evA_bpi le_usel cu_sel fm_usel_bpi
          eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H NL NR X u_sel b_pi) eqA_FR eqval_arg
          eqval_arg_raw = pae_FR u_sel v_sel sel_big NL NR htNL_AFR htNR_AFR cvNLNR_AFR eqval_arg_A0
          eqval_arg_var : EqVal2 H (App FR NL) (App FR NR) (subst1 sCD NL) v_sel ef_usel
          eqval_arg_var = S.Eq-transport
            (\ X -> EqVal2 H (App FR NL) (App FR NR) (subst1 X NL) v_sel ef_usel)
            (S.Eq-sym eqB_FR) eqval_arg_raw
          eqval_combined = EqVal2-trans v_sel ef_usel cv_sel c_efusel eqval_fun_var eqval_arg_var
          -- codomain eval / scrutinee bridge
          evCod_ef = EvalRel-Pi-body NatT (subSucC C) rho b_pi f_pi u_sel crho cu_sel evPab
          evC_suc  = EvalRel-subSucC-fwd C rho u_sel ef_usel crho cu_sel evCod_ef
          evM_su_sel = EvalRel-down M rho (SucEl v'') (SucEl u_sel) crho cu_sel evM_scrut le_usel_v''
          evC_ef   = EvalRel-subst1-backward C M rho (SucEl u_sel) ef_usel crho evM_su_sel evC_suc
          comp_ac_ef = EvalRel-Comp (subst1 C M) rho crho ac1 ef_usel evAc1 evC_ef
          ac1_U    = FinMem-a-in-U u1 ac1 fm1
          ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cf_pi cu_sel allU_fpi
          fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
          vt_ac = Val2-U-to-ValTy2 ac1 ac1_U
                    (adq-subst1-CM dC dM IHC IHM sigma rho crho vs fits wtsub wfH ac1 evAc1 UCode evU ac1_U)
          vt_ef = Val2-U-to-ValTy2 ef_usel ef_uselU
                    (adq-subst1-CM dC dM IHC IHM sigma rho crho vs fits wtsub wfH ef_usel evC_ef UCode evU ef_uselU)
          -- motive transport (LEFT): subst1 sC (Suc NL) -> subst1 sC sM at ef_usel
          fm_svsel = sucNat-from v'' fm_v''
          envle_up = mkSigma (EnvLe-refl rho crho) (mkSigma cu_sel (mkSigma cv'' le_usel_v''))
          evC_sv'' = EvalRel-mon-env C (extendEnv rho (SucEl u_sel)) (extendEnv rho (SucEl v''))
                       ef_usel evC_suc envle_up
          provX = \ u' a' le cu' evNa' fm' ->
            valSuc-direct NL v'' wfH htNL predProv u' a' le cu' (snd evNa') fm'
          provM = \ u' a' le cu' evNa' fm' ->
            IHM sigma rho crho vs fits wtsub wfH u'
              (EvalRel-down M rho (SucEl v'') u' crho cu' evM_scrut le) a' evNa' fm'
          provXM = \ u' a' le cu' evNa' fm' ->
            eqSuc-cross sM NL v'' wfH htNL redSM predProv u' a' le cu' (snd evNa') fm'
          eqvty_ef = motiveEqValTy2 wfG IHCc sigma rho crho vs fits wtsub wfH
                       (Suc NL) sM (ty-Suc htNL) htsM cvSucN-sM (SucEl v'') cv'' fm_svsel
                       provX provM provXM ef_usel evC_sv'' ef_uselU
          eqval1 : EqVal2 H (App sf NL) (App FR NR) (subst1 sC (Suc NL)) v_sel ef_usel
          eqval1 = S.Eq-transport (\ T -> EqVal2 H (App sf NL) (App FR NR) T v_sel ef_usel) eq-cod eqval_combined
          eqvalX : EqVal2 H (App sf NL) (App FR NR) (subst1 sC sM) v_sel ef_usel
          eqvalX = EqVal2-EqValTy2-fwd v_sel ef_usel c_efusel eqvty_ef eqval1
          eqval2 : EqVal2 H (App sf NL) (App FR NR) RT v_sel ef_usel
          eqval2 = S.Eq-transport (\ T -> EqVal2 H (App sf NL) (App FR NR) T v_sel ef_usel)
                     (subst-subst1-comm sigma C M) eqvalX
      in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
           v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval2

    transported : EqVal2 H (App sf NL) (App FR NR) RT u1 ac1
    transported =
      let typed_f = theorem1 db rho fits (FunEl sing) evF_sing
          u_big   = fst typed_f
          a_pi    = fst (snd typed_f)
          le_sing = fst (snd (snd typed_f))
          evF_big = fst (snd (snd (snd typed_f)))
          fm_big  = fst (snd (snd (snd (snd typed_f))))
          evPi    = snd (snd (snd (snd (snd typed_f))))
          eqval_f = funcross u_big a_pi evF_big evPi fm_big
      in appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f

------------------------------------------------------------------------
-- adequacyVE-ty-Case-dep : the two-substitution (cross) combinator for
-- ty-Case-dep (consumed by adequacyConvSub2).  Same shape as adequacyVE-ty-Case
-- but the dependent result type subst1 C M; the RIGHT contractum's natural type
-- subst1 sC' sM' is conv-conv'd to the LEFT subst1 sC sM via the cross type
-- conversion (subst-ConvTm-cross on ty-subst1-motive).
------------------------------------------------------------------------

adequacyVE-ty-Case-dep : {h g : Nat} {H : Ctx h} {G : Ctx g} {C : Expr (suc g)} {M a b : Expr g} ->
  HasType (extend G NatT) C U -> HasType G M NatT ->
  HasType G a (subst1 C Zero) -> HasType G b (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> AdqConv (extend G NatT) C U -> Adq G M NatT ->
  AdqConv G M NatT -> AdqConv G a (subst1 C Zero) -> AdqConv G b (Pi NatT (subSucC C)) ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel (subst1 C M) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case M a b)) (substExpr sigma' (Case M a b))
           (substExpr sigma (subst1 C M)) u ac
adequacyVE-ty-Case-dep {H = H} {C = C} {M = M} {a = a} {b = b}
  dC dM da db IHC IHCc IHMs IHM IHa IHb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu ac evAc fm =
  Eq-transport (\ T -> EqVal2 H (Case sM sa sb) (Case sM' sa' sb') T u ac) (subst-subst1-comm sigma C M)
    (branch (fst hu) (fst (snd hu)) (snd (snd hu)))
  where
    sM = substExpr sigma M ; sM' = substExpr sigma' M
    sa = substExpr sigma a ; sa' = substExpr sigma' a
    sb = substExpr sigma b ; sb' = substExpr sigma' b
    sC = substExpr (liftSub sigma) C ; sC' = substExpr (liftSub sigma') C
    wfG  = typing-WfCtx dM
    htsM  = subst-HasType wtsub  wfH dM
    htsM' = subst-HasType wtsub' wfH dM
    htCdep : HasType (extend H NatT) sC U
    htCdep = subst-HasType (liftSub-WtSub-NatT wtsub wfH) (wf-extend (ty-NatT wfH)) dC
    htC'dep : HasType (extend H NatT) sC' U
    htC'dep = subst-HasType (liftSub-WtSub-NatT wtsub' wfH) (wf-extend (ty-NatT wfH)) dC
    htaZ : HasType H sa (subst1 sC Zero)
    htaZ = Eq-transport (\ T -> HasType H sa T) (Eq-sym (subst-subst1-comm sigma C Zero))
             (subst-HasType wtsub wfH da)
    hta'Z : HasType H sa' (subst1 sC' Zero)
    hta'Z = Eq-transport (\ T -> HasType H sa' T) (Eq-sym (subst-subst1-comm sigma' C Zero))
              (subst-HasType wtsub' wfH da)
    htb-suc : HasType H sb (Pi NatT (subSucC sC))
    htb-suc = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subSucC-subst sigma C)
                (subst-HasType wtsub wfH db)
    htb'-suc : HasType H sb' (Pi NatT (subSucC sC'))
    htb'-suc = Eq-transport (\ X -> HasType H sb' (Pi NatT X)) (subSucC-subst sigma' C)
                 (subst-HasType wtsub' wfH db)
    typed  : HasType H (subst1 sC sM) U
    typed  = ty-subst1-motive htCdep htsM
    typed' : HasType H (subst1 sC' sM') U
    typed' = ty-subst1-motive htC'dep htsM'
    ac_U = FinMem-a-in-U u ac fm
    coh-ac = coh-from-aU ac ac_U
    -- cross type conversion subst1 sC' sM' ~ subst1 sC sM
    cvCrossType : ConvTm H (subst1 sC sM) (subst1 sC' sM') U
    cvCrossType =
      Eq-transport (\ T -> ConvTm H (subst1 sC sM) T U) (Eq-sym (subst-subst1-comm sigma' C M))
        (Eq-transport (\ T -> ConvTm H T (substExpr sigma' (subst1 C M)) U) (Eq-sym (subst-subst1-comm sigma C M))
          (subst-ConvTm-cross (ty-subst1-motive dC dM) wtsub wtsub' wcs wfH))
    cvTypeRL : ConvTm H (subst1 sC' sM') (subst1 sC sM) U
    cvTypeRL = conv-sym cvCrossType

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branchBot cb =
      restrictEqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) Bot u ac (snd cb) fm
        (finMem-bot-from ac ac_U) (EqVal2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branchZero evM cb =
      let eqZ   = IHM sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          redM0 = fst (snd eqZ) ; redM0' = snd (snd eqZ)
          ctZero  = Red3.ct redM0
          -- bridge ac : subst1 C M -> subst1 C Zero, motive transport (LEFT)
          fwd     = EvalRel-subst1-forward C M rho ac crho evAc
          vMf     = fst fwd
          evM_vMf = fst (snd fwd)
          evC_vMf = snd (snd fwd)
          cvMf    = EvalRel-coh M rho vMf evM_vMf
          le_vMf  = comp-Zero-le vMf (EvalRel-Comp M rho crho ZeroEl vMf evM evM_vMf)
          envle0  = mkSigma (EnvLe-refl rho crho) (mkSigma cvMf (mkSigma tt le_vMf))
          evC_Zero = EvalRel-mon-env C (extendEnv rho vMf) (extendEnv rho ZeroEl) ac evC_vMf envle0
          evAc_Z  = EvalRel-subst1-backward C Zero rho ZeroEl ac crho
                      (mkSigma tt (LeCode-refl ZeroEl tt)) evC_Zero
          eqa   = IHa sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u cb ac evAc_Z fm
          eqa_cz = Eq-transport (\ T -> EqVal2 H sa sa' T u ac) (Eq-sym (subst-subst1-comm sigma C Zero)) eqa
          provX = \ u' a' le cu' evNa' fm' -> valZero-Nat wfH u' a' le (snd evNa') fm'
          provM = \ u' a' le cu' evNa' fm' ->
            IHMs sigma rho crho vs fits wtsub wfH u' (EvalRel-down M rho ZeroEl u' crho cu' evM le) a' evNa' fm'
          provXM = \ u' a' le cu' evNa' fm' ->
            eqZero-cross sM wfH redM0 u' a' le cu' (snd evNa') fm'
          eqvty = motiveEqValTy2 wfG IHCc sigma rho crho vs fits wtsub wfH
                    Zero sM (ty-Zero wfH) htsM (conv-sym ctZero) ZeroEl tt tt
                    provX provM provXM ac evC_Zero ac_U
          eqa_sm = EqVal2-EqValTy2-fwd u ac coh-ac eqvty eqa_cz
          hr1   = HeadRed-trans (HeadRed-Case (Red3.hr redM0))  (headred-step headred-case-zero headred-refl)
          hr2   = HeadRed-trans (HeadRed-Case (Red3.hr redM0')) (headred-step headred-case-zero headred-refl)
          cvTypeZM = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Zero wfH) htsM (conv-sym ctZero)
          cv1   = conv-trans (conv-Case-dep htCdep ctZero (conv-refl htaZ) (conv-refl htb-suc))
                    (conv-conv (conv-case-zero-dep htCdep htaZ htb-suc) cvTypeZM typed)
          cvTypeZM' = subst1-cong-ConvTm (ty-NatT wfH) htC'dep (ty-Zero wfH) htsM' (conv-sym (Red3.ct redM0'))
          cv2'  = conv-trans (conv-Case-dep htC'dep (Red3.ct redM0') (conv-refl hta'Z) (conv-refl htb'-suc))
                    (conv-conv (conv-case-zero-dep htC'dep hta'Z htb'-suc) cvTypeZM' typed')
          cv2   = conv-conv cv2' cvTypeRL typed
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqa_sm

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    sucW v Bot          a'' () evM' fm_w' evNat cb
    sucW v UCode        a'' () evM' fm_w' evNat cb
    sucW v (FunEl _)    a'' () evM' fm_w' evNat cb
    sucW v (PiCode _ _) a'' () evM' fm_w' evNat cb
    sucW v NatCode      a'' () evM' fm_w' evNat cb
    sucW v ZeroEl       a'' () evM' fm_w' evNat cb
    sucW v (SucEl v'') a'' le evM' fm_w' evNat cb =
      let fm_sv'' = finMem-upward (SucEl v'') a'' NatCode (snd evNat) (fst evNat) tt fm_w' tt
          eqS     = IHM sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SucEl v'') evM' NatCode (mkSigma tt tt) fm_sv''
          cv''    = FinMem-coh-u (SucEl v'') a'' fm_w'
          fm_v''  = sucNat-to v'' fm_sv''
          cohv    = key-coh (EvalRel-coh b rho (FunEl (cons (mkSigma v u) nil)) cb)
          record { predM = pmL ; predN = pmR ; redM = redL ; redN = redR
                 ; htM = htL ; htN = htR ; cvP = cvLR ; eqP = eqP0 } = snd (snd (snd eqS))
          eqP     = unrelevelEqVal2-Nat v'' eqP0
          funcross = \ ub ap evbb ap-pi fmm -> IHb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH ub evbb ap ap-pi fmm
          eqval_app = adequacyVE-app-Nat-dep {FR = sb'} {NL = pmL} {NR = pmR}
                        dC dM db IHC IHCc IHMs sigma rho crho vs fits wtsub wfH
                        v v'' u le cohv cv'' fm_v'' evM' cb funcross htL htR cvLR redL eqP ac evAc fm
          eqval_app_sm = Eq-transport (\ T -> EqVal2 H (App sb pmL) (App sb' pmR) T u ac)
                           (Eq-sym (subst-subst1-comm sigma C M)) eqval_app
          hr1 = HeadRed-trans (HeadRed-Case (Red3.hr redL)) (headred-step headred-case-suc headred-refl)
          hr2 = HeadRed-trans (HeadRed-Case (Red3.hr redR)) (headred-step headred-case-suc headred-refl)
          cvTypeSL = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Suc htL) htsM (conv-sym (Red3.ct redL))
          cv1 = conv-trans (conv-Case-dep htCdep (Red3.ct redL) (conv-refl htaZ) (conv-refl htb-suc))
                  (conv-conv (conv-case-suc-dep htCdep htL htaZ htb-suc) cvTypeSL typed)
          cvTypeSR = subst1-cong-ConvTm (ty-NatT wfH) htC'dep (ty-Suc htR) htsM' (conv-sym (Red3.ct redR))
          cv2' = conv-trans (conv-Case-dep htC'dep (Red3.ct redR) (conv-refl hta'Z) (conv-refl htb'-suc))
                   (conv-conv (conv-case-suc-dep htC'dep htR hta'Z htb'-suc) cvTypeSR typed')
          cv2  = conv-conv cv2' cvTypeRL typed
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqval_app_sm

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed0 = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed0) (fst (snd typed0)) (fst (snd (snd typed0)))
              (fst (snd (snd (snd typed0)))) (fst (snd (snd (snd (snd typed0)))))
              (snd (snd (snd (snd (snd typed0))))) cb

------------------------------------------------------------------------
-- adequacyEqSub2-Case-dep : the congruence combinator for conv-Case-dep
-- (consumed by adequacyEqSub2).  Single substitution, DIFFERENT terms; the
-- result type subst1 C M uses the LEFT scrutinee M.  The RIGHT contractum's
-- natural type subst1 sC sM' is conv-conv'd to subst1 sC sM via the scrutinee
-- conversion M' ~ M (subst1-cong on dMM').  The single LEFT validity of M
-- needed by the dependent app core / motive provM is the FIRST projection of
-- the scrutinee's eqsub IH (no recursion on a presupposition).
------------------------------------------------------------------------

adequacyEqSub2-Case-dep : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {C : Expr (suc g)} {M M' a a' b b' : Expr g} ->
  HasType (extend G NatT) C U -> ConvTm G M M' NatT ->
  ConvTm G a a' (subst1 C Zero) -> ConvTm G b b' (Pi NatT (subSucC C)) ->
  Adq (extend G NatT) C U -> AdqConv (extend G NatT) C U ->
  AdqE1 G M M' NatT -> AdqE1 G a a' (subst1 C Zero) -> AdqE1 G b b' (Pi NatT (subSucC C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel (subst1 C M) rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case M a b)) (substExpr sigma (Case M' a' b'))
           (substExpr sigma (subst1 C M)) u ac
adequacyEqSub2-Case-dep {H = H} {G = G} {C = C} {M = M} {M' = M'} {a = a} {a' = a'} {b = b} {b' = b'}
  dC dMM' daa' dbb' IHC IHCc IHM IHa IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  Eq-transport (\ T -> EqVal2 H (Case sM sa sb) (Case sM' sa' sb') T u ac) (subst-subst1-comm sigma C M)
    (branch (fst hu) (fst (snd hu)) (snd (snd hu)))
  where
    dM  = fst (typing-ConvTm dMM') ; dM' = snd (typing-ConvTm dMM')
    da  = fst (typing-ConvTm daa') ; da' = snd (typing-ConvTm daa')
    db  = fst (typing-ConvTm dbb') ; db' = snd (typing-ConvTm dbb')
    sM = substExpr sigma M ; sM' = substExpr sigma M'
    sa = substExpr sigma a ; sa' = substExpr sigma a'
    sb = substExpr sigma b ; sb' = substExpr sigma b'
    sC = substExpr (liftSub sigma) C
    wfG  = typing-WfCtx dM
    htsM  = subst-HasType wtsub wfH dM
    htsM' = subst-HasType wtsub wfH dM'
    htCdep : HasType (extend H NatT) sC U
    htCdep = subst-HasType (liftSub-WtSub-NatT wtsub wfH) (wf-extend (ty-NatT wfH)) dC
    htaZ : HasType H sa (subst1 sC Zero)
    htaZ = Eq-transport (\ T -> HasType H sa T) (Eq-sym (subst-subst1-comm sigma C Zero))
             (subst-HasType wtsub wfH da)
    hta'Z : HasType H sa' (subst1 sC Zero)
    hta'Z = Eq-transport (\ T -> HasType H sa' T) (Eq-sym (subst-subst1-comm sigma C Zero))
              (subst-HasType wtsub wfH da')
    htb-suc : HasType H sb (Pi NatT (subSucC sC))
    htb-suc = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subSucC-subst sigma C)
                (subst-HasType wtsub wfH db)
    htb'-suc : HasType H sb' (Pi NatT (subSucC sC))
    htb'-suc = Eq-transport (\ X -> HasType H sb' (Pi NatT X)) (subSucC-subst sigma C)
                 (subst-HasType wtsub wfH db')
    typed  : HasType H (subst1 sC sM) U
    typed  = ty-subst1-motive htCdep htsM
    typed' : HasType H (subst1 sC sM') U
    typed' = ty-subst1-motive htCdep htsM'
    ac_U = FinMem-a-in-U u ac fm
    coh-ac = coh-from-aU ac ac_U
    IHMs : Adq G M NatT
    IHMs s2 r2 cr2 v2 f2 w2 wf2 u2 hu2 a2 evA2 fm2 =
      Val2-from-EqVal2-first u2 a2 (IHM s2 r2 cr2 v2 f2 w2 wf2 u2 hu2 a2 evA2 fm2)
    -- right scrutinee conversion: subst1 sC sM' ~ subst1 sC sM
    cvTypeRL : ConvTm H (subst1 sC sM') (subst1 sC sM) U
    cvTypeRL =
      Eq-transport (\ T -> ConvTm H (subst1 sC sM') T U) (Eq-sym (subst-subst1-comm sigma C M))
        (Eq-transport (\ T -> ConvTm H T (substExpr sigma (subst1 C M)) U) (Eq-sym (subst-subst1-comm sigma C M'))
          (subst-ConvTm wtsub wfH (subst1-cong-ConvTm (ty-NatT wfG) dC dM' dM (conv-sym dMM'))))

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branchBot cb =
      restrictEqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) Bot u ac (snd cb) fm
        (finMem-bot-from ac ac_U) (EqVal2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branchZero evM cb =
      let eqZ   = IHM sigma rho crho vs fits wtsub wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          redM0 = fst (snd eqZ) ; redM0' = snd (snd eqZ)
          ctZero  = Red3.ct redM0
          fwd     = EvalRel-subst1-forward C M rho ac crho evAc
          vMf     = fst fwd
          evM_vMf = fst (snd fwd)
          evC_vMf = snd (snd fwd)
          cvMf    = EvalRel-coh M rho vMf evM_vMf
          le_vMf  = comp-Zero-le vMf (EvalRel-Comp M rho crho ZeroEl vMf evM evM_vMf)
          envle0  = mkSigma (EnvLe-refl rho crho) (mkSigma cvMf (mkSigma tt le_vMf))
          evC_Zero = EvalRel-mon-env C (extendEnv rho vMf) (extendEnv rho ZeroEl) ac evC_vMf envle0
          evAc_Z  = EvalRel-subst1-backward C Zero rho ZeroEl ac crho
                      (mkSigma tt (LeCode-refl ZeroEl tt)) evC_Zero
          eqa   = IHa sigma rho crho vs fits wtsub wfH u cb ac evAc_Z fm
          eqa_cz = Eq-transport (\ T -> EqVal2 H sa sa' T u ac) (Eq-sym (subst-subst1-comm sigma C Zero)) eqa
          provX = \ u' a' le cu' evNa' fm' -> valZero-Nat wfH u' a' le (snd evNa') fm'
          provM = \ u' a' le cu' evNa' fm' ->
            IHMs sigma rho crho vs fits wtsub wfH u' (EvalRel-down M rho ZeroEl u' crho cu' evM le) a' evNa' fm'
          provXM = \ u' a' le cu' evNa' fm' ->
            eqZero-cross sM wfH redM0 u' a' le cu' (snd evNa') fm'
          eqvty = motiveEqValTy2 wfG IHCc sigma rho crho vs fits wtsub wfH
                    Zero sM (ty-Zero wfH) htsM (conv-sym ctZero) ZeroEl tt tt
                    provX provM provXM ac evC_Zero ac_U
          eqa_sm = EqVal2-EqValTy2-fwd u ac coh-ac eqvty eqa_cz
          hr1   = HeadRed-trans (HeadRed-Case (Red3.hr redM0))  (headred-step headred-case-zero headred-refl)
          hr2   = HeadRed-trans (HeadRed-Case (Red3.hr redM0')) (headred-step headred-case-zero headred-refl)
          cvTypeZM = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Zero wfH) htsM (conv-sym ctZero)
          cv1   = conv-trans (conv-Case-dep htCdep ctZero (conv-refl htaZ) (conv-refl htb-suc))
                    (conv-conv (conv-case-zero-dep htCdep htaZ htb-suc) cvTypeZM typed)
          cvTypeZM' = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Zero wfH) htsM' (conv-sym (Red3.ct redM0'))
          cv2'  = conv-trans (conv-Case-dep htCdep (Red3.ct redM0') (conv-refl hta'Z) (conv-refl htb'-suc))
                    (conv-conv (conv-case-zero-dep htCdep hta'Z htb'-suc) cvTypeZM' typed')
          cv2   = conv-conv cv2' cvTypeRL typed
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqa_sm

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    sucW v Bot          a'' () evM' fm_w' evNat cb
    sucW v UCode        a'' () evM' fm_w' evNat cb
    sucW v (FunEl _)    a'' () evM' fm_w' evNat cb
    sucW v (PiCode _ _) a'' () evM' fm_w' evNat cb
    sucW v NatCode      a'' () evM' fm_w' evNat cb
    sucW v ZeroEl       a'' () evM' fm_w' evNat cb
    sucW v (SucEl v'') a'' le evM' fm_w' evNat cb =
      let fm_sv'' = finMem-upward (SucEl v'') a'' NatCode (snd evNat) (fst evNat) tt fm_w' tt
          eqS     = IHM sigma rho crho vs fits wtsub wfH (SucEl v'') evM' NatCode (mkSigma tt tt) fm_sv''
          cv''    = FinMem-coh-u (SucEl v'') a'' fm_w'
          fm_v''  = sucNat-to v'' fm_sv''
          cohv    = key-coh (EvalRel-coh b rho (FunEl (cons (mkSigma v u) nil)) cb)
          record { predM = pmL ; predN = pmR ; redM = redL ; redN = redR
                 ; htM = htL ; htN = htR ; cvP = cvLR ; eqP = eqP0 } = snd (snd (snd eqS))
          eqP     = unrelevelEqVal2-Nat v'' eqP0
          funcross = \ ub ap evbb ap-pi fmm -> IHb sigma rho crho vs fits wtsub wfH ub evbb ap ap-pi fmm
          eqval_app = adequacyVE-app-Nat-dep {FR = sb'} {NL = pmL} {NR = pmR}
                        dC dM db IHC IHCc IHMs sigma rho crho vs fits wtsub wfH
                        v v'' u le cohv cv'' fm_v'' evM' cb funcross htL htR cvLR redL eqP ac evAc fm
          eqval_app_sm = Eq-transport (\ T -> EqVal2 H (App sb pmL) (App sb' pmR) T u ac)
                           (Eq-sym (subst-subst1-comm sigma C M)) eqval_app
          hr1 = HeadRed-trans (HeadRed-Case (Red3.hr redL)) (headred-step headred-case-suc headred-refl)
          hr2 = HeadRed-trans (HeadRed-Case (Red3.hr redR)) (headred-step headred-case-suc headred-refl)
          cvTypeSL = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Suc htL) htsM (conv-sym (Red3.ct redL))
          cv1 = conv-trans (conv-Case-dep htCdep (Red3.ct redL) (conv-refl htaZ) (conv-refl htb-suc))
                  (conv-conv (conv-case-suc-dep htCdep htL htaZ htb-suc) cvTypeSL typed)
          cvTypeSR = subst1-cong-ConvTm (ty-NatT wfH) htCdep (ty-Suc htR) htsM' (conv-sym (Red3.ct redR))
          cv2' = conv-trans (conv-Case-dep htCdep (Red3.ct redR) (conv-refl hta'Z) (conv-refl htb'-suc))
                   (conv-conv (conv-case-suc-dep htCdep htR hta'Z htb'-suc) cvTypeSR typed')
          cv2  = conv-conv cv2' cvTypeRL typed
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqval_app_sm

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') (subst1 sC sM) u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed0 = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed0) (fst (snd typed0)) (fst (snd (snd typed0)))
              (fst (snd (snd (snd typed0)))) (fst (snd (snd (snd (snd typed0)))))
              (snd (snd (snd (snd (snd typed0))))) cb
