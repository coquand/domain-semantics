{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Adequacy.NatCase.agda
--
-- Per-rule adequacy combinators for the Nat fragment (ty-NatT/Zero/Suc/Case
-- and the conv-case-zero/-suc/conv-Suc/conv-Case conversions), factored out
-- of the Adequacy.Value driver's mutual block.  Mirrors the Beta / App
-- combinator files.  No postulates.
------------------------------------------------------------------------

module NAT.Adequacy.NatCase where

open import NAT.Adequacy.HeadRed
open import NAT.Adequacy.Pi using (Adq ; AdqConv)
open import NAT.Adequacy.App using (adequacySub2-App ; adequacyV-ty-App)
open import NAT.Adequacy.VE using (AdqE ; AdqE1)
open import NAT.Adequacy.NatApp using (adequacyV-app-Nat ; adequacyVE-app-Nat)

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; max ; tt ; mkSigma ; fst ; snd ; Sigma ; Pair ; nil ; cons ;
  FinEl ; Bot ; UCode ; FunEl ; PiCode ;
  NatCode ; ZeroEl ; SucEl ; Eq ; refl ; Eq-transport ; Eq-sym)
open import NAT.Domain.Rank using (RANK)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; FinMem ; FinMem-coh-u ;
  FinMem-a-in-U ; Coherent ; CFTcons ; sucNat-to ; finMem-bot-from ; finMem-upward)
open CFTcons
open import NAT.Model.Eval using (EnvApprox ; EvalRel ; EvalRel-coh ; EvalRel-down ;
  CaseBranch ; CoherentEnv)
open import NAT.Syntax.Raw using (Expr ; U ; Pi ; App ; NatT ; Zero ; Suc ; Case ;
  Sub ; substExpr ; subst1 ; wkExpr ; subst-wk-comm)
open import NAT.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ;
  ty-U ; ty-NatT ; ty-Zero ; ty-Suc ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Case ; conv-case-zero ; conv-case-suc ; conv-Suc)
open import NAT.Syntax.Reduction using (HeadRed ; HeadRed1 ; headred-refl ; headred-step ;
  headred-case-zero ; headred-case-suc ; HeadRed-trans ; HeadRed-Case)
open import NAT.Model.Soundness using (theorem1)
open import NAT.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; subst-ConvTm ; subst-ConvTm-cross ; subst1-wk ; wk-HasType ;
  typing-WfCtx ; typing-ConvTm)
open import NAT.Model.Soundness using (convSound)
open import NAT.Model.SoundnessLemmas using (Fits)
open import NAT.Validity.Stratified using (Red3 ; mkRed3 ; Bundle ; Stage)

------------------------------------------------------------------------
-- max m zero = m  (used to re-level a canonical Val2 at code NatCode down
-- to the predecessor-stage value that RValNatSuc.valP expects).
------------------------------------------------------------------------

max-zero-r : (m : Nat) -> Eq (max m zero) m
max-zero-r zero    = refl
max-zero-r (suc m) = refl

-- Re-level a canonical Val2 / EqVal2 at code (v', NatCode) down to the
-- predecessor-stage value that RValNatSuc.valP / REqValNatSuc.eqP expect.
relevelVal2-Nat : {h : Nat} {H : Ctx h} {M : Expr h} (v' : FinEl) ->
  Val2 H M NatT v' NatCode -> Bundle.val (Stage (suc (RANK v'))) H M NatT v' NatCode
relevelVal2-Nat {H = H} {M = M} v' x =
  Eq-transport (\ k -> Bundle.val (Stage (suc k)) H M NatT v' NatCode)
    (max-zero-r (RANK v')) x

relevelEqVal2-Nat : {h : Nat} {H : Ctx h} {M N : Expr h} (v' : FinEl) ->
  EqVal2 H M N NatT v' NatCode -> Bundle.eqval (Stage (suc (RANK v'))) H M N NatT v' NatCode
relevelEqVal2-Nat {H = H} {M = M} {N = N} v' x =
  Eq-transport (\ k -> Bundle.eqval (Stage (suc k)) H M N NatT v' NatCode)
    (max-zero-r (RANK v')) x

-- Inverse re-level: a predecessor-stage value (e.g. RValNatSuc.valP) up to the
-- canonical Val2 level.
unrelevelVal2-Nat : {h : Nat} {H : Ctx h} {M : Expr h} (v' : FinEl) ->
  Bundle.val (Stage (suc (RANK v'))) H M NatT v' NatCode -> Val2 H M NatT v' NatCode
unrelevelVal2-Nat {H = H} {M = M} v' x =
  Eq-transport (\ k -> Bundle.val (Stage (suc k)) H M NatT v' NatCode)
    (Eq-sym (max-zero-r (RANK v'))) x

unrelevelEqVal2-Nat : {h : Nat} {H : Ctx h} {M N : Expr h} (v' : FinEl) ->
  Bundle.eqval (Stage (suc (RANK v'))) H M N NatT v' NatCode -> EqVal2 H M N NatT v' NatCode
unrelevelEqVal2-Nat {H = H} {M = M} {N = N} v' x =
  Eq-transport (\ k -> Bundle.eqval (Stage (suc k)) H M N NatT v' NatCode)
    (Eq-sym (max-zero-r (RANK v'))) x

------------------------------------------------------------------------
-- ty-NatT : Val2 H NatT U u a   (NatT is a valid type; mirrors valU-UU)
------------------------------------------------------------------------

valNatT-U : {h : Nat} {H : Ctx h} -> WfCtx H ->
  (u a : FinEl) -> LeCode u NatCode -> LeCode a UCode -> FinMem u a ->
  Val2 H NatT U u a
valNatT-U wfH u           Bot          _  _  _ = tt
valNatT-U wfH Bot         UCode        _  _  _ = tt
valNatT-U wfH UCode       UCode        () _  _
valNatT-U wfH (FunEl _)   UCode        () _  _
valNatT-U wfH (PiCode _ _) UCode       () _  _
valNatT-U wfH NatCode     UCode        _  _  _ =
  mkSigma (mkRed3 headred-refl (conv-refl (ty-U wfH)))
          (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
valNatT-U wfH ZeroEl      UCode        () _  _
valNatT-U wfH (SucEl _)   UCode        () _  _
valNatT-U wfH u           (FunEl _)    _  () _
valNatT-U wfH u           (PiCode _ _) _  () _
valNatT-U wfH u           NatCode      _  () _
valNatT-U wfH u           ZeroEl       _  () _
valNatT-U wfH u           (SucEl _)    _  () _

------------------------------------------------------------------------
-- ty-Zero : Val2 H Zero NatT u a
------------------------------------------------------------------------

valZero-Nat : {h : Nat} {H : Ctx h} -> WfCtx H ->
  (u a : FinEl) -> LeCode u ZeroEl -> LeCode a NatCode -> FinMem u a ->
  Val2 H Zero NatT u a
valZero-Nat wfH u           Bot          _  _  _ = tt
valZero-Nat wfH Bot         NatCode      _  _  _ = tt
valZero-Nat wfH UCode       NatCode      () _  _
valZero-Nat wfH (FunEl _)   NatCode      () _  _
valZero-Nat wfH (PiCode _ _) NatCode     () _  _
valZero-Nat wfH NatCode     NatCode      () _  _
valZero-Nat wfH ZeroEl      NatCode      _  _  _ =
  mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
          (mkRed3 headred-refl (conv-refl (ty-Zero wfH)))
valZero-Nat wfH (SucEl _)   NatCode      () _  _
valZero-Nat wfH u           UCode        _  () _
valZero-Nat wfH u           (FunEl _)    _  () _
valZero-Nat wfH u           (PiCode _ _) _  () _
valZero-Nat wfH u           ZeroEl       _  () _
valZero-Nat wfH u           (SucEl _)    _  () _

------------------------------------------------------------------------
-- ty-Suc (single sub) : Val2 H (Suc m) NatT u a
------------------------------------------------------------------------

adequacyV-ty-Suc : {h g : Nat} {H : Ctx h} {G : Ctx g} {m : Expr g} ->
  HasType G m NatT -> Adq G m NatT ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Suc m) rho u ->
  (a : FinEl) -> EvalRel NatT rho a -> FinMem u a ->
  Val2 H (Suc (substExpr sigma m)) NatT u a
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu Bot          evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu UCode        evA fm with snd evA
... | ()
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu (FunEl _)    evA fm with snd evA
... | ()
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) evA fm with snd evA
... | ()
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu ZeroEl       evA fm with snd evA
... | ()
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH u hu (SucEl _)    evA fm with snd evA
... | ()
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH Bot          hu NatCode evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH UCode        hu NatCode evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH (FunEl _)    hu NatCode evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH (PiCode _ _) hu NatCode evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH NatCode      hu NatCode evA fm = tt
adequacyV-ty-Suc dm IHm sigma rho crho vs fits wtsub wfH ZeroEl       hu NatCode evA fm
  with snd (snd hu)
... | ()
adequacyV-ty-Suc {H = H} {m = m} dm IHm sigma rho crho vs fits wtsub wfH (SucEl v') hu NatCode evA fm =
  let cu     = fst hu
      sg     = snd hu
      v      = fst sg
      evm_v  = fst (snd sg)
      le_u   = snd (snd sg)                       -- LeCode v' v
      evm_v' = EvalRel-down m rho v v' crho cu evm_v le_u
      fm_v'  = sucNat-to v' fm
      valP_v' = IHm sigma rho crho vs fits wtsub wfH v' evm_v' NatCode (mkSigma tt tt) fm_v'
      valP_fixed = Eq-transport
                     (\ k -> Bundle.val (Stage (suc k)) H (substExpr sigma m) NatT v' NatCode)
                     (max-zero-r (RANK v')) valP_v'
      htsm   = subst-HasType wtsub wfH dm
  in mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
       (record { pred = substExpr sigma m
               ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htsm))
               ; htP  = htsm
               ; valP = valP_fixed })

------------------------------------------------------------------------
-- conv-case-zero : Case Zero a b = a : C   (head-expand to the zero branch)
------------------------------------------------------------------------

adequacyEqSub2-case-zero : {h g : Nat} {H : Ctx h} {G : Ctx g} {C a b : Expr g} ->
  HasType G C U -> HasType G a C -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G a C ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case Zero a b) rho u ->
  (ac : FinEl) -> EvalRel C rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case Zero a b)) (substExpr sigma a) (substExpr sigma C) u ac
adequacyEqSub2-case-zero dC da db IHa sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let hu_c  = convSound (conv-case-zero dC da db) rho fits u hu
      val_a = IHa sigma rho crho vs fits wtsub wfH u hu_c ac evAc fm
      hr    = headred-step headred-case-zero headred-refl
      cv    = subst-ConvTm wtsub wfH (conv-case-zero dC da db)
      hta   = subst-HasType wtsub wfH da
  in EqVal2-headred-expand u ac hr headred-refl cv (conv-refl hta)
       (Val2-to-EqVal2 u ac val_a)

------------------------------------------------------------------------
-- conv-Suc : Suc m = Suc m' : NatT   (Suc congruence at EqVal2)
------------------------------------------------------------------------

adequacyEqSub2-Suc : {h g : Nat} {H : Ctx h} {G : Ctx g} {m m' : Expr g} ->
  ConvTm G m m' NatT -> AdqE1 G m m' NatT ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Suc m) rho u ->
  (a : FinEl) -> EvalRel NatT rho a -> FinMem u a ->
  EqVal2 H (Suc (substExpr sigma m)) (Suc (substExpr sigma m')) NatT u a
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu Bot          evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu UCode        evA fm with snd evA
... | ()
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu (FunEl _)    evA fm with snd evA
... | ()
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) evA fm with snd evA
... | ()
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu ZeroEl       evA fm with snd evA
... | ()
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH u hu (SucEl _)    evA fm with snd evA
... | ()
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH Bot          hu NatCode evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH UCode        hu NatCode evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH (FunEl _)    hu NatCode evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH (PiCode _ _) hu NatCode evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH NatCode      hu NatCode evA fm = tt
adequacyEqSub2-Suc d IH sigma rho crho vs fits wtsub wfH ZeroEl       hu NatCode evA fm
  with snd (snd hu)
... | ()
adequacyEqSub2-Suc {m = m} {m' = m'} d IH sigma rho crho vs fits wtsub wfH (SucEl v') hu NatCode evA fm =
  let cu     = fst hu
      sg     = snd hu
      v      = fst sg
      evm_v  = fst (snd sg)
      le_u   = snd (snd sg)
      evm_v' = EvalRel-down m rho v v' crho cu evm_v le_u
      fm_v'  = sucNat-to v' fm
      eqv'   = IH sigma rho crho vs fits wtsub wfH v' evm_v' NatCode (mkSigma tt tt) fm_v'
      dm     = fst (typing-ConvTm d)
      dm'    = snd (typing-ConvTm d)
      htsm   = subst-HasType wtsub wfH dm
      htsm'  = subst-HasType wtsub wfH dm'
      valM   = relevelVal2-Nat v' (Val2-from-EqVal2-first  v' NatCode eqv')
      valN   = relevelVal2-Nat v' (Val2-from-EqVal2-second v' NatCode eqv')
      eqP'   = relevelEqVal2-Nat v' eqv'
  in mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
       (mkSigma (record { pred = substExpr sigma m
                        ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htsm))
                        ; htP  = htsm ; valP = valM })
         (mkSigma (record { pred = substExpr sigma m'
                          ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htsm'))
                          ; htP  = htsm' ; valP = valN })
           (record { predM = substExpr sigma m  ; predN = substExpr sigma m'
                   ; redM  = mkRed3 headred-refl (conv-refl (ty-Suc htsm))
                   ; redN  = mkRed3 headred-refl (conv-refl (ty-Suc htsm'))
                   ; htM   = htsm ; htN = htsm'
                   ; cvP   = subst-ConvTm wtsub wfH d ; eqP = eqP' })))

------------------------------------------------------------------------
-- ty-Suc (cross / two-substitution) : EqVal2 (Suc m)[σ] (Suc m)[σ'] : NatT
------------------------------------------------------------------------

adequacyVE-ty-Suc : {h g : Nat} {H : Ctx h} {G : Ctx g} {m : Expr g} ->
  HasType G m NatT -> AdqConv G m NatT ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (Suc m) rho u ->
  (a : FinEl) -> EvalRel NatT rho a -> FinMem u a ->
  EqVal2 H (Suc (substExpr sigma m)) (Suc (substExpr sigma' m)) NatT u a
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot          evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode        evA fm with snd evA
... | ()
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _)    evA fm with snd evA
... | ()
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode _ _) evA fm with snd evA
... | ()
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu ZeroEl       evA fm with snd evA
... | ()
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (SucEl _)    evA fm with snd evA
... | ()
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot          hu NatCode evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode        hu NatCode evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _)    hu NatCode evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu NatCode evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH NatCode      hu NatCode evA fm = tt
adequacyVE-ty-Suc dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH ZeroEl       hu NatCode evA fm
  with snd (snd hu)
... | ()
adequacyVE-ty-Suc {m = m} dm IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SucEl v') hu NatCode evA fm =
  let cu     = fst hu
      sg     = snd hu
      v      = fst sg
      evm_v  = fst (snd sg)
      le_u   = snd (snd sg)
      evm_v' = EvalRel-down m rho v v' crho cu evm_v le_u
      fm_v'  = sucNat-to v' fm
      eqv'   = IH sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH v' evm_v' NatCode (mkSigma tt tt) fm_v'
      htsm   = subst-HasType wtsub  wfH dm
      htsm'  = subst-HasType wtsub' wfH dm
      valM   = relevelVal2-Nat v' (Val2-from-EqVal2-first  v' NatCode eqv')
      valN   = relevelVal2-Nat v' (Val2-from-EqVal2-second v' NatCode eqv')
      eqP'   = relevelEqVal2-Nat v' eqv'
  in mkSigma (mkRed3 headred-refl (conv-refl (ty-NatT wfH)))
       (mkSigma (record { pred = substExpr sigma m
                        ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htsm))
                        ; htP  = htsm ; valP = valM })
         (mkSigma (record { pred = substExpr sigma' m
                          ; red  = mkRed3 headred-refl (conv-refl (ty-Suc htsm'))
                          ; htP  = htsm' ; valP = valN })
           (record { predM = substExpr sigma m  ; predN = substExpr sigma' m
                   ; redM  = mkRed3 headred-refl (conv-refl (ty-Suc htsm))
                   ; redN  = mkRed3 headred-refl (conv-refl (ty-Suc htsm'))
                   ; htM   = htsm ; htN = htsm'
                   ; cvP   = subst-ConvTm-cross dm wtsub wtsub' wcs wfH ; eqP = eqP' })))

------------------------------------------------------------------------
-- conv-case-suc : Case (Suc m) a b = App b m : C   (head-expand to App b m,
-- the contractum built by the value-level App core adequacyV-app-Nat).
------------------------------------------------------------------------

adequacyEqSub2-case-suc : {h g : Nat} {H : Ctx h} {G : Ctx g} {C m a b : Expr g} ->
  HasType G C U -> HasType G m NatT -> HasType G a C -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G C U -> Adq G m NatT -> Adq G b (Pi NatT (wkExpr C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case (Suc m) a b) rho u ->
  (ac : FinEl) -> EvalRel C rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case (Suc m) a b)) (App (substExpr sigma b) (substExpr sigma m))
           (substExpr sigma C) u ac
adequacyEqSub2-case-suc {H = H} {C = C} {m = m} {a = a} {b = b}
  dC dm da db IHC IHm IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  let hu_c = convSound (conv-case-suc dC dm da db) rho fits u hu
      cv   = subst-ConvTm wtsub wfH (conv-case-suc dC dm da db)
      htAp = snd (typing-ConvTm cv)
      hr   = headred-step headred-case-suc headred-refl
  in EqVal2-headred-expand u ac hr headred-refl cv (conv-refl htAp)
       (Val2-to-EqVal2 u ac (contractum-val u hu_c fm))
  where
    htsm = subst-HasType wtsub wfH dm
    cv-nonbot : (u : FinEl) ->
      Sigma FinEl (\ v -> Pair (EvalRel m rho v)
                               (EvalRel b rho (FunEl (cons (mkSigma v u) nil)))) ->
      FinMem u ac ->
      Val2 H (App (substExpr sigma b) (substExpr sigma m)) (substExpr sigma C) u ac
    cv-nonbot u ev fmu =
      let v    = fst ev
          evm  = fst (snd ev)
          sing = snd (snd ev)
          argVal = \ u' a' evNa' le cu' fm' ->
                     IHm sigma rho crho vs fits wtsub wfH u'
                       (EvalRel-down m rho v u' crho cu' evm le) a' evNa' fm'
      in adequacyV-app-Nat dC db IHC IHb sigma rho crho vs fits wtsub wfH
           v u sing (substExpr sigma m) htsm argVal ac evAc fmu
    contractum-val : (u : FinEl) -> EvalRel (App b m) rho u -> FinMem u ac ->
      Val2 H (App (substExpr sigma b) (substExpr sigma m)) (substExpr sigma C) u ac
    contractum-val Bot          ev fmu = Val2-Bot ac
    contractum-val UCode        ev fmu = cv-nonbot UCode ev fmu
    contractum-val (FunEl g)    ev fmu = cv-nonbot (FunEl g) ev fmu
    contractum-val (PiCode d f) ev fmu = cv-nonbot (PiCode d f) ev fmu
    contractum-val NatCode      ev fmu = cv-nonbot NatCode ev fmu
    contractum-val ZeroEl       ev fmu = cv-nonbot ZeroEl ev fmu
    contractum-val (SucEl w)    ev fmu = cv-nonbot (SucEl w) ev fmu

------------------------------------------------------------------------
-- nat-argVal : the argument "value provider" fed to adequacyV-app-Nat for a
-- Nat argument with a known value `valP` at code v''.  Restricts to any value
-- u' <= v <= v'' (domain code NatCode); Bot domain code -> tt; impossible codes
-- killed by EvalRel NatT rho a'.
------------------------------------------------------------------------

nat-argVal : {h g : Nat} {H : Ctx h} (pm : Expr h) (rho : EnvApprox g)
  (v v'' : FinEl) -> Coherent v -> Coherent v'' -> FinMem v'' NatCode -> LeCode v v'' ->
  Val2 H pm NatT v'' NatCode ->
  (u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
  Val2 H pm NatT u' a'
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' Bot          evNa' le' cu' fm' = tt
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' UCode        evNa' le' cu' fm' with snd evNa'
... | ()
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' (FunEl _)    evNa' le' cu' fm' with snd evNa'
... | ()
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' (PiCode _ _) evNa' le' cu' fm' with snd evNa'
... | ()
nat-argVal {H = H} pm rho v v'' cohv cv'' fm_v'' le valP u' NatCode evNa' le' cu' fm' =
  restrictVal2 H pm NatT v'' u' NatCode
    (LeCode-trans u' v v'' cu' cohv cv'' le' le) fm' fm_v'' valP
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' ZeroEl       evNa' le' cu' fm' with snd evNa'
... | ()
nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP u' (SucEl _)    evNa' le' cu' fm' with snd evNa'
... | ()

-- EqVal2 analogue: the cross argument provider, from a known arg cross-validity
-- eqP at code v''.
nat-argEq : {h g : Nat} {H : Ctx h} (NL NR : Expr h) (rho : EnvApprox g)
  (v v'' : FinEl) -> Coherent v -> Coherent v'' -> FinMem v'' NatCode -> LeCode v v'' ->
  EqVal2 H NL NR NatT v'' NatCode ->
  (u' a' : FinEl) -> EvalRel NatT rho a' -> LeCode u' v -> Coherent u' -> FinMem u' a' ->
  EqVal2 H NL NR NatT u' a'
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' Bot          evNa' le' cu' fm' = tt
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' UCode        evNa' le' cu' fm' with snd evNa'
... | ()
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' (FunEl _)    evNa' le' cu' fm' with snd evNa'
... | ()
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' (PiCode _ _) evNa' le' cu' fm' with snd evNa'
... | ()
nat-argEq {H = H} NL NR rho v v'' cohv cv'' fm_v'' le eqP u' NatCode evNa' le' cu' fm' =
  restrictEqVal2 H NL NR NatT v'' u' NatCode
    (LeCode-trans u' v v'' cu' cohv cv'' le' le) fm' fm_v'' eqP
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' ZeroEl       evNa' le' cu' fm' with snd evNa'
... | ()
nat-argEq NL NR rho v v'' cohv cv'' fm_v'' le eqP u' (SucEl _)    evNa' le' cu' fm' with snd evNa'
... | ()

------------------------------------------------------------------------
-- ty-Case (single sub) : Val2 H (Case M a b) C u ac.
-- Semantic case on the scrutinee value w; for ZeroEl/SucEl the scrutinee's
-- validity (IH-M) gives sM ↠ Zero / Suc pred, so the whole case head-reduces
-- to the zero branch / (App b pred); build the contractum's Val2 and
-- head-expand.  (Bot: the result value is below Bot.)
------------------------------------------------------------------------

adequacyV-ty-Case : {h g : Nat} {H : Ctx h} {G : Ctx g} {C M a b : Expr g} ->
  HasType G C U -> HasType G M NatT -> HasType G a C -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G C U -> Adq G M NatT -> Adq G a C -> Adq G b (Pi NatT (wkExpr C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel C rho ac -> FinMem u ac ->
  Val2 H (Case (substExpr sigma M) (substExpr sigma a) (substExpr sigma b))
         (substExpr sigma C) u ac
adequacyV-ty-Case {H = H} {C = C} {M = M} {a = a} {b = b}
  dC dM da db IHC IHM IHa IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sM = substExpr sigma M ; sa = substExpr sigma a
    sb = substExpr sigma b ; sC = substExpr sigma C
    htC  = subst-HasType wtsub wfH dC
    hta  = subst-HasType wtsub wfH da
    htb0 = subst-HasType wtsub wfH db
    htb  : HasType H sb (Pi NatT (wkExpr sC))
    htb  = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subst-wk-comm sigma C) htb0

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      Val2 H (Case sM sa sb) sC u ac
    branchBot cb =
      restrictVal2 H (Case sM sa sb) sC Bot u ac (snd cb) fm
        (finMem-bot-from ac (FinMem-a-in-U u ac fm)) (Val2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      Val2 H (Case sM sa sb) sC u ac
    branchZero evM cb =
      let valM   = IHM sigma rho crho vs fits wtsub wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          red0   = snd valM                                   -- Red3 H sM Zero NatT
          hrZ    = Red3.hr red0
          ctZ    = Red3.ct red0
          val_sa = IHa sigma rho crho vs fits wtsub wfH u cb ac evAc fm
          hrCase = HeadRed-trans (HeadRed-Case hrZ) (headred-step headred-case-zero headred-refl)
          cvCase = conv-trans (conv-Case htC ctZ (conv-refl hta) (conv-refl htb))
                              (conv-case-zero htC hta htb)
      in Val2-beta-expand u ac hrCase cvCase val_sa

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      Val2 H (Case sM sa sb) sC u ac
    sucW v Bot          a'' () evM' fm_w' evNat cb
    sucW v UCode        a'' () evM' fm_w' evNat cb
    sucW v (FunEl _)    a'' () evM' fm_w' evNat cb
    sucW v (PiCode _ _) a'' () evM' fm_w' evNat cb
    sucW v NatCode      a'' () evM' fm_w' evNat cb
    sucW v ZeroEl       a'' () evM' fm_w' evNat cb
    sucW v (SucEl v'') a'' le evM' fm_w' evNat cb =
      let fm_sv'' = finMem-upward (SucEl v'') a'' NatCode (snd evNat) (fst evNat) tt fm_w' tt
          valM    = IHM sigma rho crho vs fits wtsub wfH (SucEl v'') evM' NatCode (mkSigma tt tt) fm_sv''
          cv''    = FinMem-coh-u (SucEl v'') a'' fm_w'        -- Coherent (SucEl v'') = Coherent v''
          fm_v''  = sucNat-to v'' fm_sv''
          cohv    = key-coh (EvalRel-coh b rho (FunEl (cons (mkSigma v u) nil)) cb)
          record { pred = pm ; red = redS ; htP = htP ; valP = valP0 } = snd valM
          valP    = unrelevelVal2-Nat v'' valP0
          argVal  = nat-argVal pm rho v v'' cohv cv'' fm_v'' le valP
          val_app = adequacyV-app-Nat dC db IHC IHb sigma rho crho vs fits wtsub wfH
                      v u cb pm htP argVal ac evAc fm
          hrCase  = HeadRed-trans (HeadRed-Case (Red3.hr redS)) (headred-step headred-case-suc headred-refl)
          cvCase  = conv-trans (conv-Case htC (Red3.ct redS) (conv-refl hta) (conv-refl htb))
                               (conv-case-suc htC htP hta htb)
      in Val2-beta-expand u ac hrCase cvCase val_app

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      Val2 H (Case sM sa sb) sC u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed) (fst (snd typed)) (fst (snd (snd typed)))
              (fst (snd (snd (snd typed)))) (fst (snd (snd (snd (snd typed)))))
              (snd (snd (snd (snd (snd typed))))) cb

------------------------------------------------------------------------
-- conv-Case : Case M a b = Case M' a' b' : C  (congruence).  Dispatch on the
-- scrutinee value; head-expand BOTH sides to their contracta (zero branch /
-- App b pred) and relate the contracta by the component conversions' IHs
-- (the SucEl arg conversion is REqValNatSuc.cvP).
------------------------------------------------------------------------

adequacyEqSub2-Case : {h g : Nat} {H : Ctx h} {G : Ctx g} {C M M' a a' b b' : Expr g} ->
  HasType G C U -> ConvTm G M M' NatT -> ConvTm G a a' C -> ConvTm G b b' (Pi NatT (wkExpr C)) ->
  Adq G C U -> AdqE1 G M M' NatT -> AdqE1 G a a' C -> AdqE1 G b b' (Pi NatT (wkExpr C)) ->
  (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel C rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case M a b)) (substExpr sigma (Case M' a' b'))
           (substExpr sigma C) u ac
adequacyEqSub2-Case {H = H} {C = C} {M = M} {M' = M'} {a = a} {a' = a'} {b = b} {b' = b'}
  dC dMM' daa' dbb' IHC IHM IHa IHb sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sM = substExpr sigma M ; sM' = substExpr sigma M'
    sa = substExpr sigma a ; sa' = substExpr sigma a'
    sb = substExpr sigma b ; sb' = substExpr sigma b' ; sC = substExpr sigma C
    dM  = fst (typing-ConvTm dMM') ; dM' = snd (typing-ConvTm dMM')
    da  = fst (typing-ConvTm daa') ; da' = snd (typing-ConvTm daa')
    db  = fst (typing-ConvTm dbb') ; db' = snd (typing-ConvTm dbb')
    htC  = subst-HasType wtsub wfH dC
    hta  = subst-HasType wtsub wfH da ; hta' = subst-HasType wtsub wfH da'
    htb  : HasType H sb (Pi NatT (wkExpr sC))
    htb  = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subst-wk-comm sigma C) (subst-HasType wtsub wfH db)
    htb' : HasType H sb' (Pi NatT (wkExpr sC))
    htb' = Eq-transport (\ X -> HasType H sb' (Pi NatT X)) (subst-wk-comm sigma C) (subst-HasType wtsub wfH db')

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branchBot cb =
      restrictEqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC Bot u ac (snd cb) fm
        (finMem-bot-from ac (FinMem-a-in-U u ac fm)) (EqVal2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branchZero evM cb =
      let eqZ   = IHM sigma rho crho vs fits wtsub wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          redM0 = fst (snd eqZ) ; redM0' = snd (snd eqZ)
          eqa   = IHa sigma rho crho vs fits wtsub wfH u cb ac evAc fm
          hr1   = HeadRed-trans (HeadRed-Case (Red3.hr redM0))  (headred-step headred-case-zero headred-refl)
          hr2   = HeadRed-trans (HeadRed-Case (Red3.hr redM0')) (headred-step headred-case-zero headred-refl)
          cv1   = conv-trans (conv-Case htC (Red3.ct redM0)  (conv-refl hta)  (conv-refl htb))  (conv-case-zero htC hta  htb)
          cv2   = conv-trans (conv-Case htC (Red3.ct redM0') (conv-refl hta') (conv-refl htb')) (conv-case-zero htC hta' htb')
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqa

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
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
          funcross = \ ub ap evb evp fmm -> IHb sigma rho crho vs fits wtsub wfH ub evb ap evp fmm
          argValL = nat-argVal pmL rho v v'' cohv cv'' fm_v'' le
                      (Val2-from-EqVal2-first v'' NatCode eqP)
          argEq   = nat-argEq pmL pmR rho v v'' cohv cv'' fm_v'' le eqP
          eqval_app = adequacyVE-app-Nat {FR = sb'} {NL = pmL} {NR = pmR} dC db IHC sigma rho crho vs fits wtsub wfH
                        v u cb funcross htL htR cvLR argValL argEq ac evAc fm
          hr1 = HeadRed-trans (HeadRed-Case (Red3.hr redL)) (headred-step headred-case-suc headred-refl)
          hr2 = HeadRed-trans (HeadRed-Case (Red3.hr redR)) (headred-step headred-case-suc headred-refl)
          cv1 = conv-trans (conv-Case htC (Red3.ct redL) (conv-refl hta)  (conv-refl htb))  (conv-case-suc htC htL hta  htb)
          cv2 = conv-trans (conv-Case htC (Red3.ct redR) (conv-refl hta') (conv-refl htb')) (conv-case-suc htC htR hta' htb')
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqval_app

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed) (fst (snd typed)) (fst (snd (snd typed)))
              (fst (snd (snd (snd typed)))) (fst (snd (snd (snd (snd typed)))))
              (snd (snd (snd (snd (snd typed))))) cb

------------------------------------------------------------------------
-- ty-Case (cross / two-substitution) : EqVal2 (Case M a b)[σ] [σ'] : C[σ].
-- Same shape as conv-Case but two subs of the SAME terms; the RIGHT contractum
-- is naturally typed at C[σ'], so its conversion is conv-conv'd to C[σ] via the
-- cross conversion C[σ] ~ C[σ'].
------------------------------------------------------------------------

adequacyVE-ty-Case : {h g : Nat} {H : Ctx h} {G : Ctx g} {C M a b : Expr g} ->
  HasType G C U -> HasType G M NatT -> HasType G a C -> HasType G b (Pi NatT (wkExpr C)) ->
  Adq G C U -> AdqConv G M NatT -> AdqConv G a C -> AdqConv G b (Pi NatT (wkExpr C)) ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (Case M a b) rho u ->
  (ac : FinEl) -> EvalRel C rho ac -> FinMem u ac ->
  EqVal2 H (substExpr sigma (Case M a b)) (substExpr sigma' (Case M a b))
           (substExpr sigma C) u ac
adequacyVE-ty-Case {H = H} {C = C} {M = M} {a = a} {b = b}
  dC dM da db IHC IHM IHa IHb sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu ac evAc fm =
  branch (fst hu) (fst (snd hu)) (snd (snd hu))
  where
    sM = substExpr sigma M ; sM' = substExpr sigma' M
    sa = substExpr sigma a ; sa' = substExpr sigma' a
    sb = substExpr sigma b ; sb' = substExpr sigma' b
    sC = substExpr sigma C ; sC' = substExpr sigma' C
    htC   = subst-HasType wtsub  wfH dC
    htC'  = subst-HasType wtsub' wfH dC
    cvCC' = subst-ConvTm-cross dC wtsub wtsub' wcs wfH      -- ConvTm H sC sC' U
    cvC'C = conv-sym cvCC'
    hta   = subst-HasType wtsub  wfH da ; hta' = subst-HasType wtsub' wfH da
    htb   : HasType H sb (Pi NatT (wkExpr sC))
    htb   = Eq-transport (\ X -> HasType H sb (Pi NatT X)) (subst-wk-comm sigma C) (subst-HasType wtsub wfH db)
    htb'  : HasType H sb' (Pi NatT (wkExpr sC'))
    htb'  = Eq-transport (\ X -> HasType H sb' (Pi NatT X)) (subst-wk-comm sigma' C) (subst-HasType wtsub' wfH db)

    branchBot : Pair (Coherent u) (LeCode u Bot) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branchBot cb =
      restrictEqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC Bot u ac (snd cb) fm
        (finMem-bot-from ac (FinMem-a-in-U u ac fm)) (EqVal2-Bot ac)

    branchZero : EvalRel M rho ZeroEl -> EvalRel a rho u ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branchZero evM cb =
      let eqZ   = IHM sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH ZeroEl evM NatCode (mkSigma tt tt) tt
          redM0 = fst (snd eqZ) ; redM0' = snd (snd eqZ)
          eqa   = IHa sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u cb ac evAc fm
          hr1   = HeadRed-trans (HeadRed-Case (Red3.hr redM0))  (headred-step headred-case-zero headred-refl)
          hr2   = HeadRed-trans (HeadRed-Case (Red3.hr redM0')) (headred-step headred-case-zero headred-refl)
          cv1   = conv-trans (conv-Case htC (Red3.ct redM0) (conv-refl hta) (conv-refl htb)) (conv-case-zero htC hta htb)
          cv2'  = conv-trans (conv-Case htC' (Red3.ct redM0') (conv-refl hta') (conv-refl htb')) (conv-case-zero htC' hta' htb')
          cv2   = conv-conv cv2' cvC'C htC
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqa

    sucW : (v w' a'' : FinEl) -> LeCode (SucEl v) w' ->
      EvalRel M rho w' -> FinMem w' a'' -> EvalRel NatT rho a'' ->
      EvalRel b rho (FunEl (cons (mkSigma v u) nil)) ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
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
          argValL = nat-argVal pmL rho v v'' cohv cv'' fm_v'' le
                      (Val2-from-EqVal2-first v'' NatCode eqP)
          argEq   = nat-argEq pmL pmR rho v v'' cohv cv'' fm_v'' le eqP
          eqval_app = adequacyVE-app-Nat {FR = sb'} {NL = pmL} {NR = pmR} dC db IHC sigma rho crho vs fits wtsub wfH
                        v u cb funcross htL htR cvLR argValL argEq ac evAc fm
          hr1 = HeadRed-trans (HeadRed-Case (Red3.hr redL)) (headred-step headred-case-suc headred-refl)
          hr2 = HeadRed-trans (HeadRed-Case (Red3.hr redR)) (headred-step headred-case-suc headred-refl)
          cv1 = conv-trans (conv-Case htC (Red3.ct redL) (conv-refl hta) (conv-refl htb)) (conv-case-suc htC htL hta htb)
          cv2' = conv-trans (conv-Case htC' (Red3.ct redR) (conv-refl hta') (conv-refl htb')) (conv-case-suc htC' htR hta' htb')
          cv2  = conv-conv cv2' cvC'C htC
      in EqVal2-headred-expand u ac hr1 hr2 cv1 cv2 eqval_app

    branch : (w : FinEl) -> EvalRel M rho w -> CaseBranch a b rho u w ->
      EqVal2 H (Case sM sa sb) (Case sM' sa' sb') sC u ac
    branch Bot          evM cb = branchBot cb
    branch UCode        evM ()
    branch (FunEl g)    evM ()
    branch (PiCode d f) evM ()
    branch NatCode      evM ()
    branch ZeroEl       evM cb = branchZero evM cb
    branch (SucEl v)    evM cb =
      let typed = theorem1 dM rho fits (SucEl v) evM
      in sucW v (fst typed) (fst (snd typed)) (fst (snd (snd typed)))
              (fst (snd (snd (snd typed)))) (fst (snd (snd (snd (snd typed)))))
              (snd (snd (snd (snd (snd typed))))) cb
