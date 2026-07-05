{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- AdequacyVE.agda  (MIN/ -- PROTOTYPE)
--
-- Prototype of the "bundled validity" re-architecture of the adequacy
-- fundamental lemma, matching Abel-Oehman-Vezzosi (POPL18): validity is
-- inherently the TWO-substitution (sigma = sigma') statement, of which
-- the single-substitution reducibility is the diagonal.
--
--   AdqV G M A    (= AdequacyPi.AdqConv)  : HasType -> two subs -> EqVal2 (sM)(s'M)(sA)
--   AdqE G M N A                          : ConvTm  -> two subs -> EqVal2 (sM)(s'N)(sA)
--
-- The decisive point this file validates: in the conv-Pi case, the
-- codomain's two-substitution validity (which the current proof obtains
-- from the typing presupposition `fst (typing-ConvTm d2)`, a NON-subterm)
-- is instead derived from the cross IH `adequacyE d2` purely via
-- EqVal2-trans / EqVal2-sym -- i.e. from the pattern-bound subterm d2.
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.VE where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.Pi using (Adq ; AdqConv ; adequacy-ty-Pi ;
  Val2-U-to-ValTy2 ; EqVal2-U-to-EqValTy2 ; transportVal2' ; transportEqVal2')

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; coh-from-aU ;
  FinMem ; FinMem-a-in-U ; FinMem-coh-u ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ;
  finMemUCode-Sup ; finMem-upward)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-coh ;
  CoherentEnv ; EvalRel-Comp)
open import ID.Model.Soundness using (convSound ; convSound-inv)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; subst1 ; Sub ; liftSub ; substExpr)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm ; WfCtx ; wf-extend ;
  ty-U ; ty-Pi ; conv-refl ; conv-sym ; conv-conv ; conv-Pi)
open import ID.Syntax.Substitution using (WtSub ; WtConvSub ; subst-HasType ; typing-ConvTm ;
  liftSub-WtSub ; subst-ConvTm-cross ; liftSub-WtConvSub ; ctx-conv-HasType ; subst-ConvTm)
open import ID.Model.SoundnessLemmas using (Fits)
open import ID.Validity.Core using (FinMem-Coherent)
open import ID.Model.Eval using (EvalRel-mon-env ; EnvLe-refl)
open import ID.Model.Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode)
open import ID.Syntax.Reduction using (headred-refl)
open import ID.Syntax.Typing using (ty-conv)

------------------------------------------------------------------------
-- The bundled fundamental-theorem statements.
--   AdqV = AdequacyPi.AdqConv (HasType, two subs)   -- re-use as-is
--   AdqE = its conversion analogue (ConvTm, two subs, cross M/N)
------------------------------------------------------------------------

AdqE : {g : Nat} (G : Ctx g) (M N A : Expr g) -> Set
AdqE {g} G M N A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma' N) (substExpr sigma A) u a

------------------------------------------------------------------------
-- KEY LEMMA.  The codomain two-substitution validity from the cross IH.
--
-- Given the cross IH for a conversion  M = N : U,  the SAME-term two-sub
-- validity of the LEFT endpoint M is
--      M[sigma] = M[sigma']
-- and it is obtained as
--      trans (E s s' : M[s] = N[s'])  (sym (E s' s' : M[s'] = N[s'])).
-- Both EqVal2's sit at type U (substExpr s U = U for any s), so the
-- transitivity is well-typed with no type-transport.  Every use of the
-- IH is on the same derivation; nothing touches typing-ConvTm.
------------------------------------------------------------------------

AdqE-to-AdqConv-left-U : {g : Nat} {G : Ctx g} {M N : Expr g} ->
  AdqE G M N U -> AdqConv G M U
AdqE-to-AdqConv-left-U {G = G} IH-E sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
  let cu  = FinMem-Coherent u a fm
      ca  = EvalRel-coh U rho a evA
      ev1 = IH-E sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm
      ev2 = IH-E sigma' sigma' rho crho vs' vs' (ValidConvSub2-refl {G = G} vs') fits
              wtsub' wtsub' (WtConvSub-refl {G = G} wtsub') wfH u hu a evA fm
  in EqVal2-trans u a cu ca ev1 (EqVal2-sym u a cu ca ev2)

-- Symmetric version: the RIGHT endpoint N's two-sub validity.  Needs the
-- ConvTm M = N : U to convert the given  EvalRel N rho u  to  EvalRel M rho u
-- (convSound-inv); then  N[s] = N[s']  =  trans (sym (E s s : M[s]=N[s])) (E s s' : M[s]=N[s']).
AdqE-to-AdqConv-right-U : {g : Nat} {G : Ctx g} {M N : Expr g} ->
  AdqE G M N U -> ConvTm G M N U -> AdqConv G N U
AdqE-to-AdqConv-right-U {G = G} IH-E dMN sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u huN a evA fm =
  let huM = convSound-inv dMN rho fits u huN
      cu  = FinMem-Coherent u a fm
      ca  = EvalRel-coh U rho a evA
      ev0 = IH-E sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs) fits
              wtsub wtsub (WtConvSub-refl {G = G} wtsub) wfH u huM a evA fm
      ev1 = IH-E sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u huM a evA fm
  in EqVal2-trans u a cu ca (EqVal2-sym u a cu ca ev0) ev1

------------------------------------------------------------------------
-- ValTy2 extractors from EqVal2 at U (local; AdequacyPi exports only the
-- EqValTy2 one).  EqVal2 M N U v UCode = (ValTy2 U, ValTy2 M, ValTy2 N, EqValTy2).
------------------------------------------------------------------------

EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N : Expr n}
  (v0 : FinEl) -> FinMem v0 UCode -> EqVal2 G M N U v0 UCode -> ValTy2 G M v0
EqVal2-U-to-ValTy2-fst Bot _ _ = tt
EqVal2-U-to-ValTy2-fst UCode _ ev = fst (snd ev)
EqVal2-U-to-ValTy2-fst (PiCode _ _) _ ev = fst (snd ev)
EqVal2-U-to-ValTy2-fst (IdCode _ _ _) _ ev = fst (snd ev)
EqVal2-U-to-ValTy2-fst (FunEl _) () _

EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N : Expr n}
  (v0 : FinEl) -> FinMem v0 UCode -> EqVal2 G M N U v0 UCode -> ValTy2 G N v0
EqVal2-U-to-ValTy2-snd Bot _ _ = tt
EqVal2-U-to-ValTy2-snd UCode _ ev = fst (snd (snd ev))
EqVal2-U-to-ValTy2-snd (PiCode _ _) _ ev = fst (snd (snd ev))
EqVal2-U-to-ValTy2-snd (IdCode _ _ _) _ ev = fst (snd (snd ev))
EqVal2-U-to-ValTy2-snd (FunEl _) () _

------------------------------------------------------------------------
-- Diagonal adapter: single-substitution validity (Val2) is AdqConv at
-- sigma' = sigma, projected with Val2-from-EqVal2-first.
------------------------------------------------------------------------

V-to-diag : {g : Nat} {G : Ctx g} {M A : Expr g} -> AdqConv G M A -> Adq G M A
V-to-diag {G = G} IH-V sigma rho crho vs fits wtsub wfH u hu a evA fm =
  Val2-from-EqVal2-first u a
    (IH-V sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs) fits
       wtsub wtsub (WtConvSub-refl {G = G} wtsub) wfH u hu a evA fm)

------------------------------------------------------------------------
-- adequacyV-ty-Pi : the ty-Pi case of the bundled HasType lemma (AdqV).
-- Port of the existing  adequacyConvSub2 (ty-Pi d1 d2)  clause, with
--   adequacyConvSub2 d1 -> IH-V-A      (subterm IH)
--   adequacyConvSub2 d2 -> IH-V-B      (subterm IH)
--   adequacySub2-Pi d1 d2 -> adequacy-ty-Pi (reused) at the diagonals
--   transportVal2 d1 d2  -> transportVal2' (V-to-diag IH-V-A)
-- NON-recursive: takes the premises' bundled IHs as parameters.
------------------------------------------------------------------------

adequacyV-ty-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} ->
  HasType G A U -> HasType (extend G A) B U ->
  AdqConv G A U -> AdqConv (extend G A) B U ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (b : FinEl) (f0 : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f0) -> EvalRel U rho UCode -> FinMem (PiCode b f0) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma' (Pi A B)) (substExpr sigma U)
    (PiCode b f0) UCode
adequacyV-ty-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 IH-V-A IH-V-B
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f0 hu evA fm =
  mkSigma (fst valTyPi_s) (mkSigma (snd valTyPi_s) (mkSigma (snd valTyPi_s')
    (mk-EqValTyPi (snd valTyPi_s) (snd valTyPi_s') eqValTyPi)))
  where
    IH-A-diag = V-to-diag {G = G} {M = A} {A = U} IH-V-A
    IH-B-diag = V-to-diag {G = extend G A} {M = B} {A = U} IH-V-B
    sA   = substExpr sigma A
    sA'  = substExpr sigma' A
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma') B
    bU   = finMem-piU-dom b f0 fm
    allU = finMem-piU-allU b f0 fm
    cf   = finMem-piU-cft b f0 fm
    cb   = coh-from-aU b bU
    evUU = mkSigma tt (LeCode-refl UCode tt)
    evAb = fst (snd hu)
    bodyPi = snd (snd (snd (snd hu)))

    valTyPi_s  = adequacy-ty-Pi d1 d2 IH-A-diag IH-B-diag IH-V-B
                   sigma rho crho vs fits wtsub wfH b f0 hu evA fm
    valTyPi_s' = adequacy-ty-Pi d1 d2 IH-A-diag IH-B-diag IH-V-B
                   sigma' rho crho vs' fits wtsub' wfH b f0 hu evA fm

    eqD1 = IH-V-A sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evUU bU
    eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

    htA_loc  = subst-HasType wtsub wfH d1
    htA'_loc = subst-HasType wtsub' wfH d1
    convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
    wtsub_lift  = liftSub-WtSub wtsub wfH d1
    wtsub'_lift_raw = liftSub-WtSub wtsub' wfH d1
    wtsub'_lift : WtSub (extend H sA) (extend G A) (liftSub sigma')
    wtsub'_lift = \ i -> ctx-conv-HasType htA'_loc htA_loc (conv-sym convA) (wtsub'_lift_raw i)
    wcs_lift    = liftSub-WtConvSub wtsub wcs wfH d1
    wfH_ext     = wf-extend htA_loc
    convB       = subst-ConvTm-cross d2 wtsub_lift wtsub'_lift wcs_lift wfH_ext

    buildEdgeCrossBB' : PiEdgeEqTy2 H sA sB sB' b f0
    buildEdgeCrossBB' u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          evU'     = mkSigma tt (LeCode-refl UCode tt)
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {A = A} IH-A-diag sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs_ext   = ValidSub2-extend sigma P rho u0 vs hyp0
          valP'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valP
          hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal2' {A = A} IH-A-diag sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le_u' a_arg evA_arg fm_u'_a
          vs_ext'  = ValidSub2-extend sigma' P rho u0 vs' hyp0'
          hyp0_eq  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       Val2-to-EqVal2 u' a_arg
                         (transportVal2' {A = A} IH-A-diag sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a)
          vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs hyp0_eq
          wtsub_ext  = extSub-WtSub wtsub wfH d1 htP
          htP'       = ty-conv htP convA htA'_loc
          wtsub_ext' = extSub-WtSub wtsub' wfH d1 htP'
          wcs_ext  = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
          raw      = IH-V-B (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                       crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                       v0 evB_u0_v0 UCode evU' fm_v0_U
          eq_B1    = S.Eq-sym (substExpr-comp sigma B P)
          eq_B2    = S.Eq-sym (substExpr-comp sigma' B P)
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB P) T U v0 UCode) eq_B2
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) B) U v0 UCode) eq_B1 raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    htB_loc  = subst-HasType wtsub_lift wfH_ext d2
    wfH_ext'    = wf-extend htA'_loc
    htB'_loc_raw = subst-HasType wtsub'_lift_raw wfH_ext' d2
    htPiM    = ty-Pi htA_loc htB_loc
    htPiN    = ty-Pi htA'_loc htB'_loc_raw

    eqValTyPi : REqValTyPi H (Pi sA sB) (Pi sA' sB') b f0
    eqValTyPi = record
      { domA   = sA
      ; codB   = sB
      ; domA'  = sA'
      ; codB'  = sB'
      ; redM   = mkRed3 headred-refl (conv-refl htPiM)
      ; redN   = mkRed3 headred-refl (conv-refl htPiN)
      ; cohF   = cf
      ; fmAllU = allU
      ; convA  = convA
      ; convB  = convB
      ; eqA    = eqValTyAA'
      ; edgeET = buildEdgeCrossBB'
      }

------------------------------------------------------------------------
-- convPi-single : the SINGLE-substitution conv-Pi.  Faithful port of the
-- existing adequacyEqSub2-Pi clause, EXCEPT the two presupposition
-- recursions are replaced by the key lemmas on the cross IHs:
--   adequacyConvSub2 (fst (typing-ConvTm d2))  ->  AdqE-to-AdqConv-left-U  IH-E-B
--   adequacyConvSub2 (snd (typing-ConvTm d2))  ->  AdqE-to-AdqConv-right-U IH-E-B d2
-- and the conversion IHs adequacyEqSub2 d1/d2 by the diagonals IA-diag/IB-diag.
-- typing-ConvTm is kept ONLY for typing fields (no recursion).
------------------------------------------------------------------------

convPi-single : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  AdqE G A A' U -> AdqE (extend G A) B B' U ->
  (sigma : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) -> EvalRel U rho UCode -> FinMem (PiCode b f) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma (Pi A' B')) U (PiCode b f) UCode
convPi-single {h = h} {g = g} {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 IH-E-A IH-E-B sigma rho crho vs fits wtsub wfH b f hu evU fm =
  let valTyU : ValTy2 H U UCode
      valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))
  in mkSigma valTyU (mkSigma valTyPiAB (mkSigma valTyPiA'B' eqValTyPi))
  where
    sA   = substExpr sigma A
    sA'  = substExpr sigma A'
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma) B'
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evUU = mkSigma tt (LeCode-refl UCode tt)
    evAb = fst (snd hu)
    a'pi = fst (snd (snd hu))
    bodyPi = snd (snd (snd (snd hu)))

    IHA-Val : Adq G A U
    IHA-Val = V-to-diag {G = G} {M = A} {A = U} (AdqE-to-AdqConv-left-U {G = G} {M = A} {N = A'} IH-E-A)
    BVtwo : AdqConv (extend G A) B U
    BVtwo = AdqE-to-AdqConv-left-U {G = extend G A} {M = B} {N = B'} IH-E-B
    BV'two : AdqConv (extend G A) B' U
    BV'two = AdqE-to-AdqConv-right-U {G = extend G A} {M = B} {N = B'} IH-E-B d2

    IA-diag : (u : FinEl) -> EvalRel A rho u -> (a : FinEl) -> EvalRel U rho a -> FinMem u a ->
      EqVal2 H sA sA' (substExpr sigma U) u a
    IA-diag u hu0 a evA fm0 =
      IH-E-A sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs) fits
        wtsub wtsub (WtConvSub-refl {G = G} wtsub) wfH u hu0 a evA fm0

    IB-diag : (sigmaX : Sub h (suc g)) (rhoX : EnvApprox (suc g)) -> CoherentEnv rhoX ->
      ValidSub2 H (extend G A) sigmaX rhoX -> Fits (extend G A) rhoX ->
      WtSub H (extend G A) sigmaX -> WfCtx H ->
      (u : FinEl) -> EvalRel B rhoX u -> (a : FinEl) -> EvalRel U rhoX a -> FinMem u a ->
      EqVal2 H (substExpr sigmaX B) (substExpr sigmaX B') (substExpr sigmaX U) u a
    IB-diag sigmaX rhoX crhoX vsX fitsX wtsubX wfHX u hu0 a evA fm0 =
      IH-E-B sigmaX sigmaX rhoX crhoX vsX vsX (ValidConvSub2-refl {G = extend G A} vsX) fitsX
        wtsubX wtsubX (WtConvSub-refl {G = extend G A} wtsubX) wfHX u hu0 a evA fm0

    eqD1 = IA-diag b evAb UCode evUU bU
    valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
    valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
    eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
    eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

    trVal : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr h) -> Val2 H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val2 H N sA u' a_arg
    trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                       (IA-diag a_arg evA_arg UCode evUU a_argU)
          vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
          val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3

    buildEdgeValB2 : PiEdgeVal2 H sA sB b f
    buildEdgeValB2 u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
          ih       = IB-diag (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
           (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

    buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
    buildEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {A = A} IHA-Val sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
          raw      = BVtwo (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
    buildEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
      let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
          ih       = IB-diag (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
           (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

    buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
    buildEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          htA_loc  = subst-HasType wtsub wfH dA_conv
          convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
          htN1_A   = ty-conv htN1_A' convA'A htA_loc
          htN2_A   = ty-conv htN2_A' convA'A htA_loc
          cvN_A    = conv-conv cvN_A' convA'A htA_loc
          eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
          valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
          valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
          evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {A = A} IHA-Val sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
          raw      = BV'two (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB'_u0_v0 UCode evUU fm_v0_U
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
    buildEdgeEqTyBB'2 u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
          ih       = IB-diag (extSub sigma P) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
          eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                       (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                         (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
      in eqvt

    htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
    htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

    valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
    valTyPiAB = mk-ValTyPi (record
      { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; cohF = cf ; fmAllU = allU ; htA = htA_AB ; htB = htB_AB
      ; valA = valTyA ; edgeV = buildEdgeValB2 ; edgeE = buildEdgeEqB2 })

    htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
    htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
    htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

    valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
    valTyPiA'B' = mk-ValTyPi (record
      { domA = sA' ; codB = sB' ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU ; htA = htA_A'B' ; htB = htB_A'B'
      ; valA = valTyA' ; edgeV = buildEdgeValB'2 ; edgeE = buildEdgeEqB'2 })

    convA_sub  = subst-ConvTm wtsub wfH d1
    convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

    eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
    eqValTyPi = mk-EqValTyPi valTyPiAB valTyPiA'B' (record
      { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
      ; redM = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU
      ; convA = convA_sub ; convB = convB_sub
      ; eqA = eqValTyAA' ; edgeET = buildEdgeEqTyBB'2 })

------------------------------------------------------------------------
-- adequacyE-conv-Pi : the conv-Pi case of the bundled conversion lemma
-- (AdqE), at the (PiCode b f, UCode) instance.  Built as the composite
--   (Pi A B)[s] = (Pi A B)[s']    -- adequacyV-ty-Pi  (same term, two subs)
--   (Pi A B)[s'] = (Pi A' B')[s'] -- convPi-single    (term conversion at s')
-- glued by EqVal2-trans.  All IHs are on the subterms d1, d2; the
-- codomain two-sub flows through AdqE-to-AdqConv-{left,right}-U.
-- NON-recursive, no postulate.
------------------------------------------------------------------------

adequacyE-conv-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  AdqE G A A' U -> AdqE (extend G A) B B' U ->
  (sigma sigma' : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits G rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) -> EvalRel U rho UCode -> FinMem (PiCode b f) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma' (Pi A' B')) U (PiCode b f) UCode
adequacyE-conv-Pi {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2 IH-E-A IH-E-B
    sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f hu evU fm =
  let dA = fst (typing-ConvTm d1)
      dB = fst (typing-ConvTm d2)
      AdqConv-A = AdqE-to-AdqConv-left-U {G = G} {M = A} {N = A'} IH-E-A
      AdqConv-B = AdqE-to-AdqConv-left-U {G = extend G A} {M = B} {N = B'} IH-E-B
      c_pi = FinMem-Coherent (PiCode b f) UCode fm
      c_U  = EvalRel-coh U rho UCode evU
      X = adequacyV-ty-Pi dA dB AdqConv-A AdqConv-B
            sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b f hu evU fm
      Y = convPi-single d1 d2 IH-E-A IH-E-B
            sigma' rho crho vs' fits wtsub' wfH b f hu evU fm
  in EqVal2-trans (PiCode b f) UCode c_pi c_U X Y

------------------------------------------------------------------------
-- AdqE1 : the VALUE-ONLY single-substitution conversion adequacy statement
-- (the type of  adequacyEqSub2 d  with the derivation fixed).
------------------------------------------------------------------------

AdqE1 : {g : Nat} (G : Ctx g) (M N A : Expr g) -> Set
AdqE1 {g} G M N A =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

------------------------------------------------------------------------
-- adequacyEqSub2-Pi-core : the conv-Pi case of the VALUE-ONLY single-sub
-- conversion adequacy, factored out of the monolithic Adequacy.agda block.
-- Unlike convPi-single (which derives the codomain two-subs from the
-- non-total value-only cross via AdqE-to-AdqConv), this takes them as IH
-- VALUES supplied by the driver:
--   IH-A   = adequacySub2 dA       : Adq G A U                    (dA premise)
--   IH-eA  = adequacyEqSub2 d1     : AdqE1 G A A' U
--   IH-eB  = adequacyEqSub2 d2     : AdqE1 (extend G A) B B' U
--   IH-cB  = adequacyConvSub2 dB   : AdqConv (extend G A) B U      (dB premise)
--   IH-cB' = adequacyConvSub2 dB'  : AdqConv (extend G A) B' U     (dB' premise)
-- All on subderivations / conv-Pi premises -> the driver stays structural.
------------------------------------------------------------------------

adequacyEqSub2-Pi-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A A' : Expr g} {B B' : Expr (suc g)} ->
  ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
  Adq G A U -> AdqE1 G A A' U -> AdqE1 (extend G A) B B' U ->
  AdqConv (extend G A) B U -> AdqConv (extend G A) B' U ->
  (sigma : Sub h g) (rho : EnvApprox g) -> CoherentEnv rho ->
  ValidSub2 H G sigma rho -> Fits G rho -> WtSub H G sigma -> WfCtx H ->
  (b : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode b f) -> EvalRel U rho UCode -> FinMem (PiCode b f) UCode ->
  EqVal2 H (substExpr sigma (Pi A B)) (substExpr sigma (Pi A' B')) U (PiCode b f) UCode
adequacyEqSub2-Pi-core {h = h} {g = g} {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 IH-A IH-eA IH-eB IH-cB IH-cB' sigma rho crho vs fits wtsub wfH b f hu evU fm =
  let valTyU : ValTy2 H U UCode
      valTyU = mkRed3 headred-refl (conv-refl (ty-U wfH))
  in mkSigma valTyU (mkSigma valTyPiAB (mkSigma valTyPiA'B' eqValTyPi))
  where
    sA   = substExpr sigma A
    sA'  = substExpr sigma A'
    sB   = substExpr (liftSub sigma) B
    sB'  = substExpr (liftSub sigma) B'
    bU   = finMem-piU-dom b f fm
    allU = finMem-piU-allU b f fm
    cf   = finMem-piU-cft b f fm
    cb   = coh-from-aU b bU
    evUU = mkSigma tt (LeCode-refl UCode tt)
    evAb = fst (snd hu)
    a'pi = fst (snd (snd hu))
    bodyPi = snd (snd (snd (snd hu)))

    IHA-Val : Adq G A U
    IHA-Val = IH-A
    BVtwo : AdqConv (extend G A) B U
    BVtwo = IH-cB
    BV'two : AdqConv (extend G A) B' U
    BV'two = IH-cB'

    IA-diag : (u : FinEl) -> EvalRel A rho u -> (a : FinEl) -> EvalRel U rho a -> FinMem u a ->
      EqVal2 H sA sA' (substExpr sigma U) u a
    IA-diag u hu0 a evA fm0 =
      IH-eA sigma rho crho vs fits wtsub wfH u hu0 a evA fm0

    IB-diag : (sigmaX : Sub h (suc g)) (rhoX : EnvApprox (suc g)) -> CoherentEnv rhoX ->
      ValidSub2 H (extend G A) sigmaX rhoX -> Fits (extend G A) rhoX ->
      WtSub H (extend G A) sigmaX -> WfCtx H ->
      (u : FinEl) -> EvalRel B rhoX u -> (a : FinEl) -> EvalRel U rhoX a -> FinMem u a ->
      EqVal2 H (substExpr sigmaX B) (substExpr sigmaX B') (substExpr sigmaX U) u a
    IB-diag sigmaX rhoX crhoX vsX fitsX wtsubX wfHX u hu0 a evA fm0 =
      IH-eB sigmaX rhoX crhoX vsX fitsX wtsubX wfHX u hu0 a evA fm0

    eqD1 = IA-diag b evAb UCode evUU bU
    valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
    valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
    eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
    eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

    trVal : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr h) -> Val2 H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val2 H N sA u' a_arg
    trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                       (IA-diag a_arg evA_arg UCode evUU a_argU)
          vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
          val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3

    buildEdgeValB2 : PiEdgeVal2 H sA sB b f
    buildEdgeValB2 u0 v0 sel N htN valN =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
          ih       = IB-diag (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
           (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

    buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
    buildEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
      let valN1    = Val2-from-EqVal2-first u0 b eqvalN
          valN2    = Val2-from-EqVal2-second u0 b eqvalN
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {A = A} IHA-Val sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
          raw      = BVtwo (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB_u0_v0 UCode evUU fm_v0_U
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
    buildEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
      let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
          fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N valN_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
          htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
          ih       = IB-diag (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
      in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
           (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

    buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
    buildEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          dA_conv  = fst (typing-ConvTm d1)
          htA_loc  = subst-HasType wtsub wfH dA_conv
          convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
          htN1_A   = ty-conv htN1_A' convA'A htA_loc
          htN2_A   = ty-conv htN2_A' convA'A htA_loc
          cvN_A    = conv-conv cvN_A' convA'A htA_loc
          eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
          valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
          valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
          evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
          wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
          wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
          vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                       (ValidConvSub2-refl {G = G} vs)
                       (transportEqVal2' {A = A} IHA-Val sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
          wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
          raw      = BV'two (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                       v0 evB'_u0_v0 UCode evUU fm_v0_U
          raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                       (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
      in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

    buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
    buildEdgeEqTyBB'2 u0 v0 sel P htP valP =
      let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
          cu0      = FinMem-coh-u u0 b fm_u0_b
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
          wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
          ih       = IB-diag (extSub sigma P) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
          eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                       (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                         (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
      in eqvt

    htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
    htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

    valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
    valTyPiAB = mk-ValTyPi (record
      { domA = sA ; codB = sB ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; cohF = cf ; fmAllU = allU ; htA = htA_AB ; htB = htB_AB
      ; valA = valTyA ; edgeV = buildEdgeValB2 ; edgeE = buildEdgeEqB2 })

    htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
    htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
    htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

    valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
    valTyPiA'B' = mk-ValTyPi (record
      { domA = sA' ; codB = sB' ; red = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU ; htA = htA_A'B' ; htB = htB_A'B'
      ; valA = valTyA' ; edgeV = buildEdgeValB'2 ; edgeE = buildEdgeEqB'2 })

    convA_sub  = subst-ConvTm wtsub wfH d1
    convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

    eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
    eqValTyPi = mk-EqValTyPi valTyPiAB valTyPiA'B' (record
      { domA = sA ; codB = sB ; domA' = sA' ; codB' = sB'
      ; redM = mkRed3 headred-refl (conv-refl (ty-Pi htA_AB htB_AB))
      ; redN = mkRed3 headred-refl (conv-refl (ty-Pi htA_A'B' htB_A'B'))
      ; cohF = cf ; fmAllU = allU
      ; convA = convA_sub ; convB = convB_sub
      ; eqA = eqValTyAA' ; edgeET = buildEdgeEqTyBB'2 })
