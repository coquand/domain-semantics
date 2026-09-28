{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Relevel
--
-- The adequacy statements are stable under strengthening the level
-- constraints of the context (same term skeleton, constraints entailing
-- the old ones): every substitution into the stronger context is one
-- into the weaker, with the same environment.  The semantic analogue of
-- BCDE4.RussellRelevel, used by the level-variation cases of the driver
-- (whose target contexts carry an extra equation l = l').
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Relevel (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D

import BCDE4.Dom.Basic as S
open S using (Nat ; mkSigma ; fst ; snd ; FinEl)
open import BCDE4.Basic using (Fin)
open import BCDE4.Model.Eval D using (EnvApprox ; emptyEnv ; extendEnv ; EvalRel)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.Levels using (LCtx ; LSub ; lidS ; validC-lsub ; ent-trans)
open import BCDE4.RussellSyntax using (Expr ; Sub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellRelevel using (Skel ; sk-empty ; sk-extend ; skel-lookup ; CEnt)
open import BCDE4.RussellMeta using (WtSub ; mkWt ; wtE ; wtT)
open import BCDE4.RussellMetaCong using (ConvTmSub ; mkCS ; csE ; csT)

private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- The data of a substitution, from the stronger to the weaker context
------------------------------------------------------------------------

fits-rel : {n : Nat} {G K : Ctx n} {rho : EnvApprox TL θ n} ->
  Skel G K -> CEnt K G -> Fits (stripCtx K) rho -> Fits (stripCtx G) rho
fits-rel {θ = θ} {rho = emptyEnv} sk-empty e f =
  mkSigma (fst f) (\ {c} h -> validC-lsub θ c (snd f) (e h))
fits-rel {rho = extendEnv rho x} (sk-extend s) e f = mkSigma (fits-rel s e (fst f)) (snd f)

module _ {h g : Nat} {H : Ctx h} {G K : Ctx g} (s : Skel G K) where

  vs-rel : {sigma : Sub h g} {rho : EnvApprox (lctx H) lidS g} ->
    ValidSub2 H K sigma rho -> ValidSub2 H G sigma rho
  vs-rel {sigma} {rho} vs i u cu le a ev fm =
    S.Eq-transport (\ T -> Val2 H (sigma i) (substExpr sigma T) u a) (skel-lookup s i)
      (vs i u cu le a (S.Eq-transport (\ T -> EvalRel (strip T) rho a) (S.Eq-sym (skel-lookup s i)) ev) fm)

  vcs-rel : {sigma sigma' : Sub h g} {rho : EnvApprox (lctx H) lidS g} ->
    ValidConvSub2 H K sigma sigma' rho -> ValidConvSub2 H G sigma sigma' rho
  vcs-rel {sigma} {sigma'} {rho} vcs i u cu le a ev fm =
    S.Eq-transport (\ T -> EqVal2 H (sigma i) (sigma' i) (substExpr sigma T) u a) (skel-lookup s i)
      (vcs i u cu le a (S.Eq-transport (\ T -> EvalRel (strip T) rho a) (S.Eq-sym (skel-lookup s i)) ev) fm)

  wt-rel : {sigma : Sub h g} -> CEnt K G -> WtSub H K sigma -> WtSub H G sigma
  wt-rel {sigma} e ws =
    mkWt (ent-trans (wtE ws) e)
         (\ i -> S.Eq-transport (\ T -> HasType H (sigma i) (substExpr sigma T)) (skel-lookup s i) (wtT ws i))

  wcs-rel : {sigma sigma' : Sub h g} -> CEnt K G -> ConvTmSub H K sigma sigma' -> ConvTmSub H G sigma sigma'
  wcs-rel {sigma} {sigma'} e cs =
    mkCS (ent-trans (csE cs) e)
         (\ i -> S.Eq-transport (\ T -> ConvTm H (sigma i) (sigma' i) (substExpr sigma T)) (skel-lookup s i) (csT cs i))

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

module _ {g : Nat} {G K : Ctx g} (s : Skel G K) (e : CEnt K G) where

  relAdq : {M A : Expr g} -> Adq G M A -> Adq K M A
  relAdq IH sigma rho crho vs fits wt wfH =
    IH sigma rho crho (vs-rel s vs) (fits-rel s e fits) (wt-rel s e wt) wfH

  relConv : {M A : Expr g} -> AdqConv G M A -> AdqConv K M A
  relConv IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH =
    IH sigma sigma' rho crho (vs-rel s vs) (vs-rel s vs') (vcs-rel s vcs) (fits-rel s e fits)
       (wt-rel s e wt) (wt-rel s e wt') (wcs-rel s e wcs) wfH

  relE1 : {M N A : Expr g} -> AdqE1 G M N A -> AdqE1 K M N A
  relE1 IH sigma rho crho vs fits wt wfH =
    IH sigma rho crho (vs-rel s vs) (fits-rel s e fits) (wt-rel s e wt) wfH

  relTy : {A : Expr g} -> AdqTy G A -> AdqTy K A
  relTy IH sigma rho crho vs fits wt wfH =
    IH sigma rho crho (vs-rel s vs) (fits-rel s e fits) (wt-rel s e wt) wfH

  relConvTy : {A : Expr g} -> AdqConvTy G A -> AdqConvTy K A
  relConvTy IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH =
    IH sigma sigma' rho crho (vs-rel s vs) (vs-rel s vs') (vcs-rel s vcs) (fits-rel s e fits)
       (wt-rel s e wt) (wt-rel s e wt') (wcs-rel s e wcs) wfH

  relETy : {A B : Expr g} -> AdqETy G A B -> AdqETy K A B
  relETy IH sigma rho crho vs fits wt wfH =
    IH sigma rho crho (vs-rel s vs) (fits-rel s e fits) (wt-rel s e wt) wfH
