{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Guard
--
-- The adequacy cases for constraint products [ψ]A / ⟨ψ⟩t, the empty
-- type ∅ and the collapse rules (bcde.pdf Fig. 13, 14).
--
-- The ambient level theory of the model is lctx H, the constraints of
-- the target context.  A semantic witness of [ψ]A is either ⊥ (nothing
-- to prove) or a witness of A together with a proof that ψ is valid in
-- lctx H; in the latter case the substitution is also a substitution
-- into Γ,ψ, the induction hypothesis applies in the SAME target H, and
-- the guard is removed by head expansion ([ψ]A ~> A).  No Kripke
-- quantification and no transport between level contexts is needed.
--
-- Collapse: a fitting environment makes lctx H loop-free and entail the
-- constraints of Γ, so a loop in Γ is absurd.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Guard (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; mkSigma ; fst ; snd ; Pair ;
              Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; U0)
open import BCDE4.Basic using (Either ; inl ; inr ; Fin)
open import BCDE4.Dom.Kernel using (FinMem ; Coherent ; LeCode ; FinMem-a-in-U)
open import BCDE4.Model.Eval D using (EnvApprox ; EvalRel ; EvalRel-coh ; EvalRel-Bot ; CoherentEnv)
open import BCDE4.Model.Guard using (Guard ; guard-out)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.RussellSound D using (fits-addC ; fits-loop)
open import BCDE4.Model.Strip using (strip ; stripCtx)
import BCDE4.Model.Core as C
open import BCDE4.Levels
open import BCDE4.RussellSyntax using (Expr ; U ; Grd ; GLam ; Emp ; Sub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; mkWt ; wtE ; wtT ; subst-HasType ; subst-IsType ; subst-ConvTy ;
  typing-WfCtx ; presup-r-ConvTy ; presup-r-ConvTm)
open import BCDE4.RussellMetaCong using (ConvTmSub ; mkCS ; csE ; csT ; subst-cong-IsType)
open import BCDE4.RussellReduction using (HeadRed ; headred-refl ; headred-step ; headred-grd ; headred-glam)

------------------------------------------------------------------------
-- Substitutions into Γ,ψ when ψ is valid in the target
------------------------------------------------------------------------

private
  ent-addC-valid : {n m : Nat} (G : Ctx n) (H : Ctx m) (c : Constr) ->
    Entails (lctx H) (lctx G) -> ValidC (lctx H) c -> Entails (lctx H) (lctx (addC G c))
  ent-addC-valid G H c e v =
    Eq-transport (\ Y -> Entails (lctx H) Y) (Eq-sym (lctx-addC G c)) (ent-cons c e v)

wt-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g} (c : Constr) ->
  WtSub H G sigma -> ValidC (lctx H) c -> WtSub H (addC G c) sigma
wt-addC {H = H} {G = G} {sigma = sigma} c ws v =
  mkWt (ent-addC-valid G H c (wtE ws) v)
       (\ i -> Eq-transport (\ T -> HasType H (sigma i) (substExpr sigma T))
                 (Eq-sym (lookup-addC G c i)) (wtT ws i))

wcs-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma sigma' : Sub h g} (c : Constr) ->
  ConvTmSub H G sigma sigma' -> ValidC (lctx H) c -> ConvTmSub H (addC G c) sigma sigma'
wcs-addC {H = H} {G = G} {sigma = sigma} {sigma' = sigma'} c cs v =
  mkCS (ent-addC-valid G H c (csE cs) v)
       (\ i -> Eq-transport (\ T -> ConvTm H (sigma i) (sigma' i) (substExpr sigma T))
                 (Eq-sym (lookup-addC G c i)) (csT cs i))

vs-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g} {rho : EnvApprox (lctx H) lidS g}
  (c : Constr) -> ValidSub2 H G sigma rho -> ValidSub2 H (addC G c) sigma rho
vs-addC {H = H} {G = G} {sigma = sigma} {rho = rho} c vs i u cu le a ev fm =
  Eq-transport (\ T -> Val2 H (sigma i) (substExpr sigma T) u a) (Eq-sym (lookup-addC G c i))
    (vs i u cu le a (Eq-transport (\ T -> EvalRel (strip T) rho a) (lookup-addC G c i) ev) fm)

vcs-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma sigma' : Sub h g} {rho : EnvApprox (lctx H) lidS g}
  (c : Constr) -> ValidConvSub2 H G sigma sigma' rho -> ValidConvSub2 H (addC G c) sigma sigma' rho
vcs-addC {H = H} {G = G} {sigma = sigma} {sigma' = sigma'} {rho = rho} c vcs i u cu le a ev fm =
  Eq-transport (\ T -> EqVal2 H (sigma i) (sigma' i) (substExpr sigma T) u a) (Eq-sym (lookup-addC G c i))
    (vcs i u cu le a (Eq-transport (\ T -> EvalRel (strip T) rho a) (lookup-addC G c i) ev) fm)

------------------------------------------------------------------------
-- Head expansion through a valid guard
------------------------------------------------------------------------

hr-grd : {n : Nat} {c : Constr} {A : Expr n} -> HeadRed (Grd c A) A
hr-grd = headred-step headred-grd headred-refl

hr-glam : {n : Nat} {c : Constr} {A t : Expr n} -> HeadRed (GLam c A t) t
hr-glam = headred-step headred-glam headred-refl

ValTy2-grd : {h : Nat} {H : Ctx h} {c : Constr} {A : Expr h} (a : FinEl) -> FinMem a U0 ->
  ValidC (lctx H) c -> IsType H A -> ValTy2 H A a -> ValTy2 H (Grd c A) a
ValTy2-grd a aU v dA vt = ValTy2-headred-expand a hr-grd (conv-Ty-Grd-beta v dA) vt

EqValTy2-grd : {h : Nat} {H : Ctx h} {c : Constr} {A B : Expr h} (a : FinEl) -> FinMem a U0 ->
  ValidC (lctx H) c -> IsType H A -> IsType H B ->
  EqValTy2 H A B a -> EqValTy2 H (Grd c A) (Grd c B) a
EqValTy2-grd a aU v dA dB e =
  EqValTy2-headred-expand a hr-grd hr-grd (conv-Ty-Grd-beta v dA) (conv-Ty-Grd-beta v dB) e

-- the guard dropped on the left only
EqValTy2-grd-l : {h : Nat} {H : Ctx h} {c : Constr} {A : Expr h} (a : FinEl) -> FinMem a U0 ->
  ValidC (lctx H) c -> IsType H A -> ValTy2 H A a -> EqValTy2 H (Grd c A) A a
EqValTy2-grd-l a aU v dA vt =
  EqValTy2-headred-expand a hr-grd headred-refl (conv-Ty-Grd-beta v dA) (conv-Ty-refl dA)
    (ValTy2-to-EqValTy2 a vt)

-- a term under a valid guard, at a guarded type
Val2-glam : {h : Nat} {H : Ctx h} {c : Constr} {A t : Expr h} (u a : FinEl) ->
  FinMem a U0 -> Coherent a ->
  ValidC (lctx H) c -> IsType H A -> HasType H t A -> ValTy2 H A a ->
  Val2 H t A u a -> Val2 H (GLam c A t) (Grd c A) u a
Val2-glam u a aU ca v dA dt vtA val =
  Val2-EqValTy2-fwd u a ca (EqValTy2-sym a ca (EqValTy2-grd-l a aU v dA vtA))
    (Val2-beta-expand u a hr-glam (conv-GLam-beta v dA dt) val)

-- (the two annotations may differ up to conversion)
EqVal2-glam : {h : Nat} {H : Ctx h} {c : Constr} {A A2 t t' : Expr h} (u a : FinEl) ->
  FinMem a U0 -> Coherent a ->
  ValidC (lctx H) c -> IsType H A -> ConvTy H A A2 -> HasType H t A -> HasType H t' A -> ValTy2 H A a ->
  EqVal2 H t t' A u a -> EqVal2 H (GLam c A t) (GLam c A2 t') (Grd c A) u a
EqVal2-glam u a aU ca v dA cA2 dt dt' vtA ev =
  EqVal2-EqValTy2-fwd u a ca (EqValTy2-sym a ca (EqValTy2-grd-l a aU v dA vtA))
    (EqVal2-headred-expand u a hr-glam hr-glam
      (conv-GLam-beta v dA dt)
      (conv-conv (conv-GLam-beta v (presup-r-ConvTy cA2) (ty-conv dt' cA2)) (conv-Ty-sym cA2)) ev)

EqVal2-glam-l : {h : Nat} {H : Ctx h} {c : Constr} {A t : Expr h} (u a : FinEl) ->
  ValidC (lctx H) c -> IsType H A -> HasType H t A ->
  Val2 H t A u a -> EqVal2 H (GLam c A t) t A u a
EqVal2-glam-l u a v dA dt val =
  EqVal2-headred-expand u a hr-glam headred-refl (conv-GLam-beta v dA dt) (conv-refl dt)
    (Val2-to-EqVal2 u a val)

------------------------------------------------------------------------
-- Case analysis on a guarded witness
------------------------------------------------------------------------

private
  -- the witness of a guarded construct is ⊥, or a witness of the body
  -- with the guard valid in the ambient theory
  GCase : {g : Nat} (T : LCtx) (c : Constr) (P : FinEl -> Set) (a : FinEl) -> Set
  GCase T c P a = Either (Eq a Bot) (Pair (ValidC T c) (P a))

------------------------------------------------------------------------
-- [ψ]A is a type
------------------------------------------------------------------------

AdqTy-Grd : {g : Nat} {G : Ctx g} {c : Constr} {A : Expr g} ->
  IsType (addC G c) A -> AdqTy (addC G c) A -> AdqTy G (Grd c A)
AdqTy-Grd {G = G} {c = c} {A = A} dA IH {H = H} sigma rho crho vs fits wt wfH a ev aU =
  cases a (guard-out a ev) aU
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem a U0 -> ValTy2 H (Grd c (substExpr sigma A)) a
    cases .Bot (inl refl) aU = tt
    cases a (inr ve) aU =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          wt' = wt-addC c wt v
      in ValTy2-grd a aU v (subst-IsType wt' wfH dA)
           (IH sigma rho crho (vs-addC {G = G} c vs) (fits-addC {G = G} c fits v0) wt' wfH a (snd ve) aU)

AdqConvTy-Grd : {g : Nat} {G : Ctx g} {c : Constr} {A : Expr g} ->
  IsType (addC G c) A -> AdqConvTy (addC G c) A -> AdqConvTy G (Grd c A)
AdqConvTy-Grd {G = G} {c = c} {A = A} dA IH {H = H} sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a ev aU =
  cases a (guard-out a ev) aU
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem a U0 -> EqValTy2 H (Grd c (substExpr sigma A)) (Grd c (substExpr sigma' A)) a
    cases .Bot (inl refl) aU = tt
    cases a (inr ve) aU =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
          w2   = wt-addC c wt' v
      in EqValTy2-grd a aU v (subst-IsType w1 wfH dA) (subst-IsType w2 wfH dA)
           (IH sigma sigma' rho crho (vs-addC {G = G} c vs) (vs-addC {G = G} c vs') (vcs-addC {G = G} c vcs)
               (fits-addC {G = G} c fits v0) w1 w2 (wcs-addC c wcs v) wfH a (snd ve) aU)

AdqETy-Grd : {g : Nat} {G : Ctx g} {c : Constr} {A B : Expr g} ->
  IsType (addC G c) A -> ConvTy (addC G c) A B -> AdqETy (addC G c) A B -> AdqETy G (Grd c A) (Grd c B)
AdqETy-Grd {G = G} {c = c} {A = A} {B = B} dA dAB IH {H = H} sigma rho crho vs fits wt wfH a ev aU =
  cases a (guard-out a ev) aU
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem a U0 -> EqValTy2 H (Grd c (substExpr sigma A)) (Grd c (substExpr sigma B)) a
    cases .Bot (inl refl) aU = tt
    cases a (inr ve) aU =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
      in EqValTy2-grd a aU v (subst-IsType w1 wfH dA) (subst-IsType w1 wfH (presup-r-ConvTy dAB))
           (IH sigma rho crho (vs-addC {G = G} c vs) (fits-addC {G = G} c fits v0) w1 wfH a (snd ve) aU)

------------------------------------------------------------------------
-- ⟨ψ⟩t : [ψ]A
------------------------------------------------------------------------

private
  unguard : {T : LCtx} {c : Constr} {P : FinEl -> Set} -> P Bot -> (u : FinEl) ->
    Guard (ValidC T c) P u -> P u
  unguard {T} {c} {P} pb u gu = go u (guard-out u gu)
    where
      go : (u : FinEl) -> Either (Eq u Bot) (Pair (ValidC T c) (P u)) -> P u
      go .Bot (inl refl) = pb
      go u (inr ve) = snd ve

Adq-GLam : {g : Nat} {G : Ctx g} {c : Constr} {A t : Expr g} ->
  IsType (addC G c) A -> HasType (addC G c) t A ->
  AdqTy (addC G c) A -> Adq (addC G c) t A -> Adq G (GLam c A t) (Grd c A)
Adq-GLam {G = G} {c = c} {A = A} {t = t} dA dt IHA IHt {H = H} sigma rho crho vs fits wt wfH u hu a evA fm =
  cases a (guard-out a evA) fm
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem u a -> Val2 H (GLam c (substExpr sigma A) (substExpr sigma t)) (Grd c (substExpr sigma A)) u a
    cases .Bot (inl refl) fm = tt
    cases a (inr ve) fm =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
          vs1  = vs-addC {G = G} c vs
          fit1 = fits-addC {G = G} c fits v0
          hu'  = unguard (EvalRel-Bot (strip t) rho) u hu
          aU   = FinMem-a-in-U u a fm
          vtA  = IHA sigma rho crho vs1 fit1 w1 wfH a (snd ve) aU
          val  = IHt sigma rho crho vs1 fit1 w1 wfH u hu' a (snd ve) fm
      in Val2-glam u a aU (EvalRel-coh (strip A) rho a (snd ve)) v
           (subst-IsType w1 wfH dA) (subst-HasType w1 wfH dt) vtA val

AdqConv-GLam : {g : Nat} {G : Ctx g} {c : Constr} {A t : Expr g} ->
  IsType (addC G c) A -> HasType (addC G c) t A ->
  AdqTy (addC G c) A -> AdqConv (addC G c) t A -> AdqConv G (GLam c A t) (Grd c A)
AdqConv-GLam {G = G} {c = c} {A = A} {t = t} dA dt IHA IHt {H = H}
  sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm =
  cases a (guard-out a evA) fm
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem u a ->
      EqVal2 H (GLam c (substExpr sigma A) (substExpr sigma t)) (GLam c (substExpr sigma' A) (substExpr sigma' t))
        (Grd c (substExpr sigma A)) u a
    cases .Bot (inl refl) fm = tt
    cases a (inr ve) fm =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
          w2   = wt-addC c wt' v
          fit1 = fits-addC {G = G} c fits v0
          hu'  = unguard (EvalRel-Bot (strip t) rho) u hu
          aU   = FinMem-a-in-U u a fm
          vtA  = IHA sigma rho crho (vs-addC {G = G} c vs) fit1 w1 wfH a (snd ve) aU
          ev   = IHt sigma sigma' rho crho (vs-addC {G = G} c vs) (vs-addC {G = G} c vs') (vcs-addC {G = G} c vcs) fit1
                   w1 w2 (wcs-addC c wcs v) wfH u hu' a (snd ve) fm
          dt2  = subst-HasType w2 wfH dt
          cA   = subst-cong-IsType (wcs-addC c wcs v) wfH dA
      in EqVal2-glam u a aU (EvalRel-coh (strip A) rho a (snd ve)) v
           (subst-IsType w1 wfH dA) cA (subst-HasType w1 wfH dt)
           (ty-conv dt2 (conv-Ty-sym cA))
           vtA ev

AdqE1-GLam : {g : Nat} {G : Ctx g} {c : Constr} {A t t' : Expr g} ->
  IsType (addC G c) A -> HasType (addC G c) t A -> ConvTm (addC G c) t t' A ->
  AdqTy (addC G c) A -> AdqE1 (addC G c) t t' A -> AdqE1 G (GLam c A t) (GLam c A t') (Grd c A)
AdqE1-GLam {G = G} {c = c} {A = A} {t = t} {t' = t'} dA dt dtt IHA IHt {H = H}
  sigma rho crho vs fits wt wfH u hu a evA fm =
  cases a (guard-out a evA) fm
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem u a ->
      EqVal2 H (GLam c (substExpr sigma A) (substExpr sigma t)) (GLam c (substExpr sigma A) (substExpr sigma t'))
        (Grd c (substExpr sigma A)) u a
    cases .Bot (inl refl) fm = tt
    cases a (inr ve) fm =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
          vs1  = vs-addC {G = G} c vs
          fit1 = fits-addC {G = G} c fits v0
          hu'  = unguard (EvalRel-Bot (strip t) rho) u hu
          aU   = FinMem-a-in-U u a fm
          vtA  = IHA sigma rho crho vs1 fit1 w1 wfH a (snd ve) aU
          ev   = IHt sigma rho crho vs1 fit1 w1 wfH u hu' a (snd ve) fm
      in EqVal2-glam u a aU (EvalRel-coh (strip A) rho a (snd ve)) v
           (subst-IsType w1 wfH dA) (conv-Ty-refl (subst-IsType w1 wfH dA)) (subst-HasType w1 wfH dt)
           (subst-HasType w1 wfH (presup-r-ConvTm dtt)) vtA ev

------------------------------------------------------------------------
-- [ψ]A = A and ⟨ψ⟩t = t when ψ is valid
------------------------------------------------------------------------

AdqETy-Grd-beta : {g : Nat} {G : Ctx g} {c : Constr} {A : Expr g} ->
  ValidC (lctx G) c -> IsType G A -> AdqTy G A -> AdqETy G (Grd c A) A
AdqETy-Grd-beta {G = G} {c = c} {A = A} v0 dA IH {H = H} sigma rho crho vs fits wt wfH a ev aU =
  EqValTy2-grd-l a aU v (subst-IsType wt wfH dA)
    (IH sigma rho crho vs fits wt wfH a (unguard (EvalRel-Bot (strip A) rho) a ev) aU)
  where
    v : ValidC (lctx H) c
    v = validC-ent c (wtE wt) v0

AdqE1-GLam-beta : {g : Nat} {G : Ctx g} {c : Constr} {A t : Expr g} ->
  ValidC (lctx G) c -> IsType G A -> HasType G t A -> Adq G t A -> AdqE1 G (GLam c A t) t A
AdqE1-GLam-beta {G = G} {c = c} {A = A} {t = t} v0 dA dt IH {H = H} sigma rho crho vs fits wt wfH u hu a evA fm =
  EqVal2-glam-l u a v (subst-IsType wt wfH dA) (subst-HasType wt wfH dt)
    (IH sigma rho crho vs fits wt wfH u (unguard (EvalRel-Bot (strip t) rho) u hu) a evA fm)
  where
    v : ValidC (lctx H) c
    v = validC-ent c (wtE wt) v0

------------------------------------------------------------------------
-- guard η:  t = ⟨ψ⟩t : [ψ]A.  At ⊥ nothing to prove; otherwise ψ is
-- valid in the target, and both sides head-reduce/convert to t : A.
------------------------------------------------------------------------

AdqE1-GLam-eta : {g : Nat} {G : Ctx g} {c : Constr} {A t : Expr g} ->
  IsType (addC G c) A -> HasType (addC G c) t A ->
  AdqTy (addC G c) A -> Adq G t (Grd c A) -> AdqE1 G t (GLam c A t) (Grd c A)
AdqE1-GLam-eta {G = G} {c = c} {A = A} {t = t} dA dt' IHA IHt {H = H}
  sigma rho crho vs fits wt wfH u hu a evA fm =
  cases a (guard-out a evA) fm evA
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem u a -> EvalRel (strip (Grd c A)) rho a ->
      EqVal2 H (substExpr sigma t) (GLam c (substExpr sigma A) (substExpr sigma t)) (Grd c (substExpr sigma A)) u a
    cases .Bot (inl refl) fm _ = tt
    cases a (inr ve) fm evA =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          w1   = wt-addC c wt v
          fit1 = fits-addC {G = G} c fits v0
          aU   = FinMem-a-in-U u a fm
          ca   = EvalRel-coh (strip A) rho a (snd ve)
          vtA  = IHA sigma rho crho (vs-addC {G = G} c vs) fit1 w1 wfH a (snd ve) aU
          dA1  = subst-IsType w1 wfH dA
          dt1  = subst-HasType w1 wfH dt'
          eGA  = EqValTy2-grd-l a aU v dA1 vtA
          valG = IHt sigma rho crho vs fits wt wfH u hu a evA fm
          valA = Val2-EqValTy2-fwd u a ca eGA valG
      in EqVal2-EqValTy2-fwd u a ca (EqValTy2-sym a ca eGA)
           (EqVal2-headred-expand u a headred-refl hr-glam (conv-refl dt1) (conv-GLam-beta v dA1 dt1)
             (Val2-to-EqVal2 u a valA))

------------------------------------------------------------------------
-- [ψ]A = [ψ']A and ⟨ψ⟩t = ⟨ψ'⟩t for equivalent ψ, ψ': in the target
-- both guards are valid or neither is
------------------------------------------------------------------------

AdqETy-Grd-equiv : {g : Nat} {G : Ctx g} {c c' : Constr} {A : Expr g} ->
  EquivC (lctx G) c c' -> IsType (addC G c) A -> AdqTy (addC G c) A -> AdqETy G (Grd c A) (Grd c' A)
AdqETy-Grd-equiv {G = G} {c = c} {c' = c'} {A = A} q dA IH {H = H} sigma rho crho vs fits wt wfH a ev aU =
  cases a (guard-out a ev) aU
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem a U0 -> EqValTy2 H (Grd c (substExpr sigma A)) (Grd c' (substExpr sigma A)) a
    cases .Bot (inl refl) aU = tt
    cases a (inr ve) aU =
      let v0  = fst ve
          v   = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          v'  = equivC-valid (equivC-ent (wtE wt) q) v
          w1  = wt-addC c wt v
          dA1 = subst-IsType w1 wfH dA
          vt  = IH sigma rho crho (vs-addC {G = G} c vs) (fits-addC {G = G} c fits v0) w1 wfH a (snd ve) aU
      in EqValTy2-headred-expand a hr-grd hr-grd (conv-Ty-Grd-beta v dA1) (conv-Ty-Grd-beta v' dA1)
           (ValTy2-to-EqValTy2 a vt)

-- (the annotation may change along, to a convertible one: this also
-- covers conv-cong-GLam-Ty, with ψ' = ψ)
AdqE1-GLam-equiv : {g : Nat} {G : Ctx g} {c c' : Constr} {A A' t : Expr g} ->
  EquivC (lctx G) c c' -> IsType (addC G c) A -> ConvTy (addC G c) A A' -> HasType (addC G c) t A ->
  AdqTy (addC G c) A -> Adq (addC G c) t A -> AdqE1 G (GLam c A t) (GLam c' A' t) (Grd c A)
AdqE1-GLam-equiv {G = G} {c = c} {c' = c'} {A = A} {A' = A'} {t = t} q dA cAA' dt IHA IHt {H = H}
  sigma rho crho vs fits wt wfH u hu a evA fm =
  cases a (guard-out a evA) fm
  where
    cases : (a : FinEl) -> Either (Eq a Bot) (Pair (ValidC (lctx H) (lsubC lidS c)) (EvalRel (strip A) rho a)) ->
      FinMem u a ->
      EqVal2 H (GLam c (substExpr sigma A) (substExpr sigma t)) (GLam c' (substExpr sigma A') (substExpr sigma t))
        (Grd c (substExpr sigma A)) u a
    cases .Bot (inl refl) fm = tt
    cases a (inr ve) fm =
      let v0   = fst ve
          v    = Eq-transport (ValidC (lctx H)) (lsubC-id c) v0
          v'   = equivC-valid (equivC-ent (wtE wt) q) v
          w1   = wt-addC c wt v
          vs1  = vs-addC {G = G} c vs
          fit1 = fits-addC {G = G} c fits v0
          hu'  = unguard (EvalRel-Bot (strip t) rho) u hu
          aU   = FinMem-a-in-U u a fm
          ca   = EvalRel-coh (strip A) rho a (snd ve)
          vtA  = IHA sigma rho crho vs1 fit1 w1 wfH a (snd ve) aU
          val  = IHt sigma rho crho vs1 fit1 w1 wfH u hu' a (snd ve) fm
          dA1  = subst-IsType w1 wfH dA
          dt1  = subst-HasType w1 wfH dt
          cA1  = subst-ConvTy w1 wfH cAA'
      in EqVal2-EqValTy2-fwd u a ca (EqValTy2-sym a ca (EqValTy2-grd-l a aU v dA1 vtA))
           (EqVal2-headred-expand u a hr-glam hr-glam (conv-GLam-beta v dA1 dt1)
             (conv-conv (conv-GLam-beta v' (presup-r-ConvTy cA1) (ty-conv dt1 cA1)) (conv-Ty-sym cA1))
             (Val2-to-EqVal2 u a val))

------------------------------------------------------------------------
-- ∅ and the collapse rules
------------------------------------------------------------------------

AdqTy-Emp : {g : Nat} {G : Ctx g} -> AdqTy G Emp
AdqTy-Emp sigma rho crho vs fits wt wfH Bot          ev aU = tt
AdqTy-Emp sigma rho crho vs fits wt wfH (UCode k)    (mkSigma _ ()) aU
AdqTy-Emp sigma rho crho vs fits wt wfH (FunEl g)    (mkSigma _ ()) aU
AdqTy-Emp sigma rho crho vs fits wt wfH (PiCode b f) (mkSigma _ ()) aU

AdqConvTy-Emp : {g : Nat} {G : Ctx g} -> AdqConvTy G Emp
AdqConvTy-Emp sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH Bot          ev aU = tt
AdqConvTy-Emp sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (UCode k)    (mkSigma _ ()) aU
AdqConvTy-Emp sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl g)    (mkSigma _ ()) aU
AdqConvTy-Emp sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (PiCode b f) (mkSigma _ ()) aU

Adq-collapse : {g : Nat} {G : Ctx g} {M A : Expr g} -> Loop (lctx G) -> Adq G M A
Adq-collapse {G = G} lp sigma rho crho vs fits wt wfH u hu a evA fm = fits-loop {G = G} fits lp

AdqConv-collapse : {g : Nat} {G : Ctx g} {M A : Expr g} -> Loop (lctx G) -> AdqConv G M A
AdqConv-collapse {G = G} lp sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm =
  fits-loop {G = G} fits lp

AdqETy-collapse : {g : Nat} {G : Ctx g} {A B : Expr g} -> Loop (lctx G) -> AdqETy G A B
AdqETy-collapse {G = G} lp sigma rho crho vs fits wt wfH a ev aU = fits-loop {G = G} fits lp

AdqE1-collapse : {g : Nat} {G : Ctx g} {M N A : Expr g} -> Loop (lctx G) -> AdqE1 G M N A
AdqE1-collapse {G = G} lp sigma rho crho vs fits wt wfH u hu a evA fm = fits-loop {G = G} fits lp
