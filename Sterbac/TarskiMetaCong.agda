{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.TarskiMetaCong
--
-- Cross-substitution congruence for the Tarski theory:
--
--   subst1-cong-Ty : ConvTm G a a' A
--                 -> IsType G A
--                 -> IsType (extend G A) B
--                 -> ConvTy G (subst1 B a) (subst1 B a')
--
-- Provides the missing premise for `conv-cong-App-arg` when the
-- ConvTm-witness for `a ≡ a'` is given but the cross-substitution
-- equality of the result type is not.
--
-- Strategy: parameterise by a pointwise convertibility witness
--
--   ConvTmSub H G s s' = (i : Fin g) ->
--                          ConvTm H (s i) (s' i) (substExpr s (lookup G i))
--
-- and prove the standard mutual `subst-cong-{IsType,HasType,ConvTy,ConvTm}`
-- lemmas.  Specialise at the end with s = subst1Sub a, s' = subst1Sub a'.
------------------------------------------------------------------------

module Sterbac.TarskiMetaCong where

open import Sterbac.Basic
open import Sterbac.TarskiSyntax
open import Sterbac.TarskiTyping
open import Sterbac.TarskiMeta

------------------------------------------------------------------------
-- Pointwise-convertibility substitution
------------------------------------------------------------------------

ConvTmSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> Set
ConvTmSub H G s s' =
  (i : Fin _) -> ConvTm H (s i) (s' i) (substExpr s (lookup G i))

-- Project the "left" WtSub from a ConvTmSub.  Inlined at call sites
-- as `(\ i -> presup-l-ConvTm (cs i))` to avoid implicit-G inference issues.

------------------------------------------------------------------------
-- Lifting a ConvTmSub through a binder
------------------------------------------------------------------------

liftSub-ConvTmSub :
  {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {A : Expr g}
  -> ConvTmSub H G s s' -> WfCtx H -> IsType G A
  -> ConvTmSub (extend H (substExpr s A)) (extend G A) (liftSub s) (liftSub s')
liftSub-ConvTmSub {s = s} {A = A} cs wfH dA fzero =
  let sA-IT  = subst-IsType (\ i -> presup-l-ConvTm (cs i)) wfH dA
      wfH'   = wf-extend sA-IT
      eq     = Eq-trans (subst-ren (liftSub s) wkRen A)
                 (Eq-sym (ren-subst wkRen s A))
  in Eq-transport
       (\ T -> ConvTm (extend _ (substExpr s A))
                      (Var fzero) (Var fzero) T)
       (Eq-sym eq)
       (conv-refl (ty-var wfH'))
liftSub-ConvTmSub {H = H} {G = G} {s = s} {s' = s'} {A = A} cs wfH dA (fsuc i) =
  let sA-IT = subst-IsType (\ i -> presup-l-ConvTm (cs i)) wfH dA
      ih    = cs i
      ih-wk = wk-ConvTm sA-IT ih
      eq    = Eq-trans (subst-ren (liftSub s) wkRen (lookup G i))
                       (Eq-sym (ren-subst wkRen s (lookup G i)))
  in Eq-transport
       (\ T -> ConvTm (extend H (substExpr s A))
                      (wkExpr (s i)) (wkExpr (s' i)) T)
       (Eq-sym eq)
       ih-wk

------------------------------------------------------------------------
-- The mutual congruence block
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  ----------------------------------------------------------------------
  -- IsType cases
  ----------------------------------------------------------------------
  subst-cong-IsType :
    {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {A : Expr g}
    -> ConvTmSub H G s s' -> WfCtx H
    -> IsType G A
    -> ConvTy H (substExpr s A) (substExpr s' A)
  subst-cong-IsType cs wfH (is-Ty-U {l = l} _) =
    conv-Ty-refl (is-Ty-U {l = l} wfH)
  subst-cong-IsType cs wfH (is-Ty-Pi dA dB) =
    let cA   = subst-cong-IsType cs wfH dA
        sA-IT = subst-IsType (\ i -> presup-l-ConvTm (cs i)) wfH dA
        wfH'  = wf-extend sA-IT
        cs'   = liftSub-ConvTmSub cs wfH dA
    in conv-Ty-Pi cA (subst-cong-IsType cs' wfH' dB)
  subst-cong-IsType cs wfH (is-Ty-El {l = l} da) =
    conv-Ty-El {l = l} (subst-cong-HasType cs wfH da)

  ----------------------------------------------------------------------
  -- HasType cases (produce ConvTm at substExpr s A)
  ----------------------------------------------------------------------
  subst-cong-HasType :
    {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {M A : Expr g}
    -> ConvTmSub H G s s' -> WfCtx H
    -> HasType G M A
    -> ConvTm H (substExpr s M) (substExpr s' M) (substExpr s A)
  subst-cong-HasType cs wfH (ty-var {i = i} _) = cs i
  subst-cong-HasType cs wfH (ty-conv dM dAB) =
    conv-conv (subst-cong-HasType cs wfH dM)
              (subst-ConvTy (\ i -> presup-l-ConvTm (cs i)) wfH dAB)
  subst-cong-HasType cs wfH (ty-Lam dA dB db) =
    let sA-IT = subst-IsType (\ i -> presup-l-ConvTm (cs i)) wfH dA
        wfH'  = wf-extend sA-IT
        cs'   = liftSub-ConvTmSub cs wfH dA
        cA    = subst-cong-IsType cs wfH dA
        cB    = subst-cong-IsType cs' wfH' dB
        cb    = subst-cong-HasType cs' wfH' db
        sB    = subst-IsType (liftSub-WtSub (\ i -> presup-l-ConvTm (cs i)) wfH dA) wfH' dB
        sb-r  = presup-r-ConvTm cb
        step1 = conv-cong-Lam-body sA-IT sB cb
        step2 = conv-cong-Lam-Ty cA cB sb-r
    in conv-trans step1 step2
  subst-cong-HasType {H = H} {s = s} {s' = s'} cs wfH
                     (ty-App {A = A} {B = B} {c = c} {a = a}
                              dA dB dc da) =
    let sA-IT = subst-IsType (\ i -> presup-l-ConvTm (cs i)) wfH dA
        wfH'  = wf-extend sA-IT
        cs'   = liftSub-ConvTmSub cs wfH dA
        cA    = subst-cong-IsType cs wfH dA
        cB    = subst-cong-IsType cs' wfH' dB
        cc    = subst-cong-HasType cs wfH dc
        ca    = subst-cong-HasType cs wfH da
        sB    = subst-IsType (liftSub-WtSub (\ i -> presup-l-ConvTm (cs i)) wfH dA) wfH' dB
        sa-l  = subst-HasType (\ i -> presup-l-ConvTm (cs i)) wfH da
        sc-r  = presup-r-ConvTm cc        -- HasType H (s' c) (Pi sA sB)
        sa-r  = presup-r-ConvTm ca        -- HasType H (s' a) sA
        step1 = conv-cong-App-fun sA-IT sB cc sa-l
        BsubstCong = subst-cong-IsType (innerCS ca) wfH sB
        step2 = conv-cong-App-arg sA-IT sB sc-r ca BsubstCong
        step3raw = conv-cong-App-Ty cA cB sc-r sa-r
        step3  = conv-conv step3raw (conv-Ty-sym BsubstCong)
        composite = conv-trans step1 (conv-trans step2 step3)
        appL = App (substExpr s A) (substExpr (liftSub s) B)
                   (substExpr s c) (substExpr s a)
        appR = App (substExpr s' A) (substExpr (liftSub s') B)
                   (substExpr s' c) (substExpr s' a)
    in Eq-transport (\ T -> ConvTm H appL appR T)
         (Eq-sym (subst-subst1 s B a))
         composite
    where
      innerCS : ConvTm H (substExpr s a) (substExpr s' a) (substExpr s A)
              -> ConvTmSub H (extend H (substExpr s A))
                            (subst1Sub (substExpr s a))
                            (subst1Sub (substExpr s' a))
      innerCS ca fzero    =
        Eq-transport (\ T -> ConvTm H (substExpr s a) (substExpr s' a) T)
          (Eq-sym (subst1-wk (substExpr s A) (substExpr s a)))
          ca
      innerCS ca (fsuc i) =
        Eq-transport (\ T -> ConvTm H (Var i) (Var i) T)
          (Eq-sym (subst1-wk _ (substExpr s a)))
          (conv-refl (ty-var wfH))
  subst-cong-HasType cs wfH (ty-PiCode {l = l} da db) =
    let ca    = subst-cong-HasType cs wfH da
        sa    = subst-HasType (\ i -> presup-l-ConvTm (cs i)) wfH da
        sa-IT = is-Ty-El {l = l} sa
        wfH'  = wf-extend sa-IT
        cs'   = liftSub-ConvTmSub cs wfH (is-Ty-El {l = l} da)
        cb    = subst-cong-HasType cs' wfH' db
    in conv-cong-PiCode {l = l} ca cb
  subst-cong-HasType cs wfH (ty-UCode {m = m} {l = l} _ h) =
    conv-refl (ty-UCode {m = m} {l = l} wfH h)
  subst-cong-HasType cs wfH (ty-Lift {m = m} {l = l} h da) =
    conv-cong-Lift {m = m} {l = l} h (subst-cong-HasType cs wfH da)

------------------------------------------------------------------------
-- The wrapper we actually need
------------------------------------------------------------------------

subst1-cong-Ty :
  {n : Nat} {G : Ctx n} {a a' : Expr n} {A : Expr n} {B : Expr (suc n)}
  -> ConvTm G a a' A
  -> IsType G A
  -> IsType (extend G A) B
  -> ConvTy G (subst1 B a) (subst1 B a')
subst1-cong-Ty {G = G} {a = a} {a' = a'} {A = A} {B = B} caa' dA dB =
  subst-cong-IsType (cs caa') (isType-WfCtx dA) dB
  where
    dG : WfCtx G
    dG = isType-WfCtx dA
    cs : ConvTm G a a' A
       -> ConvTmSub G (extend G A) (subst1Sub a) (subst1Sub a')
    cs caa'' fzero    =
      Eq-transport (\ T -> ConvTm G a a' T)
        (Eq-sym (subst1-wk A a))
        caa''
    cs caa'' (fsuc i) =
      Eq-transport (\ T -> ConvTm G (Var i) (Var i) T)
        (Eq-sym (subst1-wk (lookup G i) a))
        (conv-refl (ty-var dG))
