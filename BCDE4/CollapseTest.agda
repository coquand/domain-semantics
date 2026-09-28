{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- BCDE4.CollapseTest
--
-- The equation that makes a level-ERASING model unsound: in the empty,
-- loop-free context,
--
--      [α⁺ ≤ α] (U_α → U_α)  ≡  [α⁺ ≤ α] U_α
--
-- is derivable (under the guard the context has a loop, so both bodies
-- collapse to ∅).  An interpretation with ⟦[ψ]A⟧ = ⟦A⟧ would identify
-- the codes Π and U.  The guard-aware model interprets both sides by ⊥
-- (the guard is not valid in the ambient theory), and Π-injectivity
-- still holds in loop-free contexts (BCDE4.PiInjectivityR).
------------------------------------------------------------------------

module BCDE4.CollapseTest where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (isType-U ; isType-Pi)
open import BCDE4.RussellRelevel using (wkC-WfCtx)

α : LExpr
α = lvar 0

-- α⁺ ≤ α, i.e. α⁺ ∨ α = α : a loop
ψ : Constr
ψ = ceq (lsup (lnext α) α) α

G0 : Ctx 0
G0 = empty lnil

wf0 : WfCtx G0
wf0 = wf-empty

loop : Loop (lctx (addC G0 ψ))
loop = mkSigma α (v-hyp lhere)

UU : Expr 0
UU = Pi (U α) (U α)

dUU : IsType (addC G0 ψ) UU
dUU = isType-Pi (isType-U wfψ) (isType-U (wf-extend (isType-U wfψ)))
  where wfψ = wkC-WfCtx ψ wf0

collapse-example : ConvTy G0 (Grd ψ UU) (Grd ψ (U α))
collapse-example =
  conv-Ty-Grd wf0 dUU
    (conv-Ty-trans (conv-Ty-collapse loop dUU)
                   (conv-Ty-sym (conv-Ty-collapse loop (isType-U (wkC-WfCtx ψ wf0)))))

-- the ambient context is loop-free (it has a model in ℕ), so Π-injectivity
-- (BCDE4.PiInjectivityR.PiInj-R) applies to it
G0-loopFree : LoopFree (lctx G0)
G0-loopFree = loopFree-nil
