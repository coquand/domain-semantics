{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LeqTest
--
-- Universes and invariance under level equality, on closed examples:
--
--   α = β, x : [γ]U_γ  ⊢  x α = x β : U_α
--   α = β              ⊢  U_α = U_β : U_α⁺
--   ⊢  U_α : U_α⁺⁺                              (cumulativity)
--   ⊢  [α = β]U_α = [β = α]U_α                  (as types)
--
-- and the fundamental theorem applies to them (conv-adequacy).
------------------------------------------------------------------------

module BCDE4.LeqTest where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (wkL-WfCtx ; isType-U ; lt-next)
open import BCDE4.RussellLeq using (mk-conv-cong-LApp-lvl)
import BCDE4.Main as Main
import BCDE4.Adeq.Stmt

private
  α β : LExpr
  α = lvar 0
  β = lvar 1

  Th : LCtx
  Th = lcons (ceq α β) lnil

  dLPiU : IsType (empty Th) (LPi (U (lvar 0)))
  dLPiU = is-LPi wf-empty (isType-U (wkL-WfCtx wf-empty))

  G : Ctx (suc zero)
  G = extend (empty Th) (LPi (U (lvar 0)))

  wfG : WfCtx G
  wfG = wf-extend dLPiU

-- x α = x β
lapp-lvl : ConvTm G (LApp (U (lvar 0)) (Var fzero) α) (LApp (U (lvar 0)) (Var fzero) β) (U α)
lapp-lvl = mk-conv-cong-LApp-lvl (isType-U (wkL-WfCtx wfG)) (ty-var wfG) (v-hyp lhere)

-- U_α = U_β
u-lvl : ConvTm (empty Th) (U α) (U β) (U (lnext α))
u-lvl = conv-U-lvl wf-empty (v-hyp lhere) (lt-next α)

-- U_α : U_α⁺⁺
u-cum : HasType (empty lnil) (U α) (U (lnext (lnext α)))
u-cum = ty-cum (ty-U wf-empty (lt-next α)) v-infl

-- [α = β]U_α = [β = α]U_α
grd-sym : ConvTy (empty lnil) (Grd (ceq α β) (U α)) (Grd (ceq β α) (U α))
grd-sym = conv-Ty-Grd-equiv wf-empty (mkSigma (v-sym (v-hyp lhere)) (v-sym (v-hyp lhere)))
            (isType-U wf-empty)

lapp-lvl-adequate : BCDE4.Adeq.Stmt.AdqE1 _ G (LApp (U (lvar 0)) (Var fzero) α) (LApp (U (lvar 0)) (Var fzero) β) (U α)
lapp-lvl-adequate = Main.conv-adequacy lapp-lvl

u-lvl-adequate : BCDE4.Adeq.Stmt.AdqE1 _ (empty Th) (U α) (U β) (U (lnext α))
u-lvl-adequate = Main.conv-adequacy u-lvl
