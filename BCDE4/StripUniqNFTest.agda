{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.StripUniqNFTest
--
-- Sterbac's counterexample to the proof of Lemma 4.17 (Gap417), with
-- levels (α := v0, α⁺, α⁺⁺ in place of 0, 1, 2):
--
--   u0 = app(U_α⁺, U_α⁺ , λ(U_α⁺, U_α⁺ , v0), U_α) : U_α⁺ ≤ U_α⁺⁺
--   u1 = app(U_α⁺, U_α⁺⁺, λ(U_α⁺, U_α⁺⁺, v0), U_α) : U_α⁺⁺
--
-- settled by the normalisation-free Lemma 4.18, also under a constraint
-- binder ⟨ψ⟩ (ψ arbitrary, possibly invalid) and under a level binder ⟨β⟩.
------------------------------------------------------------------------

module BCDE4.StripUniqNFTest where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (isType-U ; lt-next)
open import BCDE4.StripUniqNF

a : LExpr
a = lvar zero

U0 U1 U2 : {n : Nat} -> Expr n
U0 = U a
U1 = U (lnext a)
U2 = U (lnext (lnext a))

f0 f1 u0 u1 : Expr zero
f0 = Lam U1 U1 (Var fzero)
f1 = Lam U1 U2 (Var fzero)
u0 = App U1 U1 f0 U0
u1 = App U1 U2 f1 U0

module _ (Th : LCtx) where

  G : Ctx zero
  G = empty Th

  wf0 : WfCtx G
  wf0 = wf-empty

  wf1 : WfCtx (extend G U1)
  wf1 = wf-extend (isType-U wf0)

  le12 : LeL Th (lnext a) (lnext (lnext a))
  le12 = ltL-leL' (lt-next (lnext a))

  du0 : HasType G u0 U2
  du0 = ty-cum (ty-App (isType-U wf0) (isType-U wf1)
                  (ty-Lam (isType-U wf0) (isType-U wf1) (ty-var wf1)) (ty-U wf0 (lt-next a))) le12

  du1 : HasType G u1 U2
  du1 = ty-App (isType-U wf0) (isType-U wf1)
          (ty-Lam (isType-U wf0) (isType-U wf1) (ty-cum (ty-var wf1) le12)) (ty-U wf0 (lt-next a))

  gap-closed : ConvTm G u0 u1 U2
  gap-closed = term-uniq-conv-NF du0 du1 refl (conv-Ty-refl (isType-U wf0))

-- under a constraint binder: ⟨ψ⟩u0 = ⟨ψ⟩u1 : [ψ]U_α⁺⁺, for any ψ
under-guard : (Th : LCtx) (c : Constr) -> ConvTm (empty Th) (GLam c U2 u0) (GLam c U2 u1) (Grd c U2)
under-guard Th c =
  let G' = empty (lcons c Th)
  in term-uniq-conv-NF (ty-GLam wf-empty (isType-U wf-empty) (du0 (lcons c Th)))
       (ty-GLam wf-empty (isType-U wf-empty) (du1 (lcons c Th))) refl
       (conv-Ty-refl (is-Grd wf-empty (isType-U wf-empty)))

-- under a level binder: ⟨β⟩u0 = ⟨β⟩u1 : [β]U_β⁺⁺
under-level : (Th : LCtx) -> ConvTm (empty Th) (LLam U2 u0) (LLam U2 u1) (LPi U2)
under-level Th =
  term-uniq-conv-NF (ty-LLam wf-empty (isType-U wf-empty) (du0 (lsubTh lwkS Th)))
    (ty-LLam wf-empty (isType-U wf-empty) (du1 (lsubTh lwkS Th))) refl
    (conv-Ty-refl (is-LPi wf-empty (isType-U wf-empty)))
