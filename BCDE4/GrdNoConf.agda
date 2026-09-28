{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.GrdNoConf
--
-- Injectivity and no-confusion for constraint products [ψ]A, the
-- inputs of the T_P side (analogues of Sterbac 4.18/4.19).
--
-- Because of guard β ([ψ]A = A when ψ is valid, bcde.pdf Fig. 13) the
-- naive statements are FALSE:
--   * [ψ]A = [ψ']A'  does NOT give  ψ ⇔ ψ':   with ψ valid,
--     [ψ][ψ']B = [ψ']B  (Grd-beta) for any ψ';
--   * [ψ]A is NOT distinct from U / Π / [α]:  [ψ]U_l = U_l for ψ valid.
-- The correct forms, proved here:
--   grd-inj    : Γ ⊢ [ψ]A = [ψ']A'  ->  Γ,ψ,ψ' ⊢ A = A'
--                (purely syntactic: weaken the constraints, then Grd-beta);
--   grd-valid-*: Γ loop-free,  Γ ⊢ X = [ψ]A  with X a universe, a product
--                or a level product  ->  ψ valid in Γ
--                (soundness of the model at the bottom environment: [ψ]A
--                 denotes {⊥} when ψ is not valid, X has a non-⊥ element).
-- Also the no-confusion of U / Π / [α] among themselves (same method).
--
-- No postulates, no pragmas.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.GrdNoConf (D : LDecAll) where

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; PiCode ; LPiCode ; nil)
open import BCDE4.Levels
open import BCDE4.Basic using (absurd ; Eq-trans ; Eq-transport)
open import BCDE4.Model.Eval D using (EvalRel ; lcodeT)
open import BCDE4.Model.EvalSubstitution D using (botEnv)
open import BCDE4.Model.RussellSound D using (sound-CTy)
open import BCDE4.Model.Strip using (strip ; stripCtx)
import BCDE4.Model.Core as C
open import BCDE4.RussellSyntax using (Expr ; Pi ; LPi ; U ; Grd)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (presup-l-ConvTy ; presup-r-ConvTy ; isType-WfCtx)
open import BCDE4.RussellRelevel using (wkC-ConvTy ; wkC-IsType)
open import BCDE4.PiInjectivityR D using (botEnv-fits ; evalRel-Pi-bot ; evalRel-LPi-bot)

------------------------------------------------------------------------
-- Inversion: a constraint product is a type only by is-Grd
------------------------------------------------------------------------

hasType-Grd-absurd : {n : Nat} {G : Ctx n} {c : Constr} {A T : Expr n} ->
  HasType G (Grd c A) T -> Empty
hasType-Grd-absurd (ty-conv d _)  = hasType-Grd-absurd d
hasType-Grd-absurd (ty-cum d _)   = hasType-Grd-absurd d

inv-IsType-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n} ->
  IsType G (Grd c A) -> IsType (addC G c) A
inv-IsType-Grd (is-Ty-from-U d) = absurd (hasType-Grd-absurd d)
inv-IsType-Grd (is-Grd _ dA)   = dA

------------------------------------------------------------------------
-- [ψ]-injectivity (syntactic)
------------------------------------------------------------------------

private
  valid-top : {Th : LCtx} (c : Constr) -> ValidC (lcons c Th) c
  valid-top (ceq l m) = v-hyp lhere

  valid-snd : {Th : LCtx} (c c' : Constr) -> ValidC (lcons c' (lcons c Th)) c
  valid-snd (ceq l m) c' = v-hyp (lthere lhere)

  lctx2 : {n : Nat} (G : Ctx n) (c c' : Constr) ->
    Eq (lctx (addC (addC G c) c')) (lcons c' (lcons c (lctx G)))
  lctx2 G c c' = Eq-trans (lctx-addC (addC G c) c') (S.Eq-cong (lcons c') (lctx-addC G c))

  -- ψ is valid in Γ,ψ,ψ' and ψ' is valid in Γ,ψ,ψ'
  v1 : {n : Nat} (G : Ctx n) (c c' : Constr) -> ValidC (lctx (addC (addC G c) c')) c
  v1 G c c' = Eq-transport (\ T -> ValidC T c) (S.Eq-sym (lctx2 G c c')) (valid-snd c c')

  v2 : {n : Nat} (G : Ctx n) (c c' : Constr) -> ValidC (lctx (addC (addC G c) c')) c'
  v2 G c c' = Eq-transport (\ T -> ValidC T c') (S.Eq-sym (lctx2 G c c')) (valid-top c')

open import BCDE4.RussellRelevel using (relev-IsType ; skel-addC ; skel-self ; ent-addC ; ent-self)

grd-inj : {n : Nat} {G : Ctx n} {c c' : Constr} {A A' : Expr n} ->
  ConvTy G (Grd c A) (Grd c' A') -> ConvTy (addC (addC G c) c') A A'
grd-inj {G = G} {c} {c'} {A} {A'} d =
  let dA   = wkC-IsType c' (inv-IsType-Grd (presup-l-ConvTy d))
      dA'  = relev-IsType (skel-addC c' (skel-self G c)) (ent-addC G (addC G c) c' (ent-self G c))
               (inv-IsType-Grd (presup-r-ConvTy d))
      d2   = wkC-ConvTy c' (wkC-ConvTy c d)
  in conv-Ty-trans (conv-Ty-sym (conv-Ty-Grd-beta (v1 G c c') dA))
       (conv-Ty-trans d2 (conv-Ty-Grd-beta (v2 G c c') dA'))

-- same guard: Γ ⊢ [ψ]A = [ψ]A'  ->  Γ,ψ ⊢ A = A'
grd-inj1 : {n : Nat} {G : Ctx n} {c : Constr} {A A' : Expr n} ->
  ConvTy G (Grd c A) (Grd c A') -> ConvTy (addC G c) A A'
grd-inj1 {G = G} {c} {A} {A'} d =
  let v  = Eq-transport (\ T -> ValidC T c) (S.Eq-sym (lctx-addC G c)) (valid-top c)
      dA  = inv-IsType-Grd (presup-l-ConvTy d)
      dA' = inv-IsType-Grd (presup-r-ConvTy d)
  in conv-Ty-trans (conv-Ty-sym (conv-Ty-Grd-beta v dA))
       (conv-Ty-trans (wkC-ConvTy c d) (conv-Ty-Grd-beta v dA'))

------------------------------------------------------------------------
-- The model: X = Y and a non-⊥ element of X at the bottom environment
------------------------------------------------------------------------

transfer : {n : Nat} {G : Ctx n} {X Y : Expr n} -> LoopFree (lctx G) -> ConvTy G X Y ->
  (b : FinEl) -> EvalRel {T = lctx G} {θ = lidS} (strip X) botEnv b ->
  EvalRel {T = lctx G} {θ = lidS} (strip Y) botEnv b
transfer {G = G} lf d b ev = fst (snd (snd (sound-CTy d botEnv (botEnv-fits G lf)))) b ev

fromLid : {Th : LCtx} (c : Constr) -> ValidC Th (lsubC lidS c) -> ValidC Th c
fromLid {Th} c v = Eq-transport (ValidC Th) (lsubC-id c) v

grd-valid-Pi : {n : Nat} {G : Ctx n} {c : Constr} {A C0 : Expr n} {B0 : Expr (suc n)} ->
  LoopFree (lctx G) -> ConvTy G (Pi C0 B0) (Grd c A) -> ValidC (lctx G) c
grd-valid-Pi {G = G} {c} {A} {C0} {B0} lf d =
  fromLid c (fst (transfer lf d (PiCode Bot nil) (evalRel-Pi-bot (strip C0) (strip B0) botEnv)))

grd-valid-LPi : {n : Nat} {G : Ctx n} {c : Constr} {A A0 : Expr n} ->
  LoopFree (lctx G) -> ConvTy G (LPi A0) (Grd c A) -> ValidC (lctx G) c
grd-valid-LPi {G = G} {c} {A} {A0} lf d =
  fromLid c (fst (transfer lf d (LPiCode nil) (evalRel-LPi-bot (strip A0) botEnv)))

grd-valid-U : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n} {l : LExpr} ->
  LoopFree (lctx G) -> ConvTy G (U l) (Grd c A) -> ValidC (lctx G) c
grd-valid-U {G = G} {c} {A} {l} lf d =
  let k = lcodeT (lctx G) (lsubL lidS l)
  in fromLid c (fst (transfer lf d (UCode k) (mkSigma tt (S.EqL-refl k))))

------------------------------------------------------------------------
-- U / Π / [α] no-confusion
------------------------------------------------------------------------

noconf-Pi-U : {n : Nat} {G : Ctx n} {C0 : Expr n} {B0 : Expr (suc n)} {l : LExpr} ->
  LoopFree (lctx G) -> ConvTy G (Pi C0 B0) (U l) -> Empty
noconf-Pi-U {C0 = C0} {B0} lf d with transfer lf d (PiCode Bot nil) (evalRel-Pi-bot (strip C0) (strip B0) botEnv)
... | mkSigma _ ()

noconf-LPi-U : {n : Nat} {G : Ctx n} {A0 : Expr n} {l : LExpr} ->
  LoopFree (lctx G) -> ConvTy G (LPi A0) (U l) -> Empty
noconf-LPi-U {A0 = A0} lf d with transfer lf d (LPiCode nil) (evalRel-LPi-bot (strip A0) botEnv)
... | mkSigma _ ()

noconf-Pi-LPi : {n : Nat} {G : Ctx n} {C0 A0 : Expr n} {B0 : Expr (suc n)} ->
  LoopFree (lctx G) -> ConvTy G (Pi C0 B0) (LPi A0) -> Empty
noconf-Pi-LPi {C0 = C0} {B0 = B0} lf d with transfer lf d (PiCode Bot nil) (evalRel-Pi-bot (strip C0) (strip B0) botEnv)
... | ()
