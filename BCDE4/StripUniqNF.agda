{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.StripUniqNF
--
-- Lemma 4.18 (redundancy of the annotations of T_R) for BCDE, WITHOUT
-- normalisation (ERT.StripUniqNF extended to levels, guards and
-- level products): a structural induction on the term.
--
-- Main lemma (main): if Γ ⊢ u0 : T0, Γ ⊢ u1 : T1 and strip u0 = strip u1,
-- then there is a Join G T0 T1 L k0 k1 with Γ ⊢ coe k0 u0 = coe k1 u1 : L
-- (BCDE4.Coerce).  Types (which may be large: Π of types, [α]A, [ψ]A)
-- are handled by tyMain.  Every call decides loops first: in a loopy
-- context everything is ∅ (collapse).
--
-- Non-syntactic inputs: Π-, [α]-, U-injectivity (BCDE4.Main), the
-- no-confusion of U / Π / [α] and the validity of a guard convertible to
-- one of them (BCDE4.GrdNoConf), all from the domain model, in loop-free
-- contexts; and guard η (conv-GLam-eta) for the diagonal.
------------------------------------------------------------------------

module BCDE4.StripUniqNF where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.RussellMetaCong using (subst1-cong-Ty)
open import BCDE4.RussellLsub using (lsub-ConvTy ; lsk-inst ; lok-inst)
open import BCDE4.RussellInversion
open import BCDE4.Coerce
open import BCDE4.JoinProps
open import BCDE4.Main using (PiInj ; LPiInj)
open import BCDE4.LC.Decide using (ldecAll)
open import BCDE4.GrdNoConf ldecAll using (grd-valid-Pi ; grd-valid-LPi ; noconf-Pi-U ; noconf-LPi-U ; noconf-Pi-LPi ;
  inv-IsType-Grd)
open import BCDE4.LC.Loop using (decLoop)
open import BCDE4.Model.Strip using (strip)
import BCDE4.Model.Core as C

------------------------------------------------------------------------
-- Injectivity of the core constructors
------------------------------------------------------------------------

private
  C-Pi-inj : {n : Nat} {A A' : C.Expr n} {B B' : C.Expr (suc n)} -> Eq (C.Pi A B) (C.Pi A' B') -> Pair (Eq A A') (Eq B B')
  C-Pi-inj refl = mkSigma refl refl

  C-Lam-inj : {n : Nat} {A A' : C.Expr n} {b b' : C.Expr (suc n)} -> Eq (C.Lam A b) (C.Lam A' b') -> Pair (Eq A A') (Eq b b')
  C-Lam-inj refl = mkSigma refl refl

  C-App-inj : {n : Nat} {c c' a a' : C.Expr n} -> Eq (C.App c a) (C.App c' a') -> Pair (Eq c c') (Eq a a')
  C-App-inj refl = mkSigma refl refl

  C-GLam-inj : {n : Nat} {c c' : Constr} {t t' : C.Expr n} -> Eq (C.GLam c t) (C.GLam c' t') -> Pair (Eq c c') (Eq t t')
  C-GLam-inj refl = mkSigma refl refl

  C-Grd-inj : {n : Nat} {c c' : Constr} {t t' : C.Expr n} -> Eq (C.Grd c t) (C.Grd c' t') -> Pair (Eq c c') (Eq t t')
  C-Grd-inj refl = mkSigma refl refl

  C-LLam-inj : {n : Nat} {u u' : C.Expr n} -> Eq (C.LLam u) (C.LLam u') -> Eq u u'
  C-LLam-inj refl = refl

  C-LPi-inj : {n : Nat} {u u' : C.Expr n} -> Eq (C.LPi u) (C.LPi u') -> Eq u u'
  C-LPi-inj refl = refl

  C-LApp-inj : {n : Nat} {t t' : C.Expr n} {l l' : LExpr} -> Eq (C.LApp t l) (C.LApp t' l') -> Pair (Eq t t') (Eq l l')
  C-LApp-inj refl = mkSigma refl refl

------------------------------------------------------------------------
-- Types, as far as the product formers go
------------------------------------------------------------------------

asPi : {n : Nat} {G : Ctx n} {X : Expr n} {Y : Expr (suc n)} -> LoopFree (lctx G) ->
  IsType G (Pi X Y) -> Pair (IsType G X) (IsType (extend G X) Y)
asPi lf (is-Pi dX dY)    = mkSigma dX dY
asPi lf (is-Ty-from-U d) = let r = inv-Pi lf d in mkSigma (is-Ty-from-U (InvPi.dA r)) (is-Ty-from-U (InvPi.dB r))

asLPi : {n : Nat} {G : Ctx n} {X : Expr n} -> IsType G (LPi X) -> IsType (addL G) X
asLPi (is-LPi _ dX)     = dX
asLPi (is-Ty-from-U d)  = absurd (hasType-LPi-absurd d)

------------------------------------------------------------------------
-- The application cases (after removing a valid guard on top)
------------------------------------------------------------------------

appCase : {n : Nat} {G : Ctx n} {C0 C1 c0 c1 a0 a1 T0 T1 : Expr n} {D0 D1 : Expr (suc n)} -> LoopFree (lctx G)
  -> JResN G c0 c1 (Pi C0 D0) (Pi C1 D1)
  -> JRes G a0 a1 C0 C1
  -> InvApp G C0 D0 c0 a0 T0 -> InvApp G C1 D1 c1 a1 T1
  -> JRes G (App C0 D0 c0 a0) (App C1 D1 c1 a1) T0 T1
appCase lf (mkJResN L k0 k1 (jconv cv0 cv1) e _) ra i0 i1 =
  let dC0   = InvApp.dA i0 ; dD0 = InvApp.dB i0
      pinj  = PiInj lf (conv-Ty-trans cv0 (conv-Ty-sym cv1))
      cC    = fst pinj ; cB = snd pinj
      cf    = conv-conv e (conv-Ty-sym cv0)
      ca    = Join-diag (JRes.join ra) cC (InvApp.da i0) (InvApp.da i1) (JRes.eq ra)
      da1'  = ty-conv (InvApp.da i1) (conv-Ty-sym cC)
      df1'  = presup-r-ConvTm cf
      cBa   = subst1-cong-Ty ca dC0 dD0
      step1 = conv-cong-App-fun dC0 dD0 cf (InvApp.da i0)
      step2 = conv-cong-App-arg dC0 dD0 df1' ca cBa
      step3 = conv-conv (conv-cong-App-Ty dC0 dD0 cC cB df1' da1') (conv-Ty-sym cBa)
      cBB   = conv-Ty-trans cBa (subst-ConvTy (subst1-WtSub dC0 da1') (isType-WfCtx dC0) cB)
      p0    = presup-l-ConvTm step1
      dP    = typing-IsType p0
      p1    = ty-conv (ty-App (InvApp.dA i1) (InvApp.dB i1) (InvApp.dc i1) (InvApp.da i1)) (conv-Ty-sym cBB)
  in Join-sub lf (mkJRes _ idC idC (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (conv-trans step1 (conv-trans step2 step3)))
       p0 p1 (InvApp.sub i0) (Sub-conv-left cBB (InvApp.sub i1))
appCase lf (mkJResN _ _ _ (juniv _ _ _ _ cv0 _) _ _) ra i0 i1 = absurd (noconf-Pi-U lf cv0)
appCase lf (mkJResN _ _ _ (jlpi _ _ _ cv0 _ _) _ _) ra i0 i1 = absurd (noconf-Pi-LPi lf cv0)
appCase lf (mkJResN _ _ _ (jgrd _ _ _ _ _ _) _ ()) ra i0 i1
appCase lf (mkJResN _ _ _ (jpi dA dE0 dE1 cv0 cv1 j) e _) ra i0 i1 =
  let wfG  = isType-WfCtx dA
      pi0  = PiInj lf cv0
      pi1  = PiInj lf cv1
      dC0  = InvApp.dA i0 ; dC1 = InvApp.dA i1
      dD0  = InvApp.dB i0 ; dD1 = InvApp.dB i1
      da0  = InvApp.da i0 ; da1 = InvApp.da i1
      cC   = conv-Ty-trans (fst pi0) (conv-Ty-sym (fst pi1))
      ca   = Join-diag (JRes.join ra) cC da0 da1 (JRes.eq ra)
      a0A  = ty-conv da0 (fst pi0)
      a1A  = ty-conv da1 (fst pi1)
      caA  = conv-conv ca (fst pi0)
      c0A  = ty-conv (InvApp.dc i0) cv0
      c1A  = ty-conv (InvApp.dc i1) cv1
      dLB  = join-L j
      X    = conv-cong-App-fun dA dLB e a0A
      b0   = coe-beta dA dLB (coe-ty j (appv0-ty dA dE0 c0A)) a0A
      b1   = coe-beta dA dLB (coe-ty (Join-sym j) (appv0-ty dA dE1 c1A)) a0A
      j'   = Join-subst (subst1-WtSub dA a0A) wfG j
      cD0  = ctx-conv-ConvTy dC0 dA (fst pi0) (conv-Ty-sym (snd pi0))
      Y0   = conv-cong-App-Ty dA dE0 (conv-Ty-sym (fst pi0)) cD0 c0A a0A
      Z0   = coe-cong j' Y0
      cBa1 = subst1-cong-Ty caA dA dE1
      Y1a  = conv-cong-App-arg dA dE1 c1A caA cBa1
      cD1  = ctx-conv-ConvTy dC1 dA (fst pi1) (conv-Ty-sym (snd pi1))
      Y1b  = conv-cong-App-Ty dA dE1 (conv-Ty-sym (fst pi1)) cD1 c1A a1A
      Y1   = conv-trans Y1a (conv-conv Y1b (conv-Ty-sym cBa1))
      Z1   = coe-cong (Join-sym j') Y1
      eqf  = conv-trans (conv-sym Z0) (conv-trans (conv-sym b0) (conv-trans X (conv-trans b1 Z1)))
      cB0a = subst-ConvTy (subst1-WtSub dC0 da0) wfG (conv-Ty-sym (snd pi0))
      cB1a = subst-ConvTy (subst1-WtSub dC1 da1) wfG (conv-Ty-sym (snd pi1))
      cB1' = conv-Ty-trans cBa1 cB1a
      p0   = ty-conv (ty-App dC0 dD0 (InvApp.dc i0) da0) (conv-Ty-sym cB0a)
      p1   = ty-conv (ty-App dC1 dD1 (InvApp.dc i1) da1) (conv-Ty-sym cB1')
  in Join-sub lf (mkJRes _ _ _ j' eqf) p0 p1 (Sub-conv-left cB0a (InvApp.sub i0)) (Sub-conv-left cB1' (InvApp.sub i1))

lappCase : {n : Nat} {G : Ctx n} {A0 A1 t0 t1 T0 T1 : Expr n} -> LoopFree (lctx G) -> (l : LExpr)
  -> JResN G t0 t1 (LPi A0) (LPi A1) -> InvLApp G A0 t0 l T0 -> InvLApp G A1 t1 l T1
  -> JRes G (LApp A0 t0 l) (LApp A1 t1 l) T0 T1
lappCase {G = G} lf l (mkJResN L k0 k1 (jconv cv0 cv1) e _) i0 i1 =
  let dA0  = InvLApp.dA i0 ; dt0 = InvLApp.dt i0 ; dA1 = InvLApp.dA i1 ; dt1 = InvLApp.dt i1
      cA   = LPiInj lf (conv-Ty-trans cv0 (conv-Ty-sym cv1))
      cf   = conv-conv e (conv-Ty-sym cv0)
      dt1' = presup-r-ConvTm cf
      s1   = conv-cong-LApp-fun dA0 cf
      s2   = conv-cong-LApp-Ty dA0 cA dt1'
      cAl  = lsub-ConvTy (lsk-inst G l) (lok-inst G l) cA
      p0   = ty-LApp dA0 dt0
      dP   = typing-IsType p0
      p1   = ty-conv (ty-LApp dA1 dt1) (conv-Ty-sym cAl)
  in Join-sub lf (mkJRes _ idC idC (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (conv-trans s1 s2))
       p0 p1 (InvLApp.sub i0) (Sub-conv-left cAl (InvLApp.sub i1))
lappCase lf l (mkJResN _ _ _ (juniv _ _ _ _ cv0 _) _ _) i0 i1 = absurd (noconf-LPi-U lf cv0)
lappCase lf l (mkJResN _ _ _ (jpi _ _ _ cv0 _ _) _ _) i0 i1 = absurd (noconf-Pi-LPi lf (conv-Ty-sym cv0))
lappCase lf l (mkJResN _ _ _ (jgrd _ _ _ _ _ _) _ ()) i0 i1
lappCase {G = G} lf l (mkJResN _ _ _ (jlpi wf dB0 dB1 cv0 cv1 j) e _) i0 i1 =
  let dA0  = InvLApp.dA i0 ; dt0 = InvLApp.dt i0 ; dA1 = InvLApp.dA i1 ; dt1 = InvLApp.dt i1
      cA0  = LPiInj lf cv0
      cA1  = LPiInj lf cv1
      t0B  = ty-conv dt0 cv0
      t1B  = ty-conv dt1 cv1
      dL   = join-L j
      X    = conv-cong-LApp-fun dL e
      b0   = coe-lbeta l dL (coe-ty j (lappv0-ty dB0 t0B))
      b1   = coe-lbeta l dL (coe-ty (Join-sym j) (lappv0-ty dB1 t1B))
      s    = lsk-inst G l
      ok   = lok-inst G l
      j'   = Join-lsub s ok j
      cl0  = lsub-ConvTy s ok cA0
      cl1  = lsub-ConvTy s ok cA1
      Z0   = coe-cong j' (conv-conv (conv-cong-LApp-Ty dA0 cA0 dt0) cl0)
      Z1   = coe-cong (Join-sym j') (conv-conv (conv-cong-LApp-Ty dA1 cA1 dt1) cl1)
      eqf  = conv-trans Z0 (conv-trans (conv-sym b0) (conv-trans X (conv-trans b1 (conv-sym Z1))))
      p0   = ty-conv (ty-LApp dA0 dt0) cl0
      p1   = ty-conv (ty-LApp dA1 dt1) cl1
  in Join-sub lf (mkJRes _ _ _ j' eqf) p0 p1
       (Sub-conv-left (conv-Ty-sym cl0) (InvLApp.sub i0)) (Sub-conv-left (conv-Ty-sym cl1) (InvLApp.sub i1))

------------------------------------------------------------------------
-- The main lemma, by structural induction on the term
------------------------------------------------------------------------

mutual

  main : {n : Nat} {G : Ctx n} (u0 u1 : Expr n) {T0 T1 : Expr n}
    -> Eq (strip u0) (strip u1) -> HasType G u0 T0 -> HasType G u1 T1 -> JRes G u0 u1 T0 T1
  main {G = G} u0 u1 e d0 d1 = mainD (decLoop (lctx G)) u0 u1 e d0 d1

  mainD : {n : Nat} {G : Ctx n} -> Either (Loop (lctx G)) (LoopFree (lctx G)) -> (u0 u1 : Expr n) {T0 T1 : Expr n}
    -> Eq (strip u0) (strip u1) -> HasType G u0 T0 -> HasType G u1 T1 -> JRes G u0 u1 T0 T1
  mainD (inl lp) u0 u1 e d0 d1 = collapseRes lp d0 d1
  -- variables
  mainD (inr lf) (Var i) (Var .i) refl d0 d1 =
    let r0 = inv-Var lf d0 ; r1 = inv-Var lf d1 ; wf = fst r0 ; dP = wfCtx-lookup wf i
    in Join-sub lf (mkJRes _ idC idC (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (conv-refl (ty-var wf)))
         (ty-var wf) (ty-var wf) (snd r0) (snd r1)
  -- universes
  mainD (inr lf) (U l) (U .l) refl d0 d1 =
    let r0 = inv-U lf d0 ; r1 = inv-U lf d1 ; wf = fst r0 ; dP = isType-U {l = lnext l} wf
        dU = ty-U wf (lt-next l)
    in Join-sub lf (mkJRes _ idC idC (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (conv-refl dU))
         dU dU (snd r0) (snd r1)
  -- products (as terms)
  mainD (inr lf) (Pi A0 B0) (Pi A1 B1) e d0 d1 =
    let inj = C-Pi-inj e in piCase lf A0 B0 A1 B1 (fst inj) (snd inj) d0 d1
  -- abstractions
  mainD (inr lf) (Lam A0 B0 b0) (Lam A1 B1 b1) e d0 d1 =
    let inj = C-Lam-inj e in lamCase lf A0 B0 b0 A1 B1 b1 (fst inj) (snd inj) d0 d1
  -- applications
  mainD (inr lf) (App C0 D0 c0 a0) (App C1 D1 c1 a1) e d0 d1 =
    let inj = C-App-inj e
        i0  = inv-App lf d0 ; i1 = inv-App lf d1
        rc  = main c0 c1 (fst inj) (InvApp.dc i0) (InvApp.dc i1)
        ra  = main a0 a1 (snd inj) (InvApp.da i0) (InvApp.da i1)
    in appCase lf (normTop (\ c B cv -> grd-valid-Pi lf cv) (InvApp.dc i0) (InvApp.dc i1) rc) ra i0 i1
  -- large types have no typing
  mainD (inr lf) (Grd c A) u1 e d0 d1 = absurd (hasType-Grd-absurd d0)
  mainD (inr lf) (LPi A) u1 e d0 d1   = absurd (hasType-LPi-absurd d0)
  -- ⟨ψ⟩t
  mainD (inr lf) (GLam c A0 t0) (GLam c' A1 t1) e d0 d1 =
    let inj = C-GLam-inj e in glamCase lf (fst inj) A0 t0 A1 t1 (snd inj) d0 d1
  -- ∅
  mainD (inr lf) Emp Emp e d0 d1 =
    let r0 = inv-Emp lf d0 ; r1 = inv-Emp lf d1 ; wf = fst r0
        l0 = fst (snd r0) ; l1 = fst (snd r1)
        cU = \ (l : LExpr) -> conv-Ty-refl (isType-U {l = l} wf)
    in Join-sub lf (mkJRes (U (lsup l0 l1)) idC idC (juniv l0 l1 (lsup l0 l1) v-refl (cU l0) (cU l1)) (conv-refl (ty-Emp wf)))
         (ty-Emp wf) (ty-Emp wf) (snd (snd r0)) (snd (snd r1))
  -- ⟨α⟩u
  mainD (inr lf) (LLam A0 u0) (LLam A1 u1) e d0 d1 = llamCase lf A0 u0 A1 u1 (C-LLam-inj e) d0 d1
  -- t l
  mainD (inr lf) (LApp A0 t0 l) (LApp A1 t1 l') e d0 d1 =
    let inj = C-LApp-inj e in lappK lf (snd inj) A0 t0 A1 t1 (fst inj) d0 d1
  -- different heads
  mainD (inr lf) (Var _) (U _) () d0 d1
  mainD (inr lf) (Var _) (Pi _ _) () d0 d1
  mainD (inr lf) (Var _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (Var _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (Var _) (Grd _ _) () d0 d1
  mainD (inr lf) (Var _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (Var _) Emp () d0 d1
  mainD (inr lf) (Var _) (LPi _) () d0 d1
  mainD (inr lf) (Var _) (LLam _ _) () d0 d1
  mainD (inr lf) (Var _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (U _) (Var _) () d0 d1
  mainD (inr lf) (U _) (Pi _ _) () d0 d1
  mainD (inr lf) (U _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (U _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (U _) (Grd _ _) () d0 d1
  mainD (inr lf) (U _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (U _) Emp () d0 d1
  mainD (inr lf) (U _) (LPi _) () d0 d1
  mainD (inr lf) (U _) (LLam _ _) () d0 d1
  mainD (inr lf) (U _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (Pi _ _) (Var _) () d0 d1
  mainD (inr lf) (Pi _ _) (U _) () d0 d1
  mainD (inr lf) (Pi _ _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (Pi _ _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (Pi _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (Pi _ _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (Pi _ _) Emp () d0 d1
  mainD (inr lf) (Pi _ _) (LPi _) () d0 d1
  mainD (inr lf) (Pi _ _) (LLam _ _) () d0 d1
  mainD (inr lf) (Pi _ _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (Var _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (U _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (Pi _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) Emp () d0 d1
  mainD (inr lf) (Lam _ _ _) (LPi _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (LLam _ _) () d0 d1
  mainD (inr lf) (Lam _ _ _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (Var _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (U _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (Pi _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) Emp () d0 d1
  mainD (inr lf) (App _ _ _ _) (LPi _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (LLam _ _) () d0 d1
  mainD (inr lf) (App _ _ _ _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (Var _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (U _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (Pi _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) Emp () d0 d1
  mainD (inr lf) (GLam _ _ _) (LPi _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (LLam _ _) () d0 d1
  mainD (inr lf) (GLam _ _ _) (LApp _ _ _) () d0 d1
  mainD (inr lf) Emp (Var _) () d0 d1
  mainD (inr lf) Emp (U _) () d0 d1
  mainD (inr lf) Emp (Pi _ _) () d0 d1
  mainD (inr lf) Emp (Lam _ _ _) () d0 d1
  mainD (inr lf) Emp (App _ _ _ _) () d0 d1
  mainD (inr lf) Emp (Grd _ _) () d0 d1
  mainD (inr lf) Emp (GLam _ _ _) () d0 d1
  mainD (inr lf) Emp (LPi _) () d0 d1
  mainD (inr lf) Emp (LLam _ _) () d0 d1
  mainD (inr lf) Emp (LApp _ _ _) () d0 d1
  mainD (inr lf) (LLam _ _) (Var _) () d0 d1
  mainD (inr lf) (LLam _ _) (U _) () d0 d1
  mainD (inr lf) (LLam _ _) (Pi _ _) () d0 d1
  mainD (inr lf) (LLam _ _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (LLam _ _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (LLam _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (LLam _ _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (LLam _ _) Emp () d0 d1
  mainD (inr lf) (LLam _ _) (LPi _) () d0 d1
  mainD (inr lf) (LLam _ _) (LApp _ _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (Var _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (U _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (Pi _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (Lam _ _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (App _ _ _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (Grd _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (GLam _ _ _) () d0 d1
  mainD (inr lf) (LApp _ _ _) Emp () d0 d1
  mainD (inr lf) (LApp _ _ _) (LPi _) () d0 d1
  mainD (inr lf) (LApp _ _ _) (LLam _ _) () d0 d1

  piCase : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} -> LoopFree (lctx G) -> (A0 : Expr n) (B0 : Expr (suc n)) (A1 : Expr n) (B1 : Expr (suc n))
    -> Eq (strip A0) (strip A1) -> Eq (strip B0) (strip B1)
    -> HasType G (Pi A0 B0) T0 -> HasType G (Pi A1 B1) T1 -> JRes G (Pi A0 B0) (Pi A1 B1) T0 T1
  piCase lf A0 B0 A1 B1 eA eB d0 d1 =
    let p0   = inv-Pi lf d0 ; p1 = inv-Pi lf d1
        l0   = InvPi.lvl p0 ; l1 = InvPi.lvl p1 ; m = lsup l0 l1
        dA0  = InvPi.dA p0 ; dA1 = InvPi.dA p1
        dB0  = InvPi.dB p0 ; dB1 = InvPi.dB p1
        rA   = main A0 A1 eA dA0 dA1
        cAU  = joinU-both A0 A1 lf rA dA0 dA1
        cA   = conv-Ty-from-U cAU
        dB1' = ctx-conv-HasType (is-Ty-from-U dA1) (is-Ty-from-U dA0) (conv-Ty-sym cA) dB1
        rB   = main B0 B1 eB dB0 dB1'
        cBU  = joinU-both B0 B1 lf rB dB0 dB1'
        ePi  = conv-cong-Pi (ty-cum dA0 (leL-supl l0 l1)) (ty-cum dB0 (leL-supl l0 l1)) cAU cBU
        wf   = typing-WfCtx dA0
        cU   = \ (l : LExpr) -> conv-Ty-refl (isType-U {l = l} wf)
    in Join-sub lf (mkJRes (U m) idC idC (juniv l0 l1 m v-refl (cU l0) (cU l1)) ePi)
         (ty-Pi dA0 dB0) (ty-Pi dA1 dB1) (InvPi.sub p0) (InvPi.sub p1)

  lamCase : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} -> LoopFree (lctx G)
    -> (A0 : Expr n) (B0 b0 : Expr (suc n)) (A1 : Expr n) (B1 b1 : Expr (suc n))
    -> Eq (strip A0) (strip A1) -> Eq (strip b0) (strip b1)
    -> HasType G (Lam A0 B0 b0) T0 -> HasType G (Lam A1 B1 b1) T1 -> JRes G (Lam A0 B0 b0) (Lam A1 B1 b1) T0 T1
  lamCase lf A0 B0 b0 A1 B1 b1 eA eb d0 d1 =
    let l0   = inv-Lam lf d0 ; l1 = inv-Lam lf d1
        dA0  = InvLam.dA l0 ; dB0 = InvLam.dB l0 ; db0 = InvLam.db l0
        dA1  = InvLam.dA l1 ; dB1 = InvLam.dB l1 ; db1 = InvLam.db l1
        cA   = tyMain A0 A1 eA dA0 dA1
        dB1' = ctx-conv-IsType dA1 dA0 (conv-Ty-sym cA) dB1
        db1' = ctx-conv-HasType dA1 dA0 (conv-Ty-sym cA) db1
        rb   = main b0 b1 eb db0 db1'
        j    = JRes.join rb
        dLB  = join-L j
        jP   = jpi dA0 dB0 dB1' (conv-Ty-refl (is-Pi dA0 dB0))
                 (conv-Ty-Pi dA1 dB1 (conv-Ty-sym cA) (conv-Ty-refl dB1)) j
        E0   = coe-cong j (lam-beta-v0 dA0 dB0 db0)
        L0   = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm E0) E0
        M    = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm (JRes.eq rb)) (JRes.eq rb)
        R1   = coe-cong (Join-sym jP) (conv-cong-Lam-Ty dA1 dB1 (conv-Ty-sym cA) (conv-Ty-refl dB1) db1)
        E1   = coe-cong (Join-sym j) (lam-beta-v0 dA0 dB1' db1')
        R2   = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm E1) E1
    in Join-sub lf (mkJRes _ _ _ jP (conv-trans L0 (conv-trans M (conv-sym (conv-trans R1 R2)))))
         (ty-Lam dA0 dB0 db0) (ty-Lam dA1 dB1 db1) (InvLam.sub l0) (InvLam.sub l1)

  glamCase : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} {c c' : Constr} -> LoopFree (lctx G) -> Eq c c'
    -> (A0 t0 A1 t1 : Expr n) -> Eq (strip t0) (strip t1)
    -> HasType G (GLam c A0 t0) T0 -> HasType G (GLam c' A1 t1) T1 -> JRes G (GLam c A0 t0) (GLam c' A1 t1) T0 T1
  glamCase {G = G} {c = c} lf refl A0 t0 A1 t1 e d0 d1 =
    let g0  = inv-GLam lf d0 ; g1 = inv-GLam lf d1
        wf  = InvGLam.wf g0
        dA0 = InvGLam.dA g0 ; dt0 = InvGLam.dt g0
        dA1 = InvGLam.dA g1 ; dt1 = InvGLam.dt g1
        rt  = main t0 t1 e dt0 dt1
        j   = JRes.join rt
        dL  = join-L j
        jG  = jgrd wf dA0 dA1 (conv-Ty-refl (is-Grd wf dA0)) (conv-Ty-refl (is-Grd wf dA1)) j
        vc  = valid-addC G c
        E0  = coe-cong j (conv-GLam-beta vc dA0 dt0)
        E1  = coe-cong (Join-sym j) (conv-GLam-beta vc dA1 dt1)
        X   = conv-trans E0 (conv-trans (JRes.eq rt) (conv-sym E1))
    in Join-sub lf (mkJRes _ _ _ jG (conv-cong-GLam wf dL (presup-l-ConvTm X) X))
         (ty-GLam wf dA0 dt0) (ty-GLam wf dA1 dt1) (InvGLam.sub g0) (InvGLam.sub g1)

  llamCase : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} -> LoopFree (lctx G)
    -> (A0 u0 A1 u1 : Expr n) -> Eq (strip u0) (strip u1)
    -> HasType G (LLam A0 u0) T0 -> HasType G (LLam A1 u1) T1 -> JRes G (LLam A0 u0) (LLam A1 u1) T0 T1
  llamCase lf A0 u0 A1 u1 e d0 d1 =
    let g0  = inv-LLam lf d0 ; g1 = inv-LLam lf d1
        wf  = InvLLam.wf g0
        dA0 = InvLLam.dA g0 ; du0 = InvLLam.du g0
        dA1 = InvLLam.dA g1 ; du1 = InvLLam.du g1
        ru  = main u0 u1 e du0 du1
        j   = JRes.join ru
        dL  = join-L j
        jL  = jlpi wf dA0 dA1 (conv-Ty-refl (is-LPi wf dA0)) (conv-Ty-refl (is-LPi wf dA1)) j
        E0  = coe-cong j (llam-beta-v0 dA0 du0)
        E1  = coe-cong (Join-sym j) (llam-beta-v0 dA1 du1)
        X   = conv-trans E0 (conv-trans (JRes.eq ru) (conv-sym E1))
    in Join-sub lf (mkJRes _ _ _ jL (conv-cong-LLam wf dL (presup-l-ConvTm X) X))
         (ty-LLam wf dA0 du0) (ty-LLam wf dA1 du1) (InvLLam.sub g0) (InvLLam.sub g1)

  lappK : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} {l l' : LExpr} -> LoopFree (lctx G) -> Eq l l'
    -> (A0 t0 A1 t1 : Expr n) -> Eq (strip t0) (strip t1)
    -> HasType G (LApp A0 t0 l) T0 -> HasType G (LApp A1 t1 l') T1 -> JRes G (LApp A0 t0 l) (LApp A1 t1 l') T0 T1
  lappK {l = l} lf refl A0 t0 A1 t1 e d0 d1 =
    let i0 = inv-LApp lf d0 ; i1 = inv-LApp lf d1
        rt = main t0 t1 e (InvLApp.dt i0) (InvLApp.dt i1)
    in lappCase lf l (normTop (\ c B cv -> grd-valid-LPi lf cv) (InvLApp.dt i0) (InvLApp.dt i1) rt) i0 i1

  -- types, which may be large
  tyMain : {n : Nat} {G : Ctx n} (A0 A1 : Expr n)
    -> Eq (strip A0) (strip A1) -> IsType G A0 -> IsType G A1 -> ConvTy G A0 A1
  tyMain {G = G} A0 A1 e d0 d1 = tyMainD (decLoop (lctx G)) A0 A1 e d0 d1

  viaMain : {n : Nat} {G : Ctx n} {l0 l1 : LExpr} -> LoopFree (lctx G) -> (A0 A1 : Expr n)
    -> Eq (strip A0) (strip A1) -> HasType G A0 (U l0) -> HasType G A1 (U l1) -> ConvTy G A0 A1
  viaMain lf A0 A1 e d0 d1 = conv-Ty-from-U (joinU-both A0 A1 lf (main A0 A1 e d0 d1) d0 d1)

  tyMainD : {n : Nat} {G : Ctx n} -> Either (Loop (lctx G)) (LoopFree (lctx G)) -> (A0 A1 : Expr n)
    -> Eq (strip A0) (strip A1) -> IsType G A0 -> IsType G A1 -> ConvTy G A0 A1
  tyMainD (inl lp) A0 A1 e d0 d1 = conv-Ty-trans (conv-Ty-collapse lp d0) (conv-Ty-sym (conv-Ty-collapse lp d1))
  tyMainD (inr lf) (Pi X0 Y0) (Pi X1 Y1) e d0 d1 =
    let inj  = C-Pi-inj e
        p0   = asPi lf d0 ; p1 = asPi lf d1
        cX   = tyMain X0 X1 (fst inj) (fst p0) (fst p1)
        dY1' = ctx-conv-IsType (fst p1) (fst p0) (conv-Ty-sym cX) (snd p1)
        cY   = tyMain Y0 Y1 (snd inj) (snd p0) dY1'
    in conv-Ty-Pi (fst p0) (snd p0) cX cY
  tyMainD (inr lf) (Grd c X0) (Grd c' X1) e d0 d1 =
    let inj = C-Grd-inj e in grdTy (fst inj) X0 X1 (snd inj) d0 d1
  tyMainD (inr lf) (LPi X0) (LPi X1) e d0 d1 =
    let dX0 = asLPi d0
    in conv-Ty-LPi (isType-WfCtx d0) dX0 (tyMain X0 X1 (C-LPi-inj e) dX0 (asLPi d1))
  tyMainD (inr lf) A0@(Var _) A1@(Var _) e (is-Ty-from-U d0) (is-Ty-from-U d1)         = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) A0@(U _) A1@(U _) e (is-Ty-from-U d0) (is-Ty-from-U d1)             = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) A0@(Lam _ _ _) A1@(Lam _ _ _) e (is-Ty-from-U d0) (is-Ty-from-U d1) = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) A0@(App _ _ _ _) A1@(App _ _ _ _) e (is-Ty-from-U d0) (is-Ty-from-U d1) = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) A0@(GLam _ _ _) A1@(GLam _ _ _) e (is-Ty-from-U d0) (is-Ty-from-U d1) = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) Emp Emp e (is-Ty-from-U d0) (is-Ty-from-U d1)                       = viaMain lf Emp Emp e d0 d1
  tyMainD (inr lf) A0@(LLam _ _) A1@(LLam _ _) e (is-Ty-from-U d0) (is-Ty-from-U d1)   = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) A0@(LApp _ _ _) A1@(LApp _ _ _) e (is-Ty-from-U d0) (is-Ty-from-U d1) = viaMain lf A0 A1 e d0 d1
  tyMainD (inr lf) (Var _) (U _) () d0 d1
  tyMainD (inr lf) (Var _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (Var _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (Var _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (Var _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (Var _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (Var _) Emp () d0 d1
  tyMainD (inr lf) (Var _) (LPi _) () d0 d1
  tyMainD (inr lf) (Var _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (Var _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (U _) (Var _) () d0 d1
  tyMainD (inr lf) (U _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (U _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (U _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (U _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (U _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (U _) Emp () d0 d1
  tyMainD (inr lf) (U _) (LPi _) () d0 d1
  tyMainD (inr lf) (U _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (U _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (Var _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (U _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) Emp () d0 d1
  tyMainD (inr lf) (Pi _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (Pi _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (Var _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (U _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) Emp () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (Lam _ _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (Var _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (U _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) Emp () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (App _ _ _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (Var _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (U _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) Emp () d0 d1
  tyMainD (inr lf) (Grd _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (Grd _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (Var _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (U _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) Emp () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (GLam _ _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) Emp (Var _) () d0 d1
  tyMainD (inr lf) Emp (U _) () d0 d1
  tyMainD (inr lf) Emp (Pi _ _) () d0 d1
  tyMainD (inr lf) Emp (Lam _ _ _) () d0 d1
  tyMainD (inr lf) Emp (App _ _ _ _) () d0 d1
  tyMainD (inr lf) Emp (Grd _ _) () d0 d1
  tyMainD (inr lf) Emp (GLam _ _ _) () d0 d1
  tyMainD (inr lf) Emp (LPi _) () d0 d1
  tyMainD (inr lf) Emp (LLam _ _) () d0 d1
  tyMainD (inr lf) Emp (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (Var _) () d0 d1
  tyMainD (inr lf) (LPi _) (U _) () d0 d1
  tyMainD (inr lf) (LPi _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (LPi _) Emp () d0 d1
  tyMainD (inr lf) (LPi _) (LLam _ _) () d0 d1
  tyMainD (inr lf) (LPi _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (Var _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (U _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (LLam _ _) Emp () d0 d1
  tyMainD (inr lf) (LLam _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (LLam _ _) (LApp _ _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (Var _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (U _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (Pi _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (Lam _ _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (App _ _ _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (Grd _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (GLam _ _ _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) Emp () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (LPi _) () d0 d1
  tyMainD (inr lf) (LApp _ _ _) (LLam _ _) () d0 d1

  grdTy : {n : Nat} {G : Ctx n} {c c' : Constr} -> Eq c c' -> (X0 X1 : Expr n) -> Eq (strip X0) (strip X1)
    -> IsType G (Grd c X0) -> IsType G (Grd c' X1) -> ConvTy G (Grd c X0) (Grd c' X1)
  grdTy refl X0 X1 e d0 d1 =
    let dX0 = inv-IsType-Grd d0
    in conv-Ty-Grd (isType-WfCtx d0) dX0 (tyMain X0 X1 e dX0 (inv-IsType-Grd d1))

------------------------------------------------------------------------
-- Lemma 4.18, without normalisation
------------------------------------------------------------------------

type-uniq-NF : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
  IsType G A0 -> IsType G A1 -> Eq (strip A0) (strip A1) -> ConvTy G A0 A1
type-uniq-NF {A0 = A0} {A1 = A1} d0 d1 e = tyMain A0 A1 e d0 d1

term-uniq-conv-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> ConvTy G A0 A1 ->
  ConvTm G u0 u1 A0
term-uniq-conv-NF {u0 = u0} {u1 = u1} d0 d1 e cA =
  let r = main u0 u1 e d0 d1 in Join-diag (JRes.join r) cA d0 d1 (JRes.eq r)

term-uniq-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> Eq (strip A0) (strip A1) ->
  Pair (ConvTy G A0 A1) (ConvTm G u0 u1 A0)
term-uniq-NF d0 d1 eu eA =
  let cA = type-uniq-NF (typing-IsType d0) (typing-IsType d1) eA
  in mkSigma cA (term-uniq-conv-NF d0 d1 eu cA)
