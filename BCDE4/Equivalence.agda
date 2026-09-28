{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Equivalence
--
-- The section of erasure (Theorem 4.13 of the Russell/Tarski
-- comparison, cf. ERT.Equivalence) for T_T with internal levels,
-- cumulative universes, constraint and level products, ∅ and the
-- loop-collapse rules: every Russell judgement has a Tarski preimage.
-- Structural recursion on the Russell derivation; the Tarski side is
-- only constructed.  Soundness of erasure (Lemma 4.6) is in
-- BCDE4.EraseDeriv, uniqueness (Lemma 4.10) in BCDE4.Uniqueness.
--
-- Each rule chooses a base Tarski context (the lift of one premise)
-- and places the lifts of the other premises there (BCDE4.LiftIn).
-- The Russell universe rules become code rules:
--
--   A : U_l ⇒ A type       ↦  El_l a
--   U_l : U_m  (l < m)     ↦  U^m_l
--   A : U_l ⇒ A : U_m      ↦  ↑^m_l a
--   Π A B : U_l            ↦  Π^l a b
--   ∅ : U_l                ↦  ∅^l
--   U_l = U_l' : U_m       ↦  U^m_l = U^m_l'
--
-- conv-trans identifies the two lifts of the middle term by term-uniq
-- and sameType (after retyping at a common type by type-uniq).  The
-- β-rule of level products has all its premises under the level binder;
-- its base context is recovered by instantiating the binder (unL).
------------------------------------------------------------------------

module BCDE4.Equivalence where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax  as R
import BCDE4.RussellTyping  as RT
import BCDE4.TarskiSyntax   as T
import BCDE4.TarskiTyping   as TT
import BCDE4.Erasure        as E
import BCDE4.TarskiMeta     as TM
import BCDE4.TarskiLsub     as TL
import BCDE4.TarskiRelevel  as TR
open import BCDE4.Uniqueness using (Result ; type-uniq ; term-uniq ; sameType)
open import BCDE4.EraseDeriv
open import BCDE4.LiftBack
open import BCDE4.LiftIn public

private
  validC-top : {Th : LCtx} (c : Constr) -> ValidC (lcons c Th) c
  validC-top (ceq l m) = v-hyp lhere

------------------------------------------------------------------------
-- The five lifts, by mutual induction on Russell derivations
------------------------------------------------------------------------

lift-WfCtx : {n : Nat} {G : RT.Ctx n}
  -> RT.WfCtx G -> LiftWfCtx G

lift-IsType : {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
  -> RT.IsType G A -> LiftIsType G A

lift-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
  -> RT.HasType G M A -> LiftHasType G M A

lift-ConvTy : {n : Nat} {G : RT.Ctx n} {A B : R.Expr n}
  -> RT.ConvTy G A B -> LiftConvTy G A B

lift-ConvTm : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n}
  -> RT.ConvTm G M N A -> LiftConvTm G M N A

------------------------------------------------------------------------
-- lift-WfCtx
------------------------------------------------------------------------

lift-WfCtx (RT.wf-empty {Th = Th}) = mkLiftWfCtx (TT.empty Th) refl TT.wf-empty
lift-WfCtx (RT.wf-extend dA) =
  let mkLiftIsType H A' e eA d = lift-IsType dA
  in mkLiftWfCtx (TT.extend H A') (Eq-cong2 RT.extend e eA) (TT.wf-extend d)

------------------------------------------------------------------------
-- lift-IsType
------------------------------------------------------------------------

-- A : U_l  ↦  El_l a
lift-IsType (RT.is-Ty-from-U {l = l} d) =
  let IH = lift-HasType d
      mkBase H e wf = bH IH
      mkTmIn a ea da = tmU IH wf e
  in mkLiftIsType H (T.El l a) e ea (TT.is-El da)

lift-IsType (RT.is-Pi dA dB) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
  in mkLiftIsType H (T.Pi A' B') e (Eq-cong2 R.Pi eA eB) (TT.is-Pi dA' dB')

lift-IsType (RT.is-Grd {c = c} dG dA) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TR.wkC-WfCtx c wf) (eC H c e)
  in mkLiftIsType H (T.Grd c A') e (Eq-cong (R.Grd c) eA) (TT.is-Grd wf dA')

lift-IsType (RT.is-LPi dG dA) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TM.wkL-WfCtx wf) (eL H e)
  in mkLiftIsType H (T.LPi A') e (Eq-cong R.LPi eA) (TT.is-LPi wf dA')

------------------------------------------------------------------------
-- lift-HasType
------------------------------------------------------------------------

lift-HasType (RT.ty-GLam {c = c} dG dA dt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfc = TR.wkC-WfCtx c wf
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) wfc (eC H c e)
      mkTmIn t' et dt' = tmIn (lift-HasType dt) wfc (eC H c e) dA' eA
  in mkLiftHasType H (T.GLam c A' t') (T.Grd c A') e
       (Eq-cong2 (R.GLam c) eA et) (Eq-cong (R.Grd c) eA) (TT.ty-GLam wf dA' dt')

lift-HasType (RT.ty-LLam dG dA du) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfl = TM.wkL-WfCtx wf
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) wfl (eL H e)
      mkTmIn u' eu du' = tmIn (lift-HasType du) wfl (eL H e) dA' eA
  in mkLiftHasType H (T.LLam A' u') (T.LPi A') e
       (Eq-cong2 R.LLam eA eu) (Eq-cong R.LPi eA) (TT.ty-LLam wf dA' du')

lift-HasType (RT.ty-LApp {l = l} dA dt) =
  let IH = lift-HasType dt
      mkBase H e wf = bH IH
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TM.wkL-WfCtx wf) (eL H e)
      mkTmIn t' et dt' = tmIn IH wf e (TT.is-LPi wf dA') (Eq-cong R.LPi eA)
  in mkLiftHasType H (T.LApp A' t' l) (T.lsub1 A' l) e
       (Eq-cong2 (\ X Y -> R.LApp X Y l) eA et)
       (Eq-trans (E.erase-lsub1 A' l) (Eq-cong (\ X -> R.lsub1 X l) eA))
       (TT.ty-LApp dA' dt')

-- ∅ : U_l  ↦  ∅^l
lift-HasType (RT.ty-Emp {l = l} dG) =
  let mkBase H e wf = bW (lift-WfCtx dG)
  in mkLiftHasType H (T.EmpCode l) (T.U l) e refl refl (TT.ty-EmpCode wf)

lift-HasType (RT.ty-collapse lp dA) =
  let mkLiftIsType H A' e eA dA' = lift-IsType dA
  in mkLiftHasType H T.Emp A' e refl eA (TT.ty-collapse (lvl H e {Loop} lp) dA')

lift-HasType (RT.ty-var {i = i} dG) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      eA = Eq-trans (Eq-sym (lookup-erase H i)) (Eq-cong (\ X -> RT.lookup X i) e)
  in mkLiftHasType H (T.Var i) (TT.lookup H i) e refl eA (TT.ty-var wf)

lift-HasType (RT.ty-conv dM dAB) =
  let IH = lift-HasType dM
      mkBase H e wf = bH IH
      mkCTyIn A' B' eA eB c = ctyIn (lift-ConvTy dAB) wf e
      mkTmIn M' eM dM' = tmIn IH wf e (TM.presup-l-ConvTy c) eA
  in mkLiftHasType H M' B' e eM eB (TT.ty-conv dM' c)

-- U_l : U_m  ↦  U^m_l
lift-HasType (RT.ty-U {l = l} {m = m} dG lt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
  in mkLiftHasType H (T.UCode m l) (T.U m) e refl refl
       (TT.ty-UCode wf (lvl H e {\ X -> LtL X l m} lt))

-- A : U_l ⇒ A : U_m  ↦  ↑^m_l a
lift-HasType (RT.ty-cum {l = l} {m = m} d le) =
  let IH = lift-HasType d
      mkBase H e wf = bH IH
      mkTmIn a ea da = tmU IH wf e
  in mkLiftHasType H (T.Lift m l a) (T.U m) e ea refl
       (TT.ty-Lift (lvl H e {\ X -> LeL X l m} le) da)

-- Π A B : U_l  ↦  Π^l a b
lift-HasType (RT.ty-Pi {l = l} dA dB) =
  let IH = lift-HasType dA
      mkBase H e wf = bH IH
      mkTmIn a ea da = tmU IH wf e
      mkTmIn b eb db = tmU (lift-HasType dB) (TT.wf-extend (TT.is-El da)) (Eq-cong2 RT.extend e ea)
  in mkLiftHasType H (T.PiCode l a b) (T.U l) e (Eq-cong2 R.Pi ea eb) refl (TT.ty-PiCode da db)

lift-HasType (RT.ty-Lam dA dB db) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      mkTmIn b' eb db' = tmIn (lift-HasType db) (TT.wf-extend dA') (Eq-cong2 RT.extend e eA) dB' eB
  in mkLiftHasType H (T.Lam A' B' b') (T.Pi A' B') e
       (Eq-cong3 R.Lam eA eB eb) (Eq-cong2 R.Pi eA eB) (TT.ty-Lam dA' dB' db')

lift-HasType (RT.ty-App dA dB dc da) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      wf = TM.isType-WfCtx dA'
      mkTmIn c' ec dc' = tmIn (lift-HasType dc) wf e (TT.is-Pi dA' dB') (Eq-cong2 R.Pi eA eB)
      mkTmIn a' ea da' = tmIn (lift-HasType da) wf e dA' eA
  in mkLiftHasType H (T.App A' B' c' a') (T.subst1 B' a') e
       (Eq-cong4 R.App eA eB ec ea)
       (Eq-trans (E.erase-subst1 B' a') (Eq-cong2 R.subst1 eB ea))
       (TT.ty-App dA' dB' dc' da')

------------------------------------------------------------------------
-- lift-ConvTy
------------------------------------------------------------------------

lift-ConvTy (RT.conv-Ty-refl dA) =
  let mkLiftIsType H A' e eA d = lift-IsType dA
  in mkLiftConvTy H A' A' e eA eA (TT.conv-Ty-refl d)

lift-ConvTy (RT.conv-Ty-sym d) =
  let mkLiftConvTy H A' B' e eA eB c = lift-ConvTy d
  in mkLiftConvTy H B' A' e eB eA (TT.conv-Ty-sym c)

lift-ConvTy (RT.conv-Ty-trans d1 d2) =
  let mkLiftConvTy H A1 B1 e eA1 eB1 c1 = lift-ConvTy d1
      wf = TM.isType-WfCtx (TM.presup-l-ConvTy c1)
      mkCTyIn B2 C2 eB2 eC2 c2 = ctyIn (lift-ConvTy d2) wf e
      bridge = type-uniq (TM.presup-r-ConvTy c1) (TM.presup-l-ConvTy c2) (Eq-trans eB1 (Eq-sym eB2))
  in mkLiftConvTy H A1 C2 e eA1 eC2 (TT.conv-Ty-trans c1 (TT.conv-Ty-trans bridge c2))

lift-ConvTy (RT.conv-Ty-Pi _ _ cA cB) =
  let mkPiCIn H e AL AR eAL eAR cA' BL BR eBL eBR cB' = piCIn (lift-ConvTy cA) (lift-ConvTy cB)
  in mkLiftConvTy H (T.Pi AL BL) (T.Pi AR BR) e
       (Eq-cong2 R.Pi eAL eBL) (Eq-cong2 R.Pi eAR eBR) (TM.mk-conv-Ty-Pi cA' cB')

lift-ConvTy (RT.conv-Ty-Grd {c = c} dG _ dAB) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkCTyIn A' B' eA eB cAB = ctyIn (lift-ConvTy dAB) (TR.wkC-WfCtx c wf) (eC H c e)
  in mkLiftConvTy H (T.Grd c A') (T.Grd c B') e (Eq-cong (R.Grd c) eA) (Eq-cong (R.Grd c) eB)
       (TT.conv-Ty-Grd wf (TM.presup-l-ConvTy cAB) cAB)

lift-ConvTy (RT.conv-Ty-LPi dG _ dAB) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkCTyIn A' B' eA eB cAB = ctyIn (lift-ConvTy dAB) (TM.wkL-WfCtx wf) (eL H e)
  in mkLiftConvTy H (T.LPi A') (T.LPi B') e (Eq-cong R.LPi eA) (Eq-cong R.LPi eB)
       (TT.conv-Ty-LPi wf (TM.presup-l-ConvTy cAB) cAB)

lift-ConvTy (RT.conv-Ty-Grd-beta {c = c} v dA) =
  let mkLiftIsType H A' e eA dA' = lift-IsType dA
  in mkLiftConvTy H (T.Grd c A') A' e (Eq-cong (R.Grd c) eA) eA
       (TT.conv-Ty-Grd-beta (lvl H e {\ X -> ValidC X c} v) dA')

lift-ConvTy (RT.conv-Ty-Grd-equiv {c = c} {c' = c'} dG q dA) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TR.wkC-WfCtx c wf) (eC H c e)
  in mkLiftConvTy H (T.Grd c A') (T.Grd c' A') e (Eq-cong (R.Grd c) eA) (Eq-cong (R.Grd c') eA)
       (TT.conv-Ty-Grd-equiv wf (lvl H e {\ X -> EquivC X c c'} q) dA')

lift-ConvTy (RT.conv-Ty-collapse lp dA) =
  let mkLiftIsType H A' e eA dA' = lift-IsType dA
  in mkLiftConvTy H A' T.Emp e eA refl (TT.conv-Ty-collapse (lvl H e {Loop} lp) dA')

-- A = B : U_l  ↦  El_l a = El_l b
lift-ConvTy (RT.conv-Ty-from-U {l = l} d) =
  let IH = lift-ConvTm d
      mkBase H e wf = bCm IH
      mkCTmIn a b ea eb c = ctmU IH wf e
  in mkLiftConvTy H (T.El l a) (T.El l b) e ea eb (TT.conv-Ty-El c)

------------------------------------------------------------------------
-- lift-ConvTm
------------------------------------------------------------------------

lift-ConvTm (RT.conv-refl dM) =
  let mkLiftHasType H M' A' e eM eA d = lift-HasType dM
  in mkLiftConvTm H M' M' A' e eM eM eA (TT.conv-refl d)

lift-ConvTm (RT.conv-sym d) =
  let mkLiftConvTm H M' N' A' e eM eN eA c = lift-ConvTm d
  in mkLiftConvTm H N' M' A' e eN eM eA (TT.conv-sym c)

-- the two lifts of the middle term are identified by uniqueness
lift-ConvTm (RT.conv-trans d1 d2) =
  let mkLiftConvTm H M1 N1 A1 e eM1 eN1 eA1 c1 = lift-ConvTm d1
      dN1 = TM.presup-r-ConvTm c1
      mkCTmIn N2 P2 eN2 eP2 c2 = ctmIn (lift-ConvTm d2) (TM.typing-WfCtx dN1) e (TM.typing-IsType dN1) eA1
      dN2 = TM.presup-l-ConvTm c2
      cN  = sameType dN1 dN2 (term-uniq dN1 dN2 (Eq-trans eN1 (Eq-sym eN2)))
  in mkLiftConvTm H M1 P2 A1 e eM1 eP2 eA1 (TT.conv-trans c1 (TT.conv-trans cN c2))

lift-ConvTm (RT.conv-conv dMN dAB) =
  let IH = lift-ConvTm dMN
      mkBase H e wf = bCm IH
      mkCTyIn A' B' eA eB c = ctyIn (lift-ConvTy dAB) wf e
      mkCTmIn M' N' eM eN cMN = ctmIn IH wf e (TM.presup-l-ConvTy c) eA
  in mkLiftConvTm H M' N' B' e eM eN eB (TT.conv-conv cMN c)

lift-ConvTm (RT.conv-cong-Pi {l = l} _ _ daa dbb) =
  let IH = lift-ConvTm daa
      mkBase H e wf = bCm IH
      mkCTmIn aL aR eaL eaR ca = ctmU IH wf e
      wf2 = TT.wf-extend (TT.is-El (TM.presup-l-ConvTm ca))
      mkCTmIn bL bR ebL ebR cb = ctmU (lift-ConvTm dbb) wf2 (Eq-cong2 RT.extend e eaL)
  in mkLiftConvTm H (T.PiCode l aL bL) (T.PiCode l aR bR) (T.U l) e
       (Eq-cong2 R.Pi eaL ebL) (Eq-cong2 R.Pi eaR ebR) refl (TM.mk-conv-cong-PiCode ca cb)

lift-ConvTm (RT.conv-cum {l = l} {m = m} d le) =
  let IH = lift-ConvTm d
      mkBase H e wf = bCm IH
      mkCTmIn a b ea eb c = ctmU IH wf e
  in mkLiftConvTm H (T.Lift m l a) (T.Lift m l b) (T.U m) e ea eb refl
       (TT.conv-cong-Lift (lvl H e {\ X -> LeL X l m} le) c)

lift-ConvTm (RT.conv-U-lvl {l = l} {l' = l'} {m = m} dG v lt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
  in mkLiftConvTm H (T.UCode m l) (T.UCode m l') (T.U m) e refl refl refl
       (TT.conv-UCode-lvl wf (lvl H e {\ X -> Valid X l l'} v) v-refl (lvl H e {\ X -> LtL X l m} lt))

lift-ConvTm (RT.conv-cong-Lam-body dA dB _ db) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      mkCTmIn bL bR ebL ebR cb = ctmIn (lift-ConvTm db) (TT.wf-extend dA') (Eq-cong2 RT.extend e eA) dB' eB
  in mkLiftConvTm H (T.Lam A' B' bL) (T.Lam A' B' bR) (T.Pi A' B') e
       (Eq-cong3 R.Lam eA eB ebL) (Eq-cong3 R.Lam eA eB ebR) (Eq-cong2 R.Pi eA eB)
       (TT.conv-cong-Lam-body dA' dB' (TM.presup-l-ConvTm cb) cb)

lift-ConvTm (RT.conv-cong-Lam-Ty _ _ cA cB db) =
  let mkPiCIn H e AL AR eAL eAR cA' BL BR eBL eBR cB' = piCIn (lift-ConvTy cA) (lift-ConvTy cB)
      mkTmIn b' eb db' = tmIn (lift-HasType db) (TT.wf-extend (TM.presup-l-ConvTy cA'))
                           (Eq-cong2 RT.extend e eAL) (TM.presup-l-ConvTy cB') eBL
  in mkLiftConvTm H (T.Lam AL BL b') (T.Lam AR BR b') (T.Pi AL BL) e
       (Eq-cong3 R.Lam eAL eBL eb) (Eq-cong3 R.Lam eAR eBR eb) (Eq-cong2 R.Pi eAL eBL)
       (TM.mk-conv-cong-Lam-Ty cA' cB' db')

lift-ConvTm (RT.conv-cong-App-fun dA dB dc da) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      wf = TM.isType-WfCtx dA'
      mkCTmIn cL cR ecL ecR cc = ctmIn (lift-ConvTm dc) wf e (TT.is-Pi dA' dB') (Eq-cong2 R.Pi eA eB)
      mkTmIn a' ea da' = tmIn (lift-HasType da) wf e dA' eA
  in mkLiftConvTm H (T.App A' B' cL a') (T.App A' B' cR a') (T.subst1 B' a') e
       (Eq-cong4 R.App eA eB ecL ea) (Eq-cong4 R.App eA eB ecR ea)
       (Eq-trans (E.erase-subst1 B' a') (Eq-cong2 R.subst1 eB ea))
       (TT.conv-cong-App-fun dA' dB' cc da')

lift-ConvTm (RT.conv-cong-App-arg dA dB dc da dS) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      wf = TM.isType-WfCtx dA'
      mkTmIn c' ec dc' = tmIn (lift-HasType dc) wf e (TT.is-Pi dA' dB') (Eq-cong2 R.Pi eA eB)
      mkCTmIn aL aR eaL eaR ca = ctmIn (lift-ConvTm da) wf e dA' eA
      mkCTyIn SL SR eSL eSR cS = ctyIn (lift-ConvTy dS) wf e
      dL  = TM.subst-IsType (TM.subst1-WtSub dA' (TM.presup-l-ConvTm ca)) wf dB'
      dR  = TM.subst-IsType (TM.subst1-WtSub dA' (TM.presup-r-ConvTm ca)) wf dB'
      eL' = Eq-trans (E.erase-subst1 B' aL) (Eq-cong2 R.subst1 eB eaL)
      eR' = Eq-trans (E.erase-subst1 B' aR) (Eq-cong2 R.subst1 eB eaR)
      cBa = bridge-ConvTy cS dL dR (Eq-trans eL' (Eq-sym eSL)) (Eq-trans eSR (Eq-sym eR'))
  in mkLiftConvTm H (T.App A' B' c' aL) (T.App A' B' c' aR) (T.subst1 B' aL) e
       (Eq-cong4 R.App eA eB ec eaL) (Eq-cong4 R.App eA eB ec eaR) eL'
       (TT.conv-cong-App-arg dA' dB' dc' ca cBa)

lift-ConvTm (RT.conv-cong-App-Ty _ _ cA cB dc da) =
  let mkPiCIn H e AL AR eAL eAR cA' BL BR eBL eBR cB' = piCIn (lift-ConvTy cA) (lift-ConvTy cB)
      dAL = TM.presup-l-ConvTy cA'
      wf  = TM.isType-WfCtx dAL
      mkTmIn c' ec dc' = tmIn (lift-HasType dc) wf e (TT.is-Pi dAL (TM.presup-l-ConvTy cB')) (Eq-cong2 R.Pi eAL eBL)
      mkTmIn a' ea da' = tmIn (lift-HasType da) wf e dAL eAL
  in mkLiftConvTm H (T.App AL BL c' a') (T.App AR BR c' a') (T.subst1 BL a') e
       (Eq-cong4 R.App eAL eBL ec ea) (Eq-cong4 R.App eAR eBR ec ea)
       (Eq-trans (E.erase-subst1 BL a') (Eq-cong2 R.subst1 eBL ea))
       (TM.mk-conv-cong-App-Ty cA' cB' dc' da')

lift-ConvTm (RT.conv-beta dA dB db da) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      wf = TM.isType-WfCtx dA'
      mkTmIn b' eb db' = tmIn (lift-HasType db) (TT.wf-extend dA') (Eq-cong2 RT.extend e eA) dB' eB
      mkTmIn a' ea da' = tmIn (lift-HasType da) wf e dA' eA
  in mkLiftConvTm H (T.App A' B' (T.Lam A' B' b') a') (T.subst1 b' a') (T.subst1 B' a') e
       (Eq-cong4 R.App eA eB (Eq-cong3 R.Lam eA eB eb) ea)
       (Eq-trans (E.erase-subst1 b' a') (Eq-cong2 R.subst1 eb ea))
       (Eq-trans (E.erase-subst1 B' a') (Eq-cong2 R.subst1 eB ea))
       (TT.conv-beta dA' dB' db' da')

lift-ConvTm (RT.conv-cong-GLam {c = c} dG dA _ dtt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfc = TR.wkC-WfCtx c wf
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) wfc (eC H c e)
      mkCTmIn tL tR etL etR ct = ctmIn (lift-ConvTm dtt) wfc (eC H c e) dA' eA
  in mkLiftConvTm H (T.GLam c A' tL) (T.GLam c A' tR) (T.Grd c A') e
       (Eq-cong2 (R.GLam c) eA etL) (Eq-cong2 (R.GLam c) eA etR) (Eq-cong (R.Grd c) eA)
       (TT.conv-cong-GLam wf dA' (TM.presup-l-ConvTm ct) ct)

lift-ConvTm (RT.conv-GLam-eta {c = c} dG dA dt _) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TR.wkC-WfCtx c wf) (eC H c e)
      mkTmIn t' et dt' = tmIn (lift-HasType dt) wf e (TT.is-Grd wf dA') (Eq-cong (R.Grd c) eA)
      vc  = Eq-transport (\ X -> ValidC X c) (Eq-sym (TT.lctx-addC H c)) (validC-top c)
      dtc = TT.ty-conv (TR.wkC-HasType c dt') (TT.conv-Ty-Grd-beta vc dA')
  in mkLiftConvTm H t' (T.GLam c A' t') (T.Grd c A') e et (Eq-cong2 (R.GLam c) eA et) (Eq-cong (R.Grd c) eA)
       (TT.conv-GLam-eta wf dA' dt' dtc)

lift-ConvTm (RT.conv-GLam-beta {c = c} v dA dt) =
  let mkLiftIsType H A' e eA dA' = lift-IsType dA
      mkTmIn t' et dt' = tmIn (lift-HasType dt) (TM.isType-WfCtx dA') e dA' eA
  in mkLiftConvTm H (T.GLam c A' t') t' A' e (Eq-cong2 (R.GLam c) eA et) et eA
       (TT.conv-GLam-beta (lvl H e {\ X -> ValidC X c} v) dA' dt')

lift-ConvTm (RT.conv-cong-LLam dG dA _ duu) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfl = TM.wkL-WfCtx wf
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) wfl (eL H e)
      mkCTmIn uL uR euL euR cu = ctmIn (lift-ConvTm duu) wfl (eL H e) dA' eA
  in mkLiftConvTm H (T.LLam A' uL) (T.LLam A' uR) (T.LPi A') e
       (Eq-cong2 R.LLam eA euL) (Eq-cong2 R.LLam eA euR) (Eq-cong R.LPi eA)
       (TT.conv-cong-LLam wf dA' (TM.presup-l-ConvTm cu) cu)

lift-ConvTm (RT.conv-cong-GLam-Ty {c = c} dG _ dAA dt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfc = TR.wkC-WfCtx c wf
      mkCTyIn AL AR eAL eAR cA = ctyIn (lift-ConvTy dAA) wfc (eC H c e)
      mkTmIn t' et dt' = tmIn (lift-HasType dt) wfc (eC H c e) (TM.presup-l-ConvTy cA) eAL
  in mkLiftConvTm H (T.GLam c AL t') (T.GLam c AR t') (T.Grd c AL) e
       (Eq-cong2 (R.GLam c) eAL et) (Eq-cong2 (R.GLam c) eAR et) (Eq-cong (R.Grd c) eAL)
       (TT.conv-cong-GLam-Ty wf (TM.presup-l-ConvTy cA) cA dt')

lift-ConvTm (RT.conv-cong-LLam-Ty dG _ dAA du) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfl = TM.wkL-WfCtx wf
      mkCTyIn AL AR eAL eAR cA = ctyIn (lift-ConvTy dAA) wfl (eL H e)
      mkTmIn u' eu du' = tmIn (lift-HasType du) wfl (eL H e) (TM.presup-l-ConvTy cA) eAL
  in mkLiftConvTm H (T.LLam AL u') (T.LLam AR u') (T.LPi AL) e
       (Eq-cong2 R.LLam eAL eu) (Eq-cong2 R.LLam eAR eu) (Eq-cong R.LPi eAL)
       (TT.conv-cong-LLam-Ty wf (TM.presup-l-ConvTy cA) cA du')

lift-ConvTm (RT.conv-cong-LApp-Ty {l = l} _ dAA dt) =
  let IH = lift-HasType dt
      mkBase H e wf = bH IH
      mkCTyIn AL AR eAL eAR cA = ctyIn (lift-ConvTy dAA) (TM.wkL-WfCtx wf) (eL H e)
      dAL = TM.presup-l-ConvTy cA
      mkTmIn t' et dt' = tmIn IH wf e (TT.is-LPi wf dAL) (Eq-cong R.LPi eAL)
  in mkLiftConvTm H (T.LApp AL t' l) (T.LApp AR t' l) (T.lsub1 AL l) e
       (Eq-cong2 (\ X Y -> R.LApp X Y l) eAL et) (Eq-cong2 (\ X Y -> R.LApp X Y l) eAR et)
       (Eq-trans (E.erase-lsub1 AL l) (Eq-cong (\ X -> R.lsub1 X l) eAL))
       (TT.conv-cong-LApp-Ty dAL cA dt')

lift-ConvTm (RT.conv-cong-LApp-fun {l = l} dA dtt) =
  let IH = lift-ConvTm dtt
      mkBase H e wf = bCm IH
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TM.wkL-WfCtx wf) (eL H e)
      mkCTmIn tL tR etL etR ct = ctmIn IH wf e (TT.is-LPi wf dA') (Eq-cong R.LPi eA)
  in mkLiftConvTm H (T.LApp A' tL l) (T.LApp A' tR l) (T.lsub1 A' l) e
       (Eq-cong2 (\ X Y -> R.LApp X Y l) eA etL) (Eq-cong2 (\ X Y -> R.LApp X Y l) eA etR)
       (Eq-trans (E.erase-lsub1 A' l) (Eq-cong (\ X -> R.lsub1 X l) eA))
       (TT.conv-cong-LApp-fun dA' ct)

lift-ConvTm (RT.conv-cong-LApp-lvl {l = l} {l' = l'} dA dt v dS) =
  let IH = lift-HasType dt
      mkBase H e wf = bH IH
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TM.wkL-WfCtx wf) (eL H e)
      mkTmIn t' et dt' = tmIn IH wf e (TT.is-LPi wf dA') (Eq-cong R.LPi eA)
      mkCTyIn SL SR eSL eSR cS = ctyIn (lift-ConvTy dS) wf e
      dL  = TL.lsub-IsType (TL.lsk-inst H l) (TL.lok-inst H l) dA'
      dR  = TL.lsub-IsType (TL.lsk-inst H l') (TL.lok-inst H l') dA'
      eL' = Eq-trans (E.erase-lsub1 A' l) (Eq-cong (\ X -> R.lsub1 X l) eA)
      eR' = Eq-trans (E.erase-lsub1 A' l') (Eq-cong (\ X -> R.lsub1 X l') eA)
      cAl = bridge-ConvTy cS dL dR (Eq-trans eL' (Eq-sym eSL)) (Eq-trans eSR (Eq-sym eR'))
  in mkLiftConvTm H (T.LApp A' t' l) (T.LApp A' t' l') (T.lsub1 A' l) e
       (Eq-cong2 (\ X Y -> R.LApp X Y l) eA et) (Eq-cong2 (\ X Y -> R.LApp X Y l') eA et) eL'
       (TT.conv-cong-LApp-lvl dA' dt' (lvl H e {\ X -> Valid X l l'} v) cAl)

lift-ConvTm (RT.conv-GLam-equiv {c = c} {c' = c'} dG q dA dt) =
  let mkBase H e wf = bW (lift-WfCtx dG)
      wfc = TR.wkC-WfCtx c wf
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) wfc (eC H c e)
      mkTmIn t' et dt' = tmIn (lift-HasType dt) wfc (eC H c e) dA' eA
  in mkLiftConvTm H (T.GLam c A' t') (T.GLam c' A' t') (T.Grd c A') e
       (Eq-cong2 (R.GLam c) eA et) (Eq-cong2 (R.GLam c') eA et) (Eq-cong (R.Grd c) eA)
       (TT.conv-GLam-equiv wf (lvl H e {\ X -> EquivC X c c'} q) dA' dt')

-- all premises live under the level binder: leave it with unL
lift-ConvTm (RT.conv-LApp-beta {G = G} {l = l} dA du) =
  let IH = lift-IsType dA
      mkLiftIsType D _ eD _ dD = IH
      H   = unL D
      e   = unL-erase D G eD
      wf  = unL-WfCtx (TM.isType-WfCtx dD)
      wfl = TM.wkL-WfCtx wf
      mkTyIn A' eA dA' = tyIn IH wfl (eL H e)
      mkTmIn u' eu du' = tmIn (lift-HasType du) wfl (eL H e) dA' eA
  in mkLiftConvTm H (T.LApp A' (T.LLam A' u') l) (T.lsub1 u' l) (T.lsub1 A' l) e
       (Eq-cong2 (\ X Y -> R.LApp X Y l) eA (Eq-cong2 R.LLam eA eu))
       (Eq-trans (E.erase-lsub1 u' l) (Eq-cong (\ X -> R.lsub1 X l) eu))
       (Eq-trans (E.erase-lsub1 A' l) (Eq-cong (\ X -> R.lsub1 X l) eA))
       (TT.conv-LApp-beta dA' du')

lift-ConvTm (RT.conv-LApp-eta dA dt) =
  let IH = lift-HasType dt
      mkBase H e wf = bH IH
      mkTyIn A' eA dA' = tyIn (lift-IsType dA) (TM.wkL-WfCtx wf) (eL H e)
      mkTmIn t' et dt' = tmIn IH wf e (TT.is-LPi wf dA') (Eq-cong R.LPi eA)
      eBody = Eq-cong2 (\ X Y -> R.LApp X Y (lvar zero))
                (Eq-trans (E.erase-lsub (liftL lwkS) A') (Eq-cong (R.lsubE (liftL lwkS)) eA))
                (Eq-trans (E.erase-lshift t') (Eq-cong R.lshiftE et))
  in mkLiftConvTm H t' (T.LLam A' (T.LApp (T.lsubE (liftL lwkS) A') (T.lshiftE t') (lvar zero))) (T.LPi A') e
       et (Eq-cong2 R.LLam eA eBody) (Eq-cong R.LPi eA)
       (TT.conv-LApp-eta dA' dt')

lift-ConvTm (RT.conv-collapse lp dA dt) =
  let mkLiftIsType H A' e eA dA' = lift-IsType dA
      mkTmIn t' et dt' = tmIn (lift-HasType dt) (TM.isType-WfCtx dA') e dA' eA
  in mkLiftConvTm H t' T.Emp A' e et refl eA (TT.conv-collapse (lvl H e {Loop} lp) dA' dt')

lift-ConvTm (RT.conv-eta dA dB dc) =
  let mkPiIn H e A' eA dA' B' eB dB' = piIn (lift-IsType dA) (lift-IsType dB)
      mkTmIn c' ec dc' = tmIn (lift-HasType dc) (TM.isType-WfCtx dA') e (TT.is-Pi dA' dB') (Eq-cong2 R.Pi eA eB)
      eBody = Eq-trans (Eq-cong4 R.App (E.erase-wk A') (E.erase-ren (liftRen wkRen) B') (E.erase-wk c') refl)
                (Eq-cong4 R.App (Eq-cong R.wkExpr eA) (Eq-cong (R.renExpr (liftRen wkRen)) eB)
                   (Eq-cong R.wkExpr ec) refl)
  in mkLiftConvTm H c'
       (T.Lam A' B' (T.App (T.wkExpr A') (T.renExpr (liftRen wkRen) B') (T.wkExpr c') (T.Var fzero)))
       (T.Pi A' B') e ec (Eq-cong3 R.Lam eA eB eBody) (Eq-cong2 R.Pi eA eB)
       (TT.conv-eta dA' dB' dc')

------------------------------------------------------------------------
-- The equivalence (paper §4): erasure is sound (Lemma 4.6), has a
-- section (Theorem 4.13), and is injective up to conversion (Lemma 4.10)
------------------------------------------------------------------------

record Equivalence : Set₁ where
  field
    sound-WfCtx   : {n : Nat} {G : TT.Ctx n}
                  -> TT.WfCtx G -> RT.WfCtx (eraseCtx G)
    sound-IsType  : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
                  -> TT.IsType G A -> RT.IsType (eraseCtx G) (E.erase A)
    sound-HasType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
                  -> TT.HasType G M A
                  -> RT.HasType (eraseCtx G) (E.erase M) (E.erase A)
    sound-ConvTy  : {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
                  -> TT.ConvTy G A B -> RT.ConvTy (eraseCtx G) (E.erase A) (E.erase B)
    sound-ConvTm  : {n : Nat} {G : TT.Ctx n} {M N A : T.Expr n}
                  -> TT.ConvTm G M N A
                  -> RT.ConvTm (eraseCtx G) (E.erase M) (E.erase N) (E.erase A)
    lifts-WfCtx   : {n : Nat} {G : RT.Ctx n} -> RT.WfCtx G -> LiftWfCtx G
    lifts-IsType  : {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
                  -> RT.IsType G A -> LiftIsType G A
    lifts-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
                  -> RT.HasType G M A -> LiftHasType G M A
    lifts-ConvTy  : {n : Nat} {G : RT.Ctx n} {A B : R.Expr n}
                  -> RT.ConvTy G A B -> LiftConvTy G A B
    lifts-ConvTm  : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n}
                  -> RT.ConvTm G M N A -> LiftConvTm G M N A
    uniq-Ty : {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
            -> TT.IsType G A -> TT.IsType G B -> Eq (E.erase A) (E.erase B) -> TT.ConvTy G A B
    uniq-Tm : {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ : T.Expr n}
            -> TT.HasType G u₀ A₀ -> TT.HasType G u₁ A₁ -> Eq (E.erase u₀) (E.erase u₁)
            -> Result G u₀ u₁ A₀ A₁

equivalence : Equivalence
equivalence = record
  { sound-WfCtx   = erase-WfCtx
  ; sound-IsType  = erase-IsType
  ; sound-HasType = erase-HasType
  ; sound-ConvTy  = erase-ConvTy
  ; sound-ConvTm  = erase-ConvTm
  ; lifts-WfCtx   = lift-WfCtx
  ; lifts-IsType  = lift-IsType
  ; lifts-HasType = lift-HasType
  ; lifts-ConvTy  = lift-ConvTy
  ; lifts-ConvTm  = lift-ConvTm
  ; uniq-Ty       = type-uniq
  ; uniq-Tm       = term-uniq
  }
