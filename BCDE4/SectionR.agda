{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.SectionR  —  Theorem 4.19 (section of strip) for BCDE
--
--   If Γ ⊢ J in T_P, then there is Γ' ⊢ J' in T_R with strip(Γ') = Γ and
--   strip(J') = J, unique up to conversion.
--
-- The judgement lifts into EVERY well-formed T_R context Γ' over Γ
-- (lift-*), by structural induction on the T_P derivation (Sterbac's
-- SectionR): the annotations are read off the premises, and premises
-- that share a stripped term / type are reconciled by Lemma 4.18
-- (BCDE4.StripUniqNF).  Under ⟨ψ⟩ / ⟨α⟩ the lift goes into Γ',ψ / Γ',α.
-- Uniqueness up to conversion is Lemma 4.18 itself.
------------------------------------------------------------------------

module BCDE4.SectionR where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.RussellMetaCong using (subst1-cong-Ty)
open import BCDE4.RussellRelevel using (wkC-WfCtx)
open import BCDE4.RussellLsub using (lsub-IsType ; lsk-inst ; lok-inst)
open import BCDE4.Model.Strip using (strip ; stripCtx ; strip-subst1 ; strip-wk ; strip-lookup ; strip-lsubE ; strip-lctx)
import BCDE4.Model.Core as C
import BCDE4.PTyping as P
open import BCDE4.StripDeriv using (strip-addC ; strip-addL)
open import BCDE4.Coerce using (unguard-HasType)
open import BCDE4.StripUniqNF

------------------------------------------------------------------------
-- T_P: the context of a judgement is well formed
------------------------------------------------------------------------

mutual
  pwf-Ty : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A -> P.WfCtx G
  pwf-Ty (P.is-Ty-from-U d) = pwf-Tm d
  pwf-Ty (P.is-Pi dA _)     = pwf-Ty dA
  pwf-Ty (P.is-Grd wf _)    = wf
  pwf-Ty (P.is-LPi wf _)    = wf

  pwf-Tm : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A -> P.WfCtx G
  pwf-Tm (P.ty-GLam wf _ _)     = wf
  pwf-Tm (P.ty-LLam wf _ _)     = wf
  pwf-Tm (P.ty-LApp _ dt)       = pwf-Tm dt
  pwf-Tm (P.ty-Emp wf)          = wf
  pwf-Tm (P.ty-collapse _ dA)   = pwf-Ty dA
  pwf-Tm (P.ty-var wf)          = wf
  pwf-Tm (P.ty-conv d _)        = pwf-Tm d
  pwf-Tm (P.ty-U wf _)          = wf
  pwf-Tm (P.ty-cum d _)         = pwf-Tm d
  pwf-Tm (P.ty-Pi dA _)         = pwf-Tm dA
  pwf-Tm (P.ty-Lam dA _ _)      = pwf-Ty dA
  pwf-Tm (P.ty-App dA _ _ _)    = pwf-Ty dA

------------------------------------------------------------------------
-- Small syntactic facts
------------------------------------------------------------------------

private
  strip-U-inv : {n : Nat} {l : LExpr} (T : Expr n) -> Eq (strip T) (C.U l) -> Eq T (U l)
  strip-U-inv (U k)          refl = refl
  strip-U-inv (Var _)        ()
  strip-U-inv (Pi _ _)       ()
  strip-U-inv (Lam _ _ _)    ()
  strip-U-inv (App _ _ _ _)  ()
  strip-U-inv (Grd _ _)      ()
  strip-U-inv (GLam _ _ _)   ()
  strip-U-inv Emp            ()
  strip-U-inv (LPi _)        ()
  strip-U-inv (LLam _ _)     ()
  strip-U-inv (LApp _ _ _)   ()

  ext-eq : {n : Nat} {G G' : C.Ctx n} {A A' : C.Expr n} -> Eq G G' -> Eq A A' -> Eq (C.extend G A) (C.extend G' A')
  ext-eq refl refl = refl

  cong2 : {X Y Z : Set} (f : X -> Y -> Z) {x x' : X} {y y' : Y} -> Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
  cong2 f refl refl = refl

  atU : {n : Nat} {G : Ctx n} {M T : Expr n} {l : LExpr} -> Eq (strip T) (C.U l) -> HasType G M T -> HasType G M (U l)
  atU {T = T} e d = Eq-transport (HasType _ _) (strip-U-inv T e) d

  atU-C : {n : Nat} {G : Ctx n} {M N T : Expr n} {l : LExpr} -> Eq (strip T) (C.U l) -> ConvTm G M N T -> ConvTm G M N (U l)
  atU-C {T = T} e d = Eq-transport (ConvTm _ _ _) (strip-U-inv T e) d

  -- the level part of a lift is the level part of the T_P context
  lvR : {n : Nat} {G' : Ctx n} {G : C.Ctx n} -> Eq (stripCtx G') G -> {Q : LCtx -> Set} -> Q (C.lctx G) -> Q (lctx G')
  lvR {G' = G'} refl {Q} q = Eq-transport Q (strip-lctx G') q

  -- Γ',ψ and Γ',α over Γ,ψ and Γ,α
  eC : {n : Nat} {G' : Ctx n} {G : C.Ctx n} (c : Constr) -> Eq (stripCtx G') G -> Eq (stripCtx (addC G' c)) (P.addC G c)
  eC {G' = G'} c refl = strip-addC G' c

  eL : {n : Nat} {G' : Ctx n} {G : C.Ctx n} -> Eq (stripCtx G') G -> Eq (stripCtx (addL G')) (P.addL G)
  eL {G' = G'} refl = strip-addL G'

  sl1 : {n : Nat} (A' : Expr n) {A : C.Expr n} (l : LExpr) -> Eq (strip A') A -> Eq (strip (lsub1 A' l)) (C.lsub1 A l)
  sl1 A' l e = Eq-trans (strip-lsubE (lsub1S l) A') (Eq-cong (\ X -> C.lsub1 X l) e)

------------------------------------------------------------------------
-- Lifts into a given T_R context
------------------------------------------------------------------------

record LTy {n : Nat} (G' : Ctx n) (A : C.Expr n) : Set where
  constructor mkLTy
  field
    A' : Expr n
    eA : Eq (strip A') A
    d  : IsType G' A'

record LTm {n : Nat} (G' : Ctx n) (M A : C.Expr n) : Set where
  constructor mkLTm
  field
    M' : Expr n
    A' : Expr n
    eM : Eq (strip M') M
    eA : Eq (strip A') A
    d  : HasType G' M' A'

record LCTy {n : Nat} (G' : Ctx n) (A B : C.Expr n) : Set where
  constructor mkLCTy
  field
    A' : Expr n
    B' : Expr n
    eA : Eq (strip A') A
    eB : Eq (strip B') B
    d  : ConvTy G' A' B'

record LCTm {n : Nat} (G' : Ctx n) (M N A : C.Expr n) : Set where
  constructor mkLCTm
  field
    M' : Expr n
    N' : Expr n
    A' : Expr n
    eM : Eq (strip M') M
    eN : Eq (strip N') N
    eA : Eq (strip A') A
    d  : ConvTm G' M' N' A'

private
  -- a lifted term moved to another lift of its type
  retype : {n : Nat} {G' : Ctx n} {M A : C.Expr n} (r : LTm G' M A) {T : Expr n} ->
    IsType G' T -> Eq (strip T) A -> HasType G' (LTm.M' r) T
  retype r dT eT =
    ty-conv (LTm.d r) (type-uniq-NF (typing-IsType (LTm.d r)) dT (Eq-trans (LTm.eA r) (Eq-sym eT)))

  retypeC : {n : Nat} {G' : Ctx n} {M N A : C.Expr n} (r : LCTm G' M N A) {T : Expr n} ->
    IsType G' T -> Eq (strip T) A -> ConvTm G' (LCTm.M' r) (LCTm.N' r) T
  retypeC r dT eT =
    conv-conv (LCTm.d r)
      (type-uniq-NF (typing-IsType (presup-l-ConvTm (LCTm.d r))) dT (Eq-trans (LCTm.eA r) (Eq-sym eT)))

  -- two lifts of the same term at the same type are convertible
  same : {n : Nat} {G' : Ctx n} {X Y T : Expr n} -> HasType G' X T -> HasType G' Y T ->
    Eq (strip X) (strip Y) -> ConvTm G' X Y T
  same dX dY e = term-uniq-conv-NF dX dY e (conv-Ty-refl (typing-IsType dX))

  -- two lifts of the same type are convertible
  sameTy : {n : Nat} {G' : Ctx n} {X Y : Expr n} {A : C.Expr n} -> IsType G' X -> IsType G' Y ->
    Eq (strip X) A -> Eq (strip Y) A -> ConvTy G' X Y
  sameTy dX dY eX eY = type-uniq-NF dX dY (Eq-trans eX (Eq-sym eY))

  -- a lifted conversion, starting from a given lift of its left side
  fromL : {n : Nat} {G' : Ctx n} {A B : C.Expr n} {X : Expr n} -> IsType G' X -> Eq (strip X) A ->
    (q : LCTy G' A B) -> ConvTy G' X (LCTy.B' q)
  fromL dX eX q = conv-Ty-trans (sameTy dX (presup-l-ConvTy (LCTy.d q)) eX (LCTy.eA q)) (LCTy.d q)

  fromLm : {n : Nat} {G' : Ctx n} {M N A : C.Expr n} {X T : Expr n} -> HasType G' X T -> Eq (strip X) M ->
    IsType G' T -> Eq (strip T) A -> (q : LCTm G' M N A) -> ConvTm G' X (LCTm.N' q) T
  fromLm dX eX dT eT q =
    let cq = retypeC q dT eT
    in conv-trans (same dX (presup-l-ConvTm cq) (Eq-trans eX (Eq-sym (LCTm.eM q)))) cq

mutual

  lift-IsType : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A ->
    (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LTy G' A
  lift-IsType (P.is-Ty-from-U d) G' wf e =
    let r = lift-HasType d G' wf e
    in mkLTy (LTm.M' r) (LTm.eM r) (is-Ty-from-U (atU (LTm.eA r) (LTm.d r)))
  lift-IsType (P.is-Pi dA dB) G' wf e =
    let a = lift-IsType dA G' wf e
        b = lift-IsType dB (extend G' (LTy.A' a)) (wf-extend (LTy.d a)) (ext-eq e (LTy.eA a))
    in mkLTy (Pi (LTy.A' a) (LTy.A' b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b)) (is-Pi (LTy.d a) (LTy.d b))
  lift-IsType (P.is-Grd {c = c} _ dA) G' wf e =
    let a = lift-IsType dA (addC G' c) (wkC-WfCtx c wf) (eC c e)
    in mkLTy (Grd c (LTy.A' a)) (Eq-cong (C.Grd c) (LTy.eA a)) (is-Grd wf (LTy.d a))
  lift-IsType (P.is-LPi _ dA) G' wf e =
    let a = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
    in mkLTy (LPi (LTy.A' a)) (Eq-cong C.LPi (LTy.eA a)) (is-LPi wf (LTy.d a))

  lift-HasType : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A ->
    (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LTm G' M A
  lift-HasType (P.ty-GLam {c = c} _ dA dt) G' wf e =
    let G1 = addC G' c ; wf1 = wkC-WfCtx c wf ; e1 = eC c e
        a  = lift-IsType dA G1 wf1 e1
        t  = lift-HasType dt G1 wf1 e1
    in mkLTm (GLam c (LTy.A' a) (LTm.M' t)) (Grd c (LTy.A' a)) (Eq-cong (C.GLam c) (LTm.eM t)) (Eq-cong (C.Grd c) (LTy.eA a))
         (ty-GLam wf (LTy.d a) (retype t (LTy.d a) (LTy.eA a)))
  lift-HasType (P.ty-LLam _ dA du) G' wf e =
    let G1 = addL G' ; wf1 = wkL-WfCtx wf ; e1 = eL e
        a  = lift-IsType dA G1 wf1 e1
        u  = lift-HasType du G1 wf1 e1
    in mkLTm (LLam (LTy.A' a) (LTm.M' u)) (LPi (LTy.A' a)) (Eq-cong C.LLam (LTm.eM u)) (Eq-cong C.LPi (LTy.eA a))
         (ty-LLam wf (LTy.d a) (retype u (LTy.d a) (LTy.eA a)))
  lift-HasType (P.ty-LApp {l = l} dA dt) G' wf e =
    let a  = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
        t  = lift-HasType dt G' wf e
        dt' = retype t (is-LPi wf (LTy.d a)) (Eq-cong C.LPi (LTy.eA a))
    in mkLTm (LApp (LTy.A' a) (LTm.M' t) l) (lsub1 (LTy.A' a) l) (Eq-cong (\ X -> C.LApp X l) (LTm.eM t))
         (sl1 (LTy.A' a) l (LTy.eA a)) (ty-LApp (LTy.d a) dt')
  lift-HasType (P.ty-Emp {l = l} _) G' wf e = mkLTm Emp (U l) refl refl (ty-Emp wf)
  lift-HasType (P.ty-collapse lp dA) G' wf e =
    let a = lift-IsType dA G' wf e
    in mkLTm Emp (LTy.A' a) refl (LTy.eA a) (ty-collapse (lvR e {Loop} lp) (LTy.d a))
  lift-HasType (P.ty-var {i = i} _) G' wf e =
    mkLTm (Var i) (lookup G' i) refl
      (Eq-trans (strip-lookup G' i) (Eq-cong (\ X -> C.lookup X i) e)) (ty-var wf)
  lift-HasType (P.ty-conv d c) G' wf e =
    let r = lift-HasType d G' wf e
        q = lift-ConvTy c G' wf e
    in mkLTm (LTm.M' r) (LCTy.B' q) (LTm.eM r) (LCTy.eB q) (ty-conv (LTm.d r) (fromL (typing-IsType (LTm.d r)) (LTm.eA r) q))
  lift-HasType (P.ty-U {l = l} {m = m} _ lt) G' wf e =
    mkLTm (U l) (U m) refl refl (ty-U wf (lvR e {\ T -> LtL T l m} lt))
  lift-HasType (P.ty-cum {l = l} {m = m} d le) G' wf e =
    let r = lift-HasType d G' wf e
    in mkLTm (LTm.M' r) (U m) (LTm.eM r) refl (ty-cum (atU (LTm.eA r) (LTm.d r)) (lvR e {\ T -> LeL T l m} le))
  lift-HasType (P.ty-Pi {l = l} dA dB) G' wf e =
    let rA  = lift-HasType dA G' wf e
        dA' = atU (LTm.eA rA) (LTm.d rA)
        rB  = lift-HasType dB (extend G' (LTm.M' rA)) (wf-extend (is-Ty-from-U dA')) (ext-eq e (LTm.eM rA))
        dB' = atU (LTm.eA rB) (LTm.d rB)
    in mkLTm (Pi (LTm.M' rA) (LTm.M' rB)) (U l) (cong2 C.Pi (LTm.eM rA) (LTm.eM rB)) refl (ty-Pi dA' dB')
  lift-HasType (P.ty-Lam dA dB db) G' wf e =
    let a  = lift-IsType dA G' wf e
        G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b  = lift-IsType dB G1 wf1 e1
        t  = lift-HasType db G1 wf1 e1
    in mkLTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Pi (LTy.A' a) (LTy.A' b))
         (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
         (ty-Lam (LTy.d a) (LTy.d b) (retype t (LTy.d b) (LTy.eA b)))
  lift-HasType (P.ty-App dA dB dc da) G' wf e =
    let a  = lift-IsType dA G' wf e
        G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b  = lift-IsType dB G1 wf1 e1
        c  = lift-HasType dc G' wf e
        s  = lift-HasType da G' wf e
        dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
        da' = retype s (LTy.d a) (LTy.eA a)
    in mkLTm (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LTm.M' s)) (subst1 (LTy.A' b) (LTm.M' s))
         (cong2 C.App (LTm.eM c) (LTm.eM s))
         (Eq-trans (strip-subst1 (LTy.A' b) (LTm.M' s)) (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
         (ty-App (LTy.d a) (LTy.d b) dc' da')

  lift-ConvTy : {n : Nat} {G : C.Ctx n} {A B : C.Expr n} -> P.ConvTy G A B ->
    (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LCTy G' A B
  lift-ConvTy (P.conv-Ty-refl dA) G' wf e =
    let a = lift-IsType dA G' wf e in mkLCTy (LTy.A' a) (LTy.A' a) (LTy.eA a) (LTy.eA a) (conv-Ty-refl (LTy.d a))
  lift-ConvTy (P.conv-Ty-sym c) G' wf e =
    let q = lift-ConvTy c G' wf e in mkLCTy (LCTy.B' q) (LCTy.A' q) (LCTy.eB q) (LCTy.eA q) (conv-Ty-sym (LCTy.d q))
  lift-ConvTy (P.conv-Ty-trans c1 c2) G' wf e =
    let q1 = lift-ConvTy c1 G' wf e
        q2 = lift-ConvTy c2 G' wf e
    in mkLCTy (LCTy.A' q1) (LCTy.B' q2) (LCTy.eA q1) (LCTy.eB q2)
         (conv-Ty-trans (LCTy.d q1) (fromL (presup-r-ConvTy (LCTy.d q1)) (LCTy.eB q1) q2))
  lift-ConvTy (P.conv-Ty-Pi dA dB cA cB) G' wf e =
    let a  = lift-IsType dA G' wf e
        G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b  = lift-IsType dB G1 wf1 e1
        qA = lift-ConvTy cA G' wf e
        qB = lift-ConvTy cB G1 wf1 e1
    in mkLCTy (Pi (LTy.A' a) (LTy.A' b)) (Pi (LCTy.B' qA) (LCTy.B' qB))
         (cong2 C.Pi (LTy.eA a) (LTy.eA b)) (cong2 C.Pi (LCTy.eB qA) (LCTy.eB qB))
         (conv-Ty-Pi (LTy.d a) (LTy.d b) (fromL (LTy.d a) (LTy.eA a) qA) (fromL (LTy.d b) (LTy.eA b) qB))
  lift-ConvTy (P.conv-Ty-Grd {c = c} _ dA cAB) G' wf e =
    let G1 = addC G' c ; wf1 = wkC-WfCtx c wf ; e1 = eC c e
        a  = lift-IsType dA G1 wf1 e1
        q  = lift-ConvTy cAB G1 wf1 e1
    in mkLCTy (Grd c (LTy.A' a)) (Grd c (LCTy.B' q)) (Eq-cong (C.Grd c) (LTy.eA a)) (Eq-cong (C.Grd c) (LCTy.eB q))
         (conv-Ty-Grd wf (LTy.d a) (fromL (LTy.d a) (LTy.eA a) q))
  lift-ConvTy (P.conv-Ty-LPi _ dA cAB) G' wf e =
    let G1 = addL G' ; wf1 = wkL-WfCtx wf ; e1 = eL e
        a  = lift-IsType dA G1 wf1 e1
        q  = lift-ConvTy cAB G1 wf1 e1
    in mkLCTy (LPi (LTy.A' a)) (LPi (LCTy.B' q)) (Eq-cong C.LPi (LTy.eA a)) (Eq-cong C.LPi (LCTy.eB q))
         (conv-Ty-LPi wf (LTy.d a) (fromL (LTy.d a) (LTy.eA a) q))
  lift-ConvTy (P.conv-Ty-Grd-beta {c = c} v dA) G' wf e =
    let a = lift-IsType dA G' wf e
    in mkLCTy (Grd c (LTy.A' a)) (LTy.A' a) (Eq-cong (C.Grd c) (LTy.eA a)) (LTy.eA a)
         (conv-Ty-Grd-beta (lvR e {\ T -> ValidC T c} v) (LTy.d a))
  lift-ConvTy (P.conv-Ty-Grd-equiv {c = c} {c' = c'} _ q dA) G' wf e =
    let a = lift-IsType dA (addC G' c) (wkC-WfCtx c wf) (eC c e)
    in mkLCTy (Grd c (LTy.A' a)) (Grd c' (LTy.A' a)) (Eq-cong (C.Grd c) (LTy.eA a)) (Eq-cong (C.Grd c') (LTy.eA a))
         (conv-Ty-Grd-equiv wf (lvR e {\ T -> EquivC T c c'} q) (LTy.d a))
  lift-ConvTy (P.conv-Ty-collapse lp dA) G' wf e =
    let a = lift-IsType dA G' wf e
    in mkLCTy (LTy.A' a) Emp (LTy.eA a) refl (conv-Ty-collapse (lvR e {Loop} lp) (LTy.d a))
  lift-ConvTy (P.conv-Ty-from-U d) G' wf e =
    let q = lift-ConvTm d G' wf e
    in mkLCTy (LCTm.M' q) (LCTm.N' q) (LCTm.eM q) (LCTm.eN q) (conv-Ty-from-U (atU-C (LCTm.eA q) (LCTm.d q)))

  lift-ConvTm : {n : Nat} {G : C.Ctx n} {M N A : C.Expr n} -> P.ConvTm G M N A ->
    (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LCTm G' M N A
  lift-ConvTm (P.conv-refl d) G' wf e =
    let r = lift-HasType d G' wf e
    in mkLCTm (LTm.M' r) (LTm.M' r) (LTm.A' r) (LTm.eM r) (LTm.eM r) (LTm.eA r) (conv-refl (LTm.d r))
  lift-ConvTm (P.conv-sym d) G' wf e =
    let q = lift-ConvTm d G' wf e
    in mkLCTm (LCTm.N' q) (LCTm.M' q) (LCTm.A' q) (LCTm.eN q) (LCTm.eM q) (LCTm.eA q) (conv-sym (LCTm.d q))
  lift-ConvTm (P.conv-trans d1 d2) G' wf e =
    let q1 = lift-ConvTm d1 G' wf e
        q2 = lift-ConvTm d2 G' wf e
        u  = term-uniq-NF (presup-r-ConvTm (LCTm.d q1)) (presup-l-ConvTm (LCTm.d q2))
               (Eq-trans (LCTm.eN q1) (Eq-sym (LCTm.eM q2))) (Eq-trans (LCTm.eA q1) (Eq-sym (LCTm.eA q2)))
    in mkLCTm (LCTm.M' q1) (LCTm.N' q2) (LCTm.A' q1) (LCTm.eM q1) (LCTm.eN q2) (LCTm.eA q1)
         (conv-trans (LCTm.d q1) (conv-trans (snd u) (conv-conv (LCTm.d q2) (conv-Ty-sym (fst u)))))
  lift-ConvTm (P.conv-conv d c) G' wf e =
    let q  = lift-ConvTm d G' wf e
        cq = lift-ConvTy c G' wf e
    in mkLCTm (LCTm.M' q) (LCTm.N' q) (LCTy.B' cq) (LCTm.eM q) (LCTm.eN q) (LCTy.eB cq)
         (conv-conv (LCTm.d q) (fromL (typing-IsType (presup-l-ConvTm (LCTm.d q))) (LCTm.eA q) cq))
  lift-ConvTm (P.conv-cong-Pi {l = l} dA dB cA cB) G' wf e =
    let rA  = lift-HasType dA G' wf e
        dA' = atU (LTm.eA rA) (LTm.d rA)
        G1  = extend G' (LTm.M' rA) ; wf1 = wf-extend (is-Ty-from-U dA') ; e1 = ext-eq e (LTm.eM rA)
        rB  = lift-HasType dB G1 wf1 e1
        dB' = atU (LTm.eA rB) (LTm.d rB)
        qA  = lift-ConvTm cA G' wf e
        qB  = lift-ConvTm cB G1 wf1 e1
        wfU = isType-U {l = l} wf
        cA' = fromLm dA' (LTm.eM rA) wfU refl qA
        cB' = fromLm dB' (LTm.eM rB) (isType-U {l = l} wf1) refl qB
    in mkLCTm (Pi (LTm.M' rA) (LTm.M' rB)) (Pi (LCTm.N' qA) (LCTm.N' qB)) (U l)
         (cong2 C.Pi (LTm.eM rA) (LTm.eM rB)) (cong2 C.Pi (LCTm.eN qA) (LCTm.eN qB)) refl
         (conv-cong-Pi dA' dB' cA' cB')
  lift-ConvTm (P.conv-cum {l = l} {m = m} d le) G' wf e =
    let q = lift-ConvTm d G' wf e
    in mkLCTm (LCTm.M' q) (LCTm.N' q) (U m) (LCTm.eM q) (LCTm.eN q) refl
         (conv-cum (atU-C (LCTm.eA q) (LCTm.d q)) (lvR e {\ T -> LeL T l m} le))
  lift-ConvTm (P.conv-U-lvl {l = l} {l' = l'} {m = m} _ v lt) G' wf e =
    mkLCTm (U l) (U l') (U m) refl refl refl
      (conv-U-lvl wf (lvR e {\ T -> Valid T l l'} v) (lvR e {\ T -> LtL T l m} lt))
  lift-ConvTm (P.conv-cong-Lam-body dA dB db0 cb) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        t   = lift-HasType db0 G1 wf1 e1
        db' = retype t (LTy.d b) (LTy.eA b)
        qc  = lift-ConvTm cb G1 wf1 e1
    in mkLCTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Lam (LTy.A' a) (LTy.A' b) (LCTm.N' qc)) (Pi (LTy.A' a) (LTy.A' b))
         (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Lam (LTy.eA a) (LCTm.eN qc)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
         (conv-cong-Lam-body (LTy.d a) (LTy.d b) db' (fromLm db' (LTm.eM t) (LTy.d b) (LTy.eA b) qc))
  lift-ConvTm (P.conv-cong-Lam-dom dA dB cA db) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        qA  = lift-ConvTy cA G' wf e
        t   = lift-HasType db G1 wf1 e1
        db' = retype t (LTy.d b) (LTy.eA b)
    in mkLCTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Lam (LCTy.B' qA) (LTy.A' b) (LTm.M' t)) (Pi (LTy.A' a) (LTy.A' b))
         (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Lam (LCTy.eB qA) (LTm.eM t)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
         (conv-cong-Lam-Ty (LTy.d a) (LTy.d b) (fromL (LTy.d a) (LTy.eA a) qA) (conv-Ty-refl (LTy.d b)) db')
  lift-ConvTm (P.conv-cong-App-fun dA dB cc da) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        qc  = lift-ConvTm cc G' wf e
        cc' = retypeC qc (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
        s   = lift-HasType da G' wf e
        da' = retype s (LTy.d a) (LTy.eA a)
    in mkLCTm (App (LTy.A' a) (LTy.A' b) (LCTm.M' qc) (LTm.M' s)) (App (LTy.A' a) (LTy.A' b) (LCTm.N' qc) (LTm.M' s))
         (subst1 (LTy.A' b) (LTm.M' s))
         (cong2 C.App (LCTm.eM qc) (LTm.eM s)) (cong2 C.App (LCTm.eN qc) (LTm.eM s))
         (Eq-trans (strip-subst1 (LTy.A' b) (LTm.M' s)) (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
         (conv-cong-App-fun (LTy.d a) (LTy.d b) cc' da')
  lift-ConvTm (P.conv-cong-App-arg dA dB dc ca _) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        c   = lift-HasType dc G' wf e
        dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
        qa  = lift-ConvTm ca G' wf e
        ca' = retypeC qa (LTy.d a) (LTy.eA a)
    in mkLCTm (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LCTm.M' qa)) (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LCTm.N' qa))
         (subst1 (LTy.A' b) (LCTm.M' qa))
         (cong2 C.App (LTm.eM c) (LCTm.eM qa)) (cong2 C.App (LTm.eM c) (LCTm.eN qa))
         (Eq-trans (strip-subst1 (LTy.A' b) (LCTm.M' qa)) (cong2 C.subst1 (LTy.eA b) (LCTm.eM qa)))
         (conv-cong-App-arg (LTy.d a) (LTy.d b) dc' ca' (subst1-cong-Ty ca' (LTy.d a) (LTy.d b)))
  lift-ConvTm (P.conv-beta dA dB db da) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        t   = lift-HasType db G1 wf1 e1
        db' = retype t (LTy.d b) (LTy.eA b)
        s   = lift-HasType da G' wf e
        da' = retype s (LTy.d a) (LTy.eA a)
        A'  = LTy.A' a ; B' = LTy.A' b ; b' = LTm.M' t ; a' = LTm.M' s
    in mkLCTm (App A' B' (Lam A' B' b') a') (subst1 b' a') (subst1 B' a')
         (cong2 C.App (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (LTm.eM s))
         (Eq-trans (strip-subst1 b' a') (cong2 C.subst1 (LTm.eM t) (LTm.eM s)))
         (Eq-trans (strip-subst1 B' a') (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
         (conv-beta (LTy.d a) (LTy.d b) db' da')
  lift-ConvTm (P.conv-cong-GLam {c = c} _ dA dt ct) G' wf e =
    let G1  = addC G' c ; wf1 = wkC-WfCtx c wf ; e1 = eC c e
        a   = lift-IsType dA G1 wf1 e1
        t   = lift-HasType dt G1 wf1 e1
        dt' = retype t (LTy.d a) (LTy.eA a)
        qc  = lift-ConvTm ct G1 wf1 e1
    in mkLCTm (GLam c (LTy.A' a) (LTm.M' t)) (GLam c (LTy.A' a) (LCTm.N' qc)) (Grd c (LTy.A' a))
         (Eq-cong (C.GLam c) (LTm.eM t)) (Eq-cong (C.GLam c) (LCTm.eN qc)) (Eq-cong (C.Grd c) (LTy.eA a))
         (conv-cong-GLam wf (LTy.d a) dt' (fromLm dt' (LTm.eM t) (LTy.d a) (LTy.eA a) qc))
  lift-ConvTm (P.conv-GLam-beta {c = c} v dA dt) G' wf e =
    let a   = lift-IsType dA G' wf e
        t   = lift-HasType dt G' wf e
        dt' = retype t (LTy.d a) (LTy.eA a)
    in mkLCTm (GLam c (LTy.A' a) (LTm.M' t)) (LTm.M' t) (LTy.A' a) (Eq-cong (C.GLam c) (LTm.eM t)) (LTm.eM t) (LTy.eA a)
         (conv-GLam-beta (lvR e {\ T -> ValidC T c} v) (LTy.d a) dt')
  lift-ConvTm (P.conv-cong-LLam _ dA du cu) G' wf e =
    let G1  = addL G' ; wf1 = wkL-WfCtx wf ; e1 = eL e
        a   = lift-IsType dA G1 wf1 e1
        u   = lift-HasType du G1 wf1 e1
        du' = retype u (LTy.d a) (LTy.eA a)
        qc  = lift-ConvTm cu G1 wf1 e1
    in mkLCTm (LLam (LTy.A' a) (LTm.M' u)) (LLam (LTy.A' a) (LCTm.N' qc)) (LPi (LTy.A' a))
         (Eq-cong C.LLam (LTm.eM u)) (Eq-cong C.LLam (LCTm.eN qc)) (Eq-cong C.LPi (LTy.eA a))
         (conv-cong-LLam wf (LTy.d a) du' (fromLm du' (LTm.eM u) (LTy.d a) (LTy.eA a) qc))
  lift-ConvTm (P.conv-cong-LApp-fun {l = l} dA ct) G' wf e =
    let a   = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
        qc  = lift-ConvTm ct G' wf e
        cc' = retypeC qc (is-LPi wf (LTy.d a)) (Eq-cong C.LPi (LTy.eA a))
    in mkLCTm (LApp (LTy.A' a) (LCTm.M' qc) l) (LApp (LTy.A' a) (LCTm.N' qc) l) (lsub1 (LTy.A' a) l)
         (Eq-cong (\ X -> C.LApp X l) (LCTm.eM qc)) (Eq-cong (\ X -> C.LApp X l) (LCTm.eN qc)) (sl1 (LTy.A' a) l (LTy.eA a))
         (conv-cong-LApp-fun (LTy.d a) cc')
  lift-ConvTm (P.conv-cong-LApp-lvl {l = l} {l' = l'} dA dt v cA) G' wf e =
    let a   = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
        t   = lift-HasType dt G' wf e
        dt' = retype t (is-LPi wf (LTy.d a)) (Eq-cong C.LPi (LTy.eA a))
        q   = lift-ConvTy cA G' wf e
        A'  = LTy.A' a
        dAl  = lsub-IsType (lsk-inst G' l) (lok-inst G' l) (LTy.d a)
        dAl' = lsub-IsType (lsk-inst G' l') (lok-inst G' l') (LTy.d a)
        cL  = conv-Ty-trans (fromL dAl (sl1 A' l (LTy.eA a)) q)
                (sameTy (presup-r-ConvTy (LCTy.d q)) dAl' (LCTy.eB q) (sl1 A' l' (LTy.eA a)))
    in mkLCTm (LApp A' (LTm.M' t) l) (LApp A' (LTm.M' t) l') (lsub1 A' l)
         (Eq-cong (\ X -> C.LApp X l) (LTm.eM t)) (Eq-cong (\ X -> C.LApp X l') (LTm.eM t)) (sl1 A' l (LTy.eA a))
         (conv-cong-LApp-lvl (LTy.d a) dt' (lvR e {\ T -> Valid T l l'} v) cL)
  lift-ConvTm (P.conv-GLam-equiv {c = c} {c' = c'} _ q dA dt) G' wf e =
    let G1  = addC G' c ; wf1 = wkC-WfCtx c wf ; e1 = eC c e
        a   = lift-IsType dA G1 wf1 e1
        t   = lift-HasType dt G1 wf1 e1
        dt' = retype t (LTy.d a) (LTy.eA a)
    in mkLCTm (GLam c (LTy.A' a) (LTm.M' t)) (GLam c' (LTy.A' a) (LTm.M' t)) (Grd c (LTy.A' a))
         (Eq-cong (C.GLam c) (LTm.eM t)) (Eq-cong (C.GLam c') (LTm.eM t)) (Eq-cong (C.Grd c) (LTy.eA a))
         (conv-GLam-equiv wf (lvR e {\ T -> EquivC T c c'} q) (LTy.d a) dt')
  lift-ConvTm (P.conv-LApp-beta {l = l} dA du) G' wf e =
    let a   = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
        u   = lift-HasType du (addL G') (wkL-WfCtx wf) (eL e)
        du' = retype u (LTy.d a) (LTy.eA a)
        A'  = LTy.A' a ; u' = LTm.M' u
    in mkLCTm (LApp A' (LLam A' u') l) (lsub1 u' l) (lsub1 A' l)
         (Eq-cong (\ X -> C.LApp (C.LLam X) l) (LTm.eM u)) (sl1 u' l (LTm.eM u)) (sl1 A' l (LTy.eA a))
         (conv-LApp-beta (LTy.d a) du')
  lift-ConvTm (P.conv-LApp-eta dA dt) G' wf e =
    let a   = lift-IsType dA (addL G') (wkL-WfCtx wf) (eL e)
        t   = lift-HasType dt G' wf e
        dt' = retype t (is-LPi wf (LTy.d a)) (Eq-cong C.LPi (LTy.eA a))
        A'  = LTy.A' a ; t' = LTm.M' t
    in mkLCTm t' (LLam A' (LApp (lsubE (liftL lwkS) A') (lshiftE t') (lvar zero))) (LPi A')
         (LTm.eM t)
         (Eq-cong (\ X -> C.LLam (C.LApp X (lvar zero)))
            (Eq-trans (strip-lsubE lwkS t') (Eq-cong C.lshiftE (LTm.eM t))))
         (Eq-cong C.LPi (LTy.eA a))
         (conv-LApp-eta (LTy.d a) dt')
  lift-ConvTm (P.conv-GLam-eta {c = c} _ dA dt _) G' wf e =
    let a   = lift-IsType dA (addC G' c) (wkC-WfCtx c wf) (eC c e)
        t   = lift-HasType dt G' wf e
        dt' = retype t (is-Grd wf (LTy.d a)) (Eq-cong (C.Grd c) (LTy.eA a))
        A'  = LTy.A' a ; t' = LTm.M' t
    in mkLCTm t' (GLam c A' t') (Grd c A') (LTm.eM t) (Eq-cong (C.GLam c) (LTm.eM t)) (Eq-cong (C.Grd c) (LTy.eA a))
         (conv-GLam-eta wf (LTy.d a) dt' (unguard-HasType (LTy.d a) dt'))
  lift-ConvTm (P.conv-collapse lp dA dt) G' wf e =
    let a   = lift-IsType dA G' wf e
        t   = lift-HasType dt G' wf e
        dt' = retype t (LTy.d a) (LTy.eA a)
    in mkLCTm (LTm.M' t) Emp (LTy.A' a) (LTm.eM t) refl (LTy.eA a)
         (conv-collapse (lvR e {Loop} lp) (LTy.d a) dt')
  lift-ConvTm (P.conv-eta dA dB dc) G' wf e =
    let a   = lift-IsType dA G' wf e
        G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
        b   = lift-IsType dB G1 wf1 e1
        c   = lift-HasType dc G' wf e
        dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
        A'  = LTy.A' a ; B' = LTy.A' b ; c' = LTm.M' c
    in mkLCTm c' (Lam A' B' (App (wkExpr A') (renExpr (liftRen wkRen) B') (wkExpr c') (Var fzero))) (Pi A' B')
         (LTm.eM c)
         (cong2 C.Lam (LTy.eA a)
            (Eq-cong (\ X -> C.App X (C.Var fzero)) (Eq-trans (strip-wk c') (Eq-cong C.wkExpr (LTm.eM c)))))
         (cong2 C.Pi (LTy.eA a) (LTy.eA b))
         (conv-eta (LTy.d a) (LTy.d b) dc')

------------------------------------------------------------------------
-- Contexts: every well-formed T_P context has a well-formed lift
------------------------------------------------------------------------

record LiftCtx {n : Nat} (G : C.Ctx n) : Set where
  constructor mkLiftCtx
  field
    G'  : Ctx n
    eG  : Eq (stripCtx G') G
    wf  : WfCtx G'

lift-WfCtx : {n : Nat} (G : C.Ctx n) -> P.WfCtx G -> LiftCtx G
lift-WfCtx (C.empty Th)   P.wf-empty       = mkLiftCtx (empty Th) refl wf-empty
lift-WfCtx (C.extend G A) (P.wf-extend dA) =
  let r = lift-WfCtx G (pwf-Ty dA)
      a = lift-IsType dA (LiftCtx.G' r) (LiftCtx.wf r) (LiftCtx.eG r)
  in mkLiftCtx (extend (LiftCtx.G' r) (LTy.A' a)) (ext-eq (LiftCtx.eG r) (LTy.eA a)) (wf-extend (LTy.d a))

------------------------------------------------------------------------
-- Theorem 4.19
------------------------------------------------------------------------

-- existence
section-HasType : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A ->
  Sigma (LiftCtx G) (\ r -> LTm (LiftCtx.G' r) M A)
section-HasType {G = G} d =
  let r = lift-WfCtx G (pwf-Tm d)
  in mkSigma r (lift-HasType d (LiftCtx.G' r) (LiftCtx.wf r) (LiftCtx.eG r))

section-IsType : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A ->
  Sigma (LiftCtx G) (\ r -> LTy (LiftCtx.G' r) A)
section-IsType {G = G} d =
  let r = lift-WfCtx G (pwf-Ty d)
  in mkSigma r (lift-IsType d (LiftCtx.G' r) (LiftCtx.wf r) (LiftCtx.eG r))

-- uniqueness up to conversion (in any T_R context): Lemma 4.18
section-uniq-Tm : {n : Nat} {G' : Ctx n} {M A : C.Expr n} (r1 r2 : LTm G' M A) ->
  Pair (ConvTy G' (LTm.A' r1) (LTm.A' r2)) (ConvTm G' (LTm.M' r1) (LTm.M' r2) (LTm.A' r1))
section-uniq-Tm r1 r2 =
  term-uniq-NF (LTm.d r1) (LTm.d r2)
    (Eq-trans (LTm.eM r1) (Eq-sym (LTm.eM r2))) (Eq-trans (LTm.eA r1) (Eq-sym (LTm.eA r2)))

section-uniq-Ty : {n : Nat} {G' : Ctx n} {A : C.Expr n} (r1 r2 : LTy G' A) ->
  ConvTy G' (LTy.A' r1) (LTy.A' r2)
section-uniq-Ty r1 r2 = sameTy (LTy.d r1) (LTy.d r2) (LTy.eA r1) (LTy.eA r2)
