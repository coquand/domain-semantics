{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.StripDeriv  —  Theorem 4.15 (Sterbac) for BCDE
--
--   If Γ ⊢ J in T_R, then strip(Γ) ⊢ strip(J) in T_P.
--
-- By structural induction on the T_R derivation: every T_R rule strips
-- to a T_P rule (dropping presupposition premises that T_P does not
-- have), except the annotation congruences of app, ⟨ψ⟩, ⟨α⟩ and t l,
-- whose two sides strip alike and which therefore strip to reflexivity.
------------------------------------------------------------------------

module BCDE4.StripDeriv where

open import BCDE4.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport ; fzero ; Eq-trans)
open import BCDE4.Levels
import BCDE4.RussellSyntax as R
import BCDE4.RussellTyping as RT
import BCDE4.Model.Core as C
import BCDE4.PTyping as P
open import BCDE4.Model.Strip

------------------------------------------------------------------------
-- strip commutes with the context operations
------------------------------------------------------------------------

strip-addC : {n : Nat} (G : RT.Ctx n) (c : Constr) -> Eq (stripCtx (RT.addC G c)) (P.addC (stripCtx G) c)
strip-addC (RT.empty Th)   c = refl
strip-addC (RT.extend G A) c = Eq-cong (\ X -> C.extend X (strip A)) (strip-addC G c)

strip-addL : {n : Nat} (G : RT.Ctx n) -> Eq (stripCtx (RT.addL G)) (P.addL (stripCtx G))
strip-addL (RT.empty Th)   = refl
strip-addL (RT.extend G A) =
  Eq-trans (Eq-cong (\ X -> C.extend X (strip (R.lshiftE A))) (strip-addL G))
           (Eq-cong (C.extend (P.addL (stripCtx G))) (strip-lsubE lwkS A))

-- the level part is unchanged
lv : {n : Nat} (G : RT.Ctx n) {Q : LCtx -> Set} -> Q (RT.lctx G) -> Q (C.lctx (stripCtx G))
lv G {Q} q = Eq-transport Q (Eq-sym (strip-lctx G)) q

private
  cxW : {n : Nat} {G G' : C.Ctx n} -> Eq G G' -> P.WfCtx G -> P.WfCtx G'
  cxW refl d = d
  cxI : {n : Nat} {G G' : C.Ctx n} {A : C.Expr n} -> Eq G G' -> P.IsType G A -> P.IsType G' A
  cxI refl d = d
  cxH : {n : Nat} {G G' : C.Ctx n} {M A : C.Expr n} -> Eq G G' -> P.HasType G M A -> P.HasType G' M A
  cxH refl d = d
  cxY : {n : Nat} {G G' : C.Ctx n} {A B : C.Expr n} -> Eq G G' -> P.ConvTy G A B -> P.ConvTy G' A B
  cxY refl d = d
  cxM : {n : Nat} {G G' : C.Ctx n} {M N A : C.Expr n} -> Eq G G' -> P.ConvTm G M N A -> P.ConvTm G' M N A
  cxM refl d = d

  tyM : {n : Nat} {G : C.Ctx n} {M A A' : C.Expr n} -> Eq A A' -> P.HasType G M A -> P.HasType G M A'
  tyM refl d = d

  cvM : {n : Nat} {G : C.Ctx n} {M M' N N' A A' : C.Expr n} ->
    Eq M M' -> Eq N N' -> Eq A A' -> P.ConvTm G M N A -> P.ConvTm G M' N' A'
  cvM refl refl refl d = d

  cyM : {n : Nat} {G : C.Ctx n} {A A' B B' : C.Expr n} -> Eq A A' -> Eq B B' -> P.ConvTy G A B -> P.ConvTy G A' B'
  cyM refl refl d = d

mutual

  strip-WfCtx : {n : Nat} {G : RT.Ctx n} -> RT.WfCtx G -> P.WfCtx (stripCtx G)
  strip-WfCtx RT.wf-empty       = P.wf-empty
  strip-WfCtx (RT.wf-extend dA) = P.wf-extend (strip-IsType dA)

  -- in Γ,ψ and Γ,α
  sIC : {n : Nat} {G : RT.Ctx n} {c : Constr} {A : R.Expr n} ->
    RT.IsType (RT.addC G c) A -> P.IsType (P.addC (stripCtx G) c) (strip A)
  sIC {G = G} {c} d = cxI (strip-addC G c) (strip-IsType d)
  sHC : {n : Nat} {G : RT.Ctx n} {c : Constr} {M A : R.Expr n} ->
    RT.HasType (RT.addC G c) M A -> P.HasType (P.addC (stripCtx G) c) (strip M) (strip A)
  sHC {G = G} {c} d = cxH (strip-addC G c) (strip-HasType d)
  sIL : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} ->
    RT.IsType (RT.addL G) A -> P.IsType (P.addL (stripCtx G)) (strip A)
  sIL {G = G} d = cxI (strip-addL G) (strip-IsType d)
  sHL : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n} ->
    RT.HasType (RT.addL G) M A -> P.HasType (P.addL (stripCtx G)) (strip M) (strip A)
  sHL {G = G} d = cxH (strip-addL G) (strip-HasType d)

  strip-IsType : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} ->
    RT.IsType G A -> P.IsType (stripCtx G) (strip A)
  strip-IsType (RT.is-Ty-from-U d) = P.is-Ty-from-U (strip-HasType d)
  strip-IsType (RT.is-Pi dA dB)    = P.is-Pi (strip-IsType dA) (strip-IsType dB)
  strip-IsType (RT.is-Grd dG dA)   = P.is-Grd (strip-WfCtx dG) (sIC dA)
  strip-IsType (RT.is-LPi dG dA)   = P.is-LPi (strip-WfCtx dG) (sIL dA)

  strip-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n} ->
    RT.HasType G M A -> P.HasType (stripCtx G) (strip M) (strip A)
  strip-HasType (RT.ty-GLam dG dA dt) = P.ty-GLam (strip-WfCtx dG) (sIC dA) (sHC dt)
  strip-HasType (RT.ty-LLam dG dA du) = P.ty-LLam (strip-WfCtx dG) (sIL dA) (sHL du)
  strip-HasType (RT.ty-LApp {A = A} {l = l} dA dt) =
    tyM (Eq-sym (strip-lsubE (lsub1S l) A)) (P.ty-LApp (sIL dA) (strip-HasType dt))
  strip-HasType (RT.ty-Emp dG)        = P.ty-Emp (strip-WfCtx dG)
  strip-HasType {G = G} (RT.ty-collapse lp dA) = P.ty-collapse (lv G {Loop} lp) (strip-IsType dA)
  strip-HasType {G = G} (RT.ty-var {i = i} wf) =
    tyM (Eq-sym (strip-lookup G i)) (P.ty-var (strip-WfCtx wf))
  strip-HasType (RT.ty-conv d c)      = P.ty-conv (strip-HasType d) (strip-ConvTy c)
  strip-HasType {G = G} (RT.ty-U {l = l} {m = m} wf lt) = P.ty-U (strip-WfCtx wf) (lv G {\ T -> LtL T l m} lt)
  strip-HasType {G = G} (RT.ty-cum {l = l} {m = m} d le) = P.ty-cum (strip-HasType d) (lv G {\ T -> LeL T l m} le)
  strip-HasType (RT.ty-Pi dA dB)      = P.ty-Pi (strip-HasType dA) (strip-HasType dB)
  strip-HasType (RT.ty-Lam dA dB db)  = P.ty-Lam (strip-IsType dA) (strip-IsType dB) (strip-HasType db)
  strip-HasType (RT.ty-App {B = B} {a = a} dA dB dc da) =
    tyM (Eq-sym (strip-subst1 B a)) (P.ty-App (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-HasType da))

  strip-ConvTy : {n : Nat} {G : RT.Ctx n} {A B : R.Expr n} ->
    RT.ConvTy G A B -> P.ConvTy (stripCtx G) (strip A) (strip B)
  strip-ConvTy (RT.conv-Ty-refl dA)      = P.conv-Ty-refl (strip-IsType dA)
  strip-ConvTy (RT.conv-Ty-sym d)        = P.conv-Ty-sym (strip-ConvTy d)
  strip-ConvTy (RT.conv-Ty-trans d1 d2)  = P.conv-Ty-trans (strip-ConvTy d1) (strip-ConvTy d2)
  strip-ConvTy (RT.conv-Ty-Pi dA dB cA cB) =
    P.conv-Ty-Pi (strip-IsType dA) (strip-IsType dB) (strip-ConvTy cA) (strip-ConvTy cB)
  strip-ConvTy {G = G} (RT.conv-Ty-Grd {c = c} dG dA dAB) =
    P.conv-Ty-Grd (strip-WfCtx dG) (sIC dA) (cxY (strip-addC G c) (strip-ConvTy dAB))
  strip-ConvTy {G = G} (RT.conv-Ty-LPi dG dA dAB) =
    P.conv-Ty-LPi (strip-WfCtx dG) (sIL dA) (cxY (strip-addL G) (strip-ConvTy dAB))
  strip-ConvTy {G = G} (RT.conv-Ty-Grd-beta {c = c} v dA) =
    P.conv-Ty-Grd-beta (lv G {\ T -> ValidC T c} v) (strip-IsType dA)
  strip-ConvTy {G = G} (RT.conv-Ty-Grd-equiv {c = c} {c' = c'} dG q dA) =
    P.conv-Ty-Grd-equiv (strip-WfCtx dG) (lv G {\ T -> EquivC T c c'} q) (sIC dA)
  strip-ConvTy {G = G} (RT.conv-Ty-collapse lp dA) = P.conv-Ty-collapse (lv G {Loop} lp) (strip-IsType dA)
  strip-ConvTy (RT.conv-Ty-from-U d)     = P.conv-Ty-from-U (strip-ConvTm d)

  strip-ConvTm : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n} ->
    RT.ConvTm G M N A -> P.ConvTm (stripCtx G) (strip M) (strip N) (strip A)
  strip-ConvTm (RT.conv-refl d)       = P.conv-refl (strip-HasType d)
  strip-ConvTm (RT.conv-sym d)        = P.conv-sym (strip-ConvTm d)
  strip-ConvTm (RT.conv-trans d1 d2)  = P.conv-trans (strip-ConvTm d1) (strip-ConvTm d2)
  strip-ConvTm (RT.conv-conv d c)     = P.conv-conv (strip-ConvTm d) (strip-ConvTy c)
  strip-ConvTm (RT.conv-cong-Pi dA dB cA cB) =
    P.conv-cong-Pi (strip-HasType dA) (strip-HasType dB) (strip-ConvTm cA) (strip-ConvTm cB)
  strip-ConvTm {G = G} (RT.conv-cum {l = l} {m = m} d le) = P.conv-cum (strip-ConvTm d) (lv G {\ T -> LeL T l m} le)
  strip-ConvTm {G = G} (RT.conv-U-lvl {l = l} {l' = l'} {m = m} wf v lt) =
    P.conv-U-lvl (strip-WfCtx wf) (lv G {\ T -> Valid T l l'} v) (lv G {\ T -> LtL T l m} lt)
  strip-ConvTm (RT.conv-cong-Lam-body dA dB db0 db) =
    P.conv-cong-Lam-body (strip-IsType dA) (strip-IsType dB) (strip-HasType db0) (strip-ConvTm db)
  strip-ConvTm (RT.conv-cong-Lam-Ty dA dB cA _ db) =
    P.conv-cong-Lam-dom (strip-IsType dA) (strip-IsType dB) (strip-ConvTy cA) (strip-HasType db)
  strip-ConvTm (RT.conv-cong-App-fun {B = B} {a = a} dA dB dc da) =
    cvM refl refl (Eq-sym (strip-subst1 B a))
      (P.conv-cong-App-fun (strip-IsType dA) (strip-IsType dB) (strip-ConvTm dc) (strip-HasType da))
  strip-ConvTm (RT.conv-cong-App-arg {B = B} {a = a} {a' = a'} dA dB dc da cB) =
    cvM refl refl (Eq-sym (strip-subst1 B a))
      (P.conv-cong-App-arg (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-ConvTm da)
        (cyM (strip-subst1 B a) (strip-subst1 B a') (strip-ConvTy cB)))
  strip-ConvTm (RT.conv-cong-App-Ty {B = B} {a = a} dA dB _ _ dc da) =
    P.conv-refl (tyM (Eq-sym (strip-subst1 B a))
      (P.ty-App (strip-IsType dA) (strip-IsType dB) (strip-HasType dc) (strip-HasType da)))
  strip-ConvTm (RT.conv-beta {B = B} {b = b} {a = a} dA dB db da) =
    cvM refl (Eq-sym (strip-subst1 b a)) (Eq-sym (strip-subst1 B a))
      (P.conv-beta (strip-IsType dA) (strip-IsType dB) (strip-HasType db) (strip-HasType da))
  strip-ConvTm {G = G} (RT.conv-cong-GLam {c = c} dG dA dt dtt) =
    P.conv-cong-GLam (strip-WfCtx dG) (sIC dA) (sHC dt) (cxM (strip-addC G c) (strip-ConvTm dtt))
  strip-ConvTm {G = G} (RT.conv-GLam-beta {c = c} v dA dt) =
    P.conv-GLam-beta (lv G {\ T -> ValidC T c} v) (strip-IsType dA) (strip-HasType dt)
  strip-ConvTm {G = G} (RT.conv-cong-LLam dG dA du duu) =
    P.conv-cong-LLam (strip-WfCtx dG) (sIL dA) (sHL du) (cxM (strip-addL G) (strip-ConvTm duu))
  strip-ConvTm (RT.conv-cong-GLam-Ty dG dA _ dt) = P.conv-refl (P.ty-GLam (strip-WfCtx dG) (sIC dA) (sHC dt))
  strip-ConvTm (RT.conv-cong-LLam-Ty dG dA _ du) = P.conv-refl (P.ty-LLam (strip-WfCtx dG) (sIL dA) (sHL du))
  strip-ConvTm (RT.conv-cong-LApp-Ty {A = A} {l = l} dA _ dt) =
    P.conv-refl (tyM (Eq-sym (strip-lsubE (lsub1S l) A)) (P.ty-LApp (sIL dA) (strip-HasType dt)))
  strip-ConvTm (RT.conv-cong-LApp-fun {A = A} {l = l} dA dtt) =
    cvM refl refl (Eq-sym (strip-lsubE (lsub1S l) A)) (P.conv-cong-LApp-fun (sIL dA) (strip-ConvTm dtt))
  strip-ConvTm {G = G} (RT.conv-cong-LApp-lvl {A = A} {l = l} {l' = l'} dA dt v cA) =
    cvM refl refl (Eq-sym (strip-lsubE (lsub1S l) A))
      (P.conv-cong-LApp-lvl (sIL dA) (strip-HasType dt) (lv G {\ T -> Valid T l l'} v)
        (cyM (strip-lsubE (lsub1S l) A) (strip-lsubE (lsub1S l') A) (strip-ConvTy cA)))
  strip-ConvTm {G = G} (RT.conv-GLam-equiv {c = c} {c' = c'} dG q dA dt) =
    P.conv-GLam-equiv (strip-WfCtx dG) (lv G {\ T -> EquivC T c c'} q) (sIC dA) (sHC dt)
  strip-ConvTm (RT.conv-LApp-beta {A = A} {u = u} {l = l} dA du) =
    cvM refl (Eq-sym (strip-lsubE (lsub1S l) u)) (Eq-sym (strip-lsubE (lsub1S l) A))
      (P.conv-LApp-beta (sIL dA) (sHL du))
  strip-ConvTm (RT.conv-LApp-eta {t = t} dA dt) =
    cvM refl (Eq-cong (\ X -> C.LLam (C.LApp X (lvar zero))) (Eq-sym (strip-lsubE lwkS t))) refl
      (P.conv-LApp-eta (sIL dA) (strip-HasType dt))
  strip-ConvTm (RT.conv-GLam-eta dG dA dt dt') =
    P.conv-GLam-eta (strip-WfCtx dG) (sIC dA) (strip-HasType dt) (sHC dt')
  strip-ConvTm {G = G} (RT.conv-collapse lp dA dt) =
    P.conv-collapse (lv G {Loop} lp) (strip-IsType dA) (strip-HasType dt)
  strip-ConvTm (RT.conv-eta {A = A} {c = c} dA dB dc) =
    cvM refl (Eq-cong (\ X -> C.Lam (strip A) (C.App X (C.Var fzero))) (Eq-sym (strip-wk c))) refl
      (P.conv-eta (strip-IsType dA) (strip-IsType dB) (strip-HasType dc))
