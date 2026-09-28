{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.RussellLsub
--
-- Level substitution preserves all judgements: if ζ maps the level
-- constraints of Γ to constraints valid in Δ, and Δ is Γ with ζ applied
-- to its types, then every judgement of Γ, with ζ applied, holds in Δ.
-- Structural recursion on derivations.  Instances: the shift under a
-- level binder (Γ ⊢ J ⇒ Γ,α ⊢ J↑) and instantiation (Γ,α ⊢ J ⇒ Γ ⊢ J(l/α)).
------------------------------------------------------------------------

module BCDE4.RussellLsub where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping

------------------------------------------------------------------------
-- Contexts related by a level substitution
------------------------------------------------------------------------

data LSk (z : LSub) : {n : Nat} -> Ctx n -> Ctx n -> Set where
  lsk-empty  : {Th T : LCtx} -> LSk z (empty Th) (empty T)
  lsk-extend : {n : Nat} {G H : Ctx n} {A B : Expr n} ->
    LSk z G H -> Eq B (lsubE z A) -> LSk z (extend G A) (extend H B)

lsk-lookup : {z : LSub} {n : Nat} {G H : Ctx n} -> LSk z G H -> (i : Fin n) ->
  Eq (lookup H i) (lsubE z (lookup G i))
lsk-lookup {z} (lsk-extend {A = A} s refl) fzero = Eq-sym (lsubE-ren z wkRen A)
lsk-lookup {z} {G = extend G A} (lsk-extend s refl) (fsuc i) =
  Eq-trans (Eq-cong wkExpr (lsk-lookup s i)) (Eq-sym (lsubE-ren z wkRen (lookup G i)))

lsk-addC : {z : LSub} {n : Nat} {G H : Ctx n} (c : Constr) -> LSk z G H -> LSk z (addC G c) (addC H (lsubC z c))
lsk-addC c lsk-empty        = lsk-empty
lsk-addC c (lsk-extend s e) = lsk-extend (lsk-addC c s) e

lsk-addL : {z : LSub} {n : Nat} {G H : Ctx n} -> LSk z G H -> LSk (liftL z) (addL G) (addL H)
lsk-addL lsk-empty = lsk-empty
lsk-addL {z} (lsk-extend {A = A} s refl) =
  lsk-extend (lsk-addL s) (Eq-sym (lsubE-liftL-shift z A))

-- the constraints are mapped to valid ones
LOK : LSub -> {n : Nat} -> Ctx n -> Ctx n -> Set
LOK z G H = LSubOK (lctx H) (lctx G) z

private
  tr-lok : {z : LSub} {T T' Th Th' : LCtx} -> Eq T T' -> Eq Th Th' -> LSubOK T Th z -> LSubOK T' Th' z
  tr-lok refl refl ok = ok

lok-addC : {z : LSub} {n : Nat} (G H : Ctx n) (c : Constr) -> LOK z G H -> LOK z (addC G c) (addC H (lsubC z c))
lok-addC {z} G H c ok =
  tr-lok {z = z} (Eq-sym (lctx-addC H (lsubC z c))) (Eq-sym (lctx-addC G c)) ok'
  where
    ok' : LSubOK (lcons (lsubC z c) (lctx H)) (lcons c (lctx G)) z
    ok' {ceq l m} lhere = v-hyp lhere
    ok' {ceq l m} (lthere h) = validC-ent (lsubC z (ceq l m)) (ent-wk (lsubC z c)) (ok h)

lok-addL : {z : LSub} {n : Nat} (G H : Ctx n) -> LOK z G H -> LOK (liftL z) (addL G) (addL H)
lok-addL {z} G H ok =
  tr-lok {z = liftL z} (Eq-sym (lctx-addL H)) (Eq-sym (lctx-addL G)) ok'
  where
    shiftC : (c : Constr) -> Eq (lsubC (liftL z) (lsubC lwkS c)) (lsubC lwkS (lsubC z c))
    shiftC (ceq l m) = Eq-cong2 ceq (liftL-shift z l) (liftL-shift z m)
    unmap : {d : Constr} (Th : LCtx) -> LMem d (lsubTh lwkS Th) ->
      Sigma Constr (\ c -> Pair (LMem c Th) (Eq d (lsubC lwkS c)))
    unmap (lcons c Th) lhere      = mkSigma c (mkSigma lhere refl)
    unmap (lcons c Th) (lthere h) =
      let r = unmap Th h in mkSigma (fst r) (mkSigma (lthere (fst (snd r))) (snd (snd r)))
    ok' : LSubOK (lsubTh lwkS (lctx H)) (lsubTh lwkS (lctx G)) (liftL z)
    ok' {d} h =
      let r = unmap (lctx G) h
          c = fst r
          v : ValidC (lsubTh lwkS (lctx H)) (lsubC lwkS (lsubC z c))
          v = validC-lsub lwkS (lsubC z c) (lsubOK-self lwkS (lctx H)) (ok (fst (snd r)))
      in Eq-transport (ValidC (lsubTh lwkS (lctx H)))
           (Eq-sym (Eq-trans (Eq-cong (lsubC (liftL z)) (snd (snd r))) (shiftC c))) v

------------------------------------------------------------------------
-- Commutation facts
------------------------------------------------------------------------

lsubE-subst1 : {n : Nat} (z : LSub) (B : Expr (suc n)) (a : Expr n) ->
  Eq (lsubE z (subst1 B a)) (subst1 (lsubE z B) (lsubE z a))
lsubE-subst1 z B a =
  Eq-trans (lsubE-subst z (subst1Sub a) B) (substExpr-ext _ _ pt (lsubE z B))
  where
    pt : (i : Fin _) -> Eq (lsubE z (subst1Sub a i)) (subst1Sub (lsubE z a) i)
    pt fzero    = refl
    pt (fsuc i) = refl

lsubE-lsub1 : {n : Nat} (z : LSub) (A : Expr n) (l : LExpr) ->
  Eq (lsubE z (lsub1 A l)) (lsub1 (lsubE (liftL z) A) (lsubL z l))
lsubE-lsub1 z A l =
  Eq-trans (lsubE-comp z (lsub1S l) A)
    (Eq-trans (lsubE-ext _ _ pt A) (Eq-sym (lsubE-comp (lsub1S (lsubL z l)) (liftL z) A)))
  where
    pt : (i : Nat) -> Eq (lcomp z (lsub1S l) i) (lcomp (lsub1S (lsubL z l)) (liftL z) i)
    pt zero    = refl
    pt (suc i) = Eq-sym (lsub1-shift (lsubL z l) (z i))

lsubE-wkExpr : {n : Nat} (z : LSub) (A : Expr n) -> Eq (lsubE z (wkExpr A)) (wkExpr (lsubE z A))
lsubE-wkExpr z A = lsubE-ren z wkRen A

lsubE-liftRen-wk : {n : Nat} (z : LSub) (B : Expr (suc n)) ->
  Eq (lsubE z (renExpr (liftRen wkRen) B)) (renExpr (liftRen wkRen) (lsubE z B))
lsubE-liftRen-wk z B = lsubE-ren z (liftRen wkRen) B

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

mutual
  lsub-WfCtx : {z : LSub} {n : Nat} {G H : Ctx n} -> LSk z G H -> LOK z G H ->
    WfCtx G -> WfCtx H
  lsub-WfCtx lsk-empty ok wf-empty = wf-empty
  lsub-WfCtx (lsk-extend s refl) ok (wf-extend dA) = wf-extend (lsub-IsType s ok dA)

  lsub-IsType : {z : LSub} {n : Nat} {G H : Ctx n} {A : Expr n} -> LSk z G H -> LOK z G H ->
    IsType G A -> IsType H (lsubE z A)
  lsub-IsType s ok (is-Ty-from-U d) = is-Ty-from-U (lsub-HasType s ok d)
  lsub-IsType s ok (is-Pi dA dB) = is-Pi (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
  lsub-IsType {z} {G = G} {H = H} s ok (is-Grd {c = c} dG dA) =
    is-Grd (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
  lsub-IsType {z} {G = G} {H = H} s ok (is-LPi dG dA) =
    is-LPi (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)

  lsub-HasType : {z : LSub} {n : Nat} {G H : Ctx n} {M A : Expr n} -> LSk z G H -> LOK z G H ->
    HasType G M A -> HasType H (lsubE z M) (lsubE z A)
  lsub-HasType {z} {G = G} {H = H} s ok (ty-GLam {c = c} dG dA dt) =
    ty-GLam (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
            (lsub-HasType (lsk-addC c s) (lok-addC G H c ok) dt)
  lsub-HasType s ok (ty-Emp dG) = ty-Emp (lsub-WfCtx s ok dG)
  lsub-HasType {z} s ok (ty-collapse lp dA) = ty-collapse (loop-lsub z ok lp) (lsub-IsType s ok dA)
  lsub-HasType {z} {G = G} {H = H} s ok (ty-LLam dG dA du) =
    ty-LLam (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
            (lsub-HasType (lsk-addL s) (lok-addL G H ok) du)
  lsub-HasType {z} {G = G} {H = H} s ok (ty-LApp {A = A} {t = t} {l = l} dA dt) =
    Eq-transport (\ T -> HasType H (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l)) T) (Eq-sym (lsubE-lsub1 z A l))
      (ty-LApp (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA) (lsub-HasType s ok dt))
  lsub-HasType {z} {H = H} s ok (ty-var {i = i} dG) =
    Eq-transport (\ T -> HasType H (Var i) T) (lsk-lookup s i) (ty-var (lsub-WfCtx s ok dG))
  lsub-HasType s ok (ty-conv dM dAB) = ty-conv (lsub-HasType s ok dM) (lsub-ConvTy s ok dAB)
  lsub-HasType {z} s ok (ty-U dG v) = ty-U (lsub-WfCtx s ok dG) (valid-lsub z ok v)
  lsub-HasType {z} s ok (ty-cum d v) = ty-cum (lsub-HasType s ok d) (valid-lsub z ok v)
  lsub-HasType s ok (ty-Pi dA dB) =
    ty-Pi (lsub-HasType s ok dA) (lsub-HasType (lsk-extend s refl) ok dB)
  lsub-HasType s ok (ty-Lam dA dB db) =
    ty-Lam (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
           (lsub-HasType (lsk-extend s refl) ok db)
  lsub-HasType {z} {H = H} s ok (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    Eq-transport (\ T -> HasType H (App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a)) T)
      (Eq-sym (lsubE-subst1 z B a))
      (ty-App (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
              (lsub-HasType s ok dc) (lsub-HasType s ok da))

  lsub-ConvTy : {z : LSub} {n : Nat} {G H : Ctx n} {A B : Expr n} -> LSk z G H -> LOK z G H ->
    ConvTy G A B -> ConvTy H (lsubE z A) (lsubE z B)
  lsub-ConvTy s ok (conv-Ty-refl dA) = conv-Ty-refl (lsub-IsType s ok dA)
  lsub-ConvTy s ok (conv-Ty-sym d) = conv-Ty-sym (lsub-ConvTy s ok d)
  lsub-ConvTy s ok (conv-Ty-trans d1 d2) = conv-Ty-trans (lsub-ConvTy s ok d1) (lsub-ConvTy s ok d2)
  lsub-ConvTy s ok (conv-Ty-Pi dA dB dAA dBB) =
    conv-Ty-Pi (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
               (lsub-ConvTy s ok dAA) (lsub-ConvTy (lsk-extend s refl) ok dBB)
  lsub-ConvTy {z} {G = G} {H = H} s ok (conv-Ty-Grd {c = c} dG dA dAB) =
    conv-Ty-Grd (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
                (lsub-ConvTy (lsk-addC c s) (lok-addC G H c ok) dAB)
  lsub-ConvTy {z} {G = G} {H = H} s ok (conv-Ty-LPi dG dA dAB) =
    conv-Ty-LPi (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
                (lsub-ConvTy (lsk-addL s) (lok-addL G H ok) dAB)
  lsub-ConvTy {z} s ok (conv-Ty-collapse lp dA) =
    conv-Ty-collapse (loop-lsub z ok lp) (lsub-IsType s ok dA)
  lsub-ConvTy s ok (conv-Ty-from-U d) = conv-Ty-from-U (lsub-ConvTm s ok d)
  lsub-ConvTy {z} s ok (conv-Ty-Grd-beta {c = c} v dA) = conv-Ty-Grd-beta (validC-lsub z c ok v) (lsub-IsType s ok dA)
  lsub-ConvTy {z} {G = G} {H = H} s ok (conv-Ty-Grd-equiv {c = c} dG q dA) =
    conv-Ty-Grd-equiv (lsub-WfCtx s ok dG) (equivC-lsub z ok q) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)

  lsub-ConvTm : {z : LSub} {n : Nat} {G H : Ctx n} {M N A : Expr n} -> LSk z G H -> LOK z G H ->
    ConvTm G M N A -> ConvTm H (lsubE z M) (lsubE z N) (lsubE z A)
  lsub-ConvTm s ok (conv-refl dM) = conv-refl (lsub-HasType s ok dM)
  lsub-ConvTm {z} s ok (conv-cum d v) = conv-cum (lsub-ConvTm s ok d) (valid-lsub z ok v)
  lsub-ConvTm {z} s ok (conv-U-lvl dG v w) = conv-U-lvl (lsub-WfCtx s ok dG) (valid-lsub z ok v) (valid-lsub z ok w)
  lsub-ConvTm s ok (conv-sym d) = conv-sym (lsub-ConvTm s ok d)
  lsub-ConvTm s ok (conv-trans d1 d2) = conv-trans (lsub-ConvTm s ok d1) (lsub-ConvTm s ok d2)
  lsub-ConvTm s ok (conv-conv d dAB) = conv-conv (lsub-ConvTm s ok d) (lsub-ConvTy s ok dAB)
  lsub-ConvTm s ok (conv-cong-Pi dA dB dAA dBB) =
    conv-cong-Pi (lsub-HasType s ok dA) (lsub-HasType (lsk-extend s refl) ok dB)
                 (lsub-ConvTm s ok dAA) (lsub-ConvTm (lsk-extend s refl) ok dBB)
  lsub-ConvTm s ok (conv-cong-Lam-body dA dB db dbb) =
    conv-cong-Lam-body (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                       (lsub-HasType (lsk-extend s refl) ok db) (lsub-ConvTm (lsk-extend s refl) ok dbb)
  lsub-ConvTm s ok (conv-cong-Lam-Ty dA dB dAA dBB db) =
    conv-cong-Lam-Ty (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                     (lsub-ConvTy s ok dAA) (lsub-ConvTy (lsk-extend s refl) ok dBB)
                     (lsub-HasType (lsk-extend s refl) ok db)
  lsub-ConvTm {z} {H = H} s ok (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a} dA dB dc da) =
    Eq-transport (\ T -> ConvTm H (App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a))
                                  (App (lsubE z A) (lsubE z B) (lsubE z c') (lsubE z a)) T)
      (Eq-sym (lsubE-subst1 z B a))
      (conv-cong-App-fun (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                         (lsub-ConvTm s ok dc) (lsub-HasType s ok da))
  lsub-ConvTm {z} {H = H} s ok (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'} dA dB dc da dBa) =
    Eq-transport (\ T -> ConvTm H (App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a))
                                  (App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a')) T)
      (Eq-sym (lsubE-subst1 z B a))
      (conv-cong-App-arg (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                         (lsub-HasType s ok dc) (lsub-ConvTm s ok da)
                         (Eq-transport (\ X -> ConvTy H X (subst1 (lsubE z B) (lsubE z a'))) (lsubE-subst1 z B a)
                           (Eq-transport (\ Y -> ConvTy H (lsubE z (subst1 B a)) Y) (lsubE-subst1 z B a')
                             (lsub-ConvTy s ok dBa))))
  lsub-ConvTm {z} {H = H} s ok (conv-cong-App-Ty {A = A} {A' = A'} {B = B} {B' = B'} {c = c} {a = a} dA dB dAA dBB dc da) =
    Eq-transport (\ T -> ConvTm H (App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a))
                                  (App (lsubE z A') (lsubE z B') (lsubE z c) (lsubE z a)) T)
      (Eq-sym (lsubE-subst1 z B a))
      (conv-cong-App-Ty (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                        (lsub-ConvTy s ok dAA) (lsub-ConvTy (lsk-extend s refl) ok dBB)
                        (lsub-HasType s ok dc) (lsub-HasType s ok da))
  lsub-ConvTm {z} {H = H} s ok (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    Eq-transport (\ T -> ConvTm H (App (lsubE z A) (lsubE z B) (Lam (lsubE z A) (lsubE z B) (lsubE z b)) (lsubE z a))
                                  (lsubE z (subst1 b a)) T)
      (Eq-sym (lsubE-subst1 z B a))
      (Eq-transport (\ X -> ConvTm H (App (lsubE z A) (lsubE z B) (Lam (lsubE z A) (lsubE z B) (lsubE z b)) (lsubE z a))
                                     X (subst1 (lsubE z B) (lsubE z a)))
        (Eq-sym (lsubE-subst1 z b a))
        (conv-beta (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
                   (lsub-HasType (lsk-extend s refl) ok db) (lsub-HasType s ok da)))
  lsub-ConvTm {z} {H = H} s ok (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    Eq-transport (\ X -> ConvTm H (lsubE z c) X (Pi (lsubE z A) (lsubE z B)))
      (Eq-cong (Lam (lsubE z A) (lsubE z B))
        (Eq-sym (Eq-cong4 App (lsubE-wkExpr z A) (lsubE-liftRen-wk z B) (lsubE-wkExpr z c) refl)))
      (conv-eta (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB) (lsub-HasType s ok dc))
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-GLam {c = c} dG dA dt dtt) =
    conv-cong-GLam (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
                   (lsub-HasType (lsk-addC c s) (lok-addC G H c ok) dt)
                   (lsub-ConvTm (lsk-addC c s) (lok-addC G H c ok) dtt)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-GLam-eta {c = c} dG dA dt dt') =
    conv-GLam-eta (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
                  (lsub-HasType s ok dt) (lsub-HasType (lsk-addC c s) (lok-addC G H c ok) dt')
  lsub-ConvTm {z} s ok (conv-GLam-beta {c = c} v dA dt) =
    conv-GLam-beta (validC-lsub z c ok v) (lsub-IsType s ok dA) (lsub-HasType s ok dt)
  lsub-ConvTm {z} s ok (conv-collapse lp dA dt) =
    conv-collapse (loop-lsub z ok lp) (lsub-IsType s ok dA) (lsub-HasType s ok dt)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-LLam dG dA du duu) =
    conv-cong-LLam (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
                   (lsub-HasType (lsk-addL s) (lok-addL G H ok) du)
                   (lsub-ConvTm (lsk-addL s) (lok-addL G H ok) duu)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-GLam-Ty {c = c} dG dA dAA dt) =
    conv-cong-GLam-Ty (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
                      (lsub-ConvTy (lsk-addC c s) (lok-addC G H c ok) dAA)
                      (lsub-HasType (lsk-addC c s) (lok-addC G H c ok) dt)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-LLam-Ty dG dA dAA du) =
    conv-cong-LLam-Ty (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
                      (lsub-ConvTy (lsk-addL s) (lok-addL G H ok) dAA)
                      (lsub-HasType (lsk-addL s) (lok-addL G H ok) du)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-LApp-Ty {A = A} {A' = A'} {t = t} {l = l} dA dAA dt) =
    Eq-transport (\ T -> ConvTm H (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l)) (LApp (lsubE (liftL z) A') (lsubE z t) (lsubL z l)) T)
      (Eq-sym (lsubE-lsub1 z A l))
      (conv-cong-LApp-Ty (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
        (lsub-ConvTy (lsk-addL s) (lok-addL G H ok) dAA) (lsub-HasType s ok dt))
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-LApp-fun {A = A} {t = t} {t' = t'} {l = l} dA dtt) =
    Eq-transport (\ T -> ConvTm H (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l)) (LApp (lsubE (liftL z) A) (lsubE z t') (lsubL z l)) T)
      (Eq-sym (lsubE-lsub1 z A l))
      (conv-cong-LApp-fun (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA) (lsub-ConvTm s ok dtt))
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-cong-LApp-lvl {A = A} {t = t} {l = l} {l' = l'} dA dt v dAA) =
    Eq-transport (\ T -> ConvTm H (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l)) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l')) T)
      (Eq-sym (lsubE-lsub1 z A l))
      (conv-cong-LApp-lvl (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA) (lsub-HasType s ok dt)
        (valid-lsub z ok v)
        (Eq-transport (\ X -> ConvTy H X (lsub1 (lsubE (liftL z) A) (lsubL z l'))) (lsubE-lsub1 z A l)
          (Eq-transport (ConvTy H (lsubE z (lsub1 A l))) (lsubE-lsub1 z A l') (lsub-ConvTy s ok dAA))))
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-GLam-equiv {c = c} dG q dA dt) =
    conv-GLam-equiv (lsub-WfCtx s ok dG) (equivC-lsub z ok q)
                    (lsub-IsType (lsk-addC c s) (lok-addC G H c ok) dA)
                    (lsub-HasType (lsk-addC c s) (lok-addC G H c ok) dt)
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-LApp-beta {A = A} {u = u} {l = l} dA du) =
    Eq-transport (\ T -> ConvTm H (LApp (lsubE (liftL z) A) (LLam (lsubE (liftL z) A) (lsubE (liftL z) u)) (lsubL z l)) (lsubE z (lsub1 u l)) T)
      (Eq-sym (lsubE-lsub1 z A l))
      (Eq-transport (\ X -> ConvTm H (LApp (lsubE (liftL z) A) (LLam (lsubE (liftL z) A) (lsubE (liftL z) u)) (lsubL z l)) X
                                     (lsub1 (lsubE (liftL z) A) (lsubL z l)))
        (Eq-sym (lsubE-lsub1 z u l))
        (conv-LApp-beta (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
                        (lsub-HasType (lsk-addL s) (lok-addL G H ok) du)))
  lsub-ConvTm {z} {G = G} {H = H} s ok (conv-LApp-eta {A = A} {t = t} dA dt) =
    Eq-transport (\ X -> ConvTm H (lsubE z t) X (LPi (lsubE (liftL z) A)))
      (Eq-cong2 (\ Y X -> LLam (lsubE (liftL z) A) (LApp Y X (lvar zero))) (Eq-sym (lsubE-liftL2-shift z A)) (Eq-sym (lsubE-liftL-shift z t)))
      (conv-LApp-eta (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA) (lsub-HasType s ok dt))

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- the context itself, shifted
lsk-shift : {n : Nat} (G : Ctx n) -> LSk lwkS G (addL G)
lsk-shift (empty Th)   = lsk-empty
lsk-shift (extend G A) = lsk-extend (lsk-shift G) refl

lok-shift : {n : Nat} (G : Ctx n) -> LOK lwkS G (addL G)
lok-shift G =
  Eq-transport (\ X -> LSubOK X (lctx G) lwkS) (Eq-sym (lctx-addL G)) (lsubOK-self lwkS (lctx G))

-- instantiating the fresh level: Γ,α ↦ Γ with α := l
lsk-inst : {n : Nat} (G : Ctx n) (l : LExpr) -> LSk (lsub1S l) (addL G) G
lsk-inst (empty Th)   l = lsk-empty
lsk-inst (extend G A) l = lsk-extend (lsk-inst G l) (Eq-sym (lsubE-lsub1-shift l A))
  where
    lsubE-lsub1-shift : {n : Nat} (l : LExpr) (A : Expr n) -> Eq (lsubE (lsub1S l) (lshiftE A)) A
    lsubE-lsub1-shift l A = Eq-trans (lsubE-comp (lsub1S l) lwkS A) (Eq-trans (lsubE-ext _ _ (\ i -> refl) A) (lsubE-id A))

lok-inst : {n : Nat} (G : Ctx n) (l : LExpr) -> LOK (lsub1S l) (addL G) G
lok-inst G l =
  Eq-transport (\ X -> LSubOK (lctx G) X (lsub1S l)) (Eq-sym (lctx-addL G)) (lsubOK-inst l (lctx G))

------------------------------------------------------------------------
-- The level-substituted context  Γζ
------------------------------------------------------------------------

lsubCtx : {n : Nat} -> LSub -> Ctx n -> Ctx n
lsubCtx z (empty Th)   = empty (lsubTh z Th)
lsubCtx z (extend G A) = extend (lsubCtx z G) (lsubE z A)

lctx-lsubCtx : {n : Nat} (z : LSub) (G : Ctx n) -> Eq (lctx (lsubCtx z G)) (lsubTh z (lctx G))
lctx-lsubCtx z (empty Th)   = refl
lctx-lsubCtx z (extend G A) = lctx-lsubCtx z G

lsk-lsubCtx : {n : Nat} (z : LSub) (G : Ctx n) -> LSk z G (lsubCtx z G)
lsk-lsubCtx z (empty Th)   = lsk-empty
lsk-lsubCtx z (extend G A) = lsk-extend (lsk-lsubCtx z G) refl

lok-lsubCtx : {n : Nat} (z : LSub) (G : Ctx n) -> LOK z G (lsubCtx z G)
lok-lsubCtx z G =
  Eq-transport (\ X -> LSubOK X (lctx G) z) (Eq-sym (lctx-lsubCtx z G)) (lsubOK-self z (lctx G))

-- Γζ for the identity is Γ
lsubCtx-id : {n : Nat} (G : Ctx n) -> Eq (lsubCtx lidS G) G
lsubCtx-id (empty Th)   = Eq-cong empty (lsubTh-id Th)
lsubCtx-id (extend G A) = Eq-cong2 extend (lsubCtx-id G) (lsubE-id A)

-- entering a level binder and instantiating it at l: (Γ,α)(l·ζ) = Γζ
lsubCtx-inst : {n : Nat} (l : LExpr) (z : LSub) (G : Ctx n) ->
  Eq (lsubCtx (lconsS l z) (addL G)) (lsubCtx z G)
lsubCtx-inst l z (empty Th)   =
  Eq-cong empty (Eq-trans (lsubTh-comp (lconsS l z) lwkS Th) (lsubTh-ext _ _ (\ i -> refl) Th))
lsubCtx-inst l z (extend G A) =
  Eq-cong2 extend (lsubCtx-inst l z G)
    (Eq-trans (lsubE-comp (lconsS l z) lwkS A) (lsubE-ext _ _ (\ i -> refl) A))

-- the instantiation of a body under liftL ζ at l is the body at l·ζ
lsub1-liftL : {n : Nat} (z : LSub) (A : Expr n) (l : LExpr) ->
  Eq (lsub1 (lsubE (liftL z) A) l) (lsubE (lconsS l z) A)
lsub1-liftL z A l =
  Eq-trans (lsubE-comp (lsub1S l) (liftL z) A) (lsubE-ext _ _ pt A)
  where
    pt : (i : Nat) -> Eq (lcomp (lsub1S l) (liftL z) i) (lconsS l z i)
    pt zero    = refl
    pt (suc i) = lsub1-shift l (z i)

-- level substitution of contexts commutes with adding a constraint / a level
lsubCtx-addC : {n : Nat} (z : LSub) (G : Ctx n) (c : Constr) ->
  Eq (lsubCtx z (addC G c)) (addC (lsubCtx z G) (lsubC z c))
lsubCtx-addC z (empty Th)   c = refl
lsubCtx-addC z (extend G A) c = Eq-cong (\ X -> extend X (lsubE z A)) (lsubCtx-addC z G c)

lsubCtx-addL : {n : Nat} (z : LSub) (G : Ctx n) ->
  Eq (lsubCtx (liftL z) (addL G)) (addL (lsubCtx z G))
lsubCtx-addL z (empty Th)   =
  Eq-cong empty (Eq-trans (lsubTh-comp (liftL z) lwkS Th)
    (Eq-trans (lsubTh-ext _ _ (\ i -> refl) Th) (Eq-sym (lsubTh-comp lwkS z Th))))
lsubCtx-addL z (extend G A) = Eq-cong2 extend (lsubCtx-addL z G) (lsubE-liftL-shift z A)

-- the substituted derivations
module _ {n : Nat} (z : LSub) (G : Ctx n) where
  lsubD-HasType : {M A : Expr n} -> HasType G M A -> HasType (lsubCtx z G) (lsubE z M) (lsubE z A)
  lsubD-HasType = lsub-HasType (lsk-lsubCtx z G) (lok-lsubCtx z G)
  lsubD-IsType : {A : Expr n} -> IsType G A -> IsType (lsubCtx z G) (lsubE z A)
  lsubD-IsType = lsub-IsType (lsk-lsubCtx z G) (lok-lsubCtx z G)
  lsubD-ConvTy : {A B : Expr n} -> ConvTy G A B -> ConvTy (lsubCtx z G) (lsubE z A) (lsubE z B)
  lsubD-ConvTy = lsub-ConvTy (lsk-lsubCtx z G) (lok-lsubCtx z G)
  lsubD-ConvTm : {M N A : Expr n} -> ConvTm G M N A -> ConvTm (lsubCtx z G) (lsubE z M) (lsubE z N) (lsubE z A)
  lsubD-ConvTm = lsub-ConvTm (lsk-lsubCtx z G) (lok-lsubCtx z G)
  lsubD-WfCtx : WfCtx G -> WfCtx (lsubCtx z G)
  lsubD-WfCtx = lsub-WfCtx (lsk-lsubCtx z G) (lok-lsubCtx z G)

-- constraints and loops transfer to Γζ
lsubCtx-valid : {n : Nat} (z : LSub) (G : Ctx n) (c : Constr) -> ValidC (lctx G) c -> ValidC (lctx (lsubCtx z G)) (lsubC z c)
lsubCtx-valid z G c v = validC-lsub z c (lok-lsubCtx z G) v

lsubCtx-loop : {n : Nat} (z : LSub) (G : Ctx n) -> Loop (lctx G) -> Loop (lctx (lsubCtx z G))
lsubCtx-loop z G = loop-lsub z (lok-lsubCtx z G)
