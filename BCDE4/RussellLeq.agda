{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.RussellLeq
--
-- Invariance of judgements under level EQUALITY (bcde.pdf): two level
-- substitutions z, z' that are pointwise equal in the constraints of
-- the target context give convertible instances,
--
--   leq-HasType : Γ ⊢ M : A  ->  Δ ⊢ Mz = Mz' : Az
--   leq-IsType  : Γ ⊢ A      ->  Δ ⊢ Az = Az'
--
-- for Δ related to Γ by z (LSk, LOK of BCDE4.RussellLsub).  Structural
-- recursion on the derivation, along the lines of
-- BCDE4.RussellMetaCong; the level cases use the rules
-- conv-cong-LApp-lvl, conv-Grd-equiv and conv-GLam-equiv, and the
-- instance conversion premise of conv-cong-LApp-lvl is the induction
-- hypothesis on the level body at the instances  l·z, l·z'.
--
-- Corollaries: A(l/α) = A(l'/α) for l = l' (lsub1-cong), hence the
-- level-application congruence with the paper's premises only
-- (mk-conv-cong-LApp-lvl).
------------------------------------------------------------------------

module BCDE4.RussellLeq where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.RussellMetaCong using (subst1-cong-Ty)
open import BCDE4.RussellLsub
open import BCDE4.RussellRelevel using (Skel ; sk-empty ; sk-extend ; CEnt)

------------------------------------------------------------------------
-- Pointwise equal level substitutions
------------------------------------------------------------------------

LEqS : LCtx -> LSub -> LSub -> Set
LEqS T z z' = (i : Nat) -> Valid T (z i) (z' i)

leqL : {T : LCtx} {z z' : LSub} -> LEqS T z z' -> (l : LExpr) -> Valid T (lsubL z l) (lsubL z' l)
leqL e (lvar i)   = e i
leqL e (lsup l m) = v-sup (leqL e l) (leqL e m)
leqL e (lnext l)  = v-next (leqL e l)

leqS-ent : {T T' : LCtx} {z z' : LSub} -> Entails T' T -> LEqS T z z' -> LEqS T' z z'
leqS-ent e q i = valid-ent e (q i)

leqS-lift : {T : LCtx} {z z' : LSub} -> LEqS T z z' -> LEqS (lsubTh lwkS T) (liftL z) (liftL z')
leqS-lift q zero    = v-refl
leqS-lift q (suc i) = valid-shift (q i)

leqS-inst : {T : LCtx} {z : LSub} {l l' : LExpr} -> Valid T l l' -> LEqS T (lconsS l z) (lconsS l' z)
leqS-inst v zero    = v
leqS-inst v (suc i) = v-refl

leqS-inst1 : {T : LCtx} {l l' : LExpr} -> Valid T l l' -> LEqS T (lsub1S l) (lsub1S l')
leqS-inst1 v zero    = v
leqS-inst1 v (suc i) = v-refl

-- the instances of a constraint are equivalent
equivC-leq : {T : LCtx} {z z' : LSub} -> LEqS T z z' -> (c : Constr) -> EquivC T (lsubC z c) (lsubC z' c)
equivC-leq {T} {z} {z'} q (ceq l m) =
  mkSigma (v-trans (v-sym (wk (lsubC z (ceq l m)) (leqL q l)))
            (v-trans (v-hyp lhere) (wk (lsubC z (ceq l m)) (leqL q m))))
          (v-trans (wk (lsubC z' (ceq l m)) (leqL q l))
            (v-trans (v-hyp lhere) (v-sym (wk (lsubC z' (ceq l m)) (leqL q m)))))
  where
    wk : (d : Constr) {a b : LExpr} -> Valid T a b -> Valid (lcons d T) a b
    wk d = valid-ent (ent-wk d)

------------------------------------------------------------------------
-- Entering a level binder and instantiating it:  Γ,α  ~(l·z)~>  Δ
------------------------------------------------------------------------

lsk-cons : {z : LSub} {n : Nat} {G H : Ctx n} (l : LExpr) -> LSk z G H -> LSk (lconsS l z) (addL G) H
lsk-cons l lsk-empty = lsk-empty
lsk-cons {z} l (lsk-extend {A = A} s e) =
  lsk-extend (lsk-cons l s)
    (Eq-trans e (Eq-sym (Eq-trans (lsubE-comp (lconsS l z) lwkS A) (lsubE-ext _ _ (\ i -> refl) A))))

lok-cons : {z : LSub} {n : Nat} (G H : Ctx n) (l : LExpr) -> LOK z G H -> LOK (lconsS l z) (addL G) H
lok-cons {z} G H l ok {d} h =
  let r = lmem-unmap lwkS (lctx G) (Eq-transport (LMem d) (lctx-addL G) h)
      c = fst r
  in Eq-transport (\ e -> ValidC (lctx H) (lsubC (lconsS l z) e)) (Eq-sym (snd (snd r)))
       (Eq-transport (ValidC (lctx H))
         (Eq-sym (Eq-trans (lsubC-comp (lconsS l z) lwkS c) (lsubC-ext _ _ (\ i -> refl) c)))
         (ok (fst (snd r))))

-- the context-level facts under a constraint / a level binder
leqS-addC : {T : LCtx} {z z' : LSub} {n : Nat} (H : Ctx n) (c : Constr) ->
  LEqS (lctx H) z z' -> LEqS (lctx (addC H c)) z z'
leqS-addC H c q = Eq-transport (\ X -> LEqS X _ _) (Eq-sym (lctx-addC H c)) (leqS-ent (ent-wk c) q)

leqS-addL : {z z' : LSub} {n : Nat} (H : Ctx n) ->
  LEqS (lctx H) z z' -> LEqS (lctx (addL H)) (liftL z) (liftL z')
leqS-addL H q = Eq-transport (\ X -> LEqS X _ _) (Eq-sym (lctx-addL H)) (leqS-lift q)

-- instantiating a level binder at the same level on both sides
leqS-same : {T : LCtx} {z z' : LSub} (l : LExpr) -> LEqS T z z' -> LEqS T (lconsS l z) (lconsS l z')
leqS-same l q zero    = v-refl
leqS-same l q (suc i) = q i

-- ... and at two levels made equal by an added constraint
leqS-hyp : {n : Nat} (K : Ctx n) (l l' : LExpr) {z : LSub} ->
  LEqS (lctx (addC K (ceq l l'))) (lconsS l z) (lconsS l' z)
leqS-hyp K l l' zero    = Eq-transport (\ X -> Valid X l l') (Eq-sym (lctx-addC K (ceq l l'))) (v-hyp lhere)
leqS-hyp K l l' (suc i) = v-refl

-- a constraint added to the target
lsk-addCr : {z : LSub} {n : Nat} {G H : Ctx n} (c : Constr) -> LSk z G H -> LSk z G (addC H c)
lsk-addCr c lsk-empty        = lsk-empty
lsk-addCr c (lsk-extend s e) = lsk-extend (lsk-addCr c s) e

lok-addCr : {z : LSub} {n : Nat} (G H : Ctx n) (c : Constr) -> LOK z G H -> LOK z G (addC H c)
lok-addCr {z} G H c ok =
  Eq-transport (\ X -> LSubOK X (lctx G) z) (Eq-sym (lctx-addC H c)) (lsubOK-ent z (ent-wk c) ok)

-- a target related by z has the skeleton of Γz and entails its constraints
lsk-skel : {z : LSub} {n : Nat} {G H : Ctx n} -> LSk z G H -> Skel (lsubCtx z G) H
lsk-skel lsk-empty           = sk-empty
lsk-skel (lsk-extend s refl) = sk-extend (lsk-skel s)

lok-cent : {z : LSub} {n : Nat} (G H : Ctx n) -> LOK z G H -> CEnt H (lsubCtx z G)
lok-cent {z} G H ok {d} h =
  let r = lmem-unmap z (lctx G) (Eq-transport (LMem d) (lctx-lsubCtx z G) h)
  in Eq-transport (ValidC (lctx H)) (Eq-sym (snd (snd r))) (ok (fst (snd r)))

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

mutual
  leq-IsType : {z z' : LSub} {n : Nat} {G H : Ctx n} {A : Expr n} ->
    LSk z G H -> LOK z G H -> LEqS (lctx H) z z' ->
    IsType G A -> ConvTy H (lsubE z A) (lsubE z' A)
  leq-IsType s ok q (is-Ty-from-U d) = conv-Ty-from-U (leq-HasType s ok q d)
  leq-IsType s ok q (is-Pi dA dB) =
    conv-Ty-Pi (lsub-IsType s ok dA) (lsub-IsType (lsk-extend s refl) ok dB)
      (leq-IsType s ok q dA) (leq-IsType (lsk-extend s refl) ok q dB)
  leq-IsType {z} {z'} {G = G} {H = H} s ok q (is-Grd {c = c} dG dA) =
    let s'  = lsk-addC c s
        ok' = lok-addC G H c ok
        q'  = leqS-addC {T = lctx H} H (lsubC z c) q
        wfH = lsub-WfCtx s ok dG
        cA  = leq-IsType s' ok' q' dA
    in conv-Ty-trans (conv-Ty-Grd wfH (lsub-IsType s' ok' dA) cA)
                     (conv-Ty-Grd-equiv wfH (equivC-leq q c) (presup-r-ConvTy cA))
  leq-IsType {G = G} {H = H} s ok q (is-LPi dG dA) =
    conv-Ty-LPi (lsub-WfCtx s ok dG) (lsub-IsType (lsk-addL s) (lok-addL G H ok) dA)
      (leq-IsType (lsk-addL s) (lok-addL G H ok) (leqS-addL H q) dA)

  leq-HasType : {z z' : LSub} {n : Nat} {G H : Ctx n} {M A : Expr n} ->
    LSk z G H -> LOK z G H -> LEqS (lctx H) z z' ->
    HasType G M A -> ConvTm H (lsubE z M) (lsubE z' M) (lsubE z A)
  leq-HasType {z} {z'} {G = G} {H = H} s ok q (ty-GLam {c = c} dG dA dt) =
    let s'  = lsk-addC c s
        ok' = lok-addC G H c ok
        q'  = leqS-addC {T = lctx H} H (lsubC z c) q
        wfH = lsub-WfCtx s ok dG
        sA  = lsub-IsType s' ok' dA
        ct  = leq-HasType s' ok' q' dt
        cA  = leq-IsType s' ok' q' dA
    in conv-trans (conv-cong-GLam wfH sA (lsub-HasType s' ok' dt) ct)
         (conv-trans (conv-cong-GLam-Ty wfH sA cA (presup-r-ConvTm ct))
            (conv-conv (conv-GLam-equiv wfH (equivC-leq q c) (presup-r-ConvTy cA) (ty-conv (presup-r-ConvTm ct) cA))
                       (conv-Ty-sym (conv-Ty-Grd wfH sA cA))))
  leq-HasType s ok q (ty-Emp dG) = conv-refl (ty-Emp (lsub-WfCtx s ok dG))
  leq-HasType s ok q d@(ty-collapse lp dA) = conv-refl (lsub-HasType s ok d)
  leq-HasType {G = G} {H = H} s ok q (ty-LLam dG dA du) =
    let sA = lsub-IsType (lsk-addL s) (lok-addL G H ok) dA
        cu = leq-HasType (lsk-addL s) (lok-addL G H ok) (leqS-addL H q) du
    in conv-trans (conv-cong-LLam (lsub-WfCtx s ok dG) sA (lsub-HasType (lsk-addL s) (lok-addL G H ok) du) cu)
         (conv-cong-LLam-Ty (lsub-WfCtx s ok dG) sA (leq-IsType (lsk-addL s) (lok-addL G H ok) (leqS-addL H q) dA)
            (presup-r-ConvTm cu))
  leq-HasType {z} {z'} {G = G} {H = H} s ok q (ty-LApp {A = A} {t = t} {l = l} dA dt) =
    let sA  = lsub-IsType (lsk-addL s) (lok-addL G H ok) dA
        ct  = leq-HasType s ok q dt
        -- A↑z (l z) = A↑z (l z'), from the IH on the body at l z·z, l z'·z
        cAl : ConvTy H (lsub1 (lsubE (liftL z) A) (lsubL z l)) (lsub1 (lsubE (liftL z) A) (lsubL z' l))
        cAl = Eq-transport (\ X -> ConvTy H X (lsub1 (lsubE (liftL z) A) (lsubL z' l)))
                (Eq-sym (lsub1-liftL z A (lsubL z l)))
                (Eq-transport (ConvTy H (lsubE (lconsS (lsubL z l) z) A))
                  (Eq-sym (lsub1-liftL z A (lsubL z' l)))
                  (leq-IsType (lsk-cons (lsubL z l) s) (lok-cons G H (lsubL z l) ok)
                     (leqS-inst {z = z} (leqL q l)) dA))
        step1 = conv-cong-LApp-lvl sA (lsub-HasType s ok dt) (leqL q l) cAl
        step2 = conv-conv (conv-cong-LApp-fun sA ct) (conv-Ty-sym cAl)
        cA    = leq-IsType (lsk-addL s) (lok-addL G H ok) (leqS-addL H q) dA
        step3 = conv-conv (conv-cong-LApp-Ty {l = lsubL z' l} sA cA (presup-r-ConvTm ct)) (conv-Ty-sym cAl)
    in Eq-transport (\ T -> ConvTm H (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))
                                     (LApp (lsubE (liftL z') A) (lsubE z' t) (lsubL z' l)) T)
         (Eq-sym (lsubE-lsub1 z A l)) (conv-trans step1 (conv-trans step2 step3))
  leq-HasType s ok q d@(ty-var _) = conv-refl (lsub-HasType s ok d)
  leq-HasType s ok q (ty-conv dM dAB) = conv-conv (leq-HasType s ok q dM) (lsub-ConvTy s ok dAB)
  leq-HasType {z} s ok q (ty-U {l = l} dG v) =
    conv-U-lvl (lsub-WfCtx s ok dG) (leqL q l) (valid-lsub z ok v)
  leq-HasType {z} s ok q (ty-cum d v) = conv-cum (leq-HasType s ok q d) (valid-lsub z ok v)
  leq-HasType s ok q (ty-Pi dA dB) =
    conv-cong-Pi (lsub-HasType s ok dA) (lsub-HasType (lsk-extend s refl) ok dB)
      (leq-HasType s ok q dA) (leq-HasType (lsk-extend s refl) ok q dB)
  leq-HasType s ok q (ty-Lam dA dB db) =
    let sA = lsub-IsType s ok dA
        sB = lsub-IsType (lsk-extend s refl) ok dB
        cb = leq-HasType (lsk-extend s refl) ok q db
    in conv-trans (conv-cong-Lam-body sA sB (lsub-HasType (lsk-extend s refl) ok db) cb)
                  (conv-cong-Lam-Ty sA sB (leq-IsType s ok q dA) (leq-IsType (lsk-extend s refl) ok q dB)
                     (presup-r-ConvTm cb))
  leq-HasType {z} {z'} {H = H} s ok q (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    let sA = lsub-IsType s ok dA
        sB = lsub-IsType (lsk-extend s refl) ok dB
        cc = leq-HasType s ok q dc
        ca = leq-HasType s ok q da
        cB = subst1-cong-Ty ca sA sB
        step1 = conv-cong-App-fun sA sB cc (lsub-HasType s ok da)
        step2 = conv-cong-App-arg sA sB (presup-r-ConvTm cc) ca cB
        step3 = conv-conv (conv-cong-App-Ty sA sB (leq-IsType s ok q dA) (leq-IsType (lsk-extend s refl) ok q dB)
                             (presup-r-ConvTm cc) (presup-r-ConvTm ca))
                          (conv-Ty-sym cB)
    in Eq-transport (\ T -> ConvTm H (lsubE z (App A B c a)) (lsubE z' (App A B c a)) T)
         (Eq-sym (lsubE-subst1 z B a)) (conv-trans step1 (conv-trans step2 step3))

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- A(l/α) = A(l'/α)  for  l = l'
lsub1-cong : {n : Nat} {G : Ctx n} {A : Expr n} {l l' : LExpr} ->
  IsType (addL G) A -> Valid (lctx G) l l' -> ConvTy G (lsub1 A l) (lsub1 A l')
lsub1-cong {G = G} {l = l} dA v =
  leq-IsType (lsk-inst G l) (lok-inst G l) (leqS-inst1 v) dA

lsub1-congTm : {n : Nat} {G : Ctx n} {A u : Expr n} {l l' : LExpr} ->
  HasType (addL G) u A -> Valid (lctx G) l l' -> ConvTm G (lsub1 u l) (lsub1 u l') (lsub1 A l)
lsub1-congTm {G = G} {l = l} du v =
  leq-HasType (lsk-inst G l) (lok-inst G l) (leqS-inst1 v) du

-- the level-application congruence with the paper's premises
mk-conv-cong-LApp-lvl : {n : Nat} {G : Ctx n} {A t : Expr n} {l l' : LExpr} ->
  IsType (addL G) A -> HasType G t (LPi A) -> Valid (lctx G) l l' ->
  ConvTm G (LApp A t l) (LApp A t l') (lsub1 A l)
mk-conv-cong-LApp-lvl dA dt v = conv-cong-LApp-lvl dA dt v (lsub1-cong dA v)
