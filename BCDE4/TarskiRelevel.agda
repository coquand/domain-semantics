{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiRelevel
--
-- (The Tarski analogue of BCDE4.RussellRelevel.)
--
-- Changing the level constraints of a context along an entailment:
-- if Γ and Δ have the same term variables and the constraints of Δ
-- entail those of Γ, every judgement of Γ is a judgement of Δ.
-- In particular Γ ⊢ J  ⇒  Γ,ψ ⊢ J  (constraint weakening).
-- Structural recursion on derivations; no renaming is involved.
------------------------------------------------------------------------

module BCDE4.TarskiRelevel where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.TarskiSyntax
open import BCDE4.TarskiTyping

------------------------------------------------------------------------
-- Same term skeleton
------------------------------------------------------------------------

data Skel : {n : Nat} -> Ctx n -> Ctx n -> Set where
  sk-empty  : {Th T : LCtx} -> Skel (empty Th) (empty T)
  sk-extend : {n : Nat} {G H : Ctx n} {A : Expr n} ->
    Skel G H -> Skel (extend G A) (extend H A)

skel-lookup : {n : Nat} {G H : Ctx n} -> Skel G H -> (i : Fin n) ->
  Eq (lookup H i) (lookup G i)
skel-lookup (sk-extend s) fzero    = refl
skel-lookup (sk-extend s) (fsuc i) = Eq-cong wkExpr (skel-lookup s i)

skel-addC : {n : Nat} {G H : Ctx n} (c : Constr) -> Skel G H -> Skel (addC G c) (addC H c)
skel-addC c sk-empty      = sk-empty
skel-addC c (sk-extend s) = sk-extend (skel-addC c s)

skel-addL : {n : Nat} {G H : Ctx n} -> Skel G H -> Skel (addL G) (addL H)
skel-addL sk-empty      = sk-empty
skel-addL (sk-extend s) = sk-extend (skel-addL s)

skel-self : {n : Nat} (G : Ctx n) (c : Constr) -> Skel G (addC G c)
skel-self (empty Th)   c = sk-empty
skel-self (extend G A) c = sk-extend (skel-self G c)

skel-refl : {n : Nat} (G : Ctx n) -> Skel G G
skel-refl (empty Th)   = sk-empty
skel-refl (extend G A) = sk-extend (skel-refl G)

------------------------------------------------------------------------
-- Entailment between the level parts of contexts
------------------------------------------------------------------------

CEnt : {n m : Nat} -> Ctx m -> Ctx n -> Set
CEnt H G = Entails (lctx H) (lctx G)

ent-addC : {n m : Nat} (G : Ctx n) (H : Ctx m) (c : Constr) ->
  CEnt H G -> CEnt (addC H c) (addC G c)
ent-addC G H c e =
  Eq-transport (\ X -> Entails X (lctx (addC G c))) (Eq-sym (lctx-addC H c))
    (Eq-transport (\ Y -> Entails (lcons c (lctx H)) Y) (Eq-sym (lctx-addC G c))
      (ent-lift c e))

ent-addL : {n m : Nat} (G : Ctx n) (H : Ctx m) -> CEnt H G -> CEnt (addL H) (addL G)
ent-addL G H e =
  Eq-transport (\ X -> Entails X (lctx (addL G))) (Eq-sym (lctx-addL H))
    (Eq-transport (\ Y -> Entails (lsubTh lwkS (lctx H)) Y) (Eq-sym (lctx-addL G))
      (ent-lsub lwkS e))

ent-self : {n : Nat} (G : Ctx n) (c : Constr) -> CEnt (addC G c) G
ent-self G c =
  Eq-transport (\ X -> Entails X (lctx G)) (Eq-sym (lctx-addC G c)) (ent-wk c)

-- a constraint valid in G can be removed
ent-valid : {n : Nat} (G : Ctx n) (c : Constr) -> ValidC (lctx G) c -> CEnt G (addC G c)
ent-valid G c v =
  Eq-transport (\ Y -> Entails (lctx G) Y) (Eq-sym (lctx-addC G c))
    (ent-cons c ent-refl v)

------------------------------------------------------------------------
-- Relevelling
------------------------------------------------------------------------

mutual
  relev-WfCtx : {n : Nat} {G H : Ctx n} -> Skel G H -> CEnt H G ->
    WfCtx G -> WfCtx H
  relev-WfCtx sk-empty      e wf-empty       = wf-empty
  relev-WfCtx (sk-extend s) e (wf-extend dA) = wf-extend (relev-IsType s e dA)

  relev-IsType : {n : Nat} {G H : Ctx n} {A : Expr n} -> Skel G H -> CEnt H G ->
    IsType G A -> IsType H A
  relev-IsType s e (is-U dG) = is-U (relev-WfCtx s e dG)
  relev-IsType s e (is-El d) = is-El (relev-HasType s e d)
  relev-IsType s e (is-Emp dG) = is-Emp (relev-WfCtx s e dG)
  relev-IsType s e (is-Pi dA dB) = is-Pi (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
  relev-IsType {G = G} {H = H} s e (is-Grd {c = c} dG dA) =
    is-Grd (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
  relev-IsType {G = G} {H = H} s e (is-LPi dG dA) =
    is-LPi (relev-WfCtx s e dG) (relev-IsType (skel-addL s) (ent-addL G H e) dA)

  relev-HasType : {n : Nat} {G H : Ctx n} {M A : Expr n} -> Skel G H -> CEnt H G ->
    HasType G M A -> HasType H M A
  relev-HasType {G = G} {H = H} s e (ty-GLam {c = c} dG dA dt) =
    ty-GLam (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
            (relev-HasType (skel-addC c s) (ent-addC G H c e) dt)
  relev-HasType {G = G} {H = H} s e (ty-LLam dG dA du) =
    ty-LLam (relev-WfCtx s e dG) (relev-IsType (skel-addL s) (ent-addL G H e) dA)
            (relev-HasType (skel-addL s) (ent-addL G H e) du)
  relev-HasType {G = G} {H = H} s e (ty-LApp dA dt) =
    ty-LApp (relev-IsType (skel-addL s) (ent-addL G H e) dA) (relev-HasType s e dt)
  relev-HasType s e (ty-collapse lp dA) = ty-collapse (loop-ent e lp) (relev-IsType s e dA)
  relev-HasType {H = H} s e (ty-var {i = i} dG) =
    Eq-transport (\ T -> HasType H (Var i) T) (skel-lookup s i) (ty-var (relev-WfCtx s e dG))
  relev-HasType s e (ty-conv dM dAB) = ty-conv (relev-HasType s e dM) (relev-ConvTy s e dAB)
  relev-HasType s e (ty-PiCode da db) =
    ty-PiCode (relev-HasType s e da) (relev-HasType (sk-extend s) e db)
  relev-HasType s e (ty-UCode dG v) = ty-UCode (relev-WfCtx s e dG) (valid-ent e v)
  relev-HasType s e (ty-Lift v da) = ty-Lift (valid-ent e v) (relev-HasType s e da)
  relev-HasType s e (ty-EmpCode dG) = ty-EmpCode (relev-WfCtx s e dG)
  relev-HasType s e (ty-Lam dA dB db) =
    ty-Lam (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB) (relev-HasType (sk-extend s) e db)
  relev-HasType s e (ty-App dA dB dc da) =
    ty-App (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
           (relev-HasType s e dc) (relev-HasType s e da)

  relev-ConvTy : {n : Nat} {G H : Ctx n} {A B : Expr n} -> Skel G H -> CEnt H G ->
    ConvTy G A B -> ConvTy H A B
  relev-ConvTy s e (conv-Ty-refl dA) = conv-Ty-refl (relev-IsType s e dA)
  relev-ConvTy s e (conv-Ty-sym d) = conv-Ty-sym (relev-ConvTy s e d)
  relev-ConvTy s e (conv-Ty-trans d1 d2) = conv-Ty-trans (relev-ConvTy s e d1) (relev-ConvTy s e d2)
  relev-ConvTy s e (conv-Ty-Pi dA dB dAA dBB) =
    conv-Ty-Pi (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
               (relev-ConvTy s e dAA) (relev-ConvTy (sk-extend s) e dBB)
  relev-ConvTy {G = G} {H = H} s e (conv-Ty-Grd {c = c} dG dA dAB) =
    conv-Ty-Grd (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
                (relev-ConvTy (skel-addC c s) (ent-addC G H c e) dAB)
  relev-ConvTy s e (conv-Ty-collapse lp dA) = conv-Ty-collapse (loop-ent e lp) (relev-IsType s e dA)
  relev-ConvTy s e (conv-Ty-El d) = conv-Ty-El (relev-ConvTm s e d)
  relev-ConvTy s e (conv-Ty-U-lvl dG v) = conv-Ty-U-lvl (relev-WfCtx s e dG) (valid-ent e v)
  relev-ConvTy s e (conv-Ty-El-lvl v da) = conv-Ty-El-lvl (valid-ent e v) (relev-HasType s e da)
  relev-ConvTy s e (conv-Ty-El-UCode dG v) = conv-Ty-El-UCode (relev-WfCtx s e dG) (valid-ent e v)
  relev-ConvTy s e (conv-Ty-El-PiCode da db) =
    conv-Ty-El-PiCode (relev-HasType s e da) (relev-HasType (sk-extend s) e db)
  relev-ConvTy s e (conv-Ty-El-Lift v da) = conv-Ty-El-Lift (valid-ent e v) (relev-HasType s e da)
  relev-ConvTy s e (conv-Ty-El-EmpCode dG) = conv-Ty-El-EmpCode (relev-WfCtx s e dG)
  relev-ConvTy s e (conv-Ty-Grd-beta {c = c} v dA) = conv-Ty-Grd-beta (validC-ent c e v) (relev-IsType s e dA)
  relev-ConvTy {G = G} {H = H} s e (conv-Ty-Grd-equiv {c = c} dG q dA) =
    conv-Ty-Grd-equiv (relev-WfCtx s e dG) (equivC-ent e q) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
  relev-ConvTy {G = G} {H = H} s e (conv-Ty-LPi dG dA dAB) =
    conv-Ty-LPi (relev-WfCtx s e dG) (relev-IsType (skel-addL s) (ent-addL G H e) dA)
                (relev-ConvTy (skel-addL s) (ent-addL G H e) dAB)

  relev-ConvTm : {n : Nat} {G H : Ctx n} {M N A : Expr n} -> Skel G H -> CEnt H G ->
    ConvTm G M N A -> ConvTm H M N A
  relev-ConvTm s e (conv-refl dM) = conv-refl (relev-HasType s e dM)
  relev-ConvTm s e (conv-sym d) = conv-sym (relev-ConvTm s e d)
  relev-ConvTm s e (conv-trans d1 d2) = conv-trans (relev-ConvTm s e d1) (relev-ConvTm s e d2)
  relev-ConvTm s e (conv-conv d dAB) = conv-conv (relev-ConvTm s e d) (relev-ConvTy s e dAB)
  relev-ConvTm s e (conv-cong-Lam-body dA dB db dbb) =
    conv-cong-Lam-body (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
                       (relev-HasType (sk-extend s) e db) (relev-ConvTm (sk-extend s) e dbb)
  relev-ConvTm s e (conv-cong-Lam-Ty dA dB dAA dBB db) =
    conv-cong-Lam-Ty (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
                     (relev-ConvTy s e dAA) (relev-ConvTy (sk-extend s) e dBB)
                     (relev-HasType (sk-extend s) e db)
  relev-ConvTm s e (conv-cong-App-fun dA dB dc da) =
    conv-cong-App-fun (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
                      (relev-ConvTm s e dc) (relev-HasType s e da)
  relev-ConvTm s e (conv-cong-App-arg dA dB dc da dBa) =
    conv-cong-App-arg (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
                      (relev-HasType s e dc) (relev-ConvTm s e da) (relev-ConvTy s e dBa)
  relev-ConvTm s e (conv-cong-App-Ty dA dB dAA dBB dc da) =
    conv-cong-App-Ty (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
                     (relev-ConvTy s e dAA) (relev-ConvTy (sk-extend s) e dBB)
                     (relev-HasType s e dc) (relev-HasType s e da)
  relev-ConvTm s e (conv-beta dA dB db da) =
    conv-beta (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB)
              (relev-HasType (sk-extend s) e db) (relev-HasType s e da)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-GLam {c = c} dG dA dt dtt) =
    conv-cong-GLam (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
                   (relev-HasType (skel-addC c s) (ent-addC G H c e) dt)
                   (relev-ConvTm (skel-addC c s) (ent-addC G H c e) dtt)
  relev-ConvTm {G = G} {H = H} s e (conv-GLam-eta {c = c} dG dA dt dt') =
    conv-GLam-eta (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
                  (relev-HasType s e dt) (relev-HasType (skel-addC c s) (ent-addC G H c e) dt')
  relev-ConvTm s e (conv-GLam-beta {c = c} v dA dt) =
    conv-GLam-beta (validC-ent c e v) (relev-IsType s e dA) (relev-HasType s e dt)
  relev-ConvTm s e (conv-collapse lp dA dt) =
    conv-collapse (loop-ent e lp) (relev-IsType s e dA) (relev-HasType s e dt)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-LLam dG dA du duu) =
    conv-cong-LLam (relev-WfCtx s e dG) (relev-IsType (skel-addL s) (ent-addL G H e) dA)
                   (relev-HasType (skel-addL s) (ent-addL G H e) du)
                   (relev-ConvTm (skel-addL s) (ent-addL G H e) duu)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-GLam-Ty {c = c} dG dA dAA dt) =
    conv-cong-GLam-Ty (relev-WfCtx s e dG) (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
      (relev-ConvTy (skel-addC c s) (ent-addC G H c e) dAA) (relev-HasType (skel-addC c s) (ent-addC G H c e) dt)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-LLam-Ty dG dA dAA du) =
    conv-cong-LLam-Ty (relev-WfCtx s e dG) (relev-IsType (skel-addL s) (ent-addL G H e) dA)
      (relev-ConvTy (skel-addL s) (ent-addL G H e) dAA) (relev-HasType (skel-addL s) (ent-addL G H e) du)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-LApp-Ty dA dAA dt) =
    conv-cong-LApp-Ty (relev-IsType (skel-addL s) (ent-addL G H e) dA)
      (relev-ConvTy (skel-addL s) (ent-addL G H e) dAA) (relev-HasType s e dt)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-LApp-fun dA dtt) =
    conv-cong-LApp-fun (relev-IsType (skel-addL s) (ent-addL G H e) dA) (relev-ConvTm s e dtt)
  relev-ConvTm {G = G} {H = H} s e (conv-cong-LApp-lvl dA dt v dAA) =
    conv-cong-LApp-lvl (relev-IsType (skel-addL s) (ent-addL G H e) dA) (relev-HasType s e dt)
                       (valid-ent e v) (relev-ConvTy s e dAA)
  relev-ConvTm {G = G} {H = H} s e (conv-GLam-equiv {c = c} dG q dA dt) =
    conv-GLam-equiv (relev-WfCtx s e dG) (equivC-ent e q)
                    (relev-IsType (skel-addC c s) (ent-addC G H c e) dA)
                    (relev-HasType (skel-addC c s) (ent-addC G H c e) dt)
  relev-ConvTm {G = G} {H = H} s e (conv-LApp-beta dA du) =
    conv-LApp-beta (relev-IsType (skel-addL s) (ent-addL G H e) dA)
                   (relev-HasType (skel-addL s) (ent-addL G H e) du)
  relev-ConvTm {G = G} {H = H} s e (conv-LApp-eta dA dt) =
    conv-LApp-eta (relev-IsType (skel-addL s) (ent-addL G H e) dA) (relev-HasType s e dt)
  relev-ConvTm s e (conv-eta dA dB dc) =
    conv-eta (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB) (relev-HasType s e dc)
  relev-ConvTm s e (conv-cong-PiCode da db daa dbb) =
    conv-cong-PiCode (relev-HasType s e da) (relev-HasType (sk-extend s) e db)
                     (relev-ConvTm s e daa) (relev-ConvTm (sk-extend s) e dbb)
  relev-ConvTm s e (conv-cong-Lift v daa) = conv-cong-Lift (valid-ent e v) (relev-ConvTm s e daa)
  relev-ConvTm s e (conv-Lift-refl v da) = conv-Lift-refl (valid-ent e v) (relev-HasType s e da)
  relev-ConvTm s e (conv-Lift-Lift v w da) =
    conv-Lift-Lift (valid-ent e v) (valid-ent e w) (relev-HasType s e da)
  relev-ConvTm s e (conv-Lift-UCode dG v w) =
    conv-Lift-UCode (relev-WfCtx s e dG) (valid-ent e v) (valid-ent e w)
  relev-ConvTm s e (conv-Lift-PiCode v da db) =
    conv-Lift-PiCode (valid-ent e v) (relev-HasType s e da) (relev-HasType (sk-extend s) e db)
  relev-ConvTm s e (conv-Lift-EmpCode dG v) = conv-Lift-EmpCode (relev-WfCtx s e dG) (valid-ent e v)
  relev-ConvTm s e (conv-UCode-lvl dG v w u) =
    conv-UCode-lvl (relev-WfCtx s e dG) (valid-ent e v) (valid-ent e w) (valid-ent e u)
  relev-ConvTm s e (conv-Lift-lvl v w u da) =
    conv-Lift-lvl (valid-ent e v) (valid-ent e w) (valid-ent e u) (relev-HasType s e da)
  relev-ConvTm s e (conv-PiCode-lvl v da db) =
    conv-PiCode-lvl (valid-ent e v) (relev-HasType s e da) (relev-HasType (sk-extend s) e db)
  relev-ConvTm s e (conv-EmpCode-lvl dG v) = conv-EmpCode-lvl (relev-WfCtx s e dG) (valid-ent e v)

------------------------------------------------------------------------
-- Replacing a constraint by an equivalent one  Γ,ψ ⊢ J  ⇒  Γ,ψ' ⊢ J
------------------------------------------------------------------------

skel-swapC : {n : Nat} (G : Ctx n) (c c' : Constr) -> Skel (addC G c) (addC G c')
skel-swapC (empty Th)   c c' = sk-empty
skel-swapC (extend G A) c c' = sk-extend (skel-swapC G c c')

ent-swapC : {n : Nat} (G : Ctx n) (c c' : Constr) -> ValidC (lcons c' (lctx G)) c ->
  CEnt (addC G c') (addC G c)
ent-swapC G c c' v =
  Eq-transport (\ X -> Entails X (lctx (addC G c))) (Eq-sym (lctx-addC G c'))
    (Eq-transport (\ Y -> Entails (lcons c' (lctx G)) Y) (Eq-sym (lctx-addC G c))
      (ent-cons c (ent-wk c') v))

------------------------------------------------------------------------
-- Constraint weakening  Γ ⊢ J  ⇒  Γ,ψ ⊢ J
------------------------------------------------------------------------

wkC-WfCtx : {n : Nat} {G : Ctx n} (c : Constr) -> WfCtx G -> WfCtx (addC G c)
wkC-WfCtx {G = G} c = relev-WfCtx (skel-self G c) (ent-self G c)

wkC-IsType : {n : Nat} {G : Ctx n} {A : Expr n} (c : Constr) -> IsType G A -> IsType (addC G c) A
wkC-IsType {G = G} c = relev-IsType (skel-self G c) (ent-self G c)

wkC-HasType : {n : Nat} {G : Ctx n} {M A : Expr n} (c : Constr) -> HasType G M A -> HasType (addC G c) M A
wkC-HasType {G = G} c = relev-HasType (skel-self G c) (ent-self G c)

wkC-ConvTy : {n : Nat} {G : Ctx n} {A B : Expr n} (c : Constr) -> ConvTy G A B -> ConvTy (addC G c) A B
wkC-ConvTy {G = G} c = relev-ConvTy (skel-self G c) (ent-self G c)

wkC-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n} (c : Constr) -> ConvTm G M N A -> ConvTm (addC G c) M N A
wkC-ConvTm {G = G} c = relev-ConvTm (skel-self G c) (ent-self G c)

swapC-HasType : {n : Nat} {G : Ctx n} {c c' : Constr} {M A : Expr n} ->
  EquivC (lctx G) c c' -> HasType (addC G c) M A -> HasType (addC G c') M A
swapC-HasType {G = G} {c} {c'} q = relev-HasType (skel-swapC G c c') (ent-swapC G c c' (snd q))

swapC-IsType : {n : Nat} {G : Ctx n} {c c' : Constr} {A : Expr n} ->
  EquivC (lctx G) c c' -> IsType (addC G c) A -> IsType (addC G c') A
swapC-IsType {G = G} {c} {c'} q = relev-IsType (skel-swapC G c c') (ent-swapC G c c' (snd q))
