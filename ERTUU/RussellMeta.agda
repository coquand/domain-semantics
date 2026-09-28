{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.RussellMeta
--
-- Metatheory of the Russell system T_R, as ERTUU.TarskiMeta is for
-- T_T: renaming, weakening, substitution, context conversion and
-- presupposition (both sides of ConvTy/ConvTm, and the type of a
-- typed term).  Structural recursion throughout.
--
-- Types in T_R are the terms of some universe, so "Π A B is a type"
-- needs a common level for A and B; `isType-Pi` raises both with the
-- cumulativity rule.
------------------------------------------------------------------------

module ERTUU.RussellMeta where

open import ERTUU.Basic
open import ERTUU.RussellSyntax
open import ERTUU.RussellTyping

------------------------------------------------------------------------
-- Auxiliary syntactic lemmas
------------------------------------------------------------------------

idSub : {n : Nat} -> Sub n n
idSub i = Var i

substExpr-id : {n : Nat} (e : Expr n) -> Eq (substExpr idSub e) e
substExpr-id (Var i)        = refl
substExpr-id (Pi A B)       =
  Eq-cong2 Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
substExpr-id U          = refl
substExpr-id (Lam A B b)    =
  Eq-cong3 Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) b)
              (substExpr-id b))
substExpr-id (App A B c a)  =
  Eq-cong4 App (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
    (substExpr-id c) (substExpr-id a)

ren-subst1 : {n m : Nat} (r : Ren n m) (B : Expr (suc n)) (a : Expr n)
  -> Eq (renExpr r (subst1 B a))
        (subst1 (renExpr (liftRen r) B) (renExpr r a))
ren-subst1 r B a =
  Eq-trans (ren-subst r (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-ren (subst1Sub (renExpr r a)) (liftRen r) B)))
  where
    ext : (i : Fin _)
        -> Eq (renExpr r (subst1Sub a i))
              (subst1Sub (renExpr r a) (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

subst-subst1 : {h g : Nat} (sigma : Sub h g) (B : Expr (suc g)) (a : Expr g)
  -> Eq (substExpr sigma (subst1 B a))
        (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a))
subst-subst1 sigma B a =
  Eq-trans (subst-subst sigma (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-subst (subst1Sub (substExpr sigma a))
                            (liftSub sigma) B)))
  where
    ext : (i : Fin _)
        -> Eq (substExpr sigma (subst1Sub a i))
              (substExpr (subst1Sub (substExpr sigma a)) (liftSub sigma i))
    ext fzero    = refl
    ext (fsuc i) =
      Eq-sym (Eq-trans (subst-ren (subst1Sub (substExpr sigma a))
                                   wkRen (sigma i))
                       (substExpr-id (sigma i)))

subst1-wk : {n : Nat} (e : Expr n) (a : Expr n)
  -> Eq (substExpr (subst1Sub a) (wkExpr e)) e
subst1-wk e a =
  Eq-trans (subst-ren (subst1Sub a) wkRen e)
    (Eq-trans (substExpr-ext _ idSub (\ i -> refl) e) (substExpr-id e))

liftRen-liftRen-wk-comm : {n m : Nat} (r : Ren n m) (e : Expr (suc n))
  -> Eq (renExpr (liftRen (liftRen r)) (renExpr (liftRen wkRen) e))
        (renExpr (liftRen wkRen) (renExpr (liftRen r) e))
liftRen-liftRen-wk-comm r e =
  Eq-trans (ren-ren (liftRen (liftRen r)) (liftRen wkRen) e)
    (Eq-trans (renExpr-ext _ _ ext e)
      (Eq-sym (ren-ren (liftRen wkRen) (liftRen r) e)))
  where
    ext : (i : Fin _)
        -> Eq (liftRen (liftRen r) (liftRen wkRen i))
              (liftRen wkRen (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

liftSub-liftSub-wk-comm : {h g : Nat} (sigma : Sub h g) (e : Expr (suc g))
  -> Eq (substExpr (liftSub (liftSub sigma)) (renExpr (liftRen wkRen) e))
        (renExpr (liftRen wkRen) (substExpr (liftSub sigma) e))
liftSub-liftSub-wk-comm sigma e =
  Eq-trans (subst-ren (liftSub (liftSub sigma)) (liftRen wkRen) e)
    (Eq-trans (substExpr-ext _ _ ext e)
      (Eq-sym (ren-subst (liftRen wkRen) (liftSub sigma) e)))
  where
    ext : (i : Fin _)
        -> Eq (liftSub (liftSub sigma) (liftRen wkRen i))
              (renExpr (liftRen wkRen) (liftSub sigma i))
    ext fzero    = refl
    ext (fsuc i) =
      Eq-sym (Eq-trans (ren-ren (liftRen wkRen) wkRen (sigma i))
                (Eq-sym (ren-ren wkRen wkRen (sigma i))))

subst1-liftWk-cancel : {n : Nat} (e : Expr (suc n))
  -> Eq (subst1 (renExpr (liftRen wkRen) e) (Var fzero)) e
subst1-liftWk-cancel e =
  Eq-trans (subst-ren (subst1Sub (Var fzero)) (liftRen wkRen) e)
    (Eq-trans (substExpr-ext _ idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) e)
              (substExpr-id e))

------------------------------------------------------------------------
-- Type-preserving renamings
------------------------------------------------------------------------

RenTypes : {n m : Nat} -> Ctx n -> Ctx m -> Ren n m -> Set
RenTypes G H r = (i : Fin _) -> Eq (lookup H (r i)) (renExpr r (lookup G i))

wkRen-RenTypes : {n : Nat} {G : Ctx n} {C : Expr n}
  -> RenTypes G (extend G C) wkRen
wkRen-RenTypes i = refl

liftRen-RenTypes : {n m : Nat} {G : Ctx n} {H : Ctx m}
  {r : Ren n m} {A : Expr n}
  -> RenTypes G H r
  -> RenTypes (extend G A) (extend H (renExpr r A)) (liftRen r)
liftRen-RenTypes {r = r} {A = A} rt fzero = Eq-sym (ren-wk-comm r A)
liftRen-RenTypes {G = G} {r = r} rt (fsuc i) =
  Eq-trans (Eq-cong wkExpr (rt i)) (Eq-sym (ren-wk-comm r (lookup G i)))

------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

WtSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Set
WtSub H G sigma =
  (i : Fin _) -> HasType H (sigma i) (substExpr sigma (lookup G i))

isType-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> IsType G (Pi A B)
isType-Pi (is-Ty-from-U dA) (is-Ty-from-U dB) = is-Ty-from-U (ty-Pi dA dB)

isType-U : {n : Nat} {G : Ctx n} -> WfCtx G -> IsType G U
isType-U wf = is-Ty-from-U (ty-U wf)

mutual

  typing-WfCtx : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A -> WfCtx G
  typing-WfCtx (ty-var dG)         = dG
  typing-WfCtx (ty-conv dM _)      = typing-WfCtx dM
  typing-WfCtx (ty-U dG)           = dG
  typing-WfCtx (ty-Pi dA _)        = typing-WfCtx dA
  typing-WfCtx (ty-Lam dA _ _)     = isType-WfCtx dA
  typing-WfCtx (ty-App dA _ _ _)   = isType-WfCtx dA

  isType-WfCtx : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A -> WfCtx G
  isType-WfCtx (is-Ty-from-U d) = typing-WfCtx d

  presup-l-ConvTy : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B -> IsType G A
  presup-l-ConvTy (conv-Ty-refl dA)        = dA
  presup-l-ConvTy (conv-Ty-sym d)          = presup-r-ConvTy d
  presup-l-ConvTy (conv-Ty-trans d1 _)     = presup-l-ConvTy d1
  presup-l-ConvTy (conv-Ty-Pi dA0 dB0 _ _) = isType-Pi dA0 dB0
  presup-l-ConvTy (conv-Ty-from-U d)       = is-Ty-from-U (presup-l-ConvTm d)

  presup-r-ConvTy : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B -> IsType G B
  presup-r-ConvTy (conv-Ty-refl dA)        = dA
  presup-r-ConvTy (conv-Ty-sym d)          = presup-l-ConvTy d
  presup-r-ConvTy (conv-Ty-trans _ d2)     = presup-r-ConvTy d2
  presup-r-ConvTy (conv-Ty-Pi dA-IT _ dA dB) =
    let dA'-IT = presup-r-ConvTy dA
    in isType-Pi dA'-IT (ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB))
  presup-r-ConvTy (conv-Ty-from-U d)       = is-Ty-from-U (presup-r-ConvTm d)


  ----------------------------------------------------------------------
  -- typing-WfCtx, isType-WfCtx, wfCtx-lookup
  ----------------------------------------------------------------------
  wfCtx-lookup : {n : Nat} {G : Ctx n}
    -> WfCtx G -> (i : Fin n) -> IsType G (lookup G i)
  wfCtx-lookup (wf-extend dA) fzero    = wk-IsType dA dA
  wfCtx-lookup (wf-extend dA) (fsuc i) =
    wk-IsType dA (wfCtx-lookup (isType-WfCtx dA) i)

  ----------------------------------------------------------------------
  -- Renaming preserves IsType
  ----------------------------------------------------------------------
  ren-IsType : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {A : Expr n}
    -> RenTypes G H r -> WfCtx H
    -> IsType G A -> IsType H (renExpr r A)
  ren-IsType rt wfH (is-Ty-from-U d) = is-Ty-from-U (ren-HasType rt wfH d)
  ----------------------------------------------------------------------
  -- Renaming preserves HasType
  ----------------------------------------------------------------------
  ren-HasType : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M A : Expr n}
    -> RenTypes G H r -> WfCtx H
    -> HasType G M A -> HasType H (renExpr r M) (renExpr r A)
  ren-HasType rt wfH (ty-U _)   = ty-U wfH
  ren-HasType rt wfH (ty-Pi dA dB) =
    let dA'  = ren-HasType rt wfH dA
        wfH' = wf-extend (is-Ty-from-U dA')
        rt'  = liftRen-RenTypes rt
    in ty-Pi dA' (ren-HasType rt' wfH' dB)
  ren-HasType {r = r} rt wfH (ty-var {i = i} _) =
    Eq-transport (\ T -> HasType _ (Var (r i)) T) (rt i) (ty-var wfH)
  ren-HasType rt wfH (ty-conv dM dAB) =
    ty-conv (ren-HasType rt wfH dM) (ren-ConvTy rt wfH dAB)
  ren-HasType rt wfH (ty-Lam dA dB db) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in ty-Lam dA' (ren-IsType rt' wfH' dB) (ren-HasType rt' wfH' db)
  ren-HasType {r = r} rt wfH
              (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in Eq-transport
         (\ T -> HasType _
                   (App (renExpr r A) (renExpr (liftRen r) B)
                        (renExpr r c) (renExpr r a)) T)
         (Eq-sym (ren-subst1 r B a))
         (ty-App dA' (ren-IsType rt' wfH' dB)
                     (ren-HasType rt wfH dc) (ren-HasType rt wfH da))
  ----------------------------------------------------------------------
  -- Renaming preserves ConvTy
  ----------------------------------------------------------------------
  ren-ConvTy : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {A B : Expr n}
    -> RenTypes G H r -> WfCtx H
    -> ConvTy G A B -> ConvTy H (renExpr r A) (renExpr r B)
  ren-ConvTy rt wfH (conv-Ty-from-U d) = conv-Ty-from-U (ren-ConvTm rt wfH d)
  ren-ConvTy rt wfH (conv-Ty-refl dA) =
    conv-Ty-refl (ren-IsType rt wfH dA)
  ren-ConvTy rt wfH (conv-Ty-sym d) =
    conv-Ty-sym (ren-ConvTy rt wfH d)
  ren-ConvTy rt wfH (conv-Ty-trans d1 d2) =
    conv-Ty-trans (ren-ConvTy rt wfH d1) (ren-ConvTy rt wfH d2)
  ren-ConvTy rt wfH (conv-Ty-Pi dA0 dB0 dA dB) =
    let dA-IT = ren-IsType rt wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
    in conv-Ty-Pi dA-IT (ren-IsType rt' wfH' dB0) (ren-ConvTy rt wfH dA) (ren-ConvTy rt' wfH' dB)
  ----------------------------------------------------------------------
  -- Renaming preserves ConvTm
  ----------------------------------------------------------------------
  ren-ConvTm : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M N A : Expr n}
    -> RenTypes G H r -> WfCtx H
    -> ConvTm G M N A
    -> ConvTm H (renExpr r M) (renExpr r N) (renExpr r A)
  ren-ConvTm rt wfH (conv-cong-Pi da0 db0 daa' dbb') =
    let da'  = ren-HasType rt wfH da0
        wfH' = wf-extend (is-Ty-from-U da')
        rt'  = liftRen-RenTypes rt
    in conv-cong-Pi da' (ren-HasType rt' wfH' db0) (ren-ConvTm rt wfH daa') (ren-ConvTm rt' wfH' dbb')
  ren-ConvTm rt wfH (conv-refl dM) = conv-refl (ren-HasType rt wfH dM)
  ren-ConvTm rt wfH (conv-sym d)   = conv-sym (ren-ConvTm rt wfH d)
  ren-ConvTm rt wfH (conv-trans d1 d2) =
    conv-trans (ren-ConvTm rt wfH d1) (ren-ConvTm rt wfH d2)
  ren-ConvTm rt wfH (conv-conv dMN dAB) =
    conv-conv (ren-ConvTm rt wfH dMN) (ren-ConvTy rt wfH dAB)
  ren-ConvTm rt wfH (conv-cong-Lam-body dA dB db0 db) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in conv-cong-Lam-body dA' (ren-IsType rt' wfH' dB) (ren-HasType rt' wfH' db0)
                          (ren-ConvTm rt' wfH' db)
  ren-ConvTm rt wfH (conv-cong-Lam-Ty dA0 dB0 dA dB db) =
    let dA-IT = ren-IsType rt wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
    in conv-cong-Lam-Ty dA-IT (ren-IsType rt' wfH' dB0) (ren-ConvTy rt wfH dA) (ren-ConvTy rt' wfH' dB)
                        (ren-HasType rt' wfH' db)
  ren-ConvTm {r = r} rt wfH
             (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a}
                                 dA dB dc da) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a)
        appR = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c') (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-fun dA' (ren-IsType rt' wfH' dB)
                           (ren-ConvTm rt wfH dc) (ren-HasType rt wfH da))
  ren-ConvTm {r = r} rt wfH
             (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'}
                                 dA dB dc da Bsubst-conv) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a)
        appR = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a')
        Bsubst-conv' =
          Eq-transport (\ X -> ConvTy _ X _) (ren-subst1 r B a)
            (Eq-transport (\ Y -> ConvTy _ _ Y) (ren-subst1 r B a')
              (ren-ConvTy rt wfH Bsubst-conv))
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-arg dA' (ren-IsType rt' wfH' dB)
                           (ren-HasType rt wfH dc) (ren-ConvTm rt wfH da)
                           Bsubst-conv')
  ren-ConvTm {r = r} rt wfH
             (conv-cong-App-Ty {A = A} {A' = A'} {B = B} {B' = B'}
                                {c = c} {a = a} dA0 dB0 dA dB dc da) =
    let dA-IT = ren-IsType rt wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
        appL  = App (renExpr r A) (renExpr (liftRen r) B)
                    (renExpr r c) (renExpr r a)
        appR  = App (renExpr r A') (renExpr (liftRen r) B')
                    (renExpr r c) (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-Ty dA-IT (ren-IsType rt' wfH' dB0) (ren-ConvTy rt wfH dA) (ren-ConvTy rt' wfH' dB)
                          (ren-HasType rt wfH dc) (ren-HasType rt wfH da))
  ren-ConvTm {r = r} rt wfH
             (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        core = conv-beta dA' (ren-IsType rt' wfH' dB)
                         (ren-HasType rt' wfH' db) (ren-HasType rt wfH da)
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (Lam (renExpr r A) (renExpr (liftRen r) B)
                        (renExpr (liftRen r) b))
                   (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL _ T)
                    (Eq-sym (ren-subst1 r B a))
        (Eq-transport (\ M -> ConvTm _ appL M _)
                      (Eq-sym (ren-subst1 r b a))
          core)
  ren-ConvTm {H = H} {r = r} rt wfH
             (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let dA'  = ren-IsType rt wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        core = conv-eta dA' (ren-IsType rt' wfH' dB) (ren-HasType rt wfH dc)
        eA   = Eq-sym (ren-wk-comm r A)
        eC   = Eq-sym (ren-wk-comm r c)
        eB   = Eq-sym (liftRen-liftRen-wk-comm r B)
        app-eq = Eq-cong4 App eA eB eC refl
        lam-eq = Eq-cong (Lam (renExpr r A) (renExpr (liftRen r) B)) app-eq
    in Eq-transport
         (\ M -> ConvTm H (renExpr r c) M
                   (Pi (renExpr r A) (renExpr (liftRen r) B)))
         lam-eq core
  ----------------------------------------------------------------------
  -- Weakening corollaries
  ----------------------------------------------------------------------
  wk-IsType : {n : Nat} {G : Ctx n} {C A : Expr n}
    -> IsType G C -> IsType G A -> IsType (extend G C) (wkExpr A)
  wk-IsType {G = G} {C = C} dC dA =
    ren-IsType (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) dA

  wk-HasType : {n : Nat} {G : Ctx n} {C M A : Expr n}
    -> IsType G C -> HasType G M A
    -> HasType (extend G C) (wkExpr M) (wkExpr A)
  wk-HasType {G = G} {C = C} dC dM =
    ren-HasType (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) dM

  wk-ConvTy : {n : Nat} {G : Ctx n} {C A B : Expr n}
    -> IsType G C -> ConvTy G A B
    -> ConvTy (extend G C) (wkExpr A) (wkExpr B)
  wk-ConvTy {G = G} {C = C} dC d =
    ren-ConvTy (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) d

  wk-ConvTm : {n : Nat} {G : Ctx n} {C M N A : Expr n}
    -> IsType G C -> ConvTm G M N A
    -> ConvTm (extend G C) (wkExpr M) (wkExpr N) (wkExpr A)
  wk-ConvTm {G = G} {C = C} dC d =
    ren-ConvTm (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) d

  ----------------------------------------------------------------------
  -- Lifting a well-typed substitution
  ----------------------------------------------------------------------
  liftSub-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g}
    -> WtSub H G sigma -> WfCtx H -> IsType G A
    -> WtSub (extend H (substExpr sigma A)) (extend G A) (liftSub sigma)
  liftSub-WtSub {sigma = sigma} {A = A} ws wfH dA fzero =
    Eq-transport (\ T -> HasType (extend _ (substExpr sigma A)) (Var fzero) T)
      (Eq-sym (Eq-trans (subst-ren (liftSub sigma) wkRen A)
                        (Eq-sym (ren-subst wkRen sigma A))))
      (ty-var (wf-extend (subst-IsType ws wfH dA)))
  liftSub-WtSub {H = H} {G = G} {sigma = sigma} {A = A} ws wfH dA (fsuc i) =
    Eq-transport
      (\ T -> HasType (extend H (substExpr sigma A)) (wkExpr (sigma i)) T)
      (Eq-sym (Eq-trans (subst-ren (liftSub sigma) wkRen (lookup G i))
                        (Eq-sym (ren-subst wkRen sigma (lookup G i)))))
      (wk-HasType (subst-IsType ws wfH dA) (ws i))

  ----------------------------------------------------------------------
  -- Substitution preserves IsType
  ----------------------------------------------------------------------
  subst-IsType : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> IsType G A -> IsType H (substExpr sigma A)
  subst-IsType ws wfH (is-Ty-from-U d) = is-Ty-from-U (subst-HasType ws wfH d)
  ----------------------------------------------------------------------
  -- Substitution preserves HasType
  ----------------------------------------------------------------------
  subst-HasType : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> HasType G M A -> HasType H (substExpr sigma M) (substExpr sigma A)
  subst-HasType ws wfH (ty-U _)   = ty-U wfH
  subst-HasType ws wfH (ty-Pi dA dB) =
    let dA'  = subst-HasType ws wfH dA
        wfH' = wf-extend (is-Ty-from-U dA')
        ws'  = liftSub-WtSub ws wfH (is-Ty-from-U dA)
    in ty-Pi dA' (subst-HasType ws' wfH' dB)
  subst-HasType ws wfH (ty-var {i = i} _) = ws i
  subst-HasType ws wfH (ty-conv dM dAB) =
    ty-conv (subst-HasType ws wfH dM) (subst-ConvTy ws wfH dAB)
  subst-HasType ws wfH (ty-Lam dA dB db) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
    in ty-Lam dA' (subst-IsType ws' wfH' dB) (subst-HasType ws' wfH' db)
  subst-HasType {sigma = sigma} ws wfH
                (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appE = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
    in Eq-transport (\ T -> HasType _ appE T)
        (Eq-sym (subst-subst1 sigma B a))
        (ty-App dA' (subst-IsType ws' wfH' dB)
                    (subst-HasType ws wfH dc) (subst-HasType ws wfH da))
  ----------------------------------------------------------------------
  -- Substitution preserves ConvTy
  ----------------------------------------------------------------------
  subst-ConvTy : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A B : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> ConvTy G A B -> ConvTy H (substExpr sigma A) (substExpr sigma B)
  subst-ConvTy ws wfH (conv-Ty-from-U d) = conv-Ty-from-U (subst-ConvTm ws wfH d)
  subst-ConvTy ws wfH (conv-Ty-refl dA) =
    conv-Ty-refl (subst-IsType ws wfH dA)
  subst-ConvTy ws wfH (conv-Ty-sym d) =
    conv-Ty-sym (subst-ConvTy ws wfH d)
  subst-ConvTy ws wfH (conv-Ty-trans d1 d2) =
    conv-Ty-trans (subst-ConvTy ws wfH d1) (subst-ConvTy ws wfH d2)
  subst-ConvTy ws wfH (conv-Ty-Pi dA0 dB0 dA dB) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
    in conv-Ty-Pi dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
  ----------------------------------------------------------------------
  -- Substitution preserves ConvTm
  ----------------------------------------------------------------------
  subst-ConvTm : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M N A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> ConvTm G M N A
    -> ConvTm H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A)
  subst-ConvTm ws wfH (conv-cong-Pi da0 db0 daa' dbb') =
    let da'  = subst-HasType ws wfH da0
        wfH' = wf-extend (is-Ty-from-U da')
        ws'  = liftSub-WtSub ws wfH (is-Ty-from-U da0)
    in conv-cong-Pi da' (subst-HasType ws' wfH' db0) (subst-ConvTm ws wfH daa') (subst-ConvTm ws' wfH' dbb')
  subst-ConvTm ws wfH (conv-refl dM) = conv-refl (subst-HasType ws wfH dM)
  subst-ConvTm ws wfH (conv-sym d)   = conv-sym (subst-ConvTm ws wfH d)
  subst-ConvTm ws wfH (conv-trans d1 d2) =
    conv-trans (subst-ConvTm ws wfH d1) (subst-ConvTm ws wfH d2)
  subst-ConvTm ws wfH (conv-conv dMN dAB) =
    conv-conv (subst-ConvTm ws wfH dMN) (subst-ConvTy ws wfH dAB)
  subst-ConvTm ws wfH (conv-cong-Lam-body dA dB db0 db) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
    in conv-cong-Lam-body dA' (subst-IsType ws' wfH' dB) (subst-HasType ws' wfH' db0)
                          (subst-ConvTm ws' wfH' db)
  subst-ConvTm ws wfH (conv-cong-Lam-Ty dA0 dB0 dA dB db) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
    in conv-cong-Lam-Ty dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
                        (subst-HasType ws' wfH' db)
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a}
                                   dA dB dc da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
        appR = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c') (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-fun dA' (subst-IsType ws' wfH' dB)
                           (subst-ConvTm ws wfH dc) (subst-HasType ws wfH da))
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'}
                                   dA dB dc da Bsubst-conv) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
        appR = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a')
        Bsubst-conv' =
          Eq-transport (\ X -> ConvTy _ X _) (subst-subst1 sigma B a)
            (Eq-transport (\ Y -> ConvTy _ _ Y) (subst-subst1 sigma B a')
              (subst-ConvTy ws wfH Bsubst-conv))
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-arg dA' (subst-IsType ws' wfH' dB)
                           (subst-HasType ws wfH dc) (subst-ConvTm ws wfH da)
                           Bsubst-conv')
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-Ty {A = A} {A' = A'} {B = B} {B' = B'}
                                  {c = c} {a = a} dA0 dB0 dA dB dc da) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
        appL  = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                    (substExpr sigma c) (substExpr sigma a)
        appR  = App (substExpr sigma A') (substExpr (liftSub sigma) B')
                    (substExpr sigma c) (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-Ty dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
                          (subst-HasType ws wfH dc) (subst-HasType ws wfH da))
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        core = conv-beta dA' (subst-IsType ws' wfH' dB)
                         (subst-HasType ws' wfH' db)
                         (subst-HasType ws wfH da)
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (Lam (substExpr sigma A) (substExpr (liftSub sigma) B)
                        (substExpr (liftSub sigma) b))
                   (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL _ T)
        (Eq-sym (subst-subst1 sigma B a))
        (Eq-transport (\ M -> ConvTm _ appL M _)
          (Eq-sym (subst-subst1 sigma b a))
          core)
  subst-ConvTm {H = H} {sigma = sigma} ws wfH
               (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        core = conv-eta dA' (subst-IsType ws' wfH' dB)
                            (subst-HasType ws wfH dc)
        eA   = Eq-sym
                (Eq-trans (subst-ren (liftSub sigma) wkRen A)
                          (Eq-sym (ren-subst wkRen sigma A)))
        eC   = Eq-sym
                (Eq-trans (subst-ren (liftSub sigma) wkRen c)
                          (Eq-sym (ren-subst wkRen sigma c)))
        eB   = Eq-sym (liftSub-liftSub-wk-comm sigma B)
        app-eq = Eq-cong4 App eA eB eC refl
        lam-eq = Eq-cong (Lam (substExpr sigma A) (substExpr (liftSub sigma) B))
                          app-eq
    in Eq-transport
         (\ M -> ConvTm H (substExpr sigma c) M
                   (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)))
         lam-eq core
  ----------------------------------------------------------------------
  -- Identity-substitution-with-conversion (for context conversion)
  ----------------------------------------------------------------------
  ctx-conv-WtSub : {n : Nat} {G : Ctx n} {A A' : Expr n}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> WtSub (extend G A') (extend G A) idSub
  ctx-conv-WtSub {G = G} {A = A} {A' = A'} dA dA' AAconv fzero =
    Eq-transport (\ T -> HasType (extend G A') (Var fzero) T)
      (Eq-sym (Eq-trans
        (substExpr-ext idSub _ (\ i -> refl) (wkExpr A))
        (substExpr-id (wkExpr A))))
      (ty-conv (ty-var (wf-extend dA'))
               (wk-ConvTy dA' (conv-Ty-sym AAconv)))
  ctx-conv-WtSub {G = G} {A' = A'} dA dA' AAconv (fsuc i) =
    Eq-transport (\ T -> HasType (extend G A') (Var (fsuc i)) T)
      (Eq-sym (Eq-trans
        (substExpr-ext idSub _ (\ j -> refl) (wkExpr (lookup G i)))
        (substExpr-id (wkExpr (lookup G i)))))
      (ty-var (wf-extend dA'))

  ----------------------------------------------------------------------
  -- Context conversion
  ----------------------------------------------------------------------
  ctx-conv-IsType : {n : Nat} {G : Ctx n} {A A' : Expr n} {B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> IsType (extend G A) B -> IsType (extend G A') B
  ctx-conv-IsType {B = B} dA dA' AAconv d =
    let d' = subst-IsType (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> IsType (extend _ _) X) (substExpr-id B) d'

  ctx-conv-HasType : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> HasType (extend G A) M B -> HasType (extend G A') M B
  ctx-conv-HasType {M = M} {B = B} dA dA' AAconv d =
    let d' = subst-HasType (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> HasType (extend _ _) X B) (substExpr-id M)
        (Eq-transport (\ Y -> HasType (extend _ _) (substExpr idSub M) Y)
          (substExpr-id B) d')

  ctx-conv-ConvTy : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {B C : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> ConvTy (extend G A) B C -> ConvTy (extend G A') B C
  ctx-conv-ConvTy {B = B} {C = C} dA dA' AAconv d =
    let d' = subst-ConvTy (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> ConvTy (extend _ _) X C) (substExpr-id B)
        (Eq-transport (\ Y -> ConvTy (extend _ _) (substExpr idSub B) Y)
          (substExpr-id C) d')

  ctx-conv-ConvTm : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M N B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> ConvTm (extend G A) M N B -> ConvTm (extend G A') M N B
  ctx-conv-ConvTm {M = M} {N = N} {B = B} dA dA' AAconv d =
    let d' = subst-ConvTm (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> ConvTm (extend _ _) X N B) (substExpr-id M)
        (Eq-transport (\ Y -> ConvTm (extend _ _) (substExpr idSub M) Y B)
          (substExpr-id N)
          (Eq-transport
            (\ Z -> ConvTm (extend _ _) (substExpr idSub M) (substExpr idSub N) Z)
            (substExpr-id B) d'))

  ----------------------------------------------------------------------
  -- subst1-WtSub: WtSub for the single-substitution (subst1Sub a)
  ----------------------------------------------------------------------
  subst1-WtSub : {n : Nat} {G : Ctx n} {A : Expr n} {a : Expr n}
    -> IsType G A -> HasType G a A
    -> WtSub G (extend G A) (subst1Sub a)
  subst1-WtSub {a = a} dA da fzero =
    Eq-transport (\ T -> HasType _ a T) (Eq-sym (subst1-wk _ a)) da
  subst1-WtSub {G = G} {a = a} dA da (fsuc i) =
    Eq-transport (\ T -> HasType _ (Var i) T)
      (Eq-sym (subst1-wk (lookup G i) a))
      (ty-var (isType-WfCtx dA))

  ----------------------------------------------------------------------
  -- Left-side presupposition for ConvTy
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- Right-side presupposition for ConvTy
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- Left-side presupposition for ConvTm
  ----------------------------------------------------------------------
  presup-l-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A -> HasType G M A
  presup-l-ConvTm (conv-cong-Pi da0 db0 _ _) = ty-Pi da0 db0
  presup-l-ConvTm (conv-refl dM)              = dM
  presup-l-ConvTm (conv-sym d)                = presup-r-ConvTm d
  presup-l-ConvTm (conv-trans d1 _)           = presup-l-ConvTm d1
  presup-l-ConvTm (conv-conv dMN dAB)         =
    ty-conv (presup-l-ConvTm dMN) dAB
  presup-l-ConvTm (conv-cong-Lam-body dA dB db0 _) =
    ty-Lam dA dB db0
  presup-l-ConvTm (conv-cong-Lam-Ty dA0 dB0 _ _ db) =
    ty-Lam dA0 dB0 db
  presup-l-ConvTm (conv-cong-App-fun dA dB dc da) =
    ty-App dA dB (presup-l-ConvTm dc) da
  presup-l-ConvTm (conv-cong-App-arg dA dB dc da _) =
    ty-App dA dB dc (presup-l-ConvTm da)
  presup-l-ConvTm (conv-cong-App-Ty dA0 _ _ dB dc da) =
    ty-App dA0 (presup-l-ConvTy dB) dc da
  presup-l-ConvTm (conv-beta dA dB db da)     =
    ty-App dA dB (ty-Lam dA dB db) da
  presup-l-ConvTm (conv-eta _ _ dc)           = dc
  ----------------------------------------------------------------------
  -- Right-side presupposition for ConvTm
  ----------------------------------------------------------------------
  presup-r-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A -> HasType G N A
  presup-r-ConvTm (conv-cong-Pi da0 _ daa' dbb') =
    let dr     = presup-r-ConvTm daa'
        dl-IT  = is-Ty-from-U da0
        dr-IT  = is-Ty-from-U dr
        dbb'-r = ctx-conv-HasType dl-IT dr-IT (conv-Ty-from-U daa') (presup-r-ConvTm dbb')
    in ty-Pi dr dbb'-r
  presup-r-ConvTm (conv-refl dM)              = dM
  presup-r-ConvTm (conv-sym d)                = presup-l-ConvTm d
  presup-r-ConvTm (conv-trans _ d2)           = presup-r-ConvTm d2
  presup-r-ConvTm (conv-conv dMN dAB)         =
    ty-conv (presup-r-ConvTm dMN) dAB
  presup-r-ConvTm (conv-cong-Lam-body dA dB _ db) =
    ty-Lam dA dB (presup-r-ConvTm db)
  presup-r-ConvTm (conv-cong-Lam-Ty dA-IT dB-IT dA dB db) =
    let dA'-IT = presup-r-ConvTy dA
        dB'-IT = ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB)
        db'    = ctx-conv-HasType dA-IT dA'-IT dA (ty-conv db dB)
    in ty-conv (ty-Lam dA'-IT dB'-IT db')
               (conv-Ty-sym (conv-Ty-Pi dA-IT dB-IT dA dB))
  presup-r-ConvTm (conv-cong-App-fun dA dB dc da) =
    ty-App dA dB (presup-r-ConvTm dc) da
  presup-r-ConvTm (conv-cong-App-arg dA dB dc da Bsubst-conv) =
    ty-conv (ty-App dA dB dc (presup-r-ConvTm da))
            (conv-Ty-sym Bsubst-conv)
  presup-r-ConvTm (conv-cong-App-Ty dA-IT _ dA dB dc da) =
    let dA'-IT = presup-r-ConvTy dA
        dB'-IT = ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB)
        dc'    = ty-conv dc (conv-Ty-Pi dA-IT (presup-l-ConvTy dB) dA dB)
        da'    = ty-conv da dA
        result-app = ty-App dA'-IT dB'-IT dc' da'
        -- subst1 B' a = subst1 B a (substituting same a into B B')
        Bsubst : ConvTy _ _ _
        Bsubst = subst-ConvTy (subst1-WtSub dA-IT da)
                              (isType-WfCtx dA-IT)
                              (conv-Ty-sym dB)
    in ty-conv result-app Bsubst
  presup-r-ConvTm (conv-beta {A = A} {B = B} {b = b} {a = a}
                              dA dB db da) =
    subst-HasType (subst1-WtSub dA da) (isType-WfCtx dA) db
  presup-r-ConvTm {G = G} (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let wfG-A = wf-extend dA
        c-wk  = wk-HasType dA dc
        v0    = ty-var {G = extend G A} {i = fzero} wfG-A
        A-wk-IT = wk-IsType dA dA
        B-wk-IT = ren-IsType
                    (liftRen-RenTypes
                       (wkRen-RenTypes {G = G} {C = A}))
                    (wf-extend A-wk-IT) dB
        appE  = App (wkExpr A) (renExpr (liftRen wkRen) B)
                    (wkExpr c) (Var fzero)
        body : HasType (extend G A) appE
                       (subst1 (renExpr (liftRen wkRen) B) (Var fzero))
        body = ty-App A-wk-IT B-wk-IT c-wk v0
        body' = Eq-transport (\ T -> HasType (extend G A) appE T)
                  (subst1-liftWk-cancel B) body
    in ty-Lam dA dB body'
------------------------------------------------------------------------
-- The type of a typed term is a type
------------------------------------------------------------------------

typing-IsType : {n : Nat} {G : Ctx n} {M A : Expr n}
  -> HasType G M A -> IsType G A
typing-IsType (ty-var {i = i} dG)  = wfCtx-lookup dG i
typing-IsType (ty-conv _ dAB)      = presup-r-ConvTy dAB
typing-IsType (ty-U dG)            = isType-U dG
typing-IsType (ty-Pi dA _)         = isType-U (typing-WfCtx dA)
typing-IsType (ty-Lam dA dB _)     = isType-Pi dA dB
typing-IsType (ty-App dA dB _ da)  =
  subst-IsType (subst1-WtSub dA da) (isType-WfCtx dA) dB

------------------------------------------------------------------------
-- The binder congruences with their presupposition premises filled in:
-- these are the rules of the paper
------------------------------------------------------------------------

mk-conv-Ty-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> ConvTy G (Pi A B) (Pi A' B')
mk-conv-Ty-Pi dA dB = conv-Ty-Pi (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB

mk-conv-cong-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
  -> ConvTm G A A' U -> ConvTm (extend G A) B B' U
  -> ConvTm G (Pi A B) (Pi A' B') U
mk-conv-cong-Pi dA dB = conv-cong-Pi (presup-l-ConvTm dA) (presup-l-ConvTm dB) dA dB

mk-conv-cong-Lam-Ty : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' b : Expr (suc n)}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> HasType (extend G A) b B
  -> ConvTm G (Lam A B b) (Lam A' B' b) (Pi A B)
mk-conv-cong-Lam-Ty dA dB db = conv-cong-Lam-Ty (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB db

mk-conv-cong-App-Ty : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
  {c a : Expr n}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> HasType G c (Pi A B) -> HasType G a A
  -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)
mk-conv-cong-App-Ty dA dB dc da = conv-cong-App-Ty (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB dc da

typing-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
  -> ConvTm G M N A -> Pair (HasType G M A) (HasType G N A)
typing-ConvTm d = mkSigma (presup-l-ConvTm d) (presup-r-ConvTm d)
