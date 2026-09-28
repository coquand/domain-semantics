{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.RussellInversion
--
-- Inversion of T_R typing in the presence of cumulativity (Sterbac's
-- RussellInversion with universe levels).  A typing derivation ends
-- with its principal rule followed by conversions and cumulativity
-- steps, summarised by
--
--   SubTy G P T :=  Γ ⊢ P = T
--               or Γ ⊢ P = U_k and Γ ⊢ T = U_m with k ⩽ m.
--
-- In a loop-free context (U-injectivity, from the model).  Constraint
-- and level products are large: they have no typing (only IsType).
------------------------------------------------------------------------

module BCDE4.RussellInversion where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.Main using (UInj)

------------------------------------------------------------------------
-- The order of levels
------------------------------------------------------------------------

leL-self : {Th : LCtx} (l : LExpr) -> LeL Th l l
leL-self l = leL-refl v-refl

leL-supl : {Th : LCtx} (l m : LExpr) -> LeL Th l (lsup l m)
leL-supl l m = v-trans (v-sym v-assoc) (v-sup v-idem v-refl)

leL-supr : {Th : LCtx} (l m : LExpr) -> LeL Th m (lsup l m)
leL-supr l m =
  v-trans (v-sup v-refl v-comm) (v-trans (v-sym v-assoc) (v-trans (v-sup v-idem v-refl) v-comm))

leL-lub : {Th : LCtx} {l m p : LExpr} -> LeL Th l p -> LeL Th m p -> LeL Th (lsup l m) p
leL-lub lp mp = v-trans v-assoc (v-trans (v-sup v-refl mp) lp)

leL-sup-mono : {Th : LCtx} {l l' m m' : LExpr} -> LeL Th l l' -> LeL Th m m' -> LeL Th (lsup l m) (lsup l' m')
leL-sup-mono {l' = l'} {m' = m'} a b =
  leL-lub (leL-trans a (leL-supl l' m')) (leL-trans b (leL-supr l' m'))

-- a universe typing moved along a level equality
U-resp : {n : Nat} {G : Ctx n} {M : Expr n} {l l' : LExpr} -> Valid (lctx G) l l' -> HasType G M (U l) -> HasType G M (U l')
U-resp v d = ty-cum d (leL-refl v)

U-resp-Tm : {n : Nat} {G : Ctx n} {M N : Expr n} {l l' : LExpr} -> Valid (lctx G) l l' -> ConvTm G M N (U l) -> ConvTm G M N (U l')
U-resp-Tm v d = conv-cum d (leL-refl v)

------------------------------------------------------------------------
-- Large types have no typing
------------------------------------------------------------------------

hasType-Grd-absurd : {n : Nat} {G : Ctx n} {c : Constr} {A T : Expr n} -> HasType G (Grd c A) T -> Empty
hasType-Grd-absurd (ty-conv d _) = hasType-Grd-absurd d
hasType-Grd-absurd (ty-cum d _)  = hasType-Grd-absurd d

hasType-LPi-absurd : {n : Nat} {G : Ctx n} {A T : Expr n} -> HasType G (LPi A) T -> Empty
hasType-LPi-absurd (ty-conv d _) = hasType-LPi-absurd d
hasType-LPi-absurd (ty-cum d _)  = hasType-LPi-absurd d

------------------------------------------------------------------------
-- The relation SubTy
------------------------------------------------------------------------

data SubTy {n : Nat} (G : Ctx n) (P T : Expr n) : Set where
  sub-conv : ConvTy G P T -> SubTy G P T
  sub-cum  : (k m : LExpr) -> LeL (lctx G) k m -> ConvTy G P (U k) -> ConvTy G T (U m) -> SubTy G P T

Sub-refl : {n : Nat} {G : Ctx n} {P : Expr n} -> IsType G P -> SubTy G P P
Sub-refl dP = sub-conv (conv-Ty-refl dP)

Sub-conv-right : {n : Nat} {G : Ctx n} {P T T' : Expr n} -> SubTy G P T -> ConvTy G T T' -> SubTy G P T'
Sub-conv-right (sub-conv c)           c' = sub-conv (conv-Ty-trans c c')
Sub-conv-right (sub-cum k m le cP cT) c' = sub-cum k m le cP (conv-Ty-trans (conv-Ty-sym c') cT)

Sub-conv-left : {n : Nat} {G : Ctx n} {P P' T : Expr n} -> ConvTy G P' P -> SubTy G P T -> SubTy G P' T
Sub-conv-left c' (sub-conv c)           = sub-conv (conv-Ty-trans c' c)
Sub-conv-left c' (sub-cum k m le cP cT) = sub-cum k m le (conv-Ty-trans c' cP) cT

-- one cumulativity step on the right
Sub-cum : {n : Nat} {G : Ctx n} {P : Expr n} {l m : LExpr} -> LoopFree (lctx G) ->
  SubTy G P (U l) -> LeL (lctx G) l m -> SubTy G P (U m)
Sub-cum {l = l} {m = m} lf (sub-conv c) le =
  sub-cum l m le c (conv-Ty-refl (isType-U (isType-WfCtx (presup-r-ConvTy c))))
Sub-cum {l = l} {m = m} lf (sub-cum k m' le' cP cT) le =
  sub-cum k m (leL-trans le' (leL-trans (leL-refl (v-sym (UInj lf cT))) le)) cP
    (conv-Ty-refl (isType-U (isType-WfCtx (presup-r-ConvTy cT))))

-- moving a typing / a conversion up along Sub
lift-HasType : {n : Nat} {G : Ctx n} {M P T : Expr n} -> HasType G M P -> SubTy G P T -> HasType G M T
lift-HasType d (sub-conv c)           = ty-conv d c
lift-HasType d (sub-cum k m le cP cT) = ty-conv (ty-cum (ty-conv d cP) le) (conv-Ty-sym cT)

lift-ConvTm : {n : Nat} {G : Ctx n} {M N P T : Expr n} -> ConvTm G M N P -> SubTy G P T -> ConvTm G M N T
lift-ConvTm d (sub-conv c)           = conv-conv d c
lift-ConvTm d (sub-cum k m le cP cT) = conv-conv (conv-cum (conv-conv d cP) le) (conv-Ty-sym cT)

------------------------------------------------------------------------
-- Inversion lemmas (loop-free contexts)
------------------------------------------------------------------------

inv-Var : {n : Nat} {G : Ctx n} {i : Fin n} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G (Var i) T -> Pair (WfCtx G) (SubTy G (lookup G i) T)
inv-Var lf (ty-var {i = i} wf) = mkSigma wf (Sub-refl (wfCtx-lookup wf i))
inv-Var lf (ty-conv d c)       = let r = inv-Var lf d in mkSigma (fst r) (Sub-conv-right (snd r) c)
inv-Var lf (ty-cum d le)       = let r = inv-Var lf d in mkSigma (fst r) (Sub-cum lf (snd r) le)

-- U_l : U_{l⁺}, the least universe containing U_l
inv-U : {n : Nat} {G : Ctx n} {l : LExpr} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G (U l) T -> Pair (WfCtx G) (SubTy G (U (lnext l)) T)
inv-U {l = l} lf (ty-U {m = m} wf lt) =
  mkSigma wf (sub-cum (lnext l) m lt (conv-Ty-refl (isType-U wf)) (conv-Ty-refl (isType-U wf)))
inv-U lf (ty-conv d c)  = let r = inv-U lf d in mkSigma (fst r) (Sub-conv-right (snd r) c)
inv-U lf (ty-cum d le)  = let r = inv-U lf d in mkSigma (fst r) (Sub-cum lf (snd r) le)

-- ∅ : U_l for every l (there is no least one)
inv-Emp : {n : Nat} {G : Ctx n} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G Emp T -> Pair (WfCtx G) (Sigma LExpr (\ l -> SubTy G (U l) T))
inv-Emp lf (ty-Emp {l = l} wf) = mkSigma wf (mkSigma l (Sub-refl (isType-U wf)))
inv-Emp lf (ty-collapse lp _)  = absurd (lf lp)
inv-Emp lf (ty-conv d c)       =
  let r = inv-Emp lf d in mkSigma (fst r) (mkSigma (fst (snd r)) (Sub-conv-right (snd (snd r)) c))
inv-Emp lf (ty-cum d le)       =
  let r = inv-Emp lf d in mkSigma (fst r) (mkSigma (fst (snd r)) (Sub-cum lf (snd (snd r)) le))

record InvPi {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvPi
  field
    lvl : LExpr
    dA  : HasType G A (U lvl)
    dB  : HasType (extend G A) B (U lvl)
    sub : SubTy G (U lvl) T

inv-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G (Pi A B) T -> InvPi G A B T
inv-Pi lf (ty-Pi {l = l} dA dB) = mkInvPi l dA dB (Sub-refl (isType-U (typing-WfCtx dA)))
inv-Pi lf (ty-conv d c) = let r = inv-Pi lf d in
  mkInvPi (InvPi.lvl r) (InvPi.dA r) (InvPi.dB r) (Sub-conv-right (InvPi.sub r) c)
inv-Pi lf (ty-cum d le) = let r = inv-Pi lf d in
  mkInvPi (InvPi.lvl r) (InvPi.dA r) (InvPi.dB r) (Sub-cum lf (InvPi.sub r) le)

record InvLam {n : Nat} (G : Ctx n) (A : Expr n) (B b : Expr (suc n)) (T : Expr n) : Set where
  constructor mkInvLam
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    db  : HasType (extend G A) b B
    sub : SubTy G (Pi A B) T

inv-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G (Lam A B b) T -> InvLam G A B b T
inv-Lam lf (ty-Lam dA dB db) = mkInvLam dA dB db (Sub-refl (isType-Pi dA dB))
inv-Lam lf (ty-conv d c) = let r = inv-Lam lf d in
  mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r) (Sub-conv-right (InvLam.sub r) c)
inv-Lam lf (ty-cum d le) = let r = inv-Lam lf d in
  mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r) (Sub-cum lf (InvLam.sub r) le)

record InvApp {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n)) (c a T : Expr n) : Set where
  constructor mkInvApp
  field
    dA  : IsType G A
    dB  : IsType (extend G A) B
    dc  : HasType G c (Pi A B)
    da  : HasType G a A
    sub : SubTy G (subst1 B a) T

inv-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {c a T : Expr n} -> LoopFree (lctx G) ->
  HasType G (App A B c a) T -> InvApp G A B c a T
inv-App lf (ty-App dA dB dc da) =
  mkInvApp dA dB dc da (Sub-refl (subst-IsType (subst1-WtSub dA da) (isType-WfCtx dA) dB))
inv-App lf (ty-conv d c) = let r = inv-App lf d in
  mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r) (Sub-conv-right (InvApp.sub r) c)
inv-App lf (ty-cum d le) = let r = inv-App lf d in
  mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r) (Sub-cum lf (InvApp.sub r) le)

record InvGLam {n : Nat} (G : Ctx n) (c : Constr) (A t T : Expr n) : Set where
  constructor mkInvGLam
  field
    wf  : WfCtx G
    dA  : IsType (addC G c) A
    dt  : HasType (addC G c) t A
    sub : SubTy G (Grd c A) T

inv-GLam : {n : Nat} {G : Ctx n} {c : Constr} {A t T : Expr n} -> LoopFree (lctx G) ->
  HasType G (GLam c A t) T -> InvGLam G c A t T
inv-GLam lf (ty-GLam wf dA dt) = mkInvGLam wf dA dt (Sub-refl (is-Grd wf dA))
inv-GLam lf (ty-conv d c) = let r = inv-GLam lf d in
  mkInvGLam (InvGLam.wf r) (InvGLam.dA r) (InvGLam.dt r) (Sub-conv-right (InvGLam.sub r) c)
inv-GLam lf (ty-cum d le) = let r = inv-GLam lf d in
  mkInvGLam (InvGLam.wf r) (InvGLam.dA r) (InvGLam.dt r) (Sub-cum lf (InvGLam.sub r) le)

record InvLLam {n : Nat} (G : Ctx n) (A u T : Expr n) : Set where
  constructor mkInvLLam
  field
    wf  : WfCtx G
    dA  : IsType (addL G) A
    du  : HasType (addL G) u A
    sub : SubTy G (LPi A) T

inv-LLam : {n : Nat} {G : Ctx n} {A u T : Expr n} -> LoopFree (lctx G) ->
  HasType G (LLam A u) T -> InvLLam G A u T
inv-LLam lf (ty-LLam wf dA du) = mkInvLLam wf dA du (Sub-refl (is-LPi wf dA))
inv-LLam lf (ty-conv d c) = let r = inv-LLam lf d in
  mkInvLLam (InvLLam.wf r) (InvLLam.dA r) (InvLLam.du r) (Sub-conv-right (InvLLam.sub r) c)
inv-LLam lf (ty-cum d le) = let r = inv-LLam lf d in
  mkInvLLam (InvLLam.wf r) (InvLLam.dA r) (InvLLam.du r) (Sub-cum lf (InvLLam.sub r) le)

record InvLApp {n : Nat} (G : Ctx n) (A t : Expr n) (l : LExpr) (T : Expr n) : Set where
  constructor mkInvLApp
  field
    dA  : IsType (addL G) A
    dt  : HasType G t (LPi A)
    sub : SubTy G (lsub1 A l) T

inv-LApp : {n : Nat} {G : Ctx n} {A t : Expr n} {l : LExpr} {T : Expr n} -> LoopFree (lctx G) ->
  HasType G (LApp A t l) T -> InvLApp G A t l T
inv-LApp lf d@(ty-LApp dA dt) = mkInvLApp dA dt (Sub-refl (typing-IsType d))
inv-LApp lf (ty-conv d c) = let r = inv-LApp lf d in
  mkInvLApp (InvLApp.dA r) (InvLApp.dt r) (Sub-conv-right (InvLApp.sub r) c)
inv-LApp lf (ty-cum d le) = let r = inv-LApp lf d in
  mkInvLApp (InvLApp.dA r) (InvLApp.dt r) (Sub-cum lf (InvLApp.sub r) le)
