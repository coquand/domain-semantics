{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LiftBack
--
-- Tools for the section of erasure (Theorem 4.13 of the Russell/Tarski
-- comparison, cf. ERT.LiftBack), for T_T with internal levels.
--
--   * move-*: a Tarski judgement holding in G_src also holds in any
--     well-formed G_tgt with the same erasure.  The two contexts have
--     the same level constraints (both are the level context of the
--     erasure), and their types are pointwise convertible by type-uniq;
--     so the identity is a well-typed substitution G_tgt → G_src, built
--     by induction on the contexts.  Unlike ERT.LiftBack (which
--     re-derives every rule in the new context) this reuses the
--     substitution lemma of BCDE4.TarskiMeta.
--
--   * coerce-*: retype a term along a type with the same erasure.
--
--   * unL-*: from a Tarski context whose erasure is  Γ, α  recover a
--     Tarski context whose erasure is Γ (instantiate α by itself).  This
--     is needed for the β-rule of level products, whose premises all
--     live under the level binder.
------------------------------------------------------------------------

module BCDE4.LiftBack where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax  as R
import BCDE4.RussellTyping  as RT
import BCDE4.TarskiSyntax   as T
import BCDE4.TarskiTyping   as TT
import BCDE4.Erasure        as E
import BCDE4.TarskiMeta     as TM
import BCDE4.TarskiLsub     as TL
open import BCDE4.Uniqueness using (type-uniq)
open import BCDE4.EraseDeriv using (eraseCtx ; lctx-erase)

------------------------------------------------------------------------
-- Level contexts
------------------------------------------------------------------------

-- contexts with the same erasure have the same level constraints
lctx-eq : {n : Nat} (G H : TT.Ctx n) -> Eq (eraseCtx G) (eraseCtx H) -> Eq (TT.lctx G) (TT.lctx H)
lctx-eq G H e = Eq-trans (Eq-sym (lctx-erase G)) (Eq-trans (Eq-cong RT.lctx e) (lctx-erase H))

-- the level facts of a Russell context hold in a Tarski preimage
lvl : {n : Nat} (H : TT.Ctx n) {G : RT.Ctx n} -> Eq (eraseCtx H) G ->
  {P : LCtx -> Set} -> P (RT.lctx G) -> P (TT.lctx H)
lvl H e {P} p = Eq-transport P (Eq-trans (Eq-cong RT.lctx (Eq-sym e)) (lctx-erase H)) p

------------------------------------------------------------------------
-- Injectivity of the Russell context formers
------------------------------------------------------------------------

R-extend-inj : {n : Nat} {G G' : RT.Ctx n} {A A' : R.Expr n}
  -> Eq (RT.extend G A) (RT.extend G' A') -> Pair (Eq G G') (Eq A A')
R-extend-inj refl = mkSigma refl refl

R-empty-inj : {Th Th' : LCtx} -> Eq (RT.empty Th) (RT.empty Th') -> Eq Th Th'
R-empty-inj refl = refl

------------------------------------------------------------------------
-- The identity substitution between contexts with the same erasure
------------------------------------------------------------------------

IdTy : {n : Nat} -> TT.Ctx n -> TT.Ctx n -> Set
IdTy H G = (i : Fin _) -> TT.HasType H (T.Var i) (TT.lookup G i)

idWt : {n : Nat} {H G : TT.Ctx n} -> Eq (TT.lctx H) (TT.lctx G) -> IdTy H G -> TM.WtSub H G TM.idSub
idWt {H = H} {G = G} e t =
  TM.mkWt (Eq-transport (\ X -> Entails (TT.lctx H) X) e ent-refl)
    (\ i -> Eq-transport (TT.HasType H (T.Var i)) (Eq-sym (TM.substExpr-id (TT.lookup G i))) (t i))

mkIdTy : {n : Nat} (G H : TT.Ctx n) -> TT.WfCtx G -> TT.WfCtx H
  -> Eq (eraseCtx G) (eraseCtx H) -> IdTy H G
mkIdTy (TT.empty _) (TT.empty _) _ _ _ ()
mkIdTy (TT.extend G A) (TT.extend H A') (TT.wf-extend dA) (TT.wf-extend dA') e =
  let mkSigma eG eA = R-extend-inj e
      inner = mkIdTy G H (TM.isType-WfCtx dA) (TM.isType-WfCtx dA') eG
      ws    = idWt (lctx-eq H G (Eq-sym eG)) inner
      dA''  = Eq-transport (TT.IsType H) (TM.substExpr-id A)
                (TM.subst-IsType ws (TM.isType-WfCtx dA') dA)
      c     = type-uniq dA' dA'' (Eq-sym eA)
  in \ { fzero    -> TT.ty-conv (TT.ty-var (TT.wf-extend dA')) (TM.wk-ConvTy dA' c)
       ; (fsuc i) -> TM.wk-HasType dA' (inner i) }

wtMove : {n : Nat} (G H : TT.Ctx n) -> TT.WfCtx G -> TT.WfCtx H
  -> Eq (eraseCtx G) (eraseCtx H) -> TM.WtSub H G TM.idSub
wtMove G H wG wH e = idWt (lctx-eq H G (Eq-sym e)) (mkIdTy G H wG wH e)

------------------------------------------------------------------------
-- move-*: transport a derivation to a context with the same erasure
------------------------------------------------------------------------

move-IsType : {n : Nat} (G_src G_tgt : TT.Ctx n) {A : T.Expr n}
  -> TT.WfCtx G_tgt -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.IsType G_src A -> TT.IsType G_tgt A
move-IsType Gs Gt {A} wt e d =
  Eq-transport (TT.IsType Gt) (TM.substExpr-id A)
    (TM.subst-IsType (wtMove Gs Gt (TM.isType-WfCtx d) wt e) wt d)

move-HasType : {n : Nat} (G_src G_tgt : TT.Ctx n) {M A : T.Expr n}
  -> TT.WfCtx G_tgt -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.HasType G_src M A -> TT.HasType G_tgt M A
move-HasType Gs Gt {M} {A} wt e d =
  Eq-transport (\ X -> TT.HasType Gt X A) (TM.substExpr-id M)
    (Eq-transport (TT.HasType Gt (T.substExpr TM.idSub M)) (TM.substExpr-id A)
      (TM.subst-HasType (wtMove Gs Gt (TM.typing-WfCtx d) wt e) wt d))

move-ConvTy : {n : Nat} (G_src G_tgt : TT.Ctx n) {A B : T.Expr n}
  -> TT.WfCtx G_tgt -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.ConvTy G_src A B -> TT.ConvTy G_tgt A B
move-ConvTy Gs Gt {A} {B} wt e d =
  Eq-transport (\ X -> TT.ConvTy Gt X B) (TM.substExpr-id A)
    (Eq-transport (TT.ConvTy Gt (T.substExpr TM.idSub A)) (TM.substExpr-id B)
      (TM.subst-ConvTy (wtMove Gs Gt (TM.isType-WfCtx (TM.presup-l-ConvTy d)) wt e) wt d))

move-ConvTm : {n : Nat} (G_src G_tgt : TT.Ctx n) {M N A : T.Expr n}
  -> TT.WfCtx G_tgt -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.ConvTm G_src M N A -> TT.ConvTm G_tgt M N A
move-ConvTm Gs Gt {M} {N} {A} wt e d =
  Eq-transport (\ X -> TT.ConvTm Gt X N A) (TM.substExpr-id M)
    (Eq-transport (\ Y -> TT.ConvTm Gt (T.substExpr TM.idSub M) Y A) (TM.substExpr-id N)
      (Eq-transport (TT.ConvTm Gt (T.substExpr TM.idSub M) (T.substExpr TM.idSub N)) (TM.substExpr-id A)
        (TM.subst-ConvTm (wtMove Gs Gt (TM.typing-WfCtx (TM.presup-l-ConvTm d)) wt e) wt d)))

------------------------------------------------------------------------
-- Coercions along types with the same erasure
------------------------------------------------------------------------

coerce-HasType-to : {n : Nat} {G : TT.Ctx n} {M A B : T.Expr n}
  -> TT.HasType G M A -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.HasType G M B
coerce-HasType-to dM dB eq =
  TT.ty-conv dM (type-uniq (TM.typing-IsType dM) dB eq)

coerce-ConvTm-to : {n : Nat} {G : TT.Ctx n} {M N A B : T.Expr n}
  -> TT.ConvTm G M N A -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.ConvTm G M N B
coerce-ConvTm-to dMN dB eq =
  TT.conv-conv dMN
    (type-uniq (TM.typing-IsType (TM.presup-l-ConvTm dMN)) dB eq)

-- a conversion between two types, re-expressed between two other types
-- with the same erasures
bridge-ConvTy : {n : Nat} {G : TT.Ctx n} {A B A' B' : T.Expr n}
  -> TT.ConvTy G A B -> TT.IsType G A' -> TT.IsType G B'
  -> Eq (E.erase A') (E.erase A) -> Eq (E.erase B) (E.erase B')
  -> TT.ConvTy G A' B'
bridge-ConvTy c dA' dB' eA eB =
  TT.conv-Ty-trans (type-uniq dA' (TM.presup-l-ConvTy c) eA)
    (TT.conv-Ty-trans c (type-uniq (TM.presup-r-ConvTy c) dB' eB))

------------------------------------------------------------------------
-- Leaving a level binder:  |Δ| = Γ,α  ⇒  |Δ(α/α)| = Γ
------------------------------------------------------------------------

v0S : LSub
v0S = lsub1S (lvar zero)

unL : {n : Nat} -> TT.Ctx n -> TT.Ctx n
unL = TL.lsubCtx v0S

unL-WfCtx : {n : Nat} {D : TT.Ctx n} -> TT.WfCtx D -> TT.WfCtx (unL D)
unL-WfCtx {D = D} = TL.lsubD-WfCtx v0S D

private
  R-inst-shift : {n : Nat} (A : R.Expr n) -> Eq (R.lsubE v0S (R.lshiftE A)) A
  R-inst-shift A =
    Eq-trans (R.lsubE-comp v0S lwkS A) (Eq-trans (R.lsubE-ext _ lidS (\ i -> refl) A) (R.lsubE-id A))

  Th-inst-shift : (Th : LCtx) -> Eq (lsubTh v0S (lsubTh lwkS Th)) Th
  Th-inst-shift Th =
    Eq-trans (lsubTh-comp v0S lwkS Th) (Eq-trans (lsubTh-ext _ lidS (\ i -> refl) Th) (lsubTh-id Th))

unL-erase : {n : Nat} (D : TT.Ctx n) (G : RT.Ctx n) -> Eq (eraseCtx D) (RT.addL G) -> Eq (eraseCtx (unL D)) G
unL-erase (TT.empty Th') (RT.empty Th) e =
  Eq-cong RT.empty (Eq-trans (Eq-cong (lsubTh v0S) (R-empty-inj e)) (Th-inst-shift Th))
unL-erase (TT.extend D A') (RT.extend G A) e =
  let mkSigma eG eA = R-extend-inj e
  in Eq-cong2 RT.extend (unL-erase D G eG)
       (Eq-trans (E.erase-lsub v0S A') (Eq-trans (Eq-cong (R.lsubE v0S) eA) (R-inst-shift A)))
