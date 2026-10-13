{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Equivalence.agda
--
-- Russell (MAHLO/Typing, rule R') and Tarski (MAHLORT/TarskiTyping,
-- recursive subuniverses + reflection) are equivalent, relative to TInj
-- (instantiated in MAHLORT/EquivalenceFinal):
--
--   soundness   Tarski |- J        ==>  Russell |- |J|          (Lemma 4.6)
--   section     Russell |- J       ==>  Tarski |- J' with |J'| = J,
--                                       in any Tarski context erasing to
--                                       that of J              (Thm 4.13)
--   retraction  lift (|J|) agrees with J: types up to TyEq, terms up to
--               Coh (same / both universes / eta / surjective pairing)
--   contexts    every well-formed Russell context lifts; two Tarski
--               contexts with the same erasure are interconvertible.
------------------------------------------------------------------------

open import MAHLORT.Hyp

module MAHLORT.Equivalence (I : TInj) where

open import MAHLO.Basic hiding (Sigma)
import MAHLO.Syntax as R
import MAHLO.Typing as RT
import MAHLOINJ.Syntax.Wf as RW
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Erasure
open import MAHLORT.EraseDeriv public
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.Presup
open import MAHLORT.Coh public
open import MAHLORT.Uniq I public using (type-uniq ; term-uniq)
open import MAHLORT.SectionLemmas I public using (LTy ; LTm ; LTE ; LCv ; lty ; ltm ; lte ; lcv)
open import MAHLORT.Section I public using (lift-Ty ; lift-Tm ; lift-TE ; lift-Cv)

------------------------------------------------------------------------
-- Contexts: lift
------------------------------------------------------------------------

record LCtx {n : Num} (G : RT.Ctx n) : Set where
  constructor lctx
  field
    ctx  : Ctx n
    wf   : WfCtx ctx
    ectx : Eq (erCtx ctx) G

lift-Wf : {n : Num} (G : RT.Ctx n) -> RT.WfCtx G -> LCtx G
lift-Wf RT.empty RT.wf-empty = lctx empty wf-empty refl
lift-Wf (RT.extend G A) (RT.wf-extend hA) =
  let L  = lift-Wf G (RW.wfTy hA)
      LA = lift-Ty (LCtx.wf L) (LCtx.ectx L) hA
  in lctx (extend (LCtx.ctx L) (LTy.ty LA)) (wf-extend (LTy.dty LA)) (cong2 RT.extend (LCtx.ectx L) (LTy.ety LA))

------------------------------------------------------------------------
-- Contexts: uniqueness up to conversion
------------------------------------------------------------------------

private
  r-ext : {n : Num} {G H : RT.Ctx n} {A B : R.Expr n} -> Eq (RT.extend G A) (RT.extend H B) -> Eq G H * Eq A B
  r-ext refl = refl , refl

-- G1 sees every variable of G0 at (a type convertible to) its G0-type
ctx-uniq : {n : Num} {G0 G1 : Ctx n} -> WfCtx G0 -> WfCtx G1 -> Eq (erCtx G0) (erCtx G1) -> WtSub G1 G0 idSub
ctx-uniq {G0 = empty} {empty} w0 w1 e ()
ctx-uniq {G0 = extend H0 B0} {extend H1 B1} (wf-extend hB0) (wf-extend hB1) e = ws'
  where
    ws = ctx-uniq (wfTy hB0) (wfTy hB1) (fst (r-ext e))
    hB0' = trTy (substExpr-id B0) (sbTy idSub ws (wfTy hB1) hB0)
    q = type-uniq hB1 hB0' (Eq-sym (snd (r-ext e)))
    ws' : WtSub (extend H1 B1) (extend H0 B0) idSub
    ws' fzero = trHT refl (Eq-sym (substExpr-id (wkExpr B0))) (ty-conv (ty-var (wf-extend hB1)) (wkTE hB1 q))
    ws' (fsuc i) =
      trHT refl (Eq-trans (Eq-cong wkExpr (substExpr-id (lookup H0 i))) (Eq-sym (substExpr-id (wkExpr (lookup H0 i)))))
           (wkTm hB1 (ws i))

-- moving judgements between contexts with the same erasure
module Move {n : Num} {G0 G1 : Ctx n} (w0 : WfCtx G0) (w1 : WfCtx G1) (e : Eq (erCtx G0) (erCtx G1)) where
  private ws = ctx-uniq w0 w1 e

  moveTy : {A : Expr n} -> IsType G0 A -> IsType G1 A
  moveTy {A} h = trTy (substExpr-id A) (sbTy idSub ws w1 h)

  moveTm : {t A : Expr n} -> HasType G0 t A -> HasType G1 t A
  moveTm {t} {A} h = trHT (substExpr-id t) (substExpr-id A) (sbTm idSub ws w1 h)

  moveTE : {A B : Expr n} -> TyEq G0 A B -> TyEq G1 A B
  moveTE {A} {B} h = trTE (substExpr-id A) (substExpr-id B) (sbTE idSub ws w1 h)

  moveCv : {t u A : Expr n} -> ConvTm G0 t u A -> ConvTm G1 t u A
  moveCv {t} {u} {A} h = trCv (substExpr-id t) (substExpr-id u) (substExpr-id A) (sbCv idSub ws w1 h)

------------------------------------------------------------------------
-- Section and retraction, in a fixed Tarski context
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} (w : WfCtx G) where

  section-Ty : {A : R.Expr n} -> RT.IsType (erCtx G) A -> LTy G A
  section-Ty = lift-Ty w refl

  section-Tm : {t A : R.Expr n} -> RT.HasType (erCtx G) t A -> LTm G t A
  section-Tm = lift-Tm w refl

  section-TE : {A B : R.Expr n} -> RT.TyEq (erCtx G) A B -> LTE G A B
  section-TE = lift-TE w refl

  section-Cv : {t u A : R.Expr n} -> RT.ConvTm (erCtx G) t u A -> LCv G t u A
  section-Cv = lift-Cv w refl

  -- lifting the erasure gives back the type, up to TyEq
  retract-Ty : {A : Expr n} (d : IsType G A) -> TyEq G (LTy.ty (section-Ty (erI d))) A
  retract-Ty d = type-uniq (LTy.dty L) d (LTy.ety L)
    where L = section-Ty (erI d)

  -- ... and the term, up to coherence; its type up to TyEq
  retract-Tm : {t A : Expr n} (d : HasType G t A) ->
               Coh G (LTm.tm (section-Tm (erH d))) (LTm.ty (section-Tm (erH d))) t A
  retract-Tm d = term-uniq (LTm.dtm L) d (LTm.etm L)
    where L = section-Tm (erH d)

  retract-TmTy : {t A : Expr n} (d : HasType G t A) -> TyEq G (LTm.ty (section-Tm (erH d))) A
  retract-TmTy d = type-uniq (pTm (LTm.dtm L)) (pTm d) (LTm.ety L)
    where L = section-Tm (erH d)

------------------------------------------------------------------------
-- The equivalence, as one record
------------------------------------------------------------------------

record Equivalence : Set where
  field
    -- soundness of erasure (Lemma 4.6)
    sound-Ty : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> RT.IsType (erCtx G) (er A)
    sound-Tm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> RT.HasType (erCtx G) (er t) (er A)
    sound-TE : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> RT.TyEq (erCtx G) (er A) (er B)
    sound-Cv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
               RT.ConvTm (erCtx G) (er t) (er u) (er A)
    -- section (Theorem 4.13)
    lift-ctx : {n : Num} (G : RT.Ctx n) -> RT.WfCtx G -> LCtx G
    lift-ty  : {n : Num} {G : Ctx n} {A : R.Expr n} -> WfCtx G -> RT.IsType (erCtx G) A -> LTy G A
    lift-tm  : {n : Num} {G : Ctx n} {t A : R.Expr n} -> WfCtx G -> RT.HasType (erCtx G) t A -> LTm G t A
    lift-te  : {n : Num} {G : Ctx n} {A B : R.Expr n} -> WfCtx G -> RT.TyEq (erCtx G) A B -> LTE G A B
    lift-cv  : {n : Num} {G : Ctx n} {t u A : R.Expr n} -> WfCtx G -> RT.ConvTm (erCtx G) t u A -> LCv G t u A
    -- uniqueness (Lemma 4.10 / 4.18): erasure is injective up to conversion
    uniq-ctx : {n : Num} {G0 G1 : Ctx n} -> WfCtx G0 -> WfCtx G1 -> Eq (erCtx G0) (erCtx G1) -> WtSub G1 G0 idSub
    uniq-ty  : {n : Num} {G : Ctx n} {A0 A1 : Expr n} -> IsType G A0 -> IsType G A1 -> Eq (er A0) (er A1) ->
               TyEq G A0 A1
    uniq-tm  : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} -> HasType G t0 A0 -> HasType G t1 A1 ->
               Eq (er t0) (er t1) -> Coh G t0 A0 t1 A1

equivalence : Equivalence
equivalence = record
  { sound-Ty = erI ; sound-Tm = erH ; sound-TE = erT ; sound-Cv = erC
  ; lift-ctx = lift-Wf
  ; lift-ty = \ w -> lift-Ty w refl ; lift-tm = \ w -> lift-Tm w refl
  ; lift-te = \ w -> lift-TE w refl ; lift-cv = \ w -> lift-Cv w refl
  ; uniq-ctx = ctx-uniq ; uniq-ty = type-uniq ; uniq-tm = term-uniq }
