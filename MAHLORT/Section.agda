{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Section.agda
--
-- Section of erasure (ERT Theorem 4.13), relative to TInj: every
-- derivable Russell judgement (MAHLO/Typing) lifts to a derivable
-- Tarski judgement with the prescribed erasure, in ANY Tarski context
-- G' erasing to the Russell context.
--
--   isty-el (A : V)  |->  T_V(A')
--   ty-sub           |->  T^
--   ty-Pi at V / U   |->  Pi^_V / Pi^_U   (likewise Sigma, N)
--   (R')             |->  conv-reflect, through uniqueness at V (upSame)
--   delta-f / -g     |->  conv-That-Fhat / -Ghat
--   conv-Fhat/-Ghat  |->  CodeCong.ccFhat/ccGhat (f, g move)
-- Mismatched lifts of the same Russell expression are reconciled by
-- type-uniq (coerce) and term-uniq + extraction (sameTm).
------------------------------------------------------------------------

open import MAHLORT.Hyp

module MAHLORT.Section (I : TInj) where

open import MAHLO.Basic hiding (Sigma)
import MAHLO.Syntax as R
import MAHLO.Typing as RT
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Erasure
open import MAHLORT.EraseLemmas
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.CtxConv
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Ops
open import MAHLORT.Syntax.Presup
open import MAHLORT.Syntax.CodeCong
open import MAHLORT.Coh
open import MAHLORT.UniqLemmas I
open import MAHLORT.Uniq I
open import MAHLORT.SectionLemmas I
import MAHLOINJ.Syntax.Wf as RW

------------------------------------------------------------------------
-- Erasure equations
------------------------------------------------------------------------

private
  eqPiB : {n : Num} {a A : R.Expr n} {b B : R.Expr (suc n)} -> Eq a A -> Eq b B -> Eq (R.PiB a b) (R.PiB A B)
  eqPiB refl refl = refl

  eqSigB : {n : Num} {a A : R.Expr n} {b B : R.Expr (suc n)} -> Eq a A -> Eq b B -> Eq (R.SigmaB a b) (R.SigmaB A B)
  eqSigB refl refl = refl

  eqU : {n : Num} (f g : Expr n) {p q : R.Expr n} -> Eq (er f) p -> Eq (er g) q -> Eq (er (TyU f g)) (R.Ucode p q)
  eqU f g ef eg = cong2 R.Ucode ef eg

  eqWkU : {n : Num} (f g : Expr n) {p q : R.Expr n} -> Eq (er f) p -> Eq (er g) q ->
          Eq (er (wkExpr (TyU f g))) (R.wkExpr (R.Ucode p q))
  eqWkU f g ef eg = Eq-trans (er-wk (TyU f g)) (Eq-cong R.wkExpr (eqU f g ef eg))

  eqS1 : {n : Num} (B : Expr (suc n)) (a : Expr n) {B0 : R.Expr (suc n)} {a0 : R.Expr n} ->
         Eq (er B) B0 -> Eq (er a) a0 -> Eq (er (subst1 B a)) (R.subst1 B0 a0)
  eqS1 B a eB ea = Eq-trans (er-subst1 B a) (cong2 R.subst1 eB ea)

  eqOpG : {n : Num} (f : Expr n) {p : R.Expr n} -> Eq (er f) p -> Eq (er (OpG f)) (R.OpG p)
  eqOpG f ef = Eq-trans (er-OpG f) (Eq-cong R.OpG ef)

  eqLk : {n : Num} {G' : Ctx n} {G : RT.Ctx n} (i : Fin n) -> Eq (erCtx G') G ->
         Eq (er (lookup G' i)) (RT.lookup G i)
  eqLk {G' = G'} i eG = Eq-trans (er-lookup G' i) (Eq-cong (\ H -> RT.lookup H i) eG)

  -- two convertible lifts of the same Russell term
  alignL : {n : Num} {G : Ctx n} {t u A : R.Expr n} {x X : Expr n} ->
           HasType G x X -> Eq (er x) t -> Eq (er X) A -> (C : LCv G t u A) ->
           ConvTm G x (LCv.lhs C) X
  alignL hx ex eX C =
    sameTm hx (fst (pCv (LCv.dcv C))) (Eq-trans ex (Eq-sym (LCv.el C))) (Eq-trans eX (Eq-sym (LCv.ety C)))

------------------------------------------------------------------------
-- Lifted operator pairs and f^-data
------------------------------------------------------------------------

record OpL {n : Num} (G : Ctx n) (f g : R.Expr n) : Set where
  constructor opl
  field
    f' : Expr n
    g' : Expr n
    ef : Eq (er f') f
    eg : Eq (er g') g
    hf : HasType G f' OpF
    hg : HasType G g' (OpG f')

record FhL {n : Num} (G : Ctx n) (f g A : R.Expr n) (B : R.Expr (suc n)) : Set where
  constructor fhl
  field
    op : OpL G f g
    A' : Expr n
    B' : Expr (suc n)
    eA : Eq (er A') A
    eB : Eq (er B') B
    hA : HasType G A' (TyU (OpL.f' op) (OpL.g' op))
    hB : HasType (extend G (ElU (OpL.f' op) (OpL.g' op) A')) B' (wkExpr (TyU (OpL.f' op) (OpL.g' op)))

------------------------------------------------------------------------
-- The lifts
------------------------------------------------------------------------

lift-Ty : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {A : R.Expr n} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.IsType G A -> LTy G' A
lift-Tm : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {t A : R.Expr n} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.HasType G t A -> LTm G' t A
lift-TE : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {A B : R.Expr n} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.TyEq G A B -> LTE G' A B
lift-Cv : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {t u A : R.Expr n} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.ConvTm G t u A -> LCv G' t u A
liftOp  : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {f g : R.Expr n} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.HasType G f R.OpF -> RT.HasType G g (R.OpG f) -> OpL G' f g
liftFh  : {n : Num} {G : RT.Ctx n} {G' : Ctx n} {f g A : R.Expr n} {B : R.Expr (suc n)} ->
          WfCtx G' -> Eq (erCtx G') G -> RT.HasType G f R.OpF -> RT.HasType G g (R.OpG f) ->
          RT.HasType G A (R.Ucode f g) -> RT.HasType (RT.extend G A) B (R.wkExpr (R.Ucode f g)) ->
          FhL G' f g A B

-- extending the context by a lifted type
private
  extW : {n : Num} {G' : Ctx n} {A : R.Expr n} (L : LTy G' A) -> WfCtx (extend G' (LTy.ty L))
  extW L = wf-extend (LTy.dty L)

  extE : {n : Num} {G' : Ctx n} {G : RT.Ctx n} {A : R.Expr n} (L : LTy G' A) -> Eq (erCtx G') G ->
         Eq (erCtx (extend G' (LTy.ty L))) (RT.extend G A)
  extE L eG = cong2 RT.extend eG (LTy.ety L)

liftOp w eG hf hg =
  let
      Lf = lift-Tm w eG hf
      Lg = lift-Tm w eG hg
      f' = LTm.tm Lf
      g' = LTm.tm Lg
      hf' = at Lf (opFTy w) refl
      hg' = at Lg (opGTy w hf') (eqOpG f' (LTm.etm Lf))
  in
    opl f' g' (LTm.etm Lf) (LTm.etm Lg) hf' hg'

liftFh w eG hf hg hA hB =
  let
      O = liftOp w eG hf hg
      open OpL O renaming (hf to hf1 ; hg to hg1)
      LA = lift-Tm w eG hA
      hA' = at LA (isty-TyU hf1 hg1) (eqU f' g' ef eg)
      wE = wf-extend (isty-ElU hA')
      LB = lift-Tm wE (cong2 RT.extend eG (LTm.etm LA)) hB
      hB' = at LB (wkTy (isty-ElU hA') (isty-TyU hf1 hg1)) (eqWkU f' g' ef eg)
  in
    fhl O (LTm.tm LA) (LTm.tm LB) (LTm.etm LA) (LTm.etm LB) hA' hB'

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

lift-Ty w eG (RT.isty-V _) = lty V refl (isty-V w)
lift-Ty w eG (RT.isty-el h) =
  let
      L = lift-Tm w eG h
  in
    lty (ElV (LTm.tm L)) (LTm.etm L) (isty-ElV (at L (isty-V w) refl))
lift-Ty w eG (RT.isty-Pi hA hB) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
  in
    lty (PiB (LTy.ty LA) (LTy.ty LB)) (eqPiB (LTy.ety LA) (LTy.ety LB)) (isty-Pi (LTy.dty LA) (LTy.dty LB))
lift-Ty w eG (RT.isty-Sigma hA hB) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
  in
    lty (SigmaB (LTy.ty LA) (LTy.ty LB)) (eqSigB (LTy.ety LA) (LTy.ety LB)) (isty-Sigma (LTy.dty LA) (LTy.dty LB))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

lift-Tm {G' = G'} w eG (RT.ty-var {i = i} _) = ltm (Var i) (lookup G' i) refl (eqLk i eG) (ty-var w)
lift-Tm w eG (RT.ty-conv h q) =
  let
      L = lift-Tm w eG h
      Q = lift-TE w eG q
  in
    ltm (LTm.tm L) (LTE.rhs Q) (LTm.etm L) (LTE.er' Q)
        (ty-conv (at L (fst (pTE (LTE.dte Q))) (LTE.el Q)) (LTE.dte Q))
lift-Tm w eG (RT.ty-sub h) =
  let
      L = lift-Tm w eG h
      U = asU (pTm (LTm.dtm L)) (LTm.ety L)
  in
    ltm (That (LTm.tm L)) V (LTm.etm L) refl (ty-That (ty-conv (LTm.dtm L) (UDec.eq U)))
lift-Tm w eG (RT.ty-Pi (RT.univ-V refl) hA hB) =
  let
      LA = lift-Tm w eG hA
      hA' = at LA (isty-V w) refl
      wE = wf-extend (isty-ElV hA')
      LB = lift-Tm wE (cong2 RT.extend eG (LTm.etm LA)) hB
  in
    ltm (PiV (LTm.tm LA) (Lam (ElV (LTm.tm LA)) (LTm.tm LB))) V (eqPiB (LTm.etm LA) (LTm.etm LB)) refl
        (ty-PiV hA' (at LB (isty-V wE) refl))
lift-Tm w eG (RT.ty-Pi (RT.univ-U f g refl) hA hB) =
  let
      LA = lift-Tm w eG hA
      U = asU (pTm (LTm.dtm LA)) (LTm.ety LA)
      open UDec U renaming (f to f' ; g to g')
      hA' = ty-conv (LTm.dtm LA) eq
      wE = wf-extend (isty-ElU hA')
      LB = lift-Tm wE (cong2 RT.extend eG (LTm.etm LA)) hB
  in
    ltm (PiU f' g' (LTm.tm LA) (Lam (ElU f' g' (LTm.tm LA)) (LTm.tm LB))) (TyU f' g')
        (eqPiB (LTm.etm LA) (LTm.etm LB)) (eqU f' g' ef eg)
        (ty-PiU hA' (at LB (wkTy (isty-ElU hA') (isty-TyU hf hg)) (eqWkU f' g' ef eg)))
lift-Tm w eG (RT.ty-Sigma (RT.univ-V refl) hA hB) =
  let
      LA = lift-Tm w eG hA
      hA' = at LA (isty-V w) refl
      wE = wf-extend (isty-ElV hA')
      LB = lift-Tm wE (cong2 RT.extend eG (LTm.etm LA)) hB
  in
    ltm (SigV (LTm.tm LA) (Lam (ElV (LTm.tm LA)) (LTm.tm LB))) V (eqSigB (LTm.etm LA) (LTm.etm LB)) refl
        (ty-SigV hA' (at LB (isty-V wE) refl))
lift-Tm w eG (RT.ty-Sigma (RT.univ-U f g refl) hA hB) =
  let
      LA = lift-Tm w eG hA
      U = asU (pTm (LTm.dtm LA)) (LTm.ety LA)
      open UDec U renaming (f to f' ; g to g')
      hA' = ty-conv (LTm.dtm LA) eq
      wE = wf-extend (isty-ElU hA')
      LB = lift-Tm wE (cong2 RT.extend eG (LTm.etm LA)) hB
  in
    ltm (SigU f' g' (LTm.tm LA) (Lam (ElU f' g' (LTm.tm LA)) (LTm.tm LB))) (TyU f' g')
        (eqSigB (LTm.etm LA) (LTm.etm LB)) (eqU f' g' ef eg)
        (ty-SigU hA' (at LB (wkTy (isty-ElU hA') (isty-TyU hf hg)) (eqWkU f' g' ef eg)))
lift-Tm w eG (RT.ty-Nat-V _) = ltm NatV V refl refl (ty-NatV w)
lift-Tm w eG (RT.ty-Nat-U h) =
  let
      L = lift-Tm w eG h
      open UDec (decU kV (at L (isty-V w) refl) (tyeq-refl (isty-V w)) (LTm.etm L))
  in
    ltm (NatU f g) (TyU f g) refl (eqU f g ef eg) (ty-NatU (isty-TyU hf hg))
lift-Tm w eG (RT.ty-Ucode hf hg) =
  let
      open OpL (liftOp w eG hf hg) renaming (hf to hf' ; hg to hg')
  in
    ltm (UV f' g') V (eqU f' g' ef eg) refl (ty-UV hf' hg')
lift-Tm w eG (RT.ty-Fhat hf hg hA hB) =
  let
      F = liftFh w eG hf hg hA hB
      open FhL F renaming (hA to hA' ; hB to hB')
      open OpL op renaming (hf to hf' ; hg to hg')
  in
    ltm (Fhat f' g' A' (Lam (ElU f' g' A') B')) (TyU f' g')
        (cong4 R.Fhat ef eg eA (cong2 R.Lam eA eB)) (eqU f' g' ef eg) (ty-Fhat hf' hg' hA' hB')
lift-Tm w eG (RT.ty-Ghat hf hg hA hB hc) =
  let
      F = liftFh w eG hf hg hA hB
      open FhL F renaming (hA to hA' ; hB to hB')
      open OpL op renaming (hf to hf' ; hg to hg')
      Lc = lift-Tm w eG hc
  in
    ltm (Ghat f' g' A' (Lam (ElU f' g' A') B') (LTm.tm Lc)) (TyU f' g')
        (cong5 R.Ghat ef eg eA (cong2 R.Lam eA eB) (LTm.etm Lc)) (eqU f' g' ef eg)
        (ty-Ghat hf' hg' hA' hB' (at Lc (isty-ElU (ty-Fhat hf' hg' hA' hB')) (cong4 R.Fhat ef eg eA (cong2 R.Lam eA eB))))
lift-Tm w eG (RT.ty-Lam hA hB ht) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      Lt = lift-Tm (extW LA) (extE LA eG) ht
  in
    ltm (Lam (LTy.ty LA) (LTm.tm Lt)) (PiB (LTy.ty LA) (LTy.ty LB))
        (cong2 R.Lam (LTy.ety LA) (LTm.etm Lt)) (eqPiB (LTy.ety LA) (LTy.ety LB))
        (ty-Lam (LTy.dty LA) (LTy.dty LB) (at Lt (LTy.dty LB) (LTy.ety LB)))
lift-Tm w eG (RT.ty-App hA hB ht ha) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
      La = lift-Tm w eG ha
  in
    ltm (appB A' B' (LTm.tm Lt) (LTm.tm La)) (subst1 B' (LTm.tm La))
        (cong2 R.App (LTm.etm Lt) (LTm.etm La)) (eqS1 (LTy.ty LB) (LTm.tm La) (LTy.ety LB) (LTm.etm La))
        (ty-App (LTy.dty LA) (LTy.dty LB) (at Lt (isty-Pi (LTy.dty LA) (LTy.dty LB)) (eqPiB (LTy.ety LA) (LTy.ety LB)))
                (at La (LTy.dty LA) (LTy.ety LA)))
lift-Tm w eG (RT.ty-Pair hA hB ht hu) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
      Lu = lift-Tm w eG hu
      ht' = at Lt (LTy.dty LA) (LTy.ety LA)
  in
    ltm (Pair A' (Lam A' B') (LTm.tm Lt) (LTm.tm Lu)) (SigmaB A' B')
        (cong2 R.Pair (LTm.etm Lt) (LTm.etm Lu)) (eqSigB (LTy.ety LA) (LTy.ety LB))
        (ty-Pair (LTy.dty LA) (LTy.dty LB) ht' (at Lu (s1Ty w ht' (LTy.dty LB)) (eqS1 (LTy.ty LB) (LTm.tm Lt) (LTy.ety LB) (LTm.etm Lt))))
lift-Tm w eG (RT.ty-Fst hA hB ht) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
  in
    ltm (Fst A' (Lam A' B') (LTm.tm Lt)) A' (Eq-cong R.Fst (LTm.etm Lt)) (LTy.ety LA)
        (ty-Fst (LTy.dty LA) (LTy.dty LB) (at Lt (isty-Sigma (LTy.dty LA) (LTy.dty LB)) (eqSigB (LTy.ety LA) (LTy.ety LB))))
lift-Tm w eG (RT.ty-Snd hA hB ht) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
  in
    ltm (Snd A' (Lam A' B') (LTm.tm Lt)) (subst1 B' (Fst A' (Lam A' B') (LTm.tm Lt)))
        (Eq-cong R.Snd (LTm.etm Lt)) (eqS1 (LTy.ty LB) (Fst A' (Lam A' B') (LTm.tm Lt)) (LTy.ety LB) (Eq-cong R.Fst (LTm.etm Lt)))
        (ty-Snd (LTy.dty LA) (LTy.dty LB) (at Lt (isty-Sigma (LTy.dty LA) (LTy.dty LB)) (eqSigB (LTy.ety LA) (LTy.ety LB))))
lift-Tm w eG (RT.ty-Zero _) = ltm Zero Nat refl refl (ty-Zero w)
lift-Tm w eG (RT.ty-Suc h) =
  let
      L = lift-Tm w eG h
  in
    ltm (Suc (LTm.tm L)) Nat (Eq-cong R.Suc (LTm.etm L)) refl (ty-Suc (at L (isty-Nat w) refl))
lift-Tm w eG (RT.ty-Rec hC hz hs hk) =
  let
      LC = lift-Ty (wf-extend (isty-Nat w)) (cong2 RT.extend eG refl) hC
      C' = LTy.ty LC
      Lz = lift-Tm w eG hz
      Ls = lift-Tm w eG hs
      Lk = lift-Tm w eG hk
  in
    ltm (Rec (Lam Nat C') (LTm.tm Lz) (LTm.tm Ls) (LTm.tm Lk)) (subst1 C' (LTm.tm Lk))
        (cong4 R.Rec (Eq-cong (R.Lam R.Nat) (LTy.ety LC)) (LTm.etm Lz) (LTm.etm Ls) (LTm.etm Lk))
        (eqS1 (LTy.ty LC) (LTm.tm Lk) (LTy.ety LC) (LTm.etm Lk))
        (ty-Rec (LTy.dty LC)
           (at Lz (s1Ty w (ty-Zero w) (LTy.dty LC)) (eqS1 (LTy.ty LC) Zero (LTy.ety LC) refl))
           (at Ls (recStepTy w (LTy.dty LC)) (Eq-trans (er-RecStep C') (Eq-cong R.RecStep (LTy.ety LC))))
           (at Lk (isty-Nat w) refl))

------------------------------------------------------------------------
-- Type equality
------------------------------------------------------------------------

lift-TE w eG (RT.tyeq-refl h) =
  let
      L = lift-Ty w eG h
  in
    lte (LTy.ty L) (LTy.ty L) (LTy.ety L) (LTy.ety L) (tyeq-refl (LTy.dty L))
lift-TE w eG (RT.tyeq-sym q) =
  let
      Q = lift-TE w eG q
  in
    lte (LTE.rhs Q) (LTE.lhs Q) (LTE.er' Q) (LTE.el Q) (tyeq-sym (LTE.dte Q))
lift-TE w eG (RT.tyeq-trans q q') =
  let
      Q = lift-TE w eG q
      Q' = lift-TE w eG q'
  in
    lte (LTE.lhs Q) (LTE.rhs Q') (LTE.el Q) (LTE.er' Q')
        (tyeq-trans (LTE.dte Q)
          (tyeq-trans (type-uniq (snd (pTE (LTE.dte Q))) (fst (pTE (LTE.dte Q'))) (Eq-trans (LTE.er' Q) (Eq-sym (LTE.el Q'))))
                      (LTE.dte Q')))
lift-TE w eG (RT.tyeq-el c) =
  let
      C = lift-Cv w eG c
  in
    lte (ElV (LCv.lhs C)) (ElV (LCv.rhs C)) (LCv.el C) (LCv.er' C) (tyeq-ElV (atCv C (isty-V w) refl))
lift-TE w eG (RT.tyeq-Pi hA hB hB' qA qB) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      LB' = lift-Ty (extW LA) (extE LA eG) hB'
      A0 = LTy.ty LA
      B0 = LTy.ty LB
      B0' = LTy.ty LB'
      QA = lift-TE w eG qA
      QB = lift-TE (extW LA) (extE LA eG) qB
      qA0 = tyeq-trans (type-uniq (LTy.dty LA) (fst (pTE (LTE.dte QA))) (Eq-trans (LTy.ety LA) (Eq-sym (LTE.el QA))))
                       (LTE.dte QA)
      qB0 = tyeq-trans (type-uniq (LTy.dty LB) (fst (pTE (LTE.dte QB))) (Eq-trans (LTy.ety LB) (Eq-sym (LTE.el QB))))
              (tyeq-trans (LTE.dte QB)
                 (type-uniq (snd (pTE (LTE.dte QB))) (LTy.dty LB') (Eq-trans (LTE.er' QB) (Eq-sym (LTy.ety LB')))))
  in
    lte (PiB A0 B0) (PiB (LTE.rhs QA) B0') (eqPiB (LTy.ety LA) (LTy.ety LB)) (eqPiB (LTE.er' QA) (LTy.ety LB'))
        (tyeq-Pi (LTy.dty LA) (LTy.dty LB) (LTy.dty LB') qA0 qB0)
lift-TE w eG (RT.tyeq-Sigma hA hB hB' qA qB) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      LB' = lift-Ty (extW LA) (extE LA eG) hB'
      A0 = LTy.ty LA
      B0 = LTy.ty LB
      B0' = LTy.ty LB'
      QA = lift-TE w eG qA
      QB = lift-TE (extW LA) (extE LA eG) qB
      qA0 = tyeq-trans (type-uniq (LTy.dty LA) (fst (pTE (LTE.dte QA))) (Eq-trans (LTy.ety LA) (Eq-sym (LTE.el QA))))
                       (LTE.dte QA)
      qB0 = tyeq-trans (type-uniq (LTy.dty LB) (fst (pTE (LTE.dte QB))) (Eq-trans (LTy.ety LB) (Eq-sym (LTE.el QB))))
              (tyeq-trans (LTE.dte QB)
                 (type-uniq (snd (pTE (LTE.dte QB))) (LTy.dty LB') (Eq-trans (LTE.er' QB) (Eq-sym (LTy.ety LB')))))
  in
    lte (SigmaB A0 B0) (SigmaB (LTE.rhs QA) B0') (eqSigB (LTy.ety LA) (LTy.ety LB)) (eqSigB (LTE.er' QA) (LTy.ety LB'))
        (tyeq-Sigma (LTy.dty LA) (LTy.dty LB) (LTy.dty LB') qA0 qB0)

------------------------------------------------------------------------
-- Term equality
------------------------------------------------------------------------

lift-Cv w eG (RT.conv-refl h) =
  let
      L = lift-Tm w eG h
  in
    lcv (LTm.tm L) (LTm.tm L) (LTm.ty L) (LTm.etm L) (LTm.etm L) (LTm.ety L) (conv-refl (LTm.dtm L))
lift-Cv w eG (RT.conv-sym c) =
  let
      C = lift-Cv w eG c
  in
    lcv (LCv.rhs C) (LCv.lhs C) (LCv.ty C) (LCv.er' C) (LCv.el C) (LCv.ety C) (conv-sym (LCv.dcv C))
lift-Cv w eG (RT.conv-trans c c') =
  let
      C = lift-Cv w eG c
      C' = lift-Cv w eG c'
  in
    lcv (LCv.lhs C) (LCv.rhs C') (LCv.ty C) (LCv.el C) (LCv.er' C') (LCv.ety C)
        (conv-trans (LCv.dcv C)
          (conv-trans (sameTm (snd (pCv (LCv.dcv C))) (fst (pCv (LCv.dcv C')))
                              (Eq-trans (LCv.er' C) (Eq-sym (LCv.el C'))) (Eq-trans (LCv.ety C) (Eq-sym (LCv.ety C'))))
                      (atCv C' (pTm (fst (pCv (LCv.dcv C)))) (LCv.ety C))))
lift-Cv w eG (RT.conv-conv c q) =
  let
      C = lift-Cv w eG c
      Q = lift-TE w eG q
  in
    lcv (LCv.lhs C) (LCv.rhs C) (LTE.rhs Q) (LCv.el C) (LCv.er' C) (LTE.er' Q)
        (conv-conv (atCv C (fst (pTE (LTE.dte Q))) (LTE.el Q)) (LTE.dte Q))
lift-Cv w eG (RT.conv-sub c) =
  let
      C = lift-Cv w eG c
      U = asU (pTm (fst (pCv (LCv.dcv C)))) (LCv.ety C)
  in
    lcv (That (LCv.lhs C)) (That (LCv.rhs C)) V (LCv.el C) (LCv.er' C) refl
        (conv-That (conv-conv (LCv.dcv C) (UDec.eq U)))
lift-Cv w eG (RT.conv-R' hA hB c) =
  let
      LA = lift-Tm w eG hA
      U = asU (pTm (LTm.dtm LA)) (LTm.ety LA)
      open UDec U
      hA' = ty-conv (LTm.dtm LA) eq
      LB = lift-Tm w eG hB
      hB' = at LB (isty-TyU hf hg) (eqU f g ef eg)
      C = lift-Cv w eG c
      c' = atCv C (isty-V w) refl
      hl = fst (pCv c')
      hr = snd (pCv c')
  in
    lcv (LTm.tm LA) (LTm.tm LB) (TyU f g) (LTm.etm LA) (LTm.etm LB) (eqU f g ef eg)
        (conv-reflect hA' hB'
           (conv-trans (conv-sym (upSame hl hA' (Eq-trans (LCv.el C) (Eq-sym (LTm.etm LA)))))
             (conv-trans c' (upSame hr hB' (Eq-trans (LCv.er' C) (Eq-sym (LTm.etm LB)))))))
lift-Cv w eG (RT.conv-delta-f hf hg hA hB) =
  let
      open FhL (liftFh w eG hf hg hA hB) renaming (hA to hA' ; hB to hB')
      open OpL op renaming (hf to hf' ; hg to hg')
  in
    lcv (That (Fhat f' g' A' (Lam (ElU f' g' A') B'))) (fApp f' (That A') (Lam (ElV (That A')) (That B'))) V
        (cong4 R.Fhat ef eg eA (cong2 R.Lam eA eB)) (cong2 R.App (cong2 R.App ef eA) (cong2 R.Lam eA eB)) refl
        (conv-That-Fhat hf' hg' hA' hB')
lift-Cv w eG (RT.conv-delta-g hf hg hA hB hc) =
  let
      open FhL (liftFh w eG hf hg hA hB) renaming (hA to hA' ; hB to hB')
      open OpL op renaming (hf to hf' ; hg to hg')
      Lc = lift-Tm w eG hc
  in
    lcv (That (Ghat f' g' A' (Lam (ElU f' g' A') B') (LTm.tm Lc)))
        (gApp f' g' (That A') (Lam (ElV (That A')) (That B')) (LTm.tm Lc)) V
        (cong5 R.Ghat ef eg eA (cong2 R.Lam eA eB) (LTm.etm Lc))
        (cong2 R.App (cong2 R.App (cong2 R.App eg eA) (cong2 R.Lam eA eB)) (LTm.etm Lc)) refl
        (conv-That-Ghat hf' hg' hA' hB' (at Lc (isty-ElU (ty-Fhat hf' hg' hA' hB')) (cong4 R.Fhat ef eg eA (cong2 R.Lam eA eB))))
lift-Cv w eG (RT.conv-beta hA hB ht ha) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm (extW LA) (extE LA eG) ht
      t' = LTm.tm Lt
      La = lift-Tm w eG ha
      a' = LTm.tm La
  in
    lcv (appB A' B' (Lam A' t') a') (subst1 t' a') (subst1 B' a')
        (cong2 R.App (cong2 R.Lam (LTy.ety LA) (LTm.etm Lt)) (LTm.etm La)) (eqS1 (LTm.tm Lt) (LTm.tm La) (LTm.etm Lt) (LTm.etm La))
        (eqS1 (LTy.ty LB) (LTm.tm La) (LTy.ety LB) (LTm.etm La))
        (conv-beta (LTy.dty LA) (LTy.dty LB) (at Lt (LTy.dty LB) (LTy.ety LB)) (at La (LTy.dty LA) (LTy.ety LA)))
lift-Cv w eG (RT.conv-funext hA hB ht ht' c) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      dA = LTy.dty LA
      dB = LTy.dty LB
      Lt = lift-Tm w eG ht
      Lt' = lift-Tm w eG ht'
      t1 = LTm.tm Lt
      t2 = LTm.tm Lt'
      h1 = at Lt (isty-Pi dA dB) (eqPiB (LTy.ety LA) (LTy.ety LB))
      h2 = at Lt' (isty-Pi dA dB) (eqPiB (LTy.ety LA) (LTy.ety LB))
      C = lift-Cv (extW LA) (extE LA eG) c
      fb1 = funTy dA dB h1
      fb2 = funTy dA dB h2
      eFB : (t : Expr _) {t0 : R.Expr _} -> Eq (er t) t0 ->
            Eq (er (FunB A' B' t)) (R.App (R.wkExpr t0) (R.Var fzero))
      eFB t et = Eq-cong (\ z -> R.App z (R.Var fzero)) (Eq-trans (er-wk t) (Eq-cong R.wkExpr et))
  in
    lcv t1 t2 (PiB A' B') (LTm.etm Lt) (LTm.etm Lt') (eqPiB (LTy.ety LA) (LTy.ety LB))
        (conv-funext dA dB h1 h2
          (conv-trans (sameTm fb1 (fst (pCv (LCv.dcv C))) (Eq-trans (eFB t1 (LTm.etm Lt)) (Eq-sym (LCv.el C)))
                              (Eq-trans (LTy.ety LB) (Eq-sym (LCv.ety C))))
            (conv-trans (atCv C dB (LTy.ety LB))
              (coerceCv (sameTm (snd (pCv (LCv.dcv C))) fb2 (Eq-trans (LCv.er' C) (Eq-sym (eFB t2 (LTm.etm Lt'))))
                                (Eq-trans (LCv.ety C) (Eq-sym (LTy.ety LB))))
                        dB (Eq-trans (LCv.ety C) (Eq-sym (LTy.ety LB)))))))
lift-Cv w eG (RT.conv-fst-beta hA hB ht hu) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
      Lu = lift-Tm w eG hu
      t' = LTm.tm Lt
      u' = LTm.tm Lu
      ht' = at Lt (LTy.dty LA) (LTy.ety LA)
      hu' = at Lu (s1Ty w ht' (LTy.dty LB)) (eqS1 (LTy.ty LB) (LTm.tm Lt) (LTy.ety LB) (LTm.etm Lt))
  in
    lcv (Fst A' (Lam A' B') (Pair A' (Lam A' B') t' u')) t' A'
        (Eq-cong R.Fst (cong2 R.Pair (LTm.etm Lt) (LTm.etm Lu))) (LTm.etm Lt) (LTy.ety LA)
        (conv-fst-beta (LTy.dty LA) (LTy.dty LB) ht' hu')
lift-Cv w eG (RT.conv-snd-beta hA hB ht hu) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      Lt = lift-Tm w eG ht
      Lu = lift-Tm w eG hu
      t' = LTm.tm Lt
      u' = LTm.tm Lu
      ht' = at Lt (LTy.dty LA) (LTy.ety LA)
      hu' = at Lu (s1Ty w ht' (LTy.dty LB)) (eqS1 (LTy.ty LB) (LTm.tm Lt) (LTy.ety LB) (LTm.etm Lt))
  in
    lcv (Snd A' (Lam A' B') (Pair A' (Lam A' B') t' u')) u' (subst1 B' t')
        (Eq-cong R.Snd (cong2 R.Pair (LTm.etm Lt) (LTm.etm Lu))) (LTm.etm Lu) (eqS1 (LTy.ty LB) (LTm.tm Lt) (LTy.ety LB) (LTm.etm Lt))
        (conv-snd-beta (LTy.dty LA) (LTy.dty LB) ht' hu')
lift-Cv w eG (RT.conv-pairext hA hB ht ht' cf cs) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      dA = LTy.dty LA
      dB = LTy.dty LB
      Lt = lift-Tm w eG ht
      Lt' = lift-Tm w eG ht'
      t1 = LTm.tm Lt
      t2 = LTm.tm Lt'
      h1 = at Lt (isty-Sigma dA dB) (eqSigB (LTy.ety LA) (LTy.ety LB))
      h2 = at Lt' (isty-Sigma dA dB) (eqSigB (LTy.ety LA) (LTy.ety LB))
      CF = lift-Cv w eG cf
      CS = lift-Cv w eG cs
      f1 = ty-Fst dA dB h1
      f2 = ty-Fst dA dB h2
      cfst = conv-trans (sameTm f1 (fst (pCv (LCv.dcv CF))) (Eq-trans (Eq-cong R.Fst (LTm.etm Lt)) (Eq-sym (LCv.el CF)))
                                (Eq-trans (LTy.ety LA) (Eq-sym (LCv.ety CF))))
               (conv-trans (atCv CF dA (LTy.ety LA))
                 (coerceCv (sameTm (snd (pCv (LCv.dcv CF))) f2 (Eq-trans (LCv.er' CF) (Eq-sym (Eq-cong R.Fst (LTm.etm Lt'))))
                                   (Eq-trans (LCv.ety CF) (Eq-sym (LTy.ety LA))))
                           dA (Eq-trans (LCv.ety CF) (Eq-sym (LTy.ety LA)))))
      s1 = ty-Snd dA dB h1
      s2 = ty-Snd dA dB h2
      eS1 = eqS1 (LTy.ty LB) (Fst A' (Lam A' B') (LTm.tm Lt)) (LTy.ety LB) (Eq-cong R.Fst (LTm.etm Lt))
      hS1 = pTm s1
      hW = pTm (fst (pCv (LCv.dcv CS)))
      qW = type-uniq hW hS1 (Eq-trans (LCv.ety CS) (Eq-sym eS1))
      qF = s1fTy w dA f1 f2 cfst dB
      m2 = extract (term-uniq (snd (pCv (LCv.dcv CS))) s2 (Eq-trans (LCv.er' CS) (Eq-sym (Eq-cong R.Snd (LTm.etm Lt')))))
                   (tyeq-trans qW qF)
      csnd = conv-trans (sameTm s1 (fst (pCv (LCv.dcv CS))) (Eq-trans (Eq-cong R.Snd (LTm.etm Lt)) (Eq-sym (LCv.el CS)))
                                (Eq-trans eS1 (Eq-sym (LCv.ety CS))))
               (conv-trans (atCv CS hS1 eS1) (conv-conv m2 qW))
  in
    lcv t1 t2 (SigmaB A' B') (LTm.etm Lt) (LTm.etm Lt') (eqSigB (LTy.ety LA) (LTy.ety LB))
        (conv-pairext dA dB h1 h2 cfst csnd)
lift-Cv w eG (RT.conv-rec-zero hC hz hs) =
  let
      LC = lift-Ty (wf-extend (isty-Nat w)) (cong2 RT.extend eG refl) hC
      C' = LTy.ty LC
      Lz = lift-Tm w eG hz
      Ls = lift-Tm w eG hs
      z' = LTm.tm Lz
      s' = LTm.tm Ls
  in
    lcv (Rec (Lam Nat C') z' s' Zero) z' (subst1 C' Zero)
        (cong4 R.Rec (Eq-cong (R.Lam R.Nat) (LTy.ety LC)) (LTm.etm Lz) (LTm.etm Ls) refl) (LTm.etm Lz)
        (eqS1 (LTy.ty LC) Zero (LTy.ety LC) refl)
        (conv-rec-zero (LTy.dty LC) (at Lz (s1Ty w (ty-Zero w) (LTy.dty LC)) (eqS1 (LTy.ty LC) Zero (LTy.ety LC) refl))
           (at Ls (recStepTy w (LTy.dty LC)) (Eq-trans (er-RecStep C') (Eq-cong R.RecStep (LTy.ety LC)))))
lift-Cv w eG (RT.conv-rec-suc hC hz hs hk) =
  let
      LC = lift-Ty (wf-extend (isty-Nat w)) (cong2 RT.extend eG refl) hC
      C' = LTy.ty LC
      eM = Eq-cong (R.Lam R.Nat) (LTy.ety LC)
      Lz = lift-Tm w eG hz
      Ls = lift-Tm w eG hs
      Lk = lift-Tm w eG hk
      z' = LTm.tm Lz
      s' = LTm.tm Ls
      k' = LTm.tm Lk
  in
    lcv (Rec (Lam Nat C') z' s' (Suc k')) (RecSuc C' z' s' k') (subst1 C' (Suc k'))
        (cong4 R.Rec eM (LTm.etm Lz) (LTm.etm Ls) (Eq-cong R.Suc (LTm.etm Lk)))
        (cong2 R.App (cong2 R.App (LTm.etm Ls) (LTm.etm Lk)) (cong4 R.Rec eM (LTm.etm Lz) (LTm.etm Ls) (LTm.etm Lk)))
        (eqS1 (LTy.ty LC) (Suc (LTm.tm Lk)) (LTy.ety LC) (Eq-cong R.Suc (LTm.etm Lk)))
        (conv-rec-suc (LTy.dty LC) (at Lz (s1Ty w (ty-Zero w) (LTy.dty LC)) (eqS1 (LTy.ty LC) Zero (LTy.ety LC) refl))
           (at Ls (recStepTy w (LTy.dty LC)) (Eq-trans (er-RecStep C') (Eq-cong R.RecStep (LTy.ety LC))))
           (at Lk (isty-Nat w) refl))
lift-Cv w eG (RT.conv-App hA hB c ca) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      dA = LTy.dty LA
      dB = LTy.dty LB
      C = lift-Cv w eG c
      Ca = lift-Cv w eG ca
  in
    lcv (appB A' B' (LCv.lhs C) (LCv.lhs Ca)) (appB A' B' (LCv.rhs C) (LCv.rhs Ca)) (subst1 B' (LCv.lhs Ca))
        (cong2 R.App (LCv.el C) (LCv.el Ca)) (cong2 R.App (LCv.er' C) (LCv.er' Ca)) (eqS1 (LTy.ty LB) (LCv.lhs Ca) (LTy.ety LB) (LCv.el Ca))
        (conv-App dA dB (tyeq-refl dA) (tyeq-refl dB) (atCv C (isty-Pi dA dB) (eqPiB (LTy.ety LA) (LTy.ety LB)))
                  (atCv Ca dA (LTy.ety LA)))
lift-Cv w eG (RT.conv-Fst hA hB c) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      dA = LTy.dty LA
      dB = LTy.dty LB
      C = lift-Cv w eG c
  in
    lcv (Fst A' (Lam A' B') (LCv.lhs C)) (Fst A' (Lam A' B') (LCv.rhs C)) A'
        (Eq-cong R.Fst (LCv.el C)) (Eq-cong R.Fst (LCv.er' C)) (LTy.ety LA)
        (conv-Fst dA dB (tyeq-refl dA) (tyeq-refl dB) (atCv C (isty-Sigma dA dB) (eqSigB (LTy.ety LA) (LTy.ety LB))))
lift-Cv w eG (RT.conv-Snd hA hB c) =
  let
      LA = lift-Ty w eG hA
      LB = lift-Ty (extW LA) (extE LA eG) hB
      A' = LTy.ty LA
      B' = LTy.ty LB
      dA = LTy.dty LA
      dB = LTy.dty LB
      C = lift-Cv w eG c
  in
    lcv (Snd A' (Lam A' B') (LCv.lhs C)) (Snd A' (Lam A' B') (LCv.rhs C)) (subst1 B' (Fst A' (Lam A' B') (LCv.lhs C)))
        (Eq-cong R.Snd (LCv.el C)) (Eq-cong R.Snd (LCv.er' C)) (eqS1 (LTy.ty LB) (Fst A' (Lam A' B') (LCv.lhs C)) (LTy.ety LB) (Eq-cong R.Fst (LCv.el C)))
        (conv-Snd dA dB (tyeq-refl dA) (tyeq-refl dB) (atCv C (isty-Sigma dA dB) (eqSigB (LTy.ety LA) (LTy.ety LB))))
lift-Cv w eG (RT.conv-Pi (RT.univ-V refl) hA hB hB' cA cB) =
  let
      LA = lift-Tm w eG hA
      A1 = LTm.tm LA
      hA1 = at LA (isty-V w) refl
      wE = wf-extend (isty-ElV hA1)
      eE = cong2 RT.extend eG (LTm.etm LA)
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B1 = LTm.tm LB
      B1' = LTm.tm LB'
      hB1 = at LB (isty-V wE) refl
      hB1' = at LB' (isty-V wE) refl
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA1 = conv-trans (alignL hA1 (LTm.etm LA) refl CA) (atCv CA (isty-V w) refl)
      CB = lift-Cv wE eE cB
      cB1 = conv-trans (alignL hB1 (LTm.etm LB) refl CB)
              (conv-trans (atCv CB (isty-V wE) refl)
                 (sameTm (snd (pCv (atCv CB (isty-V wE) refl))) hB1' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
  in
    lcv (PiV A1 (Lam (ElV A1) B1)) (PiV r (Lam (ElV r) B1')) V
        (eqPiB (LTm.etm LA) (LTm.etm LB)) (eqPiB (LCv.er' CA) (LTm.etm LB')) refl
        (conv-PiV hA1 hB1 hB1' cA1 cB1)
lift-Cv w eG (RT.conv-Pi (RT.univ-U f g refl) hA hB hB' cA cB) =
  let
      LA = lift-Tm w eG hA
      A1 = LTm.tm LA
      U = asU (pTm (LTm.dtm LA)) (LTm.ety LA)
      open UDec U renaming (f to f' ; g to g')
      hU = isty-TyU hf hg
      hA1 = ty-conv (LTm.dtm LA) eq
      hE = isty-ElU hA1
      wE = wf-extend hE
      eE = cong2 RT.extend eG (LTm.etm LA)
      hWU = wkTy hE hU
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B1 = LTm.tm LB
      B1' = LTm.tm LB'
      hB1 = at LB hWU (eqWkU f' g' ef eg)
      hB1' = at LB' hWU (eqWkU f' g' ef eg)
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA1 = conv-trans (alignL hA1 (LTm.etm LA) (eqU f' g' ef eg) CA) (atCv CA hU (eqU f' g' ef eg))
      CB = lift-Cv wE eE cB
      cB' = atCv CB hWU (eqWkU f' g' ef eg)
      cB1 = conv-trans (alignL hB1 (LTm.etm LB) (eqWkU f' g' ef eg) CB)
              (conv-trans cB'
                 (sameTm (snd (pCv cB')) hB1' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
  in
    lcv (PiU f' g' A1 (Lam (ElU f' g' A1) B1)) (PiU f' g' r (Lam (ElU f' g' r) B1')) (TyU f' g')
        (eqPiB (LTm.etm LA) (LTm.etm LB)) (eqPiB (LCv.er' CA) (LTm.etm LB')) (eqU f' g' ef eg)
        (conv-PiU hA1 hB1 hB1' cA1 cB1)
lift-Cv w eG (RT.conv-Sigma (RT.univ-V refl) hA hB hB' cA cB) =
  let
      LA = lift-Tm w eG hA
      A1 = LTm.tm LA
      hA1 = at LA (isty-V w) refl
      wE = wf-extend (isty-ElV hA1)
      eE = cong2 RT.extend eG (LTm.etm LA)
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B1 = LTm.tm LB
      B1' = LTm.tm LB'
      hB1 = at LB (isty-V wE) refl
      hB1' = at LB' (isty-V wE) refl
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA1 = conv-trans (alignL hA1 (LTm.etm LA) refl CA) (atCv CA (isty-V w) refl)
      CB = lift-Cv wE eE cB
      cB1 = conv-trans (alignL hB1 (LTm.etm LB) refl CB)
              (conv-trans (atCv CB (isty-V wE) refl)
                 (sameTm (snd (pCv (atCv CB (isty-V wE) refl))) hB1' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
  in
    lcv (SigV A1 (Lam (ElV A1) B1)) (SigV r (Lam (ElV r) B1')) V
        (eqSigB (LTm.etm LA) (LTm.etm LB)) (eqSigB (LCv.er' CA) (LTm.etm LB')) refl
        (conv-SigV hA1 hB1 hB1' cA1 cB1)
lift-Cv w eG (RT.conv-Sigma (RT.univ-U f g refl) hA hB hB' cA cB) =
  let
      LA = lift-Tm w eG hA
      A1 = LTm.tm LA
      U = asU (pTm (LTm.dtm LA)) (LTm.ety LA)
      open UDec U renaming (f to f' ; g to g')
      hU = isty-TyU hf hg
      hA1 = ty-conv (LTm.dtm LA) eq
      hE = isty-ElU hA1
      wE = wf-extend hE
      eE = cong2 RT.extend eG (LTm.etm LA)
      hWU = wkTy hE hU
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B1 = LTm.tm LB
      B1' = LTm.tm LB'
      hB1 = at LB hWU (eqWkU f' g' ef eg)
      hB1' = at LB' hWU (eqWkU f' g' ef eg)
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA1 = conv-trans (alignL hA1 (LTm.etm LA) (eqU f' g' ef eg) CA) (atCv CA hU (eqU f' g' ef eg))
      CB = lift-Cv wE eE cB
      cB' = atCv CB hWU (eqWkU f' g' ef eg)
      cB1 = conv-trans (alignL hB1 (LTm.etm LB) (eqWkU f' g' ef eg) CB)
              (conv-trans cB'
                 (sameTm (snd (pCv cB')) hB1' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
  in
    lcv (SigU f' g' A1 (Lam (ElU f' g' A1) B1)) (SigU f' g' r (Lam (ElU f' g' r) B1')) (TyU f' g')
        (eqSigB (LTm.etm LA) (LTm.etm LB)) (eqSigB (LCv.er' CA) (LTm.etm LB')) (eqU f' g' ef eg)
        (conv-SigU hA1 hB1 hB1' cA1 cB1)
lift-Cv w eG (RT.conv-Suc c) =
  let
      C = lift-Cv w eG c
  in
    lcv (Suc (LCv.lhs C)) (Suc (LCv.rhs C)) Nat (Eq-cong R.Suc (LCv.el C)) (Eq-cong R.Suc (LCv.er' C)) refl
        (conv-Suc (atCv C (isty-Nat w) refl))
lift-Cv w eG (RT.conv-Rec hC hC' q cz cs ck) =
  let
      wN = wf-extend (isty-Nat w)
      eN = cong2 RT.extend eG refl
      LC = lift-Ty wN eN hC
      LC' = lift-Ty wN eN hC'
      C1 = LTy.ty LC
      C1' = LTy.ty LC'
      dC = LTy.dty LC
      dC' = LTy.dty LC'
      Q = lift-TE wN eN q
      qC = tyeq-trans (type-uniq dC (fst (pTE (LTE.dte Q))) (Eq-trans (LTy.ety LC) (Eq-sym (LTE.el Q))))
             (tyeq-trans (LTE.dte Q) (type-uniq (snd (pTE (LTE.dte Q))) dC' (Eq-trans (LTE.er' Q) (Eq-sym (LTy.ety LC')))))
      Cz = lift-Cv w eG cz
      Cs = lift-Cv w eG cs
      Ck = lift-Cv w eG ck
  in
    lcv (Rec (Lam Nat C1) (LCv.lhs Cz) (LCv.lhs Cs) (LCv.lhs Ck)) (Rec (Lam Nat C1') (LCv.rhs Cz) (LCv.rhs Cs) (LCv.rhs Ck))
        (subst1 C1 (LCv.lhs Ck))
        (cong4 R.Rec (Eq-cong (R.Lam R.Nat) (LTy.ety LC)) (LCv.el Cz) (LCv.el Cs) (LCv.el Ck))
        (cong4 R.Rec (Eq-cong (R.Lam R.Nat) (LTy.ety LC')) (LCv.er' Cz) (LCv.er' Cs) (LCv.er' Ck))
        (eqS1 (LTy.ty LC) (LCv.lhs Ck) (LTy.ety LC) (LCv.el Ck))
        (conv-Rec dC dC' qC (atCv Cz (s1Ty w (ty-Zero w) dC) (eqS1 (LTy.ty LC) Zero (LTy.ety LC) refl))
           (atCv Cs (recStepTy w dC) (Eq-trans (er-RecStep C1) (Eq-cong R.RecStep (LTy.ety LC))))
           (atCv Ck (isty-Nat w) refl))
lift-Cv w eG (RT.conv-Ucode hf hg cf cg) =
  let
      open OpL (liftOp w eG hf hg) renaming (hf to hf' ; hg to hg')
      Cf = lift-Cv w eG cf
      Cg = lift-Cv w eG cg
      cf' = conv-trans (alignL hf' ef refl Cf) (atCv Cf (opFTy w) refl)
      cg' = conv-trans (alignL hg' eg (eqOpG f' ef) Cg) (atCv Cg (opGTy w hf') (eqOpG f' ef))
  in
    lcv (UV f' g') (UV (LCv.rhs Cf) (LCv.rhs Cg)) V (eqU f' g' ef eg) (eqU (LCv.rhs Cf) (LCv.rhs Cg) (LCv.er' Cf) (LCv.er' Cg)) refl
        (conv-UV hf' hg' cf' cg')
lift-Cv w eG (RT.conv-Fhat cf cg hA hB hB' cA cB) =
  let
      Cf = lift-Cv w eG cf
      Cg = lift-Cv w eG cg
      cf' = atCv Cf (opFTy w) refl
      lf = LCv.lhs Cf
      rf = LCv.rhs Cf
      hf0 = fst (pCv cf')
      hf1 = snd (pCv cf')
      cg' = atCv Cg (opGTy w hf0) (eqOpG lf (LCv.el Cf))
      lg = LCv.lhs Cg
      rg = LCv.rhs Cg
      hg0 = fst (pCv cg')
      hg1 = ty-conv (snd (pCv cg')) (opGEq w hf0 hf1 cf')
      hU0 = isty-TyU hf0 hg0
      eU = tyeq-TyU hf0 hg0 cf' cg'
      eU0 = eqU lf lg (LCv.el Cf) (LCv.el Cg)
      LA = lift-Tm w eG hA
      A0 = LTm.tm LA
      hA0 = at LA hU0 eU0
      hE = isty-ElU hA0
      wE = wf-extend hE
      eE = cong2 RT.extend eG (LTm.etm LA)
      hWU = wkTy hE hU0
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B0 = LTm.tm LB
      B0' = LTm.tm LB'
      hB0 = at LB hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      hB0' = at LB' hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA0 = conv-trans (alignL hA0 (LTm.etm LA) eU0 CA) (atCv CA hU0 eU0)
      hr = ty-conv (snd (pCv cA0)) eU
      CB = lift-Cv wE eE cB
      cB' = atCv CB hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      cB0 = conv-trans (alignL hB0 (LTm.etm LB) (eqWkU lf lg (LCv.el Cf) (LCv.el Cg)) CB)
              (conv-trans cB' (sameTm (snd (pCv cB')) hB0' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
      hEr = isty-ElU hr
      hB0r = ty-conv (ccTm hEr (tyeq-sym (elUEq hA0 hr cA0)) hB0') (wkTE hEr eU)
  in
    lcv (Fhat lf lg A0 (Lam (ElU lf lg A0) B0)) (Fhat rf rg r (Lam (ElU rf rg r) B0')) (TyU lf lg)
        (cong4 R.Fhat (LCv.el Cf) (LCv.el Cg) (LTm.etm LA) (cong2 R.Lam (LTm.etm LA) (LTm.etm LB)))
        (cong4 R.Fhat (LCv.er' Cf) (LCv.er' Cg) (LCv.er' CA) (cong2 R.Lam (LCv.er' CA) (LTm.etm LB')))
        (eqU lf lg (LCv.el Cf) (LCv.el Cg))
        (ccFhat hA0 hr cA0 hB0 hB0r cB0 eU hf0 hg0 hf1 hg1 cf')
lift-Cv w eG (RT.conv-Ghat cf cg hA hB hB' cA cB cc) =
  let
      Cf = lift-Cv w eG cf
      Cg = lift-Cv w eG cg
      cf' = atCv Cf (opFTy w) refl
      lf = LCv.lhs Cf
      rf = LCv.rhs Cf
      hf0 = fst (pCv cf')
      hf1 = snd (pCv cf')
      cg' = atCv Cg (opGTy w hf0) (eqOpG lf (LCv.el Cf))
      lg = LCv.lhs Cg
      rg = LCv.rhs Cg
      hg0 = fst (pCv cg')
      hg1 = ty-conv (snd (pCv cg')) (opGEq w hf0 hf1 cf')
      hU0 = isty-TyU hf0 hg0
      eU = tyeq-TyU hf0 hg0 cf' cg'
      eU0 = eqU lf lg (LCv.el Cf) (LCv.el Cg)
      LA = lift-Tm w eG hA
      A0 = LTm.tm LA
      hA0 = at LA hU0 eU0
      hE = isty-ElU hA0
      wE = wf-extend hE
      eE = cong2 RT.extend eG (LTm.etm LA)
      hWU = wkTy hE hU0
      LB = lift-Tm wE eE hB
      LB' = lift-Tm wE eE hB'
      B0 = LTm.tm LB
      B0' = LTm.tm LB'
      hB0 = at LB hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      hB0' = at LB' hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      CA = lift-Cv w eG cA
      r = LCv.rhs CA
      cA0 = conv-trans (alignL hA0 (LTm.etm LA) eU0 CA) (atCv CA hU0 eU0)
      hr = ty-conv (snd (pCv cA0)) eU
      CB = lift-Cv wE eE cB
      cB' = atCv CB hWU (eqWkU lf lg (LCv.el Cf) (LCv.el Cg))
      cB0 = conv-trans (alignL hB0 (LTm.etm LB) (eqWkU lf lg (LCv.el Cf) (LCv.el Cg)) CB)
              (conv-trans cB' (sameTm (snd (pCv cB')) hB0' (Eq-trans (LCv.er' CB) (Eq-sym (LTm.etm LB'))) refl))
      hEr = isty-ElU hr
      hB0r = ty-conv (ccTm hEr (tyeq-sym (elUEq hA0 hr cA0)) hB0') (wkTE hEr eU)
      hF0 = ty-Fhat hf0 hg0 hA0 hB0
      hF1 = ty-Fhat hf1 hg1 hr hB0r
      eF = cong4 R.Fhat (LCv.el Cf) (LCv.el Cg) (LTm.etm LA) (cong2 R.Lam (LTm.etm LA) (LTm.etm LB))
      Cc = lift-Cv w eG cc
      cc' = atCv Cc (isty-ElU hF0) eF
      hc0 = fst (pCv cc')
      qF = elUEq hF0 hF1 (ccFhat hA0 hr cA0 hB0 hB0r cB0 eU hf0 hg0 hf1 hg1 cf')
      hc1 = ty-conv (snd (pCv cc')) qF
  in
    lcv (Ghat lf lg A0 (Lam (ElU lf lg A0) B0) (LCv.lhs Cc)) (Ghat rf rg r (Lam (ElU rf rg r) B0') (LCv.rhs Cc)) (TyU lf lg)
        (cong5 R.Ghat (LCv.el Cf) (LCv.el Cg) (LTm.etm LA) (cong2 R.Lam (LTm.etm LA) (LTm.etm LB)) (LCv.el Cc))
        (cong5 R.Ghat (LCv.er' Cf) (LCv.er' Cg) (LCv.er' CA) (cong2 R.Lam (LCv.er' CA) (LTm.etm LB')) (LCv.er' Cc))
        (eqU lf lg (LCv.el Cf) (LCv.el Cg))
        (ccGhat hA0 hr cA0 hB0 hB0r cB0 eU hf0 hg0 hf1 hg1 cf' cg' hc0 hc1 cc')
