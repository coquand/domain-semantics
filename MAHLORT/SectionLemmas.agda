{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/SectionLemmas.agda
--
-- Tools for the section of erasure (MAHLORT/Section), relative to TInj:
--   * the lift records (a Tarski judgement with prescribed erasure, in a
--     GIVEN Tarski context);
--   * asV / asU: a Tarski type whose erasure is V, resp. Ucode p q, is
--     V, resp. some U_{f,g} with |f| = p, |g| = q (no term erases to V;
--     the codes erasing to Ucode are U^ and its T^-images);
--   * coerce / sameTm: retyping along, and identifying by, erasure
--     (type-uniq, term-uniq + extraction).
------------------------------------------------------------------------

open import MAHLORT.Hyp

module MAHLORT.SectionLemmas (I : TInj) where

open import MAHLO.Basic hiding (Sigma)
import MAHLO.Syntax as R
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Erasure
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.Presup
open import MAHLORT.TNoConf
open import MAHLORT.Coh
open import MAHLORT.UniqLemmas I
open import MAHLORT.Uniq I

------------------------------------------------------------------------
-- Lift records
------------------------------------------------------------------------

record LTy {n : Num} (G : Ctx n) (A : R.Expr n) : Set where
  constructor lty
  field
    ty  : Expr n
    ety : Eq (er ty) A
    dty : IsType G ty

record LTm {n : Num} (G : Ctx n) (t A : R.Expr n) : Set where
  constructor ltm
  field
    tm  : Expr n
    ty  : Expr n
    etm : Eq (er tm) t
    ety : Eq (er ty) A
    dtm : HasType G tm ty

record LTE {n : Num} (G : Ctx n) (A B : R.Expr n) : Set where
  constructor lte
  field
    lhs : Expr n
    rhs : Expr n
    el  : Eq (er lhs) A
    er' : Eq (er rhs) B
    dte : TyEq G lhs rhs

record LCv {n : Num} (G : Ctx n) (t u A : R.Expr n) : Set where
  constructor lcv
  field
    lhs : Expr n
    rhs : Expr n
    ty  : Expr n
    el  : Eq (er lhs) t
    er' : Eq (er rhs) u
    ety : Eq (er ty) A
    dcv : ConvTm G lhs rhs ty

------------------------------------------------------------------------
-- No term erases to V
------------------------------------------------------------------------

noVtm : {n : Num} {G : Ctx n} {a A : Expr n} -> HasType G a A -> Eq (er a) R.V -> Empty
noVtm (ty-conv h q) e = noVtm h e
noVtm (ty-That h) e = noVtm h e
noVtm (ty-var _) ()
noVtm (ty-Lam _ _ _) ()
noVtm (ty-App _ _ _ _) ()
noVtm (ty-Pair _ _ _ _) ()
noVtm (ty-Fst _ _ _) ()
noVtm (ty-Snd _ _ _) ()
noVtm (ty-Zero _) ()
noVtm (ty-Suc _) ()
noVtm (ty-Rec _ _ _ _) ()
noVtm (ty-PiV _ _) ()
noVtm (ty-SigV _ _) ()
noVtm (ty-NatV _) ()
noVtm (ty-UV _ _) ()
noVtm (ty-PiU _ _) ()
noVtm (ty-SigU _ _) ()
noVtm (ty-NatU _) ()
noVtm (ty-Fhat _ _ _ _) ()
noVtm (ty-Ghat _ _ _ _ _) ()

asV : {n : Num} {G : Ctx n} {X : Expr n} -> IsType G X -> Eq (er X) R.V -> TyEq G X V
asV h@(isty-V w) e = tyeq-refl h
asV (isty-ElV h) e = Empty-elim (noVtm h e)
asV (isty-ElU h) e = Empty-elim (noVtm h e)
asV (isty-TyU _ _) ()
asV (isty-Pi _ _) ()
asV (isty-Sigma _ _) ()
asV (isty-Nat _) ()

------------------------------------------------------------------------
-- Codes erasing to Ucode
------------------------------------------------------------------------

record UDec {n : Num} (G : Ctx n) (X : Expr n) (p q : R.Expr n) : Set where
  constructor udec
  field
    f  : Expr n
    g  : Expr n
    ef : Eq (er f) p
    eg : Eq (er g) q
    hf : HasType G f OpF
    hg : HasType G g (OpG f)
    eq : TyEq G X (TyU f g)

decU : {n : Num} {G : Ctx n} {a A : Expr n} {p q : R.Expr n} (k : Kind n) ->
       HasType G a A -> TyEq G A (KTy k) -> Eq (er a) (R.Ucode p q) -> UDec G (ElV (KIm k a)) p q
decU k (ty-conv h q) qK e = decU k h (tyeq-trans q qK) e
decU kV (ty-That {f = f} {g = g} hy) qK e = decU (kU f g) hy (tyeq-refl (pTm hy)) e
decU (kU f g) (ty-That hy) qK e = Empty-elim (tV-U qK)
decU kV (ty-UV {f = f} {g = g} hf hg) qK e =
  udec f g (fst (r-ucode e)) (snd (r-ucode e)) hf hg (tyeq-El-UV hf hg)
decU (kU f g) (ty-UV hf hg) qK e = Empty-elim (tV-U qK)
decU k (ty-var _) qK ()
decU k (ty-Lam _ _ _) qK ()
decU k (ty-App _ _ _ _) qK ()
decU k (ty-Pair _ _ _ _) qK ()
decU k (ty-Fst _ _ _) qK ()
decU k (ty-Snd _ _ _) qK ()
decU k (ty-Zero _) qK ()
decU k (ty-Suc _) qK ()
decU k (ty-Rec _ _ _ _) qK ()
decU k (ty-PiV _ _) qK ()
decU k (ty-SigV _ _) qK ()
decU k (ty-NatV _) qK ()
decU k (ty-PiU _ _) qK ()
decU k (ty-SigU _ _) qK ()
decU k (ty-NatU _) qK ()
decU k (ty-Fhat _ _ _ _) qK ()
decU k (ty-Ghat _ _ _ _ _) qK ()

asU : {n : Num} {G : Ctx n} {X : Expr n} {p q : R.Expr n} -> IsType G X -> Eq (er X) (R.Ucode p q) -> UDec G X p q
asU (isty-TyU {f = f} {g = g} hf hg) e =
  udec f g (fst (r-ucode e)) (snd (r-ucode e)) hf hg (tyeq-refl (isty-TyU hf hg))
asU (isty-ElV h) e = decU kV h (tyeq-refl (isty-V (wfTm h))) e
asU (isty-ElU {f = f} {g = g} h) e =
  udec f' g' ef eg hf hg (tyeq-trans (tyeq-ElU-That h) eq)
  where open UDec (decU (kU f g) h (tyeq-refl (pTm h)) e) renaming (f to f' ; g to g')
asU (isty-V _) ()
asU (isty-Pi _ _) ()
asU (isty-Sigma _ _) ()
asU (isty-Nat _) ()

------------------------------------------------------------------------
-- Retyping and identifying along erasure
------------------------------------------------------------------------

coerce : {n : Num} {G : Ctx n} {t X Y : Expr n} ->
         HasType G t X -> IsType G Y -> Eq (er X) (er Y) -> HasType G t Y
coerce h hY e = ty-conv h (type-uniq (pTm h) hY e)

coerceCv : {n : Num} {G : Ctx n} {t u X Y : Expr n} ->
           ConvTm G t u X -> IsType G Y -> Eq (er X) (er Y) -> ConvTm G t u Y
coerceCv c hY e = conv-conv c (type-uniq (pTm (fst (pCv c))) hY e)

sameTm : {n : Num} {G : Ctx n} {t t' X Y : Expr n} ->
         HasType G t X -> HasType G t' Y -> Eq (er t) (er t') -> Eq (er X) (er Y) -> ConvTm G t t' X
sameTm h h' e eX = extract (term-uniq h h' e) (type-uniq (pTm h) (pTm h') eX)

-- the image in V of a code of U_{f,g} agrees with a V-code of the same erasure
upSame : {n : Num} {G : Ctx n} {a b f g : Expr n} ->
         HasType G a V -> HasType G b (TyU f g) -> Eq (er a) (er b) -> ConvTm G a (That b) V
upSame ha hb e =
  cohUp (term-uniq ha hb e) (upV (tyeq-refl (isty-V (wfTm ha))) ha refl) (upK' (kU _ _) hb)

-- the lifted term, at a prescribed type of the same erasure
at : {n : Num} {G : Ctx n} {t A : R.Expr n} (L : LTm G t A) {Y : Expr n} ->
     IsType G Y -> Eq (er Y) A -> HasType G (LTm.tm L) Y
at L hY eY = coerce (LTm.dtm L) hY (Eq-trans (LTm.ety L) (Eq-sym eY))

atCv : {n : Num} {G : Ctx n} {t u A : R.Expr n} (L : LCv G t u A) {Y : Expr n} ->
       IsType G Y -> Eq (er Y) A -> ConvTm G (LCv.lhs L) (LCv.rhs L) Y
atCv L hY eY = coerceCv (LCv.dcv L) hY (Eq-trans (LCv.ety L) (Eq-sym eY))
