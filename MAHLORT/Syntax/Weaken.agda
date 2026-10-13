{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Weaken.agda
--
-- Type-preserving renamings preserve the judgements of
-- MAHLORT/TarskiTyping.agda; weakening is the instance  r = wkRen.
-- Port of MAHLOINJ/Syntax/Weaken.agda.  Written so that Subst.agda is
-- generated from it: every renaming fact is a lemma  ren-X r  (with
-- counterpart  subst-X s), and  liftRT  takes the (unused) IsType of the
-- new entry, as  liftWS  does.
------------------------------------------------------------------------

module MAHLORT.Syntax.Weaken where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas

RenTypes : {n m : Num} -> Ctx n -> Ctx m -> Ren n m -> Set
RenTypes G H r = (i : Fin _) -> Eq (lookup H (r i)) (renExpr r (lookup G i))

liftRT : {n m : Num} {G : Ctx n} {H : Ctx m} {r : Ren n m} {A : Expr n} ->
         RenTypes G H r -> IsType H (renExpr r A) ->
         RenTypes (extend G A) (extend H (renExpr r A)) (liftRen r)
liftRT {r = r} {A} rt _ fzero = Eq-sym (ren-wk-comm r A)
liftRT {G = G} {r = r} rt _ (fsuc i) =
  Eq-trans (Eq-cong wkExpr (rt i)) (Eq-sym (ren-wk-comm r (lookup G i)))

mutual
  rTy : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {A : Expr n} -> IsType G A -> IsType H (renExpr r A)
  rTy r rt w (isty-V _) = isty-V w
  rTy r rt w (isty-ElV h) = isty-ElV (rTm r rt w h)
  rTy r rt w (isty-TyU {f = f} hf hg) =
    isty-TyU (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg))
  rTy r rt w (isty-ElU h) = isty-ElU (rTm r rt w h)
  rTy r rt w (isty-Pi hA hB) =
    isty-Pi hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
    where hX = rTy r rt w hA
  rTy r rt w (isty-Sigma hA hB) =
    isty-Sigma hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
    where hX = rTy r rt w hA
  rTy r rt w (isty-Nat _) = isty-Nat w

  rTm : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {t A : Expr n} -> HasType G t A -> HasType H (renExpr r t) (renExpr r A)
  rTm r rt w (ty-var {i = i} _) = trHT refl (rt i) (ty-var w)
  rTm r rt w (ty-conv h q) = ty-conv (rTm r rt w h) (rTE r rt w q)
  rTm r rt w (ty-Lam hA hB ht) =
    ty-Lam hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
              (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) ht)
    where hX = rTy r rt w hA
  rTm r rt w (ty-App {a = a} {B} hA hB ht ha) =
    trHT refl (Eq-sym (ren-subst1 r B a))
      (ty-App hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTm r rt w ht) (rTm r rt w ha))
    where hX = rTy r rt w hA
  rTm r rt w (ty-Pair {a = a} {B = B} hA hB ha hb) =
    ty-Pair hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
            (rTm r rt w ha) (trHT refl (ren-subst1 r B a) (rTm r rt w hb))
    where hX = rTy r rt w hA
  rTm r rt w (ty-Fst hA hB ht) =
    ty-Fst hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTm r rt w ht)
    where hX = rTy r rt w hA
  rTm r rt w (ty-Snd {A = A} {t = t} {B} hA hB ht) =
    trHT refl (Eq-sym (ren-subst1 r B (Fst A (Lam A B) t)))
      (ty-Snd hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTm r rt w ht))
    where hX = rTy r rt w hA
  rTm r rt w (ty-Zero _) = ty-Zero w
  rTm r rt w (ty-Suc h) = ty-Suc (rTm r rt w h)
  rTm r rt w (ty-Rec {k = k} {C} hC hz hs hk) =
    trHT refl (Eq-sym (ren-subst1 r C k))
      (ty-Rec (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hC)
              (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
              (trHT refl (ren-RecStep r C) (rTm r rt w hs))
              (rTm r rt w hk))
    where hX = isty-Nat w
  rTm r rt w (ty-PiV ha hb) =
    ty-PiV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
    where hX = isty-ElV (rTm r rt w ha)
  rTm r rt w (ty-SigV ha hb) =
    ty-SigV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
    where hX = isty-ElV (rTm r rt w ha)
  rTm r rt w (ty-NatV _) = ty-NatV w
  rTm r rt w (ty-UV {f = f} hf hg) =
    ty-UV (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg))
  rTm r rt w (ty-PiU {f = f} {g} ha hb) =
    ty-PiU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rTm r rt w (ty-SigU {f = f} {g} ha hb) =
    ty-SigU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rTm r rt w (ty-NatU hU) = ty-NatU (rTy r rt w hU)
  rTm r rt w (ty-Fhat {f = f} {g} hf hg ha hb) =
    ty-Fhat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rTm r rt w (ty-Ghat {f = f} {g} hf hg ha hb hc) =
    ty-Ghat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
      (rTm r rt w hc)
    where hX = isty-ElU (rTm r rt w ha)
  rTm r rt w (ty-That h) = ty-That (rTm r rt w h)

  rTE : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {A B : Expr n} -> TyEq G A B -> TyEq H (renExpr r A) (renExpr r B)
  rTE r rt w (tyeq-refl h) = tyeq-refl (rTy r rt w h)
  rTE r rt w (tyeq-sym q) = tyeq-sym (rTE r rt w q)
  rTE r rt w (tyeq-trans q q') = tyeq-trans (rTE r rt w q) (rTE r rt w q')
  rTE r rt w (tyeq-ElV c) = tyeq-ElV (rCv r rt w c)
  rTE r rt w (tyeq-ElU c) = tyeq-ElU (rCv r rt w c)
  rTE r rt w (tyeq-TyU {f = f} hf hg cf cg) =
    tyeq-TyU (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rCv r rt w cf)
             (trCv refl refl (ren-OpG r f) (rCv r rt w cg))
  rTE r rt w (tyeq-Pi hA hB hB' qA qB) =
    tyeq-Pi hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
            (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB') (rTE r rt w qA)
            (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB)
    where hX = rTy r rt w hA
  rTE r rt w (tyeq-Sigma hA hB hB' qA qB) =
    tyeq-Sigma hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
               (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB') (rTE r rt w qA)
               (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB)
    where hX = rTy r rt w hA
  rTE r rt w (tyeq-El-PiV ha hb) =
    tyeq-El-PiV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
    where hX = isty-ElV (rTm r rt w ha)
  rTE r rt w (tyeq-El-SigV ha hb) =
    tyeq-El-SigV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
    where hX = isty-ElV (rTm r rt w ha)
  rTE r rt w (tyeq-El-NatV _) = tyeq-El-NatV w
  rTE r rt w (tyeq-El-UV {f = f} hf hg) =
    tyeq-El-UV (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg))
  rTE r rt w (tyeq-ElU-That h) = tyeq-ElU-That (rTm r rt w h)

  rCv : {n m : Num} {G : Ctx n} {H : Ctx m} (r : Ren n m) -> RenTypes G H r -> WfCtx H ->
        {t u A : Expr n} -> ConvTm G t u A -> ConvTm H (renExpr r t) (renExpr r u) (renExpr r A)
  rCv r rt w (conv-refl h) = conv-refl (rTm r rt w h)
  rCv r rt w (conv-sym c) = conv-sym (rCv r rt w c)
  rCv r rt w (conv-trans c c') = conv-trans (rCv r rt w c) (rCv r rt w c')
  rCv r rt w (conv-conv c q) = conv-conv (rCv r rt w c) (rTE r rt w q)
  rCv r rt w (conv-beta {a = a} {B} {t} hA hB ht ha) =
    trCv refl (Eq-sym (ren-subst1 r t a)) (Eq-sym (ren-subst1 r B a))
      (conv-beta hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
                 (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) ht) (rTm r rt w ha))
    where hX = rTy r rt w hA
  rCv r rt w (conv-funext {A = A} {t} {t'} {B} hA hB ht ht' c) =
    conv-funext hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
                (rTm r rt w ht) (rTm r rt w ht')
      (trCv (ren-FunB r A B t) (ren-FunB r A B t') refl
            (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) c))
    where hX = rTy r rt w hA
  rCv r rt w (conv-fst-beta {a = a} {B = B} hA hB ha hb) =
    conv-fst-beta hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
                  (rTm r rt w ha) (trHT refl (ren-subst1 r B a) (rTm r rt w hb))
    where hX = rTy r rt w hA
  rCv r rt w (conv-snd-beta {a = a} {B = B} hA hB ha hb) =
    trCv refl refl (Eq-sym (ren-subst1 r B a))
      (conv-snd-beta hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
                     (rTm r rt w ha) (trHT refl (ren-subst1 r B a) (rTm r rt w hb)))
    where hX = rTy r rt w hA
  rCv r rt w (conv-pairext {A = A} {t = t} {B = B} hA hB ht ht' cf cs) =
    conv-pairext hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB)
                 (rTm r rt w ht) (rTm r rt w ht') (rCv r rt w cf)
                 (trCv refl refl (ren-subst1 r B (Fst A (Lam A B) t)) (rCv r rt w cs))
    where hX = rTy r rt w hA
  rCv r rt w (conv-rec-zero {C = C} hC hz hs) =
    trCv refl refl (Eq-sym (ren-subst1 r C Zero))
      (conv-rec-zero (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hC)
                     (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
                     (trHT refl (ren-RecStep r C) (rTm r rt w hs)))
    where hX = isty-Nat w
  rCv r rt w (conv-rec-suc {z = z} {s} {k} {C} hC hz hs hk) =
    trCv refl (Eq-sym (ren-RecSuc r C z s k)) (Eq-sym (ren-subst1 r C (Suc k)))
      (conv-rec-suc (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hC)
                    (trHT refl (ren-subst1 r C Zero) (rTm r rt w hz))
                    (trHT refl (ren-RecStep r C) (rTm r rt w hs))
                    (rTm r rt w hk))
    where hX = isty-Nat w
  rCv r rt w (conv-Lam hA hB q c) =
    conv-Lam hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTE r rt w q)
             (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) c)
    where hX = rTy r rt w hA
  rCv r rt w (conv-App {a = a} {B = B} hA hB qA qB c ca) =
    trCv refl refl (Eq-sym (ren-subst1 r B a))
      (conv-App hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTE r rt w qA)
                (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB) (rCv r rt w c) (rCv r rt w ca))
    where hX = rTy r rt w hA
  rCv r rt w (conv-Pair {a = a} {B = B} hA hB qA qB ca cb) =
    conv-Pair hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTE r rt w qA)
              (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB) (rCv r rt w ca)
              (trCv refl refl (ren-subst1 r B a) (rCv r rt w cb))
    where hX = rTy r rt w hA
  rCv r rt w (conv-Fst hA hB qA qB c) =
    conv-Fst hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTE r rt w qA)
             (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB) (rCv r rt w c)
    where hX = rTy r rt w hA
  rCv r rt w (conv-Snd {A = A} {t = t} {B = B} hA hB qA qB c) =
    trCv refl refl (Eq-sym (ren-subst1 r B (Fst A (Lam A B) t)))
      (conv-Snd hX (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hB) (rTE r rt w qA)
                (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) qB) (rCv r rt w c))
    where hX = rTy r rt w hA
  rCv r rt w (conv-Suc c) = conv-Suc (rCv r rt w c)
  rCv r rt w (conv-Rec {k = k} {C = C} hC hC' q cz cs ck) =
    trCv refl refl (Eq-sym (ren-subst1 r C k))
      (conv-Rec (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hC)
                (rTy (liftRen r) (liftRT rt hX) (wf-extend hX) hC')
                (rTE (liftRen r) (liftRT rt hX) (wf-extend hX) q)
                (trCv refl refl (ren-subst1 r C Zero) (rCv r rt w cz))
                (trCv refl refl (ren-RecStep r C) (rCv r rt w cs))
                (rCv r rt w ck))
    where hX = isty-Nat w
  rCv r rt w (conv-PiV ha hb hb' ca cb) =
    conv-PiV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
             (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb') (rCv r rt w ca)
             (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb)
    where hX = isty-ElV (rTm r rt w ha)
  rCv r rt w (conv-SigV ha hb hb' ca cb) =
    conv-SigV (rTm r rt w ha) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb)
              (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb') (rCv r rt w ca)
              (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb)
    where hX = isty-ElV (rTm r rt w ha)
  rCv r rt w (conv-UV {f = f} hf hg cf cg) =
    conv-UV (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rCv r rt w cf)
            (trCv refl refl (ren-OpG r f) (rCv r rt w cg))
  rCv r rt w (conv-PiU {f = f} {g} ha hb hb' ca cb) =
    conv-PiU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb'))
      (rCv r rt w ca)
      (trCv refl refl (ren-wk-comm r (TyU f g)) (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-SigU {f = f} {g} ha hb hb' ca cb) =
    conv-SigU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb'))
      (rCv r rt w ca)
      (trCv refl refl (ren-wk-comm r (TyU f g)) (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-Fhat {f = f} {g} hf hg ha hb hb' ca cb) =
    conv-Fhat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb'))
      (rCv r rt w ca)
      (trCv refl refl (ren-wk-comm r (TyU f g)) (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-Ghat {f = f} {g} hf hg ha hb hb' ca cb cc) =
    conv-Ghat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb'))
      (rCv r rt w ca)
      (trCv refl refl (ren-wk-comm r (TyU f g)) (rCv (liftRen r) (liftRT rt hX) (wf-extend hX) cb))
      (rCv r rt w cc)
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-That c) = conv-That (rCv r rt w c)
  rCv r rt w (conv-That-PiU {f = f} {g} ha hb) =
    conv-That-PiU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-That-SigU {f = f} {g} ha hb) =
    conv-That-SigU (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-That-NatU hU) = conv-That-NatU (rTy r rt w hU)
  rCv r rt w (conv-That-Fhat {f = f} {g} hf hg ha hb) =
    conv-That-Fhat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
      (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-That-Ghat {f = f} {g} {a} {c} {b} hf hg ha hb hc) =
    trCv refl (Eq-sym (ren-gApp r f g (That a) (Lam (ElV (That a)) (That b)) c)) refl
      (conv-That-Ghat (rTm r rt w hf) (trHT refl (ren-OpG r f) (rTm r rt w hg)) (rTm r rt w ha)
        (trHT refl (ren-wk-comm r (TyU f g)) (rTm (liftRen r) (liftRT rt hX) (wf-extend hX) hb))
        (rTm r rt w hc))
    where hX = isty-ElU (rTm r rt w ha)
  rCv r rt w (conv-reflect ha hb c) = conv-reflect (rTm r rt w ha) (rTm r rt w hb) (rCv r rt w c)

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

wkRT : {n : Num} {G : Ctx n} {C : Expr n} -> RenTypes G (extend G C) wkRen
wkRT i = refl

module _ {n : Num} {G : Ctx n} {C : Expr n} (hC : IsType G C) where

  wkTy : {A : Expr n} -> IsType G A -> IsType (extend G C) (wkExpr A)
  wkTy = rTy wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkTm : {t A : Expr n} -> HasType G t A -> HasType (extend G C) (wkExpr t) (wkExpr A)
  wkTm = rTm wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkTE : {A B : Expr n} -> TyEq G A B -> TyEq (extend G C) (wkExpr A) (wkExpr B)
  wkTE = rTE wkRen (wkRT {G = G} {C}) (wf-extend hC)

  wkCv : {t u A : Expr n} -> ConvTm G t u A ->
         ConvTm (extend G C) (wkExpr t) (wkExpr u) (wkExpr A)
  wkCv = rCv wkRen (wkRT {G = G} {C}) (wf-extend hC)
