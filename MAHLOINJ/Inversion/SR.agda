{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Inversion/SR.agda
--
-- Subject reduction for weak-head beta / pi / iota (NOT delta, which
-- fails at U(f,g)), relative to InjHyp.  Stated in the strong form
--   G |- t : C,  t ->wh t'   ==>   G |- t = t' : C
-- by induction on the typing derivation; inversion (Lam, Pair, Suc)
-- and Pi/Sigma-injectivity are used only at the redexes.
------------------------------------------------------------------------

open import MAHLOINJ.Inversion.Hyp

module MAHLOINJ.Inversion.SR (H : InjHyp) where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup
open import MAHLOINJ.Inversion.Inv H
open InjHyp H

------------------------------------------------------------------------
-- Weak-head reduction: beta, pi, iota, in head position
------------------------------------------------------------------------

data WhRed {n : Num} : Expr n -> Expr n -> Set where
  wh-beta     : {A a : Expr n} {t : Expr (suc n)} -> WhRed (App (Lam A t) a) (subst1 t a)
  wh-app      : {t t' a : Expr n} -> WhRed t t' -> WhRed (App t a) (App t' a)
  wh-fst-pair : {t u : Expr n} -> WhRed (Fst (Pair t u)) t
  wh-snd-pair : {t u : Expr n} -> WhRed (Snd (Pair t u)) u
  wh-fst      : {t t' : Expr n} -> WhRed t t' -> WhRed (Fst t) (Fst t')
  wh-snd      : {t t' : Expr n} -> WhRed t t' -> WhRed (Snd t) (Snd t')
  wh-rec-zero : {F z s : Expr n} -> WhRed (Rec F z s Zero) z
  wh-rec-suc  : {F z s k : Expr n} -> WhRed (Rec F z s (Suc k)) (App (App s k) (Rec F z s k))
  wh-rec      : {F z s k k' : Expr n} -> WhRed k k' -> WhRed (Rec F z s k) (Rec F z s k')

------------------------------------------------------------------------
-- Subject reduction
------------------------------------------------------------------------

sr : {n : Num} {G : Ctx n} {t t' C : Expr n} -> HasType G t C -> WhRed t t' -> ConvTm G t t' C
sr (ty-conv h q) r = conv-conv (sr h r) q
sr (ty-sub h) r = conv-sub (sr h r)
-- beta
sr (ty-App {a = a} {B} hA hB ht ha) wh-beta =
  conv-conv (conv-beta hA0 hB0 ht0 (ty-conv ha (fst pi)))
            (tyeq-sym (s1TE (wfTy hA) ha (snd pi)))
  where
    open LamInv (invLam ht) renaming (B to B0 ; hA to hA0 ; hB to hB0 ; ht to ht0 ; eq to e0)
    pi = Pi-inj e0
sr (ty-App hA hB ht ha) (wh-app r) = conv-App hA hB (sr ht r) (conv-refl ha)
-- pi
sr (ty-Fst hA hB ht) wh-fst-pair =
  conv-conv (conv-fst-beta hA0 hB0 ht0 hu0) (tyeq-sym (fst si))
  where
    open PairInv (invPair ht) renaming (A to A0 ; B to B0 ; hA to hA0 ; hB to hB0 ;
                                        ht to ht0 ; hu to hu0 ; eq to e0)
    si = Sig-inj e0
sr (ty-Fst hA hB ht) (wh-fst r) = conv-Fst hA hB (sr ht r)
sr (ty-Snd hA hB ht) wh-snd-pair =
  conv-conv (conv-snd-beta hA0 hB0 ht0 hu0) (tyeq-trans e1 e2)
  where
    open PairInv (invPair ht) renaming (A to A0 ; B to B0 ; hA to hA0 ; hB to hB0 ;
                                        ht to ht0 ; hu to hu0 ; eq to e0)
    si = Sig-inj e0
    w = wfTy hA
    ht1 = ty-conv ht0 (tyeq-sym (fst si))
    e1 = tyeq-sym (s1TE w ht1 (snd si))
    cf = conv-sym (conv-conv (conv-fst-beta hA0 hB0 ht0 hu0) (tyeq-sym (fst si)))
    e2 = s1fTy w hA ht1 (ty-Fst hA hB ht) cf hB
sr (ty-Snd hA hB ht) (wh-snd r) = conv-Snd hA hB (sr ht r)
-- iota
sr (ty-Rec hC hz hs hk) wh-rec-zero = conv-rec-zero hC hz hs
sr (ty-Rec hC hz hs hk) wh-rec-suc = conv-rec-suc hC hz hs (fst (invSuc hk))
sr (ty-Rec hC hz hs hk) (wh-rec r) =
  conv-Rec hC hC (tyeq-refl hC) (conv-refl hz) (conv-refl hs) (sr hk r)
-- no other subject reduces
sr (ty-var w) ()
sr (ty-Pi u hA hB) ()
sr (ty-Sigma u hA hB) ()
sr (ty-Nat-V w) ()
sr (ty-Nat-U h) ()
sr (ty-Ucode hf hg) ()
sr (ty-Fhat hf hg hA hB) ()
sr (ty-Ghat hf hg hA hB hc) ()
sr (ty-Lam hA hB ht) ()
sr (ty-Pair hA hB ht hu) ()
sr (ty-Zero w) ()
sr (ty-Suc h) ()

-- the reduct is well typed
sr-ty : {n : Num} {G : Ctx n} {t t' C : Expr n} -> HasType G t C -> WhRed t t' -> HasType G t' C
sr-ty h r = snd (pCv (sr h r))
