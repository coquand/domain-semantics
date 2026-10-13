{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/Eval.agda
--
-- Soundness of weak-head evaluation (plan Lemma "evaluation away from
-- subuniverses", in constructive form).
--
-- A step of HR on a well-typed term is either a WhRed step (beta, pi,
-- iota, and their head congruences), which is sound at every type by
-- subject reduction, or a delta step AT THE TOP of a term fhat/ghat.
-- A delta step below an elimination is impossible for well-typed terms:
-- fhat/ghat have a universe as type, and a universe is not a Pi, a
-- Sigma or Nat (U-Pi, U-Sig, U-Nat, V-Pi, V-Sig, V-Nat).
--
-- A top delta step is a conversion at V only.  At an arbitrary type C,
-- inversion of the fhat/ghat typing gives  C = U(f,g)  or  C = V : in
-- the second case the step is a conversion at C; in the first, the
-- evaluation lemma returns the evidence  C = U(f,g)  instead.  This is
-- the constructive replacement of the case split "C is / is not a
-- subuniverse" of the plan: it is decided by derivation data.
------------------------------------------------------------------------

module MAHLOINJ.Algo.Eval where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Presup using (pCv)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Final using (injHyp ; U-Pi ; U-Sig ; U-Nat)
open import MAHLOINJ.Inversion.Inv injHyp
open import MAHLOINJ.Inversion.SR injHyp using (WhRed ; sr ; wh-beta ; wh-app ; wh-fst-pair ; wh-snd-pair ; wh-fst ; wh-snd
  ; wh-rec-zero ; wh-rec-suc ; wh-rec)
open import MAHLOINJ.Algo.NoConfV

-- top-level delta steps
data DTop {n : Num} : Expr n -> Expr n -> Set where
  dfhat : {f g A F : Expr n} -> DTop (Fhat f g A F) (App (App f A) F)
  dghat : {f g A F c : Expr n} -> DTop (Ghat f g A F c) (App (App (App g A) F) c)

private
  -- a universe-typed term is not a function, a pair or a numeral
  univTy : {n : Num} {G : Ctx n} {t t1 C : Expr n} -> HasType G t C -> DTop t t1 ->
    Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g))) + TyEq G C V
  univTy h dfhat = go (FhatInv.ty (invFhat h))
    where
      go : _ -> _
      go (inl e) = inl (_ , (_ , e))
      go (inr e) = inr e
  univTy h dghat = go (GhatInv.ty (invGhat h))
    where
      go : _ -> _
      go (inl e) = inl (_ , (_ , e))
      go (inr e) = inr e

  noDPi : {n : Num} {G : Ctx n} {t t1 A : Expr n} {B : Expr (suc n)} -> HasType G t (PiB A B) -> DTop t t1 -> Empty
  noDPi h d = go (univTy h d)
    where
      go : _ -> Empty
      go (inl (f , (g , e))) = U-Pi (tyeq-sym e)
      go (inr e) = V-Pi (tyeq-sym e)

  noDSig : {n : Num} {G : Ctx n} {t t1 A : Expr n} {B : Expr (suc n)} -> HasType G t (SigmaB A B) -> DTop t t1 -> Empty
  noDSig h d = go (univTy h d)
    where
      go : _ -> Empty
      go (inl (f , (g , e))) = U-Sig (tyeq-sym e)
      go (inr e) = V-Sig (tyeq-sym e)

  noDNat : {n : Num} {G : Ctx n} {t t1 : Expr n} -> HasType G t Nat -> DTop t t1 -> Empty
  noDNat h d = go (univTy h d)
    where
      go : _ -> Empty
      go (inl (f , (g , e))) = U-Nat (tyeq-sym e)
      go (inr e) = V-Nat (tyeq-sym e)

-- a step on a well-typed term
hrSplit : {n : Num} {G : Ctx n} {t t1 C : Expr n} -> HasType G t C -> HR t t1 -> WhRed t t1 + DTop t t1
hrSplit h hr-beta = inl wh-beta
hrSplit h (hr-app r) = go (hrSplit (AppInv.ht (invApp h)) r)
  where
    go : _ -> _
    go (inl w) = inl (wh-app w)
    go (inr d) = Empty-elim (noDPi (AppInv.ht (invApp h)) d)
hrSplit h hr-fst-pair = inl wh-fst-pair
hrSplit h hr-snd-pair = inl wh-snd-pair
hrSplit h (hr-fst r) = go (hrSplit (FstInv.ht (invFst h)) r)
  where
    go : _ -> _
    go (inl w) = inl (wh-fst w)
    go (inr d) = Empty-elim (noDSig (FstInv.ht (invFst h)) d)
hrSplit h (hr-snd r) = go (hrSplit (SndInv.ht (invSnd h)) r)
  where
    go : _ -> _
    go (inl w) = inl (wh-snd w)
    go (inr d) = Empty-elim (noDSig (SndInv.ht (invSnd h)) d)
hrSplit h hr-rec-zero = inl wh-rec-zero
hrSplit h hr-rec-suc = inl wh-rec-suc
hrSplit h (hr-rec r) = go (hrSplit (RecInv.hk (invRec h)) r)
  where
    go : _ -> _
    go (inl w) = inl (wh-rec w)
    go (inr d) = Empty-elim (noDNat (RecInv.hk (invRec h)) d)
hrSplit h hr-fhat = inr dfhat
hrSplit h hr-ghat = inr dghat

-- a top delta step is a conversion at V
deltaV : {n : Num} {G : Ctx n} {t t1 C : Expr n} -> HasType G t C -> DTop t t1 -> ConvTm G t t1 V
deltaV {G = G} h (dfhat {f} {g} {A} {F}) =
  transport (\ X -> ConvTm G (Fhat f g A X) (App (App f A) X) V) (Eq-sym eF) (conv-delta-f hf hg hA hB)
  where open FhatInv (invFhat h)
deltaV {G = G} h (dghat {f} {g} {A} {F} {c}) =
  transport (\ X -> ConvTm G (Ghat f g A X c) (App (App (App g A) X) c) V) (Eq-sym eF)
    (conv-delta-g hf hg hA hB hc)
  where open GhatInv (invGhat h)

-- evaluation at V
evalV : {n : Num} {G : Ctx n} {t w : Expr n} -> HasType G t V -> HRs t w -> ConvTm G t w V
evalV h hrs-refl = conv-refl h
evalV h (hrs-step r rs) = go (hrSplit h r)
  where
    go : _ -> _
    go (inl wr) = let c = sr h wr in conv-trans c (evalV (snd (pCv c)) rs)
    go (inr d) = let c = deltaV h d in conv-trans c (evalV (snd (pCv c)) rs)

-- evaluation at an arbitrary type: a conversion, or the type is a code
UEv : {n : Num} -> Ctx n -> Expr n -> Set
UEv {n} G C = Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g)))

evalC : {n : Num} {G : Ctx n} {t w C : Expr n} -> HasType G t C -> HRs t w -> ConvTm G t w C + UEv G C
evalC h hrs-refl = inl (conv-refl h)
evalC {G = G} {t = t} {C = C} h (hrs-step {t' = t1} r rs) = go (hrSplit h r)
  where
    cont : ConvTm G t t1 C -> _
    cont c = goR (evalC (snd (pCv c)) rs)
      where
        goR : _ -> _
        goR (inl c') = inl (conv-trans c c')
        goR (inr u) = inr u
    go : _ -> _
    go (inl wr) = cont (sr h wr)
    go (inr d) = goU (univTy h d)
      where
        goU : _ -> _
        goU (inl u) = inr u
        goU (inr e) = cont (conv-conv (deltaV h d) (tyeq-sym e))

-- evaluation of types
private
  noRedHRs : {n : Num} {t w : Expr n} -> NoRed t -> HRs t w -> Eq t w
  noRedHRs nr hrs-refl = refl
  noRedHRs nr (hrs-step r rs) = Empty-elim (nr r)

tyRed : {n : Num} {G : Ctx n} {A w : Expr n} -> IsType G A -> HRs A w -> TyEq G A w
tyRed (isty-el h) r = tyeq-el (evalV h r)
tyRed {G = G} iA@(isty-V w) r = transport (TyEq G V) (noRedHRs nored-V r) (tyeq-refl iA)
tyRed {G = G} iA@(isty-Pi hA hB) r = transport (TyEq G _) (noRedHRs nored-Pi r) (tyeq-refl iA)
tyRed {G = G} iA@(isty-Sigma hA hB) r = transport (TyEq G _) (noRedHRs nored-Sigma r) (tyeq-refl iA)
