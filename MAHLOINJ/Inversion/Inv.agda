{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Inversion/Inv.agda
--
-- Inversion of typing (plan Lemma 18) for every term former, relative
-- to the hypotheses InjHyp (only the no-confusion facts for U(f,g) are
-- used here).  Each lemma is by induction on the derivation, through
-- the non-syntax-directed rules ty-conv and ty-sub.
--
-- For formers whose type may be a universe (Var, App, Fst, Snd, Rec),
-- subsumption cannot be refuted: the result says the type is the
-- canonical one, OR it is V and the canonical one is a code  (UpTo).
------------------------------------------------------------------------

open import MAHLOINJ.Inversion.Hyp

module MAHLOINJ.Inversion.Inv (H : InjHyp) where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.Presup
open InjHyp H

------------------------------------------------------------------------
-- Up to subsumption
------------------------------------------------------------------------

data UpTo {n : Num} (G : Ctx n) (C X : Expr n) : Set where
  upEq  : TyEq G C X -> UpTo G C X
  upSub : (f g : Expr n) -> TyEq G C V -> TyEq G X (Ucode f g) -> UpTo G C X

upConv : {n : Num} {G : Ctx n} {C C' X : Expr n} -> UpTo G C X -> TyEq G C C' -> UpTo G C' X
upConv (upEq e) q = upEq (tyeq-trans (tyeq-sym q) e)
upConv (upSub f g e1 e2) q = upSub f g (tyeq-trans (tyeq-sym q) e1) e2

upToV : {n : Num} {G : Ctx n} {f g X : Expr n} -> WfCtx G -> UpTo G (Ucode f g) X -> UpTo G V X
upToV {f = f} {g} w (upEq e) = upSub f g (tyeq-refl (isty-V w)) (tyeq-sym e)
upToV w (upSub f' g' e1 e2) = upSub f' g' (tyeq-refl (isty-V w)) e2

-- an element of a universe is an element of V
toV : {n : Num} {G : Ctx n} {u A : Expr n} -> Univ u -> HasType G A u -> HasType G A V
toV (univ-V refl) h = h
toV (univ-U f g refl) h = ty-sub h

------------------------------------------------------------------------
-- V has no type
------------------------------------------------------------------------

noV : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G V C -> Empty
noV (ty-conv h q) = noV h
noV (ty-sub h) = noV h

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

invVar : {n : Num} {G : Ctx n} {i : Fin n} {C : Expr n} ->
         HasType G (Var i) C -> UpTo G C (lookup G i)
invVar (ty-var {i = i} w) = upEq (tyeq-refl (lookupTy w i))
invVar (ty-conv h q) = upConv (invVar h) q
invVar (ty-sub h) = upToV (wfTm h) (invVar h)

------------------------------------------------------------------------
-- Pi
------------------------------------------------------------------------

record LamInv {n : Num} (G : Ctx n) (A : Expr n) (t : Expr (suc n)) (C : Expr n) : Set where
  constructor laminv
  field
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType (extend G A) t B
    eq : TyEq G C (PiB A B)

invLam : {n : Num} {G : Ctx n} {A C : Expr n} {t : Expr (suc n)} ->
         HasType G (Lam A t) C -> LamInv G A t C
invLam (ty-Lam hA hB ht) = laminv _ hA hB ht (tyeq-refl (isty-Pi hA hB))
invLam (ty-conv h q) = laminv B hA hB ht (tyeq-trans (tyeq-sym q) eq)
  where open LamInv (invLam h)
invLam (ty-sub h) = Empty-elim (U-Pi (LamInv.eq (invLam h)))

record AppInv {n : Num} (G : Ctx n) (t a C : Expr n) : Set where
  constructor appinv
  field
    A  : Expr n
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType G t (PiB A B)
    ha : HasType G a A
    up : UpTo G C (subst1 B a)

invApp : {n : Num} {G : Ctx n} {t a C : Expr n} -> HasType G (App t a) C -> AppInv G t a C
invApp (ty-App hA hB ht ha) =
  appinv _ _ hA hB ht ha (upEq (tyeq-refl (s1Ty (wfTy hA) ha hB)))
invApp (ty-conv h q) = appinv A B hA hB ht ha (upConv up q)
  where open AppInv (invApp h)
invApp (ty-sub h) = appinv A B hA hB ht ha (upToV (wfTm h) up)
  where open AppInv (invApp h)

------------------------------------------------------------------------
-- Sigma
------------------------------------------------------------------------

record PairInv {n : Num} (G : Ctx n) (t u C : Expr n) : Set where
  constructor pairinv
  field
    A  : Expr n
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType G t A
    hu : HasType G u (subst1 B t)
    eq : TyEq G C (SigmaB A B)

invPair : {n : Num} {G : Ctx n} {t u C : Expr n} -> HasType G (Pair t u) C -> PairInv G t u C
invPair (ty-Pair hA hB ht hu) = pairinv _ _ hA hB ht hu (tyeq-refl (isty-Sigma hA hB))
invPair (ty-conv h q) = pairinv A B hA hB ht hu (tyeq-trans (tyeq-sym q) eq)
  where open PairInv (invPair h)
invPair (ty-sub h) = Empty-elim (U-Sig (PairInv.eq (invPair h)))

record FstInv {n : Num} (G : Ctx n) (t C : Expr n) : Set where
  constructor fstinv
  field
    A  : Expr n
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType G t (SigmaB A B)
    up : UpTo G C A

invFst : {n : Num} {G : Ctx n} {t C : Expr n} -> HasType G (Fst t) C -> FstInv G t C
invFst (ty-Fst hA hB ht) = fstinv _ _ hA hB ht (upEq (tyeq-refl hA))
invFst (ty-conv h q) = fstinv A B hA hB ht (upConv up q)
  where open FstInv (invFst h)
invFst (ty-sub h) = fstinv A B hA hB ht (upToV (wfTm h) up)
  where open FstInv (invFst h)

record SndInv {n : Num} (G : Ctx n) (t C : Expr n) : Set where
  constructor sndinv
  field
    A  : Expr n
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType G t (SigmaB A B)
    up : UpTo G C (subst1 B (Fst t))

invSnd : {n : Num} {G : Ctx n} {t C : Expr n} -> HasType G (Snd t) C -> SndInv G t C
invSnd (ty-Snd hA hB ht) =
  sndinv _ _ hA hB ht (upEq (tyeq-refl (s1Ty (wfTy hA) (ty-Fst hA hB ht) hB)))
invSnd (ty-conv h q) = sndinv A B hA hB ht (upConv up q)
  where open SndInv (invSnd h)
invSnd (ty-sub h) = sndinv A B hA hB ht (upToV (wfTm h) up)
  where open SndInv (invSnd h)

------------------------------------------------------------------------
-- Nat
------------------------------------------------------------------------

invZero : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G Zero C -> TyEq G C Nat
invZero (ty-Zero w) = tyeq-refl (NatTy w)
invZero (ty-conv h q) = tyeq-trans (tyeq-sym q) (invZero h)
invZero (ty-sub h) = Empty-elim (U-Nat (invZero h))

invSuc : {n : Num} {G : Ctx n} {k C : Expr n} -> HasType G (Suc k) C ->
         HasType G k Nat * TyEq G C Nat
invSuc (ty-Suc h) = h , tyeq-refl (NatTy (wfTm h))
invSuc (ty-conv h q) = fst (invSuc h) , tyeq-trans (tyeq-sym q) (snd (invSuc h))
invSuc (ty-sub h) = Empty-elim (U-Nat (snd (invSuc h)))

record RecInv {n : Num} (G : Ctx n) (F z s k C : Expr n) : Set where
  constructor recinv
  field
    C0 : Expr (suc n)
    eF : Eq F (Lam Nat C0)
    hC : IsType (extend G Nat) C0
    hz : HasType G z (subst1 C0 Zero)
    hs : HasType G s (RecStep C0)
    hk : HasType G k Nat
    up : UpTo G C (subst1 C0 k)

invRec : {n : Num} {G : Ctx n} {F z s k C : Expr n} ->
         HasType G (Rec F z s k) C -> RecInv G F z s k C
invRec (ty-Rec hC hz hs hk) =
  recinv _ refl hC hz hs hk (upEq (tyeq-refl (s1Ty (wfTm hk) hk hC)))
invRec (ty-conv h q) = recinv C0 eF hC hz hs hk (upConv up q)
  where open RecInv (invRec h)
invRec (ty-sub h) = recinv C0 eF hC hz hs hk (upToV (wfTm h) up)
  where open RecInv (invRec h)

------------------------------------------------------------------------
-- Type formers as elements of a universe
------------------------------------------------------------------------

-- Pi A F : C  (F = \x:A.B)
record PiInv {n : Num} (G : Ctx n) (A F C : Expr n) : Set where
  constructor piinv
  field
    B  : Expr (suc n)
    eF : Eq F (Lam A B)
    u  : Expr n
    un : Univ u
    hA : HasType G A u
    hB : HasType (extend G A) B (wkExpr u)
    eq : TyEq G C u

invPi : {n : Num} {G : Ctx n} {A F C : Expr n} -> HasType G (Pi A F) C -> PiInv G A F C
invPi (ty-Pi un hA hB) = piinv _ refl _ un hA hB (tyeq-refl (pTm hA))
invPi (ty-conv h q) = piinv B eF u un hA hB (tyeq-trans (tyeq-sym q) eq)
  where open PiInv (invPi h)
invPi (ty-sub h) =
  let r = invPi h ; un = PiInv.un r in
  piinv (PiInv.B r) (PiInv.eF r) V (univ-V refl) (toV un (PiInv.hA r))
        (toV (renUniv wkRen un) (PiInv.hB r)) (tyeq-refl (isty-V (wfTm h)))

invSigma : {n : Num} {G : Ctx n} {A F C : Expr n} -> HasType G (Sigma A F) C -> PiInv G A F C
invSigma (ty-Sigma un hA hB) = piinv _ refl _ un hA hB (tyeq-refl (pTm hA))
invSigma (ty-conv h q) = piinv B eF u un hA hB (tyeq-trans (tyeq-sym q) eq)
  where open PiInv (invSigma h)
invSigma (ty-sub h) =
  let r = invSigma h ; un = PiInv.un r in
  piinv (PiInv.B r) (PiInv.eF r) V (univ-V refl) (toV un (PiInv.hA r))
        (toV (renUniv wkRen un) (PiInv.hB r)) (tyeq-refl (isty-V (wfTm h)))

invNat : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G Nat C ->
         TyEq G C V +
         Sg (Expr n) (\ f -> Sg (Expr n) (\ g ->
           HasType G (Ucode f g) V * TyEq G C (Ucode f g)))
invNat (ty-Nat-V w) = inl (tyeq-refl (isty-V w))
invNat (ty-Nat-U {f = f} {g} h) = inr (f , (g , (h , tyeq-refl (isty-el h))))
invNat (ty-conv h q) = t' (invNat h)
  where
    t' : _ -> _
    t' (inl e) = inl (tyeq-trans (tyeq-sym q) e)
    t' (inr (f , (g , (hU , e)))) = inr (f , (g , (hU , tyeq-trans (tyeq-sym q) e)))
invNat (ty-sub h) = inl (tyeq-refl (isty-V (wfTm h)))

invUcode : {n : Num} {G : Ctx n} {f g C : Expr n} -> HasType G (Ucode f g) C ->
           HasType G f OpF * (HasType G g (OpG f) * TyEq G C V)
invUcode (ty-Ucode hf hg) = hf , (hg , tyeq-refl (isty-V (wfTm hf)))
invUcode (ty-conv h q) =
  let r = invUcode h in fst r , (fst (snd r) , tyeq-trans (tyeq-sym q) (snd (snd r)))
invUcode (ty-sub h) =
  fst (invUcode h) , (fst (snd (invUcode h)) , tyeq-refl (isty-V (wfTm h)))

-- fhat f g A F : C  (F = \x:A.B);  C is the code, or V
record FhatInv {n : Num} (G : Ctx n) (f g A F C : Expr n) : Set where
  constructor fhatinv
  field
    B  : Expr (suc n)
    eF : Eq F (Lam A B)
    hf : HasType G f OpF
    hg : HasType G g (OpG f)
    hA : HasType G A (Ucode f g)
    hB : HasType (extend G A) B (wkExpr (Ucode f g))
    ty : TyEq G C (Ucode f g) + TyEq G C V

invFhat : {n : Num} {G : Ctx n} {f g A F C : Expr n} ->
          HasType G (Fhat f g A F) C -> FhatInv G f g A F C
invFhat (ty-Fhat hf hg hA hB) = fhatinv _ refl hf hg hA hB (inl (tyeq-refl (pTm hA)))
invFhat (ty-conv h q) = fhatinv B eF hf hg hA hB (t' ty)
  where
    open FhatInv (invFhat h)
    t' : _ -> _
    t' (inl e) = inl (tyeq-trans (tyeq-sym q) e)
    t' (inr e) = inr (tyeq-trans (tyeq-sym q) e)
invFhat (ty-sub h) = fhatinv B eF hf hg hA hB (inr (tyeq-refl (isty-V (wfTm h))))
  where open FhatInv (invFhat h)

record GhatInv {n : Num} (G : Ctx n) (f g A F c C : Expr n) : Set where
  constructor ghatinv
  field
    B  : Expr (suc n)
    eF : Eq F (Lam A B)
    hf : HasType G f OpF
    hg : HasType G g (OpG f)
    hA : HasType G A (Ucode f g)
    hB : HasType (extend G A) B (wkExpr (Ucode f g))
    hc : HasType G c (Fhat f g A (Lam A B))
    ty : TyEq G C (Ucode f g) + TyEq G C V

invGhat : {n : Num} {G : Ctx n} {f g A F c C : Expr n} ->
          HasType G (Ghat f g A F c) C -> GhatInv G f g A F c C
invGhat (ty-Ghat hf hg hA hB hc) = ghatinv _ refl hf hg hA hB hc (inl (tyeq-refl (pTm hA)))
invGhat (ty-conv h q) = ghatinv B eF hf hg hA hB hc (t' ty)
  where
    open GhatInv (invGhat h)
    t' : _ -> _
    t' (inl e) = inl (tyeq-trans (tyeq-sym q) e)
    t' (inr e) = inr (tyeq-trans (tyeq-sym q) e)
invGhat (ty-sub h) = ghatinv B eF hf hg hA hB hc (inr (tyeq-refl (isty-V (wfTm h))))
  where open GhatInv (invGhat h)
