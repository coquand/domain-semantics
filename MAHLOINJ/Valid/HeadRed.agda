{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/HeadRed.agda
--
-- Untyped weak-head reduction used by the logical relation:
-- beta, pi (projections of pairs), iota (rec), and delta (fhat/ghat to
-- the applications of f/g), with head congruences.  Deterministic.
-- (delta is a reduction of TYPES only: the relation never extracts a
-- conversion at U(f,g) from a reduction.)
------------------------------------------------------------------------

module MAHLOINJ.Valid.HeadRed where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax

data HR {n : Num} : Expr n -> Expr n -> Set where
  hr-beta     : {A a : Expr n} {t : Expr (suc n)} -> HR (App (Lam A t) a) (subst1 t a)
  hr-app      : {t t' a : Expr n} -> HR t t' -> HR (App t a) (App t' a)
  hr-fst-pair : {t u : Expr n} -> HR (Fst (Pair t u)) t
  hr-snd-pair : {t u : Expr n} -> HR (Snd (Pair t u)) u
  hr-fst      : {t t' : Expr n} -> HR t t' -> HR (Fst t) (Fst t')
  hr-snd      : {t t' : Expr n} -> HR t t' -> HR (Snd t) (Snd t')
  hr-rec-zero : {F z s : Expr n} -> HR (Rec F z s Zero) z
  hr-rec-suc  : {F z s k : Expr n} -> HR (Rec F z s (Suc k)) (App (App s k) (Rec F z s k))
  hr-rec      : {F z s k k' : Expr n} -> HR k k' -> HR (Rec F z s k) (Rec F z s k')
  hr-fhat     : {f g A F : Expr n} -> HR (Fhat f g A F) (App (App f A) F)
  hr-ghat     : {f g A F c : Expr n} -> HR (Ghat f g A F c) (App (App (App g A) F) c)

data HRs {n : Num} : Expr n -> Expr n -> Set where
  hrs-refl : {t : Expr n} -> HRs t t
  hrs-step : {t t' t'' : Expr n} -> HR t t' -> HRs t' t'' -> HRs t t''

HRs-trans : {n : Num} {t t' t'' : Expr n} -> HRs t t' -> HRs t' t'' -> HRs t t''
HRs-trans hrs-refl q = q
HRs-trans (hrs-step r p) q = hrs-step r (HRs-trans p q)

HRs-app : {n : Num} {t t' a : Expr n} -> HRs t t' -> HRs (App t a) (App t' a)
HRs-app hrs-refl = hrs-refl
HRs-app (hrs-step r p) = hrs-step (hr-app r) (HRs-app p)

HRs-fst : {n : Num} {t t' : Expr n} -> HRs t t' -> HRs (Fst t) (Fst t')
HRs-fst hrs-refl = hrs-refl
HRs-fst (hrs-step r p) = hrs-step (hr-fst r) (HRs-fst p)

HRs-snd : {n : Num} {t t' : Expr n} -> HRs t t' -> HRs (Snd t) (Snd t')
HRs-snd hrs-refl = hrs-refl
HRs-snd (hrs-step r p) = hrs-step (hr-snd r) (HRs-snd p)

HRs-rec : {n : Num} {F z s k k' : Expr n} -> HRs k k' -> HRs (Rec F z s k) (Rec F z s k')
HRs-rec hrs-refl = hrs-refl
HRs-rec (hrs-step r p) = hrs-step (hr-rec r) (HRs-rec p)

------------------------------------------------------------------------
-- Determinism
------------------------------------------------------------------------

-- terms that do not reduce
NoRed : {n : Num} -> Expr n -> Set
NoRed t = {t' : _} -> HR t t' -> Empty

nored-Lam : {n : Num} {A : Expr n} {t : Expr (suc n)} -> NoRed (Lam A t)
nored-Lam ()
nored-Pair : {n : Num} {t u : Expr n} -> NoRed (Pair t u)
nored-Pair ()
nored-Zero : {n : Num} -> NoRed (Zero {n})
nored-Zero ()
nored-Suc : {n : Num} {t : Expr n} -> NoRed (Suc t)
nored-Suc ()
nored-Pi : {n : Num} {A F : Expr n} -> NoRed (Pi A F)
nored-Pi ()
nored-Sigma : {n : Num} {A F : Expr n} -> NoRed (Sigma A F)
nored-Sigma ()
nored-Nat : {n : Num} -> NoRed (Nat {n})
nored-Nat ()
nored-V : {n : Num} -> NoRed (V {n})
nored-V ()
nored-Ucode : {n : Num} {f g : Expr n} -> NoRed (Ucode f g)
nored-Ucode ()

HR-det : {n : Num} {t t1 t2 : Expr n} -> HR t t1 -> HR t t2 -> Eq t1 t2
HR-det hr-beta hr-beta = refl
HR-det hr-beta (hr-app ())
HR-det (hr-app ()) hr-beta
HR-det (hr-app r1) (hr-app r2) = Eq-cong (\ x -> App x _) (HR-det r1 r2)
HR-det hr-fst-pair hr-fst-pair = refl
HR-det hr-fst-pair (hr-fst ())
HR-det (hr-fst ()) hr-fst-pair
HR-det (hr-fst r1) (hr-fst r2) = Eq-cong Fst (HR-det r1 r2)
HR-det hr-snd-pair hr-snd-pair = refl
HR-det hr-snd-pair (hr-snd ())
HR-det (hr-snd ()) hr-snd-pair
HR-det (hr-snd r1) (hr-snd r2) = Eq-cong Snd (HR-det r1 r2)
HR-det hr-rec-zero hr-rec-zero = refl
HR-det hr-rec-zero (hr-rec ())
HR-det hr-rec-suc hr-rec-suc = refl
HR-det hr-rec-suc (hr-rec ())
HR-det (hr-rec ()) hr-rec-zero
HR-det (hr-rec ()) hr-rec-suc
HR-det (hr-rec r1) (hr-rec r2) = Eq-cong (Rec _ _ _) (HR-det r1 r2)
HR-det hr-fhat hr-fhat = refl
HR-det hr-ghat hr-ghat = refl

-- two reductions of the same term to non-reducing terms coincide
HRs-det : {n : Num} {t u v : Expr n} -> HRs t u -> HRs t v -> NoRed u -> NoRed v -> Eq u v
HRs-det hrs-refl hrs-refl nu nv = refl
HRs-det hrs-refl (hrs-step r q) nu nv = Empty-elim (nu r)
HRs-det (hrs-step r p) hrs-refl nu nv = Empty-elim (nv r)
HRs-det (hrs-step r1 p) (hrs-step r2 q) nu nv =
  HRs-det p (transport (\ x -> HRs x _) (Eq-sym (HR-det r1 r2)) q) nu nv

-- a reduction sequence from t can be continued from any reduct on the way
HRs-from-step : {n : Num} {t t1 u : Expr n} -> HR t t1 -> HRs t u -> NoRed u -> HRs t1 u
HRs-from-step r hrs-refl nu = Empty-elim (nu r)
HRs-from-step r (hrs-step r' p) nu = transport (\ x -> HRs x _) (HR-det r' r) p

------------------------------------------------------------------------
-- Shapes reached by the relation, and their injectivity
------------------------------------------------------------------------

-- selectors (total, defaulting elsewhere) for injectivity without K
dom1 : {n : Num} -> Expr n -> Expr n
dom1 (Var _) = Nat
dom1 (Lam _ _) = Nat
dom1 (App _ _) = Nat
dom1 (Pi A F) = A
dom1 (Sigma A F) = A
dom1 (Pair _ _) = Nat
dom1 (Fst _) = Nat
dom1 (Snd _) = Nat
dom1 Nat = Nat
dom1 Zero = Nat
dom1 (Suc _) = Nat
dom1 (Rec _ _ _ _) = Nat
dom1 V = Nat
dom1 (Ucode _ _) = Nat
dom1 (Fhat _ _ _ _) = Nat
dom1 (Ghat _ _ _ _ _) = Nat

fam1 : {n : Num} -> Expr n -> Expr n
fam1 (Var _) = Nat
fam1 (Lam _ _) = Nat
fam1 (App _ _) = Nat
fam1 (Pi A F) = F
fam1 (Sigma A F) = F
fam1 (Pair _ _) = Nat
fam1 (Fst _) = Nat
fam1 (Snd _) = Nat
fam1 Nat = Nat
fam1 Zero = Nat
fam1 (Suc _) = Nat
fam1 (Rec _ _ _ _) = Nat
fam1 V = Nat
fam1 (Ucode _ _) = Nat
fam1 (Fhat _ _ _ _) = Nat
fam1 (Ghat _ _ _ _ _) = Nat

lamb1 : {n : Num} -> Expr n -> Expr (suc n)
lamb1 (Var _) = Nat
lamb1 (Lam A B) = B
lamb1 (App _ _) = Nat
lamb1 (Pi _ _) = Nat
lamb1 (Sigma _ _) = Nat
lamb1 (Pair _ _) = Nat
lamb1 (Fst _) = Nat
lamb1 (Snd _) = Nat
lamb1 Nat = Nat
lamb1 Zero = Nat
lamb1 (Suc _) = Nat
lamb1 (Rec _ _ _ _) = Nat
lamb1 V = Nat
lamb1 (Ucode _ _) = Nat
lamb1 (Fhat _ _ _ _) = Nat
lamb1 (Ghat _ _ _ _ _) = Nat

cod1 : {n : Num} -> Expr n -> Expr (suc n)
cod1 t = lamb1 (fam1 t)

pred1 : {n : Num} -> Expr n -> Expr n
pred1 (Var _) = Nat
pred1 (Lam _ _) = Nat
pred1 (App _ _) = Nat
pred1 (Pi _ _) = Nat
pred1 (Sigma _ _) = Nat
pred1 (Pair _ _) = Nat
pred1 (Fst _) = Nat
pred1 (Snd _) = Nat
pred1 Nat = Nat
pred1 Zero = Nat
pred1 (Suc t) = t
pred1 (Rec _ _ _ _) = Nat
pred1 V = Nat
pred1 (Ucode _ _) = Nat
pred1 (Fhat _ _ _ _) = Nat
pred1 (Ghat _ _ _ _ _) = Nat

PiB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} -> Eq (PiB A B) (PiB A' B') -> Eq A A' * Eq B B'
PiB-inj e = Eq-cong dom1 e , Eq-cong cod1 e

SigmaB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} -> Eq (SigmaB A B) (SigmaB A' B') -> Eq A A' * Eq B B'
SigmaB-inj e = Eq-cong dom1 e , Eq-cong cod1 e

Suc-inj : {n : Num} {t t' : Expr n} -> Eq (Suc t) (Suc t') -> Eq t t'
Suc-inj e = Eq-cong pred1 e
