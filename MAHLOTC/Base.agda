{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Base.agda
--
-- Decisions, finite lists, decidable syntactic equality of Expr
-- (generated), and the hypotheses TCHyp of the type checker.
------------------------------------------------------------------------

module MAHLOTC.Base where

open import MAHLO.Basic renaming (Sigma to Sg) public
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Inversion.Hyp public

data Dec (P : Set) : Set where
  yes : P -> Dec P
  no  : (P -> Empty) -> Dec P

data Unit : Set where
  unit : Unit

mapDec : {P Q : Set} -> (P -> Q) -> (Q -> P) -> Dec P -> Dec Q
mapDec f g (yes p) = yes (f p)
mapDec f g (no k) = no (\ q -> k (g q))

both : {P Q : Set} -> Dec P -> Dec Q -> Dec (P * Q)
both (yes p) (yes q) = yes (p , q)
both (yes p) (no k) = no (\ r -> k (snd r))
both (no k) d = no (\ r -> k (fst r))

decOr : {P Q : Set} -> Dec P -> Dec Q -> Dec (P + Q)
decOr (yes p) d = yes (inl p)
decOr (no k) (yes q) = yes (inr q)
decOr (no k) (no k') = no (\ { (inl p) -> k p ; (inr q) -> k' q })

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Any {A : Set} (P : A -> Set) : List A -> Set where
  here  : {x : A} {xs : List A} -> P x -> Any P (x :: xs)
  there : {x : A} {xs : List A} -> Any P xs -> Any P (x :: xs)

All : {A : Set} -> (A -> Set) -> List A -> Set
All P [] = Unit
All P (x :: xs) = P x * All P xs

any-l : {A : Set} {P : A -> Set} (xs ys : List A) -> Any P xs -> Any P (xs ++ ys)
any-l (x :: xs) ys (here p) = here p
any-l (x :: xs) ys (there a) = there (any-l xs ys a)

any-r : {A : Set} {P : A -> Set} (xs ys : List A) -> Any P ys -> Any P (xs ++ ys)
any-r [] ys a = a
any-r (x :: xs) ys a = there (any-r xs ys a)

all-++ : {A : Set} {P : A -> Set} (xs ys : List A) -> All P xs -> All P ys -> All P (xs ++ ys)
all-++ [] ys p q = q
all-++ (x :: xs) ys (p , ps) q = p , all-++ xs ys ps q

-- deciding an existential over a list, given decisions on its elements
decAny : {A : Set} {P Q : A -> Set} (xs : List A) -> All Q xs ->
         ((x : A) -> Q x -> Dec (P x)) -> Dec (Any P xs)
decAny [] u d = no (\ ())
decAny (x :: xs) (q , qs) d = h (d x q) (decAny xs qs d)
  where
    h : Dec _ -> Dec (Any _ xs) -> Dec (Any _ (x :: xs))
    h (yes p) r = yes (here p)
    h (no k) (yes a) = yes (there a)
    h (no k) (no k') = no (\ { (here p) -> k p ; (there a) -> k' a })

------------------------------------------------------------------------
-- Decidable equality of Expr
------------------------------------------------------------------------

decFin : {n : Num} (i j : Fin n) -> Dec (Eq i j)
decFin fzero fzero = yes refl
decFin fzero (fsuc j) = no (\ ())
decFin (fsuc i) fzero = no (\ ())
decFin (fsuc i) (fsuc j) = mapDec (\ { refl -> refl }) (\ { refl -> refl }) (decFin i j)

decExpr : {n : Num} (a b : Expr n) -> Dec (Eq a b)
decExpr (Var x0) (Var x0_) = mapDec (\ { refl -> refl }) (\ { refl -> refl }) ((decFin x0 x0_))
decExpr (Var x0) (Lam x0_ x1_) = no (\ ())
decExpr (Var x0) (App x0_ x1_) = no (\ ())
decExpr (Var x0) (Pi x0_ x1_) = no (\ ())
decExpr (Var x0) (Sigma x0_ x1_) = no (\ ())
decExpr (Var x0) (Pair x0_ x1_) = no (\ ())
decExpr (Var x0) (Fst x0_) = no (\ ())
decExpr (Var x0) (Snd x0_) = no (\ ())
decExpr (Var x0) Nat = no (\ ())
decExpr (Var x0) Zero = no (\ ())
decExpr (Var x0) (Suc x0_) = no (\ ())
decExpr (Var x0) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Var x0) V = no (\ ())
decExpr (Var x0) (Ucode x0_ x1_) = no (\ ())
decExpr (Var x0) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Var x0) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Lam x0 x1) (Var x0_) = no (\ ())
decExpr (Lam x0 x1) (Lam x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (Lam x0 x1) (App x0_ x1_) = no (\ ())
decExpr (Lam x0 x1) (Pi x0_ x1_) = no (\ ())
decExpr (Lam x0 x1) (Sigma x0_ x1_) = no (\ ())
decExpr (Lam x0 x1) (Pair x0_ x1_) = no (\ ())
decExpr (Lam x0 x1) (Fst x0_) = no (\ ())
decExpr (Lam x0 x1) (Snd x0_) = no (\ ())
decExpr (Lam x0 x1) Nat = no (\ ())
decExpr (Lam x0 x1) Zero = no (\ ())
decExpr (Lam x0 x1) (Suc x0_) = no (\ ())
decExpr (Lam x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Lam x0 x1) V = no (\ ())
decExpr (Lam x0 x1) (Ucode x0_ x1_) = no (\ ())
decExpr (Lam x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Lam x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (App x0 x1) (Var x0_) = no (\ ())
decExpr (App x0 x1) (Lam x0_ x1_) = no (\ ())
decExpr (App x0 x1) (App x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (App x0 x1) (Pi x0_ x1_) = no (\ ())
decExpr (App x0 x1) (Sigma x0_ x1_) = no (\ ())
decExpr (App x0 x1) (Pair x0_ x1_) = no (\ ())
decExpr (App x0 x1) (Fst x0_) = no (\ ())
decExpr (App x0 x1) (Snd x0_) = no (\ ())
decExpr (App x0 x1) Nat = no (\ ())
decExpr (App x0 x1) Zero = no (\ ())
decExpr (App x0 x1) (Suc x0_) = no (\ ())
decExpr (App x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (App x0 x1) V = no (\ ())
decExpr (App x0 x1) (Ucode x0_ x1_) = no (\ ())
decExpr (App x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (App x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Pi x0 x1) (Var x0_) = no (\ ())
decExpr (Pi x0 x1) (Lam x0_ x1_) = no (\ ())
decExpr (Pi x0 x1) (App x0_ x1_) = no (\ ())
decExpr (Pi x0 x1) (Pi x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (Pi x0 x1) (Sigma x0_ x1_) = no (\ ())
decExpr (Pi x0 x1) (Pair x0_ x1_) = no (\ ())
decExpr (Pi x0 x1) (Fst x0_) = no (\ ())
decExpr (Pi x0 x1) (Snd x0_) = no (\ ())
decExpr (Pi x0 x1) Nat = no (\ ())
decExpr (Pi x0 x1) Zero = no (\ ())
decExpr (Pi x0 x1) (Suc x0_) = no (\ ())
decExpr (Pi x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Pi x0 x1) V = no (\ ())
decExpr (Pi x0 x1) (Ucode x0_ x1_) = no (\ ())
decExpr (Pi x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Pi x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Sigma x0 x1) (Var x0_) = no (\ ())
decExpr (Sigma x0 x1) (Lam x0_ x1_) = no (\ ())
decExpr (Sigma x0 x1) (App x0_ x1_) = no (\ ())
decExpr (Sigma x0 x1) (Pi x0_ x1_) = no (\ ())
decExpr (Sigma x0 x1) (Sigma x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (Sigma x0 x1) (Pair x0_ x1_) = no (\ ())
decExpr (Sigma x0 x1) (Fst x0_) = no (\ ())
decExpr (Sigma x0 x1) (Snd x0_) = no (\ ())
decExpr (Sigma x0 x1) Nat = no (\ ())
decExpr (Sigma x0 x1) Zero = no (\ ())
decExpr (Sigma x0 x1) (Suc x0_) = no (\ ())
decExpr (Sigma x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Sigma x0 x1) V = no (\ ())
decExpr (Sigma x0 x1) (Ucode x0_ x1_) = no (\ ())
decExpr (Sigma x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Sigma x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Pair x0 x1) (Var x0_) = no (\ ())
decExpr (Pair x0 x1) (Lam x0_ x1_) = no (\ ())
decExpr (Pair x0 x1) (App x0_ x1_) = no (\ ())
decExpr (Pair x0 x1) (Pi x0_ x1_) = no (\ ())
decExpr (Pair x0 x1) (Sigma x0_ x1_) = no (\ ())
decExpr (Pair x0 x1) (Pair x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (Pair x0 x1) (Fst x0_) = no (\ ())
decExpr (Pair x0 x1) (Snd x0_) = no (\ ())
decExpr (Pair x0 x1) Nat = no (\ ())
decExpr (Pair x0 x1) Zero = no (\ ())
decExpr (Pair x0 x1) (Suc x0_) = no (\ ())
decExpr (Pair x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Pair x0 x1) V = no (\ ())
decExpr (Pair x0 x1) (Ucode x0_ x1_) = no (\ ())
decExpr (Pair x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Pair x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Fst x0) (Var x0_) = no (\ ())
decExpr (Fst x0) (Lam x0_ x1_) = no (\ ())
decExpr (Fst x0) (App x0_ x1_) = no (\ ())
decExpr (Fst x0) (Pi x0_ x1_) = no (\ ())
decExpr (Fst x0) (Sigma x0_ x1_) = no (\ ())
decExpr (Fst x0) (Pair x0_ x1_) = no (\ ())
decExpr (Fst x0) (Fst x0_) = mapDec (\ { refl -> refl }) (\ { refl -> refl }) ((decExpr x0 x0_))
decExpr (Fst x0) (Snd x0_) = no (\ ())
decExpr (Fst x0) Nat = no (\ ())
decExpr (Fst x0) Zero = no (\ ())
decExpr (Fst x0) (Suc x0_) = no (\ ())
decExpr (Fst x0) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Fst x0) V = no (\ ())
decExpr (Fst x0) (Ucode x0_ x1_) = no (\ ())
decExpr (Fst x0) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Fst x0) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Snd x0) (Var x0_) = no (\ ())
decExpr (Snd x0) (Lam x0_ x1_) = no (\ ())
decExpr (Snd x0) (App x0_ x1_) = no (\ ())
decExpr (Snd x0) (Pi x0_ x1_) = no (\ ())
decExpr (Snd x0) (Sigma x0_ x1_) = no (\ ())
decExpr (Snd x0) (Pair x0_ x1_) = no (\ ())
decExpr (Snd x0) (Fst x0_) = no (\ ())
decExpr (Snd x0) (Snd x0_) = mapDec (\ { refl -> refl }) (\ { refl -> refl }) ((decExpr x0 x0_))
decExpr (Snd x0) Nat = no (\ ())
decExpr (Snd x0) Zero = no (\ ())
decExpr (Snd x0) (Suc x0_) = no (\ ())
decExpr (Snd x0) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Snd x0) V = no (\ ())
decExpr (Snd x0) (Ucode x0_ x1_) = no (\ ())
decExpr (Snd x0) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Snd x0) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr Nat (Var x0_) = no (\ ())
decExpr Nat (Lam x0_ x1_) = no (\ ())
decExpr Nat (App x0_ x1_) = no (\ ())
decExpr Nat (Pi x0_ x1_) = no (\ ())
decExpr Nat (Sigma x0_ x1_) = no (\ ())
decExpr Nat (Pair x0_ x1_) = no (\ ())
decExpr Nat (Fst x0_) = no (\ ())
decExpr Nat (Snd x0_) = no (\ ())
decExpr Nat Nat = yes refl
decExpr Nat Zero = no (\ ())
decExpr Nat (Suc x0_) = no (\ ())
decExpr Nat (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr Nat V = no (\ ())
decExpr Nat (Ucode x0_ x1_) = no (\ ())
decExpr Nat (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr Nat (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr Zero (Var x0_) = no (\ ())
decExpr Zero (Lam x0_ x1_) = no (\ ())
decExpr Zero (App x0_ x1_) = no (\ ())
decExpr Zero (Pi x0_ x1_) = no (\ ())
decExpr Zero (Sigma x0_ x1_) = no (\ ())
decExpr Zero (Pair x0_ x1_) = no (\ ())
decExpr Zero (Fst x0_) = no (\ ())
decExpr Zero (Snd x0_) = no (\ ())
decExpr Zero Nat = no (\ ())
decExpr Zero Zero = yes refl
decExpr Zero (Suc x0_) = no (\ ())
decExpr Zero (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr Zero V = no (\ ())
decExpr Zero (Ucode x0_ x1_) = no (\ ())
decExpr Zero (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr Zero (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Suc x0) (Var x0_) = no (\ ())
decExpr (Suc x0) (Lam x0_ x1_) = no (\ ())
decExpr (Suc x0) (App x0_ x1_) = no (\ ())
decExpr (Suc x0) (Pi x0_ x1_) = no (\ ())
decExpr (Suc x0) (Sigma x0_ x1_) = no (\ ())
decExpr (Suc x0) (Pair x0_ x1_) = no (\ ())
decExpr (Suc x0) (Fst x0_) = no (\ ())
decExpr (Suc x0) (Snd x0_) = no (\ ())
decExpr (Suc x0) Nat = no (\ ())
decExpr (Suc x0) Zero = no (\ ())
decExpr (Suc x0) (Suc x0_) = mapDec (\ { refl -> refl }) (\ { refl -> refl }) ((decExpr x0 x0_))
decExpr (Suc x0) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Suc x0) V = no (\ ())
decExpr (Suc x0) (Ucode x0_ x1_) = no (\ ())
decExpr (Suc x0) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Suc x0) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Var x0_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Lam x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (App x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Pi x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Sigma x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Pair x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Fst x0_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Snd x0_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) Nat = no (\ ())
decExpr (Rec x0 x1 x2 x3) Zero = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Suc x0_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Rec x0_ x1_ x2_ x3_) = mapDec (\ { (refl , (refl , (refl , refl))) -> refl }) (\ { refl -> (refl , (refl , (refl , refl))) }) (both (decExpr x0 x0_) (both (decExpr x1 x1_) (both (decExpr x2 x2_) (decExpr x3 x3_))))
decExpr (Rec x0 x1 x2 x3) V = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Ucode x0_ x1_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Rec x0 x1 x2 x3) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr V (Var x0_) = no (\ ())
decExpr V (Lam x0_ x1_) = no (\ ())
decExpr V (App x0_ x1_) = no (\ ())
decExpr V (Pi x0_ x1_) = no (\ ())
decExpr V (Sigma x0_ x1_) = no (\ ())
decExpr V (Pair x0_ x1_) = no (\ ())
decExpr V (Fst x0_) = no (\ ())
decExpr V (Snd x0_) = no (\ ())
decExpr V Nat = no (\ ())
decExpr V Zero = no (\ ())
decExpr V (Suc x0_) = no (\ ())
decExpr V (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr V V = yes refl
decExpr V (Ucode x0_ x1_) = no (\ ())
decExpr V (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr V (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Ucode x0 x1) (Var x0_) = no (\ ())
decExpr (Ucode x0 x1) (Lam x0_ x1_) = no (\ ())
decExpr (Ucode x0 x1) (App x0_ x1_) = no (\ ())
decExpr (Ucode x0 x1) (Pi x0_ x1_) = no (\ ())
decExpr (Ucode x0 x1) (Sigma x0_ x1_) = no (\ ())
decExpr (Ucode x0 x1) (Pair x0_ x1_) = no (\ ())
decExpr (Ucode x0 x1) (Fst x0_) = no (\ ())
decExpr (Ucode x0 x1) (Snd x0_) = no (\ ())
decExpr (Ucode x0 x1) Nat = no (\ ())
decExpr (Ucode x0 x1) Zero = no (\ ())
decExpr (Ucode x0 x1) (Suc x0_) = no (\ ())
decExpr (Ucode x0 x1) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Ucode x0 x1) V = no (\ ())
decExpr (Ucode x0 x1) (Ucode x0_ x1_) = mapDec (\ { (refl , refl) -> refl }) (\ { refl -> (refl , refl) }) (both (decExpr x0 x0_) (decExpr x1 x1_))
decExpr (Ucode x0 x1) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Ucode x0 x1) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Var x0_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Lam x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (App x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Pi x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Sigma x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Pair x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Fst x0_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Snd x0_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) Nat = no (\ ())
decExpr (Fhat x0 x1 x2 x3) Zero = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Suc x0_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) V = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Ucode x0_ x1_) = no (\ ())
decExpr (Fhat x0 x1 x2 x3) (Fhat x0_ x1_ x2_ x3_) = mapDec (\ { (refl , (refl , (refl , refl))) -> refl }) (\ { refl -> (refl , (refl , (refl , refl))) }) (both (decExpr x0 x0_) (both (decExpr x1 x1_) (both (decExpr x2 x2_) (decExpr x3 x3_))))
decExpr (Fhat x0 x1 x2 x3) (Ghat x0_ x1_ x2_ x3_ x4_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Var x0_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Lam x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (App x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Pi x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Sigma x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Pair x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Fst x0_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Snd x0_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) Nat = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) Zero = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Suc x0_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Rec x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) V = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Ucode x0_ x1_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Fhat x0_ x1_ x2_ x3_) = no (\ ())
decExpr (Ghat x0 x1 x2 x3 x4) (Ghat x0_ x1_ x2_ x3_ x4_) = mapDec (\ { (refl , (refl , (refl , (refl , refl)))) -> refl }) (\ { refl -> (refl , (refl , (refl , (refl , refl)))) }) (both (decExpr x0 x0_) (both (decExpr x1 x1_) (both (decExpr x2 x2_) (both (decExpr x3 x3_) (decExpr x4 x4_)))))

------------------------------------------------------------------------
-- The hypotheses: decidable type equality and type head views
-- (to be inhabited by the decidable conversion of domain-6c)
------------------------------------------------------------------------

record TCHyp : Set where
  field
    inj     : InjHyp
    decTyEq : {n : Num} {G : Ctx n} {A A' : Expr n} -> IsType G A -> IsType G A' ->
              Dec (TyEq G A A')
    decPi   : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C ->
              Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G C (PiB A B))))
    decSig  : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C ->
              Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G C (SigmaB A B))))
    decU    : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C ->
              Dec (Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g))))

