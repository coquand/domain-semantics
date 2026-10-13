{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Res.agda
--
-- Inference results: a finite list of types of t, every one a type of t
-- (sound), and covering every type of t up to TyEq (complete) -- or
-- covering a given predicate P.  Saturation under U(f,g) <= V, unions,
-- and binding over a list of candidate types.
------------------------------------------------------------------------

open import MAHLOTC.Base

module MAHLOTC.Res (H : TCHyp) where

open import MAHLO.Syntax
open import MAHLO.Typing
open TCHyp H
open import MAHLOINJ.Inversion.Inv inj
open import MAHLOINJ.Syntax.Presup using (pTm ; pTE)

record LRes {n : Num} (G : Ctx n) (t : Expr n) (P : Expr n -> Set) : Set where
  constructor lres
  field
    L     : List (Expr n)
    sound : All (HasType G t) L
    cmp   : (C : Expr n) -> P C -> Any (TyEq G C) L
open LRes public

Res : {n : Num} -> Ctx n -> Expr n -> Set
Res G t = LRes G t (HasType G t)

module _ {n : Num} {G : Ctx n} {t : Expr n} where

  nilRes : {P : Expr n -> Set} -> ((C : Expr n) -> P C -> Empty) -> LRes G t P
  nilRes k = lres [] unit (\ C p -> Empty-elim (k C p))

  weakRes : {P Q : Expr n -> Set} -> ((C : Expr n) -> Q C -> P C) -> LRes G t P -> LRes G t Q
  weakRes f (lres L s c) = lres L s (\ C q -> c C (f C q))

  orRes : {P Q : Expr n -> Set} -> LRes G t P -> LRes G t Q -> LRes G t (\ C -> P C + Q C)
  orRes (lres L1 s1 c1) (lres L2 s2 c2) =
    lres (L1 ++ L2) (all-++ L1 L2 s1 s2)
         (\ { C (inl p) -> any-l L1 L2 (c1 C p) ; C (inr q) -> any-r L1 L2 (c2 C q) })

  -- one principal type X, complete up to subsumption (as for inversion)
  sat : (X : Expr n) -> HasType G t X -> LRes G t (\ C -> UpTo G C X)
  sat X hX = h (decU (pTm hX))
    where
      h : Dec (Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G X (Ucode f g)))) ->
          LRes G t (\ C -> UpTo G C X)
      h (yes (f , (g , e))) =
        lres (X :: V :: []) (hX , (ty-sub (ty-conv hX e) , unit))
             (\ { C (upEq e1) -> here e1 ; C (upSub f' g' eCV eU) -> there (here eCV) })
      h (no k) =
        lres (X :: []) (hX , unit)
             (\ { C (upEq e1) -> here e1 ; C (upSub f' g' eCV eU) -> Empty-elim (k (f' , (g' , eU))) })

  -- binding over a list of candidates
  bindRes : {Q : Expr n -> Set} {R : Expr n -> Expr n -> Set} (Xs : List (Expr n)) -> All Q Xs ->
            ((X : Expr n) -> Q X -> LRes G t (R X)) ->
            LRes G t (\ C -> Any (\ X -> R X C) Xs)
  bindRes [] u f = nilRes (\ C ())
  bindRes (X :: Xs) (q , qs) f =
    weakRes (\ { C (here r) -> inl r ; C (there a) -> inr a }) (orRes (f X q) (bindRes Xs qs f))

-- moving the second argument of UpTo along TyEq
upConvR : {n : Num} {G : Ctx n} {C Y Y' : Expr n} -> UpTo G C Y -> TyEq G Y Y' -> UpTo G C Y'
upConvR (upEq e) q = upEq (tyeq-trans e q)
upConvR (upSub f g e1 e2) q = upSub f g e1 (tyeq-trans (tyeq-sym q) e2)

any-map : {A : Set} {P Q : A -> Set} -> ((x : A) -> P x -> Q x) -> {xs : List A} -> Any P xs -> Any Q xs
any-map f (here p) = here (f _ p)
any-map f (there a) = there (any-map f a)

-- an element witnessing Any, with its All-property
anyAll : {A : Set} {P Q : A -> Set} {xs : List A} -> Any P xs -> All Q xs -> Sg A (\ x -> P x * Q x)
anyAll (here p) (q , qs) = _ , (p , q)
anyAll (there a) (q , qs) = anyAll a qs

-- checking against a type, from an inference result
checkRes : {n : Num} {G : Ctx n} {t C : Expr n} -> IsType G C -> Res G t -> Dec (HasType G t C)
checkRes hC (lres L s c) = h (decAny L s (\ X hX -> decTyEq hC (pTm hX)))
  where
    h : Dec (Any (TyEq _ _) L) -> Dec (HasType _ _ _)
    h (yes a) = let x = anyAll a s in yes (ty-conv (snd (snd x)) (tyeq-sym (fst (snd x))))
    h (no k) = no (\ ht -> k (c _ ht))
