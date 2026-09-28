{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.RussellReduction
--
-- Head reduction on Russell terms (as MIN.Syntax.Reduction):
--
--   app(A,B,λ(A',B',b),a)  ->  b[a]         (annotations are ignored)
--   M -> M'  ==>  app(A,B,M,N) -> app(A,B,M',N)
--
-- It is deterministic, and products and universes are head normal, so
-- a term reduces to at most one product and at most one universe.
------------------------------------------------------------------------

module ERTUU.RussellReduction where

open import ERTUU.Basic
open import ERTUU.RussellSyntax

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A A' : Expr n} {B B' b : Expr (suc n)} {a : Expr n} ->
    HeadRed1 (App A B (Lam A' B' b) a) (subst1 b a)
  headred-app : {n : Nat} {A : Expr n} {B : Expr (suc n)} {M M' N : Expr n} ->
    HeadRed1 M M' -> HeadRed1 (App A B M N) (App A B M' N)

data HeadRed : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-refl : {n : Nat} {M : Expr n} -> HeadRed M M
  headred-step : {n : Nat} {M N P : Expr n} ->
    HeadRed1 M N -> HeadRed N P -> HeadRed M P

HeadRed-trans : {n : Nat} {M N P : Expr n} ->
  HeadRed M N -> HeadRed N P -> HeadRed M P
HeadRed-trans headred-refl hr2 = hr2
HeadRed-trans (headred-step s hr1) hr2 = headred-step s (HeadRed-trans hr1 hr2)

HeadRed-App : {n : Nat} {A : Expr n} {B : Expr (suc n)} {M N P : Expr n} ->
  HeadRed M N -> HeadRed (App A B M P) (App A B N P)
HeadRed-App headred-refl = headred-refl
HeadRed-App (headred-step s hr) = headred-step (headred-app s) (HeadRed-App hr)

HeadRed1-det : {n : Nat} {M N P : Expr n} -> HeadRed1 M N -> HeadRed1 M P -> Eq N P
HeadRed1-det headred-beta headred-beta = refl
HeadRed1-det headred-beta (headred-app ())
HeadRed1-det (headred-app ()) headred-beta
HeadRed1-det (headred-app {A = A} {B = B} {N = N} s1) (headred-app s2) =
  Eq-cong (\ X -> App A B X N) (HeadRed1-det s1 s2)

-- Head normal forms: a term that head-reduces to itself only.
HNF : {n : Nat} -> Expr n -> Set
HNF {n} M = {N : Expr n} -> HeadRed1 M N -> Empty

HNF-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} -> HNF (Pi A B)
HNF-Pi ()

HNF-U : {n : Nat} -> HNF {n} U
HNF-U ()

HNF-Lam : {n : Nat} {A : Expr n} {B b : Expr (suc n)} -> HNF (Lam A B b)
HNF-Lam ()

-- A reduction from a head normal form is trivial.
HeadRed-HNF : {n : Nat} {M N : Expr n} -> HNF M -> HeadRed M N -> Eq M N
HeadRed-HNF h headred-refl = refl
HeadRed-HNF h (headred-step s _) = absurd (h s)

-- Confluence of head reduction towards a head normal form: any reduct
-- of M still reduces to the normal form M reaches.
HeadRed-strip : {n : Nat} {M M' Z : Expr n} -> HNF Z ->
  HeadRed M M' -> HeadRed M Z -> HeadRed M' Z
HeadRed-strip h headred-refl hr2 = hr2
HeadRed-strip h (headred-step s1 hr1) headred-refl = absurd (h s1)
HeadRed-strip h (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip h hr1
    (Eq-transport (\ x -> HeadRed x _) (Eq-sym (HeadRed1-det s1 s2)) hr2)

-- Two head normal forms reached from the same term are equal.
HeadRed-unique : {n : Nat} {M Z Z' : Expr n} -> HNF Z -> HNF Z' ->
  HeadRed M Z -> HeadRed M Z' -> Eq Z Z'
HeadRed-unique h h' hr1 hr2 = HeadRed-HNF h (HeadRed-strip h' hr1 hr2)

Pi-inj-Eq : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)}
  -> Eq (Pi A B) (Pi A' B') -> Pair (Eq A A') (Eq B B')
Pi-inj-Eq refl = mkSigma refl refl

HeadRed-unique-Pi : {n : Nat} {M A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed M (Pi A B) -> HeadRed M (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-unique-Pi hr1 hr2 = Pi-inj-Eq (HeadRed-unique HNF-Pi HNF-Pi hr1 hr2)

HeadRed-Pi-U : {n : Nat} {M A : Expr n} {B : Expr (suc n)} ->
  HeadRed M (Pi A B) -> HeadRed M U -> Empty
HeadRed-Pi-U hr1 hr2 = clash (HeadRed-unique HNF-Pi HNF-U hr1 hr2)
  where
    clash : {n : Nat} {A : Expr n} {B : Expr (suc n)} -> Eq (Pi A B) U -> Empty
    clash ()

HeadRed-strip-Pi : {n : Nat} {M M' A : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> HeadRed M (Pi A B) -> HeadRed M' (Pi A B)
HeadRed-strip-Pi = HeadRed-strip HNF-Pi

HeadRed-strip-U : {n : Nat} {M M' : Expr n} ->
  HeadRed M M' -> HeadRed M U -> HeadRed M' U
HeadRed-strip-U = HeadRed-strip HNF-U

------------------------------------------------------------------------
-- Head reduction commutes with renaming and substitution
------------------------------------------------------------------------

open import ERTUU.RussellMeta using (ren-subst1 ; subst-subst1)

HeadRed1-ren : {n m : Nat} (r : Ren n m) {M N : Expr n} ->
  HeadRed1 M N -> HeadRed1 (renExpr r M) (renExpr r N)
HeadRed1-ren r (headred-beta {A = A} {A' = A'} {B = B} {B' = B'} {b = b} {a = a}) =
  Eq-transport (\ X -> HeadRed1 (renExpr r (App A B (Lam A' B' b) a)) X)
    (Eq-sym (ren-subst1 r b a))
    (headred-beta {A = renExpr r A} {A' = renExpr r A'} {B = renExpr (liftRen r) B}
                  {B' = renExpr (liftRen r) B'} {b = renExpr (liftRen r) b} {a = renExpr r a})
HeadRed1-ren r (headred-app s) = headred-app (HeadRed1-ren r s)

HeadRed-ren : {n m : Nat} (r : Ren n m) {M N : Expr n} ->
  HeadRed M N -> HeadRed (renExpr r M) (renExpr r N)
HeadRed-ren r headred-refl = headred-refl
HeadRed-ren r (headred-step s hr) = headred-step (HeadRed1-ren r s) (HeadRed-ren r hr)

HeadRed1-subst : {h g : Nat} (sigma : Sub h g) {M N : Expr g} ->
  HeadRed1 M N -> HeadRed1 (substExpr sigma M) (substExpr sigma N)
HeadRed1-subst sigma (headred-beta {A = A} {A' = A'} {B = B} {B' = B'} {b = b} {a = a}) =
  Eq-transport (\ X -> HeadRed1 (substExpr sigma (App A B (Lam A' B' b) a)) X)
    (Eq-sym (subst-subst1 sigma b a))
    (headred-beta {A = substExpr sigma A} {A' = substExpr sigma A'}
                  {B = substExpr (liftSub sigma) B} {B' = substExpr (liftSub sigma) B'}
                  {b = substExpr (liftSub sigma) b} {a = substExpr sigma a})
HeadRed1-subst sigma (headred-app s) = headred-app (HeadRed1-subst sigma s)

HeadRed-subst : {h g : Nat} (sigma : Sub h g) {M N : Expr g} ->
  HeadRed M N -> HeadRed (substExpr sigma M) (substExpr sigma N)
HeadRed-subst sigma headred-refl = headred-refl
HeadRed-subst sigma (headred-step s hr) =
  headred-step (HeadRed1-subst sigma s) (HeadRed-subst sigma hr)

------------------------------------------------------------------------
-- Red: head reduction with a phantom context (as MIN.Syntax.Reduction)
------------------------------------------------------------------------

open import ERTUU.RussellTyping using (Ctx)

data Red {n : Nat} (G : Ctx n) (M N : Expr n) : Set where
  mkRed : HeadRed M N -> Red G M N

Red-hr : {n : Nat} {G : Ctx n} {M N : Expr n} -> Red G M N -> HeadRed M N
Red-hr (mkRed hr) = hr

Red-unique-Pi : {n : Nat} {G : Ctx n} {M A A' : Expr n} {B B' : Expr (suc n)} ->
  Red G M (Pi A B) -> Red G M (Pi A' B') -> Pair (Eq A A') (Eq B B')
Red-unique-Pi (mkRed r1) (mkRed r2) = HeadRed-unique-Pi r1 r2
