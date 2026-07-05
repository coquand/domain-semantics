{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Syntax.Reduction
--
-- Head reduction. Minimal version with only Pi and U.
-- Parallel version of Reduction.agda.
------------------------------------------------------------------------

module ID.Syntax.Reduction where

import ID.Domain.Basic as S
open S using (Nat ; suc ; Pair ; mkSigma ; Eq ; refl ; fst ; snd ; Empty ;
  Eq-sym ; Eq-transport ; Eq-cong)
open import ID.Syntax.Raw using (Expr ; Var ; Pi ; App ; Lam ; U ;
  Id ; Ref ; J ;
  wkExpr ; subst1 ;
  Sub ; substExpr ; subst1Sub ; liftSub ; wkRen ;
  Fin ; fzero ; fsuc ; Eq-trans ; Eq-cong2-Expr ; Eq-cong3-Expr ;
  subst-ren ; subst-subst ; substExpr-ext)
open import ID.Syntax.Typing using (Ctx)

------------------------------------------------------------------------
-- HeadRed1: single-step head reduction
------------------------------------------------------------------------

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
    HeadRed1 (App (Lam A M) N) (subst1 M N)
  headred-app : {n : Nat} {M1 M2 N : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (App M1 N) (App M2 N)
  -- based-J beta (ML original): J C d (Ref a) reduces to  App d a  (fires on a
  -- literal Ref; the base d is applied to the diagonal witness a).
  headred-J : {n : Nat} {C d a : Expr n} ->
    HeadRed1 (J C d (Ref a)) (App d a)
  -- congruence in the proof (scrutinee) position
  headred-J-scrut : {n : Nat} {C d p p' : Expr n} ->
    HeadRed1 p p' -> HeadRed1 (J C d p) (J C d p')

------------------------------------------------------------------------
-- HeadRed: reflexive-transitive closure
------------------------------------------------------------------------

data HeadRed : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-refl : {n : Nat} {M : Expr n} -> HeadRed M M
  headred-step : {n : Nat} {M N P : Expr n} ->
    HeadRed1 M N -> HeadRed N P -> HeadRed M P

HeadRed-trans : {n : Nat} {M N P : Expr n} ->
  HeadRed M N -> HeadRed N P -> HeadRed M P
HeadRed-trans headred-refl hr2 = hr2
HeadRed-trans (headred-step s hr1) hr2 = headred-step s (HeadRed-trans hr1 hr2)

HeadRed-App : {n : Nat} {M N P : Expr n} ->
  HeadRed M N -> HeadRed (App M P) (App N P)
HeadRed-App headred-refl = headred-refl
HeadRed-App (headred-step s hr) = headred-step (headred-app s) (HeadRed-App hr)

-- congruence of the RT-closure in the proof position of J
HeadRed-J : {n : Nat} {C d p p' : Expr n} ->
  HeadRed p p' -> HeadRed (J C d p) (J C d p')
HeadRed-J headred-refl = headred-refl
HeadRed-J (headred-step s hr) = headred-step (headred-J-scrut s) (HeadRed-J hr)

------------------------------------------------------------------------
-- Normal form lemmas
------------------------------------------------------------------------

HeadRed1-not-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Pi A B) N -> Empty
HeadRed1-not-Pi ()

HeadRed1-not-Lam : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Lam A M) N -> Empty
HeadRed1-not-Lam ()

-- HeadRed1 is deterministic
HeadRed1-det : {n : Nat} {M N P : Expr n} ->
  HeadRed1 M N -> HeadRed1 M P -> Eq N P
HeadRed1-det headred-beta headred-beta = refl
HeadRed1-det headred-beta (headred-app s) with HeadRed1-not-Lam s
... | ()
HeadRed1-det (headred-app s) headred-beta with HeadRed1-not-Lam s
... | ()
HeadRed1-det (headred-app {N = N} s1) (headred-app s2) =
  Eq-cong2-Expr App (HeadRed1-det s1 s2) refl
HeadRed1-det headred-J headred-J = refl
HeadRed1-det headred-J (headred-J-scrut ())
HeadRed1-det (headred-J-scrut ()) headred-J
HeadRed1-det (headred-J-scrut s1) (headred-J-scrut s2) =
  Eq-cong3-Expr J refl refl (HeadRed1-det s1 s2)

-- HeadRed from Pi to Pi must be reflexivity
HeadRed-Pi-refl : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed (Pi A B) (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-Pi-refl headred-refl = mkSigma refl refl
HeadRed-Pi-refl (headred-step s _) with HeadRed1-not-Pi s
... | ()

HeadRed-unique-Pi : {n : Nat} {M : Expr n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed M (Pi A B) -> HeadRed M (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-unique-Pi headred-refl hr2 = HeadRed-Pi-refl hr2
HeadRed-unique-Pi (headred-step s1 _) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-unique-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

-- Id is a value: no HeadRed1 step, and HeadRed Id->Id is reflexivity.
HeadRed1-not-Id : {n : Nat} {A a b : Expr n} {N : Expr n} ->
  HeadRed1 (Id A a b) N -> Empty
HeadRed1-not-Id ()

HeadRed-Id-refl : {n : Nat} {A A' a a' b b' : Expr n} ->
  HeadRed (Id A a b) (Id A' a' b') -> Pair (Eq A A') (Pair (Eq a a') (Eq b b'))
HeadRed-Id-refl headred-refl = mkSigma refl (mkSigma refl refl)
HeadRed-Id-refl (headred-step s _) with HeadRed1-not-Id s
... | ()

HeadRed-unique-Id : {n : Nat} {M : Expr n} {A A' a a' b b' : Expr n} ->
  HeadRed M (Id A a b) -> HeadRed M (Id A' a' b') ->
  Pair (Eq A A') (Pair (Eq a a') (Eq b b'))
HeadRed-unique-Id headred-refl hr2 = HeadRed-Id-refl hr2
HeadRed-unique-Id (headred-step s1 _) headred-refl with HeadRed1-not-Id s1
... | ()
HeadRed-unique-Id (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Id hr1
    (Eq-transport (\ x -> HeadRed x (Id _ _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Pi : {n : Nat} {M M' : Expr n} {A : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> HeadRed M (Pi A B) -> HeadRed M' (Pi A B)
HeadRed-strip-Pi headred-refl hr2 = hr2
HeadRed-strip-Pi (headred-step s1 hr1) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-strip-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Id : {n : Nat} {M M' : Expr n} {A a b : Expr n} ->
  HeadRed M M' -> HeadRed M (Id A a b) -> HeadRed M' (Id A a b)
HeadRed-strip-Id headred-refl hr2 = hr2
HeadRed-strip-Id (headred-step s1 hr1) headred-refl with HeadRed1-not-Id s1
... | ()
HeadRed-strip-Id (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Id hr1
    (Eq-transport (\ x -> HeadRed x (Id _ _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

-- Ref is a value: no HeadRed1 step out of it.  (`headred-J` reduces a J-redex,
-- whose head is J, not Ref, so this stays valid after J reduction is added.)
HeadRed1-not-Ref : {n : Nat} {a N : Expr n} -> HeadRed1 (Ref a) N -> Empty
HeadRed1-not-Ref ()

HeadRed-strip-Ref : {n : Nat} {M M' a : Expr n} ->
  HeadRed M M' -> HeadRed M (Ref a) -> HeadRed M' (Ref a)
HeadRed-strip-Ref headred-refl hr2 = hr2
HeadRed-strip-Ref (headred-step s1 hr1) headred-refl with HeadRed1-not-Ref s1
... | ()
HeadRed-strip-Ref (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Ref hr1
    (Eq-transport (\ x -> HeadRed x (Ref _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

------------------------------------------------------------------------
-- Red: head reduction with phantom context/type indices
------------------------------------------------------------------------

data Red : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set where
  mkRed : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    HeadRed M N -> Red G M N A

Red-refl : {n : Nat} {G : Ctx n} {M A : Expr n} -> Red G M M A
Red-refl = mkRed headred-refl

Red-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red G M N A -> HeadRed M N
Red-hr (mkRed hr) = hr

------------------------------------------------------------------------
-- Identity substitution
------------------------------------------------------------------------

idSub : {n : Nat} -> Sub n n
idSub i = Var i

substExpr-id : {n : Nat} (M : Expr n) -> Eq (substExpr idSub M) M
substExpr-id (Var i)      = refl
substExpr-id U            = refl
substExpr-id (Pi A B)     =
  Eq-cong2-Expr Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
substExpr-id (Lam A M)    =
  Eq-cong2-Expr Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> refl ; (fsuc i) -> refl }) M)
              (substExpr-id M))
substExpr-id (App f a)    =
  Eq-cong2-Expr App (substExpr-id f) (substExpr-id a)
substExpr-id (Id A a b)   =
  Eq-cong3-Expr Id (substExpr-id A) (substExpr-id a) (substExpr-id b)
substExpr-id (Ref a)      = Eq-cong Ref (substExpr-id a)
substExpr-id (J C d p)    =
  Eq-cong3-Expr J (substExpr-id C) (substExpr-id d) (substExpr-id p)

------------------------------------------------------------------------
-- HeadRed commutes with substitution
------------------------------------------------------------------------

subst-subst1-comm : {n m : Nat} (sigma : Sub m n)
  (M : Expr (suc n)) (N : Expr n) ->
  Eq (subst1 (substExpr (liftSub sigma) M) (substExpr sigma N))
     (substExpr sigma (subst1 M N))
subst-subst1-comm sigma M N =
  Eq-trans (subst-subst (subst1Sub (substExpr sigma N)) (liftSub sigma) M)
    (Eq-trans (substExpr-ext _ _ ext M)
      (Eq-sym (subst-subst sigma (subst1Sub N) M)))
  where
    ext : (i : Fin _) ->
      Eq (substExpr (subst1Sub (substExpr sigma N)) (liftSub sigma i))
         (substExpr sigma (subst1Sub N i))
    ext fzero    = refl
    ext (fsuc i) =
      Eq-trans (subst-ren (subst1Sub (substExpr sigma N)) wkRen (sigma i))
        (Eq-trans (substExpr-ext _ idSub (\ j -> refl) (sigma i))
          (substExpr-id (sigma i)))
