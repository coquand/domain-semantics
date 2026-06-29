{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Syntax.Reduction
--
-- Head reduction. Minimal version with only Pi and U.
-- Parallel version of Reduction.agda.
------------------------------------------------------------------------

module NAT.Syntax.Reduction where

import NAT.Domain.Basic as S
open S using (Nat ; suc ; Pair ; mkSigma ; Eq ; refl ; fst ; snd ; Empty ;
  Eq-sym ; Eq-transport ; Eq-cong)
open import NAT.Syntax.Raw using (Expr ; Var ; Pi ; App ; Lam ; U ; Y ;
  NatT ; Zero ; Suc ; Case ;
  wkExpr ; subst1 ;
  Sub ; substExpr ; subst1Sub ; liftSub ; wkRen ;
  Fin ; fzero ; fsuc ; Eq-trans ; Eq-cong2-Expr ; Eq-cong3 ;
  subst-ren ; subst-subst ; substExpr-ext)
open import NAT.Syntax.Typing using (Ctx)

------------------------------------------------------------------------
-- HeadRed1: single-step head reduction
------------------------------------------------------------------------

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
    HeadRed1 (App (Lam A M) N) (subst1 M N)
  headred-app : {n : Nat} {M1 M2 N : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (App M1 N) (App M2 N)
  -- Y g -> g (Y g)
  headred-Y : {n : Nat} {g : Expr n} ->
    HeadRed1 (Y g) (App g (Y g))
  -- caseNat 0 a b -> a
  headred-case-zero : {n : Nat} {a b : Expr n} ->
    HeadRed1 (Case Zero a b) a
  -- caseNat (S m) a b -> b m
  headred-case-suc : {n : Nat} {m a b : Expr n} ->
    HeadRed1 (Case (Suc m) a b) (App b m)
  -- reduce the scrutinee
  headred-case : {n : Nat} {M1 M2 a b : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (Case M1 a b) (Case M2 a b)

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

-- Scrutinee congruence for caseNat, lifted to the closure HeadRed.
HeadRed-Case : {n : Nat} {M1 M2 a b : Expr n} ->
  HeadRed M1 M2 -> HeadRed (Case M1 a b) (Case M2 a b)
HeadRed-Case headred-refl = headred-refl
HeadRed-Case (headred-step s hr) = headred-step (headred-case s) (HeadRed-Case hr)

------------------------------------------------------------------------
-- Normal form lemmas
------------------------------------------------------------------------

HeadRed1-not-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Pi A B) N -> Empty
HeadRed1-not-Pi ()

HeadRed1-not-Lam : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Lam A M) N -> Empty
HeadRed1-not-Lam ()

HeadRed1-not-Zero : {n : Nat} {N : Expr n} -> HeadRed1 Zero N -> Empty
HeadRed1-not-Zero ()

HeadRed1-not-Suc : {n : Nat} {m N : Expr n} -> HeadRed1 (Suc m) N -> Empty
HeadRed1-not-Suc ()

-- HeadRed1 is deterministic
HeadRed1-det : {n : Nat} {M N P : Expr n} ->
  HeadRed1 M N -> HeadRed1 M P -> Eq N P
HeadRed1-det headred-beta headred-beta = refl
HeadRed1-det headred-Y headred-Y = refl
HeadRed1-det headred-beta (headred-app s) with HeadRed1-not-Lam s
... | ()
HeadRed1-det (headred-app s) headred-beta with HeadRed1-not-Lam s
... | ()
HeadRed1-det (headred-app {N = N} s1) (headred-app s2) =
  Eq-cong2-Expr App (HeadRed1-det s1 s2) refl
HeadRed1-det headred-case-zero headred-case-zero = refl
HeadRed1-det headred-case-suc  headred-case-suc  = refl
HeadRed1-det headred-case-zero (headred-case s) with HeadRed1-not-Zero s
... | ()
HeadRed1-det headred-case-suc  (headred-case s) with HeadRed1-not-Suc s
... | ()
HeadRed1-det (headred-case s) headred-case-zero with HeadRed1-not-Zero s
... | ()
HeadRed1-det (headred-case s) headred-case-suc  with HeadRed1-not-Suc s
... | ()
HeadRed1-det (headred-case s1) (headred-case s2) =
  Eq-cong3 Case (HeadRed1-det s1 s2) refl refl

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

-- HeadRed from Suc to Suc must be reflexivity (Suc is WHNF)
HeadRed-Suc-refl : {n : Nat} {a b : Expr n} ->
  HeadRed (Suc a) (Suc b) -> Eq a b
HeadRed-Suc-refl headred-refl = refl
HeadRed-Suc-refl (headred-step s _) with HeadRed1-not-Suc s
... | ()

HeadRed-unique-Suc : {n : Nat} {M : Expr n} {a b : Expr n} ->
  HeadRed M (Suc a) -> HeadRed M (Suc b) -> Eq a b
HeadRed-unique-Suc headred-refl hr2 = HeadRed-Suc-refl hr2
HeadRed-unique-Suc (headred-step s1 _) headred-refl with HeadRed1-not-Suc s1
... | ()
HeadRed-unique-Suc (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Suc hr1
    (Eq-transport (\ x -> HeadRed x (Suc _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Pi : {n : Nat} {M M' : Expr n} {A : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> HeadRed M (Pi A B) -> HeadRed M' (Pi A B)
HeadRed-strip-Pi headred-refl hr2 = hr2
HeadRed-strip-Pi (headred-step s1 hr1) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-strip-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

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
substExpr-id (Y g)        = Eq-cong Y (substExpr-id g)
substExpr-id (App f a)    =
  Eq-cong2-Expr App (substExpr-id f) (substExpr-id a)
substExpr-id NatT         = refl
substExpr-id Zero         = refl
substExpr-id (Suc m)      = Eq-cong Suc (substExpr-id m)
substExpr-id (Case M a b) =
  Eq-cong3 Case (substExpr-id M) (substExpr-id a) (substExpr-id b)

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
