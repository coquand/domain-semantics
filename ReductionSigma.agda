{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ReductionSigma.agda
--
-- Head reduction extended with Sigma types.
-- Parallel version of Reduction.agda.
--
-- New reduction rules:
--   Fst (MkPair M N) → M
--   Snd (MkPair M N) → N
--   Congruence: Fst M → Fst M', Snd M → Snd M' under head reduction
------------------------------------------------------------------------

module ReductionSigma where

import BasicSigma as S
open S using (Nat ; suc ; Pair ; mkSigma ; Eq ; refl ; fst ; snd ; Empty ;
  Eq-sym ; Eq-transport)
open import RawSyntaxSigma using (Expr ; Var ; Pi ; App ; Lam ; U ; Prop ;
  Sigma ; MkPair ; Fst ; Snd ;
  wkExpr ; subst1 ;
  Sub ; substExpr ; subst1Sub ; liftSub ; wkRen ;
  Fin ; fzero ; fsuc ; Eq-trans ; Eq-cong2-Expr ;
  subst-ren ; subst-subst ; substExpr-ext)
open import TypingRulesSigma using (Ctx)

------------------------------------------------------------------------
-- HeadRed1: single-step head reduction
------------------------------------------------------------------------

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
    HeadRed1 (App (Lam A M) N) (subst1 M N)
  headred-app : {n : Nat} {M1 M2 N : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (App M1 N) (App M2 N)
  headred-beta-fst : {n : Nat} {M N : Expr n} ->
    HeadRed1 (Fst (MkPair M N)) M
  headred-beta-snd : {n : Nat} {M N : Expr n} ->
    HeadRed1 (Snd (MkPair M N)) N
  headred-fst : {n : Nat} {M1 M2 : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (Fst M1) (Fst M2)
  headred-snd : {n : Nat} {M1 M2 : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (Snd M1) (Snd M2)

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

HeadRed-Fst : {n : Nat} {M N : Expr n} ->
  HeadRed M N -> HeadRed (Fst M) (Fst N)
HeadRed-Fst headred-refl = headred-refl
HeadRed-Fst (headred-step s hr) = headred-step (headred-fst s) (HeadRed-Fst hr)

HeadRed-Snd : {n : Nat} {M N : Expr n} ->
  HeadRed M N -> HeadRed (Snd M) (Snd N)
HeadRed-Snd headred-refl = headred-refl
HeadRed-Snd (headred-step s hr) = headred-step (headred-snd s) (HeadRed-Snd hr)

------------------------------------------------------------------------
-- Normal form lemmas
------------------------------------------------------------------------

HeadRed1-not-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Pi A B) N -> Empty
HeadRed1-not-Pi ()

HeadRed1-not-Lam : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Lam A M) N -> Empty
HeadRed1-not-Lam ()

HeadRed1-not-Sigma : {n : Nat} {A : Expr n} {B : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Sigma A B) N -> Empty
HeadRed1-not-Sigma ()

HeadRed1-not-MkPair : {n : Nat} {M N P : Expr n} ->
  HeadRed1 (MkPair M N) P -> Empty
HeadRed1-not-MkPair ()

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
HeadRed1-det headred-beta-fst headred-beta-fst = refl
HeadRed1-det headred-beta-fst (headred-fst s) with HeadRed1-not-MkPair s
... | ()
HeadRed1-det (headred-fst s) headred-beta-fst with HeadRed1-not-MkPair s
... | ()
HeadRed1-det headred-beta-snd headred-beta-snd = refl
HeadRed1-det headred-beta-snd (headred-snd s) with HeadRed1-not-MkPair s
... | ()
HeadRed1-det (headred-snd s) headred-beta-snd with HeadRed1-not-MkPair s
... | ()
HeadRed1-det (headred-fst s1) (headred-fst s2) =
  Eq-cong Fst (HeadRed1-det s1 s2)
  where open import BasicSigma using (Eq-cong)
HeadRed1-det (headred-snd s1) (headred-snd s2) =
  Eq-cong Snd (HeadRed1-det s1 s2)
  where open import BasicSigma using (Eq-cong)

-- HeadRed from Pi to Pi must be reflexivity
HeadRed-Pi-refl : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed (Pi A B) (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-Pi-refl headred-refl = mkSigma refl refl
HeadRed-Pi-refl (headred-step s _) with HeadRed1-not-Pi s
... | ()

-- HeadRed from Sigma to Sigma must be reflexivity
HeadRed-Sigma-refl : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed (Sigma A B) (Sigma A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-Sigma-refl headred-refl = mkSigma refl refl
HeadRed-Sigma-refl (headred-step s _) with HeadRed1-not-Sigma s
... | ()

HeadRed-unique-Pi : {n : Nat} {M : Expr n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed M (Pi A B) -> HeadRed M (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-unique-Pi headred-refl hr2 = HeadRed-Pi-refl hr2
HeadRed-unique-Pi (headred-step s1 _) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-unique-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-unique-Sigma : {n : Nat} {M : Expr n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed M (Sigma A B) -> HeadRed M (Sigma A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-unique-Sigma headred-refl hr2 = HeadRed-Sigma-refl hr2
HeadRed-unique-Sigma (headred-step s1 _) headred-refl with HeadRed1-not-Sigma s1
... | ()
HeadRed-unique-Sigma (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Sigma hr1
    (Eq-transport (\ x -> HeadRed x (Sigma _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Pi : {n : Nat} {M M' : Expr n} {A : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> HeadRed M (Pi A B) -> HeadRed M' (Pi A B)
HeadRed-strip-Pi headred-refl hr2 = hr2
HeadRed-strip-Pi (headred-step s1 hr1) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-strip-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

HeadRed-strip-Sigma : {n : Nat} {M M' : Expr n} {A : Expr n} {B : Expr (suc n)} ->
  HeadRed M M' -> HeadRed M (Sigma A B) -> HeadRed M' (Sigma A B)
HeadRed-strip-Sigma headred-refl hr2 = hr2
HeadRed-strip-Sigma (headred-step s1 hr1) headred-refl with HeadRed1-not-Sigma s1
... | ()
HeadRed-strip-Sigma (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-Sigma hr1
    (Eq-transport (\ x -> HeadRed x (Sigma _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

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
substExpr-id Prop         = refl
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
substExpr-id (Sigma A B)  =
  Eq-cong2-Expr Sigma (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
substExpr-id (MkPair a b) =
  Eq-cong2-Expr MkPair (substExpr-id a) (substExpr-id b)
substExpr-id (Fst M)      =
  Eq-cong Fst (substExpr-id M)
  where open import BasicSigma using (Eq-cong)
substExpr-id (Snd M)      =
  Eq-cong Snd (substExpr-id M)
  where open import BasicSigma using (Eq-cong)

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
