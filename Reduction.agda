{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Reduction.agda
--
-- Head reduction and Red (= HeadRed with phantom context/type parameters).
--
-- HeadRed1 M N : single-step head reduction (beta at head, congruence under App)
-- HeadRed  M N : reflexive-transitive closure of HeadRed1
-- Red G M N A  = HeadRed M N  (G and A are phantom)
--
-- All proved, 0 postulates.
-- Key results: HeadRed1-det, HeadRed-unique-Pi, HeadRed-wk, HeadRed-subst
------------------------------------------------------------------------

module Reduction where

import Basic as S
open S using (Nat ; suc ; Pair ; mkSigma ; Eq ; refl ; fst ; snd ; Empty ;
  Eq-sym ; Eq-transport)
open import RawSyntax using (Expr ; Var ; Pi ; App ; Lam ; U ; wkExpr ; subst1 ;
  Sub ; substExpr ; subst1Sub ; liftSub ; liftRen ; wkRen ; renExpr ;
  Fin ; fzero ; fsuc ; Eq-trans ; Eq-cong2-Expr ;
  subst-ren ; ren-subst ; subst-subst ; substExpr-ext)
open import TypingRules using (Ctx)

------------------------------------------------------------------------
-- HeadRed1: single-step head reduction
------------------------------------------------------------------------

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
    HeadRed1 (App (Lam A M) N) (subst1 M N)
  headred-app : {n : Nat} {M1 M2 N : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (App M1 N) (App M2 N)

------------------------------------------------------------------------
-- HeadRed: reflexive-transitive closure
------------------------------------------------------------------------

data HeadRed : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-refl : {n : Nat} {M : Expr n} -> HeadRed M M
  headred-step : {n : Nat} {M N P : Expr n} ->
    HeadRed1 M N -> HeadRed N P -> HeadRed M P

-- Transitivity of HeadRed
HeadRed-trans : {n : Nat} {M N P : Expr n} ->
  HeadRed M N -> HeadRed N P -> HeadRed M P
HeadRed-trans headred-refl hr2 = hr2
HeadRed-trans (headred-step s hr1) hr2 = headred-step s (HeadRed-trans hr1 hr2)

-- Congruence of HeadRed under App (left slot)
HeadRed-App : {n : Nat} {M N P : Expr n} ->
  HeadRed M N -> HeadRed (App M P) (App N P)
HeadRed-App headred-refl = headred-refl
HeadRed-App (headred-step s hr) = headred-step (headred-app s) (HeadRed-App hr)

------------------------------------------------------------------------
-- HeadRed1 cannot apply to Pi (Pi is not an App form)
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

-- HeadRed from Pi to Pi must be reflexivity
HeadRed-Pi-refl : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed (Pi A B) (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-Pi-refl headred-refl = mkSigma refl refl
HeadRed-Pi-refl (headred-step s _) with HeadRed1-not-Pi s
... | ()

-- HeadRed to Pi is unique (determinism + normal form)
HeadRed-unique-Pi : {n : Nat} {M : Expr n} {A A' : Expr n} {B B' : Expr (suc n)} ->
  HeadRed M (Pi A B) -> HeadRed M (Pi A' B') -> Pair (Eq A A') (Eq B B')
HeadRed-unique-Pi headred-refl hr2 = HeadRed-Pi-refl hr2
HeadRed-unique-Pi (headred-step s1 _) headred-refl with HeadRed1-not-Pi s1
... | ()
HeadRed-unique-Pi (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-unique-Pi hr1
    (Eq-transport (\ x -> HeadRed x (Pi _ _)) (Eq-sym (HeadRed1-det s1 s2)) hr2)

-- Strip lemma: HeadRed M M' and HeadRed M (Pi A B) imply HeadRed M' (Pi A B)
-- Pi is a normal form, so by determinism, M' lies on the path M →* Pi A B.
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
--
-- Red G M N A wraps HeadRed M N.  The context G and type A are
-- phantom parameters carried only so that Agda can infer them at
-- use sites.  No ConvTm, no postulates.
------------------------------------------------------------------------

data Red : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set where
  mkRed : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    HeadRed M N -> Red G M N A

------------------------------------------------------------------------
-- Proved properties
------------------------------------------------------------------------

-- Reflexivity (no premises needed)
Red-refl : {n : Nat} {G : Ctx n} {M A : Expr n} -> Red G M M A
Red-refl = mkRed headred-refl

-- Extract the HeadRed from a Red
Red-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red G M N A -> HeadRed M N
Red-hr (mkRed hr) = hr

-- Pi-injectivity: Red from Pi to Pi implies syntactic equality
Red-Pi-inj : {n : Nat} {G : Ctx n} {A A' : Expr n}
  {B B' : Expr (suc n)} ->
  Red G (Pi A B) (Pi A' B') U ->
  Pair (Eq A A') (Eq B B')
Red-Pi-inj (mkRed r) = HeadRed-Pi-refl r

------------------------------------------------------------------------
-- Identity substitution
------------------------------------------------------------------------

idSub : {n : Nat} -> Sub n n
idSub i = Var i

substExpr-id : {n : Nat} (M : Expr n) -> Eq (substExpr idSub M) M
substExpr-id (Var i)   = refl
substExpr-id U         = refl
substExpr-id (Pi A B)  =
  Eq-cong2-Expr Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
substExpr-id (Lam A M) =
  Eq-cong2-Expr Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> refl ; (fsuc i) -> refl }) M)
              (substExpr-id M))
substExpr-id (App f a) =
  Eq-cong2-Expr App (substExpr-id f) (substExpr-id a)

------------------------------------------------------------------------
-- HeadRed commutes with weakening
--
-- Key lemma: subst1 (renExpr (liftRen wkRen) M) (wkExpr N) = wkExpr (subst1 M N)
-- Proof: both sides reduce to the same substitution by subst-ren/ren-subst + ext.
------------------------------------------------------------------------

wk-subst1-comm : {n : Nat} (M : Expr (suc n)) (N : Expr n) ->
  Eq (subst1 (renExpr (liftRen wkRen) M) (wkExpr N)) (wkExpr (subst1 M N))
wk-subst1-comm M N =
  Eq-trans (subst-ren (subst1Sub (wkExpr N)) (liftRen wkRen) M)
    (Eq-trans (substExpr-ext _ _ ext M)
      (Eq-sym (ren-subst wkRen (subst1Sub N) M)))
  where
    ext : (i : Fin _) ->
      Eq (subst1Sub (wkExpr N) (liftRen wkRen i))
         (renExpr wkRen (subst1Sub N i))
    ext fzero    = refl
    ext (fsuc i) = refl

HeadRed1-wk : {n : Nat} {M N : Expr n} ->
  HeadRed1 M N -> HeadRed1 (wkExpr M) (wkExpr N)
HeadRed1-wk {M = App (Lam A M) N} (headred-beta {A = .A} {M = .M} {N = .N}) =
  Eq-transport (\ X -> HeadRed1 (App (Lam (wkExpr A) (renExpr (liftRen wkRen) M))
    (wkExpr N)) X) (wk-subst1-comm M N) headred-beta
HeadRed1-wk (headred-app s) = headred-app (HeadRed1-wk s)

HeadRed-wk : {n : Nat} {M N : Expr n} ->
  HeadRed M N -> HeadRed (wkExpr M) (wkExpr N)
HeadRed-wk headred-refl = headred-refl
HeadRed-wk (headred-step s hr) = headred-step (HeadRed1-wk s) (HeadRed-wk hr)

------------------------------------------------------------------------
-- HeadRed commutes with substitution
--
-- Key lemma: subst1 (substExpr (liftSub sigma) M) (substExpr sigma N)
--          = substExpr sigma (subst1 M N)
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
      -- LHS: substExpr (subst1Sub (substExpr sigma N)) (wkExpr (sigma i))
      -- by subst-ren: = substExpr (\ j -> Var j) (sigma i)
      -- by substExpr-ext + substExpr-id: = sigma i = RHS
      Eq-trans (subst-ren (subst1Sub (substExpr sigma N)) wkRen (sigma i))
        (Eq-trans (substExpr-ext _ idSub (\ j -> refl) (sigma i))
          (substExpr-id (sigma i)))

HeadRed1-subst : {n m : Nat} {M N : Expr n} (sigma : Sub m n) ->
  HeadRed1 M N -> HeadRed1 (substExpr sigma M) (substExpr sigma N)
HeadRed1-subst {M = App (Lam A M) N} sigma (headred-beta {A = .A} {M = .M} {N = .N}) =
  Eq-transport (\ X -> HeadRed1 (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
    (substExpr sigma N)) X) (subst-subst1-comm sigma M N) headred-beta
HeadRed1-subst sigma (headred-app s) = headred-app (HeadRed1-subst sigma s)

HeadRed-subst : {n m : Nat} {M N : Expr n} (sigma : Sub m n) ->
  HeadRed M N -> HeadRed (substExpr sigma M) (substExpr sigma N)
HeadRed-subst sigma headred-refl = headred-refl
HeadRed-subst sigma (headred-step s hr) =
  headred-step (HeadRed1-subst sigma s) (HeadRed-subst sigma hr)

