{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.Reduction
--
-- Head reduction. Minimal version with only Pi and U.
-- Parallel version of Reduction.agda.
------------------------------------------------------------------------

module CAST.Reduction where

import CAST.Basic as S
open S using (Nat ; suc ; Pair ; mkSigma ; Eq ; refl ; fst ; snd ; Empty ;
  Eq-sym ; Eq-transport)
open import CAST.RawSyntax using (Expr ; Var ; Pi ; App ; Lam ; U ;
  Id ; refl ; sym ; pi1 ; pi2 ; cast ;
  wkExpr ; subst1 ;
  Sub ; substExpr ; subst1Sub ; liftSub ; wkRen ;
  Fin ; fzero ; fsuc ; Eq-trans ; Eq-cong2-Expr ; Eq-cong3-Expr ; Eq-cong4-Expr ;
  subst-ren ; subst-subst ; substExpr-ext)
open S using (Eq-cong)
open import CAST.TypingRules using (Ctx)

------------------------------------------------------------------------
-- HeadRed1: single-step head reduction
------------------------------------------------------------------------

data HeadRed1 : {n : Nat} -> Expr n -> Expr n -> Set where
  headred-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
    HeadRed1 (App (Lam A M) N) (subst1 M N)
  -- ι-rule for coercion at a Π-type (the cast analog of β): a cast between
  -- Π-types is a value; applying it casts the argument back, applies, and
  -- casts the result forward.
  headred-cast-Pi : {n : Nat} {A C : Expr n} {B D : Expr (suc n)} {p M N : Expr n} ->
    HeadRed1 (App (cast (Pi A B) (Pi C D) p M) N)
             (cast (subst1 B (cast C A (pi1 (sym p)) N)) (subst1 D N)
                   (sym (pi2 (sym p) N))
                   (App M (cast C A (pi1 (sym p)) N)))
  headred-app : {n : Nat} {M1 M2 N : Expr n} ->
    HeadRed1 M1 M2 -> HeadRed1 (App M1 N) (App M2 N)
  -- Reduce a cast's TYPE arguments so that headred-cast-Pi can fire when the
  -- source/target are convertible (not literally) Pi.  Source first; target
  -- only once the source is a literal Pi (which is head-normal), keeping
  -- HeadRed1 deterministic.
  headred-cast-src : {n : Nat} {A A' B p M : Expr n} ->
    HeadRed1 A A' -> HeadRed1 (cast A B p M) (cast A' B p M)
  headred-cast-tgt : {n : Nat} {A0 : Expr n} {B0 : Expr (suc n)} {B B' p M : Expr n} ->
    HeadRed1 B B' -> HeadRed1 (cast (Pi A0 B0) B p M) (cast (Pi A0 B0) B' p M)
  headred-cast-tgt-U : {n : Nat} {B B' p M : Expr n} ->
    HeadRed1 B B' -> HeadRed1 (cast U B p M) (cast U B' p M)
  -- collapse: cast U U p M -> M  (the head-reduction analogue of conv-cast-refl,
  -- the LAST rule; fires only once both type arguments are the normal form U, so
  -- it is disjoint from src/tgt and from headred-cast-Pi -- HeadRed1 stays det).
  headred-cast-U : {n : Nat} {p M : Expr n} ->
    HeadRed1 (cast U U p M) M
  -- NB (settled 2026-06-10): the general Lean ι-rule `cast A B refl M -> M` is
  -- DELIBERATELY NOT a HeadRed1 rule.  It is not needed for adequacy (every case
  -- where a cast must reduce to expose a constructor is covered by cast-src/
  -- cast-tgt-U/cast-U at type level and headred-cast-Pi at application level),
  -- and adding it would overlap headred-cast-src on a reducible source, breaking
  -- HeadRed1 determinism (forcing a confluence rework).  The `cast A B p M = M`
  -- equality lives only as the CONVERSION conv-cast-refl / collapse-conv.

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

HeadRed-cast-src : {n : Nat} {A A' B p M : Expr n} ->
  HeadRed A A' -> HeadRed (cast A B p M) (cast A' B p M)
HeadRed-cast-src headred-refl = headred-refl
HeadRed-cast-src (headred-step s hr) = headred-step (headred-cast-src s) (HeadRed-cast-src hr)

HeadRed-cast-tgt : {n : Nat} {A0 : Expr n} {B0 : Expr (suc n)} {B B' p M : Expr n} ->
  HeadRed B B' -> HeadRed (cast (Pi A0 B0) B p M) (cast (Pi A0 B0) B' p M)
HeadRed-cast-tgt headred-refl = headred-refl
HeadRed-cast-tgt (headred-step s hr) = headred-step (headred-cast-tgt s) (HeadRed-cast-tgt hr)

HeadRed-cast-tgt-U : {n : Nat} {B B' p M : Expr n} ->
  HeadRed B B' -> HeadRed (cast U B p M) (cast U B' p M)
HeadRed-cast-tgt-U headred-refl = headred-refl
HeadRed-cast-tgt-U (headred-step s hr) = headred-step (headred-cast-tgt-U s) (HeadRed-cast-tgt-U hr)

------------------------------------------------------------------------
-- Normal form lemmas
------------------------------------------------------------------------

HeadRed1-not-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Pi A B) N -> Empty
HeadRed1-not-Pi ()

HeadRed1-not-Lam : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
  HeadRed1 (Lam A M) N -> Empty
HeadRed1-not-Lam ()

HeadRed1-not-U : {n : Nat} {N : Expr n} -> HeadRed1 U N -> Empty
HeadRed1-not-U ()

-- HeadRed1 is deterministic
HeadRed1-det : {n : Nat} {M N P : Expr n} ->
  HeadRed1 M N -> HeadRed1 M P -> Eq N P
HeadRed1-det headred-beta headred-beta = refl
HeadRed1-det headred-beta (headred-app s) with HeadRed1-not-Lam s
... | ()
HeadRed1-det (headred-app s) headred-beta with HeadRed1-not-Lam s
... | ()
HeadRed1-det headred-cast-Pi headred-cast-Pi = refl
HeadRed1-det headred-cast-Pi (headred-app (headred-cast-src s)) with HeadRed1-not-Pi s
... | ()
HeadRed1-det headred-cast-Pi (headred-app (headred-cast-tgt s)) with HeadRed1-not-Pi s
... | ()
HeadRed1-det (headred-app (headred-cast-src s)) headred-cast-Pi with HeadRed1-not-Pi s
... | ()
HeadRed1-det (headred-app (headred-cast-tgt s)) headred-cast-Pi with HeadRed1-not-Pi s
... | ()
HeadRed1-det (headred-app {N = N} s1) (headred-app s2) =
  Eq-cong2-Expr App (HeadRed1-det s1 s2) refl
HeadRed1-det (headred-cast-src s1) (headred-cast-src s2) =
  Eq-cong4-Expr cast (HeadRed1-det s1 s2) refl refl refl
HeadRed1-det (headred-cast-src s1) (headred-cast-tgt s2) with HeadRed1-not-Pi s1
... | ()
HeadRed1-det (headred-cast-tgt s1) (headred-cast-src s2) with HeadRed1-not-Pi s2
... | ()
HeadRed1-det (headred-cast-tgt s1) (headred-cast-tgt s2) =
  Eq-cong4-Expr cast refl (HeadRed1-det s1 s2) refl refl
HeadRed1-det (headred-cast-src s1) (headred-cast-tgt-U s2) with HeadRed1-not-U s1
... | ()
HeadRed1-det (headred-cast-tgt-U s1) (headred-cast-src s2) with HeadRed1-not-U s2
... | ()
HeadRed1-det (headred-cast-tgt-U s1) (headred-cast-tgt-U s2) =
  Eq-cong4-Expr cast refl (HeadRed1-det s1 s2) refl refl
HeadRed1-det headred-cast-U headred-cast-U = refl
HeadRed1-det headred-cast-U (headred-cast-src s) with HeadRed1-not-U s
... | ()
HeadRed1-det (headred-cast-src s) headred-cast-U with HeadRed1-not-U s
... | ()
HeadRed1-det headred-cast-U (headred-cast-tgt-U s) with HeadRed1-not-U s
... | ()
HeadRed1-det (headred-cast-tgt-U s) headred-cast-U with HeadRed1-not-U s
... | ()

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

-- exFalso + uniqueness of the untyped normal form (from single-step determinism)
exFalso-HR : {A : Set} -> Empty -> A
exFalso-HR ()

HeadRed-NF-unique : {n : Nat} {M N1 N2 : Expr n} ->
  HeadRed M N1 -> HeadRed M N2 ->
  ((X : Expr n) -> HeadRed1 N1 X -> Empty) ->
  ((X : Expr n) -> HeadRed1 N2 X -> Empty) ->
  Eq N1 N2
HeadRed-NF-unique headred-refl headred-refl nf1 nf2 = refl
HeadRed-NF-unique headred-refl (headred-step {N = N} s2 _) nf1 nf2 = exFalso-HR (nf1 N s2)
HeadRed-NF-unique (headred-step {N = N} s1 _) headred-refl nf1 nf2 = exFalso-HR (nf2 N s1)
HeadRed-NF-unique (headred-step s1 hr1) (headred-step s2 hr2) nf1 nf2 =
  HeadRed-NF-unique hr1 (Eq-transport (\ x -> HeadRed x _) (HeadRed1-det s2 s1) hr2) nf1 nf2

HeadRed-strip-U : {n : Nat} {M M' : Expr n} ->
  HeadRed M M' -> HeadRed M U -> HeadRed M' U
HeadRed-strip-U headred-refl hr2 = hr2
HeadRed-strip-U (headred-step s1 hr1) headred-refl with HeadRed1-not-U s1
... | ()
HeadRed-strip-U (headred-step s1 hr1) (headred-step s2 hr2) =
  HeadRed-strip-U hr1 (Eq-transport (\ x -> HeadRed x U) (Eq-sym (HeadRed1-det s1 s2)) hr2)

-- strip an untyped prefix M ->* M' from M ->* N when N is untyped-normal
HeadRed-strip-nf : {n : Nat} {M M' N : Expr n} ->
  HeadRed M M' -> HeadRed M N -> ((X : Expr n) -> HeadRed1 N X -> Empty) -> HeadRed M' N
HeadRed-strip-nf headred-refl hr2 nf = hr2
HeadRed-strip-nf (headred-step {N = K} s1 _) headred-refl nf = exFalso-HR (nf K s1)
HeadRed-strip-nf (headred-step s1 hr1) (headred-step s2 hr2) nf =
  HeadRed-strip-nf hr1 (Eq-transport (\ x -> HeadRed x _) (HeadRed1-det s2 s1) hr2) nf

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
substExpr-id (App f a)    =
  Eq-cong2-Expr App (substExpr-id f) (substExpr-id a)
substExpr-id (Id A B)     =
  Eq-cong2-Expr Id (substExpr-id A) (substExpr-id B)
substExpr-id refl         = refl
substExpr-id (sym p)      = Eq-cong sym (substExpr-id p)
substExpr-id (pi1 p)      = Eq-cong pi1 (substExpr-id p)
substExpr-id (pi2 p N)    = Eq-cong2-Expr pi2 (substExpr-id p) (substExpr-id N)
substExpr-id (cast A B p M) =
  Eq-cong4-Expr cast (substExpr-id A) (substExpr-id B) (substExpr-id p) (substExpr-id M)

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
