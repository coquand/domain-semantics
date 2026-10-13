{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Syntax.agda   (FROZEN shared module: edit only via coordinator)
--
-- Raw de Bruijn syntax of the annotated Russell Mahlo theory
-- (mahlo-plan.tex Sec. 1.1 and 6.1), renaming, parallel substitution
-- and their basic lemmas (after MIN/Syntax/Raw.agda).
--
-- All constructors are non-curried (plan Sec. 6.1): they are applied
-- to exactly their arguments.  Families are TERMS, not binders:
--   Pi A F, Sigma A F, Rec C z s n, Fhat f g A F, Ghat f g A F c,
-- and the typing rules (MAHLO/Typing.agda) only use F = Lam A B,
-- i.e. Pi x:A.B is  Pi A (Lam A B).  So Lam is the ONLY binder.
------------------------------------------------------------------------

module MAHLO.Syntax where

open import MAHLO.Basic using (Eq ; refl ; Eq-sym ; Eq-trans ; Eq-cong)

------------------------------------------------------------------------
-- Meta-level numbers (scope sizes) and de Bruijn indices
------------------------------------------------------------------------

data Num : Set where
  zero : Num
  suc  : Num -> Num

data Fin : Num -> Set where
  fzero : {n : Num} -> Fin (suc n)
  fsuc  : {n : Num} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Expr: raw terms
------------------------------------------------------------------------

data Expr : Num -> Set where
  Var   : {n : Num} -> Fin n -> Expr n
  Lam   : {n : Num} -> Expr n -> Expr (suc n) -> Expr n      -- \x:A. t
  App   : {n : Num} -> Expr n -> Expr n -> Expr n
  Pi    : {n : Num} -> Expr n -> Expr n -> Expr n            -- Pi(A,F)
  Sigma : {n : Num} -> Expr n -> Expr n -> Expr n            -- Sigma(A,F)
  Pair  : {n : Num} -> Expr n -> Expr n -> Expr n
  Fst   : {n : Num} -> Expr n -> Expr n
  Snd   : {n : Num} -> Expr n -> Expr n
  Nat   : {n : Num} -> Expr n
  Zero  : {n : Num} -> Expr n
  Suc   : {n : Num} -> Expr n -> Expr n
  Rec   : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n
                                                             -- rec(C,z,s,n)
  V     : {n : Num} -> Expr n
  Ucode : {n : Num} -> Expr n -> Expr n -> Expr n            -- U(f,g)
  Fhat  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n
                                                             -- fhat(f,g,A,F)
  Ghat  : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n
          -> Expr n                                          -- ghat(f,g,A,F,c)

------------------------------------------------------------------------
-- Congruence helpers
------------------------------------------------------------------------

cong2 : {A B C : Set} (h : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (h a b) (h a' b')
cong2 h refl refl = refl

cong4 : {A B C D E : Set} (h : A -> B -> C -> D -> E)
  {a a' : A} {b b' : B} {c c' : C} {d d' : D} ->
  Eq a a' -> Eq b b' -> Eq c c' -> Eq d d' -> Eq (h a b c d) (h a' b' c' d')
cong4 h refl refl refl refl = refl

cong5 : {A B C D E F : Set} (h : A -> B -> C -> D -> E -> F)
  {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} ->
  Eq a a' -> Eq b b' -> Eq c c' -> Eq d d' -> Eq e e' ->
  Eq (h a b c d e) (h a' b' c' d' e')
cong5 h refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Renamings
------------------------------------------------------------------------

Ren : Num -> Num -> Set
Ren n m = Fin n -> Fin m

liftRen : {n m : Num} -> Ren n m -> Ren (suc n) (suc m)
liftRen r fzero    = fzero
liftRen r (fsuc i) = fsuc (r i)

renExpr : {n m : Num} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)          = Var (r i)
renExpr r (Lam A t)        = Lam (renExpr r A) (renExpr (liftRen r) t)
renExpr r (App t u)        = App (renExpr r t) (renExpr r u)
renExpr r (Pi A F)         = Pi (renExpr r A) (renExpr r F)
renExpr r (Sigma A F)      = Sigma (renExpr r A) (renExpr r F)
renExpr r (Pair t u)       = Pair (renExpr r t) (renExpr r u)
renExpr r (Fst t)          = Fst (renExpr r t)
renExpr r (Snd t)          = Snd (renExpr r t)
renExpr r Nat              = Nat
renExpr r Zero             = Zero
renExpr r (Suc t)          = Suc (renExpr r t)
renExpr r (Rec C z s k)    = Rec (renExpr r C) (renExpr r z) (renExpr r s) (renExpr r k)
renExpr r V                = V
renExpr r (Ucode f g)      = Ucode (renExpr r f) (renExpr r g)
renExpr r (Fhat f g A F)   = Fhat (renExpr r f) (renExpr r g) (renExpr r A) (renExpr r F)
renExpr r (Ghat f g A F c) =
  Ghat (renExpr r f) (renExpr r g) (renExpr r A) (renExpr r F) (renExpr r c)

wkRen : {n : Num} -> Ren n (suc n)
wkRen i = fsuc i

wkExpr : {n : Num} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

------------------------------------------------------------------------
-- Parallel substitutions
------------------------------------------------------------------------

Sub : Num -> Num -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Num} -> Sub h g -> Sub (suc h) (suc g)
liftSub sigma fzero    = Var fzero
liftSub sigma (fsuc i) = wkExpr (sigma i)

substExpr : {h g : Num} -> Sub h g -> Expr g -> Expr h
substExpr s (Var i)          = s i
substExpr s (Lam A t)        = Lam (substExpr s A) (substExpr (liftSub s) t)
substExpr s (App t u)        = App (substExpr s t) (substExpr s u)
substExpr s (Pi A F)         = Pi (substExpr s A) (substExpr s F)
substExpr s (Sigma A F)      = Sigma (substExpr s A) (substExpr s F)
substExpr s (Pair t u)       = Pair (substExpr s t) (substExpr s u)
substExpr s (Fst t)          = Fst (substExpr s t)
substExpr s (Snd t)          = Snd (substExpr s t)
substExpr s Nat              = Nat
substExpr s Zero             = Zero
substExpr s (Suc t)          = Suc (substExpr s t)
substExpr s (Rec C z u k)    =
  Rec (substExpr s C) (substExpr s z) (substExpr s u) (substExpr s k)
substExpr s V                = V
substExpr s (Ucode f g)      = Ucode (substExpr s f) (substExpr s g)
substExpr s (Fhat f g A F)   =
  Fhat (substExpr s f) (substExpr s g) (substExpr s A) (substExpr s F)
substExpr s (Ghat f g A F c) =
  Ghat (substExpr s f) (substExpr s g) (substExpr s A) (substExpr s F) (substExpr s c)

idSub : {n : Num} -> Sub n n
idSub i = Var i

subst1Sub : {n : Num} -> Expr n -> Sub n (suc n)
subst1Sub a fzero    = a
subst1Sub a (fsuc i) = Var i

-- B[a/x]
subst1 : {n : Num} -> Expr (suc n) -> Expr n -> Expr n
subst1 B a = substExpr (subst1Sub a) B

------------------------------------------------------------------------
-- Extensionality
------------------------------------------------------------------------

liftRen-ext : {n m : Num} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (j : Fin (suc n)) -> Eq (liftRen r1 j) (liftRen r2 j)
liftRen-ext r1 r2 e fzero    = refl
liftRen-ext r1 r2 e (fsuc i) = Eq-cong fsuc (e i)

renExpr-ext : {n m : Num} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (t : Expr n) -> Eq (renExpr r1 t) (renExpr r2 t)
renExpr-ext r1 r2 e (Var i)          = Eq-cong Var (e i)
renExpr-ext r1 r2 e (Lam A t)        =
  cong2 Lam (renExpr-ext r1 r2 e A)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 e) t)
renExpr-ext r1 r2 e (App t u)        = cong2 App (renExpr-ext r1 r2 e t) (renExpr-ext r1 r2 e u)
renExpr-ext r1 r2 e (Pi A F)         = cong2 Pi (renExpr-ext r1 r2 e A) (renExpr-ext r1 r2 e F)
renExpr-ext r1 r2 e (Sigma A F)      = cong2 Sigma (renExpr-ext r1 r2 e A) (renExpr-ext r1 r2 e F)
renExpr-ext r1 r2 e (Pair t u)       = cong2 Pair (renExpr-ext r1 r2 e t) (renExpr-ext r1 r2 e u)
renExpr-ext r1 r2 e (Fst t)          = Eq-cong Fst (renExpr-ext r1 r2 e t)
renExpr-ext r1 r2 e (Snd t)          = Eq-cong Snd (renExpr-ext r1 r2 e t)
renExpr-ext r1 r2 e Nat              = refl
renExpr-ext r1 r2 e Zero             = refl
renExpr-ext r1 r2 e (Suc t)          = Eq-cong Suc (renExpr-ext r1 r2 e t)
renExpr-ext r1 r2 e (Rec C z s k)    =
  cong4 Rec (renExpr-ext r1 r2 e C) (renExpr-ext r1 r2 e z)
    (renExpr-ext r1 r2 e s) (renExpr-ext r1 r2 e k)
renExpr-ext r1 r2 e V                = refl
renExpr-ext r1 r2 e (Ucode f g)      = cong2 Ucode (renExpr-ext r1 r2 e f) (renExpr-ext r1 r2 e g)
renExpr-ext r1 r2 e (Fhat f g A F)   =
  cong4 Fhat (renExpr-ext r1 r2 e f) (renExpr-ext r1 r2 e g)
    (renExpr-ext r1 r2 e A) (renExpr-ext r1 r2 e F)
renExpr-ext r1 r2 e (Ghat f g A F c) =
  cong5 Ghat (renExpr-ext r1 r2 e f) (renExpr-ext r1 r2 e g)
    (renExpr-ext r1 r2 e A) (renExpr-ext r1 r2 e F) (renExpr-ext r1 r2 e c)

liftSub-ext : {h g : Num} (s1 s2 : Sub h g) ->
  ((i : Fin g) -> Eq (s1 i) (s2 i)) ->
  (j : Fin (suc g)) -> Eq (liftSub s1 j) (liftSub s2 j)
liftSub-ext s1 s2 e fzero    = refl
liftSub-ext s1 s2 e (fsuc i) = Eq-cong wkExpr (e i)

substExpr-ext : {h g : Num} (s1 s2 : Sub h g) ->
  ((i : Fin g) -> Eq (s1 i) (s2 i)) ->
  (t : Expr g) -> Eq (substExpr s1 t) (substExpr s2 t)
substExpr-ext s1 s2 e (Var i)          = e i
substExpr-ext s1 s2 e (Lam A t)        =
  cong2 Lam (substExpr-ext s1 s2 e A)
    (substExpr-ext (liftSub s1) (liftSub s2) (liftSub-ext s1 s2 e) t)
substExpr-ext s1 s2 e (App t u)        = cong2 App (substExpr-ext s1 s2 e t) (substExpr-ext s1 s2 e u)
substExpr-ext s1 s2 e (Pi A F)         = cong2 Pi (substExpr-ext s1 s2 e A) (substExpr-ext s1 s2 e F)
substExpr-ext s1 s2 e (Sigma A F)      = cong2 Sigma (substExpr-ext s1 s2 e A) (substExpr-ext s1 s2 e F)
substExpr-ext s1 s2 e (Pair t u)       = cong2 Pair (substExpr-ext s1 s2 e t) (substExpr-ext s1 s2 e u)
substExpr-ext s1 s2 e (Fst t)          = Eq-cong Fst (substExpr-ext s1 s2 e t)
substExpr-ext s1 s2 e (Snd t)          = Eq-cong Snd (substExpr-ext s1 s2 e t)
substExpr-ext s1 s2 e Nat              = refl
substExpr-ext s1 s2 e Zero             = refl
substExpr-ext s1 s2 e (Suc t)          = Eq-cong Suc (substExpr-ext s1 s2 e t)
substExpr-ext s1 s2 e (Rec C z s k)    =
  cong4 Rec (substExpr-ext s1 s2 e C) (substExpr-ext s1 s2 e z)
    (substExpr-ext s1 s2 e s) (substExpr-ext s1 s2 e k)
substExpr-ext s1 s2 e V                = refl
substExpr-ext s1 s2 e (Ucode f g)      = cong2 Ucode (substExpr-ext s1 s2 e f) (substExpr-ext s1 s2 e g)
substExpr-ext s1 s2 e (Fhat f g A F)   =
  cong4 Fhat (substExpr-ext s1 s2 e f) (substExpr-ext s1 s2 e g)
    (substExpr-ext s1 s2 e A) (substExpr-ext s1 s2 e F)
substExpr-ext s1 s2 e (Ghat f g A F c) =
  cong5 Ghat (substExpr-ext s1 s2 e f) (substExpr-ext s1 s2 e g)
    (substExpr-ext s1 s2 e A) (substExpr-ext s1 s2 e F) (substExpr-ext s1 s2 e c)

------------------------------------------------------------------------
-- Composition laws.  Each is first proved for an arbitrary pointwise
-- description of the composite (argument  e), which makes the binder
-- case a one-liner; the usual form is the instance  e = \ _ -> refl.
------------------------------------------------------------------------

-- renaming after renaming
ren-ren-gen : {n m k : Num} (r1 : Ren m k) (r2 : Ren n m) (r : Ren n k) ->
  ((i : Fin n) -> Eq (r1 (r2 i)) (r i)) ->
  (t : Expr n) -> Eq (renExpr r1 (renExpr r2 t)) (renExpr r t)
ren-ren-gen r1 r2 r e (Var i)          = Eq-cong Var (e i)
ren-ren-gen r1 r2 r e (Lam A t)        =
  cong2 Lam (ren-ren-gen r1 r2 r e A)
    (ren-ren-gen (liftRen r1) (liftRen r2) (liftRen r) e' t)
  where
    e' : (i : Fin _) -> Eq (liftRen r1 (liftRen r2 i)) (liftRen r i)
    e' fzero    = refl
    e' (fsuc i) = Eq-cong fsuc (e i)
ren-ren-gen r1 r2 r e (App t u)        = cong2 App (ren-ren-gen r1 r2 r e t) (ren-ren-gen r1 r2 r e u)
ren-ren-gen r1 r2 r e (Pi A F)         = cong2 Pi (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F)
ren-ren-gen r1 r2 r e (Sigma A F)      = cong2 Sigma (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F)
ren-ren-gen r1 r2 r e (Pair t u)       = cong2 Pair (ren-ren-gen r1 r2 r e t) (ren-ren-gen r1 r2 r e u)
ren-ren-gen r1 r2 r e (Fst t)          = Eq-cong Fst (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e (Snd t)          = Eq-cong Snd (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e Nat              = refl
ren-ren-gen r1 r2 r e Zero             = refl
ren-ren-gen r1 r2 r e (Suc t)          = Eq-cong Suc (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e (Rec C z s k)    =
  cong4 Rec (ren-ren-gen r1 r2 r e C) (ren-ren-gen r1 r2 r e z)
    (ren-ren-gen r1 r2 r e s) (ren-ren-gen r1 r2 r e k)
ren-ren-gen r1 r2 r e V                = refl
ren-ren-gen r1 r2 r e (Ucode f g)      = cong2 Ucode (ren-ren-gen r1 r2 r e f) (ren-ren-gen r1 r2 r e g)
ren-ren-gen r1 r2 r e (Fhat f g A F)   =
  cong4 Fhat (ren-ren-gen r1 r2 r e f) (ren-ren-gen r1 r2 r e g)
    (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F)
ren-ren-gen r1 r2 r e (Ghat f g A F c) =
  cong5 Ghat (ren-ren-gen r1 r2 r e f) (ren-ren-gen r1 r2 r e g)
    (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F) (ren-ren-gen r1 r2 r e c)

ren-ren : {n m k : Num} (r1 : Ren m k) (r2 : Ren n m) (t : Expr n) ->
  Eq (renExpr r1 (renExpr r2 t)) (renExpr (\ i -> r1 (r2 i)) t)
ren-ren r1 r2 t = ren-ren-gen r1 r2 (\ i -> r1 (r2 i)) (\ i -> refl) t

-- substitution after renaming
subst-ren-gen : {h g k : Num} (s : Sub h g) (r : Ren k g) (s' : Sub h k) ->
  ((i : Fin k) -> Eq (s (r i)) (s' i)) ->
  (t : Expr k) -> Eq (substExpr s (renExpr r t)) (substExpr s' t)
subst-ren-gen s r s' e (Var i)          = e i
subst-ren-gen s r s' e (Lam A t)        =
  cong2 Lam (subst-ren-gen s r s' e A)
    (subst-ren-gen (liftSub s) (liftRen r) (liftSub s') e' t)
  where
    e' : (i : Fin _) -> Eq (liftSub s (liftRen r i)) (liftSub s' i)
    e' fzero    = refl
    e' (fsuc i) = Eq-cong wkExpr (e i)
subst-ren-gen s r s' e (App t u)        = cong2 App (subst-ren-gen s r s' e t) (subst-ren-gen s r s' e u)
subst-ren-gen s r s' e (Pi A F)         = cong2 Pi (subst-ren-gen s r s' e A) (subst-ren-gen s r s' e F)
subst-ren-gen s r s' e (Sigma A F)      = cong2 Sigma (subst-ren-gen s r s' e A) (subst-ren-gen s r s' e F)
subst-ren-gen s r s' e (Pair t u)       = cong2 Pair (subst-ren-gen s r s' e t) (subst-ren-gen s r s' e u)
subst-ren-gen s r s' e (Fst t)          = Eq-cong Fst (subst-ren-gen s r s' e t)
subst-ren-gen s r s' e (Snd t)          = Eq-cong Snd (subst-ren-gen s r s' e t)
subst-ren-gen s r s' e Nat              = refl
subst-ren-gen s r s' e Zero             = refl
subst-ren-gen s r s' e (Suc t)          = Eq-cong Suc (subst-ren-gen s r s' e t)
subst-ren-gen s r s' e (Rec C z u k)    =
  cong4 Rec (subst-ren-gen s r s' e C) (subst-ren-gen s r s' e z)
    (subst-ren-gen s r s' e u) (subst-ren-gen s r s' e k)
subst-ren-gen s r s' e V                = refl
subst-ren-gen s r s' e (Ucode f g)      = cong2 Ucode (subst-ren-gen s r s' e f) (subst-ren-gen s r s' e g)
subst-ren-gen s r s' e (Fhat f g A F)   =
  cong4 Fhat (subst-ren-gen s r s' e f) (subst-ren-gen s r s' e g)
    (subst-ren-gen s r s' e A) (subst-ren-gen s r s' e F)
subst-ren-gen s r s' e (Ghat f g A F c) =
  cong5 Ghat (subst-ren-gen s r s' e f) (subst-ren-gen s r s' e g)
    (subst-ren-gen s r s' e A) (subst-ren-gen s r s' e F) (subst-ren-gen s r s' e c)

subst-ren : {h g k : Num} (s : Sub h g) (r : Ren k g) (t : Expr k) ->
  Eq (substExpr s (renExpr r t)) (substExpr (\ i -> s (r i)) t)
subst-ren s r t = subst-ren-gen s r (\ i -> s (r i)) (\ i -> refl) t

-- renaming after substitution
ren-wk-comm : {n m : Num} (r : Ren n m) (t : Expr n) ->
  Eq (renExpr (liftRen r) (wkExpr t)) (wkExpr (renExpr r t))
ren-wk-comm r t =
  Eq-trans (ren-ren-gen (liftRen r) wkRen (\ i -> fsuc (r i)) (\ i -> refl) t)
    (Eq-sym (ren-ren-gen wkRen r (\ i -> fsuc (r i)) (\ i -> refl) t))

ren-subst-gen : {h g k : Num} (r : Ren g k) (s : Sub g h) (s' : Sub k h) ->
  ((i : Fin h) -> Eq (renExpr r (s i)) (s' i)) ->
  (t : Expr h) -> Eq (renExpr r (substExpr s t)) (substExpr s' t)
ren-subst-gen r s s' e (Var i)          = e i
ren-subst-gen r s s' e (Lam A t)        =
  cong2 Lam (ren-subst-gen r s s' e A)
    (ren-subst-gen (liftRen r) (liftSub s) (liftSub s') e' t)
  where
    e' : (i : Fin _) -> Eq (renExpr (liftRen r) (liftSub s i)) (liftSub s' i)
    e' fzero    = refl
    e' (fsuc i) = Eq-trans (ren-wk-comm r (s i)) (Eq-cong wkExpr (e i))
ren-subst-gen r s s' e (App t u)        = cong2 App (ren-subst-gen r s s' e t) (ren-subst-gen r s s' e u)
ren-subst-gen r s s' e (Pi A F)         = cong2 Pi (ren-subst-gen r s s' e A) (ren-subst-gen r s s' e F)
ren-subst-gen r s s' e (Sigma A F)      = cong2 Sigma (ren-subst-gen r s s' e A) (ren-subst-gen r s s' e F)
ren-subst-gen r s s' e (Pair t u)       = cong2 Pair (ren-subst-gen r s s' e t) (ren-subst-gen r s s' e u)
ren-subst-gen r s s' e (Fst t)          = Eq-cong Fst (ren-subst-gen r s s' e t)
ren-subst-gen r s s' e (Snd t)          = Eq-cong Snd (ren-subst-gen r s s' e t)
ren-subst-gen r s s' e Nat              = refl
ren-subst-gen r s s' e Zero             = refl
ren-subst-gen r s s' e (Suc t)          = Eq-cong Suc (ren-subst-gen r s s' e t)
ren-subst-gen r s s' e (Rec C z u k)    =
  cong4 Rec (ren-subst-gen r s s' e C) (ren-subst-gen r s s' e z)
    (ren-subst-gen r s s' e u) (ren-subst-gen r s s' e k)
ren-subst-gen r s s' e V                = refl
ren-subst-gen r s s' e (Ucode f g)      = cong2 Ucode (ren-subst-gen r s s' e f) (ren-subst-gen r s s' e g)
ren-subst-gen r s s' e (Fhat f g A F)   =
  cong4 Fhat (ren-subst-gen r s s' e f) (ren-subst-gen r s s' e g)
    (ren-subst-gen r s s' e A) (ren-subst-gen r s s' e F)
ren-subst-gen r s s' e (Ghat f g A F c) =
  cong5 Ghat (ren-subst-gen r s s' e f) (ren-subst-gen r s s' e g)
    (ren-subst-gen r s s' e A) (ren-subst-gen r s s' e F) (ren-subst-gen r s s' e c)

ren-subst : {h g k : Num} (r : Ren g k) (s : Sub g h) (t : Expr h) ->
  Eq (renExpr r (substExpr s t)) (substExpr (\ i -> renExpr r (s i)) t)
ren-subst r s t = ren-subst-gen r s (\ i -> renExpr r (s i)) (\ i -> refl) t

-- substitution after substitution
subst-wk-comm : {h g : Num} (s : Sub g h) (t : Expr h) ->
  Eq (substExpr (liftSub s) (wkExpr t)) (wkExpr (substExpr s t))
subst-wk-comm s t =
  Eq-trans (subst-ren s' wkRen t) (Eq-sym (ren-subst wkRen s t))
  where s' = liftSub s

subst-subst-gen : {h g k : Num} (s2 : Sub k g) (s1 : Sub g h) (s : Sub k h) ->
  ((i : Fin h) -> Eq (substExpr s2 (s1 i)) (s i)) ->
  (t : Expr h) -> Eq (substExpr s2 (substExpr s1 t)) (substExpr s t)
subst-subst-gen s2 s1 s e (Var i)          = e i
subst-subst-gen s2 s1 s e (Lam A t)        =
  cong2 Lam (subst-subst-gen s2 s1 s e A)
    (subst-subst-gen (liftSub s2) (liftSub s1) (liftSub s) e' t)
  where
    e' : (i : Fin _) -> Eq (substExpr (liftSub s2) (liftSub s1 i)) (liftSub s i)
    e' fzero    = refl
    e' (fsuc i) = Eq-trans (subst-wk-comm s2 (s1 i)) (Eq-cong wkExpr (e i))
subst-subst-gen s2 s1 s e (App t u)        = cong2 App (subst-subst-gen s2 s1 s e t) (subst-subst-gen s2 s1 s e u)
subst-subst-gen s2 s1 s e (Pi A F)         = cong2 Pi (subst-subst-gen s2 s1 s e A) (subst-subst-gen s2 s1 s e F)
subst-subst-gen s2 s1 s e (Sigma A F)      = cong2 Sigma (subst-subst-gen s2 s1 s e A) (subst-subst-gen s2 s1 s e F)
subst-subst-gen s2 s1 s e (Pair t u)       = cong2 Pair (subst-subst-gen s2 s1 s e t) (subst-subst-gen s2 s1 s e u)
subst-subst-gen s2 s1 s e (Fst t)          = Eq-cong Fst (subst-subst-gen s2 s1 s e t)
subst-subst-gen s2 s1 s e (Snd t)          = Eq-cong Snd (subst-subst-gen s2 s1 s e t)
subst-subst-gen s2 s1 s e Nat              = refl
subst-subst-gen s2 s1 s e Zero             = refl
subst-subst-gen s2 s1 s e (Suc t)          = Eq-cong Suc (subst-subst-gen s2 s1 s e t)
subst-subst-gen s2 s1 s e (Rec C z u k)    =
  cong4 Rec (subst-subst-gen s2 s1 s e C) (subst-subst-gen s2 s1 s e z)
    (subst-subst-gen s2 s1 s e u) (subst-subst-gen s2 s1 s e k)
subst-subst-gen s2 s1 s e V                = refl
subst-subst-gen s2 s1 s e (Ucode f g)      = cong2 Ucode (subst-subst-gen s2 s1 s e f) (subst-subst-gen s2 s1 s e g)
subst-subst-gen s2 s1 s e (Fhat f g A F)   =
  cong4 Fhat (subst-subst-gen s2 s1 s e f) (subst-subst-gen s2 s1 s e g)
    (subst-subst-gen s2 s1 s e A) (subst-subst-gen s2 s1 s e F)
subst-subst-gen s2 s1 s e (Ghat f g A F c) =
  cong5 Ghat (subst-subst-gen s2 s1 s e f) (subst-subst-gen s2 s1 s e g)
    (subst-subst-gen s2 s1 s e A) (subst-subst-gen s2 s1 s e F) (subst-subst-gen s2 s1 s e c)

subst-subst : {h g k : Num} (s2 : Sub k g) (s1 : Sub g h) (t : Expr h) ->
  Eq (substExpr s2 (substExpr s1 t)) (substExpr (\ i -> substExpr s2 (s1 i)) t)
subst-subst s2 s1 t = subst-subst-gen s2 s1 (\ i -> substExpr s2 (s1 i)) (\ i -> refl) t

------------------------------------------------------------------------
-- Identity laws
------------------------------------------------------------------------

substExpr-id-gen : {n : Num} (s : Sub n n) ->
  ((i : Fin n) -> Eq (s i) (Var i)) ->
  (t : Expr n) -> Eq (substExpr s t) t
substExpr-id-gen s e (Var i)          = e i
substExpr-id-gen s e (Lam A t)        =
  cong2 Lam (substExpr-id-gen s e A) (substExpr-id-gen (liftSub s) e' t)
  where
    e' : (i : Fin _) -> Eq (liftSub s i) (Var i)
    e' fzero    = refl
    e' (fsuc i) = Eq-cong wkExpr (e i)
substExpr-id-gen s e (App t u)        = cong2 App (substExpr-id-gen s e t) (substExpr-id-gen s e u)
substExpr-id-gen s e (Pi A F)         = cong2 Pi (substExpr-id-gen s e A) (substExpr-id-gen s e F)
substExpr-id-gen s e (Sigma A F)      = cong2 Sigma (substExpr-id-gen s e A) (substExpr-id-gen s e F)
substExpr-id-gen s e (Pair t u)       = cong2 Pair (substExpr-id-gen s e t) (substExpr-id-gen s e u)
substExpr-id-gen s e (Fst t)          = Eq-cong Fst (substExpr-id-gen s e t)
substExpr-id-gen s e (Snd t)          = Eq-cong Snd (substExpr-id-gen s e t)
substExpr-id-gen s e Nat              = refl
substExpr-id-gen s e Zero             = refl
substExpr-id-gen s e (Suc t)          = Eq-cong Suc (substExpr-id-gen s e t)
substExpr-id-gen s e (Rec C z u k)    =
  cong4 Rec (substExpr-id-gen s e C) (substExpr-id-gen s e z)
    (substExpr-id-gen s e u) (substExpr-id-gen s e k)
substExpr-id-gen s e V                = refl
substExpr-id-gen s e (Ucode f g)      = cong2 Ucode (substExpr-id-gen s e f) (substExpr-id-gen s e g)
substExpr-id-gen s e (Fhat f g A F)   =
  cong4 Fhat (substExpr-id-gen s e f) (substExpr-id-gen s e g)
    (substExpr-id-gen s e A) (substExpr-id-gen s e F)
substExpr-id-gen s e (Ghat f g A F c) =
  cong5 Ghat (substExpr-id-gen s e f) (substExpr-id-gen s e g)
    (substExpr-id-gen s e A) (substExpr-id-gen s e F) (substExpr-id-gen s e c)

substExpr-id : {n : Num} (t : Expr n) -> Eq (substExpr idSub t) t
substExpr-id t = substExpr-id-gen idSub (\ i -> refl) t

-- a renaming, seen as a substitution
ren-as-subst : {n m : Num} (r : Ren n m) (t : Expr n) ->
  Eq (renExpr r t) (substExpr (\ i -> Var (r i)) t)
ren-as-subst r t =
  Eq-trans (Eq-sym (substExpr-id (renExpr r t)))
    (subst-ren-gen idSub r (\ i -> Var (r i)) (\ i -> refl) t)

------------------------------------------------------------------------
-- Single substitution
------------------------------------------------------------------------

-- (wk e)[a/x] = e
subst1-wk : {n : Num} (e a : Expr n) -> Eq (subst1 (wkExpr e) a) e
subst1-wk e a =
  Eq-trans (subst-ren-gen (subst1Sub a) wkRen idSub (\ i -> refl) e) (substExpr-id e)

-- r (B[a/x]) = (lift r B)[r a / x]
ren-subst1 : {n m : Num} (r : Ren n m) (B : Expr (suc n)) (a : Expr n) ->
  Eq (renExpr r (subst1 B a)) (subst1 (renExpr (liftRen r) B) (renExpr r a))
ren-subst1 r B a =
  Eq-trans (ren-subst-gen r (subst1Sub a) s e B)
    (Eq-sym (subst-ren-gen (subst1Sub (renExpr r a)) (liftRen r) s e' B))
  where
    s : Sub _ _
    s fzero    = renExpr r a
    s (fsuc i) = Var (r i)
    e : (i : Fin _) -> Eq (renExpr r (subst1Sub a i)) (s i)
    e fzero    = refl
    e (fsuc i) = refl
    e' : (i : Fin _) -> Eq (subst1Sub (renExpr r a) (liftRen r i)) (s i)
    e' fzero    = refl
    e' (fsuc i) = refl

-- sigma (B[a/x]) = (lift sigma B)[sigma a / x]
subst-subst1-comm : {h g : Num} (s : Sub h g) (B : Expr (suc g)) (a : Expr g) ->
  Eq (substExpr s (subst1 B a)) (subst1 (substExpr (liftSub s) B) (substExpr s a))
subst-subst1-comm s B a =
  Eq-trans (subst-subst-gen s (subst1Sub a) s0 e B)
    (Eq-sym (subst-subst-gen (subst1Sub (substExpr s a)) (liftSub s) s0 e' B))
  where
    s0 : Sub _ _
    s0 fzero    = substExpr s a
    s0 (fsuc i) = s i
    e : (i : Fin _) -> Eq (substExpr s (subst1Sub a i)) (s0 i)
    e fzero    = refl
    e (fsuc i) = refl
    e' : (i : Fin _) -> Eq (substExpr (subst1Sub (substExpr s a)) (liftSub s i)) (s0 i)
    e' fzero    = refl
    e' (fsuc i) = subst1-wk (s i) (substExpr s a)

-- (lift wk B)[x0/x] = B
subst1-liftWk-cancel : {n : Num} (B : Expr (suc n)) ->
  Eq (subst1 (renExpr (liftRen wkRen) B) (Var fzero)) B
subst1-liftWk-cancel B =
  Eq-trans (subst-ren-gen (subst1Sub (Var fzero)) (liftRen wkRen) idSub e B)
    (substExpr-id B)
  where
    e : (i : Fin _) -> Eq (subst1Sub (Var fzero) (liftRen wkRen i)) (Var i)
    e fzero    = refl
    e (fsuc i) = refl

------------------------------------------------------------------------
-- Derived formers used by the typing rules
------------------------------------------------------------------------

-- Pi x:A. B  and  Sigma x:A. B,  B in scope (suc n)
PiB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n
PiB A B = Pi A (Lam A B)

SigmaB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n
SigmaB A B = Sigma A (Lam A B)

-- A -> B  (non-dependent)
Arr : {n : Num} -> Expr n -> Expr n -> Expr n
Arr A B = PiB A (wkExpr B)

x0 : {n : Num} -> Expr (suc n)
x0 = Var fzero

x1 : {n : Num} -> Expr (suc (suc n))
x1 = Var (fsuc fzero)

-- type of f :  Pi A:V. (A -> V) -> V
OpF : {n : Num} -> Expr n
OpF = PiB V (Arr (Arr x0 V) V)

-- type of g :  Pi A:V. Pi B:A -> V. f A B -> V
OpG : {n : Num} -> Expr n -> Expr n
OpG f = PiB V (PiB (Arr x0 V) (Arr (App (App (wkExpr (wkExpr f)) x1) x0) V))

-- C[S x / x]  (C in scope (suc n), result in scope (suc n))
sucSub : {n : Num} -> Sub (suc n) (suc n)
sucSub fzero    = Suc x0
sucSub (fsuc i) = Var (fsuc i)

-- type of the step of rec:  Pi x:Nat. C -> C[S x]
RecStep : {n : Num} -> Expr (suc n) -> Expr n
RecStep C = PiB Nat (Arr C (substExpr sucSub C))
