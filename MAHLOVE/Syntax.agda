{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOVE/Syntax.agda
--
-- The raw syntax of MAHLO/Syntax.agda (copied verbatim: renaming,
-- substitution, derived formers), extended by ONE new term former
--   VElim C cN cP cS cU t
-- the eliminator of the Mahlo universe V (Palmgren's "closed" V).
-- MAHLO/Syntax.agda itself is frozen and is not modified: adding a
-- constructor to its Expr would break every downstream project.
-- Only the definitions needed to state the rules are copied, not the
-- substitution lemmas.
------------------------------------------------------------------------

module MAHLOVE.Syntax where

open import MAHLOVE.Basic using (Eq ; refl ; Eq-sym ; Eq-trans ; Eq-cong)

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
  -- NEW: elimination of V,  velim(x.C, cN, A B iA iB.cP, A B iA iB.cS,
  --                               f g if ig.cU, t)
  -- binder style: C binds 1 variable, the three step cases bind 4.
  VElim : {n : Num} -> Expr (suc n) -> Expr n
          -> Expr (suc (suc (suc (suc n))))
          -> Expr (suc (suc (suc (suc n))))
          -> Expr (suc (suc (suc (suc n))))
          -> Expr n -> Expr n

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

liftRen4 : {n m : Num} -> Ren n m -> Ren (suc (suc (suc (suc n)))) (suc (suc (suc (suc m))))
liftRen4 r = liftRen (liftRen (liftRen (liftRen r)))

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
renExpr r (VElim C cN cP cS cU t) =
  VElim (renExpr (liftRen r) C) (renExpr r cN) (renExpr (liftRen4 r) cP)
        (renExpr (liftRen4 r) cS) (renExpr (liftRen4 r) cU) (renExpr r t)

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

liftSub4 : {h g : Num} -> Sub h g -> Sub (suc (suc (suc (suc h)))) (suc (suc (suc (suc g))))
liftSub4 s = liftSub (liftSub (liftSub (liftSub s)))

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
substExpr s (VElim C cN cP cS cU t) =
  VElim (substExpr (liftSub s) C) (substExpr s cN) (substExpr (liftSub4 s) cP)
        (substExpr (liftSub4 s) cS) (substExpr (liftSub4 s) cU) (substExpr s t)

idSub : {n : Num} -> Sub n n
idSub i = Var i

subst1Sub : {n : Num} -> Expr n -> Sub n (suc n)
subst1Sub a fzero    = a
subst1Sub a (fsuc i) = Var i

-- B[a/x]
subst1 : {n : Num} -> Expr (suc n) -> Expr n -> Expr n
subst1 B a = substExpr (subst1Sub a) B

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

------------------------------------------------------------------------
-- NEW: helpers for the V-elimination rule
------------------------------------------------------------------------

x2 : {n : Num} -> Expr (suc (suc (suc n)))
x2 = Var (fsuc (fsuc fzero))

x3 : {n : Num} -> Expr (suc (suc (suc (suc n))))
x3 = Var (fsuc (fsuc (fsuc fzero)))

x4 : {n : Num} -> Expr (suc (suc (suc (suc (suc n)))))
x4 = Var (fsuc (fsuc (fsuc (fsuc fzero))))

-- weakening renamings  Ren n (k + n)
w2 : {n : Num} -> Ren n (suc (suc n))
w2 i = fsuc (fsuc i)

w4 : {n : Num} -> Ren n (suc (suc (suc (suc n))))
w4 i = fsuc (fsuc (fsuc (fsuc i)))

w6 : {n : Num} -> Ren n (suc (suc (suc (suc (suc (suc n))))))
w6 i = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc i)))))

consSub : {h g : Num} -> Expr h -> Sub h g -> Sub h (suc g)
consSub t s fzero    = t
consSub t s (fsuc i) = s i

-- C[t] for C in scope (suc n), t in scope m, along a weakening r
inst : {n m : Num} -> Ren n m -> Expr (suc n) -> Expr m -> Expr m
inst r C t = substExpr (consSub t (\ i -> Var (r i))) C

-- [a, b, c, d / x3, x2, x1, x0]
sub4 : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Sub n (suc (suc (suc (suc n))))
sub4 a b c d = consSub d (consSub c (consSub b (consSub a (\ i -> Var i))))

-- the eliminator with all components renamed along r (used for the
-- induction hypotheses of the computation rules)
velimR : {n m : Num} -> Ren n m -> Expr (suc n) -> Expr n
         -> Expr (suc (suc (suc (suc n)))) -> Expr (suc (suc (suc (suc n))))
         -> Expr (suc (suc (suc (suc n)))) -> Expr m -> Expr m
velimR r C cN cP cS cU t =
  VElim (renExpr (liftRen r) C) (renExpr r cN) (renExpr (liftRen4 r) cP)
        (renExpr (liftRen4 r) cS) (renExpr (liftRen4 r) cU) t

w3 : {n : Num} -> Ren n (suc (suc (suc n)))
w3 i = fsuc (fsuc (fsuc i))
