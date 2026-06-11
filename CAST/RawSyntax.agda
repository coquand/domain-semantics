{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RawSyntax.agda  (MIN/ — Pi + U fragment)
--
-- Raw syntax with only Pi and U. No Sigma, no Prop.
------------------------------------------------------------------------

module CAST.RawSyntax where

open import CAST.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ; Eq-transport ; Eq-sym)

------------------------------------------------------------------------
-- Fin — de Bruijn variables
------------------------------------------------------------------------

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Expr — raw expressions
------------------------------------------------------------------------

data Expr : Nat -> Set where
  Var    : {n : Nat} -> Fin n -> Expr n
  U      : {n : Nat} -> Expr n
  Pi     : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  Lam    : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  App    : {n : Nat} -> Expr n -> Expr n -> Expr n
  -- Proof-irrelevant equality of types, its proofs, and type-directed cast.
  Id     : {n : Nat} -> Expr n -> Expr n -> Expr n           -- Id A B : U
  refl   : {n : Nat} -> Expr n                               -- refl : Id A A
  sym    : {n : Nat} -> Expr n -> Expr n                     -- sym p : Id B A
  pi1    : {n : Nat} -> Expr n -> Expr n                     -- pi1 p : Id A C
  pi2    : {n : Nat} -> Expr n -> Expr n -> Expr n           -- pi2 p N
  cast   : {n : Nat} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n  -- cast A B p M : B

------------------------------------------------------------------------
-- Ren — renamings
------------------------------------------------------------------------

Ren : Nat -> Nat -> Set
Ren n m = Fin n -> Fin m

liftRen : {n m : Nat} -> Ren n m -> Ren (suc n) (suc m)
liftRen r fzero    = fzero
liftRen r (fsuc i) = fsuc (r i)

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)      = Var (r i)
renExpr r U            = U
renExpr r (Pi A B)     = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A M)    = Lam (renExpr r A) (renExpr (liftRen r) M)
renExpr r (App f a)    = App (renExpr r f) (renExpr r a)
renExpr r (Id A B)     = Id (renExpr r A) (renExpr r B)
renExpr r refl         = refl
renExpr r (sym p)      = sym (renExpr r p)
renExpr r (pi1 p)      = pi1 (renExpr r p)
renExpr r (pi2 p N)    = pi2 (renExpr r p) (renExpr r N)
renExpr r (cast A B p M) = cast (renExpr r A) (renExpr r B) (renExpr r p) (renExpr r M)

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

wkRen : {n : Nat} -> Ren n (suc n)
wkRen i = fsuc i

wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

------------------------------------------------------------------------
-- General (parallel) substitution
------------------------------------------------------------------------

Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub sigma fzero    = Var fzero
liftSub sigma (fsuc i) = wkExpr (sigma i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr sigma (Var i)      = sigma i
substExpr sigma U            = U
substExpr sigma (Pi A B)     = Pi (substExpr sigma A) (substExpr (liftSub sigma) B)
substExpr sigma (Lam A M)    = Lam (substExpr sigma A) (substExpr (liftSub sigma) M)
substExpr sigma (App f a)    = App (substExpr sigma f) (substExpr sigma a)
substExpr sigma (Id A B)     = Id (substExpr sigma A) (substExpr sigma B)
substExpr sigma refl         = refl
substExpr sigma (sym p)      = sym (substExpr sigma p)
substExpr sigma (pi1 p)      = pi1 (substExpr sigma p)
substExpr sigma (pi2 p N)    = pi2 (substExpr sigma p) (substExpr sigma N)
substExpr sigma (cast A B p M) =
  cast (substExpr sigma A) (substExpr sigma B) (substExpr sigma p) (substExpr sigma M)

------------------------------------------------------------------------
-- Unary substitution
------------------------------------------------------------------------

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub s fzero    = s
subst1Sub s (fsuc i) = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 M s = substExpr (subst1Sub s) M

------------------------------------------------------------------------
-- Equality helpers
------------------------------------------------------------------------

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans refl refl = refl

Eq-cong2-Expr : {n m : Nat} (c : Expr n -> Expr m -> Expr n) ->
  {a a' : Expr n} {b b' : Expr m} ->
  Eq a a' -> Eq b b' -> Eq (c a b) (c a' b')
Eq-cong2-Expr c refl refl = refl

Eq-cong3-Expr : {n : Nat} (c : Expr n -> Expr n -> Expr n -> Expr n) ->
  {a a' b b' m m' : Expr n} ->
  Eq a a' -> Eq b b' -> Eq m m' -> Eq (c a b m) (c a' b' m')
Eq-cong3-Expr c refl refl refl = refl

Eq-cong4-Expr : {n : Nat} (c : Expr n -> Expr n -> Expr n -> Expr n -> Expr n) ->
  {a a' b b' p p' m m' : Expr n} ->
  Eq a a' -> Eq b b' -> Eq p p' -> Eq m m' -> Eq (c a b p m) (c a' b' p' m')
Eq-cong4-Expr c refl refl refl refl = refl

------------------------------------------------------------------------
-- Substitution respects pointwise equality
------------------------------------------------------------------------

liftSub-ext : {h g : Nat} (sigma tau : Sub h g) ->
  ((i : Fin g) -> Eq (sigma i) (tau i)) ->
  (j : Fin (suc g)) -> Eq (liftSub sigma j) (liftSub tau j)
liftSub-ext sigma tau ext fzero    = refl
liftSub-ext sigma tau ext (fsuc i) = Eq-cong wkExpr (ext i)

substExpr-ext : {h g : Nat} (sigma tau : Sub h g) ->
  ((i : Fin g) -> Eq (sigma i) (tau i)) ->
  (e : Expr g) -> Eq (substExpr sigma e) (substExpr tau e)
substExpr-ext sigma tau ext (Var i)      = ext i
substExpr-ext sigma tau ext U            = refl
substExpr-ext sigma tau ext (Pi A B)     =
  Eq-cong2-Expr Pi (substExpr-ext sigma tau ext A)
    (substExpr-ext (liftSub sigma) (liftSub tau) (liftSub-ext sigma tau ext) B)
substExpr-ext sigma tau ext (Lam A M)    =
  Eq-cong2-Expr Lam (substExpr-ext sigma tau ext A)
    (substExpr-ext (liftSub sigma) (liftSub tau) (liftSub-ext sigma tau ext) M)
substExpr-ext sigma tau ext (App f a)    =
  Eq-cong2-Expr App (substExpr-ext sigma tau ext f)
    (substExpr-ext sigma tau ext a)
substExpr-ext sigma tau ext (Id A B)     =
  Eq-cong2-Expr Id (substExpr-ext sigma tau ext A) (substExpr-ext sigma tau ext B)
substExpr-ext sigma tau ext refl         = refl
substExpr-ext sigma tau ext (sym p)      = Eq-cong sym (substExpr-ext sigma tau ext p)
substExpr-ext sigma tau ext (pi1 p)      = Eq-cong pi1 (substExpr-ext sigma tau ext p)
substExpr-ext sigma tau ext (pi2 p N)    =
  Eq-cong2-Expr pi2 (substExpr-ext sigma tau ext p) (substExpr-ext sigma tau ext N)
substExpr-ext sigma tau ext (cast A B p M) =
  Eq-cong4-Expr cast (substExpr-ext sigma tau ext A) (substExpr-ext sigma tau ext B)
    (substExpr-ext sigma tau ext p) (substExpr-ext sigma tau ext M)

------------------------------------------------------------------------
-- Renaming extensionality and composition
------------------------------------------------------------------------

liftRen-ext : {n m : Nat} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (j : Fin (suc n)) -> Eq (liftRen r1 j) (liftRen r2 j)
liftRen-ext r1 r2 ext fzero    = refl
liftRen-ext r1 r2 ext (fsuc i) = Eq-cong fsuc (ext i)

renExpr-ext : {n m : Nat} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (e : Expr n) -> Eq (renExpr r1 e) (renExpr r2 e)
renExpr-ext r1 r2 ext (Var i)      = Eq-cong Var (ext i)
renExpr-ext r1 r2 ext U            = refl
renExpr-ext r1 r2 ext (Pi A B)     =
  Eq-cong2-Expr Pi (renExpr-ext r1 r2 ext A)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 ext) B)
renExpr-ext r1 r2 ext (Lam A M)    =
  Eq-cong2-Expr Lam (renExpr-ext r1 r2 ext A)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 ext) M)
renExpr-ext r1 r2 ext (App f a)    =
  Eq-cong2-Expr App (renExpr-ext r1 r2 ext f)
    (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (Id A B)     =
  Eq-cong2-Expr Id (renExpr-ext r1 r2 ext A) (renExpr-ext r1 r2 ext B)
renExpr-ext r1 r2 ext refl         = refl
renExpr-ext r1 r2 ext (sym p)      = Eq-cong sym (renExpr-ext r1 r2 ext p)
renExpr-ext r1 r2 ext (pi1 p)      = Eq-cong pi1 (renExpr-ext r1 r2 ext p)
renExpr-ext r1 r2 ext (pi2 p N)    =
  Eq-cong2-Expr pi2 (renExpr-ext r1 r2 ext p) (renExpr-ext r1 r2 ext N)
renExpr-ext r1 r2 ext (cast A B p M) =
  Eq-cong4-Expr cast (renExpr-ext r1 r2 ext A) (renExpr-ext r1 r2 ext B)
    (renExpr-ext r1 r2 ext p) (renExpr-ext r1 r2 ext M)

ren-ren : {n m k : Nat} (r1 : Ren m k) (r2 : Ren n m) (e : Expr n) ->
  Eq (renExpr r1 (renExpr r2 e)) (renExpr (\ i -> r1 (r2 i)) e)
ren-ren r1 r2 (Var i)      = refl
ren-ren r1 r2 U            = refl
ren-ren r1 r2 (Pi A B)     =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      ihB' = renExpr-ext
               (\ j -> liftRen r1 (liftRen r2 j))
               (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl })
               B
  in Eq-cong2-Expr Pi ihA (Eq-trans ihB ihB')
ren-ren r1 r2 (Lam A M)    =
  let ihA = ren-ren r1 r2 A
      ihM = ren-ren (liftRen r1) (liftRen r2) M
      ihM' = renExpr-ext
               (\ j -> liftRen r1 (liftRen r2 j))
               (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl })
               M
  in Eq-cong2-Expr Lam ihA (Eq-trans ihM ihM')
ren-ren r1 r2 (App f a)    =
  Eq-cong2-Expr App (ren-ren r1 r2 f) (ren-ren r1 r2 a)
ren-ren r1 r2 (Id A B)     =
  Eq-cong2-Expr Id (ren-ren r1 r2 A) (ren-ren r1 r2 B)
ren-ren r1 r2 refl         = refl
ren-ren r1 r2 (sym p)      = Eq-cong sym (ren-ren r1 r2 p)
ren-ren r1 r2 (pi1 p)      = Eq-cong pi1 (ren-ren r1 r2 p)
ren-ren r1 r2 (pi2 p N)    = Eq-cong2-Expr pi2 (ren-ren r1 r2 p) (ren-ren r1 r2 N)
ren-ren r1 r2 (cast A B p M) =
  Eq-cong4-Expr cast (ren-ren r1 r2 A) (ren-ren r1 r2 B) (ren-ren r1 r2 p) (ren-ren r1 r2 M)

------------------------------------------------------------------------
-- Substitution/renaming interaction
------------------------------------------------------------------------

subst-ren : {h g k : Nat} (sigma : Sub h g) (r : Ren k g) (e : Expr k) ->
  Eq (substExpr sigma (renExpr r e)) (substExpr (\ i -> sigma (r i)) e)
subst-ren sigma r (Var i)      = refl
subst-ren sigma r U            = refl
subst-ren sigma r (Pi A B)     =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      ihB' = substExpr-ext
               (\ j -> liftSub sigma (liftRen r j))
               (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl })
               B
  in Eq-cong2-Expr Pi ihA (Eq-trans ihB ihB')
subst-ren sigma r (Lam A M)    =
  let ihA = subst-ren sigma r A
      ihM = subst-ren (liftSub sigma) (liftRen r) M
      ihM' = substExpr-ext
               (\ j -> liftSub sigma (liftRen r j))
               (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl })
               M
  in Eq-cong2-Expr Lam ihA (Eq-trans ihM ihM')
subst-ren sigma r (App f a)    =
  Eq-cong2-Expr App (subst-ren sigma r f) (subst-ren sigma r a)
subst-ren sigma r (Id A B)     =
  Eq-cong2-Expr Id (subst-ren sigma r A) (subst-ren sigma r B)
subst-ren sigma r refl         = refl
subst-ren sigma r (sym p)      = Eq-cong sym (subst-ren sigma r p)
subst-ren sigma r (pi1 p)      = Eq-cong pi1 (subst-ren sigma r p)
subst-ren sigma r (pi2 p N)    = Eq-cong2-Expr pi2 (subst-ren sigma r p) (subst-ren sigma r N)
subst-ren sigma r (cast A B p M) =
  Eq-cong4-Expr cast (subst-ren sigma r A) (subst-ren sigma r B)
    (subst-ren sigma r p) (subst-ren sigma r M)

------------------------------------------------------------------------
-- Renaming after substitution
------------------------------------------------------------------------

ren-wk-comm : {n m : Nat} (r : Ren n m) (e : Expr n) ->
  Eq (renExpr (liftRen r) (wkExpr e)) (wkExpr (renExpr r e))
ren-wk-comm r e =
  let step1 = ren-ren (liftRen r) wkRen e
      step2 = Eq-sym (ren-ren wkRen r e)
  in Eq-trans step1 step2

liftSub-ren-ext : {h g k : Nat} (r : Ren g k) (sigma : Sub g h) ->
  (j : Fin (suc h)) ->
  Eq (renExpr (liftRen r) (liftSub sigma j))
     (liftSub (\ i -> renExpr r (sigma i)) j)
liftSub-ren-ext r sigma fzero    = refl
liftSub-ren-ext r sigma (fsuc i) = ren-wk-comm r (sigma i)

ren-subst : {h g k : Nat} (r : Ren g k) (sigma : Sub g h) (e : Expr h) ->
  Eq (renExpr r (substExpr sigma e)) (substExpr (\ i -> renExpr r (sigma i)) e)
ren-subst r sigma (Var i)      = refl
ren-subst r sigma U            = refl
ren-subst r sigma (Pi A B)     =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      ihB' = substExpr-ext
               (\ j -> renExpr (liftRen r) (liftSub sigma j))
               (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma)
               B
  in Eq-cong2-Expr Pi ihA (Eq-trans ihB ihB')
ren-subst r sigma (Lam A M)    =
  let ihA = ren-subst r sigma A
      ihM = ren-subst (liftRen r) (liftSub sigma) M
      ihM' = substExpr-ext
               (\ j -> renExpr (liftRen r) (liftSub sigma j))
               (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma)
               M
  in Eq-cong2-Expr Lam ihA (Eq-trans ihM ihM')
ren-subst r sigma (App f a)    =
  Eq-cong2-Expr App (ren-subst r sigma f) (ren-subst r sigma a)
ren-subst r sigma (Id A B)     =
  Eq-cong2-Expr Id (ren-subst r sigma A) (ren-subst r sigma B)
ren-subst r sigma refl         = refl
ren-subst r sigma (sym p)      = Eq-cong sym (ren-subst r sigma p)
ren-subst r sigma (pi1 p)      = Eq-cong pi1 (ren-subst r sigma p)
ren-subst r sigma (pi2 p N)    = Eq-cong2-Expr pi2 (ren-subst r sigma p) (ren-subst r sigma N)
ren-subst r sigma (cast A B p M) =
  Eq-cong4-Expr cast (ren-subst r sigma A) (ren-subst r sigma B)
    (ren-subst r sigma p) (ren-subst r sigma M)

------------------------------------------------------------------------
-- Substitution composition
------------------------------------------------------------------------

subst-wk-comm : {h g : Nat} (tau : Sub g h) (e : Expr h) ->
  Eq (substExpr (liftSub tau) (wkExpr e)) (wkExpr (substExpr tau e))
subst-wk-comm tau e =
  let step1 = subst-ren (liftSub tau) wkRen e
      step2 = Eq-sym (ren-subst wkRen tau e)
  in Eq-trans step1 step2

liftSub-subst-ext : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h) ->
  (j : Fin (suc h)) ->
  Eq (substExpr (liftSub tau) (liftSub sigma j))
     (liftSub (\ i -> substExpr tau (sigma i)) j)
liftSub-subst-ext tau sigma fzero    = refl
liftSub-subst-ext tau sigma (fsuc i) = subst-wk-comm tau (sigma i)

subst-subst : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h) (e : Expr h) ->
  Eq (substExpr tau (substExpr sigma e)) (substExpr (\ i -> substExpr tau (sigma i)) e)
subst-subst tau sigma (Var i)      = refl
subst-subst tau sigma U            = refl
subst-subst tau sigma (Pi A B)     =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      ihB' = substExpr-ext
               (\ j -> substExpr (liftSub tau) (liftSub sigma j))
               (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma)
               B
  in Eq-cong2-Expr Pi ihA (Eq-trans ihB ihB')
subst-subst tau sigma (Lam A M)    =
  let ihA = subst-subst tau sigma A
      ihM = subst-subst (liftSub tau) (liftSub sigma) M
      ihM' = substExpr-ext
               (\ j -> substExpr (liftSub tau) (liftSub sigma j))
               (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma)
               M
  in Eq-cong2-Expr Lam ihA (Eq-trans ihM ihM')
subst-subst tau sigma (App f a)    =
  Eq-cong2-Expr App (subst-subst tau sigma f) (subst-subst tau sigma a)
subst-subst tau sigma (Id A B)     =
  Eq-cong2-Expr Id (subst-subst tau sigma A) (subst-subst tau sigma B)
subst-subst tau sigma refl         = refl
subst-subst tau sigma (sym p)      = Eq-cong sym (subst-subst tau sigma p)
subst-subst tau sigma (pi1 p)      = Eq-cong pi1 (subst-subst tau sigma p)
subst-subst tau sigma (pi2 p N)    =
  Eq-cong2-Expr pi2 (subst-subst tau sigma p) (subst-subst tau sigma N)
subst-subst tau sigma (cast A B p M) =
  Eq-cong4-Expr cast (subst-subst tau sigma A) (subst-subst tau sigma B)
    (subst-subst tau sigma p) (subst-subst tau sigma M)
