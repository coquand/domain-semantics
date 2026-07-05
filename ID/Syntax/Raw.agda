{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RawSyntax.agda  (MIN/ — Pi + U fragment)
--
-- Raw syntax with only Pi and U. No Sigma, no Prop.
------------------------------------------------------------------------

module ID.Syntax.Raw where

open import ID.Domain.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ; Eq-transport ; Eq-sym)

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
  -- Element-level Martin-Lof identity: Id A a b : U (A : U ; a b : A)
  Id     : {n : Nat} -> Expr n -> Expr n -> Expr n -> Expr n
  Ref    : {n : Nat} -> Expr n -> Expr n                       -- Ref a : Id A a a
  -- Based-J eliminator: J C d p, motive C : (x:A) -> Id A a x -> U
  J      : {n : Nat} -> Expr n -> Expr n -> Expr n -> Expr n

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
renExpr r (Id A a b)   = Id (renExpr r A) (renExpr r a) (renExpr r b)
renExpr r (Ref a)      = Ref (renExpr r a)
renExpr r (J C d p)    = J (renExpr r C) (renExpr r d) (renExpr r p)

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
substExpr sigma (Id A a b)   = Id (substExpr sigma A) (substExpr sigma a) (substExpr sigma b)
substExpr sigma (Ref a)      = Ref (substExpr sigma a)
substExpr sigma (J C d p)    = J (substExpr sigma C) (substExpr sigma d) (substExpr sigma p)

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
  {a a' b b' d d' : Expr n} ->
  Eq a a' -> Eq b b' -> Eq d d' -> Eq (c a b d) (c a' b' d')
Eq-cong3-Expr c refl refl refl = refl

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
substExpr-ext sigma tau ext (Id A a b)   =
  Eq-cong3-Expr Id (substExpr-ext sigma tau ext A)
    (substExpr-ext sigma tau ext a) (substExpr-ext sigma tau ext b)
substExpr-ext sigma tau ext (Ref a)      =
  Eq-cong Ref (substExpr-ext sigma tau ext a)
substExpr-ext sigma tau ext (J C d p)    =
  Eq-cong3-Expr J (substExpr-ext sigma tau ext C)
    (substExpr-ext sigma tau ext d) (substExpr-ext sigma tau ext p)

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
renExpr-ext r1 r2 ext (Id A a b)   =
  Eq-cong3-Expr Id (renExpr-ext r1 r2 ext A)
    (renExpr-ext r1 r2 ext a) (renExpr-ext r1 r2 ext b)
renExpr-ext r1 r2 ext (Ref a)      =
  Eq-cong Ref (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (J C d p)    =
  Eq-cong3-Expr J (renExpr-ext r1 r2 ext C)
    (renExpr-ext r1 r2 ext d) (renExpr-ext r1 r2 ext p)

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
ren-ren r1 r2 (Id A a b)   =
  Eq-cong3-Expr Id (ren-ren r1 r2 A) (ren-ren r1 r2 a) (ren-ren r1 r2 b)
ren-ren r1 r2 (Ref a)      = Eq-cong Ref (ren-ren r1 r2 a)
ren-ren r1 r2 (J C d p)    =
  Eq-cong3-Expr J (ren-ren r1 r2 C) (ren-ren r1 r2 d) (ren-ren r1 r2 p)

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
subst-ren sigma r (Id A a b)   =
  Eq-cong3-Expr Id (subst-ren sigma r A) (subst-ren sigma r a) (subst-ren sigma r b)
subst-ren sigma r (Ref a)      = Eq-cong Ref (subst-ren sigma r a)
subst-ren sigma r (J C d p)    =
  Eq-cong3-Expr J (subst-ren sigma r C) (subst-ren sigma r d) (subst-ren sigma r p)

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
ren-subst r sigma (Id A a b)   =
  Eq-cong3-Expr Id (ren-subst r sigma A) (ren-subst r sigma a) (ren-subst r sigma b)
ren-subst r sigma (Ref a)      = Eq-cong Ref (ren-subst r sigma a)
ren-subst r sigma (J C d p)    =
  Eq-cong3-Expr J (ren-subst r sigma C) (ren-subst r sigma d) (ren-subst r sigma p)

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
subst-subst tau sigma (Id A a b)   =
  Eq-cong3-Expr Id (subst-subst tau sigma A) (subst-subst tau sigma a) (subst-subst tau sigma b)
subst-subst tau sigma (Ref a)      = Eq-cong Ref (subst-subst tau sigma a)
subst-subst tau sigma (J C d p)    =
  Eq-cong3-Expr J (subst-subst tau sigma C) (subst-subst tau sigma d) (subst-subst tau sigma p)

------------------------------------------------------------------------
-- ML original J: dependent motive / base type encodings + their
-- renaming/substitution commutation lemmas (used by ty-J/conv-J).
--   motiveTy A   = (x y : A) -> Id A x y -> U
--   baseTy A C   = (x : A) -> C x x (Ref x)
--   result type of  J C d p  is  App (App (App C a) b) p  (binder-free,
--   substitutes definitionally, so no lemma needed there).
------------------------------------------------------------------------

motiveTy : {n : Nat} -> Expr n -> Expr n
motiveTy A = Pi A (Pi (wkExpr A) (Pi (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)) U))

baseTy : {n : Nat} -> Expr n -> Expr n -> Expr n
baseTy A C = Pi A (App (App (App (wkExpr C) (Var fzero)) (Var fzero)) (Ref (Var fzero)))

ren-motiveTy : {n m : Nat} (r : Ren n m) (A : Expr n) ->
  Eq (renExpr r (motiveTy A)) (motiveTy (renExpr r A))
ren-motiveTy r A =
  Eq-cong2-Expr Pi refl
    (Eq-cong2-Expr Pi (ren-wk-comm r A)
      (Eq-cong2-Expr Pi
        (Eq-cong3-Expr Id
          (Eq-trans (ren-wk-comm (liftRen r) (wkExpr A)) (Eq-cong wkExpr (ren-wk-comm r A)))
          refl refl)
        refl))

subst-motiveTy : {h g : Nat} (s : Sub g h) (A : Expr h) ->
  Eq (substExpr s (motiveTy A)) (motiveTy (substExpr s A))
subst-motiveTy s A =
  Eq-cong2-Expr Pi refl
    (Eq-cong2-Expr Pi (subst-wk-comm s A)
      (Eq-cong2-Expr Pi
        (Eq-cong3-Expr Id
          (Eq-trans (subst-wk-comm (liftSub s) (wkExpr A)) (Eq-cong wkExpr (subst-wk-comm s A)))
          refl refl)
        refl))

ren-baseTy : {n m : Nat} (r : Ren n m) (A C : Expr n) ->
  Eq (renExpr r (baseTy A C)) (baseTy (renExpr r A) (renExpr r C))
ren-baseTy r A C =
  Eq-cong2-Expr Pi refl
    (Eq-cong2-Expr App
      (Eq-cong2-Expr App
        (Eq-cong2-Expr App (ren-wk-comm r C) refl)
        refl)
      refl)

subst-baseTy : {h g : Nat} (s : Sub g h) (A C : Expr h) ->
  Eq (substExpr s (baseTy A C)) (baseTy (substExpr s A) (substExpr s C))
subst-baseTy s A C =
  Eq-cong2-Expr Pi refl
    (Eq-cong2-Expr App
      (Eq-cong2-Expr App
        (Eq-cong2-Expr App (subst-wk-comm s C) refl)
        refl)
      refl)
