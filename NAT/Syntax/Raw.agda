{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RawSyntax.agda  (NAT/ — Pi + U fragment)
--
-- Raw syntax with only Pi and U. No Sigma, no Prop.
------------------------------------------------------------------------

module NAT.Syntax.Raw where

open import NAT.Domain.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ; Eq-transport ; Eq-sym)

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
  Y      : {n : Nat} -> Expr n -> Expr n
  NatT   : {n : Nat} -> Expr n
  Zero   : {n : Nat} -> Expr n
  Suc    : {n : Nat} -> Expr n -> Expr n
  -- caseNat M a b : scrutinee M, zero-branch a, succ-branch b (applied to the predecessor)
  Case   : {n : Nat} -> Expr n -> Expr n -> Expr n -> Expr n

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
renExpr r (Y g)        = Y (renExpr r g)
renExpr r NatT          = NatT
renExpr r Zero         = Zero
renExpr r (Suc m)      = Suc (renExpr r m)
renExpr r (Case M a b) = Case (renExpr r M) (renExpr r a) (renExpr r b)

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
substExpr sigma (Y g)        = Y (substExpr sigma g)
substExpr sigma NatT          = NatT
substExpr sigma Zero         = Zero
substExpr sigma (Suc m)      = Suc (substExpr sigma m)
substExpr sigma (Case M a b) = Case (substExpr sigma M) (substExpr sigma a) (substExpr sigma b)

------------------------------------------------------------------------
-- Unary substitution
------------------------------------------------------------------------

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub s fzero    = s
subst1Sub s (fsuc i) = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 M s = substExpr (subst1Sub s) M

------------------------------------------------------------------------
-- Successor substitution (for the dependent caseNat motive):
--   subSucC C = C[x := S x]   over the same extended context.
-- If C : Nat ⊢ U is the motive, then subSucC C is the codomain of the
-- succ branch's type Π(n:Nat) C[S n], and subst1 (subSucC C) m = C[S m].
------------------------------------------------------------------------

sucSub : {n : Nat} -> Sub (suc n) (suc n)
sucSub fzero    = Suc (Var fzero)
sucSub (fsuc i) = Var (fsuc i)

subSucC : {n : Nat} -> Expr (suc n) -> Expr (suc n)
subSucC C = substExpr sucSub C

------------------------------------------------------------------------
-- Equality helpers
------------------------------------------------------------------------

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans refl refl = refl

Eq-cong2-Expr : {n m : Nat} (c : Expr n -> Expr m -> Expr n) ->
  {a a' : Expr n} {b b' : Expr m} ->
  Eq a a' -> Eq b b' -> Eq (c a b) (c a' b')
Eq-cong2-Expr c refl refl = refl

Eq-cong3 : {A B C D : Set} (f : A -> B -> C -> D) ->
  {a a' : A} {b b' : B} {c c' : C} ->
  Eq a a' -> Eq b b' -> Eq c c' -> Eq (f a b c) (f a' b' c')
Eq-cong3 f refl refl refl = refl

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
substExpr-ext sigma tau ext (Y g)        =
  Eq-cong Y (substExpr-ext sigma tau ext g)
substExpr-ext sigma tau ext NatT          = refl
substExpr-ext sigma tau ext Zero         = refl
substExpr-ext sigma tau ext (Suc m)      = Eq-cong Suc (substExpr-ext sigma tau ext m)
substExpr-ext sigma tau ext (Case M a b) =
  Eq-cong3 Case (substExpr-ext sigma tau ext M)
    (substExpr-ext sigma tau ext a) (substExpr-ext sigma tau ext b)

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
renExpr-ext r1 r2 ext (Y g)        =
  Eq-cong Y (renExpr-ext r1 r2 ext g)
renExpr-ext r1 r2 ext NatT          = refl
renExpr-ext r1 r2 ext Zero         = refl
renExpr-ext r1 r2 ext (Suc m)      = Eq-cong Suc (renExpr-ext r1 r2 ext m)
renExpr-ext r1 r2 ext (Case M a b) =
  Eq-cong3 Case (renExpr-ext r1 r2 ext M)
    (renExpr-ext r1 r2 ext a) (renExpr-ext r1 r2 ext b)

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
ren-ren r1 r2 (Y g)        =
  Eq-cong Y (ren-ren r1 r2 g)
ren-ren r1 r2 NatT          = refl
ren-ren r1 r2 Zero         = refl
ren-ren r1 r2 (Suc m)      = Eq-cong Suc (ren-ren r1 r2 m)
ren-ren r1 r2 (Case M a b) =
  Eq-cong3 Case (ren-ren r1 r2 M) (ren-ren r1 r2 a) (ren-ren r1 r2 b)

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
subst-ren sigma r (Y g)        =
  Eq-cong Y (subst-ren sigma r g)
subst-ren sigma r NatT          = refl
subst-ren sigma r Zero         = refl
subst-ren sigma r (Suc m)      = Eq-cong Suc (subst-ren sigma r m)
subst-ren sigma r (Case M a b) =
  Eq-cong3 Case (subst-ren sigma r M) (subst-ren sigma r a) (subst-ren sigma r b)

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
ren-subst r sigma (Y g)        =
  Eq-cong Y (ren-subst r sigma g)
ren-subst r sigma NatT          = refl
ren-subst r sigma Zero         = refl
ren-subst r sigma (Suc m)      = Eq-cong Suc (ren-subst r sigma m)
ren-subst r sigma (Case M a b) =
  Eq-cong3 Case (ren-subst r sigma M) (ren-subst r sigma a) (ren-subst r sigma b)

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
subst-subst tau sigma (Y g)        =
  Eq-cong Y (subst-subst tau sigma g)
subst-subst tau sigma NatT          = refl
subst-subst tau sigma Zero         = refl
subst-subst tau sigma (Suc m)      = Eq-cong Suc (subst-subst tau sigma m)
subst-subst tau sigma (Case M a b) =
  Eq-cong3 Case (subst-subst tau sigma M) (subst-subst tau sigma a) (subst-subst tau sigma b)

------------------------------------------------------------------------
-- Renaming as substitution by variables, and lemmas about subSucC
------------------------------------------------------------------------

-- A renaming acts as the substitution by the corresponding variables.
ren-as-subst : {n m : Nat} (r : Ren n m) (e : Expr n) ->
  Eq (renExpr r e) (substExpr (\ i -> Var (r i)) e)
ren-as-subst r (Var i)      = refl
ren-as-subst r U            = refl
ren-as-subst r (Pi A B)     =
  Eq-cong2-Expr Pi (ren-as-subst r A)
    (Eq-trans (ren-as-subst (liftRen r) B)
      (substExpr-ext _ _ (\ { fzero -> refl ; (fsuc i) -> refl }) B))
ren-as-subst r (Lam A M)    =
  Eq-cong2-Expr Lam (ren-as-subst r A)
    (Eq-trans (ren-as-subst (liftRen r) M)
      (substExpr-ext _ _ (\ { fzero -> refl ; (fsuc i) -> refl }) M))
ren-as-subst r (App f a)    =
  Eq-cong2-Expr App (ren-as-subst r f) (ren-as-subst r a)
ren-as-subst r (Y g)        = Eq-cong Y (ren-as-subst r g)
ren-as-subst r NatT          = refl
ren-as-subst r Zero         = refl
ren-as-subst r (Suc m)      = Eq-cong Suc (ren-as-subst r m)
ren-as-subst r (Case M a b) =
  Eq-cong3 Case (ren-as-subst r M) (ren-as-subst r a) (ren-as-subst r b)

-- sucSub absorbs a weakening: substExpr sucSub (wkExpr e) = wkExpr e.
sucSub-wk : {n : Nat} (e : Expr n) -> Eq (substExpr sucSub (wkExpr e)) (wkExpr e)
sucSub-wk e =
  Eq-trans (subst-ren sucSub wkRen e)
    (Eq-trans (substExpr-ext (\ i -> sucSub (wkRen i)) (\ i -> Var (fsuc i)) (\ i -> refl) e)
      (Eq-sym (ren-as-subst wkRen e)))

-- subst1 (subSucC C) m = subst1 C (Suc m)  (the succ-branch type identity).
subSucC-subst1 : {n : Nat} (C : Expr (suc n)) (m : Expr n) ->
  Eq (subst1 (subSucC C) m) (subst1 C (Suc m))
subSucC-subst1 C m =
  Eq-trans (subst-subst (subst1Sub m) sucSub C)
    (substExpr-ext _ (subst1Sub (Suc m)) (\ { fzero -> refl ; (fsuc i) -> refl }) C)

-- subSucC commutes with a lifted renaming.
subSucC-ren : {h g : Nat} (r : Ren h g) (C : Expr (suc h)) ->
  Eq (renExpr (liftRen r) (subSucC C)) (subSucC (renExpr (liftRen r) C))
subSucC-ren r C =
  Eq-trans (ren-subst (liftRen r) sucSub C)
    (Eq-trans (substExpr-ext _ _ (\ { fzero -> refl ; (fsuc i) -> refl }) C)
      (Eq-sym (subst-ren sucSub (liftRen r) C)))

-- subSucC commutes with a lifted substitution.
subSucC-subst : {h g : Nat} (sigma : Sub h g) (C : Expr (suc g)) ->
  Eq (substExpr (liftSub sigma) (subSucC C)) (subSucC (substExpr (liftSub sigma) C))
subSucC-subst sigma C =
  Eq-trans (subst-subst (liftSub sigma) sucSub C)
    (Eq-trans (substExpr-ext _ _ ext C)
      (Eq-sym (subst-subst sucSub (liftSub sigma) C)))
  where
    ext : (i : Fin _) ->
      Eq (substExpr (liftSub sigma) (sucSub i)) (substExpr sucSub (liftSub sigma i))
    ext fzero    = refl
    ext (fsuc j) = Eq-sym (sucSub-wk (sigma j))
