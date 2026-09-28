{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.Core
--
-- The core syntax interpreted by the finite-element model: MIN's raw
-- syntax (MIN/Syntax/Raw.agda) with a LEVEL on the universe.  Russell
-- terms are mapped here by BCDE4.Model.Strip, which forgets the
-- codomain annotations of λ and application (the model ignores them).
------------------------------------------------------------------------

module BCDE4.Model.Core where

open import BCDE4.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ; Eq-cong2 ; Eq-transport ; Eq-sym)
open import BCDE4.Basic public using (Fin ; fzero ; fsuc ; Ren ; liftRen ; wkRen)
open import BCDE4.Levels

------------------------------------------------------------------------
-- Fin — de Bruijn variables
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Expr — raw expressions
------------------------------------------------------------------------

data Expr : Nat -> Set where
  Var    : {n : Nat} -> Fin n -> Expr n
  U      : {n : Nat} -> LExpr -> Expr n
  Pi     : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  Lam    : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  App    : {n : Nat} -> Expr n -> Expr n -> Expr n
  Grd    : {n : Nat} -> Constr -> Expr n -> Expr n
  GLam   : {n : Nat} -> Constr -> Expr n -> Expr n
  Emp    : {n : Nat} -> Expr n
  LPi    : {n : Nat} -> Expr n -> Expr n            -- [α]A  (binds level 0)
  LLam   : {n : Nat} -> Expr n -> Expr n            -- ⟨α⟩u
  LApp   : {n : Nat} -> Expr n -> LExpr -> Expr n   -- t l

------------------------------------------------------------------------
-- Ren — renamings
------------------------------------------------------------------------


renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)      = Var (r i)
renExpr r (U l)        = U l
renExpr r (Grd c A)    = Grd c (renExpr r A)
renExpr r (GLam c t)   = GLam c (renExpr r t)
renExpr r Emp          = Emp
renExpr r (LPi A)      = LPi (renExpr r A)
renExpr r (LLam u)     = LLam (renExpr r u)
renExpr r (LApp t l)   = LApp (renExpr r t) l
renExpr r (Pi A B)     = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A M)    = Lam (renExpr r A) (renExpr (liftRen r) M)
renExpr r (App f a)    = App (renExpr r f) (renExpr r a)

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------


wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

lsubE : {n : Nat} -> LSub -> Expr n -> Expr n
lsubE z (Var i)    = Var i
lsubE z (U l)      = U (lsubL z l)
lsubE z (Pi A B)   = Pi (lsubE z A) (lsubE z B)
lsubE z (Lam A M)  = Lam (lsubE z A) (lsubE z M)
lsubE z (App f a)  = App (lsubE z f) (lsubE z a)
lsubE z (Grd c A)  = Grd (lsubC z c) (lsubE z A)
lsubE z (GLam c t) = GLam (lsubC z c) (lsubE z t)
lsubE z Emp        = Emp
lsubE z (LPi A)    = LPi (lsubE (liftL z) A)
lsubE z (LLam u)   = LLam (lsubE (liftL z) u)
lsubE z (LApp t l) = LApp (lsubE z t) (lsubL z l)

lshiftE : {n : Nat} -> Expr n -> Expr n
lshiftE = lsubE lwkS

lsub1 : {n : Nat} -> Expr n -> LExpr -> Expr n
lsub1 A l = lsubE (lsub1S l) A

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
substExpr sigma (U l)        = U l
substExpr sigma (Grd c A)  = Grd c (substExpr sigma A)
substExpr sigma (GLam c t) = GLam c (substExpr sigma t)
substExpr sigma Emp        = Emp
substExpr sigma (LPi A)    = LPi (substExpr (\ i -> lshiftE (sigma i)) A)
substExpr sigma (LLam u)   = LLam (substExpr (\ i -> lshiftE (sigma i)) u)
substExpr sigma (LApp t l) = LApp (substExpr sigma t) l
substExpr sigma (Pi A B)     = Pi (substExpr sigma A) (substExpr (liftSub sigma) B)
substExpr sigma (Lam A M)    = Lam (substExpr sigma A) (substExpr (liftSub sigma) M)
substExpr sigma (App f a)    = App (substExpr sigma f) (substExpr sigma a)

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
substExpr-ext sigma tau ext (U l)        = refl
substExpr-ext sigma tau ext (Grd c A)  = Eq-cong (Grd c) (substExpr-ext sigma tau ext A)
substExpr-ext sigma tau ext (GLam c t) = Eq-cong (GLam c) (substExpr-ext sigma tau ext t)
substExpr-ext sigma tau ext Emp        = refl
substExpr-ext sigma tau ext (LPi A)  = Eq-cong LPi (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) A)
substExpr-ext sigma tau ext (LLam u) = Eq-cong LLam (substExpr-ext _ _ (\ i -> Eq-cong lshiftE (ext i)) u)
substExpr-ext sigma tau ext (LApp t l) = Eq-cong (\ X -> LApp X l) (substExpr-ext sigma tau ext t)
substExpr-ext sigma tau ext (Pi A B)     =
  Eq-cong2-Expr Pi (substExpr-ext sigma tau ext A)
    (substExpr-ext (liftSub sigma) (liftSub tau) (liftSub-ext sigma tau ext) B)
substExpr-ext sigma tau ext (Lam A M)    =
  Eq-cong2-Expr Lam (substExpr-ext sigma tau ext A)
    (substExpr-ext (liftSub sigma) (liftSub tau) (liftSub-ext sigma tau ext) M)
substExpr-ext sigma tau ext (App f a)    =
  Eq-cong2-Expr App (substExpr-ext sigma tau ext f)
    (substExpr-ext sigma tau ext a)

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
renExpr-ext r1 r2 ext (U l)        = refl
renExpr-ext r1 r2 ext (Grd c A)  = Eq-cong (Grd c) (renExpr-ext r1 r2 ext A)
renExpr-ext r1 r2 ext (GLam c t) = Eq-cong (GLam c) (renExpr-ext r1 r2 ext t)
renExpr-ext r1 r2 ext Emp        = refl
renExpr-ext r1 r2 ext (LPi A)  = Eq-cong LPi (renExpr-ext r1 r2 ext A)
renExpr-ext r1 r2 ext (LLam u) = Eq-cong LLam (renExpr-ext r1 r2 ext u)
renExpr-ext r1 r2 ext (LApp t l) = Eq-cong (\ X -> LApp X l) (renExpr-ext r1 r2 ext t)
renExpr-ext r1 r2 ext (Pi A B)     =
  Eq-cong2-Expr Pi (renExpr-ext r1 r2 ext A)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 ext) B)
renExpr-ext r1 r2 ext (Lam A M)    =
  Eq-cong2-Expr Lam (renExpr-ext r1 r2 ext A)
    (renExpr-ext (liftRen r1) (liftRen r2) (liftRen-ext r1 r2 ext) M)
renExpr-ext r1 r2 ext (App f a)    =
  Eq-cong2-Expr App (renExpr-ext r1 r2 ext f)
    (renExpr-ext r1 r2 ext a)

------------------------------------------------------------------------
-- Level substitution laws (as in BCDE4.RussellSyntax)
------------------------------------------------------------------------

liftL-ext : (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (i : Nat) -> Eq (liftL z i) (liftL z' i)
liftL-ext z z' e zero    = refl
liftL-ext z z' e (suc i) = Eq-cong lshift (e i)

lsubE-ext : {n : Nat} (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (M : Expr n) ->
  Eq (lsubE z M) (lsubE z' M)
lsubE-ext z z' e (Var i)    = refl
lsubE-ext z z' e (U l)      = Eq-cong U (lsubL-ext z z' e l)
lsubE-ext z z' e (Pi A B)   = Eq-cong2-Expr Pi (lsubE-ext z z' e A) (lsubE-ext z z' e B)
lsubE-ext z z' e (Lam A M)  = Eq-cong2-Expr Lam (lsubE-ext z z' e A) (lsubE-ext z z' e M)
lsubE-ext z z' e (App f a)  = Eq-cong2-Expr App (lsubE-ext z z' e f) (lsubE-ext z z' e a)
lsubE-ext z z' e (Grd c A)  = Eq-cong2 Grd (lsubC-ext z z' e c) (lsubE-ext z z' e A)
lsubE-ext z z' e (GLam c t) = Eq-cong2 GLam (lsubC-ext z z' e c) (lsubE-ext z z' e t)
lsubE-ext z z' e Emp        = refl
lsubE-ext z z' e (LPi A)    = Eq-cong LPi (lsubE-ext _ _ (liftL-ext z z' e) A)
lsubE-ext z z' e (LLam u)   = Eq-cong LLam (lsubE-ext _ _ (liftL-ext z z' e) u)
lsubE-ext z z' e (LApp t l) = Eq-cong2 LApp (lsubE-ext z z' e t) (lsubL-ext z z' e l)

liftL-comp : (z2 z1 : LSub) (i : Nat) -> Eq (lcomp (liftL z2) (liftL z1) i) (liftL (lcomp z2 z1) i)
liftL-comp z2 z1 zero    = refl
liftL-comp z2 z1 (suc i) = liftL-shift z2 (z1 i)

lsubE-comp : {n : Nat} (z2 z1 : LSub) (M : Expr n) -> Eq (lsubE z2 (lsubE z1 M)) (lsubE (lcomp z2 z1) M)
lsubE-comp z2 z1 (Var i)    = refl
lsubE-comp z2 z1 (U l)      = Eq-cong U (lsubL-comp z2 z1 l)
lsubE-comp z2 z1 (Pi A B)   = Eq-cong2-Expr Pi (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 B)
lsubE-comp z2 z1 (Lam A M)  = Eq-cong2-Expr Lam (lsubE-comp z2 z1 A) (lsubE-comp z2 z1 M)
lsubE-comp z2 z1 (App f a)  = Eq-cong2-Expr App (lsubE-comp z2 z1 f) (lsubE-comp z2 z1 a)
lsubE-comp z2 z1 (Grd c A)  = Eq-cong2 Grd (lsubC-comp z2 z1 c) (lsubE-comp z2 z1 A)
lsubE-comp z2 z1 (GLam c t) = Eq-cong2 GLam (lsubC-comp z2 z1 c) (lsubE-comp z2 z1 t)
lsubE-comp z2 z1 Emp        = refl
lsubE-comp z2 z1 (LPi A)    = Eq-cong LPi (Eq-trans (lsubE-comp _ _ A) (lsubE-ext _ _ (liftL-comp z2 z1) A))
lsubE-comp z2 z1 (LLam u)   = Eq-cong LLam (Eq-trans (lsubE-comp _ _ u) (lsubE-ext _ _ (liftL-comp z2 z1) u))
lsubE-comp z2 z1 (LApp t l) = Eq-cong2 LApp (lsubE-comp z2 z1 t) (lsubL-comp z2 z1 l)

liftL-id : (i : Nat) -> Eq (liftL lidS i) (lidS i)
liftL-id zero    = refl
liftL-id (suc i) = refl

lsubE-id : {n : Nat} (M : Expr n) -> Eq (lsubE lidS M) M
lsubE-id (Var i)    = refl
lsubE-id (U l)      = Eq-cong U (lsubL-id l)
lsubE-id (Pi A B)   = Eq-cong2-Expr Pi (lsubE-id A) (lsubE-id B)
lsubE-id (Lam A M)  = Eq-cong2-Expr Lam (lsubE-id A) (lsubE-id M)
lsubE-id (App f a)  = Eq-cong2-Expr App (lsubE-id f) (lsubE-id a)
lsubE-id (Grd c A)  = Eq-cong2 Grd (lsubC-id c) (lsubE-id A)
lsubE-id (GLam c t) = Eq-cong2 GLam (lsubC-id c) (lsubE-id t)
lsubE-id Emp        = refl
lsubE-id (LPi A)    = Eq-cong LPi (Eq-trans (lsubE-ext _ _ liftL-id A) (lsubE-id A))
lsubE-id (LLam u)   = Eq-cong LLam (Eq-trans (lsubE-ext _ _ liftL-id u) (lsubE-id u))
lsubE-id (LApp t l) = Eq-cong2 LApp (lsubE-id t) (lsubL-id l)

lsubE-ren : {n m : Nat} (z : LSub) (r : Ren n m) (M : Expr n) ->
  Eq (lsubE z (renExpr r M)) (renExpr r (lsubE z M))
lsubE-ren z r (Var i)    = refl
lsubE-ren z r (U l)      = refl
lsubE-ren z r (Pi A B)   = Eq-cong2-Expr Pi (lsubE-ren z r A) (lsubE-ren z (liftRen r) B)
lsubE-ren z r (Lam A M)  = Eq-cong2-Expr Lam (lsubE-ren z r A) (lsubE-ren z (liftRen r) M)
lsubE-ren z r (App f a)  = Eq-cong2-Expr App (lsubE-ren z r f) (lsubE-ren z r a)
lsubE-ren z r (Grd c A)  = Eq-cong (Grd (lsubC z c)) (lsubE-ren z r A)
lsubE-ren z r (GLam c t) = Eq-cong (GLam (lsubC z c)) (lsubE-ren z r t)
lsubE-ren z r Emp        = refl
lsubE-ren z r (LPi A)    = Eq-cong LPi (lsubE-ren (liftL z) r A)
lsubE-ren z r (LLam u)   = Eq-cong LLam (lsubE-ren (liftL z) r u)
lsubE-ren z r (LApp t l) = Eq-cong (\ X -> LApp X (lsubL z l)) (lsubE-ren z r t)

lsubE-liftL-shift : {n : Nat} (z : LSub) (M : Expr n) ->
  Eq (lsubE (liftL z) (lshiftE M)) (lshiftE (lsubE z M))
lsubE-liftL-shift z M = Eq-trans (lsubE-comp (liftL z) lwkS M) (Eq-sym (lsubE-comp lwkS z M))

liftSub-lsub : {h g : Nat} (z : LSub) (sigma : Sub h g) (i : Fin (suc g)) ->
  Eq (lsubE z (liftSub sigma i)) (liftSub (\ j -> lsubE z (sigma j)) i)
liftSub-lsub z sigma fzero    = refl
liftSub-lsub z sigma (fsuc i) = lsubE-ren z wkRen (sigma i)

lsubE-subst : {h g : Nat} (z : LSub) (sigma : Sub h g) (M : Expr g) ->
  Eq (lsubE z (substExpr sigma M)) (substExpr (\ i -> lsubE z (sigma i)) (lsubE z M))
lsubE-subst z sigma (Var i)    = refl
lsubE-subst z sigma (U l)      = refl
lsubE-subst z sigma (Pi A B)   =
  Eq-cong2-Expr Pi (lsubE-subst z sigma A)
    (Eq-trans (lsubE-subst z (liftSub sigma) B) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z B)))
lsubE-subst z sigma (Lam A M)  =
  Eq-cong2-Expr Lam (lsubE-subst z sigma A)
    (Eq-trans (lsubE-subst z (liftSub sigma) M) (substExpr-ext _ _ (liftSub-lsub z sigma) (lsubE z M)))
lsubE-subst z sigma (App f a)  = Eq-cong2-Expr App (lsubE-subst z sigma f) (lsubE-subst z sigma a)
lsubE-subst z sigma (Grd c A)  = Eq-cong (Grd (lsubC z c)) (lsubE-subst z sigma A)
lsubE-subst z sigma (GLam c t) = Eq-cong (GLam (lsubC z c)) (lsubE-subst z sigma t)
lsubE-subst z sigma Emp        = refl
lsubE-subst z sigma (LPi A)    =
  Eq-cong LPi (Eq-trans (lsubE-subst (liftL z) _ A)
    (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) A)))
lsubE-subst z sigma (LLam u)   =
  Eq-cong LLam (Eq-trans (lsubE-subst (liftL z) _ u)
    (substExpr-ext _ _ (\ i -> lsubE-liftL-shift z (sigma i)) (lsubE (liftL z) u)))
lsubE-subst z sigma (LApp t l) = Eq-cong (\ X -> LApp X (lsubL z l)) (lsubE-subst z sigma t)


ren-ren : {n m k : Nat} (r1 : Ren m k) (r2 : Ren n m) (e : Expr n) ->
  Eq (renExpr r1 (renExpr r2 e)) (renExpr (\ i -> r1 (r2 i)) e)
ren-ren r1 r2 (Var i)      = refl
ren-ren r1 r2 (U l)        = refl
ren-ren r1 r2 (Grd c A)  = Eq-cong (Grd c) (ren-ren r1 r2 A)
ren-ren r1 r2 (GLam c t) = Eq-cong (GLam c) (ren-ren r1 r2 t)
ren-ren r1 r2 Emp        = refl
ren-ren r1 r2 (LPi A)  = Eq-cong LPi (ren-ren r1 r2 A)
ren-ren r1 r2 (LLam u) = Eq-cong LLam (ren-ren r1 r2 u)
ren-ren r1 r2 (LApp t l) = Eq-cong (\ X -> LApp X l) (ren-ren r1 r2 t)
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

------------------------------------------------------------------------
-- Substitution/renaming interaction
------------------------------------------------------------------------

subst-ren : {h g k : Nat} (sigma : Sub h g) (r : Ren k g) (e : Expr k) ->
  Eq (substExpr sigma (renExpr r e)) (substExpr (\ i -> sigma (r i)) e)
subst-ren sigma r (Var i)      = refl
subst-ren sigma r (U l)        = refl
subst-ren sigma r (Grd c A)  = Eq-cong (Grd c) (subst-ren sigma r A)
subst-ren sigma r (GLam c t) = Eq-cong (GLam c) (subst-ren sigma r t)
subst-ren sigma r Emp        = refl
subst-ren sigma r (LPi A)  = Eq-cong LPi (subst-ren _ r A)
subst-ren sigma r (LLam u) = Eq-cong LLam (subst-ren _ r u)
subst-ren sigma r (LApp t l) = Eq-cong (\ X -> LApp X l) (subst-ren sigma r t)
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
ren-subst r sigma (U l)        = refl
ren-subst r sigma (Grd c A)  = Eq-cong (Grd c) (ren-subst r sigma A)
ren-subst r sigma (GLam c t) = Eq-cong (GLam c) (ren-subst r sigma t)
ren-subst r sigma Emp        = refl
ren-subst r sigma (LPi A)  =
  Eq-cong LPi (Eq-trans (ren-subst r _ A) (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) A))
ren-subst r sigma (LLam u) =
  Eq-cong LLam (Eq-trans (ren-subst r _ u) (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-ren lwkS r (sigma i))) u))
ren-subst r sigma (LApp t l) = Eq-cong (\ X -> LApp X l) (ren-subst r sigma t)
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
subst-subst tau sigma (U l)        = refl
subst-subst tau sigma (Grd c A)  = Eq-cong (Grd c) (subst-subst tau sigma A)
subst-subst tau sigma (GLam c t) = Eq-cong (GLam c) (subst-subst tau sigma t)
subst-subst tau sigma Emp        = refl
subst-subst tau sigma (LPi A)  =
  Eq-cong LPi (Eq-trans (subst-subst _ _ A) (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) A))
subst-subst tau sigma (LLam u) =
  Eq-cong LLam (Eq-trans (subst-subst _ _ u) (substExpr-ext _ _ (\ i -> Eq-sym (lsubE-subst lwkS tau (sigma i))) u))
subst-subst tau sigma (LApp t l) = Eq-cong (\ X -> LApp X l) (subst-subst tau sigma t)
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

------------------------------------------------------------------------
-- Contexts of core types (as in MIN.Syntax.Typing)
------------------------------------------------------------------------

data Ctx : Nat -> Set where
  empty  : LCtx -> Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

lctx : {n : Nat} -> Ctx n -> LCtx
lctx (empty Th)   = Th
lctx (extend G A) = lctx G
