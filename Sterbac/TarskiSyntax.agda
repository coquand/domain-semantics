{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.TarskiSyntax
--
-- Raw syntax for the Tarski-style theory T_T (slide 8).
--
--   Types  A, B ::= Π A B | U n | El n a
--   Terms  a, b ::= v_i | λ(A,B,b) | app(A,B,c,a)
--                 | Π^n a b | U^m_n | ↑^m_n a
--
-- We use a single sort Expr (types and terms in the same syntactic
-- category, distinguished by the typing rules), matching RussellSyntax
-- so that erasure |·| : Expr_T → Expr_R is a plain map.
--
-- Constructors:
--   Var i               de Bruijn variable
--   Pi A B              Π-type
--   U n                 universe U_n (type)
--   El n a              decode of a code a at level n (type)
--   Lam A B b           annotated λ
--   App A B c a         annotated application
--   PiCode l a b        Π^l a b   (code in U_l of Π(El_l a, El_l b))
--   UCode m n           U^m_n     (code in U_m of U_n; well-typed when n < m)
--   Lift m n a          ↑^m_n a   (lift from U_n into U_m; n ≤ m)
--
-- Binding: Pi A B, Lam A B b, App A B c a, PiCode l a b all bind one
-- variable in B / b. UCode and Lift bind nothing.
------------------------------------------------------------------------

module Sterbac.TarskiSyntax where

open import Sterbac.Basic

------------------------------------------------------------------------
-- Expr
------------------------------------------------------------------------

data Expr : Nat -> Set where
  Var    : {n : Nat} -> Fin n -> Expr n
  Pi     : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
  U      : {n : Nat} -> Nat -> Expr n
  El     : {n : Nat} -> Nat -> Expr n -> Expr n
  Lam    : {n : Nat} -> Expr n -> Expr (suc n) -> Expr (suc n) -> Expr n
  App    : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n -> Expr n -> Expr n
  PiCode : {n : Nat} -> Nat -> Expr n -> Expr (suc n) -> Expr n
  UCode  : {n : Nat} -> Nat -> Nat -> Expr n
  Lift   : {n : Nat} -> Nat -> Nat -> Expr n -> Expr n

------------------------------------------------------------------------
-- Renamings (Ren / liftRen / wkRen are shared in Sterbac.Basic)
------------------------------------------------------------------------

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)         = Var (r i)
renExpr r (Pi A B)        = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (U l)           = U l
renExpr r (El l a)        = El l (renExpr r a)
renExpr r (Lam A B b)     = Lam (renExpr r A) (renExpr (liftRen r) B)
                                (renExpr (liftRen r) b)
renExpr r (App A B c a)   = App (renExpr r A) (renExpr (liftRen r) B)
                                (renExpr r c) (renExpr r a)
renExpr r (PiCode l a b)  = PiCode l (renExpr r a) (renExpr (liftRen r) b)
renExpr r (UCode m l)     = UCode m l
renExpr r (Lift m l a)    = Lift m l (renExpr r a)

wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

------------------------------------------------------------------------
-- Parallel substitution
------------------------------------------------------------------------

Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub sigma fzero    = Var fzero
liftSub sigma (fsuc i) = wkExpr (sigma i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr sigma (Var i)         = sigma i
substExpr sigma (Pi A B)        = Pi (substExpr sigma A)
                                     (substExpr (liftSub sigma) B)
substExpr sigma (U l)           = U l
substExpr sigma (El l a)        = El l (substExpr sigma a)
substExpr sigma (Lam A B b)     = Lam (substExpr sigma A)
                                      (substExpr (liftSub sigma) B)
                                      (substExpr (liftSub sigma) b)
substExpr sigma (App A B c a)   = App (substExpr sigma A)
                                      (substExpr (liftSub sigma) B)
                                      (substExpr sigma c)
                                      (substExpr sigma a)
substExpr sigma (PiCode l a b)  = PiCode l (substExpr sigma a)
                                           (substExpr (liftSub sigma) b)
substExpr sigma (UCode m l)     = UCode m l
substExpr sigma (Lift m l a)    = Lift m l (substExpr sigma a)

------------------------------------------------------------------------
-- Single substitution
------------------------------------------------------------------------

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub s fzero    = s
subst1Sub s (fsuc i) = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 M s = substExpr (subst1Sub s) M

------------------------------------------------------------------------
-- Pointwise extensionality
------------------------------------------------------------------------

liftRen-ext : {n m : Nat} (r1 r2 : Ren n m)
  -> ((i : Fin n) -> Eq (r1 i) (r2 i))
  -> (j : Fin (suc n)) -> Eq (liftRen r1 j) (liftRen r2 j)
liftRen-ext r1 r2 ext fzero    = refl
liftRen-ext r1 r2 ext (fsuc i) = Eq-cong fsuc (ext i)

renExpr-ext : {n m : Nat} (r1 r2 : Ren n m)
  -> ((i : Fin n) -> Eq (r1 i) (r2 i))
  -> (e : Expr n) -> Eq (renExpr r1 e) (renExpr r2 e)
renExpr-ext r1 r2 ext (Var i)        = Eq-cong Var (ext i)
renExpr-ext r1 r2 ext (Pi A B)       =
  Eq-cong2 Pi (renExpr-ext r1 r2 ext A)
              (renExpr-ext (liftRen r1) (liftRen r2)
                           (liftRen-ext r1 r2 ext) B)
renExpr-ext r1 r2 ext (U l)          = refl
renExpr-ext r1 r2 ext (El l a)       =
  Eq-cong (El l) (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (Lam A B b)    =
  Eq-cong3 Lam (renExpr-ext r1 r2 ext A)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) B)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) b)
renExpr-ext r1 r2 ext (App A B c a)  =
  Eq-cong4 App (renExpr-ext r1 r2 ext A)
               (renExpr-ext (liftRen r1) (liftRen r2)
                            (liftRen-ext r1 r2 ext) B)
               (renExpr-ext r1 r2 ext c)
               (renExpr-ext r1 r2 ext a)
renExpr-ext r1 r2 ext (PiCode l a b) =
  Eq-cong2 (PiCode l) (renExpr-ext r1 r2 ext a)
                      (renExpr-ext (liftRen r1) (liftRen r2)
                                   (liftRen-ext r1 r2 ext) b)
renExpr-ext r1 r2 ext (UCode m l)    = refl
renExpr-ext r1 r2 ext (Lift m l a)   =
  Eq-cong (Lift m l) (renExpr-ext r1 r2 ext a)

liftSub-ext : {h g : Nat} (s1 s2 : Sub h g)
  -> ((i : Fin g) -> Eq (s1 i) (s2 i))
  -> (j : Fin (suc g)) -> Eq (liftSub s1 j) (liftSub s2 j)
liftSub-ext s1 s2 ext fzero    = refl
liftSub-ext s1 s2 ext (fsuc i) = Eq-cong wkExpr (ext i)

substExpr-ext : {h g : Nat} (s1 s2 : Sub h g)
  -> ((i : Fin g) -> Eq (s1 i) (s2 i))
  -> (e : Expr g) -> Eq (substExpr s1 e) (substExpr s2 e)
substExpr-ext s1 s2 ext (Var i)        = ext i
substExpr-ext s1 s2 ext (Pi A B)       =
  Eq-cong2 Pi (substExpr-ext s1 s2 ext A)
              (substExpr-ext (liftSub s1) (liftSub s2)
                             (liftSub-ext s1 s2 ext) B)
substExpr-ext s1 s2 ext (U l)          = refl
substExpr-ext s1 s2 ext (El l a)       =
  Eq-cong (El l) (substExpr-ext s1 s2 ext a)
substExpr-ext s1 s2 ext (Lam A B b)    =
  Eq-cong3 Lam (substExpr-ext s1 s2 ext A)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) B)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) b)
substExpr-ext s1 s2 ext (App A B c a)  =
  Eq-cong4 App (substExpr-ext s1 s2 ext A)
               (substExpr-ext (liftSub s1) (liftSub s2)
                              (liftSub-ext s1 s2 ext) B)
               (substExpr-ext s1 s2 ext c)
               (substExpr-ext s1 s2 ext a)
substExpr-ext s1 s2 ext (PiCode l a b) =
  Eq-cong2 (PiCode l) (substExpr-ext s1 s2 ext a)
                      (substExpr-ext (liftSub s1) (liftSub s2)
                                     (liftSub-ext s1 s2 ext) b)
substExpr-ext s1 s2 ext (UCode m l)    = refl
substExpr-ext s1 s2 ext (Lift m l a)   =
  Eq-cong (Lift m l) (substExpr-ext s1 s2 ext a)

------------------------------------------------------------------------
-- Renaming composition
------------------------------------------------------------------------

ren-ren : {n m k : Nat} (r1 : Ren m k) (r2 : Ren n m) (e : Expr n)
  -> Eq (renExpr r1 (renExpr r2 e)) (renExpr (\ i -> r1 (r2 i)) e)
ren-ren r1 r2 (Var i)        = refl
ren-ren r1 r2 (Pi A B)       =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      adj = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
ren-ren r1 r2 (U l)          = refl
ren-ren r1 r2 (El l a)       = Eq-cong (El l) (ren-ren r1 r2 a)
ren-ren r1 r2 (Lam A B b)    =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      ihb = ren-ren (liftRen r1) (liftRen r2) b
      adjB = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
      adjb = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
ren-ren r1 r2 (App A B c a)  =
  let ihA = ren-ren r1 r2 A
      ihB = ren-ren (liftRen r1) (liftRen r2) B
      ihc = ren-ren r1 r2 c
      iha = ren-ren r1 r2 a
      adjB = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha
ren-ren r1 r2 (PiCode l a b) =
  let iha = ren-ren r1 r2 a
      ihb = ren-ren (liftRen r1) (liftRen r2) b
      adj = renExpr-ext _ (liftRen (\ i -> r1 (r2 i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong2 (PiCode l) iha (Eq-trans ihb adj)
ren-ren r1 r2 (UCode m l)    = refl
ren-ren r1 r2 (Lift m l a)   = Eq-cong (Lift m l) (ren-ren r1 r2 a)

------------------------------------------------------------------------
-- Renaming/substitution interaction
------------------------------------------------------------------------

subst-ren : {h g k : Nat} (sigma : Sub h g) (r : Ren k g) (e : Expr k)
  -> Eq (substExpr sigma (renExpr r e)) (substExpr (\ i -> sigma (r i)) e)
subst-ren sigma r (Var i)        = refl
subst-ren sigma r (Pi A B)       =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      adj = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
subst-ren sigma r (U l)          = refl
subst-ren sigma r (El l a)       = Eq-cong (El l) (subst-ren sigma r a)
subst-ren sigma r (Lam A B b)    =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      ihb = subst-ren (liftSub sigma) (liftRen r) b
      adjB = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
      adjb = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
subst-ren sigma r (App A B c a)  =
  let ihA = subst-ren sigma r A
      ihB = subst-ren (liftSub sigma) (liftRen r) B
      ihc = subst-ren sigma r c
      iha = subst-ren sigma r a
      adjB = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
               (\ { fzero -> refl ; (fsuc i) -> refl }) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha
subst-ren sigma r (PiCode l a b) =
  let iha = subst-ren sigma r a
      ihb = subst-ren (liftSub sigma) (liftRen r) b
      adj = substExpr-ext _ (liftSub (\ i -> sigma (r i)))
              (\ { fzero -> refl ; (fsuc i) -> refl }) b
  in Eq-cong2 (PiCode l) iha (Eq-trans ihb adj)
subst-ren sigma r (UCode m l)    = refl
subst-ren sigma r (Lift m l a)   = Eq-cong (Lift m l) (subst-ren sigma r a)

ren-wk-comm : {n m : Nat} (r : Ren n m) (e : Expr n)
  -> Eq (renExpr (liftRen r) (wkExpr e)) (wkExpr (renExpr r e))
ren-wk-comm r e =
  Eq-trans (ren-ren (liftRen r) wkRen e) (Eq-sym (ren-ren wkRen r e))

liftSub-ren-ext : {h g k : Nat} (r : Ren g k) (sigma : Sub g h)
  -> (j : Fin (suc h))
  -> Eq (renExpr (liftRen r) (liftSub sigma j))
        (liftSub (\ i -> renExpr r (sigma i)) j)
liftSub-ren-ext r sigma fzero    = refl
liftSub-ren-ext r sigma (fsuc i) = ren-wk-comm r (sigma i)

ren-subst : {h g k : Nat} (r : Ren g k) (sigma : Sub g h) (e : Expr h)
  -> Eq (renExpr r (substExpr sigma e))
        (substExpr (\ i -> renExpr r (sigma i)) e)
ren-subst r sigma (Var i)        = refl
ren-subst r sigma (Pi A B)       =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      adj = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
              (liftSub-ren-ext r sigma) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
ren-subst r sigma (U l)          = refl
ren-subst r sigma (El l a)       = Eq-cong (El l) (ren-subst r sigma a)
ren-subst r sigma (Lam A B b)    =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      ihb = ren-subst (liftRen r) (liftSub sigma) b
      adjB = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) B
      adjb = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
ren-subst r sigma (App A B c a)  =
  let ihA = ren-subst r sigma A
      ihB = ren-subst (liftRen r) (liftSub sigma) B
      ihc = ren-subst r sigma c
      iha = ren-subst r sigma a
      adjB = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
               (liftSub-ren-ext r sigma) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha
ren-subst r sigma (PiCode l a b) =
  let iha = ren-subst r sigma a
      ihb = ren-subst (liftRen r) (liftSub sigma) b
      adj = substExpr-ext _ (liftSub (\ i -> renExpr r (sigma i)))
              (liftSub-ren-ext r sigma) b
  in Eq-cong2 (PiCode l) iha (Eq-trans ihb adj)
ren-subst r sigma (UCode m l)    = refl
ren-subst r sigma (Lift m l a)   = Eq-cong (Lift m l) (ren-subst r sigma a)

------------------------------------------------------------------------
-- Substitution composition
------------------------------------------------------------------------

subst-wk-comm : {h g : Nat} (tau : Sub g h) (e : Expr h)
  -> Eq (substExpr (liftSub tau) (wkExpr e)) (wkExpr (substExpr tau e))
subst-wk-comm tau e =
  Eq-trans (subst-ren (liftSub tau) wkRen e) (Eq-sym (ren-subst wkRen tau e))

liftSub-subst-ext : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h)
  -> (j : Fin (suc h))
  -> Eq (substExpr (liftSub tau) (liftSub sigma j))
        (liftSub (\ i -> substExpr tau (sigma i)) j)
liftSub-subst-ext tau sigma fzero    = refl
liftSub-subst-ext tau sigma (fsuc i) = subst-wk-comm tau (sigma i)

subst-subst : {h g k : Nat} (tau : Sub k g) (sigma : Sub g h) (e : Expr h)
  -> Eq (substExpr tau (substExpr sigma e))
        (substExpr (\ i -> substExpr tau (sigma i)) e)
subst-subst tau sigma (Var i)        = refl
subst-subst tau sigma (Pi A B)       =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      adj = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
              (liftSub-subst-ext tau sigma) B
  in Eq-cong2 Pi ihA (Eq-trans ihB adj)
subst-subst tau sigma (U l)          = refl
subst-subst tau sigma (El l a)       = Eq-cong (El l) (subst-subst tau sigma a)
subst-subst tau sigma (Lam A B b)    =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      ihb = subst-subst (liftSub tau) (liftSub sigma) b
      adjB = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) B
      adjb = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) b
  in Eq-cong3 Lam ihA (Eq-trans ihB adjB) (Eq-trans ihb adjb)
subst-subst tau sigma (App A B c a)  =
  let ihA = subst-subst tau sigma A
      ihB = subst-subst (liftSub tau) (liftSub sigma) B
      ihc = subst-subst tau sigma c
      iha = subst-subst tau sigma a
      adjB = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
               (liftSub-subst-ext tau sigma) B
  in Eq-cong4 App ihA (Eq-trans ihB adjB) ihc iha
subst-subst tau sigma (PiCode l a b) =
  let iha = subst-subst tau sigma a
      ihb = subst-subst (liftSub tau) (liftSub sigma) b
      adj = substExpr-ext _ (liftSub (\ i -> substExpr tau (sigma i)))
              (liftSub-subst-ext tau sigma) b
  in Eq-cong2 (PiCode l) iha (Eq-trans ihb adj)
subst-subst tau sigma (UCode m l)    = refl
subst-subst tau sigma (Lift m l a)   = Eq-cong (Lift m l) (subst-subst tau sigma a)
