{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/SubstLemmas.agda
--
-- The renaming/substitution algebra of MAHLO/Syntax.agda, for the Tarski
-- syntax (generated from it: Var and Lam clauses verbatim -- Lam is the
-- only binder on both sides -- the other formers are congruences).
------------------------------------------------------------------------

module MAHLORT.Syntax.SubstLemmas where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax

cong3 : {A B C D : Set} (h : A -> B -> C -> D) {a a' : A} {b b' : B} {c c' : C} ->
        Eq a a' -> Eq b b' -> Eq c c' -> Eq (h a b c) (h a' b' c')
cong3 h refl refl refl = refl

idSub : {n : Num} -> Sub n n
idSub i = Var i
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
renExpr-ext r1 r2 e (App y0 y1 y2 y3) = cong4 App (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e (Pi y0 y1) = cong2 Pi (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (Sigma y0 y1) = cong2 Sigma (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (Pair y0 y1 y2 y3) = cong4 Pair (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e (Fst y0 y1 y2) = cong3 Fst (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2)
renExpr-ext r1 r2 e (Snd y0 y1 y2) = cong3 Snd (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2)
renExpr-ext r1 r2 e Nat = refl
renExpr-ext r1 r2 e Zero = refl
renExpr-ext r1 r2 e (Suc y0) = Eq-cong Suc (renExpr-ext r1 r2 e y0)
renExpr-ext r1 r2 e (Rec y0 y1 y2 y3) = cong4 Rec (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e V = refl
renExpr-ext r1 r2 e (ElV y0) = Eq-cong ElV (renExpr-ext r1 r2 e y0)
renExpr-ext r1 r2 e (TyU y0 y1) = cong2 TyU (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (ElU y0 y1 y2) = cong3 ElU (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2)
renExpr-ext r1 r2 e (PiV y0 y1) = cong2 PiV (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (SigV y0 y1) = cong2 SigV (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e NatV = refl
renExpr-ext r1 r2 e (UV y0 y1) = cong2 UV (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (PiU y0 y1 y2 y3) = cong4 PiU (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e (SigU y0 y1 y2 y3) = cong4 SigU (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e (NatU y0 y1) = cong2 NatU (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1)
renExpr-ext r1 r2 e (Fhat y0 y1 y2 y3) = cong4 Fhat (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3)
renExpr-ext r1 r2 e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (renExpr-ext r1 r2 e y0) (renExpr-ext r1 r2 e y1) (renExpr-ext r1 r2 e y2) (renExpr-ext r1 r2 e y3) (renExpr-ext r1 r2 e y4)
renExpr-ext r1 r2 e (That y0) = Eq-cong That (renExpr-ext r1 r2 e y0)

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
substExpr-ext s1 s2 e (App y0 y1 y2 y3) = cong4 App (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e (Pi y0 y1) = cong2 Pi (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (Sigma y0 y1) = cong2 Sigma (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (Pair y0 y1 y2 y3) = cong4 Pair (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e (Fst y0 y1 y2) = cong3 Fst (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2)
substExpr-ext s1 s2 e (Snd y0 y1 y2) = cong3 Snd (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2)
substExpr-ext s1 s2 e Nat = refl
substExpr-ext s1 s2 e Zero = refl
substExpr-ext s1 s2 e (Suc y0) = Eq-cong Suc (substExpr-ext s1 s2 e y0)
substExpr-ext s1 s2 e (Rec y0 y1 y2 y3) = cong4 Rec (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e V = refl
substExpr-ext s1 s2 e (ElV y0) = Eq-cong ElV (substExpr-ext s1 s2 e y0)
substExpr-ext s1 s2 e (TyU y0 y1) = cong2 TyU (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (ElU y0 y1 y2) = cong3 ElU (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2)
substExpr-ext s1 s2 e (PiV y0 y1) = cong2 PiV (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (SigV y0 y1) = cong2 SigV (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e NatV = refl
substExpr-ext s1 s2 e (UV y0 y1) = cong2 UV (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (PiU y0 y1 y2 y3) = cong4 PiU (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e (SigU y0 y1 y2 y3) = cong4 SigU (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e (NatU y0 y1) = cong2 NatU (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1)
substExpr-ext s1 s2 e (Fhat y0 y1 y2 y3) = cong4 Fhat (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3)
substExpr-ext s1 s2 e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (substExpr-ext s1 s2 e y0) (substExpr-ext s1 s2 e y1) (substExpr-ext s1 s2 e y2) (substExpr-ext s1 s2 e y3) (substExpr-ext s1 s2 e y4)
substExpr-ext s1 s2 e (That y0) = Eq-cong That (substExpr-ext s1 s2 e y0)

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
ren-ren-gen r1 r2 r e (App y0 y1 y2 y3) = cong4 App (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e (Pi y0 y1) = cong2 Pi (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (Sigma y0 y1) = cong2 Sigma (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (Pair y0 y1 y2 y3) = cong4 Pair (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e (Fst y0 y1 y2) = cong3 Fst (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2)
ren-ren-gen r1 r2 r e (Snd y0 y1 y2) = cong3 Snd (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2)
ren-ren-gen r1 r2 r e Nat = refl
ren-ren-gen r1 r2 r e Zero = refl
ren-ren-gen r1 r2 r e (Suc y0) = Eq-cong Suc (ren-ren-gen r1 r2 r e y0)
ren-ren-gen r1 r2 r e (Rec y0 y1 y2 y3) = cong4 Rec (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e V = refl
ren-ren-gen r1 r2 r e (ElV y0) = Eq-cong ElV (ren-ren-gen r1 r2 r e y0)
ren-ren-gen r1 r2 r e (TyU y0 y1) = cong2 TyU (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (ElU y0 y1 y2) = cong3 ElU (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2)
ren-ren-gen r1 r2 r e (PiV y0 y1) = cong2 PiV (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (SigV y0 y1) = cong2 SigV (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e NatV = refl
ren-ren-gen r1 r2 r e (UV y0 y1) = cong2 UV (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (PiU y0 y1 y2 y3) = cong4 PiU (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e (SigU y0 y1 y2 y3) = cong4 SigU (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e (NatU y0 y1) = cong2 NatU (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1)
ren-ren-gen r1 r2 r e (Fhat y0 y1 y2 y3) = cong4 Fhat (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3)
ren-ren-gen r1 r2 r e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (ren-ren-gen r1 r2 r e y0) (ren-ren-gen r1 r2 r e y1) (ren-ren-gen r1 r2 r e y2) (ren-ren-gen r1 r2 r e y3) (ren-ren-gen r1 r2 r e y4)
ren-ren-gen r1 r2 r e (That y0) = Eq-cong That (ren-ren-gen r1 r2 r e y0)

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
subst-ren-gen s r s' e (App y0 y1 y2 y3) = cong4 App (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e (Pi y0 y1) = cong2 Pi (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (Sigma y0 y1) = cong2 Sigma (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (Pair y0 y1 y2 y3) = cong4 Pair (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e (Fst y0 y1 y2) = cong3 Fst (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2)
subst-ren-gen s r s' e (Snd y0 y1 y2) = cong3 Snd (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2)
subst-ren-gen s r s' e Nat = refl
subst-ren-gen s r s' e Zero = refl
subst-ren-gen s r s' e (Suc y0) = Eq-cong Suc (subst-ren-gen s r s' e y0)
subst-ren-gen s r s' e (Rec y0 y1 y2 y3) = cong4 Rec (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e V = refl
subst-ren-gen s r s' e (ElV y0) = Eq-cong ElV (subst-ren-gen s r s' e y0)
subst-ren-gen s r s' e (TyU y0 y1) = cong2 TyU (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (ElU y0 y1 y2) = cong3 ElU (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2)
subst-ren-gen s r s' e (PiV y0 y1) = cong2 PiV (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (SigV y0 y1) = cong2 SigV (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e NatV = refl
subst-ren-gen s r s' e (UV y0 y1) = cong2 UV (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (PiU y0 y1 y2 y3) = cong4 PiU (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e (SigU y0 y1 y2 y3) = cong4 SigU (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e (NatU y0 y1) = cong2 NatU (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1)
subst-ren-gen s r s' e (Fhat y0 y1 y2 y3) = cong4 Fhat (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3)
subst-ren-gen s r s' e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (subst-ren-gen s r s' e y0) (subst-ren-gen s r s' e y1) (subst-ren-gen s r s' e y2) (subst-ren-gen s r s' e y3) (subst-ren-gen s r s' e y4)
subst-ren-gen s r s' e (That y0) = Eq-cong That (subst-ren-gen s r s' e y0)

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
ren-subst-gen r s s' e (App y0 y1 y2 y3) = cong4 App (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e (Pi y0 y1) = cong2 Pi (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (Sigma y0 y1) = cong2 Sigma (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (Pair y0 y1 y2 y3) = cong4 Pair (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e (Fst y0 y1 y2) = cong3 Fst (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2)
ren-subst-gen r s s' e (Snd y0 y1 y2) = cong3 Snd (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2)
ren-subst-gen r s s' e Nat = refl
ren-subst-gen r s s' e Zero = refl
ren-subst-gen r s s' e (Suc y0) = Eq-cong Suc (ren-subst-gen r s s' e y0)
ren-subst-gen r s s' e (Rec y0 y1 y2 y3) = cong4 Rec (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e V = refl
ren-subst-gen r s s' e (ElV y0) = Eq-cong ElV (ren-subst-gen r s s' e y0)
ren-subst-gen r s s' e (TyU y0 y1) = cong2 TyU (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (ElU y0 y1 y2) = cong3 ElU (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2)
ren-subst-gen r s s' e (PiV y0 y1) = cong2 PiV (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (SigV y0 y1) = cong2 SigV (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e NatV = refl
ren-subst-gen r s s' e (UV y0 y1) = cong2 UV (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (PiU y0 y1 y2 y3) = cong4 PiU (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e (SigU y0 y1 y2 y3) = cong4 SigU (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e (NatU y0 y1) = cong2 NatU (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1)
ren-subst-gen r s s' e (Fhat y0 y1 y2 y3) = cong4 Fhat (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3)
ren-subst-gen r s s' e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (ren-subst-gen r s s' e y0) (ren-subst-gen r s s' e y1) (ren-subst-gen r s s' e y2) (ren-subst-gen r s s' e y3) (ren-subst-gen r s s' e y4)
ren-subst-gen r s s' e (That y0) = Eq-cong That (ren-subst-gen r s s' e y0)

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
subst-subst-gen s2 s1 s e (App y0 y1 y2 y3) = cong4 App (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e (Pi y0 y1) = cong2 Pi (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (Sigma y0 y1) = cong2 Sigma (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (Pair y0 y1 y2 y3) = cong4 Pair (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e (Fst y0 y1 y2) = cong3 Fst (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2)
subst-subst-gen s2 s1 s e (Snd y0 y1 y2) = cong3 Snd (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2)
subst-subst-gen s2 s1 s e Nat = refl
subst-subst-gen s2 s1 s e Zero = refl
subst-subst-gen s2 s1 s e (Suc y0) = Eq-cong Suc (subst-subst-gen s2 s1 s e y0)
subst-subst-gen s2 s1 s e (Rec y0 y1 y2 y3) = cong4 Rec (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e V = refl
subst-subst-gen s2 s1 s e (ElV y0) = Eq-cong ElV (subst-subst-gen s2 s1 s e y0)
subst-subst-gen s2 s1 s e (TyU y0 y1) = cong2 TyU (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (ElU y0 y1 y2) = cong3 ElU (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2)
subst-subst-gen s2 s1 s e (PiV y0 y1) = cong2 PiV (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (SigV y0 y1) = cong2 SigV (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e NatV = refl
subst-subst-gen s2 s1 s e (UV y0 y1) = cong2 UV (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (PiU y0 y1 y2 y3) = cong4 PiU (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e (SigU y0 y1 y2 y3) = cong4 SigU (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e (NatU y0 y1) = cong2 NatU (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1)
subst-subst-gen s2 s1 s e (Fhat y0 y1 y2 y3) = cong4 Fhat (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3)
subst-subst-gen s2 s1 s e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (subst-subst-gen s2 s1 s e y0) (subst-subst-gen s2 s1 s e y1) (subst-subst-gen s2 s1 s e y2) (subst-subst-gen s2 s1 s e y3) (subst-subst-gen s2 s1 s e y4)
subst-subst-gen s2 s1 s e (That y0) = Eq-cong That (subst-subst-gen s2 s1 s e y0)

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
substExpr-id-gen s e (App y0 y1 y2 y3) = cong4 App (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e (Pi y0 y1) = cong2 Pi (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (Sigma y0 y1) = cong2 Sigma (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (Pair y0 y1 y2 y3) = cong4 Pair (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e (Fst y0 y1 y2) = cong3 Fst (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2)
substExpr-id-gen s e (Snd y0 y1 y2) = cong3 Snd (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2)
substExpr-id-gen s e Nat = refl
substExpr-id-gen s e Zero = refl
substExpr-id-gen s e (Suc y0) = Eq-cong Suc (substExpr-id-gen s e y0)
substExpr-id-gen s e (Rec y0 y1 y2 y3) = cong4 Rec (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e V = refl
substExpr-id-gen s e (ElV y0) = Eq-cong ElV (substExpr-id-gen s e y0)
substExpr-id-gen s e (TyU y0 y1) = cong2 TyU (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (ElU y0 y1 y2) = cong3 ElU (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2)
substExpr-id-gen s e (PiV y0 y1) = cong2 PiV (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (SigV y0 y1) = cong2 SigV (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e NatV = refl
substExpr-id-gen s e (UV y0 y1) = cong2 UV (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (PiU y0 y1 y2 y3) = cong4 PiU (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e (SigU y0 y1 y2 y3) = cong4 SigU (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e (NatU y0 y1) = cong2 NatU (substExpr-id-gen s e y0) (substExpr-id-gen s e y1)
substExpr-id-gen s e (Fhat y0 y1 y2 y3) = cong4 Fhat (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3)
substExpr-id-gen s e (Ghat y0 y1 y2 y3 y4) = cong5 Ghat (substExpr-id-gen s e y0) (substExpr-id-gen s e y1) (substExpr-id-gen s e y2) (substExpr-id-gen s e y3) (substExpr-id-gen s e y4)
substExpr-id-gen s e (That y0) = Eq-cong That (substExpr-id-gen s e y0)

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
