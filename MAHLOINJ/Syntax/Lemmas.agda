{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/Lemmas.agda
--
-- Syntactic equalities for the derived formers of MAHLO/Syntax.agda
-- (OpF, OpG, RecStep, sucSub) under renaming and substitution, the
-- extension  consSub  of a substitution, and transport helpers for the
-- judgements of MAHLO/Typing.agda.
------------------------------------------------------------------------

module MAHLOINJ.Syntax.Lemmas where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing

------------------------------------------------------------------------
-- Transport
------------------------------------------------------------------------

trTy : {n : Num} {G : Ctx n} {A A' : Expr n} -> Eq A A' -> IsType G A -> IsType G A'
trTy refl d = d

trHT : {n : Num} {G : Ctx n} {t t' A A' : Expr n} ->
       Eq t t' -> Eq A A' -> HasType G t A -> HasType G t' A'
trHT refl refl d = d

trTE : {n : Num} {G : Ctx n} {A A' B B' : Expr n} ->
       Eq A A' -> Eq B B' -> TyEq G A B -> TyEq G A' B'
trTE refl refl d = d

trCv : {n : Num} {G : Ctx n} {t t' u u' A A' : Expr n} ->
       Eq t t' -> Eq u u' -> Eq A A' -> ConvTm G t u A -> ConvTm G t' u' A'
trCv refl refl refl d = d

-- an element of a universe is a type
elTy : {n : Num} {G : Ctx n} {u A : Expr n} -> Univ u -> HasType G A u -> IsType G A
elTy (univ-V refl) h = isty-el h
elTy (univ-U f g refl) h = isty-el (ty-sub h)

------------------------------------------------------------------------
-- wk e  as a substitution, and  sucSub  on weakened terms
------------------------------------------------------------------------

wk-as-subst : {n : Num} (e : Expr n) -> Eq (wkExpr e) (substExpr (\ i -> Var (fsuc i)) e)
wk-as-subst e = ren-as-subst wkRen e

sucSub-wk : {n : Num} (e : Expr n) -> Eq (substExpr sucSub (wkExpr e)) (wkExpr e)
sucSub-wk e =
  Eq-trans (subst-ren-gen sucSub wkRen (\ i -> Var (fsuc i)) (\ i -> refl) e)
           (Eq-sym (wk-as-subst e))

-- sigma (lift wk B) ... : renaming and sucSub commute
ren-sucSub : {n m : Num} (r : Ren n m) (C : Expr (suc n)) ->
  Eq (renExpr (liftRen r) (substExpr sucSub C)) (substExpr sucSub (renExpr (liftRen r) C))
ren-sucSub r C =
  Eq-trans (ren-subst-gen (liftRen r) sucSub s' e C)
           (Eq-sym (subst-ren-gen sucSub (liftRen r) s' e' C))
  where
    s' : Sub _ _
    s' i = sucSub (liftRen r i)
    e : (i : Fin _) -> Eq (renExpr (liftRen r) (sucSub i)) (s' i)
    e fzero    = refl
    e (fsuc i) = refl
    e' : (i : Fin _) -> Eq (sucSub (liftRen r i)) (s' i)
    e' i = refl

subst-sucSub : {h g : Num} (s : Sub h g) (C : Expr (suc g)) ->
  Eq (substExpr (liftSub s) (substExpr sucSub C)) (substExpr sucSub (substExpr (liftSub s) C))
subst-sucSub s C =
  Eq-trans (subst-subst-gen (liftSub s) sucSub s0 e C)
           (Eq-sym (subst-subst-gen sucSub (liftSub s) s0 e' C))
  where
    s0 : Sub _ _
    s0 i = substExpr (liftSub s) (sucSub i)
    e : (i : Fin _) -> Eq (substExpr (liftSub s) (sucSub i)) (s0 i)
    e i = refl
    e' : (i : Fin _) -> Eq (substExpr sucSub (liftSub s i)) (s0 i)
    e' fzero    = refl
    e' (fsuc i) = sucSub-wk (s i)

-- C[S x/x][k/x] = C[S k/x]
subst1-sucSub : {n : Num} (C : Expr (suc n)) (k : Expr n) ->
  Eq (subst1 (substExpr sucSub C) k) (subst1 C (Suc k))
subst1-sucSub C k = subst-subst-gen (subst1Sub k) sucSub (subst1Sub (Suc k)) e C
  where
    e : (i : Fin _) -> Eq (substExpr (subst1Sub k) (sucSub i)) (subst1Sub (Suc k) i)
    e fzero    = refl
    e (fsuc i) = refl

------------------------------------------------------------------------
-- OpG and RecStep under renaming and substitution
------------------------------------------------------------------------

-- OpG f = OpG' (wk (wk f)); renaming/substitution act on OpG' pointwise
OpG' : {n : Num} -> Expr (suc (suc n)) -> Expr n
OpG' ff = PiB V (PiB (Arr x0 V) (Arr (App (App ff x1) x0) V))

ren-OpG : {n m : Num} (r : Ren n m) (f : Expr n) ->
  Eq (renExpr r (OpG f)) (OpG (renExpr r f))
ren-OpG r f =
  Eq-cong OpG' (Eq-trans (ren-wk-comm (liftRen r) (wkExpr f))
                         (Eq-cong wkExpr (ren-wk-comm r f)))

subst-OpG : {h g : Num} (s : Sub h g) (f : Expr g) ->
  Eq (substExpr s (OpG f)) (OpG (substExpr s f))
subst-OpG s f =
  Eq-cong OpG' (Eq-trans (subst-wk-comm (liftSub s) (wkExpr f))
                         (Eq-cong wkExpr (subst-wk-comm s f)))

-- RecStep C = RS C (wk (C[S x/x]))
RS : {n : Num} -> Expr (suc n) -> Expr (suc (suc n)) -> Expr n
RS C E = Pi Nat (Lam Nat (Pi C (Lam C E)))

ren-RecStep : {n m : Num} (r : Ren n m) (C : Expr (suc n)) ->
  Eq (renExpr r (RecStep C)) (RecStep (renExpr (liftRen r) C))
ren-RecStep r C =
  Eq-cong (RS (renExpr (liftRen r) C))
    (Eq-trans (ren-wk-comm (liftRen r) (substExpr sucSub C))
              (Eq-cong wkExpr (ren-sucSub r C)))

subst-RecStep : {h g : Num} (s : Sub h g) (C : Expr (suc g)) ->
  Eq (substExpr s (RecStep C)) (RecStep (substExpr (liftSub s) C))
subst-RecStep s C =
  Eq-cong (RS (substExpr (liftSub s) C))
    (Eq-trans (subst-wk-comm (liftSub s) (substExpr sucSub C))
              (Eq-cong wkExpr (subst-sucSub s C)))

------------------------------------------------------------------------
-- Extension of a substitution
------------------------------------------------------------------------

consSub : {h g : Num} -> Sub h g -> Expr h -> Sub h (suc g)
consSub s a fzero    = a
consSub s a (fsuc i) = s i

subst-consSub : {h g : Num} (s : Sub h g) (a : Expr h) (B : Expr (suc g)) ->
  Eq (substExpr (consSub s a) B) (subst1 (substExpr (liftSub s) B) a)
subst-consSub s a B = Eq-sym (subst-subst-gen (subst1Sub a) (liftSub s) (consSub s a) e B)
  where
    e : (i : Fin _) -> Eq (substExpr (subst1Sub a) (liftSub s i)) (consSub s a i)
    e fzero    = refl
    e (fsuc i) = subst1-wk (s i) a

consSub-wk : {h g : Num} (s : Sub h g) (a : Expr h) (B : Expr g) ->
  Eq (substExpr (consSub s a) (wkExpr B)) (substExpr s B)
consSub-wk s a B = subst-ren-gen (consSub s a) wkRen s (\ i -> refl) B

-- the identity extended by a:  consSub idSub a  acts as  subst1 _ a
consId : {n : Num} (a : Expr n) (B : Expr (suc n)) ->
  Eq (substExpr (consSub idSub a) B) (subst1 B a)
consId a B = substExpr-ext (consSub idSub a) (subst1Sub a) e B
  where
    e : (i : Fin _) -> Eq (consSub idSub a i) (subst1Sub a i)
    e fzero    = refl
    e (fsuc i) = refl
