{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Lemmas.agda
--
-- Syntactic equalities for the derived formers of MAHLORT/TarskiSyntax
-- (OpG, RecStep, gApp, the funext body, the rec-suc contractum) under
-- renaming and substitution; consSub; transports for the judgements of
-- MAHLORT/TarskiTyping.  Port of MAHLOINJ/Syntax/Lemmas.agda.
-- Each fact comes as a pair  ren-X r / subst-X s  of the same shape.
------------------------------------------------------------------------

module MAHLORT.Syntax.Lemmas where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.SubstLemmas public

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

------------------------------------------------------------------------
-- wk e  as a substitution, sucSub
------------------------------------------------------------------------

wk-as-subst : {n : Num} (e : Expr n) -> Eq (wkExpr e) (substExpr (\ i -> Var (fsuc i)) e)
wk-as-subst e = ren-as-subst wkRen e

sucSub-wk : {n : Num} (e : Expr n) -> Eq (substExpr sucSub (wkExpr e)) (wkExpr e)
sucSub-wk e =
  Eq-trans (subst-ren-gen sucSub wkRen (\ i -> Var (fsuc i)) (\ i -> refl) e)
           (Eq-sym (wk-as-subst e))

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

subst1-sucSub : {n : Num} (C : Expr (suc n)) (k : Expr n) ->
  Eq (subst1 (substExpr sucSub C) k) (subst1 C (Suc k))
subst1-sucSub C k = subst-subst-gen (subst1Sub k) sucSub (subst1Sub (Suc k)) e C
  where
    e : (i : Fin _) -> Eq (substExpr (subst1Sub k) (sucSub i)) (subst1Sub (Suc k) i)
    e fzero    = refl
    e (fsuc i) = refl

------------------------------------------------------------------------
-- lift wk  under a lifted renaming / substitution
------------------------------------------------------------------------

ren-liftwk : {n m : Num} (r : Ren n m) (B : Expr (suc n)) ->
  Eq (renExpr (liftRen (liftRen r)) (renExpr (liftRen wkRen) B))
     (renExpr (liftRen wkRen) (renExpr (liftRen r) B))
ren-liftwk r B =
  Eq-trans (ren-ren-gen (liftRen (liftRen r)) (liftRen wkRen) q e B)
           (Eq-sym (ren-ren-gen (liftRen wkRen) (liftRen r) q e' B))
  where
    q : Ren _ _
    q fzero = fzero
    q (fsuc i) = fsuc (fsuc (r i))
    e : (i : Fin _) -> Eq (liftRen (liftRen r) (liftRen wkRen i)) (q i)
    e fzero = refl
    e (fsuc i) = refl
    e' : (i : Fin _) -> Eq (liftRen wkRen (liftRen r i)) (q i)
    e' fzero = refl
    e' (fsuc i) = refl

subst-liftwk : {h g : Num} (s : Sub h g) (B : Expr (suc g)) ->
  Eq (substExpr (liftSub (liftSub s)) (renExpr (liftRen wkRen) B))
     (renExpr (liftRen wkRen) (substExpr (liftSub s) B))
subst-liftwk s B =
  Eq-trans (subst-ren-gen (liftSub (liftSub s)) (liftRen wkRen) q e B)
           (Eq-sym (ren-subst-gen (liftRen wkRen) (liftSub s) q e' B))
  where
    q : Sub _ _
    q fzero = Var fzero
    q (fsuc i) = wkExpr (wkExpr (s i))
    e : (i : Fin _) -> Eq (liftSub (liftSub s) (liftRen wkRen i)) (q i)
    e fzero = refl
    e (fsuc i) = refl
    e' : (i : Fin _) -> Eq (renExpr (liftRen wkRen) (liftSub s i)) (q i)
    e' fzero = refl
    e' (fsuc i) = ren-wk-comm wkRen (s i)

-- the body of conv-funext
FunB : {n : Num} -> Expr n -> Expr (suc n) -> Expr n -> Expr (suc n)
FunB A B t = appB (wkExpr A) (renExpr (liftRen wkRen) B) (wkExpr t) x0

private
  FB : {n : Num} -> Expr (suc n) -> Expr (suc (suc n)) -> Expr (suc n) -> Expr (suc n)
  FB a b c = App a (Lam a b) c x0

ren-FunB : {n m : Num} (r : Ren n m) (A : Expr n) (B : Expr (suc n)) (t : Expr n) ->
  Eq (renExpr (liftRen r) (FunB A B t)) (FunB (renExpr r A) (renExpr (liftRen r) B) (renExpr r t))
ren-FunB r A B t = cong3 FB (ren-wk-comm r A) (ren-liftwk r B) (ren-wk-comm r t)

subst-FunB : {h g : Num} (s : Sub h g) (A : Expr g) (B : Expr (suc g)) (t : Expr g) ->
  Eq (substExpr (liftSub s) (FunB A B t))
     (FunB (substExpr s A) (substExpr (liftSub s) B) (substExpr s t))
subst-FunB s A B t = cong3 FB (subst-wk-comm s A) (subst-liftwk s B) (subst-wk-comm s t)

------------------------------------------------------------------------
-- OpG, gApp
------------------------------------------------------------------------

OpG' : {n : Num} -> Expr (suc (suc n)) -> Expr n
OpG' ff = PiB V (PiB (Arr (ElV x0) V) (Arr (ElV (fApp ff x1 x0)) V))

ren-wkwk : {n m : Num} (r : Ren n m) (f : Expr n) ->
  Eq (renExpr (liftRen (liftRen r)) (wkExpr (wkExpr f))) (wkExpr (wkExpr (renExpr r f)))
ren-wkwk r f = Eq-trans (ren-wk-comm (liftRen r) (wkExpr f)) (Eq-cong wkExpr (ren-wk-comm r f))

subst-wkwk : {h g : Num} (s : Sub h g) (f : Expr g) ->
  Eq (substExpr (liftSub (liftSub s)) (wkExpr (wkExpr f))) (wkExpr (wkExpr (substExpr s f)))
subst-wkwk s f = Eq-trans (subst-wk-comm (liftSub s) (wkExpr f)) (Eq-cong wkExpr (subst-wk-comm s f))

ren-OpG : {n m : Num} (r : Ren n m) (f : Expr n) -> Eq (renExpr r (OpG f)) (OpG (renExpr r f))
ren-OpG r f = Eq-cong OpG' (ren-wkwk r f)

subst-OpG : {h g : Num} (s : Sub h g) (f : Expr g) -> Eq (substExpr s (OpG f)) (OpG (substExpr s f))
subst-OpG s f = Eq-cong OpG' (subst-wkwk s f)

private
  GA : {n : Num} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n ->
       Expr (suc n) -> Expr (suc n) -> Expr (suc (suc n)) -> Expr n
  GA f g a F c e1 e2 e3 =
    appB (ElV (fApp f a F)) V
      (appB (Arr (ElV a) V) (Arr (ElV (fApp e1 e2 x0)) V)
         (appB V (PiB (Arr (ElV x0) V) (Arr (ElV (fApp e3 x1 x0)) V)) g a) F) c

ren-gApp : {n m : Num} (r : Ren n m) (f g a F c : Expr n) ->
  Eq (renExpr r (gApp f g a F c))
     (gApp (renExpr r f) (renExpr r g) (renExpr r a) (renExpr r F) (renExpr r c))
ren-gApp r f g a F c =
  cong3 (GA (renExpr r f) (renExpr r g) (renExpr r a) (renExpr r F) (renExpr r c))
    (ren-wk-comm r f) (ren-wk-comm r a) (ren-wkwk r f)

subst-gApp : {h k : Num} (s : Sub h k) (f g a F c : Expr k) ->
  Eq (substExpr s (gApp f g a F c))
     (gApp (substExpr s f) (substExpr s g) (substExpr s a) (substExpr s F) (substExpr s c))
subst-gApp s f g a F c =
  cong3 (GA (substExpr s f) (substExpr s g) (substExpr s a) (substExpr s F) (substExpr s c))
    (subst-wk-comm s f) (subst-wk-comm s a) (subst-wkwk s f)

------------------------------------------------------------------------
-- RecStep, and the contractum of conv-rec-suc
------------------------------------------------------------------------

RS : {n : Num} -> Expr (suc n) -> Expr (suc (suc n)) -> Expr n
RS C E = Pi Nat (Lam Nat (Pi C (Lam C E)))

ren-recE : {n m : Num} (r : Ren n m) (C : Expr (suc n)) ->
  Eq (renExpr (liftRen (liftRen r)) (wkExpr (substExpr sucSub C)))
     (wkExpr (substExpr sucSub (renExpr (liftRen r) C)))
ren-recE r C = Eq-trans (ren-wk-comm (liftRen r) (substExpr sucSub C)) (Eq-cong wkExpr (ren-sucSub r C))

subst-recE : {h g : Num} (s : Sub h g) (C : Expr (suc g)) ->
  Eq (substExpr (liftSub (liftSub s)) (wkExpr (substExpr sucSub C)))
     (wkExpr (substExpr sucSub (substExpr (liftSub s) C)))
subst-recE s C = Eq-trans (subst-wk-comm (liftSub s) (substExpr sucSub C)) (Eq-cong wkExpr (subst-sucSub s C))

ren-RecStep : {n m : Num} (r : Ren n m) (C : Expr (suc n)) ->
  Eq (renExpr r (RecStep C)) (RecStep (renExpr (liftRen r) C))
ren-RecStep r C = Eq-cong (RS (renExpr (liftRen r) C)) (ren-recE r C)

subst-RecStep : {h g : Num} (s : Sub h g) (C : Expr (suc g)) ->
  Eq (substExpr s (RecStep C)) (RecStep (substExpr (liftSub s) C))
subst-RecStep s C = Eq-cong (RS (substExpr (liftSub s) C)) (subst-recE s C)

-- the contractum of conv-rec-suc
RecSuc : {n : Num} -> Expr (suc n) -> Expr n -> Expr n -> Expr n -> Expr n
RecSuc C z s k = appB (subst1 C k) (wkExpr (subst1 C (Suc k)))
                   (appB Nat (Arr C (substExpr sucSub C)) s k) (Rec (Lam Nat C) z s k)

private
  RSC : {n : Num} -> Expr (suc n) -> Expr n -> Expr n -> Expr n ->
        Expr n -> Expr (suc n) -> Expr (suc (suc n)) -> Expr n
  RSC C z s k P Q E = App P (Lam P Q) (App Nat (Lam Nat (Pi C (Lam C E))) s k) (Rec (Lam Nat C) z s k)

ren-RecSuc : {n m : Num} (r : Ren n m) (C : Expr (suc n)) (z s k : Expr n) ->
  Eq (renExpr r (RecSuc C z s k))
     (RecSuc (renExpr (liftRen r) C) (renExpr r z) (renExpr r s) (renExpr r k))
ren-RecSuc r C z s k =
  cong3 (RSC (renExpr (liftRen r) C) (renExpr r z) (renExpr r s) (renExpr r k))
    (ren-subst1 r C k)
    (Eq-trans (ren-wk-comm r (subst1 C (Suc k))) (Eq-cong wkExpr (ren-subst1 r C (Suc k))))
    (ren-recE r C)

subst-RecSuc : {h g : Num} (sg : Sub h g) (C : Expr (suc g)) (z s k : Expr g) ->
  Eq (substExpr sg (RecSuc C z s k))
     (RecSuc (substExpr (liftSub sg) C) (substExpr sg z) (substExpr sg s) (substExpr sg k))
subst-RecSuc sg C z s k =
  cong3 (RSC (substExpr (liftSub sg) C) (substExpr sg z) (substExpr sg s) (substExpr sg k))
    (subst-subst1-comm sg C k)
    (Eq-trans (subst-wk-comm sg (subst1 C (Suc k))) (Eq-cong wkExpr (subst-subst1-comm sg C (Suc k))))
    (subst-recE sg C)

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

consId : {n : Num} (a : Expr n) (B : Expr (suc n)) ->
  Eq (substExpr (consSub idSub a) B) (subst1 B a)
consId a B = substExpr-ext (consSub idSub a) (subst1Sub a) e B
  where
    e : (i : Fin _) -> Eq (consSub idSub a i) (subst1Sub a i)
    e fzero    = refl
    e (fsuc i) = refl
