{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Den.agda
--
-- The denotation of the raw syntax (MAHLO/Syntax.agda) in the concrete
-- model:  den t rho  is the erasure of  t[rho],  with the delta-steps
-- performed:  fhat(f,g,A,F) |-> f A F,  ghat(f,g,A,F,c) |-> g A F c.
-- Substitution laws up to syntactic equality, and invariance under
-- convertible environments.
------------------------------------------------------------------------

module MAHLO.Concrete.Den where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Conv

TEnv : Num -> Set
TEnv n = Fin n -> Tm

up : {n : Num} -> TEnv n -> TEnv (suc n)
up rho fzero = tvar zero
up rho (fsuc i) = shift (rho i)

den : {n : Num} -> Expr n -> TEnv n -> Tm
den (Var i) rho = rho i
den (Lam A t) rho = tlam (den t (up rho))
den (App t u) rho = tapp (den t rho) (den u rho)
den (Pi A F) rho = tpi (den A rho) (den F rho)
den (Sigma A F) rho = tsig (den A rho) (den F rho)
den (Pair t u) rho = tpair (den t rho) (den u rho)
den (Fst t) rho = tfst (den t rho)
den (Snd t) rho = tsnd (den t rho)
den Nat rho = tnat
den Zero rho = tze
den (Suc t) rho = tsc (den t rho)
den (Rec C z s k) rho = trec (den C rho) (den z rho) (den s rho) (den k rho)
den V rho = tV
den (Ucode f g) rho = tU (den f rho) (den g rho)
den (Fhat f g A F) rho = tapp (tapp (den f rho) (den A rho)) (den F rho)
den (Ghat f g A F c) rho = tapp (tapp (tapp (den g rho) (den A rho)) (den F rho)) (den c rho)

------------------------------------------------------------------------
-- Pointwise-equal environments, renaming, substitution
------------------------------------------------------------------------

PW : {n : Num} -> TEnv n -> TEnv n -> Set
PW {n} rho rho' = (i : Fin n) -> Eq (rho i) (rho' i)

up-pw : {n : Num} {rho rho' : TEnv n} -> PW rho rho' -> PW (up rho) (up rho')
up-pw e fzero = refl
up-pw e (fsuc i) = Eq-cong shift (e i)

den-ext : {n : Num} {rho rho' : TEnv n} -> PW rho rho' -> (t : Expr n) -> Eq (den t rho) (den t rho')
den-ext e (Var i) = e i
den-ext e (Lam A t) = Eq-cong tlam (den-ext (up-pw e) t)
den-ext e (App t u) = cong2 tapp (den-ext e t) (den-ext e u)
den-ext e (Pi A F) = cong2 tpi (den-ext e A) (den-ext e F)
den-ext e (Sigma A F) = cong2 tsig (den-ext e A) (den-ext e F)
den-ext e (Pair t u) = cong2 tpair (den-ext e t) (den-ext e u)
den-ext e (Fst t) = Eq-cong tfst (den-ext e t)
den-ext e (Snd t) = Eq-cong tsnd (den-ext e t)
den-ext e Nat = refl
den-ext e Zero = refl
den-ext e (Suc t) = Eq-cong tsc (den-ext e t)
den-ext e (Rec C z s k) = cong4 trec (den-ext e C) (den-ext e z) (den-ext e s) (den-ext e k)
den-ext e V = refl
den-ext e (Ucode f g) = cong2 tU (den-ext e f) (den-ext e g)
den-ext e (Fhat f g A F) = cong2 tapp (cong2 tapp (den-ext e f) (den-ext e A)) (den-ext e F)
den-ext e (Ghat f g A F c) =
  cong2 tapp (cong2 tapp (cong2 tapp (den-ext e g) (den-ext e A)) (den-ext e F)) (den-ext e c)

-- syntactic renaming of the expression
den-renE : {n m : Num} (r : MAHLO.Syntax.Ren n m) (rho : TEnv m) (t : Expr n) ->
           Eq (den (renExpr r t) rho) (den t (\ i -> rho (r i)))
den-renE r rho (Var i) = refl
den-renE r rho (Lam A t) =
  Eq-cong tlam (Eq-trans (den-renE (liftRen r) (up rho) t) (den-ext e t))
  where
    e : PW (\ i -> up rho (liftRen r i)) (up (\ i -> rho (r i)))
    e fzero = refl
    e (fsuc i) = refl
den-renE r rho (App t u) = cong2 tapp (den-renE r rho t) (den-renE r rho u)
den-renE r rho (Pi A F) = cong2 tpi (den-renE r rho A) (den-renE r rho F)
den-renE r rho (Sigma A F) = cong2 tsig (den-renE r rho A) (den-renE r rho F)
den-renE r rho (Pair t u) = cong2 tpair (den-renE r rho t) (den-renE r rho u)
den-renE r rho (Fst t) = Eq-cong tfst (den-renE r rho t)
den-renE r rho (Snd t) = Eq-cong tsnd (den-renE r rho t)
den-renE r rho Nat = refl
den-renE r rho Zero = refl
den-renE r rho (Suc t) = Eq-cong tsc (den-renE r rho t)
den-renE r rho (Rec C z s k) =
  cong4 trec (den-renE r rho C) (den-renE r rho z) (den-renE r rho s) (den-renE r rho k)
den-renE r rho V = refl
den-renE r rho (Ucode f g) = cong2 tU (den-renE r rho f) (den-renE r rho g)
den-renE r rho (Fhat f g A F) =
  cong2 tapp (cong2 tapp (den-renE r rho f) (den-renE r rho A)) (den-renE r rho F)
den-renE r rho (Ghat f g A F c) =
  cong2 tapp (cong2 tapp (cong2 tapp (den-renE r rho g) (den-renE r rho A)) (den-renE r rho F))
             (den-renE r rho c)

-- substitution on the values commutes with den
sub-den : {n : Num} (s : Sb) (rho : TEnv n) (t : Expr n) ->
          Eq (sub s (den t rho)) (den t (\ i -> sub s (rho i)))
sub-den s rho (Var i) = refl
sub-den s rho (Lam A t) =
  Eq-cong tlam (Eq-trans (sub-den (liftS s) (up rho) t) (den-ext e t))
  where
    e : PW (\ i -> sub (liftS s) (up rho i)) (up (\ i -> sub s (rho i)))
    e fzero = refl
    e (fsuc i) = sub-shift-comm s (rho i)
sub-den s rho (App t u) = cong2 tapp (sub-den s rho t) (sub-den s rho u)
sub-den s rho (Pi A F) = cong2 tpi (sub-den s rho A) (sub-den s rho F)
sub-den s rho (Sigma A F) = cong2 tsig (sub-den s rho A) (sub-den s rho F)
sub-den s rho (Pair t u) = cong2 tpair (sub-den s rho t) (sub-den s rho u)
sub-den s rho (Fst t) = Eq-cong tfst (sub-den s rho t)
sub-den s rho (Snd t) = Eq-cong tsnd (sub-den s rho t)
sub-den s rho Nat = refl
sub-den s rho Zero = refl
sub-den s rho (Suc t) = Eq-cong tsc (sub-den s rho t)
sub-den s rho (Rec C z u k) =
  cong4 trec (sub-den s rho C) (sub-den s rho z) (sub-den s rho u) (sub-den s rho k)
sub-den s rho V = refl
sub-den s rho (Ucode f g) = cong2 tU (sub-den s rho f) (sub-den s rho g)
sub-den s rho (Fhat f g A F) =
  cong2 tapp (cong2 tapp (sub-den s rho f) (sub-den s rho A)) (sub-den s rho F)
sub-den s rho (Ghat f g A F c) =
  cong2 tapp (cong2 tapp (cong2 tapp (sub-den s rho g) (sub-den s rho A)) (sub-den s rho F))
             (sub-den s rho c)

-- substitution in the expression
den-subE : {h g : Num} (s : MAHLO.Syntax.Sub h g) (rho : TEnv h) (t : Expr g) ->
           Eq (den (substExpr s t) rho) (den t (\ i -> den (s i) rho))
den-subE s rho (Var i) = refl
den-subE s rho (Lam A t) =
  Eq-cong tlam (Eq-trans (den-subE (liftSub s) (up rho) t) (den-ext e t))
  where
    e : PW (\ i -> den (liftSub s i) (up rho)) (up (\ i -> den (s i) rho))
    e fzero = refl
    e (fsuc i) =
      Eq-trans (den-renE wkRen (up rho) (s i))
        (Eq-trans (den-ext (\ j -> ren-as-sub suc (rho j)) (s i))
          (Eq-trans (Eq-sym (sub-den (\ k -> tvar (suc k)) rho (s i)))
                    (Eq-sym (ren-as-sub suc (den (s i) rho)))))
den-subE s rho (App t u) = cong2 tapp (den-subE s rho t) (den-subE s rho u)
den-subE s rho (Pi A F) = cong2 tpi (den-subE s rho A) (den-subE s rho F)
den-subE s rho (Sigma A F) = cong2 tsig (den-subE s rho A) (den-subE s rho F)
den-subE s rho (Pair t u) = cong2 tpair (den-subE s rho t) (den-subE s rho u)
den-subE s rho (Fst t) = Eq-cong tfst (den-subE s rho t)
den-subE s rho (Snd t) = Eq-cong tsnd (den-subE s rho t)
den-subE s rho Nat = refl
den-subE s rho Zero = refl
den-subE s rho (Suc t) = Eq-cong tsc (den-subE s rho t)
den-subE s rho (Rec C z u k) =
  cong4 trec (den-subE s rho C) (den-subE s rho z) (den-subE s rho u) (den-subE s rho k)
den-subE s rho V = refl
den-subE s rho (Ucode f g) = cong2 tU (den-subE s rho f) (den-subE s rho g)
den-subE s rho (Fhat f g A F) =
  cong2 tapp (cong2 tapp (den-subE s rho f) (den-subE s rho A)) (den-subE s rho F)
den-subE s rho (Ghat f g A F c) =
  cong2 tapp (cong2 tapp (cong2 tapp (den-subE s rho g) (den-subE s rho A)) (den-subE s rho F))
             (den-subE s rho c)

-- convertible environments give convertible denotations
den-cv : {n : Num} {rho rho' : TEnv n} -> ((i : Fin n) -> Conv (rho i) (rho' i)) ->
         (t : Expr n) -> Conv (den t rho) (den t rho')
den-cv e (Var i) = e i
den-cv {rho = rho} {rho'} e (Lam A t) = cv-lam (den-cv e' t)
  where
    e' : (i : Fin _) -> Conv (up rho i) (up rho' i)
    e' fzero = cv-refl
    e' (fsuc i) = cv-ren suc (e i)
den-cv e (App t u) = cv-app (den-cv e t) (den-cv e u)
den-cv e (Pi A F) = cv-pi (den-cv e A) (den-cv e F)
den-cv e (Sigma A F) = cv-sig (den-cv e A) (den-cv e F)
den-cv e (Pair t u) = cv-pair (den-cv e t) (den-cv e u)
den-cv e (Fst t) = cv-fst (den-cv e t)
den-cv e (Snd t) = cv-snd (den-cv e t)
den-cv e Nat = cv-refl
den-cv e Zero = cv-refl
den-cv e (Suc t) = cv-sc (den-cv e t)
den-cv e (Rec C z s k) = cv-rec (den-cv e C) (den-cv e z) (den-cv e s) (den-cv e k)
den-cv e V = cv-refl
den-cv e (Ucode f g) = cv-U (den-cv e f) (den-cv e g)
den-cv e (Fhat f g A F) = cv-app (cv-app (den-cv e f) (den-cv e A)) (den-cv e F)
den-cv e (Ghat f g A F c) = cv-app (cv-app (cv-app (den-cv e g) (den-cv e A)) (den-cv e F)) (den-cv e c)

------------------------------------------------------------------------
-- The two laws of the Model record that are not immediate
------------------------------------------------------------------------

cons' : {n : Num} -> TEnv n -> Tm -> TEnv (suc n)
cons' rho d fzero = d
cons' rho d (fsuc i) = rho i

den-subst' : {h g : Num} (s : MAHLO.Syntax.Sub h g) (rho : TEnv h) (rho' : TEnv g) ->
             ((i : Fin g) -> Conv (rho' i) (den (s i) rho)) ->
             (t : Expr g) -> Conv (den (substExpr s t) rho) (den t rho')
den-subst' s rho rho' e t =
  cv-trans (transport (\ z -> Conv (den (substExpr s t) rho) z) (den-subE s rho t) cv-refl)
           (den-cv (\ i -> cv-sym (e i)) t)

den-Lam' : {n : Num} {rho : TEnv n} (A : Expr n) (t : Expr (suc n)) (d : Tm) ->
           Conv (tapp (den (Lam A t) rho) d) (den t (cons' rho d))
den-Lam' {rho = rho} A t d =
  cv-trans (cv-step s-beta)
    (transport (\ z -> Conv (inst (den t (up rho)) d) z)
      (Eq-trans (sub-den (sub0 d) (up rho) t) (den-ext e t)) cv-refl)
  where
    e : PW (\ i -> sub (sub0 d) (up rho i)) (cons' rho d)
    e fzero = refl
    e (fsuc i) = inst-shift (rho i) d
