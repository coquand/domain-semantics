{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/EraseLemmas.agda
--
-- Erasure commutes with renaming and substitution, and with the derived
-- formers: |OpF| = OpF, |OpG f| = OpG |f|, |RecStep C| = RecStep |C|.
------------------------------------------------------------------------

module MAHLORT.EraseLemmas where

open import MAHLO.Basic
open import MAHLORT.TarskiSyntax as T
import MAHLO.Syntax as R
open import MAHLO.Syntax using (cong2 ; cong4 ; cong5)
open import MAHLORT.Erasure
import MAHLORT.TarskiTyping as TT
import MAHLO.Typing as RT

er-ren : {n m : Num} (r : Ren n m) (t : T.Expr n) -> Eq (er (renExpr r t)) (R.renExpr r (er t))
er-ren r (Var i) = refl
er-ren r (Lam x0 x1) = cong2 R.Lam (er-ren r x0) (er-ren (liftRen r) x1)
er-ren r (App x0 x1 x2 x3) = cong2 R.App (er-ren r x2) (er-ren r x3)
er-ren r (Pi x0 x1) = cong2 R.Pi (er-ren r x0) (er-ren r x1)
er-ren r (Sigma x0 x1) = cong2 R.Sigma (er-ren r x0) (er-ren r x1)
er-ren r (Pair x0 x1 x2 x3) = cong2 R.Pair (er-ren r x2) (er-ren r x3)
er-ren r (Fst x0 x1 x2) = Eq-cong R.Fst (er-ren r x2)
er-ren r (Snd x0 x1 x2) = Eq-cong R.Snd (er-ren r x2)
er-ren r Nat = refl
er-ren r Zero = refl
er-ren r (Suc x0) = Eq-cong R.Suc (er-ren r x0)
er-ren r (Rec x0 x1 x2 x3) = cong4 R.Rec (er-ren r x0) (er-ren r x1) (er-ren r x2) (er-ren r x3)
er-ren r V = refl
er-ren r (ElV x0) = er-ren r x0
er-ren r (TyU x0 x1) = cong2 R.Ucode (er-ren r x0) (er-ren r x1)
er-ren r (ElU x0 x1 x2) = er-ren r x2
er-ren r (PiV x0 x1) = cong2 R.Pi (er-ren r x0) (er-ren r x1)
er-ren r (SigV x0 x1) = cong2 R.Sigma (er-ren r x0) (er-ren r x1)
er-ren r NatV = refl
er-ren r (UV x0 x1) = cong2 R.Ucode (er-ren r x0) (er-ren r x1)
er-ren r (PiU x0 x1 x2 x3) = cong2 R.Pi (er-ren r x2) (er-ren r x3)
er-ren r (SigU x0 x1 x2 x3) = cong2 R.Sigma (er-ren r x2) (er-ren r x3)
er-ren r (NatU x0 x1) = refl
er-ren r (Fhat x0 x1 x2 x3) = cong4 R.Fhat (er-ren r x0) (er-ren r x1) (er-ren r x2) (er-ren r x3)
er-ren r (Ghat x0 x1 x2 x3 x4) = cong5 R.Ghat (er-ren r x0) (er-ren r x1) (er-ren r x2) (er-ren r x3) (er-ren r x4)
er-ren r (That x0) = er-ren r x0

er-wk : {n : Num} (t : T.Expr n) -> Eq (er (wkExpr t)) (R.wkExpr (er t))
er-wk t = er-ren wkRen t

er-liftSub : {h g : Num} (s : Sub h g) (i : Fin (suc g)) ->
             Eq (er (liftSub s i)) (R.liftSub (\ j -> er (s j)) i)
er-liftSub s fzero = refl
er-liftSub s (fsuc i) = er-wk (s i)

er-subst : {h g : Num} (s : Sub h g) (t : T.Expr g) ->
           Eq (er (substExpr s t)) (R.substExpr (\ i -> er (s i)) (er t))
er-subst s (Var i) = refl
er-subst s (Lam x0 x1) = cong2 R.Lam (er-subst s x0) (Eq-trans (er-subst (liftSub s) x1) (R.substExpr-ext _ _ (er-liftSub s) (er x1)))
er-subst s (App x0 x1 x2 x3) = cong2 R.App (er-subst s x2) (er-subst s x3)
er-subst s (Pi x0 x1) = cong2 R.Pi (er-subst s x0) (er-subst s x1)
er-subst s (Sigma x0 x1) = cong2 R.Sigma (er-subst s x0) (er-subst s x1)
er-subst s (Pair x0 x1 x2 x3) = cong2 R.Pair (er-subst s x2) (er-subst s x3)
er-subst s (Fst x0 x1 x2) = Eq-cong R.Fst (er-subst s x2)
er-subst s (Snd x0 x1 x2) = Eq-cong R.Snd (er-subst s x2)
er-subst s Nat = refl
er-subst s Zero = refl
er-subst s (Suc x0) = Eq-cong R.Suc (er-subst s x0)
er-subst s (Rec x0 x1 x2 x3) = cong4 R.Rec (er-subst s x0) (er-subst s x1) (er-subst s x2) (er-subst s x3)
er-subst s V = refl
er-subst s (ElV x0) = er-subst s x0
er-subst s (TyU x0 x1) = cong2 R.Ucode (er-subst s x0) (er-subst s x1)
er-subst s (ElU x0 x1 x2) = er-subst s x2
er-subst s (PiV x0 x1) = cong2 R.Pi (er-subst s x0) (er-subst s x1)
er-subst s (SigV x0 x1) = cong2 R.Sigma (er-subst s x0) (er-subst s x1)
er-subst s NatV = refl
er-subst s (UV x0 x1) = cong2 R.Ucode (er-subst s x0) (er-subst s x1)
er-subst s (PiU x0 x1 x2 x3) = cong2 R.Pi (er-subst s x2) (er-subst s x3)
er-subst s (SigU x0 x1 x2 x3) = cong2 R.Sigma (er-subst s x2) (er-subst s x3)
er-subst s (NatU x0 x1) = refl
er-subst s (Fhat x0 x1 x2 x3) = cong4 R.Fhat (er-subst s x0) (er-subst s x1) (er-subst s x2) (er-subst s x3)
er-subst s (Ghat x0 x1 x2 x3 x4) = cong5 R.Ghat (er-subst s x0) (er-subst s x1) (er-subst s x2) (er-subst s x3) (er-subst s x4)
er-subst s (That x0) = er-subst s x0

er-subst1 : {n : Num} (B : T.Expr (suc n)) (a : T.Expr n) ->
            Eq (er (subst1 B a)) (R.subst1 (er B) (er a))
er-subst1 B a = Eq-trans (er-subst (subst1Sub a) B) (R.substExpr-ext _ _ e (er B))
  where
    e : (i : Fin _) -> Eq (er (subst1Sub a i)) (R.subst1Sub (er a) i)
    e fzero = refl
    e (fsuc i) = refl

------------------------------------------------------------------------
-- Derived formers
------------------------------------------------------------------------

er-OpF : {n : Num} -> Eq (er (OpF {n})) R.OpF
er-OpF = refl

private
  OpG' : {n : Num} -> R.Expr (suc (suc n)) -> R.Expr n
  OpG' ff = R.PiB R.V (R.PiB (R.Arr R.x0 R.V) (R.Arr (R.App (R.App ff R.x1) R.x0) R.V))

er-OpG : {n : Num} (f : T.Expr n) -> Eq (er (OpG f)) (R.OpG (er f))
er-OpG f = Eq-cong OpG' (Eq-trans (er-wk (wkExpr f)) (Eq-cong R.wkExpr (er-wk f)))

er-sucSub : {n : Num} (C : T.Expr (suc n)) ->
            Eq (er (substExpr sucSub C)) (R.substExpr R.sucSub (er C))
er-sucSub C = Eq-trans (er-subst sucSub C) (R.substExpr-ext _ _ e (er C))
  where
    e : (i : Fin _) -> Eq (er (sucSub i)) (R.sucSub i)
    e fzero = refl
    e (fsuc i) = refl

private
  RS : {n : Num} -> R.Expr (suc n) -> R.Expr (suc (suc n)) -> R.Expr n
  RS C E = R.Pi R.Nat (R.Lam R.Nat (R.Pi C (R.Lam C E)))

er-RecStep : {n : Num} (C : T.Expr (suc n)) -> Eq (er (RecStep C)) (R.RecStep (er C))
er-RecStep C =
  Eq-cong (RS (er C)) (Eq-trans (er-wk (substExpr sucSub C)) (Eq-cong R.wkExpr (er-sucSub C)))

er-lookup : {n : Num} (G : TT.Ctx n) (i : Fin n) -> Eq (er (TT.lookup G i)) (RT.lookup (erCtx G) i)
er-lookup (TT.extend G A) fzero = er-wk A
er-lookup (TT.extend G A) (fsuc i) = Eq-trans (er-wk (TT.lookup G i)) (Eq-cong R.wkExpr (er-lookup G i))

