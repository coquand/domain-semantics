{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Model.Strip
--
-- Russell terms -> core terms of the model: forget the codomain
-- annotation B of λ(A,B,b) and both annotations of app(A,B,c,a).
-- The model interprets λ through its domain A only, and application
-- through its function and argument only, so nothing is lost.
--
-- strip commutes with renaming, substitution and context lookup.
------------------------------------------------------------------------

module ERT.Model.Strip where

open import ERT.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-sym ; Eq-cong ;
  Fin ; fzero ; fsuc ; Ren ; liftRen ; wkRen)
import ERT.RussellSyntax as R
import ERT.RussellTyping as RT
import ERT.Model.Core as C
open C using (Eq-trans ; Eq-cong2-Expr)

strip : {n : Nat} -> R.Expr n -> C.Expr n
strip (R.Var i)       = C.Var i
strip (R.U l)         = C.U l
strip (R.Pi A B)      = C.Pi (strip A) (strip B)
strip (R.Lam A B b)   = C.Lam (strip A) (strip b)
strip (R.App A B c a) = C.App (strip c) (strip a)

stripCtx : {n : Nat} -> RT.Ctx n -> C.Ctx n
stripCtx RT.empty        = C.empty
stripCtx (RT.extend G A) = C.extend (stripCtx G) (strip A)

strip-ren : {n m : Nat} (r : Ren n m) (M : R.Expr n)
  -> Eq (strip (R.renExpr r M)) (C.renExpr r (strip M))
strip-ren r (R.Var i)       = refl
strip-ren r (R.U l)         = refl
strip-ren r (R.Pi A B)      =
  Eq-cong2-Expr C.Pi (strip-ren r A) (strip-ren (liftRen r) B)
strip-ren r (R.Lam A B b)   =
  Eq-cong2-Expr C.Lam (strip-ren r A) (strip-ren (liftRen r) b)
strip-ren r (R.App A B c a) =
  Eq-cong2-Expr C.App (strip-ren r c) (strip-ren r a)

strip-wk : {n : Nat} (M : R.Expr n)
  -> Eq (strip (R.wkExpr M)) (C.wkExpr (strip M))
strip-wk M = strip-ren wkRen M

strip-liftSub : {h g : Nat} (sigma : R.Sub h g) (i : Fin (suc g))
  -> Eq (strip (R.liftSub sigma i)) (C.liftSub (\ j -> strip (sigma j)) i)
strip-liftSub sigma fzero    = refl
strip-liftSub sigma (fsuc i) = strip-wk (sigma i)

strip-subst : {h g : Nat} (sigma : R.Sub h g) (M : R.Expr g)
  -> Eq (strip (R.substExpr sigma M)) (C.substExpr (\ j -> strip (sigma j)) (strip M))
strip-subst sigma (R.Var i)       = refl
strip-subst sigma (R.U l)         = refl
strip-subst sigma (R.Pi A B)      =
  Eq-cong2-Expr C.Pi (strip-subst sigma A)
    (Eq-trans (strip-subst (R.liftSub sigma) B)
      (C.substExpr-ext _ _ (strip-liftSub sigma) (strip B)))
strip-subst sigma (R.Lam A B b)   =
  Eq-cong2-Expr C.Lam (strip-subst sigma A)
    (Eq-trans (strip-subst (R.liftSub sigma) b)
      (C.substExpr-ext _ _ (strip-liftSub sigma) (strip b)))
strip-subst sigma (R.App A B c a) =
  Eq-cong2-Expr C.App (strip-subst sigma c) (strip-subst sigma a)

strip-subst1 : {n : Nat} (B : R.Expr (suc n)) (a : R.Expr n)
  -> Eq (strip (R.subst1 B a)) (C.subst1 (strip B) (strip a))
strip-subst1 B a =
  Eq-trans (strip-subst (R.subst1Sub a) B)
    (C.substExpr-ext _ _ ext (strip B))
  where
    ext : (i : Fin _) -> Eq (strip (R.subst1Sub a i)) (C.subst1Sub (strip a) i)
    ext fzero    = refl
    ext (fsuc i) = refl

strip-lookup : {n : Nat} (G : RT.Ctx n) (i : Fin n)
  -> Eq (strip (RT.lookup G i)) (C.lookup (stripCtx G) i)
strip-lookup (RT.extend G A) fzero    = strip-wk A
strip-lookup (RT.extend G A) (fsuc i) =
  Eq-trans (strip-wk (RT.lookup G i)) (Eq-cong C.wkExpr (strip-lookup G i))
