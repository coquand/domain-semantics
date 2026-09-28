{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.Strip
--
-- Russell terms (U : U) -> core terms of the model: the single universe
-- is interpreted as the level-0 universe of the (levelled) model, whose
-- membership relation ignores levels.  Forget the codomain
-- annotation B of λ(A,B,b) and both annotations of app(A,B,c,a).
-- The model interprets λ through its domain A only, and application
-- through its function and argument only, so nothing is lost.
--
-- strip commutes with renaming, substitution and context lookup.
------------------------------------------------------------------------

module BCDE4.Model.Strip where

open import BCDE4.Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-sym ; Eq-cong ;
  Fin ; fzero ; fsuc ; Ren ; liftRen ; wkRen)
import BCDE4.RussellSyntax as R
import BCDE4.RussellTyping as RT
import BCDE4.Model.Core as C
open import BCDE4.Levels using (LSub ; lsubC ; lsubL ; liftL ; lwkS)
open C using (Eq-trans ; Eq-cong2-Expr)

strip : {n : Nat} -> R.Expr n -> C.Expr n
strip (R.Var i)       = C.Var i
strip (R.U l)         = C.U l
strip (R.Pi A B)      = C.Pi (strip A) (strip B)
strip (R.Lam A B b)   = C.Lam (strip A) (strip b)
strip (R.App A B c a) = C.App (strip c) (strip a)
strip (R.Grd c A)     = C.Grd c (strip A)
strip (R.GLam c A t)    = C.GLam c (strip t)
strip R.Emp           = C.Emp
strip (R.LPi A)       = C.LPi (strip A)
strip (R.LLam A u)      = C.LLam (strip u)
strip (R.LApp A t l)    = C.LApp (strip t) l

strip-lsubE : {n : Nat} (z : LSub) (M : R.Expr n) -> Eq (strip (R.lsubE z M)) (C.lsubE z (strip M))
strip-lsubE z (R.Var i)       = refl
strip-lsubE z (R.U l)         = refl
strip-lsubE z (R.Pi A B)      = Eq-cong2-Expr C.Pi (strip-lsubE z A) (strip-lsubE z B)
strip-lsubE z (R.Lam A B b)   = Eq-cong2-Expr C.Lam (strip-lsubE z A) (strip-lsubE z b)
strip-lsubE z (R.App A B c a) = Eq-cong2-Expr C.App (strip-lsubE z c) (strip-lsubE z a)
strip-lsubE z (R.Grd c A)     = Eq-cong (C.Grd (lsubC z c)) (strip-lsubE z A)
strip-lsubE z (R.GLam c A t)    = Eq-cong (C.GLam (lsubC z c)) (strip-lsubE z t)
strip-lsubE z R.Emp           = refl
strip-lsubE z (R.LPi A)       = Eq-cong C.LPi (strip-lsubE (liftL z) A)
strip-lsubE z (R.LLam A u)      = Eq-cong C.LLam (strip-lsubE (liftL z) u)
strip-lsubE z (R.LApp A t l)    = Eq-cong (\ X -> C.LApp X (lsubL z l)) (strip-lsubE z t)

stripCtx : {n : Nat} -> RT.Ctx n -> C.Ctx n
stripCtx (RT.empty Th)   = C.empty Th
stripCtx (RT.extend G A) = C.extend (stripCtx G) (strip A)

strip-ren : {n m : Nat} (r : Ren n m) (M : R.Expr n)
  -> Eq (strip (R.renExpr r M)) (C.renExpr r (strip M))
strip-ren r (R.Var i)       = refl
strip-ren r (R.U l)     = refl
strip-ren r (R.Grd c A)  = Eq-cong (C.Grd c) (strip-ren r A)
strip-ren r (R.GLam c A t) = Eq-cong (C.GLam c) (strip-ren r t)
strip-ren r R.Emp        = refl
strip-ren r (R.LPi A)  = Eq-cong C.LPi (strip-ren r A)
strip-ren r (R.LLam A u) = Eq-cong C.LLam (strip-ren r u)
strip-ren r (R.LApp A t l) = Eq-cong (\ X -> C.LApp X l) (strip-ren r t)
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
strip-subst sigma (R.U l)     = refl
strip-subst sigma (R.Grd c A)  = Eq-cong (C.Grd c) (strip-subst sigma A)
strip-subst sigma (R.GLam c A t) = Eq-cong (C.GLam c) (strip-subst sigma t)
strip-subst sigma R.Emp        = refl
strip-subst sigma (R.LPi A)  =
  Eq-cong C.LPi (Eq-trans (strip-subst _ A) (C.substExpr-ext _ _ (\ j -> strip-lsubE lwkS (sigma j)) (strip A)))
strip-subst sigma (R.LLam A u) =
  Eq-cong C.LLam (Eq-trans (strip-subst _ u) (C.substExpr-ext _ _ (\ j -> strip-lsubE lwkS (sigma j)) (strip u)))
strip-subst sigma (R.LApp A t l) = Eq-cong (\ X -> C.LApp X l) (strip-subst sigma t)
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

strip-lctx : {n : Nat} (G : RT.Ctx n) -> Eq (C.lctx (stripCtx G)) (RT.lctx G)
strip-lctx (RT.empty Th)   = refl
strip-lctx (RT.extend G A) = strip-lctx G
