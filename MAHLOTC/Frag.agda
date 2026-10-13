{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Frag.agda
--
-- The bidirectional fragment.
--   Inf t    t is inferable: its types form a finite list (up to TyEq),
--            saturated under the subsumption U(f,g) <= V;
--   Chk t    t is checkable: Inf, or one of the check-only forms
--            Pair (unannotated), Nat (it lies in EVERY valid U(f,g)),
--            and Lam / Pi / Sigma whose body / domain is check-only;
--   ChkTy A  A is a checkable type (also V, and Pi/Sigma of types).
-- Every beta-normal term is in Chk; the only terms left out are
-- beta-redexes App (Lam A b) c with check-only body b in inference
-- position, and projections of non-inferable terms.
------------------------------------------------------------------------

module MAHLOTC.Frag where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing using (Ctx ; empty ; extend)
open import MAHLOTC.Base using (Unit)

mutual
  Inf : {n : Num} -> Expr n -> Set
  Inf (Var i) = Unit
  Inf (Lam A b) = ChkTy A * Inf b
  Inf (App t a) = Inf t * Chk a
  Inf (Pi A F) = Inf A * FamF F
  Inf (Sigma A F) = Inf A * FamF F
  Inf (Pair a b) = Empty
  Inf (Fst t) = Inf t
  Inf (Snd t) = Inf t
  Inf Nat = Empty
  Inf Zero = Unit
  Inf (Suc t) = Chk t
  Inf (Rec C z s k) = MotF C * (Chk z * (Chk s * Chk k))
  Inf V = Unit
  Inf (Ucode f g) = Chk f * Chk g
  Inf (Fhat f g A F) = Chk f * (Chk g * (Chk A * FamF F))
  Inf (Ghat f g A F c) = Chk f * (Chk g * (Chk A * (FamF F * Chk c)))

  ChkOnly : {n : Num} -> Expr n -> Set
  ChkOnly (Var i) = Empty
  ChkOnly (Lam A b) = ChkTy A * Chk b
  ChkOnly (App t a) = Empty
  ChkOnly (Pi A F) = Chk A * FamF F
  ChkOnly (Sigma A F) = Chk A * FamF F
  ChkOnly (Pair a b) = Chk a * Chk b
  ChkOnly (Fst t) = Empty
  ChkOnly (Snd t) = Empty
  ChkOnly Nat = Unit
  ChkOnly Zero = Empty
  ChkOnly (Suc t) = Empty
  ChkOnly (Rec C z s k) = Empty
  ChkOnly V = Empty
  ChkOnly (Ucode f g) = Empty
  ChkOnly (Fhat f g A F) = Empty
  ChkOnly (Ghat f g A F c) = Empty

  TyOnly : {n : Num} -> Expr n -> Set
  TyOnly (Var i) = Empty
  TyOnly (Lam A b) = Empty
  TyOnly (App t a) = Empty
  TyOnly (Pi A F) = ChkTy A * FamTy F
  TyOnly (Sigma A F) = ChkTy A * FamTy F
  TyOnly (Pair a b) = Empty
  TyOnly (Fst t) = Empty
  TyOnly (Snd t) = Empty
  TyOnly Nat = Empty
  TyOnly Zero = Empty
  TyOnly (Suc t) = Empty
  TyOnly (Rec C z s k) = Empty
  TyOnly V = Unit
  TyOnly (Ucode f g) = Empty
  TyOnly (Fhat f g A F) = Empty
  TyOnly (Ghat f g A F c) = Empty

  Chk : {n : Num} -> Expr n -> Set
  Chk t = Inf t + ChkOnly t

  ChkTy : {n : Num} -> Expr n -> Set
  ChkTy t = Chk t + TyOnly t

  -- the family argument  \x:A.B  of Pi, Sigma, fhat, ghat
  FamF : {n : Num} -> Expr n -> Set
  FamF (Var i) = Unit
  FamF (Lam A b) = Chk b
  FamF (App t a) = Unit
  FamF (Pi A F) = Unit
  FamF (Sigma A F) = Unit
  FamF (Pair a b) = Unit
  FamF (Fst t) = Unit
  FamF (Snd t) = Unit
  FamF Nat = Unit
  FamF Zero = Unit
  FamF (Suc t) = Unit
  FamF (Rec C z s k) = Unit
  FamF V = Unit
  FamF (Ucode f g) = Unit
  FamF (Fhat f g A F) = Unit
  FamF (Ghat f g A F c) = Unit

  FamTy : {n : Num} -> Expr n -> Set
  FamTy (Var i) = Unit
  FamTy (Lam A b) = ChkTy b
  FamTy (App t a) = Unit
  FamTy (Pi A F) = Unit
  FamTy (Sigma A F) = Unit
  FamTy (Pair a b) = Unit
  FamTy (Fst t) = Unit
  FamTy (Snd t) = Unit
  FamTy Nat = Unit
  FamTy Zero = Unit
  FamTy (Suc t) = Unit
  FamTy (Rec C z s k) = Unit
  FamTy V = Unit
  FamTy (Ucode f g) = Unit
  FamTy (Fhat f g A F) = Unit
  FamTy (Ghat f g A F c) = Unit

  -- the motive  \x:Nat.C  of rec
  MotF : {n : Num} -> Expr n -> Set
  MotF (Var i) = Unit
  MotF (Lam A b) = ChkTy b
  MotF (App t a) = Unit
  MotF (Pi A F) = Unit
  MotF (Sigma A F) = Unit
  MotF (Pair a b) = Unit
  MotF (Fst t) = Unit
  MotF (Snd t) = Unit
  MotF Nat = Unit
  MotF Zero = Unit
  MotF (Suc t) = Unit
  MotF (Rec C z s k) = Unit
  MotF V = Unit
  MotF (Ucode f g) = Unit
  MotF (Fhat f g A F) = Unit
  MotF (Ghat f g A F c) = Unit

ChkCtx : {n : Num} -> Ctx n -> Set
ChkCtx empty = Unit
ChkCtx (extend G A) = ChkCtx G * ChkTy A

-- Inf <= Chk <= ChkTy
inf-chk : {n : Num} {t : Expr n} -> Inf t -> Chk t
inf-chk p = inl p

chk-ty : {n : Num} {t : Expr n} -> Chk t -> ChkTy t
chk-ty p = inl p

