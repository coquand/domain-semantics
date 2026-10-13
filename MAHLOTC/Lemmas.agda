{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Lemmas.agda
--
-- Small typing facts for the checker: inversion of IsType for the type
-- formers, and injectivity of Lam on syntax.
------------------------------------------------------------------------

open import MAHLOINJ.Inversion.Hyp

module MAHLOTC.Lemmas (H : InjHyp) where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Inversion.Inv H

lam-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} ->
          Eq (Lam A B) (Lam A' B') -> Eq A A' * Eq B B'
lam-inj refl = refl , refl

-- projections (total, junk outside their shape), to avoid K
dom : {n : Num} -> Expr n -> Expr n
dom (Var y0) = (Var y0)
dom (Lam y0 y1) = y0
dom (App y0 y1) = (App y0 y1)
dom (Pi y0 y1) = y0
dom (Sigma y0 y1) = y0
dom (Pair y0 y1) = (Pair y0 y1)
dom (Fst y0) = (Fst y0)
dom (Snd y0) = (Snd y0)
dom Nat = Nat
dom Zero = Zero
dom (Suc y0) = (Suc y0)
dom (Rec y0 y1 y2 y3) = (Rec y0 y1 y2 y3)
dom V = V
dom (Ucode y0 y1) = (Ucode y0 y1)
dom (Fhat y0 y1 y2 y3) = (Fhat y0 y1 y2 y3)
dom (Ghat y0 y1 y2 y3 y4) = (Ghat y0 y1 y2 y3 y4)

fam : {n : Num} -> Expr n -> Expr n
fam (Var y0) = (Var y0)
fam (Lam y0 y1) = (Lam y0 y1)
fam (App y0 y1) = (App y0 y1)
fam (Pi y0 y1) = y1
fam (Sigma y0 y1) = y1
fam (Pair y0 y1) = (Pair y0 y1)
fam (Fst y0) = (Fst y0)
fam (Snd y0) = (Snd y0)
fam Nat = Nat
fam Zero = Zero
fam (Suc y0) = (Suc y0)
fam (Rec y0 y1 y2 y3) = (Rec y0 y1 y2 y3)
fam V = V
fam (Ucode y0 y1) = (Ucode y0 y1)
fam (Fhat y0 y1 y2 y3) = (Fhat y0 y1 y2 y3)
fam (Ghat y0 y1 y2 y3 y4) = (Ghat y0 y1 y2 y3 y4)

body : {n : Num} -> Expr n -> Expr (suc n)
body (Var y0) = wkExpr (Var y0)
body (Lam y0 y1) = y1
body (App y0 y1) = wkExpr (App y0 y1)
body (Pi y0 y1) = wkExpr (Pi y0 y1)
body (Sigma y0 y1) = wkExpr (Sigma y0 y1)
body (Pair y0 y1) = wkExpr (Pair y0 y1)
body (Fst y0) = wkExpr (Fst y0)
body (Snd y0) = wkExpr (Snd y0)
body Nat = wkExpr Nat
body Zero = wkExpr Zero
body (Suc y0) = wkExpr (Suc y0)
body (Rec y0 y1 y2 y3) = wkExpr (Rec y0 y1 y2 y3)
body V = wkExpr V
body (Ucode y0 y1) = wkExpr (Ucode y0 y1)
body (Fhat y0 y1 y2 y3) = wkExpr (Fhat y0 y1 y2 y3)
body (Ghat y0 y1 y2 y3 y4) = wkExpr (Ghat y0 y1 y2 y3 y4)

piB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} ->
          Eq (PiB A B) (PiB A' B') -> Eq A A' * Eq B B'
piB-inj e = Eq-cong dom e , Eq-cong (\ T -> body (fam T)) e

sigB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} ->
           Eq (SigmaB A B) (SigmaB A' B') -> Eq A A' * Eq B B'
sigB-inj e = Eq-cong dom e , Eq-cong (\ T -> body (fam T)) e

-- the components of a Pi / Sigma type are types
private
  piTyInv' : {n : Num} {G : Ctx n} {T A : Expr n} {B : Expr (suc n)} ->
             IsType G T -> Eq T (PiB A B) -> IsType G A * IsType (extend G A) B
  piTyInv' (isty-Pi hA hB) e =
    let q = piB-inj e in
    transport (IsType _) (fst q) hA ,
    transport2 (\ X Y -> IsType (extend _ X) Y) (fst q) (snd q) hB
  piTyInv' (isty-el h) refl =
    elTy un hA ,
    transport (IsType _) (Eq-sym (snd (lam-inj eF))) (elTy (renUniv wkRen un) hB)
    where open PiInv (invPi h)
  piTyInv' (isty-V w) ()
  piTyInv' (isty-Sigma hA hB) ()

  sigTyInv' : {n : Num} {G : Ctx n} {T A : Expr n} {B : Expr (suc n)} ->
              IsType G T -> Eq T (SigmaB A B) -> IsType G A * IsType (extend G A) B
  sigTyInv' (isty-Sigma hA hB) e =
    let q = sigB-inj e in
    transport (IsType _) (fst q) hA ,
    transport2 (\ X Y -> IsType (extend _ X) Y) (fst q) (snd q) hB
  sigTyInv' (isty-el h) refl =
    elTy un hA ,
    transport (IsType _) (Eq-sym (snd (lam-inj eF))) (elTy (renUniv wkRen un) hB)
    where open PiInv (invSigma h)
  sigTyInv' (isty-V w) ()
  sigTyInv' (isty-Pi hA hB) ()

piTyInv : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
          IsType G (PiB A B) -> IsType G A * IsType (extend G A) B
piTyInv h = piTyInv' h refl

sigTyInv : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
           IsType G (SigmaB A B) -> IsType G A * IsType (extend G A) B
sigTyInv h = sigTyInv' h refl

-- a code that is a type is an element of V
ucTy : {n : Num} {G : Ctx n} {f g : Expr n} -> IsType G (Ucode f g) -> HasType G (Ucode f g) V
ucTy (isty-el h) = h

-- V is not an element of anything, in particular not of V
noVty : {n : Num} {G : Ctx n} -> HasType G V V -> Empty
noVty h = noV h

-- the family of a Pi/Sigma type is syntactically \x:A.B
piShape : {n : Num} {G : Ctx n} {T A F : Expr n} -> IsType G T -> Eq T (Pi A F) ->
          Sg (Expr (suc n)) (\ B -> Eq F (Lam A B))
piShape (isty-V w) ()
piShape {A = A} (isty-Pi {B = B1} hA hB) e =
  B1 , Eq-trans (Eq-sym (Eq-cong fam e)) (Eq-cong (\ X -> Lam X B1) (Eq-cong dom e))
piShape (isty-Sigma hA hB) ()
piShape (isty-el h) refl = PiInv.B r , PiInv.eF r
  where r = invPi h

sigShape : {n : Num} {G : Ctx n} {T A F : Expr n} -> IsType G T -> Eq T (Sigma A F) ->
           Sg (Expr (suc n)) (\ B -> Eq F (Lam A B))
sigShape (isty-V w) ()
sigShape (isty-Pi hA hB) ()
sigShape {A = A} (isty-Sigma {B = B1} hA hB) e =
  B1 , Eq-trans (Eq-sym (Eq-cong fam e)) (Eq-cong (\ X -> Lam X B1) (Eq-cong dom e))
sigShape (isty-el h) refl = PiInv.B r , PiInv.eF r
  where r = invSigma h
