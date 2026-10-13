{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/CompLem.agda
--
-- Lemmas for completeness: values of syntactic weak-head normal forms,
-- decomposed along their shapes (at the identity environment), and the
-- arithmetic of the measure in each case.
------------------------------------------------------------------------

module MAHLOALG.CompLem where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Den
open import MAHLO.Concrete.Std
open import MAHLO.Concrete.EtaLemmas using (ne-ren)
import MAHLOALG.Measure as M
open M using (_<=_ ; z<= ; s<= ; <=-refl ; <=-trans ; <=-suc ; +-mono ; pred<= ; sz ; lp ; lp-ren ; sz-ren)
  renaming (_+_ to _⊕_)
open import MAHLOALG.Shape

------------------------------------------------------------------------
-- values along shapes
------------------------------------------------------------------------

private
  valLamInv : {x : Tm} -> Val (tlam x) -> Val x
  valLamInv (v-ne ())
  valLamInv (v-lam b) = b

  valPairInv : {x y : Tm} -> Val (tpair x y) -> Val x * Val y
  valPairInv (v-ne ())
  valPairInv (v-pair a b) = a , b

  valPiInv : {x y : Tm} -> Val (tpi x y) -> Val x * Val y
  valPiInv (v-ne ())
  valPiInv (v-pi a b) = a , b

  valSigInv : {x y : Tm} -> Val (tsig x y) -> Val x * Val y
  valSigInv (v-ne ())
  valSigInv (v-sig a b) = a , b

  valScInv : {x : Tm} -> Val (tsc x) -> Val x
  valScInv (v-ne ())
  valScInv (v-sc a) = a

  valUInv : {x y : Tm} -> Val (tU x y) -> Val x * Val y
  valUInv (v-ne ())
  valUInv (v-U a b) = a , b

  valAppInv : {x y : Tm} -> Val (tapp x y) -> Ne x * Val y
  valAppInv (v-ne (ne-app n v)) = n , v

  valFstInv : {x : Tm} -> Val (tfst x) -> Ne x
  valFstInv (v-ne (ne-fst n)) = n

  valSndInv : {x : Tm} -> Val (tsnd x) -> Ne x
  valSndInv (v-ne (ne-snd n)) = n

  valRecInv : {C z s k : Tm} -> Val (trec C z s k) -> Val C * (Val z * (Val s * Ne k))
  valRecInv (v-ne (ne-rec C z s k)) = C , (z , (s , k))

  tr⇓ : {a a' v : Tm} -> Eq a a' -> a ⇓ v -> a' ⇓ v
  tr⇓ refl d = d

  mk⇓ : {a v w : Tm} -> Red a w -> Eq v w -> Val v -> a ⇓ v
  mk⇓ r refl vv = r , vv

record VLam {n : Num} (b : Expr (suc n)) (v : Tm) : Set where
  constructor vlam
  field
    x  : Tm
    ev : Eq v (tlam x)
    dx : den b idE ⇓ x

valLam : {n : Num} {A : Expr n} {b : Expr (suc n)} {v : Tm} -> den (Lam A b) idE ⇓ v -> VLam b v
valLam {b = b} (r , vv) =
  let k = red-lam r ; e = fst (snd k)
  in vlam (fst k) e (tr⇓ (denU b) (mk⇓ (snd (snd k)) refl (valLamInv (transport Val e vv))))

record V2 (a b : Tm) (c : Tm -> Tm -> Tm) (v : Tm) : Set where
  constructor v2
  field
    x y : Tm
    ev  : Eq v (c x y)
    dx  : a ⇓ x
    dy  : b ⇓ y

valPair : {n : Num} {a b : Expr n} {v : Tm} -> den (Pair a b) idE ⇓ v -> V2 (den a idE) (den b idE) tpair v
valPair (r , vv) =
  let k = red-pair r ; e = fst (snd (snd k)) ; vs = valPairInv (transport Val e vv)
  in v2 _ _ e (fst (snd (snd (snd k))) , fst vs) (snd (snd (snd (snd k))) , snd vs)

valPi : {n : Num} {A F : Expr n} {v : Tm} -> den (Pi A F) idE ⇓ v -> V2 (den A idE) (den F idE) tpi v
valPi (r , vv) =
  let k = red-pi r ; e = fst (snd (snd k)) ; vs = valPiInv (transport Val e vv)
  in v2 _ _ e (fst (snd (snd (snd k))) , fst vs) (snd (snd (snd (snd k))) , snd vs)

valSig : {n : Num} {A F : Expr n} {v : Tm} -> den (Sigma A F) idE ⇓ v -> V2 (den A idE) (den F idE) tsig v
valSig (r , vv) =
  let k = red-sig r ; e = fst (snd (snd k)) ; vs = valSigInv (transport Val e vv)
  in v2 _ _ e (fst (snd (snd (snd k))) , fst vs) (snd (snd (snd (snd k))) , snd vs)

valU : {n : Num} {f g : Expr n} {v : Tm} -> den (Ucode f g) idE ⇓ v -> V2 (den f idE) (den g idE) tU v
valU (r , vv) =
  let k = red-U r ; e = fst (snd (snd k)) ; vs = valUInv (transport Val e vv)
  in v2 _ _ e (fst (snd (snd (snd k))) , fst vs) (snd (snd (snd (snd k))) , snd vs)

record V1 (a : Tm) (c : Tm -> Tm) (v : Tm) : Set where
  constructor v1
  field
    x  : Tm
    ev : Eq v (c x)
    dx : a ⇓ x

valSc : {n : Num} {k : Expr n} {v : Tm} -> den (Suc k) idE ⇓ v -> V1 (den k idE) tsc v
valSc (r , vv) = let k = red-sc r ; e = fst (snd k) in v1 _ e (snd (snd k) , valScInv (transport Val e vv))

-- neutrals
wneOf : {n : Num} {w : Expr n} -> SNe w -> WNe (den w idE)
wneOf sne-var = wn-var
wneOf (sne-app n) = wn-app (wneOf n)
wneOf (sne-fst n) = wn-fst (wneOf n)
wneOf (sne-snd n) = wn-snd (wneOf n)
wneOf (sne-rec n) = wn-rec (wneOf n)

valApp : {n : Num} {u a : Expr n} {v : Tm} -> SNe u -> den (App u a) idE ⇓ v -> V2 (den u idE) (den a idE) tapp v
valApp nu (r , vv) =
  let k = red-app (wneOf nu) r ; e = fst (snd (snd k)) ; vs = valAppInv (transport Val e vv)
  in v2 _ _ e (fst (snd (snd (snd k))) , v-ne (fst vs)) (snd (snd (snd (snd k))) , snd vs)

valFst : {n : Num} {u : Expr n} {v : Tm} -> SNe u -> den (Fst u) idE ⇓ v -> V1 (den u idE) tfst v
valFst nu (r , vv) = let k = red-fst (wneOf nu) r ; e = fst (snd k) in v1 _ e (snd (snd k) , v-ne (valFstInv (transport Val e vv)))

valSnd : {n : Num} {u : Expr n} {v : Tm} -> SNe u -> den (Snd u) idE ⇓ v -> V1 (den u idE) tsnd v
valSnd nu (r , vv) = let k = red-snd (wneOf nu) r ; e = fst (snd k) in v1 _ e (snd (snd k) , v-ne (valSndInv (transport Val e vv)))

record VRec {n : Num} (C : Expr (suc n)) (z s k : Expr n) (v : Tm) : Set where
  constructor vrec
  field
    xc xz xs xk : Tm
    ev : Eq v (trec (tlam xc) xz xs xk)
    dc : den C idE ⇓ xc
    dz : den z idE ⇓ xz
    ds : den s idE ⇓ xs
    dk : den k idE ⇓ xk

valRec : {n : Num} {N z s k : Expr n} {C : Expr (suc n)} {v : Tm} -> SNe k -> den (Rec (Lam N C) z s k) idE ⇓ v -> VRec C z s k v
valRec {C = C} nk (r , vv) =
  let k = red-rec (wneOf nk) r
      open RecRed k
      vs = valRecInv (transport Val ev vv)
      lc = red-lam rC
      e' = Eq-trans ev (Eq-cong (\ X -> trec X z' s' k') (fst (snd lc)))
      vc = valLamInv (transport Val (fst (snd lc)) (fst vs))
  in vrec (fst lc) z' s' k' e' (tr⇓ (denU C) (snd (snd lc) , vc)) (rz , fst (snd vs)) (rs , fst (snd (snd vs))) (rk , v-ne (snd (snd (snd vs))))

valVar : {n : Num} {i : Fin n} {v : Tm} -> den (Var i) idE ⇓ v -> Eq v (tvar (f2n i))
valVar (r-refl , vv) = refl
valVar (r-step () r , vv)

-- the value of a syntactic neutral is neutral
valNe : {n : Num} {w : Expr n} {v : Tm} -> SNe w -> den w idE ⇓ v -> Ne v
valNe nw (r , vv) = go (wneOf nw) r vv
  where
    goW : {a : Tm} -> WNe a -> Val a -> Ne a
    goW n (v-ne m) = m
    goW () (v-lam b)
    goW () (v-pair a b)
    goW () (v-pi a b)
    goW () (v-sig a b)
    goW () v-nat
    goW () v-ze
    goW () (v-sc a)
    goW () v-V
    goW () (v-U a b)
    go : {a v : Tm} -> WNe a -> Red a v -> Val v -> Ne v
    go n r-refl vv = goW n vv
    go n (r-step s r) vv = go (wne-step n s) r vv

-- the weakened neutral applied to x0
denWk : {n : Num} (t : Expr n) -> Eq (den (wkExpr t) (idE {suc n})) (shift (den t idE))
denWk t =
  Eq-trans (den-renE wkRen idE t)
    (Eq-sym (Eq-trans (ren-as-sub suc (den t idE)) (sub-den (\ k -> tvar (suc k)) idE t)))

valWkApp : {n : Num} {w : Expr n} {v : Tm} -> Ne v -> den w idE ⇓ v ->
  den (App (wkExpr w) x0) idE ⇓ tapp (shift v) (tvar zero)
valWkApp {w = w} nv (r , vv) =
  tr⇓ (Eq-cong (\ X -> tapp X (tvar zero)) (Eq-sym (denWk w)))
    (R-app (Red-ren suc r) r-refl , v-ne (ne-app (ne-ren suc nv) (v-ne ne-var)))

valFstOf : {n : Num} {w : Expr n} {v : Tm} -> Ne v -> den w idE ⇓ v -> den (Fst w) idE ⇓ tfst v
valFstOf nv (r , vv) = R-fst r , v-ne (ne-fst nv)

valSndOf : {n : Num} {w : Expr n} {v : Tm} -> Ne v -> den w idE ⇓ v -> den (Snd w) idE ⇓ tsnd v
valSndOf nv (r , vv) = R-snd r , v-ne (ne-snd nv)

------------------------------------------------------------------------
-- arithmetic of the cases
------------------------------------------------------------------------

private
  +r : (x : Num) {y : Num} -> y <= (x ⊕ y)
  +r zero = <=-refl _
  +r (suc x) = <=-suc (+r x)

  +l : (x y : Num) -> x <= (x ⊕ y)
  +l zero y = z<=
  +l (suc x) y = s<= (+l x y)

<=+l : (x y : Num) -> x <= (x ⊕ y)
<=+l = +l

<=+r : (x y : Num) -> y <= (x ⊕ y)
<=+r x y = +r x

-- lambda / lambda :  lp x + lp y < lp (tlam x) + lp (tlam y)
ar-LL : (a b c : Num) -> (suc a ⊕ suc b) <= suc c -> (a ⊕ b) <= c
ar-LL a b c p = <=-trans (+-mono (<=-refl a) (<=-suc (<=-refl b))) (pred<= p)

-- lambda / neutral :  lp x + lp (shift v) < lp (tlam x) + lp v
ar-LN : (a b c : Num) -> (suc a ⊕ b) <= suc c -> (a ⊕ b) <= c
ar-LN a b c p = pred<= p

-- neutral / lambda
ar-NL : (a b c : Num) -> (a ⊕ suc b) <= suc c -> (a ⊕ b) <= c
ar-NL a b c p = pred<= (M.eq-<= (Eq-sym (M.+-suc a b)) p)

-- a part of a sum is below the sum (componentwise)
ar-sub : {a a' b b' : Num} -> a <= a' -> b <= b' -> {c : Num} -> (a' ⊕ b') <= c -> (a ⊕ b) <= c
ar-sub p q r = <=-trans (+-mono p q) r
