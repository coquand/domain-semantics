{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Conv.agda
--
-- Conversion  a ~~ b  :=  a and b have a common reduct.  By
-- Church-Rosser it is an equivalence; it is a congruence; constructor
-- heads are preserved by reduction, hence constructors are injective
-- and pairwise disjoint up to conversion  (assumption (A1)).
------------------------------------------------------------------------

module MAHLO.Concrete.Conv where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Confluence

Conv : Tm -> Tm -> Set
Conv a b = Sigma Tm (\ c -> Red a c * Red b c)

cv-refl : {a : Tm} -> Conv a a
cv-refl {a} = a , (r-refl , r-refl)

cv-sym : {a b : Tm} -> Conv a b -> Conv b a
cv-sym (c , (p , q)) = c , (q , p)

cv-trans : {a b c : Tm} -> Conv a b -> Conv b c -> Conv a c
cv-trans (d , (p , q)) (e , (p' , q')) =
  let s = confluent q p' in
  fst s , (Red-trans p (fst (snd s)) , Red-trans q' (snd (snd s)))

cv-red : {a b : Tm} -> Red a b -> Conv a b
cv-red {b = b} p = b , (p , r-refl)

cv-step : {a b : Tm} -> Step a b -> Conv a b
cv-step s = cv-red (Red-one s)

-- congruences
cv-lam : {b b' : Tm} -> Conv b b' -> Conv (tlam b) (tlam b')
cv-lam (c , (p , q)) = tlam c , (R-lam p , R-lam q)

cv-app : {t t' u u' : Tm} -> Conv t t' -> Conv u u' -> Conv (tapp t u) (tapp t' u')
cv-app (c , (p , q)) (d , (p' , q')) = tapp c d , (R-app p p' , R-app q q')

cv-pi : {t t' u u' : Tm} -> Conv t t' -> Conv u u' -> Conv (tpi t u) (tpi t' u')
cv-pi (c , (p , q)) (d , (p' , q')) = tpi c d , (R-pi p p' , R-pi q q')

cv-sig : {t t' u u' : Tm} -> Conv t t' -> Conv u u' -> Conv (tsig t u) (tsig t' u')
cv-sig (c , (p , q)) (d , (p' , q')) = tsig c d , (R-sig p p' , R-sig q q')

cv-pair : {t t' u u' : Tm} -> Conv t t' -> Conv u u' -> Conv (tpair t u) (tpair t' u')
cv-pair (c , (p , q)) (d , (p' , q')) = tpair c d , (R-pair p p' , R-pair q q')

cv-U : {t t' u u' : Tm} -> Conv t t' -> Conv u u' -> Conv (tU t u) (tU t' u')
cv-U (c , (p , q)) (d , (p' , q')) = tU c d , (R-U p p' , R-U q q')

cv-fst : {t t' : Tm} -> Conv t t' -> Conv (tfst t) (tfst t')
cv-fst (c , (p , q)) = tfst c , (R-fst p , R-fst q)

cv-snd : {t t' : Tm} -> Conv t t' -> Conv (tsnd t) (tsnd t')
cv-snd (c , (p , q)) = tsnd c , (R-snd p , R-snd q)

cv-sc : {t t' : Tm} -> Conv t t' -> Conv (tsc t) (tsc t')
cv-sc (c , (p , q)) = tsc c , (R-sc p , R-sc q)

cv-rec : {C C' z z' s s' n n' : Tm} -> Conv C C' -> Conv z z' -> Conv s s' -> Conv n n' ->
         Conv (trec C z s n) (trec C' z' s' n')
cv-rec (c1 , (p1 , q1)) (c2 , (p2 , q2)) (c3 , (p3 , q3)) (c4 , (p4 , q4)) =
  trec c1 c2 c3 c4 , (R-rec p1 p2 p3 p4 , R-rec q1 q2 q3 q4)

cv-sub : (s : Sb) {a b : Tm} -> Conv a b -> Conv (sub s a) (sub s b)
cv-sub s (c , (p , q)) = sub s c , (Red-sub s p , Red-sub s q)

cv-ren : (r : Rn) {a b : Tm} -> Conv a b -> Conv (ren r a) (ren r b)
cv-ren r (c , (p , q)) = ren r c , (Red-ren r p , Red-ren r q)

------------------------------------------------------------------------
-- Reducts of constructor-headed terms
------------------------------------------------------------------------

-- a binary constructor  k  whose reducts are again k-headed
record Red2 (k : Tm -> Tm -> Tm) (A F c : Tm) : Set where
  constructor red2
  field
    A1 : Tm
    F1 : Tm
    ec : Eq c (k A1 F1)
    rA : Red A A1
    rF : Red F F1

red-pi : {A F c : Tm} -> Red (tpi A F) c -> Red2 tpi A F c
red-pi r-refl = red2 _ _ refl r-refl r-refl
red-pi (r-step (s-pi1 s) r) = let x = red-pi r in red2 _ _ (Red2.ec x) (r-step s (Red2.rA x)) (Red2.rF x)
red-pi (r-step (s-pi2 s) r) = let x = red-pi r in red2 _ _ (Red2.ec x) (Red2.rA x) (r-step s (Red2.rF x))

red-sig : {A F c : Tm} -> Red (tsig A F) c -> Red2 tsig A F c
red-sig r-refl = red2 _ _ refl r-refl r-refl
red-sig (r-step (s-sig1 s) r) = let x = red-sig r in red2 _ _ (Red2.ec x) (r-step s (Red2.rA x)) (Red2.rF x)
red-sig (r-step (s-sig2 s) r) = let x = red-sig r in red2 _ _ (Red2.ec x) (Red2.rA x) (r-step s (Red2.rF x))

red-U : {A F c : Tm} -> Red (tU A F) c -> Red2 tU A F c
red-U r-refl = red2 _ _ refl r-refl r-refl
red-U (r-step (s-U1 s) r) = let x = red-U r in red2 _ _ (Red2.ec x) (r-step s (Red2.rA x)) (Red2.rF x)
red-U (r-step (s-U2 s) r) = let x = red-U r in red2 _ _ (Red2.ec x) (Red2.rA x) (r-step s (Red2.rF x))

red-pair : {A F c : Tm} -> Red (tpair A F) c -> Red2 tpair A F c
red-pair r-refl = red2 _ _ refl r-refl r-refl
red-pair (r-step (s-pair1 s) r) =
  let x = red-pair r in red2 _ _ (Red2.ec x) (r-step s (Red2.rA x)) (Red2.rF x)
red-pair (r-step (s-pair2 s) r) =
  let x = red-pair r in red2 _ _ (Red2.ec x) (Red2.rA x) (r-step s (Red2.rF x))

-- nullary constructors and variables are normal
red-nat : {c : Tm} -> Red tnat c -> Eq c tnat
red-nat r-refl = refl

red-ze : {c : Tm} -> Red tze c -> Eq c tze
red-ze r-refl = refl

red-V : {c : Tm} -> Red tV c -> Eq c tV
red-V r-refl = refl

red-var : {i : Num} {c : Tm} -> Red (tvar i) c -> Eq c (tvar i)
red-var r-refl = refl

red-sc : {a c : Tm} -> Red (tsc a) c -> Sigma Tm (\ a1 -> Eq c (tsc a1) * Red a a1)
red-sc r-refl = _ , (refl , r-refl)
red-sc (r-step (s-sc s) r) = let x = red-sc r in fst x , (fst (snd x) , r-step s (snd (snd x)))

red-lam : {b c : Tm} -> Red (tlam b) c -> Sigma Tm (\ b1 -> Eq c (tlam b1) * Red b b1)
red-lam r-refl = _ , (refl , r-refl)
red-lam (r-step (s-lam s) r) = let x = red-lam r in fst x , (fst (snd x) , r-step s (snd (snd x)))

------------------------------------------------------------------------
-- (A1): injectivity and disjointness up to conversion
------------------------------------------------------------------------

private
  inj2 : {k : Tm -> Tm -> Tm} -> ({A F A' F' : Tm} -> Eq (k A F) (k A' F') -> Eq A A' * Eq F F') ->
         {A F A' F' c : Tm} -> Red2 k A F c -> Red2 k A' F' c -> Conv A A' * Conv F F'
  inj2 kinj (red2 A1 F1 e rA rF) (red2 A2 F2 e' rA' rF') =
    let i = kinj (Eq-trans (Eq-sym e) e') in
    (A1 , (rA , transport (Red _) (Eq-sym (fst i)) rA')) ,
    (F1 , (rF , transport (Red _) (Eq-sym (snd i)) rF'))

  pi-inj-Eq : {A F A' F' : Tm} -> Eq (tpi A F) (tpi A' F') -> Eq A A' * Eq F F'
  pi-inj-Eq refl = refl , refl
  sig-inj-Eq : {A F A' F' : Tm} -> Eq (tsig A F) (tsig A' F') -> Eq A A' * Eq F F'
  sig-inj-Eq refl = refl , refl
  U-inj-Eq : {A F A' F' : Tm} -> Eq (tU A F) (tU A' F') -> Eq A A' * Eq F F'
  U-inj-Eq refl = refl , refl

cv-pi-inj : {A F A' F' : Tm} -> Conv (tpi A F) (tpi A' F') -> Conv A A' * Conv F F'
cv-pi-inj (c , (p , q)) = inj2 pi-inj-Eq (red-pi p) (red-pi q)

cv-sig-inj : {A F A' F' : Tm} -> Conv (tsig A F) (tsig A' F') -> Conv A A' * Conv F F'
cv-sig-inj (c , (p , q)) = inj2 sig-inj-Eq (red-sig p) (red-sig q)

cv-U-inj : {A F A' F' : Tm} -> Conv (tU A F) (tU A' F') -> Conv A A' * Conv F F'
cv-U-inj (c , (p , q)) = inj2 U-inj-Eq (red-U p) (red-U q)

cv-pi-nat : {A F : Tm} -> Conv (tpi A F) tnat -> Empty
cv-pi-nat (c , (p , q)) = h (Eq-trans (Eq-sym (Red2.ec (red-pi p))) (red-nat q))
  where h : {A F : Tm} -> Eq (tpi A F) tnat -> Empty
        h ()

cv-sig-pi : {A F A' F' : Tm} -> Conv (tsig A F) (tpi A' F') -> Empty
cv-sig-pi (c , (p , q)) = h (Eq-trans (Eq-sym (Red2.ec (red-sig p))) (Red2.ec (red-pi q)))
  where h : {A F A' F' : Tm} -> Eq (tsig A F) (tpi A' F') -> Empty
        h ()

cv-sig-nat : {A F : Tm} -> Conv (tsig A F) tnat -> Empty
cv-sig-nat (c , (p , q)) = h (Eq-trans (Eq-sym (Red2.ec (red-sig p))) (red-nat q))
  where h : {A F : Tm} -> Eq (tsig A F) tnat -> Empty
        h ()

cv-sig-U : {A F f g : Tm} -> Conv (tsig A F) (tU f g) -> Empty
cv-sig-U (c , (p , q)) = h (Eq-trans (Eq-sym (Red2.ec (red-sig p))) (Red2.ec (red-U q)))
  where h : {A F f g : Tm} -> Eq (tsig A F) (tU f g) -> Empty
        h ()

cv-pi-U : {A F f g : Tm} -> Conv (tpi A F) (tU f g) -> Empty
cv-pi-U (c , (p , q)) = h (Eq-trans (Eq-sym (Red2.ec (red-pi p))) (Red2.ec (red-U q)))
  where h : {A F f g : Tm} -> Eq (tpi A F) (tU f g) -> Empty
        h ()

cv-nat-U : {f g : Tm} -> Conv tnat (tU f g) -> Empty
cv-nat-U (c , (p , q)) = h (Eq-trans (Eq-sym (red-nat p)) (Red2.ec (red-U q)))
  where h : {f g : Tm} -> Eq tnat (tU f g) -> Empty
        h ()

cv-V-pi : {A F : Tm} -> Conv tV (tpi A F) -> Empty
cv-V-pi (c , (p , q)) = h (Eq-trans (Eq-sym (red-V p)) (Red2.ec (red-pi q)))
  where h : {A F : Tm} -> Eq tV (tpi A F) -> Empty
        h ()

cv-V-sig : {A F : Tm} -> Conv tV (tsig A F) -> Empty
cv-V-sig (c , (p , q)) = h (Eq-trans (Eq-sym (red-V p)) (Red2.ec (red-sig q)))
  where h : {A F : Tm} -> Eq tV (tsig A F) -> Empty
        h ()

cv-V-nat : Conv tV tnat -> Empty
cv-V-nat (c , (p , q)) = h (Eq-trans (Eq-sym (red-V p)) (red-nat q))
  where h : Eq tV tnat -> Empty
        h ()

cv-V-U : {f g : Tm} -> Conv tV (tU f g) -> Empty
cv-V-U (c , (p , q)) = h (Eq-trans (Eq-sym (red-V p)) (Red2.ec (red-U q)))
  where h : {f g : Tm} -> Eq tV (tU f g) -> Empty
        h ()
