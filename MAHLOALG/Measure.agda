{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/Measure.agda
--
-- The completeness measure on values: (lp, sz), where lp counts lambda
-- and pair nodes and sz counts all nodes; both invariant under
-- renaming.  Minimal arithmetic on Num.
------------------------------------------------------------------------

module MAHLOALG.Measure where

open import MAHLO.Basic hiding (_+_)
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm

infixl 6 _+_
_+_ : Num -> Num -> Num
zero + b = b
suc a + b = suc (a + b)

data _<=_ : Num -> Num -> Set where
  z<= : {n : Num} -> zero <= n
  s<= : {m n : Num} -> m <= n -> suc m <= suc n

<=-refl : (n : Num) -> n <= n
<=-refl zero = z<=
<=-refl (suc n) = s<= (<=-refl n)

<=-trans : {a b c : Num} -> a <= b -> b <= c -> a <= c
<=-trans z<= q = z<=
<=-trans (s<= p) (s<= q) = s<= (<=-trans p q)

<=-suc : {a b : Num} -> a <= b -> a <= suc b
<=-suc z<= = z<=
<=-suc (s<= p) = s<= (<=-suc p)

+-suc : (a b : Num) -> Eq (a + suc b) (suc (a + b))
+-suc zero b = refl
+-suc (suc a) b = Eq-cong suc (+-suc a b)

+-mono : {a a' b b' : Num} -> a <= a' -> b <= b' -> (a + b) <= (a' + b')
+-mono {a' = a'} z<= q = <=-trans q (+r a')
  where
    +r : (x : Num) {y : Num} -> y <= (x + y)
    +r zero = <=-refl _
    +r (suc x) = <=-suc (+r x)
+-mono (s<= p) q = s<= (+-mono p q)

<=-eq : {a b c : Num} -> a <= b -> Eq b c -> a <= c
<=-eq p refl = p

eq-<= : {a b c : Num} -> Eq a b -> b <= c -> a <= c
eq-<= refl p = p

-- strictness from a successor below a successor
pred<= : {a b : Num} -> suc a <= suc b -> a <= b
pred<= (s<= p) = p

------------------------------------------------------------------------
-- sizes
------------------------------------------------------------------------

sz : Tm -> Num
sz (tvar _) = suc zero
sz (tlam b) = suc (sz b)
sz (tapp t u) = suc (sz t + sz u)
sz (tpi A F) = suc (sz A + sz F)
sz (tsig A F) = suc (sz A + sz F)
sz (tpair t u) = suc (sz t + sz u)
sz (tfst t) = suc (sz t)
sz (tsnd t) = suc (sz t)
sz tnat = suc zero
sz tze = suc zero
sz (tsc t) = suc (sz t)
sz (trec C z s n) = suc (sz C + (sz z + (sz s + sz n)))
sz tV = suc zero
sz (tU f g) = suc (sz f + sz g)

lp : Tm -> Num
lp (tvar _) = zero
lp (tlam b) = suc (lp b)
lp (tapp t u) = lp t + lp u
lp (tpi A F) = lp A + lp F
lp (tsig A F) = lp A + lp F
lp (tpair t u) = suc (lp t + lp u)
lp (tfst t) = lp t
lp (tsnd t) = lp t
lp tnat = zero
lp tze = zero
lp (tsc t) = lp t
lp (trec C z s n) = lp C + (lp z + (lp s + lp n))
lp tV = zero
lp (tU f g) = lp f + lp g

sz-ren : (r : Rn) (t : Tm) -> Eq (sz (ren r t)) (sz t)
sz-ren r (tvar i) = refl
sz-ren r (tlam b) = Eq-cong suc (sz-ren (liftR r) b)
sz-ren r (tapp t u) = Eq-cong suc (cong2' (sz-ren r t) (sz-ren r u))
  where cong2' : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        cong2' refl refl = refl
sz-ren r (tpi A F) = Eq-cong suc (c2 (sz-ren r A) (sz-ren r F))
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
sz-ren r (tsig A F) = Eq-cong suc (c2 (sz-ren r A) (sz-ren r F))
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
sz-ren r (tpair t u) = Eq-cong suc (c2 (sz-ren r t) (sz-ren r u))
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
sz-ren r (tfst t) = Eq-cong suc (sz-ren r t)
sz-ren r (tsnd t) = Eq-cong suc (sz-ren r t)
sz-ren r tnat = refl
sz-ren r tze = refl
sz-ren r (tsc t) = Eq-cong suc (sz-ren r t)
sz-ren r (trec C z s n) = Eq-cong suc (c4 (sz-ren r C) (sz-ren r z) (sz-ren r s) (sz-ren r n))
  where c4 : {a a' b b' c c' d d' : Num} -> Eq a a' -> Eq b b' -> Eq c c' -> Eq d d' -> Eq (a + (b + (c + d))) (a' + (b' + (c' + d')))
        c4 refl refl refl refl = refl
sz-ren r tV = refl
sz-ren r (tU f g) = Eq-cong suc (c2 (sz-ren r f) (sz-ren r g))
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl

lp-ren : (r : Rn) (t : Tm) -> Eq (lp (ren r t)) (lp t)
lp-ren r (tvar i) = refl
lp-ren r (tlam b) = Eq-cong suc (lp-ren (liftR r) b)
lp-ren r (tapp t u) = c2 (lp-ren r t) (lp-ren r u)
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
lp-ren r (tpi A F) = c2 (lp-ren r A) (lp-ren r F)
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
lp-ren r (tsig A F) = c2 (lp-ren r A) (lp-ren r F)
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
lp-ren r (tpair t u) = Eq-cong suc (c2 (lp-ren r t) (lp-ren r u))
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl
lp-ren r (tfst t) = lp-ren r t
lp-ren r (tsnd t) = lp-ren r t
lp-ren r tnat = refl
lp-ren r tze = refl
lp-ren r (tsc t) = lp-ren r t
lp-ren r (trec C z s n) = c4 (lp-ren r C) (lp-ren r z) (lp-ren r s) (lp-ren r n)
  where c4 : {a a' b b' c c' d d' : Num} -> Eq a a' -> Eq b b' -> Eq c c' -> Eq d d' -> Eq (a + (b + (c + d))) (a' + (b' + (c' + d')))
        c4 refl refl refl refl = refl
lp-ren r tV = refl
lp-ren r (tU f g) = c2 (lp-ren r f) (lp-ren r g)
  where c2 : {a a' b b' : Num} -> Eq a a' -> Eq b b' -> Eq (a + b) (a' + b')
        c2 refl refl = refl

-- every term has positive size
sz-pos : (t : Tm) -> Sigma Num (\ k -> Eq (sz t) (suc k))
sz-pos (tvar _) = _ , refl
sz-pos (tlam b) = _ , refl
sz-pos (tapp t u) = _ , refl
sz-pos (tpi A F) = _ , refl
sz-pos (tsig A F) = _ , refl
sz-pos (tpair t u) = _ , refl
sz-pos (tfst t) = _ , refl
sz-pos (tsnd t) = _ , refl
sz-pos tnat = _ , refl
sz-pos tze = _ , refl
sz-pos (tsc t) = _ , refl
sz-pos (trec C z s n) = _ , refl
sz-pos tV = _ , refl
sz-pos (tU f g) = _ , refl
