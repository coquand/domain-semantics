{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Bnd.agda
--
-- Bounds on free variables, preserved by reduction; a bound for every
-- term; and the fresh-variable renaming  fr m  (0 |-> m, the variables
-- below m shifted down) with its inverse  fr' m.  On terms bounded by
-- m+1,  b[x_m/0] = ren (fr m) b;  on terms bounded by m,
-- ren (fr' m) t = shift t.
------------------------------------------------------------------------

module MAHLO.Concrete.Bnd where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc ; cong2 ; cong4)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.DecEq
open import MAHLO.Concrete.EtaLemmas using (Retr ; retr)

data Unit : Set where
  unit : Unit

-- i < k
Lt : Num -> Num -> Set
Lt i zero = Empty
Lt zero (suc k) = Unit
Lt (suc i) (suc k) = Lt i k

decLt : (i k : Num) -> Dec (Lt i k)
decLt i zero = no (\ ())
decLt zero (suc k) = yes unit
decLt (suc i) (suc k) = decLt i k

lt-suc : (i k : Num) -> Lt i k -> Lt i (suc k)
lt-suc i zero ()
lt-suc zero (suc k) p = unit
lt-suc (suc i) (suc k) p = lt-suc i k p

lt-irrefl : (i : Num) -> Lt i i -> Empty
lt-irrefl zero ()
lt-irrefl (suc i) p = lt-irrefl i p

-- i < suc k, not i < k  ==>  i = k
lt-last : (i k : Num) -> Lt i (suc k) -> (Lt i k -> Empty) -> Eq i k
lt-last zero zero p q = refl
lt-last zero (suc k) p q = Empty-elim (q unit)
lt-last (suc i) zero p q = Empty-elim p
lt-last (suc i) (suc k) p q = Eq-cong suc (lt-last i k p q)

-- not i < k, i /= k  ==>  k < i  (in the form needed below)
not-lt-suc : (i k : Num) -> (Lt i k -> Empty) -> (Eq i k -> Empty) -> Lt k i
not-lt-suc zero zero q d = Empty-elim (d refl)
not-lt-suc zero (suc k) q d = Empty-elim (q unit)
not-lt-suc (suc i) zero q d = unit
not-lt-suc (suc i) (suc k) q d = not-lt-suc i k q (\ e -> d (Eq-cong suc e))

lt-asym : (i k : Num) -> Lt i k -> Lt k i -> Empty
lt-asym zero zero () q
lt-asym zero (suc k) p ()
lt-asym (suc i) zero () q
lt-asym (suc i) (suc k) p q = lt-asym i k p q

------------------------------------------------------------------------
-- Bounded terms
------------------------------------------------------------------------

Bnd : Num -> Tm -> Set
Bnd k (tvar i) = Lt i k
Bnd k (tlam b) = Bnd (suc k) b
Bnd k (tapp t u) = Bnd k t * Bnd k u
Bnd k (tpi A F) = Bnd k A * Bnd k F
Bnd k (tsig A F) = Bnd k A * Bnd k F
Bnd k (tpair t u) = Bnd k t * Bnd k u
Bnd k (tfst t) = Bnd k t
Bnd k (tsnd t) = Bnd k t
Bnd k tnat = Unit
Bnd k tze = Unit
Bnd k (tsc t) = Bnd k t
Bnd k (trec C z s n) = Bnd k C * (Bnd k z * (Bnd k s * Bnd k n))
Bnd k tV = Unit
Bnd k (tU f g) = Bnd k f * Bnd k g

-- substitutions on bounded terms
BndS : Num -> Num -> Sb -> Set
BndS k k' s = (i : Num) -> Lt i k' -> Bnd k (s i)

-- renaming of bounded terms
bnd-ren : (k k' : Num) (r : Rn) -> ((i : Num) -> Lt i k' -> Lt (r i) k) ->
          (t : Tm) -> Bnd k' t -> Bnd k (ren r t)
bnd-ren k k' r h (tvar i) p = h i p
bnd-ren k k' r h (tlam b) p = bnd-ren (suc k) (suc k') (liftR r) h' b p
  where
    h' : (i : Num) -> Lt i (suc k') -> Lt (liftR r i) (suc k)
    h' zero q = unit
    h' (suc i) q = h i q
bnd-ren k k' r h (tapp t u) (p , q) = bnd-ren k k' r h t p , bnd-ren k k' r h u q
bnd-ren k k' r h (tpi t u) (p , q) = bnd-ren k k' r h t p , bnd-ren k k' r h u q
bnd-ren k k' r h (tsig t u) (p , q) = bnd-ren k k' r h t p , bnd-ren k k' r h u q
bnd-ren k k' r h (tpair t u) (p , q) = bnd-ren k k' r h t p , bnd-ren k k' r h u q
bnd-ren k k' r h (tfst t) p = bnd-ren k k' r h t p
bnd-ren k k' r h (tsnd t) p = bnd-ren k k' r h t p
bnd-ren k k' r h tnat p = unit
bnd-ren k k' r h tze p = unit
bnd-ren k k' r h (tsc t) p = bnd-ren k k' r h t p
bnd-ren k k' r h (trec C z s n) (p1 , (p2 , (p3 , p4))) =
  bnd-ren k k' r h C p1 , (bnd-ren k k' r h z p2 , (bnd-ren k k' r h s p3 , bnd-ren k k' r h n p4))
bnd-ren k k' r h tV p = unit
bnd-ren k k' r h (tU f g) (p , q) = bnd-ren k k' r h f p , bnd-ren k k' r h g q

bnd-shift : (k : Num) (t : Tm) -> Bnd k t -> Bnd (suc k) (shift t)
bnd-shift k t p = bnd-ren (suc k) k suc (\ i q -> q) t p

bnd-sub : (k k' : Num) (s : Sb) -> BndS k k' s -> (t : Tm) -> Bnd k' t -> Bnd k (sub s t)
bnd-sub k k' s h (tvar i) p = h i p
bnd-sub k k' s h (tlam b) p = bnd-sub (suc k) (suc k') (liftS s) h' b p
  where
    h' : BndS (suc k) (suc k') (liftS s)
    h' zero q = unit
    h' (suc i) q = bnd-shift k (s i) (h i q)
bnd-sub k k' s h (tapp t u) (p , q) = bnd-sub k k' s h t p , bnd-sub k k' s h u q
bnd-sub k k' s h (tpi t u) (p , q) = bnd-sub k k' s h t p , bnd-sub k k' s h u q
bnd-sub k k' s h (tsig t u) (p , q) = bnd-sub k k' s h t p , bnd-sub k k' s h u q
bnd-sub k k' s h (tpair t u) (p , q) = bnd-sub k k' s h t p , bnd-sub k k' s h u q
bnd-sub k k' s h (tfst t) p = bnd-sub k k' s h t p
bnd-sub k k' s h (tsnd t) p = bnd-sub k k' s h t p
bnd-sub k k' s h tnat p = unit
bnd-sub k k' s h tze p = unit
bnd-sub k k' s h (tsc t) p = bnd-sub k k' s h t p
bnd-sub k k' s h (trec C z u n) (p1 , (p2 , (p3 , p4))) =
  bnd-sub k k' s h C p1 , (bnd-sub k k' s h z p2 , (bnd-sub k k' s h u p3 , bnd-sub k k' s h n p4))
bnd-sub k k' s h tV p = unit
bnd-sub k k' s h (tU f g) (p , q) = bnd-sub k k' s h f p , bnd-sub k k' s h g q

bnd-inst : (k : Num) (b a : Tm) -> Bnd (suc k) b -> Bnd k a -> Bnd k (inst b a)
bnd-inst k b a p q = bnd-sub k (suc k) (sub0 a) h b p
  where
    h : BndS k (suc k) (sub0 a)
    h zero _ = q
    h (suc i) r = r

-- reduction does not increase free variables
bnd-step : (k : Num) {a b : Tm} -> Step a b -> Bnd k a -> Bnd k b
bnd-step k (s-beta {b} {a}) (p , q) = bnd-inst k b a p q
bnd-step k s-fstp (p , q) = p
bnd-step k s-sndp (p , q) = q
bnd-step k s-rec0 (p1 , (p2 , (p3 , p4))) = p2
bnd-step k s-recS (p1 , (p2 , (p3 , p4))) = (p3 , p4) , (p1 , (p2 , (p3 , p4)))
bnd-step k (s-lam s) p = bnd-step (suc k) s p
bnd-step k (s-app1 s) (p , q) = bnd-step k s p , q
bnd-step k (s-app2 s) (p , q) = p , bnd-step k s q
bnd-step k (s-pi1 s) (p , q) = bnd-step k s p , q
bnd-step k (s-pi2 s) (p , q) = p , bnd-step k s q
bnd-step k (s-sig1 s) (p , q) = bnd-step k s p , q
bnd-step k (s-sig2 s) (p , q) = p , bnd-step k s q
bnd-step k (s-pair1 s) (p , q) = bnd-step k s p , q
bnd-step k (s-pair2 s) (p , q) = p , bnd-step k s q
bnd-step k (s-fst s) p = bnd-step k s p
bnd-step k (s-snd s) p = bnd-step k s p
bnd-step k (s-sc s) p = bnd-step k s p
bnd-step k (s-rec1 s) (p1 , (p2 , (p3 , p4))) = bnd-step k s p1 , (p2 , (p3 , p4))
bnd-step k (s-rec2 s) (p1 , (p2 , (p3 , p4))) = p1 , (bnd-step k s p2 , (p3 , p4))
bnd-step k (s-rec3 s) (p1 , (p2 , (p3 , p4))) = p1 , (p2 , (bnd-step k s p3 , p4))
bnd-step k (s-rec4 s) (p1 , (p2 , (p3 , p4))) = p1 , (p2 , (p3 , bnd-step k s p4))
bnd-step k (s-U1 s) (p , q) = bnd-step k s p , q
bnd-step k (s-U2 s) (p , q) = p , bnd-step k s q

bnd-red : (k : Num) {a b : Tm} -> Red a b -> Bnd k a -> Bnd k b
bnd-red k r-refl p = p
bnd-red k (r-step s r) p = bnd-red k r (bnd-step k s p)

------------------------------------------------------------------------
-- Every term is bounded
------------------------------------------------------------------------

max : Num -> Num -> Num
max zero k = k
max (suc i) zero = suc i
max (suc i) (suc k) = suc (max i k)

lt-max-l : (i a b : Num) -> Lt i a -> Lt i (max a b)
lt-max-l i zero b ()
lt-max-l zero (suc a) zero p = unit
lt-max-l zero (suc a) (suc b) p = unit
lt-max-l (suc i) (suc a) zero p = p
lt-max-l (suc i) (suc a) (suc b) p = lt-max-l i a b p

lt-max-r : (i a b : Num) -> Lt i b -> Lt i (max a b)
lt-max-r i zero b p = p
lt-max-r i (suc a) zero ()
lt-max-r zero (suc a) (suc b) p = unit
lt-max-r (suc i) (suc a) (suc b) p = lt-max-r i a b p

-- monotonicity
bnd-mono : (k k' : Num) -> ((i : Num) -> Lt i k -> Lt i k') -> (t : Tm) -> Bnd k t -> Bnd k' t
bnd-mono k k' h t p =
  transport (Bnd k') (Eq-trans (ren-as-sub (\ i -> i) t) (sub-id-gen tvar (\ i -> refl) t))
    (bnd-ren k' k (\ i -> i) h t p)

pred : Num -> Num
pred zero = zero
pred (suc i) = i

bound : Tm -> Num
bound (tvar i) = suc i
bound (tlam b) = pred (bound b)
bound (tapp t u) = max (bound t) (bound u)
bound (tpi t u) = max (bound t) (bound u)
bound (tsig t u) = max (bound t) (bound u)
bound (tpair t u) = max (bound t) (bound u)
bound (tfst t) = bound t
bound (tsnd t) = bound t
bound tnat = zero
bound tze = zero
bound (tsc t) = bound t
bound (trec C z s n) = max (bound C) (max (bound z) (max (bound s) (bound n)))
bound tV = zero
bound (tU f g) = max (bound f) (bound g)

lt-self : (i : Num) -> Lt i (suc i)
lt-self zero = unit
lt-self (suc i) = lt-self i

lt-pred : (i k : Num) -> Lt (suc i) k -> Lt i (pred k)
lt-pred i zero ()
lt-pred i (suc k) p = p

lt-suc-pred : (i k : Num) -> Lt i k -> Lt i (suc (pred k))
lt-suc-pred i zero ()
lt-suc-pred i (suc k) p = p

wkL : (a b : Num) (t : Tm) -> Bnd a t -> Bnd (max a b) t
wkL a b t = bnd-mono a (max a b) (\ i p -> lt-max-l i a b p) t

wkR : (a b : Num) (t : Tm) -> Bnd b t -> Bnd (max a b) t
wkR a b t = bnd-mono b (max a b) (\ i p -> lt-max-r i a b p) t

bnd-bound : (t : Tm) -> Bnd (bound t) t
bnd-bound (tvar i) = lt-self i
bnd-bound (tlam b) =
  bnd-mono (bound b) (suc (pred (bound b))) (\ i p -> lt-suc-pred i (bound b) p) b (bnd-bound b)
bnd-bound (tapp t u) = wkL (bound t) (bound u) t (bnd-bound t) , wkR (bound t) (bound u) u (bnd-bound u)
bnd-bound (tpi t u) = wkL (bound t) (bound u) t (bnd-bound t) , wkR (bound t) (bound u) u (bnd-bound u)
bnd-bound (tsig t u) = wkL (bound t) (bound u) t (bnd-bound t) , wkR (bound t) (bound u) u (bnd-bound u)
bnd-bound (tpair t u) = wkL (bound t) (bound u) t (bnd-bound t) , wkR (bound t) (bound u) u (bnd-bound u)
bnd-bound (tfst t) = bnd-bound t
bnd-bound (tsnd t) = bnd-bound t
bnd-bound tnat = unit
bnd-bound tze = unit
bnd-bound (tsc t) = bnd-bound t
bnd-bound (trec C z s n) =
  wkL bC m1 C (bnd-bound C) ,
  (wkR bC m1 z (wkL bz m2 z (bnd-bound z)) ,
   (wkR bC m1 s (wkR bz m2 s (wkL bs bn s (bnd-bound s))) ,
    wkR bC m1 n (wkR bz m2 n (wkR bs bn n (bnd-bound n)))))
  where
    bC = bound C
    bz = bound z
    bs = bound s
    bn = bound n
    m2 = max bs bn
    m1 = max bz m2
bnd-bound tV = unit
bnd-bound (tU f g) = wkL (bound f) (bound g) f (bnd-bound f) , wkR (bound f) (bound g) g (bnd-bound g)

------------------------------------------------------------------------
-- Substitution only depends on the variables below the bound
------------------------------------------------------------------------

sub-ext-bnd : (k : Num) (s s' : Sb) -> ((i : Num) -> Lt i k -> Eq (s i) (s' i)) ->
              (t : Tm) -> Bnd k t -> Eq (sub s t) (sub s' t)
sub-ext-bnd k s s' e (tvar i) p = e i p
sub-ext-bnd k s s' e (tlam b) p = Eq-cong tlam (sub-ext-bnd (suc k) (liftS s) (liftS s') e' b p)
  where
    e' : (i : Num) -> Lt i (suc k) -> Eq (liftS s i) (liftS s' i)
    e' zero q = refl
    e' (suc i) q = Eq-cong shift (e i q)
sub-ext-bnd k s s' e (tapp t u) (p , q) = cong2 tapp (sub-ext-bnd k s s' e t p) (sub-ext-bnd k s s' e u q)
sub-ext-bnd k s s' e (tpi t u) (p , q) = cong2 tpi (sub-ext-bnd k s s' e t p) (sub-ext-bnd k s s' e u q)
sub-ext-bnd k s s' e (tsig t u) (p , q) = cong2 tsig (sub-ext-bnd k s s' e t p) (sub-ext-bnd k s s' e u q)
sub-ext-bnd k s s' e (tpair t u) (p , q) = cong2 tpair (sub-ext-bnd k s s' e t p) (sub-ext-bnd k s s' e u q)
sub-ext-bnd k s s' e (tfst t) p = Eq-cong tfst (sub-ext-bnd k s s' e t p)
sub-ext-bnd k s s' e (tsnd t) p = Eq-cong tsnd (sub-ext-bnd k s s' e t p)
sub-ext-bnd k s s' e tnat p = refl
sub-ext-bnd k s s' e tze p = refl
sub-ext-bnd k s s' e (tsc t) p = Eq-cong tsc (sub-ext-bnd k s s' e t p)
sub-ext-bnd k s s' e (trec C z u n) (p1 , (p2 , (p3 , p4))) =
  cong4 trec (sub-ext-bnd k s s' e C p1) (sub-ext-bnd k s s' e z p2)
             (sub-ext-bnd k s s' e u p3) (sub-ext-bnd k s s' e n p4)
sub-ext-bnd k s s' e tV p = refl
sub-ext-bnd k s s' e (tU f g) (p , q) = cong2 tU (sub-ext-bnd k s s' e f p) (sub-ext-bnd k s s' e g q)

------------------------------------------------------------------------
-- The fresh-variable renaming and its inverse
------------------------------------------------------------------------

private
  frS : (m i : Num) -> Dec (Lt i m) -> Num
  frS m i (yes _) = i
  frS m i (no _) = suc i

  fr'H : (m i : Num) -> Dec (Eq i m) -> Dec (Lt i m) -> Num
  fr'H m i (yes _) dl = zero
  fr'H m i (no _) (yes _) = suc i
  fr'H m i (no _) (no _) = i

fr : Num -> Rn
fr m zero = m
fr m (suc i) = frS m i (decLt i m)

fr' : Num -> Rn
fr' m i = fr'H m i (decNum i m) (decLt i m)

private
  frS-yes : (m i : Num) (d : Dec (Lt i m)) -> Lt i m -> Eq (frS m i d) i
  frS-yes m i (yes _) p = refl
  frS-yes m i (no f) p = Empty-elim (f p)

  frS-no : (m i : Num) (d : Dec (Lt i m)) -> (Lt i m -> Empty) -> Eq (frS m i d) (suc i)
  frS-no m i (yes p) f = Empty-elim (f p)
  frS-no m i (no _) f = refl

  fr'H-eq : (m i : Num) (dn : Dec (Eq i m)) (dl : Dec (Lt i m)) -> Eq i m -> Eq (fr'H m i dn dl) zero
  fr'H-eq m i (yes _) dl e = refl
  fr'H-eq m i (no f) dl e = Empty-elim (f e)

  fr'H-lt : (m i : Num) (dn : Dec (Eq i m)) (dl : Dec (Lt i m)) -> Lt i m -> Eq (fr'H m i dn dl) (suc i)
  fr'H-lt m i (yes refl) dl p = Empty-elim (lt-irrefl i p)
  fr'H-lt m i (no f) (yes _) p = refl
  fr'H-lt m i (no f) (no g) p = Empty-elim (g p)

  fr'H-big : (m i : Num) (dn : Dec (Eq i m)) (dl : Dec (Lt i m)) ->
             (Eq i m -> Empty) -> (Lt i m -> Empty) -> Eq (fr'H m i dn dl) i
  fr'H-big m i (yes e) dl f g = Empty-elim (f e)
  fr'H-big m i (no _) (yes p) f g = Empty-elim (g p)
  fr'H-big m i (no _) (no _) f g = refl

  lt-step : (j m : Num) -> Lt (suc j) m -> Lt j m
  lt-step j zero ()
  lt-step zero (suc m) p = unit
  lt-step (suc j) (suc m) p = lt-step j m p

  lt-between : (j m : Num) -> Lt j m -> Lt m (suc j) -> Empty
  lt-between j zero () q
  lt-between zero (suc m) p ()
  lt-between (suc j) (suc m) p q = lt-between j m p q

-- fr' m is a retraction of fr m, and conversely
fr'-fr : (m i : Num) -> Eq (fr' m (fr m i)) i
fr'-fr m zero = fr'H-eq m m (decNum m m) (decLt m m) refl
fr'-fr m (suc j) = h (decLt j m)
  where
    h : (d : Dec (Lt j m)) -> Eq (fr' m (frS m j d)) (suc j)
    h (yes p) = fr'H-lt m j (decNum j m) (decLt j m) p
    h (no q) = fr'H-big m (suc j) (decNum (suc j) m) (decLt (suc j) m)
                 (\ e -> q (transport (\ z -> Lt j z) e (lt-self j)))
                 (\ p -> q (lt-step j m p))

fr-fr' : (m i : Num) -> Eq (fr m (fr' m i)) i
fr-fr' m i = h (decNum i m) (decLt i m)
  where
    h : (dn : Dec (Eq i m)) (dl : Dec (Lt i m)) -> Eq (fr m (fr'H m i dn dl)) i
    h (yes e) dl = Eq-sym e
    h (no f) (yes p) = frS-yes m i (decLt i m) p
    h (no f) (no g) = k i (not-lt-suc i m g f)
      where
        k : (i' : Num) -> Lt m i' -> Eq (fr m i') i'
        k zero ()
        k (suc j) q = frS-no m j (decLt j m) (\ p -> lt-between j m p q)

retr-fr : (m : Num) -> Retr (fr m) (fr' m)
retr-fr m = retr (fr'-fr m)

retr-fr' : (m : Num) -> Retr (fr' m) (fr m)
retr-fr' m = retr (fr-fr' m)

-- b[x_m / 0] is a renaming, for b bounded by m+1
inst-fresh : (m : Num) (b : Tm) -> Bnd (suc m) b -> Eq (inst b (tvar m)) (ren (fr m) b)
inst-fresh m b p =
  Eq-trans (sub-ext-bnd (suc m) (sub0 (tvar m)) (\ i -> tvar (fr m i)) e b p)
           (Eq-sym (ren-as-sub (fr m) b))
  where
    e : (i : Num) -> Lt i (suc m) -> Eq (sub0 (tvar m) i) (tvar (fr m i))
    e zero q = refl
    e (suc j) q = Eq-cong tvar (Eq-sym (frS-yes m j (decLt j m) q))

-- the inverse renaming is shift on terms bounded by m
fr'-shift : (m : Num) (t : Tm) -> Bnd m t -> Eq (ren (fr' m) t) (shift t)
fr'-shift m t p =
  Eq-trans (ren-as-sub (fr' m) t)
    (Eq-trans (sub-ext-bnd m (\ i -> tvar (fr' m i)) (\ i -> tvar (suc i)) e t p)
              (Eq-sym (ren-as-sub suc t)))
  where
    e : (i : Num) -> Lt i m -> Eq (tvar (fr' m i)) (tvar (suc i))
    e i q = Eq-cong tvar (fr'H-lt m i (decNum i m) (decLt i m) q)
