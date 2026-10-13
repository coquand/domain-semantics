{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/FixCounter.agda
--
-- Size sanity check for the fixed point theorem of fix.pdf (Coquand
-- 1995).  Its hypothesis "every directed SUBSET has a sup" must range
-- over subsets of the poset's own size.  If, for a poset Car : Set1,
-- sups are only required for families indexed by a Set, the statement
-- is REFUTABLE: Brouwer/W-ordinals branching over Set form such a
-- poset (bottom, binary joins, lubs of all Set-indexed families), and
-- the successor is monotone without a fixed point.
------------------------------------------------------------------------

module MAHLO.FixCounter where

open import MAHLO.Basic using (Empty ; Eq ; refl)

record Sg1 (A : Set1) (B : A -> Set) : Set1 where
  constructor _,,_
  field
    p1 : A
    p2 : B p1

record Sg0 (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

record And (A B : Set) : Set where
  constructor _&_
  field
    l : A
    r : B

data Unit : Set where
  unit : Unit

data Two : Set where
  tt ff : Two

------------------------------------------------------------------------
-- Small dcpos and the small-sup version of the theorem
------------------------------------------------------------------------

-- a directed family (indexed by a Set)
Dir : {Car : Set1} -> (Car -> Car -> Set) -> (I : Set) -> (I -> Car) -> Set
Dir le I x = (i j : I) -> Sg0 I (\ k -> And (le (x i) (x k)) (le (x j) (x k)))

record SmallDCPO : Set2 where
  field
    Car   : Set1
    _≤_   : Car -> Car -> Set
    ≤-refl  : (x : Car) -> x ≤ x
    ≤-trans : {x y z : Car} -> x ≤ y -> y ≤ z -> x ≤ z
    bot   : Car
    bot-least : (x : Car) -> bot ≤ x
    -- lubs of directed families indexed by a Set
    dsup  : (I : Set) (x : I -> Car) -> I -> Dir _≤_ I x -> Car
    dsup-ub : (I : Set) (x : I -> Car) (i0 : I) (d : Dir _≤_ I x) (i : I) -> x i ≤ dsup I x i0 d
    dsup-least : (I : Set) (x : I -> Car) (i0 : I) (d : Dir _≤_ I x) (z : Car) ->
                 ((i : I) -> x i ≤ z) -> dsup I x i0 d ≤ z
    -- conditional binary joins
    join  : (x y z : Car) -> x ≤ z -> y ≤ z -> Car
    join-l : (x y z : Car) (p : x ≤ z) (q : y ≤ z) -> x ≤ join x y z p q
    join-r : (x y z : Car) (p : x ≤ z) (q : y ≤ z) -> y ≤ join x y z p q
    join-least : (x y z : Car) (p : x ≤ z) (q : y ≤ z) (w : Car) -> x ≤ w -> y ≤ w ->
                 join x y z p q ≤ w

-- the fixed point theorem, with sups of Set-indexed directed families only
record FixThmSmall : Set3 where
  field
    fix : (P : SmallDCPO) (f : SmallDCPO.Car P -> SmallDCPO.Car P) ->
          ({x y : SmallDCPO.Car P} -> SmallDCPO._≤_ P x y -> SmallDCPO._≤_ P (f x) (f y)) ->
          Sg1 (SmallDCPO.Car P) (\ x0 -> And (SmallDCPO._≤_ P x0 (f x0)) (SmallDCPO._≤_ P (f x0) x0))

------------------------------------------------------------------------
-- W-ordinals branching over Set
------------------------------------------------------------------------

data Ord : Set1 where
  sup : (I : Set) -> (I -> Ord) -> Ord

Pred : Ord -> Set
Pred (sup I f) = I

at : (x : Ord) -> Pred x -> Ord
at (sup I f) i = f i

mutual
  -- x <= y : every predecessor of x is below y
  _≤_ : Ord -> Ord -> Set
  sup I f ≤ y = (i : I) -> f i < y

  -- x < y : x is below some predecessor of y
  _<_ : Ord -> Ord -> Set
  x < sup J g = Sg0 J (\ j -> x ≤ g j)

≤-refl : (x : Ord) -> x ≤ x
≤-refl (sup I f) i = i , ≤-refl (f i)

mutual
  ≤-trans : {x y z : Ord} -> x ≤ y -> y ≤ z -> x ≤ z
  ≤-trans {sup I f} p q i = <-≤ (p i) q

  <-≤ : {x y z : Ord} -> x < y -> y ≤ z -> x < z
  <-≤ {x} {sup J g} (j , p) q = ≤-< p (q j)

  ≤-< : {x y z : Ord} -> x ≤ y -> y < z -> x < z
  ≤-< {x} {y} {sup K h} p (k , q) = k , ≤-trans p q

-- < is irreflexive (well-foundedness)
irrefl : (x : Ord) -> x < x -> Empty
irrefl (sup I f) (i , p) = irrefl (f i) (p i')
  where
    i' = i
    -- p : sup I f ≤ f i, so f i < f i

-- the lub of a Set-indexed family: all predecessors of all members
lub : (I : Set) -> (I -> Ord) -> Ord
lub I x = sup (Sg0 I (\ i -> Pred (x i))) (\ ip -> at (x (Sg0.fst ip)) (Sg0.snd ip))

private
  below : (y L : Ord) -> ((p : Pred y) -> at y p < L) -> y ≤ L
  below (sup J g) L h = h

  at< : (y z : Ord) -> y ≤ z -> (p : Pred y) -> at y p < z
  at< (sup J g) z h p = h p

lub-ub : (I : Set) (x : I -> Ord) (i : I) -> x i ≤ lub I x
lub-ub I x i = below (x i) (lub I x) (\ p -> (i , p) , ≤-refl (at (x i) p))

lub-least : (I : Set) (x : I -> Ord) (z : Ord) -> ((i : I) -> x i ≤ z) -> lub I x ≤ z
lub-least I x z h (i , p) = at< (x i) z (h i) p

------------------------------------------------------------------------
-- The counterexample
------------------------------------------------------------------------

data Empty0 : Set where

zeroO : Ord
zeroO = sup Empty0 (\ ())

sucO : Ord -> Ord
sucO x = sup Unit (\ _ -> x)

ordDCPO : SmallDCPO
ordDCPO = record
  { Car = Ord ; _≤_ = _≤_ ; ≤-refl = ≤-refl ; ≤-trans = ≤-trans
  ; bot = zeroO ; bot-least = \ x () 
  ; dsup = \ I x i0 d -> lub I x
  ; dsup-ub = \ I x i0 d i -> lub-ub I x i
  ; dsup-least = \ I x i0 d z h -> lub-least I x z h
  ; join = \ x y z p q -> lub Two (two x y)
  ; join-l = \ x y z p q -> lub-ub Two (two x y) tt
  ; join-r = \ x y z p q -> lub-ub Two (two x y) ff
  ; join-least = \ x y z p q w hx hy -> lub-least Two (two x y) w (both hx hy) }
  where
    two : Ord -> Ord -> Two -> Ord
    two x y tt = x
    two x y ff = y
    both : {x y w : Ord} -> x ≤ w -> y ≤ w -> (b : Two) -> two x y b ≤ w
    both hx hy tt = hx
    both hx hy ff = hy

sucO-mono : {x y : Ord} -> x ≤ y -> sucO x ≤ sucO y
sucO-mono p unit = unit , p

-- the small-sup fixed point theorem is inconsistent
refute : FixThmSmall -> Empty
refute T = irrefl x0 (And.r h unit)
  where
    r = FixThmSmall.fix T ordDCPO sucO sucO-mono
    x0 = Sg1.p1 r
    h = Sg1.p2 r
