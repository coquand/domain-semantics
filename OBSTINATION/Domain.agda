{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Domain
--
-- The domain D of "lazy naturals" (entiers paresseux), Section 1 of the
-- note.  Elements are of the form S^k(0) (complete), S^k(bot)
-- (incomplete finite), or S^omega(bot) (the unique infinite element).
--
--   cpl k  =  S^k(0)         complete   (maximal)
--   bot k  =  S^k(bot)       incomplete finite;  bot 0 = bot
--   inf    =  S^omega(bot)   the unique infinite element
--
-- We also isolate the finite elements F as their own type FEl, since the
-- primitive-recursion interpretation is defined on finite tuples.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Domain where

open import OBSTINATION.Prelude

------------------------------------------------------------------------
-- The domain
------------------------------------------------------------------------

data D : Set where
  bot : Nat -> D    -- S^k(bot)
  cpl : Nat -> D    -- S^k(0)
  inf : D           -- S^omega(bot)

-- successor on D  (S(S^omega bot) = S^omega bot)
sucD : D -> D
sucD (bot k) = bot (suc k)
sucD (cpl k) = cpl (suc k)
sucD inf     = inf

-- the two distinguished elements
botD : D
botD = bot zero

zeroD : D
zeroD = cpl zero

------------------------------------------------------------------------
-- Finite elements F, as a datatype, with the embedding into D
------------------------------------------------------------------------

data FEl : Set where
  fbot : Nat -> FEl   -- S^k(bot)
  fcpl : Nat -> FEl   -- S^k(0)

embed : FEl -> D
embed (fbot k) = bot k
embed (fcpl k) = cpl k

sucF : FEl -> FEl
sucF (fbot k) = fbot (suc k)
sucF (fcpl k) = fcpl (suc k)

embed-sucF : (x : FEl) -> Eq (embed (sucF x)) (sucD (embed x))
embed-sucF (fbot k) = refl
embed-sucF (fcpl k) = refl

-- "is finite" predicate on D:  everything except inf
Finite : D -> Set
Finite (bot k) = Top
Finite (cpl k) = Top
Finite inf     = Empty

Finite-embed : (x : FEl) -> Finite (embed x)
Finite-embed (fbot k) = tt
Finite-embed (fcpl k) = tt

-- "is complete" predicate:  of the form S^k(0)
Complete : D -> Set
Complete (bot k) = Empty
Complete (cpl k) = Top
Complete inf     = Empty

------------------------------------------------------------------------
-- The information order on D
--
--   bot j <= bot k   iff  j <= k
--   bot j <= cpl k   iff  j <= k      (S^j(bot) below S^k(0))
--   bot j <= inf     always
--   cpl j <= cpl k   iff  j = k       (complete elements are maximal)
--   everything else with cpl or inf on the left is only <= itself.
------------------------------------------------------------------------

LeD : D -> D -> Set
LeD (bot j) (bot k) = LeN j k
LeD (bot j) (cpl k) = LeN j k
LeD (bot j) inf     = Top
LeD (cpl j) (bot k) = Empty
LeD (cpl j) (cpl k) = Eq j k
LeD (cpl j) inf     = Empty
LeD inf     (bot k) = Empty
LeD inf     (cpl k) = Empty
LeD inf     inf     = Top

LeD-refl : (x : D) -> LeD x x
LeD-refl (bot k) = LeN-refl k
LeD-refl (cpl k) = refl
LeD-refl inf     = tt

LeD-trans : {a b c : D} -> LeD a b -> LeD b c -> LeD a c
LeD-trans {bot i} {bot j} {bot k} p q = LeN-trans {i} {j} {k} p q
LeD-trans {bot i} {bot j} {cpl k} p q = LeN-trans {i} {j} {k} p q
LeD-trans {bot i} {bot j} {inf}   p q = tt
LeD-trans {bot i} {cpl j} {bot k} p ()
LeD-trans {bot i} {cpl j} {cpl k} p q =
  Eq-transport (\ z -> LeN i z) q p
LeD-trans {bot i} {cpl j} {inf}   p ()
LeD-trans {bot i} {inf}   {bot k} p ()
LeD-trans {bot i} {inf}   {cpl k} p ()
LeD-trans {bot i} {inf}   {inf}   p q = tt
LeD-trans {cpl i} {bot j} {c}     () q
LeD-trans {cpl i} {cpl j} {bot k} p ()
LeD-trans {cpl i} {cpl j} {cpl k} p q = Eq-trans p q
LeD-trans {cpl i} {cpl j} {inf}   p ()
LeD-trans {cpl i} {inf}   {c}     () q
LeD-trans {inf}   {bot j} {c}     () q
LeD-trans {inf}   {cpl j} {c}     () q
LeD-trans {inf}   {inf}   {bot k} p ()
LeD-trans {inf}   {inf}   {cpl k} p ()
LeD-trans {inf}   {inf}   {inf}   p q = tt

LeD-antisym : {a b : D} -> LeD a b -> LeD b a -> Eq a b
LeD-antisym {bot i} {bot j} p q = Eq-cong bot (LeN-antisym {i} {j} p q)
LeD-antisym {bot i} {cpl j} p ()
LeD-antisym {bot i} {inf}   p ()
LeD-antisym {cpl i} {bot j} () q
LeD-antisym {cpl i} {cpl j} p q = Eq-cong cpl p
LeD-antisym {cpl i} {inf}   () q
LeD-antisym {inf}   {bot j} () q
LeD-antisym {inf}   {cpl j} () q
LeD-antisym {inf}   {inf}   p q = refl

LeD-dec : (a b : D) -> Dec (LeD a b)
LeD-dec (bot j) (bot k) = LeN-dec j k
LeD-dec (bot j) (cpl k) = LeN-dec j k
LeD-dec (bot j) inf     = yes tt
LeD-dec (cpl j) (bot k) = no (\ ())
LeD-dec (cpl j) (cpl k) = EqNat-dec j k
LeD-dec (cpl j) inf     = no (\ ())
LeD-dec inf     (bot k) = no (\ ())
LeD-dec inf     (cpl k) = no (\ ())
LeD-dec inf     inf     = yes tt

-- bot is the least element
LeD-botD : (x : D) -> LeD botD x
LeD-botD (bot k) = tt
LeD-botD (cpl k) = tt
LeD-botD inf     = tt

-- successor is monotone
sucD-mono : {a b : D} -> LeD a b -> LeD (sucD a) (sucD b)
sucD-mono {bot i} {bot j} p = p
sucD-mono {bot i} {cpl j} p = p
sucD-mono {bot i} {inf}   p = tt
sucD-mono {cpl i} {bot j} ()
sucD-mono {cpl i} {cpl j} p = Eq-cong suc p
sucD-mono {cpl i} {inf}   ()
sucD-mono {inf}   {bot j} ()
sucD-mono {inf}   {cpl j} ()
sucD-mono {inf}   {inf}   p = tt

------------------------------------------------------------------------
-- Order on finite elements (inherited from D through embed)
------------------------------------------------------------------------

LeF : FEl -> FEl -> Set
LeF x y = LeD (embed x) (embed y)

LeF-refl : (x : FEl) -> LeF x x
LeF-refl x = LeD-refl (embed x)

LeF-trans : {a b c : FEl} -> LeF a b -> LeF b c -> LeF a c
LeF-trans {a} {b} {c} p q = LeD-trans {embed a} {embed b} {embed c} p q

LeF-dec : (a b : FEl) -> Dec (LeF a b)
LeF-dec a b = LeD-dec (embed a) (embed b)
