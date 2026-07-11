{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Meet
--
-- The (coherent) lattice structure on the finite domain F, needed for
-- Berry stability (min1.pdf: elements of PR are stable functions).
-- Two finite elements are "bounded" (`Bnd`) when they have a common
-- upper bound; bounded pairs have a meet `meetF` (glb) and a join
-- `joinF` (lub).  Lifted pointwise to tuples.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Meet where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples

------------------------------------------------------------------------
-- Bounded (= have a common upper bound) on finite elements
------------------------------------------------------------------------

Bnd : FEl -> FEl -> Set
Bnd (fbot j) (fbot k) = Top
Bnd (fbot j) (fcpl k) = LeN j k
Bnd (fcpl j) (fbot k) = LeN k j
Bnd (fcpl j) (fcpl k) = Eq j k

-- meet (greatest lower bound, on bounded pairs)
meetF : FEl -> FEl -> FEl
meetF (fbot j) (fbot k) = fbot (minN j k)
meetF (fbot j) (fcpl k) = fbot j
meetF (fcpl j) (fbot k) = fbot k
meetF (fcpl j) (fcpl k) = fcpl (minN j k)

-- join (least upper bound, on bounded pairs)
joinF : FEl -> FEl -> FEl
joinF (fbot j) (fbot k) = fbot (maxN j k)
joinF (fbot j) (fcpl k) = fcpl k
joinF (fcpl j) (fbot k) = fcpl j
joinF (fcpl j) (fcpl k) = fcpl (maxN j k)

------------------------------------------------------------------------
-- From a common upper bound to boundedness
------------------------------------------------------------------------

bnd-from-ub : {x y u : FEl} -> LeF x u -> LeF y u -> Bnd x y
bnd-from-ub {fbot j} {fbot k} {u}      lx ly = tt
bnd-from-ub {fbot j} {fcpl k} {fbot m}  lx ()
bnd-from-ub {fbot j} {fcpl k} {fcpl m} lx ly = Eq-transport (LeN j) (Eq-sym ly) lx
bnd-from-ub {fcpl j} {fbot k} {fbot m}  () ly
bnd-from-ub {fcpl j} {fbot k} {fcpl m} lx ly = Eq-transport (LeN k) (Eq-sym lx) ly
bnd-from-ub {fcpl j} {fcpl k} {fbot m}  () ly
bnd-from-ub {fcpl j} {fcpl k} {fcpl m} lx ly = Eq-trans lx (Eq-sym ly)

------------------------------------------------------------------------
-- join is an upper bound
------------------------------------------------------------------------

join-ub-l : {a b : FEl} -> Bnd a b -> LeF a (joinF a b)
join-ub-l {fbot j} {fbot k} bd = maxN-le-l j k
join-ub-l {fbot j} {fcpl k} bd = bd
join-ub-l {fcpl j} {fbot k} bd = refl
join-ub-l {fcpl j} {fcpl k} refl = Eq-sym (maxN-r {j} {j} (LeN-refl j))

join-ub-r : {a b : FEl} -> Bnd a b -> LeF b (joinF a b)
join-ub-r {fbot j} {fbot k} bd = maxN-le-r j k
join-ub-r {fbot j} {fcpl k} bd = refl
join-ub-r {fcpl j} {fbot k} bd = bd
join-ub-r {fcpl j} {fcpl k} refl = Eq-sym (maxN-r {j} {j} (LeN-refl j))

------------------------------------------------------------------------
-- meet with bottom, and successor commuting with meet
------------------------------------------------------------------------

meetF-fbot0-l : (z : FEl) -> Eq (meetF (fbot zero) z) (fbot zero)
meetF-fbot0-l (fbot k) = refl
meetF-fbot0-l (fcpl k) = refl

meetF-fbot0-r : (z : FEl) -> Eq (meetF z (fbot zero)) (fbot zero)
meetF-fbot0-r (fbot k) = Eq-cong fbot (minN-zero-r k)
meetF-fbot0-r (fcpl k) = refl

sucF-meetF : (a b : FEl) -> Eq (sucF (meetF a b)) (meetF (sucF a) (sucF b))
sucF-meetF (fbot j) (fbot k) = refl
sucF-meetF (fbot j) (fcpl k) = refl
sucF-meetF (fcpl j) (fbot k) = refl
sucF-meetF (fcpl j) (fcpl k) = refl

------------------------------------------------------------------------
-- Pointwise lifting to tuples
------------------------------------------------------------------------

BndT : FTup -> FTup -> Set
BndT nil         nil         = Top
BndT nil         (cons _ _)  = Empty
BndT (cons _ _)  nil         = Empty
BndT (cons a A)  (cons b B)  = Pair (Bnd a b) (BndT A B)

meetT : FTup -> FTup -> FTup
meetT nil         nil         = nil
meetT nil         (cons _ _)  = nil
meetT (cons _ _)  nil         = nil
meetT (cons a A)  (cons b B)  = cons (meetF a b) (meetT A B)

joinT : FTup -> FTup -> FTup
joinT nil         nil         = nil
joinT nil         (cons _ _)  = nil
joinT (cons _ _)  nil         = nil
joinT (cons a A)  (cons b B)  = cons (joinF a b) (joinT A B)

join-ubT-l : {A B : FTup} -> BndT A B -> LeFTup A (joinT A B)
join-ubT-l {nil}      {nil}      bd = tt
join-ubT-l {nil}      {cons _ _} ()
join-ubT-l {cons _ _} {nil}      ()
join-ubT-l {cons a A} {cons b B} bd = mkSigma (join-ub-l {a} {b} (fst bd)) (join-ubT-l (snd bd))

join-ubT-r : {A B : FTup} -> BndT A B -> LeFTup B (joinT A B)
join-ubT-r {nil}      {nil}      bd = tt
join-ubT-r {nil}      {cons _ _} ()
join-ubT-r {cons _ _} {nil}      ()
join-ubT-r {cons a A} {cons b B} bd = mkSigma (join-ub-r {a} {b} (fst bd)) (join-ubT-r (snd bd))

------------------------------------------------------------------------
-- cons is a congruence for equality (used to assemble tuple equalities)
------------------------------------------------------------------------

cons-eq : {x y : FEl} {A B : FTup} -> Eq x y -> Eq A B -> Eq (cons x A) (cons y B)
cons-eq refl refl = refl
