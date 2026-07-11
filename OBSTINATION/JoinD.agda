{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.JoinD
--
-- Upper-bound facts against a (possibly infinite) D-valued point A:
--
--   * two finite elements below a common D element are bounded (`Bnd`);
--   * `joinF`/`joinT` are still the least upper bound when the bound is
--     a D element (resp. a D-valued tuple).
--
-- These let the composition case combine the per-coordinate witnesses
-- (each `Below _ A`) into a single `Below (joinT _ _) A`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.JoinD where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Meet
open import OBSTINATION.JoinLub using (maxN-lub)
open import OBSTINATION.Property using (Below ; getF)

------------------------------------------------------------------------
-- Boundedness from a common D upper bound
------------------------------------------------------------------------

bnd-from-ubD : {a b : FEl} {d : D} -> LeD (embed a) d -> LeD (embed b) d -> Bnd a b
bnd-from-ubD {fbot j} {fbot k} {d}     p q = tt
bnd-from-ubD {fbot j} {fcpl k} {bot l} p ()
bnd-from-ubD {fbot j} {fcpl k} {cpl l} p q = Eq-transport (LeN j) (Eq-sym q) p
bnd-from-ubD {fbot j} {fcpl k} {inf}   p ()
bnd-from-ubD {fcpl j} {fbot k} {bot l} () q
bnd-from-ubD {fcpl j} {fbot k} {cpl l} p q = Eq-transport (LeN k) (Eq-sym p) q
bnd-from-ubD {fcpl j} {fbot k} {inf}   () q
bnd-from-ubD {fcpl j} {fcpl k} {bot l} () q
bnd-from-ubD {fcpl j} {fcpl k} {cpl l} p q = Eq-trans p (Eq-sym q)
bnd-from-ubD {fcpl j} {fcpl k} {inf}   () q

------------------------------------------------------------------------
-- joinF is the least upper bound against a D element
------------------------------------------------------------------------

joinF-lub-D : {a b : FEl} {d : D} ->
  LeD (embed a) d -> LeD (embed b) d -> LeD (embed (joinF a b)) d
joinF-lub-D {fbot j} {fbot k} {bot l} p q = maxN-lub {j} {k} {l} p q
joinF-lub-D {fbot j} {fbot k} {cpl l} p q = maxN-lub {j} {k} {l} p q
joinF-lub-D {fbot j} {fbot k} {inf}   p q = tt
joinF-lub-D {fbot j} {fcpl k} {bot l} p ()
joinF-lub-D {fbot j} {fcpl k} {cpl l} p q = q
joinF-lub-D {fbot j} {fcpl k} {inf}   p ()
joinF-lub-D {fcpl j} {fbot k} {bot l} () q
joinF-lub-D {fcpl j} {fbot k} {cpl l} p q = p
joinF-lub-D {fcpl j} {fbot k} {inf}   () q
joinF-lub-D {fcpl j} {fcpl k} {bot l} () q
joinF-lub-D {fcpl j} {fcpl k} {cpl l} refl refl = maxN-r {j} {j} (LeN-refl j)
joinF-lub-D {fcpl j} {fcpl k} {inf}   () q

------------------------------------------------------------------------
-- Pointwise lifting to Below (finite tuple below a D-valued tuple)
------------------------------------------------------------------------

BndT-from-Below : {P Q : FTup} {A : Tup} -> Below P A -> Below Q A -> BndT P Q
BndT-from-Below {nil}      {nil}      {nil}      p q = tt
BndT-from-Below {nil}      {nil}      {cons _ _} () q
BndT-from-Below {nil}      {cons _ _} {nil}      p ()
BndT-from-Below {nil}      {cons _ _} {cons _ _} () q
BndT-from-Below {cons _ _} {nil}      {nil}      () q
BndT-from-Below {cons _ _} {nil}      {cons _ _} p ()
BndT-from-Below {cons a P} {cons b Q} {nil}      () q
BndT-from-Below {cons a P} {cons b Q} {cons d A} p q =
  mkSigma (bnd-from-ubD {a} {b} {d} (fst p) (fst q)) (BndT-from-Below {P} {Q} {A} (snd p) (snd q))

Below-joinT : {P Q : FTup} {A : Tup} -> Below P A -> Below Q A -> Below (joinT P Q) A
Below-joinT {nil}      {nil}      {nil}      p q = tt
Below-joinT {nil}      {nil}      {cons _ _} () q
Below-joinT {nil}      {cons _ _} {nil}      p ()
Below-joinT {nil}      {cons _ _} {cons _ _} () q
Below-joinT {cons _ _} {nil}      {nil}      () q
Below-joinT {cons _ _} {nil}      {cons _ _} p ()
Below-joinT {cons a P} {cons b Q} {nil}      () q
Below-joinT {cons a P} {cons b Q} {cons d A} p q =
  mkSigma (joinF-lub-D {a} {b} {d} (fst p) (fst q)) (Below-joinT {P} {Q} {A} (snd p) (snd q))

------------------------------------------------------------------------
-- join absorbs the larger element; getF distributes over joinT
------------------------------------------------------------------------

joinF-absorb-r : {a b : FEl} -> LeF a b -> Eq (joinF a b) b
joinF-absorb-r {fbot j} {fbot k} le = Eq-cong fbot (maxN-r {j} {k} le)
joinF-absorb-r {fbot j} {fcpl k} le = refl
joinF-absorb-r {fcpl j} {fbot k} ()
joinF-absorb-r {fcpl j} {fcpl k} refl = Eq-cong fcpl (maxN-r {k} {k} (LeN-refl k))

getF-joinT : (i : Nat) (P Q : FTup) -> Eq (length P) (length Q) ->
  Eq (getF i (joinT P Q)) (joinF (getF i P) (getF i Q))
getF-joinT i       nil         nil         leq = refl
getF-joinT i       nil         (cons _ _)  ()
getF-joinT i       (cons _ _)  nil         ()
getF-joinT zero    (cons a P)  (cons b Q)  leq = refl
getF-joinT (suc i) (cons a P)  (cons b Q)  leq = getF-joinT i P Q (suc-inj leq)
