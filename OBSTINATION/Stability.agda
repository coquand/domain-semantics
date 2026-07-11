{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Stability
--
-- Berry stability of every PR element (min1.pdf: "tous les elements de
-- PR sont stables"):
--
--   BndT A B  (A, B have a common upper bound)
--     ==>  evalF p (A /\ B) = evalF p A /\ evalF p B.
--
-- Proved by induction on p, mutually with the composition and recursion
-- operators.  The recursion case `precF-stable` applies the stability of
-- the step term h (IH) to the two unfolded triples and rewrites their
-- meet by the inner induction on the first argument's height.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Stability where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Mono
open import OBSTINATION.Meet

------------------------------------------------------------------------
-- Boundedness is preserved (via the pointwise join as common bound
-- and monotonicity).
------------------------------------------------------------------------

Bnd-pres : (p : PR) {A B : FTup} -> BndT A B -> Bnd (evalF p A) (evalF p B)
Bnd-pres p {A} {B} bd =
  bnd-from-ub {evalF p A} {evalF p B} {evalF p (joinT A B)}
    (evalF-mono p (join-ubT-l bd)) (evalF-mono p (join-ubT-r bd))

precF-pres-Bnd : (g h : PR) {a a' : FEl} {Y Y' : FTup} ->
  Bnd a a' -> BndT Y Y' -> Bnd (precF g h a Y) (precF g h a' Y')
precF-pres-Bnd g h {a} {a'} {Y} {Y'} ba bY =
  bnd-from-ub {precF g h a Y} {precF g h a' Y'} {precF g h (joinF a a') (joinT Y Y')}
    (precF-mono g h {a}  {joinF a a'} {Y}  {joinT Y Y'} (join-ub-l {a} {a'} ba) (join-ubT-l bY))
    (precF-mono g h {a'} {joinF a a'} {Y'} {joinT Y Y'} (join-ub-r {a} {a'} ba) (join-ubT-r bY))

------------------------------------------------------------------------
-- meet commutes with projection
------------------------------------------------------------------------

nthF-meet : (i : Nat) {A B : FTup} -> BndT A B ->
  Eq (nth (fbot zero) i (meetT A B)) (meetF (nth (fbot zero) i A) (nth (fbot zero) i B))
nthF-meet i       {nil}      {nil}      bd = refl
nthF-meet i       {nil}      {cons _ _} ()
nthF-meet i       {cons _ _} {nil}      ()
nthF-meet zero    {cons a A} {cons b B} bd = refl
nthF-meet (suc i) {cons a A} {cons b B} bd = nthF-meet i {A} {B} (snd bd)

------------------------------------------------------------------------
-- mapE preserves boundedness (needed for the composition case)
------------------------------------------------------------------------

mapE-Bnd : (hs : List PR) {A B : FTup} -> BndT A B -> BndT (mapE hs A) (mapE hs B)
mapE-Bnd nil         bd = tt
mapE-Bnd (cons p ps) bd = mkSigma (Bnd-pres p bd) (mapE-Bnd ps bd)

------------------------------------------------------------------------
-- Stability, mutually with composition and recursion
------------------------------------------------------------------------

mutual
  stable : (p : PR) {A B : FTup} -> BndT A B ->
    Eq (evalF p (meetT A B)) (meetF (evalF p A) (evalF p B))
  stable zerf        bd                       = refl
  stable (proj i)    bd                       = nthF-meet i bd
  stable succ        {nil}      {nil}       bd = refl
  stable succ        {nil}      {cons _ _}  ()
  stable succ        {cons _ _} {nil}       ()
  stable succ        {cons a A} {cons b B}  bd = sucF-meetF a b
  stable (comp g hs) {A} {B}    bd            =
    Eq-trans (Eq-cong (evalF g) (mapE-stable hs bd)) (stable g (mapE-Bnd hs bd))
  stable (prec g h)  {nil}      {nil}       bd = refl
  stable (prec g h)  {nil}      {cons _ _}  ()
  stable (prec g h)  {cons _ _} {nil}       ()
  stable (prec g h)  {cons a Y} {cons b Y'} bd =
    precF-stable g h {a} {b} {Y} {Y'} (fst bd) (snd bd)

  mapE-stable : (hs : List PR) {A B : FTup} -> BndT A B ->
    Eq (mapE hs (meetT A B)) (meetT (mapE hs A) (mapE hs B))
  mapE-stable nil         bd = refl
  mapE-stable (cons p ps) bd = cons-eq (stable p bd) (mapE-stable ps bd)

  precF-stable : (g h : PR) {a a' : FEl} {Y Y' : FTup} ->
    Bnd a a' -> BndT Y Y' ->
    Eq (precF g h (meetF a a') (meetT Y Y')) (meetF (precF g h a Y) (precF g h a' Y'))

  -- first argument bot j vs bot k  (always bounded)
  precF-stable g h {fbot zero}    {fbot k}       {Y} {Y'} ba bY =
    Eq-sym (meetF-fbot0-l (precF g h (fbot k) Y'))
  precF-stable g h {fbot (suc j)} {fbot zero}    {Y} {Y'} ba bY =
    Eq-sym (meetF-fbot0-r (precF g h (fbot (suc j)) Y))
  precF-stable g h {fbot (suc j)} {fbot (suc k)} {Y} {Y'} ba bY =
    Eq-trans
      (Eq-cong (\ mid -> evalF h (cons (fbot (minN j k)) (cons mid (meetT Y Y'))))
        (precF-stable g h {fbot j} {fbot k} tt bY))
      (stable h
        {cons (fbot j) (cons (precF g h (fbot j) Y) Y)}
        {cons (fbot k) (cons (precF g h (fbot k) Y') Y')}
        (mkSigma tt (mkSigma (precF-pres-Bnd g h {fbot j} {fbot k} {Y} {Y'} tt bY) bY)))

  -- first argument bot j vs cpl k  (bounded iff j <= k)
  precF-stable g h {fbot zero}    {fcpl k}       {Y} {Y'} ba bY =
    Eq-sym (meetF-fbot0-l (precF g h (fcpl k) Y'))
  precF-stable g h {fbot (suc j)} {fcpl zero}    {Y} {Y'} () bY
  precF-stable g h {fbot (suc j)} {fcpl (suc k)} {Y} {Y'} ba bY =
    Eq-trans
      (Eq-cong (\ mid -> evalF h (cons (fbot j) (cons mid (meetT Y Y'))))
        (precF-stable g h {fbot j} {fcpl k} ba bY))
      (stable h
        {cons (fbot j) (cons (precF g h (fbot j) Y) Y)}
        {cons (fcpl k) (cons (precF g h (fcpl k) Y') Y')}
        (mkSigma ba (mkSigma (precF-pres-Bnd g h {fbot j} {fcpl k} {Y} {Y'} ba bY) bY)))

  -- first argument cpl j vs bot k  (bounded iff k <= j)
  precF-stable g h {fcpl j}       {fbot zero}    {Y} {Y'} ba bY =
    Eq-sym (meetF-fbot0-r (precF g h (fcpl j) Y))
  precF-stable g h {fcpl zero}    {fbot (suc k)} {Y} {Y'} () bY
  precF-stable g h {fcpl (suc j)} {fbot (suc k)} {Y} {Y'} ba bY =
    Eq-trans
      (Eq-cong (\ mid -> evalF h (cons (fbot k) (cons mid (meetT Y Y'))))
        (precF-stable g h {fcpl j} {fbot k} ba bY))
      (stable h
        {cons (fcpl j) (cons (precF g h (fcpl j) Y) Y)}
        {cons (fbot k) (cons (precF g h (fbot k) Y') Y')}
        (mkSigma ba (mkSigma (precF-pres-Bnd g h {fcpl j} {fbot k} {Y} {Y'} ba bY) bY)))

  -- first argument cpl j vs cpl j  (bounded iff equal; ba : Eq j k forces k = j)
  precF-stable g h {fcpl zero}    {fcpl zero}    {Y} {Y'} refl bY = stable g bY
  precF-stable g h {fcpl (suc j)} {fcpl (suc j)} {Y} {Y'} refl bY =
    Eq-trans
      (Eq-cong (\ mid -> evalF h (cons (fcpl (minN j j)) (cons mid (meetT Y Y'))))
        (precF-stable g h {fcpl j} {fcpl j} refl bY))
      (stable h
        {cons (fcpl j) (cons (precF g h (fcpl j) Y) Y)}
        {cons (fcpl j) (cons (precF g h (fcpl j) Y') Y')}
        (mkSigma refl (mkSigma (precF-pres-Bnd g h {fcpl j} {fcpl j} {Y} {Y'} refl bY) bY)))
