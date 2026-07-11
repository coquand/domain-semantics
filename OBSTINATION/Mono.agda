{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Mono
--
-- Monotonicity of the finite interpretation (Section 1: "chaque element
-- de PR_n est monotone").  For every PR term p,
--
--   X <= Y  (pointwise, finite)   ==>   evalF p X <= evalF p Y.
--
-- The primitive-recursion case rests on `precF-mono`: precF is monotone
-- jointly in the height/shape of its first (finite) argument and in the
-- parameters Y, using the monotonicity of the step term h.  This is the
-- domain fact that the recursion chain is increasing, restricted to
-- finite arguments.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Mono where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR

------------------------------------------------------------------------
-- Small helpers (no recursion into evalF)
------------------------------------------------------------------------

-- bot (= fbot 0) is below every finite element
LeF-fbot0 : (z : FEl) -> LeF (fbot zero) z
LeF-fbot0 (fbot k) = tt
LeF-fbot0 (fcpl k) = tt

-- successor is monotone on finite elements
sucF-mono : {x y : FEl} -> LeF x y -> LeF (sucF x) (sucF y)
sucF-mono {fbot j} {fbot k} p = p
sucF-mono {fbot j} {fcpl k} p = p
sucF-mono {fcpl j} {fbot k} ()
sucF-mono {fcpl j} {fcpl k} p = Eq-cong suc p

-- cons two comparisons into a pointwise comparison
consLe : {x y : FEl} {Y Y' : FTup} ->
  LeF x y -> LeFTup Y Y' -> LeFTup (cons x Y) (cons y Y')
consLe lx lY = mkSigma lx lY

-- projections are monotone (coordinate-wise; the default compares to itself)
nthF-mono : (i : Nat) {X Y : FTup} ->
  LeFTup X Y -> LeF (nth (fbot zero) i X) (nth (fbot zero) i Y)
nthF-mono i       {nil}       {nil}       le = LeF-refl (fbot zero)
nthF-mono i       {nil}       {cons _ _}  ()
nthF-mono i       {cons _ _}  {nil}       ()
nthF-mono zero    {cons x xs} {cons y ys} le = fst le
nthF-mono (suc i) {cons x xs} {cons y ys} le = nthF-mono i {xs} {ys} (snd le)

------------------------------------------------------------------------
-- Monotonicity, mutually with the composition and recursion operators
------------------------------------------------------------------------

-- Implicit tuple/element arguments below are pinned explicitly: they are
-- determined only through the non-injective `embed`/`evalF`, so Agda cannot
-- infer them from the goal.

mutual
  evalF-mono : (p : PR) {X Y : FTup} -> LeFTup X Y -> LeF (evalF p X) (evalF p Y)
  evalF-mono zerf        le                          = LeF-refl (fcpl zero)
  evalF-mono (proj i)    le                          = nthF-mono i le
  evalF-mono succ        {nil}      {nil}        le = LeF-refl (fbot zero)
  evalF-mono succ        {nil}      {cons _ _}   ()
  evalF-mono succ        {cons _ _} {nil}        ()
  evalF-mono succ        {cons x xs}{cons y ys}  le = sucF-mono {x} {y} (fst le)
  evalF-mono (comp g hs) le                          = evalF-mono g (mapE-mono hs le)
  evalF-mono (prec g h)  {nil}      {nil}        le = LeF-refl (fbot zero)
  evalF-mono (prec g h)  {nil}      {cons _ _}   ()
  evalF-mono (prec g h)  {cons _ _} {nil}        ()
  evalF-mono (prec g h)  {cons a Y} {cons a' Y'} le =
    precF-mono g h {a} {a'} {Y} {Y'} (fst le) (snd le)

  mapE-mono : (hs : List PR) {X Y : FTup} ->
    LeFTup X Y -> LeFTup (mapE hs X) (mapE hs Y)
  mapE-mono nil         le = tt
  mapE-mono (cons p ps) le = mkSigma (evalF-mono p le) (mapE-mono ps le)

  precF-mono : (g h : PR) {a a' : FEl} {Y Y' : FTup} ->
    LeF a a' -> LeFTup Y Y' -> LeF (precF g h a Y) (precF g h a' Y')
  -- first argument bot j vs bot k
  precF-mono g h {fbot zero}    {fbot k}       {Y} {Y'} la lY =
    LeF-fbot0 (precF g h (fbot k) Y')
  precF-mono g h {fbot (suc j)} {fbot zero}    {Y} {Y'} () lY
  precF-mono g h {fbot (suc j)} {fbot (suc k)} {Y} {Y'} la lY =
    evalF-mono h
      {cons (fbot j) (cons (precF g h (fbot j) Y) Y)}
      {cons (fbot k) (cons (precF g h (fbot k) Y') Y')}
      (mkSigma la (mkSigma (precF-mono g h {fbot j} {fbot k} {Y} {Y'} la lY) lY))
  -- first argument bot j vs cpl k
  precF-mono g h {fbot zero}    {fcpl k}       {Y} {Y'} la lY =
    LeF-fbot0 (precF g h (fcpl k) Y')
  precF-mono g h {fbot (suc j)} {fcpl zero}    {Y} {Y'} () lY
  precF-mono g h {fbot (suc j)} {fcpl (suc k)} {Y} {Y'} la lY =
    evalF-mono h
      {cons (fbot j) (cons (precF g h (fbot j) Y) Y)}
      {cons (fcpl k) (cons (precF g h (fcpl k) Y') Y')}
      (mkSigma la (mkSigma (precF-mono g h {fbot j} {fcpl k} {Y} {Y'} la lY) lY))
  -- first argument cpl j vs bot k : impossible
  precF-mono g h {fcpl j}       {fbot k}       {Y} {Y'} () lY
  -- first argument cpl j vs cpl j (la : Eq j k forces k = j)
  precF-mono g h {fcpl zero}    {fcpl zero}    {Y} {Y'} refl lY = evalF-mono g lY
  precF-mono g h {fcpl (suc j)} {fcpl (suc j)} {Y} {Y'} refl lY =
    evalF-mono h
      {cons (fcpl j) (cons (precF g h (fcpl j) Y) Y)}
      {cons (fcpl j) (cons (precF g h (fcpl j) Y') Y')}
      (mkSigma (LeF-refl (fcpl j))
        (mkSigma (precF-mono g h {fcpl j} {fcpl j} {Y} {Y'} refl lY) lY))
