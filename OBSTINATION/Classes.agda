{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Classes
--
-- Phase F of the trace development: the numeric function classes of
-- R. David, "Decidability results for primitive recursive algorithms",
-- TCS 300 (2003) 477-504 (rdavid.pdf), Definitions 11 and 12.
--
--   Def 11    a class C of functions N -> N is closed by
--             * finite change : f in C, f = g except finitely often => g in C;
--             * minimum       : f,g in C => n |-> min(f n, g n) in C;
--             * iteration     : f in C, f n > n for all n, g(n+1) = f(g n)
--                               for all n  =>  g in C;
--             * multi-step it.: f in C, f n > n, some p >= 1 with
--                               g(n+p) = f(g n) for all n  =>  g in C;
--             * mixed it.      (only needed for C_alt) -- omitted here.
--   Def 12(1) C0 = { n|->0 , n|->n , n|->n+1 , n|->(n=0 ? 0 : n-1) }.
--   Def 12(2) C_pr  = least set of INCREASING functions containing C0,
--                     closed by composition, finite change, iteration.
--   Def 12(3) C_mut = least set of INCREASING functions containing C0,
--                     closed by composition, finite change, multi-step
--                     iteration.
--
-- These are the classes over which Proposition 18 (the hard combinatorial
-- core, Phase G) classifies growth.  This file is pure arithmetic --
-- independent of the trace machinery (Words/Traces/Nb) -- so it can be
-- built and checked on its own.
--
-- MODELLING NOTE.  "least set of INCREASING functions closed by ..." makes
-- membership entail monotonicity.  Composition and (single-step) iteration
-- PRESERVE monotonicity, so their constructors need no side condition and it
-- is DERIVED (`Cpr-inc`).  Finite change and general multi-step iteration
-- (p >= 2, which relates only n and n+p) do NOT preserve monotonicity, so
-- their constructors carry `Increasing g` as a premise -- exactly David's
-- "of increasing functions" clause.  Hence every member is increasing
-- (`Cpr-inc`, `Cmut-inc`), as the definition demands.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Classes where

open import OBSTINATION.Prelude

------------------------------------------------------------------------
-- Self-contained arithmetic (recursion on the SECOND argument, so that
-- `add n (suc p) = suc (add n p)` is definitional -- what the multi-step
-- recurrence `g (add n p)` needs)
------------------------------------------------------------------------

add : Nat -> Nat -> Nat
add m zero    = m
add m (suc n) = suc (add m n)

add-zero-l : (n : Nat) -> Eq (add zero n) n
add-zero-l zero    = refl
add-zero-l (suc n) = Eq-cong suc (add-zero-l n)

add-suc-l : (m n : Nat) -> Eq (add (suc m) n) (suc (add m n))
add-suc-l m zero    = refl
add-suc-l m (suc n) = Eq-cong suc (add-suc-l m n)

add-ge : (m n : Nat) -> LeN m (add m n)
add-ge m zero    = LeN-refl m
add-ge m (suc n) = LeN-trans {m} {add m n} {suc (add m n)} (add-ge m n) (LeN-suc (add m n))

le-to-add : (m n : Nat) -> LeN m n -> Sigma Nat (\ d -> Eq (add m d) n)
le-to-add zero    n       le = mkSigma n (add-zero-l n)
le-to-add (suc m) zero    ()
le-to-add (suc m) (suc n) le =
  mkSigma (fst r) (Eq-trans (add-suc-l m (fst r)) (Eq-cong suc (snd r)))
  where
    r = le-to-add m n le

mul : Nat -> Nat -> Nat
mul a zero    = zero
mul a (suc n) = add (mul a n) a

-- weaken a strict bound
LeN-weaken : (x y : Nat) -> LeN (suc x) y -> LeN x y
LeN-weaken x zero    ()
LeN-weaken x (suc y) le = LeN-trans {x} {y} {suc y} le (LeN-suc y)

------------------------------------------------------------------------
-- Increasing (monotone non-decreasing) and expanding (f n > n)
------------------------------------------------------------------------

Increasing : (Nat -> Nat) -> Set
Increasing f = (m n : Nat) -> LeN m n -> LeN (f m) (f n)

Expanding : (Nat -> Nat) -> Set
Expanding f = (n : Nat) -> LeN (suc n) (f n)

-- monotone from the consecutive step
mono-step : (f : Nat -> Nat) -> ((n : Nat) -> LeN (f n) (f (suc n))) ->
  Increasing f
mono-step f st m n le =
  Eq-transport (\ z -> LeN (f m) (f z)) (snd r) (up (fst r))
  where
    r = le-to-add m n le

    up : (d : Nat) -> LeN (f m) (f (add m d))
    up zero    = LeN-refl (f m)
    up (suc d) =
      LeN-trans {f m} {f (add m d)} {f (suc (add m d))} (up d) (st (add m d))

-- composition preserves monotonicity
comp-inc : {f g : Nat -> Nat} -> Increasing f -> Increasing g ->
  Increasing (\ n -> f (g n))
comp-inc {f} {g} incf incg m n le = incf (g m) (g n) (incg m n le)

-- a function defined by g(suc n) = f(g n) with f expanding is increasing
iter-inc : (f g : Nat -> Nat) -> Expanding f ->
  ((n : Nat) -> Eq (g (suc n)) (f (g n))) -> Increasing g
iter-inc f g ef rec = mono-step g step
  where
    step : (n : Nat) -> LeN (g n) (g (suc n))
    step n =
      Eq-transport (\ z -> LeN (g n) z) (Eq-sym (rec n))
        (LeN-weaken (g n) (f (g n)) (ef (g n)))

------------------------------------------------------------------------
-- Finite change (agree beyond some point)
------------------------------------------------------------------------

FiniteChange : (Nat -> Nat) -> (Nat -> Nat) -> Set
FiniteChange f g = Sigma Nat (\ N -> (n : Nat) -> LeN N n -> Eq (f n) (g n))

------------------------------------------------------------------------
-- Def 12(1): the four base functions C0
------------------------------------------------------------------------

predN : Nat -> Nat
predN zero    = zero
predN (suc n) = n

data C0f : Set where
  zc ic sc pc : C0f

c0 : C0f -> (Nat -> Nat)
c0 zc = \ _ -> zero
c0 ic = \ n -> n
c0 sc = suc
c0 pc = predN

predN-inc : Increasing predN
predN-inc zero    n       le = tt
predN-inc (suc m) zero    ()
predN-inc (suc m) (suc n) le = le

c0-inc : (b : C0f) -> Increasing (c0 b)
c0-inc zc m n le = tt
c0-inc ic m n le = le
c0-inc sc m n le = le
c0-inc pc m n le = predN-inc m n le

------------------------------------------------------------------------
-- Def 12(2): C_pr
------------------------------------------------------------------------

data Cpr : (Nat -> Nat) -> Set where
  cpr-base : (b : C0f) -> Cpr (c0 b)
  cpr-comp : {f g : Nat -> Nat} -> Cpr f -> Cpr g -> Cpr (\ n -> f (g n))
  cpr-fchg : {f g : Nat -> Nat} -> Cpr f -> Increasing g ->
             FiniteChange f g -> Cpr g
  cpr-iter : {f g : Nat -> Nat} -> Cpr f -> Expanding f ->
             ((n : Nat) -> Eq (g (suc n)) (f (g n))) -> Cpr g

-- every member of C_pr is increasing
Cpr-inc : {f : Nat -> Nat} -> Cpr f -> Increasing f
Cpr-inc (cpr-base b)              = c0-inc b
Cpr-inc (cpr-comp {f} {g} cf cg)  = comp-inc {f} {g} (Cpr-inc cf) (Cpr-inc cg)
Cpr-inc (cpr-fchg cf ig fc)       = ig
Cpr-inc {g} (cpr-iter {f} cf ef rec) = iter-inc f g ef rec

------------------------------------------------------------------------
-- Def 12(3): C_mut  (multi-step iteration, p >= 1, includes p = 1)
------------------------------------------------------------------------

data Cmut : (Nat -> Nat) -> Set where
  cmut-base : (b : C0f) -> Cmut (c0 b)
  cmut-comp : {f g : Nat -> Nat} -> Cmut f -> Cmut g -> Cmut (\ n -> f (g n))
  cmut-fchg : {f g : Nat -> Nat} -> Cmut f -> Increasing g ->
              FiniteChange f g -> Cmut g
  cmut-mstep : {f g : Nat -> Nat} -> Cmut f -> Expanding f ->
               (p : Nat) -> LeN (suc zero) p -> Increasing g ->
               ((n : Nat) -> Eq (g (add n p)) (f (g n))) -> Cmut g

Cmut-inc : {f : Nat -> Nat} -> Cmut f -> Increasing f
Cmut-inc (cmut-base b)                   = c0-inc b
Cmut-inc (cmut-comp {f} {g} cf cg)       = comp-inc {f} {g} (Cmut-inc cf) (Cmut-inc cg)
Cmut-inc (cmut-fchg cf ig fc)            = ig
Cmut-inc (cmut-mstep cf ef p p1 ig r) = ig

------------------------------------------------------------------------
-- ACCEPTANCE (plan Phase F): linear functions in C_pr, halving in C_mut
------------------------------------------------------------------------

-- n |-> n + c  is in C_pr
addc-Cpr : (c : Nat) -> Cpr (\ n -> add n c)
addc-Cpr zero    = cpr-base ic
addc-Cpr (suc c) = cpr-comp (cpr-base sc) (addc-Cpr c)

-- n |-> n + a  is expanding when a >= 1
addc-exp : (a : Nat) -> LeN (suc zero) a -> Expanding (\ n -> add n a)
addc-exp zero    ()
addc-exp (suc a) le n = add-ge n a

-- n |-> a * n  is in C_pr  (for a >= 1: iteration of + a)
mul-Cpr : (a : Nat) -> LeN (suc zero) a -> Cpr (\ n -> mul a n)
mul-Cpr a a1 = cpr-iter (addc-Cpr a) (addc-exp a a1) (\ n -> refl)

-- n |-> a * n + b  is in C_pr  (the general linear function, a >= 1)
linear-Cpr : (a b : Nat) -> LeN (suc zero) a -> Cpr (\ n -> add (mul a n) b)
linear-Cpr a b a1 = cpr-comp (addc-Cpr b) (mul-Cpr a a1)

-- n |-> floor (n / 2)  (David's halving), via MULTI-STEP iteration, p = 2:
--   half (n + 2) = suc (half n) = S (half n)
half : Nat -> Nat
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

half-step : (n : Nat) -> LeN (half n) (half (suc n))
half-step zero          = tt
half-step (suc zero)    = tt
half-step (suc (suc n)) = half-step n

half-inc : Increasing half
half-inc = mono-step half half-step

-- successor is expanding
suc-exp : Expanding suc
suc-exp n = LeN-refl n

-- half is NOT expressible by single-step iteration (period 2), but IS in
-- C_mut by multi-step iteration with p = 2 and f = successor
half-Cmut : Cmut half
half-Cmut =
  cmut-mstep (cmut-base sc) suc-exp (suc (suc zero)) tt half-inc (\ n -> refl)
