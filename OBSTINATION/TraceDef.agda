{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TraceDef
--
-- THE TRACE, DEFINED BY INDUCTION ON THE TERM, AND THE BASE CASES.
--
-- A trace of arity `a` is a walk `iv : Nat -> Nat` (which coordinate is
-- demanded at step `n`, with `iv n < a`) together with the VALUE the term
-- has when its replay sticks at step `n`:
--
--     ov : Nat -> FEl
--
-- `ov` replaces the old `kv : Nat -> Nat`.  The old shape could only ever
-- output `fbot _`, so `prec zerf zerf` -- which is `bot` at `bot` and the
-- COMPLETE `0` above it -- refuted it, with no `comp` in sight.  Reading
-- the value POINTWISE, rather than as a height plus a halting threshold,
-- is what keeps the trace definable by induction on the term alone: a
-- threshold would have to be searched for, and only MP1 could produce it.
--
-- The second addition is for TOTAL ARGUMENTS.  `fbot v` and `fcpl v` both
-- supply `v` levels, so the walk is identical until it needs level `v` of
-- that coordinate; there `fbot v` blocks, while `fcpl v` answers "0" and
-- the computation goes on with that coordinate now a fixed NUMERAL -- so
-- it can be frozen into the term, and the continuation is a trace of the
-- REMAINING coordinates:
--
--     cont : (c : Nat) -> c < a -> (v : Nat) -> Tr (a-1)
--
-- The arity strictly decreases, so `Tr` is an ORDINARY inductive family
-- and `sem` is structurally recursive -- no coinduction.
--
--     sem (node iv ivr ov cont) X          -- n = nOf a iv ivr (heights X)
--       | ov n = fcpl w      =  fcpl w                        -- total
--       | X (iv n) = fbot _  =  ov n                          -- blocked
--       | X (iv n) = fcpl v  =  sem (cont (iv n) _ v) (del (iv n) X)
--
-- min1.pdf's three cases are then a THEOREM about `ov` (MP1), not data in
-- the trace: Case 1 is `ov` eventually complete, Case 2 is `ov` eventually
-- constant incomplete, Case 3 is `ov` incomplete with a strictly
-- increasing height.
--
-- This file: the definition, the semantics, and the three base cases with
-- their correctness against `PR.evalF`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TraceDef where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; sucF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (lv ; nOf)
open import OBSTINATION.PR using (PR ; zerf ; proj ; succ ; evalF)
open import OBSTINATION.MP1Base using (module Const)

------------------------------------------------------------------------
-- heights of a tuple
------------------------------------------------------------------------

hgt : FEl -> Nat
hgt (fbot k) = k
hgt (fcpl k) = k

hts : FTup -> Nat -> Nat
hts X c = hgt (nth (fbot zero) c X)

------------------------------------------------------------------------
-- re-indexing under `del`: coordinate `i` of `X`, seen in `del c X`
------------------------------------------------------------------------

sd : Nat -> Nat -> Nat
sd zero    i       = pred i
  where
    pred : Nat -> Nat
    pred zero    = zero
    pred (suc j) = j
sd (suc c) zero    = zero
sd (suc c) (suc i) = suc (sd c i)

sd-range : (a c i : Nat) -> LeN (suc c) (suc a) -> LeN (suc i) (suc a)
         -> Not (Eq i c) -> LeN (suc (sd c i)) a
sd-range a       zero    zero     lc li ne = Empty-elim (ne refl)
sd-range a       zero    (suc i)  lc li ne = li
sd-range zero    (suc c) i        () li ne
sd-range (suc a) (suc c) zero     lc li ne = tt
sd-range (suc a) (suc c) (suc i)  lc li ne =
  sd-range a c i lc li (\ e -> ne (Eq-cong suc e))

------------------------------------------------------------------------
-- THE TRACE
------------------------------------------------------------------------

data Tr : Nat -> Set where
  stop : {a : Nat} -> FEl -> Tr a
  node : {a : Nat}
       -> (iv : Nat -> Nat)
       -> (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a))
       -> (ov : Nat -> FEl)
       -> (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
       -> Tr (suc a)

------------------------------------------------------------------------
-- THE SEMANTICS
--
-- Both case analyses are TOP-LEVEL functions, not `where` clauses, so
-- that the proofs below can reason about them by `Eq-cong`.
------------------------------------------------------------------------

-- has the computation already produced a total value?
hlt : FEl -> FEl -> FEl
hlt (fcpl w) bl = fcpl w
hlt (fbot w) bl = bl

-- at the sticking point: blocked on `fbot`, freeze-and-continue on `fcpl`
brf : FEl -> FEl -> FEl -> FEl
brf out alt (fbot _) = out
brf out alt (fcpl _) = alt

mutual
  sem : (a : Nat) -> Tr a -> FTup -> FEl
  sem a       (stop v)                X = v
  sem (suc a) (node iv ivr ov cont) X =
    semAt a iv ov cont X (nOf (suc a) iv ivr (hts X)) ivr

  semAt : (a : Nat) (iv : Nat -> Nat) (ov : Nat -> FEl)
        -> (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
        -> FTup -> (n : Nat)
        -> (ivr : (m : Nat) -> LeN (suc (iv m)) (suc a)) -> FEl
  semAt a iv ov cont X n ivr =
    hlt (ov n)
      (brf (ov n)
        (sem a (cont (iv n) (ivr n) (hts X (iv n))) (del (iv n) X))
        (nth (fbot zero) (iv n) X))

------------------------------------------------------------------------
-- THE BASE CASES
--
-- All three have a CONSTANT walk index, so `MP1Base.Const.nOf-const`
-- computes their replay outright: it sticks at the height of the
-- coordinate they read.
------------------------------------------------------------------------

-- zerf: total at once, with the value 0
zerfTr : (a : Nat) -> Tr a
zerfTr a = stop (fcpl zero)

zerfTr-sem : (a : Nat) (X : FTup) -> Eq (sem a (zerfTr a) X) (evalF zerf X)
zerfTr-sem a X = refl

------------------------------------------------------------------------
-- proj i: the value at replay depth `n` is `S^n(bot)`.  Freezing
-- coordinate `i` to the numeral `v` answers `v`; freezing any OTHER
-- coordinate leaves the projection alone, at its shifted index.
------------------------------------------------------------------------

mutual
  projTr : (a i : Nat) -> LeN (suc i) a -> Tr a
  projTr zero    i       ()
  projTr (suc a) i li =
    node (\ _ -> i) (\ _ -> li) (\ n -> fbot n) (projCont a i li)

  projCont : (a i : Nat) -> LeN (suc i) (suc a)
           -> (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a
  projCont a i li c lc v = projPick a i li c lc v (EqNat-dec i c)

  projPick : (a i : Nat) -> LeN (suc i) (suc a)
           -> (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat)
           -> Dec (Eq i c) -> Tr a
  projPick a i li c lc v (yes _)  = stop (fcpl v)
  projPick a i li c lc v (no  ne) = projTr a (sd c i) (sd-range a c i lc li ne)

projCont-hit : (a i : Nat) (li : LeN (suc i) (suc a))
             (lc : LeN (suc i) (suc a)) (v : Nat)
             -> Eq (projCont a i li i lc v) (stop (fcpl v))
projCont-hit a i li lc v = go (EqNat-dec i i) refl
  where
    go : (D : Dec (Eq i i)) -> Eq (EqNat-dec i i) D
       -> Eq (projCont a i li i lc v) (stop (fcpl v))
    go (yes _)  eD = Eq-cong (projPick a i li i lc v) eD
    go (no  ne) eD = Empty-elim (ne refl)

projTr-sem : (a i : Nat) (li : LeN (suc i) (suc a)) (X : FTup)
           -> Eq (sem (suc a) (projTr (suc a) i li) X) (evalF (proj i) X)
projTr-sem a i li X = go (nth (fbot zero) i X) refl
  where
    open Const (suc a) i (\ _ -> li)

    n : Nat
    n = nOf (suc a) (\ _ -> i) (\ _ -> li) (hts X)

    stick : Eq n (hgt (nth (fbot zero) i X))
    stick = nOf-const (hts X)

    alt : FEl
    alt = sem a (projCont a i li i li (hts X i)) (del i X)

    go : (y : FEl) -> Eq (nth (fbot zero) i X) y
       -> Eq (sem (suc a) (projTr (suc a) i li) X) (nth (fbot zero) i X)
    go (fbot j) e =
      Eq-trans (Eq-cong (\ z -> brf (fbot n) alt z) e)
        (Eq-trans (Eq-cong fbot (Eq-trans stick (Eq-cong hgt e))) (Eq-sym e))
    go (fcpl j) e =
      Eq-trans (Eq-cong (\ z -> brf (fbot n) alt z) e)
        (Eq-trans hits (Eq-sym e))
      where
        hj : Eq (hts X i) j
        hj = Eq-cong hgt e

        hits : Eq alt (fcpl j)
        hits =
          Eq-trans
            (Eq-cong (\ z -> sem a (projCont a i li i li z) (del i X)) hj)
            (Eq-cong (\ T -> sem a T (del i X)) (projCont-hit a i li li j))

------------------------------------------------------------------------
-- succ: arity 1, value `S^(n+1)(bot)` at replay depth `n`; freezing its
-- single coordinate to `v` answers the numeral `v+1`
------------------------------------------------------------------------

succTr : Tr (suc zero)
succTr =
  node (\ _ -> zero) (\ _ -> tt) (\ n -> fbot (suc n))
    (\ _ _ v -> stop (fcpl (suc v)))

succTr-sem : (X : FTup) -> Eq (length X) (suc zero)
           -> Eq (sem (suc zero) succTr X) (evalF succ X)
succTr-sem nil                  ()
succTr-sem (cons x (cons y ys)) ()
succTr-sem (cons x nil)         e = go x refl
  where
    open Const (suc zero) zero (\ _ -> tt)

    n : Nat
    n = nOf (suc zero) (\ _ -> zero) (\ _ -> tt) (hts (cons x nil))

    stick : Eq n (hgt x)
    stick = nOf-const (hts (cons x nil))

    alt : FEl
    alt = fcpl (suc (hts (cons x nil) zero))

    go : (y : FEl) -> Eq x y
       -> Eq (sem (suc zero) succTr (cons x nil)) (sucF x)
    go (fbot j) ex =
      Eq-trans (Eq-cong (\ z -> brf (fbot (suc n)) alt z) ex)
        (Eq-trans (Eq-cong (\ z -> fbot (suc z)) (Eq-trans stick (Eq-cong hgt ex)))
          (Eq-cong sucF (Eq-sym ex)))
    go (fcpl j) ex =
      Eq-trans (Eq-cong (\ z -> brf (fbot (suc n)) alt z) ex)
        (Eq-trans (Eq-cong (\ z -> fcpl (suc z)) (Eq-cong hgt ex))
          (Eq-cong sucF (Eq-sym ex)))

------------------------------------------------------------------------
-- ACCESSORS
--
-- A `stop` never demands anything: its walk is junk (coordinate 0, in
-- range at every positive arity) and freezing a coordinate leaves it
-- alone.
------------------------------------------------------------------------

ovOf : {a : Nat} -> Tr a -> Nat -> FEl
ovOf (stop v)              n = v
ovOf (node iv ivr ov cont) n = ov n

ivOf : {a : Nat} -> Tr a -> Nat -> Nat
ivOf (stop v)              n = zero
ivOf (node iv ivr ov cont) n = iv n

ivrOf : {a : Nat} (T : Tr (suc a)) (n : Nat) -> LeN (suc (ivOf T n)) (suc a)
ivrOf (stop v)              n = tt
ivrOf (node iv ivr ov cont) n = ivr n

-- how far a trace's own replay gets against given levels
nOfOf : (a : Nat) -> Tr a -> (Nat -> Nat) -> Nat
nOfOf a       (stop v)              av = zero
nOfOf (suc a) (node iv ivr ov cont) av = nOf (suc a) iv ivr av

contOf : {a : Nat} -> Tr (suc a) -> (c : Nat) -> LeN (suc c) (suc a)
       -> (v : Nat) -> Tr a
contOf (stop w)              c lc v = stop w
contOf (node iv ivr ov cont) c lc v = cont c lc v

------------------------------------------------------------------------
-- WHICH COORDINATE IS THE COMPUTATION WAITING ON?
--
-- `inl tt` -- none: either it has produced a total value, or it is stuck
-- for good.  `inr c` -- it is blocked on coordinate `c` of the ORIGINAL
-- tuple, so the index has to be un-shifted through every freeze (`su`).
------------------------------------------------------------------------

-- coordinate `j` of `del c X`, seen in `X`
su : Nat -> Nat -> Nat
su zero    j       = suc j
su (suc c) zero    = zero
su (suc c) (suc j) = suc (su c j)

shiftOr : Nat -> Or Top Nat -> Or Top Nat
shiftOr c (inl tt) = inl tt
shiftOr c (inr j)  = inr (su c j)

hb : FEl -> Or Top Nat -> Or Top Nat
hb (fcpl _) r = inl tt
hb (fbot _) r = r

bb : Nat -> Or Top Nat -> FEl -> Or Top Nat
bb c alt (fbot _) = inr c
bb c alt (fcpl _) = alt

mutual
  blockOn : (a : Nat) -> Tr a -> FTup -> Or Top Nat
  blockOn a       (stop v)              X = inl tt
  blockOn (suc a) (node iv ivr ov cont) X =
    blockAt a iv ov cont X (nOf (suc a) iv ivr (hts X)) ivr

  blockAt : (a : Nat) (iv : Nat -> Nat) (ov : Nat -> FEl)
          -> (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
          -> FTup -> (n : Nat)
          -> (ivr : (m : Nat) -> LeN (suc (iv m)) (suc a)) -> Or Top Nat
  blockAt a iv ov cont X n ivr =
    hb (ov n)
      (bb (iv n)
        (shiftOr (iv n)
          (blockOn a (cont (iv n) (ivr n) (hts X (iv n))) (del (iv n) X)))
        (nth (fbot zero) (iv n) X))

------------------------------------------------------------------------
-- tuples from functions
------------------------------------------------------------------------

tup : Nat -> (Nat -> FEl) -> FTup
tup zero    f = nil
tup (suc p) f = cons (f zero) (tup p (\ j -> f (suc j)))

tup-len : (p : Nat) (f : Nat -> FEl) -> Eq (length (tup p f)) p
tup-len zero    f = refl
tup-len (suc p) f = Eq-cong suc (tup-len p (\ j -> f (suc j)))

tup-out : (p : Nat) (f : Nat -> FEl) (j : Nat) -> Not (LeN (suc j) p)
        -> Eq (nth (fbot zero) j (tup p f)) (fbot zero)
tup-out zero    f j       nj = refl
tup-out (suc p) f zero    nj = Empty-elim (nj tt)
tup-out (suc p) f (suc j) nj = tup-out p (\ d -> f (suc d)) j nj

tup-nth : (p : Nat) (f : Nat -> FEl) (j : Nat) -> LeN (suc j) p
        -> Eq (nth (fbot zero) j (tup p f)) (f j)
tup-nth zero    f j       ()
tup-nth (suc p) f zero    lj = refl
tup-nth (suc p) f (suc j) lj = tup-nth p (\ j' -> f (suc j')) j lj
