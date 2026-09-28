{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Solve
--
-- Decision of Horn derivability for a level theory (Bezem–Coquand,
-- Theorem 3.2 / Corollary 3.4), by a simplified algorithm:
--
--   repeat
--     capped forward iteration from the current function g, cap
--       K = max(g) + (|V|+1)(MaxG+1)                         (LC.Iter)
--     if no variable reaches K: the result is a model, stop.
--     otherwise a GAP  (t, t+MaxG]  free of values, with t ≥ max(g),
--       separates the variables W above it (nonempty) from the rest;
--       then every atom of W is derivable (loop certificate): set W to ∞.
--   (terminates: the number of finite variables decreases)
--
-- The loop certificate: iterating only the clauses with head in W and
-- body over W ∪ ∞ from W+n (n = t+MaxG) reaches W+(n+1) (compare with the
-- capped fixpoint through its leastness), and derivations are invariant
-- under upward shifts.
------------------------------------------------------------------------

module BCDE4.LC.Solve where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn
open import BCDE4.LC.Model
open import BCDE4.LC.Iter
open import BCDE4.LC.Equiv using (ShiftP ; der-shift)

------------------------------------------------------------------------
-- Variables and the maximal gain
------------------------------------------------------------------------

varsClause : Clause -> List Nat
varsClause c = fst (head c) ∷ map fst (body c)

varsTh : LCtx -> List Nat
varsTh Th = concatMap varsClause (clausesTh Th)

head-in-vars : (Th : LCtx) (c : Clause) -> Mem c (clausesTh Th) -> Mem (fst (head c)) (varsTh Th)
head-in-vars Th c mc = mem-concatMap varsClause (clausesTh Th) mc here

body-in-vars : (Th : LCtx) (c : Clause) -> Mem c (clausesTh Th) -> (a : Atom) -> Mem a (body c) ->
  Mem (fst a) (varsTh Th)
body-in-vars Th c mc a ma = mem-concatMap varsClause (clausesTh Th) mc (there (mem-map fst (body c) ma))

-- maximal gain: head offset minus body offset, over all clauses and body atoms
maxL : List Nat -> Nat
maxL []       = zero
maxL (n ∷ ns) = max n (maxL ns)

maxL-ub : (ns : List Nat) (n : Nat) -> Mem n ns -> Le n (maxL ns)
maxL-ub (n ∷ ns) .n here      = Le-max-l n (maxL ns)
maxL-ub (m ∷ ns) n  (there h) = Le-trans n (maxL ns) (max m (maxL ns)) (maxL-ub ns n h) (Le-max-r m (maxL ns))

gainsClause : Clause -> List Nat
gainsClause c = map (\ a -> snd (head c) ∸ snd a) (body c)

MaxG : LCtx -> Nat
MaxG Th = maxL (concatMap gainsClause (clausesTh Th))

-- l ≤ k + MaxG for every clause x_i + k_i … → y + l and body atom
monus-plus : (l k : Nat) -> Le l (k + (l ∸ k))
monus-plus zero    k       = tt
monus-plus (suc l) zero    = Le-refl l
monus-plus (suc l) (suc k) = monus-plus l k

plus-mono-r : (k a b : Nat) -> Le a b -> Le (k + a) (k + b)
plus-mono-r zero    a b p = p
plus-mono-r (suc k) a b p = plus-mono-r k a b p

gain-bound : (Th : LCtx) (c : Clause) -> Mem c (clausesTh Th) -> (a : Atom) -> Mem a (body c) ->
  Le (snd (head c)) (snd a + MaxG Th)
gain-bound Th c mc a ma =
  Le-trans (snd (head c)) (snd a + (snd (head c) ∸ snd a)) (snd a + MaxG Th)
    (monus-plus (snd (head c)) (snd a))
    (plus-mono-r (snd a) _ _
      (maxL-ub (concatMap gainsClause (clausesTh Th)) _
        (mem-concatMap gainsClause (clausesTh Th) mc
          (mem-map (\ b -> snd (head c) ∸ snd b) (body c) ma))))

------------------------------------------------------------------------
-- The start function of a list of hypotheses
------------------------------------------------------------------------

joinV : Val -> Val -> Val
joinV none    w       = w
joinV (fin j) none    = fin j
joinV (fin j) (fin i) = fin (max j i)
joinV (fin j) inf     = inf
joinV inf     w       = inf

InV-join-l : (j : Nat) (v w : Val) -> InV j v -> InV j (joinV v w)
InV-join-l j none    w       ()
InV-join-l j (fin a) none    p = p
InV-join-l j (fin a) (fin b) p = Le-trans j a (max a b) p (Le-max-l a b)
InV-join-l j (fin a) inf     p = tt
InV-join-l j inf     w       p = tt

InV-join-r : (j : Nat) (v w : Val) -> InV j w -> InV j (joinV v w)
InV-join-r j none    w       p = p
InV-join-r j (fin a) none    ()
InV-join-r j (fin a) (fin b) p = Le-trans j b (max a b) p (Le-max-r a b)
InV-join-r j (fin a) inf     p = tt
InV-join-r j inf     w       p = tt

InV-join-split : (j a : Nat) (w : Val) -> InV j (joinV (fin a) w) -> Either (Le j a) (InV j w)
InV-join-split j a none    p = inl p
InV-join-split j a (fin b) p = go (le? j a)
  where
    go : Either (Le j a) (Le (suc a) j) -> Either (Le j a) (Le j b)
    go (inl q) = inl q
    go (inr q) = inr (max-split j a b q p)
      where
        max-split : (j a b : Nat) -> Le (suc a) j -> Le j (max a b) -> Le j b
        max-split j       zero    b       q p = p
        max-split zero    (suc a) b       () p
        max-split (suc j) (suc a) zero    q p = absurd (Le-antisym-suc a (Le-trans (suc a) j a q p))
        max-split (suc j) (suc a) (suc b) q p = max-split j a b q p
InV-join-split j a inf     p = inr tt

startStep : (a : Atom) -> Val -> (x : Nat) -> Either (Eq (fst a) x) (Eq (fst a) x -> Empty) -> Val
startStep a r x (inl e) = joinV (fin (snd a)) r
startStep a r x (inr n) = r

startOf : List Atom -> Fn
startOf []       x = none
startOf (a ∷ as) x = startStep a (startOf as x) x (eqN? (fst a) x)

-- every atom of the start function is below a hypothesis
startOf-der : {Th : LCtx} (A : List Atom) -> DerAll Th (InL A) (startOf A)
startOf-der {Th} A b sb = go A (\ a m -> m) sb
  where
    go : (as : List Atom) -> ((a : Atom) -> Mem a as -> Mem a A) ->
      InV (snd b) (startOf as (fst b)) -> Der Th (InL A) b
    go []       sub ()
    go (a ∷ as) sub p = sel (eqN? (fst a) (fst b)) p
      where
        sel : (d : Either (Eq (fst a) (fst b)) (Eq (fst a) (fst b) -> Empty)) ->
          InV (snd b) (startStep a (startOf as (fst b)) (fst b) d) -> Der Th (InL A) b
        sel (inl e) q = sel2 (InV-join-split (snd b) (snd a) (startOf as (fst b)) q)
          where
            sel2 : Either (Le (snd b) (snd a)) (InV (snd b) (startOf as (fst b))) -> Der Th (InL A) b
            sel2 (inl le) = Eq-transport (\ x -> Der Th (InL A) (mkSigma x (snd b))) e
                              (der-down (fst a) (snd a) (snd b) le (d-hyp (sub a here)))
            sel2 (inr q') = go as (\ c m -> sub c (there m)) q'
        sel (inr n) q = go as (\ c m -> sub c (there m)) q

-- the hypotheses hold in the start function
startOf-sat : (A : List Atom) (a : Atom) -> Mem a A -> SatA (startOf A) a
startOf-sat (a ∷ as) .a here = sel (eqN? (fst a) (fst a))
  where
    sel : (d : Either (Eq (fst a) (fst a)) (Eq (fst a) (fst a) -> Empty)) ->
      InV (snd a) (startStep a (startOf as (fst a)) (fst a) d)
    sel (inl e) = InV-join-l (snd a) (fin (snd a)) (startOf as (fst a)) (Le-refl (snd a))
    sel (inr n) = absurd (n refl)
startOf-sat (b ∷ as) a (there m) = sel (eqN? (fst b) (fst a))
  where
    sel : (d : Either (Eq (fst b) (fst a)) (Eq (fst b) (fst a) -> Empty)) ->
      InV (snd a) (startStep b (startOf as (fst a)) (fst a) d)
    sel (inl e) = InV-join-r (snd a) (fin (snd b)) (startOf as (fst a)) (startOf-sat as a m)
    sel (inr n) = startOf-sat as a m
