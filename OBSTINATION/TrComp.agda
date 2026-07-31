{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrComp
--
-- THE TRACE OF A COMPOSITION,  f (X) = g (h_0 X , ... , h_{p-1} X).
--
-- (`TraceDef`'s notion of trace, NOT David's `Trace`/`TraceComp`.)
--
-- THE STATE IS THE LEVELS THE COMPOSITE HAS OBTAINED, NOT A PER-ARGUMENT
-- STEP COUNTER.  Driving the arguments one step at a time is wrong: the
-- arguments read the SAME `X`, so when two of them want the same level of
-- the same coordinate, the second gets it for free -- stepping them
-- charges it twice and the composite sticks a level too early.
-- (`TrCompFail` had `f x = g (x , x)` answering `S^1 bot` at `S^2 bot`.)
--
-- So the state is just
--
--     L 0 = 0~ ,   L (k+1) = bump (ivf k) (L k)
--
-- the composite's own level function, and each argument is REPLAYED
-- AGAINST IT, as far as those levels allow and no further:
--
--     dep  k i = nOfOf (Ths i) (L k)             -- argument i's replay depth
--     vals k   = ( ovOf (Ths i) (dep k i) )_i    -- what `g` sees
--     ovf  k   = sem     p Tg (vals k)
--     sel  k   = blockOn p Tg (vals k)
--     ivf  k   = ivOf (Ths (sel k)) (dep k (sel k))
--
-- Sharing is now automatic: raising `L` advances EVERY argument that was
-- waiting for that level.  And the demanded cell is always a new one --
-- the selected argument is stuck at coordinate `ivf k`, so by
-- `stuck-level` it needs exactly level `L k (ivf k)`, the first one not
-- yet obtained.
--
-- An argument becoming TOTAL is not a special case: `sem`/`blockOn`
-- already freeze `g`'s coordinate and carry on inside `Tg`.  The
-- composite's own continuation, for a total OUTER coordinate, freezes
-- that coordinate in every argument:
--
--     cont c lc v = compTr p Tg a (\ i -> contOf (Ths i) c lc v)
--
-- so the construction is a plain recursion on the outer arity `a`, with
-- no halting threshold to search for and no appeal to MP1.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrComp where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (bump ; nOf)
open import OBSTINATION.TraceDef

------------------------------------------------------------------------
-- the selected argument
------------------------------------------------------------------------

orC : Or Top Nat -> Nat
orC (inl tt) = zero
orC (inr c)  = c

------------------------------------------------------------------------
-- THE WALK
------------------------------------------------------------------------

module W (p : Nat) (Tg : Tr p) (a : Nat) (Ths : Nat -> Tr (suc a)) where

  mutual
    -- the levels the composite has obtained
    L : Nat -> Nat -> Nat
    L zero    c = zero
    L (suc k) c = bump (ivf k) (L k) c

    -- each argument replayed against exactly those levels
    dep : Nat -> Nat -> Nat
    dep k i = nOfOf (suc a) (Ths i) (L k)

    vals : Nat -> FTup
    vals k = tup p (\ i -> ovOf (Ths i) (dep k i))

    sel : Nat -> Or Top Nat
    sel k = blockOn p Tg (vals k)

    selC : Nat -> Nat
    selC k = orC (sel k)

    ivf : Nat -> Nat
    ivf k = ivOf (Ths (selC k)) (dep k (selC k))

  ivfr : (k : Nat) -> LeN (suc (ivf k)) (suc a)
  ivfr k = ivrOf (Ths (selC k)) (dep k (selC k))

  ovf : Nat -> FEl
  ovf k = sem p Tg (vals k)

------------------------------------------------------------------------
-- THE COMPOSITE TRACE
------------------------------------------------------------------------

compTr : (p : Nat) -> Tr p -> (a : Nat) -> (Nat -> Tr a) -> Tr a
compTr p Tg zero    Ths =
  stop (sem p Tg (tup p (\ i -> ovOf (Ths i) zero)))
compTr p Tg (suc a) Ths =
  node (W.ivf p Tg a Ths) (W.ivfr p Tg a Ths) (W.ovf p Tg a Ths)
    (\ c lc v -> compTr p Tg a (\ i -> contOf (Ths i) c lc v))
