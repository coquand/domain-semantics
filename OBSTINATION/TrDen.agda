{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrDen
--
-- WHAT IT MEANS FOR A TRACE TO DENOTE A FUNCTION, AND THE BASE CASES.
--
-- `sem T X = f X` for every `X` is NOT the right correctness statement:
-- `sem` reaches a continuation `cont c lc v` only when the walk happens
-- to stick on coordinate `c` at level `v`, so it constrains the other
-- continuations not at all -- yet `TrComp` freezes an ARBITRARY outer
-- coordinate in every argument.  So correctness has to say, structurally,
-- that each continuation denotes the FROZEN function:
--
--     Den (stop v)  f = v is f everywhere
--     Den (node ..) f = sem (node ..) X = f X for every X
--                     , and for all c , v ,
--                       Den (cont c _ v) (\ Y -> f (ins c (fcpl v) Y))
--
-- `ins c x` is the inverse of `del c`: `ins-del` says that putting the
-- numeral back where the freeze took it out returns the original tuple,
-- which is what makes the freeze clause of `sem` coherent with `Den`.
--
-- The arity strictly decreases, so `Den` is a plain structural
-- definition, and it is closed under pointwise equality of `f`
-- (`Den-ext`) -- needed because freezing a coordinate of a projection
-- gives another projection only up to the re-indexing `sd`.
--
-- This file: `ins`, its laws, `Den`, and `zerf` / `proj i` / `succ`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrDen where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; sucF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; zerf ; proj ; succ ; evalF)
open import OBSTINATION.TraceDef

------------------------------------------------------------------------
-- INSERTING A COORDINATE, THE INVERSE OF `del`
------------------------------------------------------------------------

ins : Nat -> FEl -> FTup -> FTup
ins zero    x Y           = cons x Y
ins (suc c) x nil         = cons (fbot zero) (ins c x nil)
ins (suc c) x (cons y ys) = cons y (ins c x ys)

nth-ins-eq : (c : Nat) (x : FEl) (Y : FTup)
           -> Eq (nth (fbot zero) c (ins c x Y)) x
nth-ins-eq zero    x Y           = refl
nth-ins-eq (suc c) x nil         = nth-ins-eq c x nil
nth-ins-eq (suc c) x (cons y ys) = nth-ins-eq c x ys

nth-ins-ne : (c i : Nat) -> Not (Eq i c) -> (x : FEl) (Y : FTup)
           -> Eq (nth (fbot zero) i (ins c x Y))
                 (nth (fbot zero) (sd c i) Y)
nth-ins-ne zero    zero    ne x Y           = Empty-elim (ne refl)
nth-ins-ne zero    (suc i) ne x Y           = refl
nth-ins-ne (suc c) zero    ne x nil         = refl
nth-ins-ne (suc c) zero    ne x (cons y ys) = refl
nth-ins-ne (suc c) (suc i) ne x nil         =
  nth-ins-ne c i (\ e -> ne (Eq-cong suc e)) x nil
nth-ins-ne (suc c) (suc i) ne x (cons y ys) =
  nth-ins-ne c i (\ e -> ne (Eq-cong suc e)) x ys

nth-out : (d : FEl) (i : Nat) (X : FTup) -> Not (LeN (suc i) (length X))
        -> Eq (nth d i X) d
nth-out d i       nil         ni = refl
nth-out d zero    (cons x xs) ni = Empty-elim (ni tt)
nth-out d (suc i) (cons x xs) ni = nth-out d i xs ni

ins-del : (c : Nat) (X : FTup) -> LeN (suc c) (length X)
        -> Eq (ins c (nth (fbot zero) c X) (del c X)) X
ins-del c       nil         ()
ins-del zero    (cons x xs) lc = refl
ins-del (suc c) (cons x xs) lc = Eq-cong (cons x) (ins-del c xs lc)

del-len : (c : Nat) (X : FTup) -> LeN (suc c) (length X)
        -> Eq (suc (length (del c X))) (length X)
del-len c       nil         ()
del-len zero    (cons x xs) lc = refl
del-len (suc c) (cons x xs) lc = Eq-cong suc (del-len c xs lc)

ins-len : (c : Nat) (x : FEl) (Y : FTup) -> LeN c (length Y)
        -> Eq (length (ins c x Y)) (suc (length Y))
ins-len zero    x Y           lc = refl
ins-len (suc c) x nil         ()
ins-len (suc c) x (cons y ys) lc = Eq-cong suc (ins-len c x ys lc)

------------------------------------------------------------------------
-- DENOTATION
------------------------------------------------------------------------

Den : (a : Nat) -> Tr a -> (FTup -> FEl) -> Set
Den a       (stop v)              f =
  (X : FTup) -> Eq (length X) a -> Eq v (f X)
Den (suc a) (node iv ivr ov cont) f =
  Pair ((X : FTup) -> Eq (length X) (suc a)
                   -> Eq (sem (suc a) (node iv ivr ov cont) X) (f X))
       ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
        -> Den a (cont c lc v) (\ Y -> f (ins c (fcpl v) Y)))

Den-ext : (a : Nat) (T : Tr a) (f g : FTup -> FEl)
        -> ((X : FTup) -> Eq (f X) (g X)) -> Den a T f -> Den a T g
Den-ext a       (stop v)              f g e d =
  \ X lx -> Eq-trans (d X lx) (e X)
Den-ext (suc a) (node iv ivr ov cont) f g e d =
  mkSigma (\ X lx -> Eq-trans (fst d X lx) (e X))
    (\ c lc v ->
       Den-ext a (cont c lc v)
         (\ Y -> f (ins c (fcpl v) Y)) (\ Y -> g (ins c (fcpl v) Y))
         (\ Y -> e (ins c (fcpl v) Y)) (snd d c lc v))

-- ... and it is enough to know the two functions agree on tuples OF THE
-- RIGHT LENGTH: a continuation quantifies over `Y` of length `a`, and
-- `ins c (fcpl v) Y` then has length `suc a` (`ins-len`, using `c <= a`).
Den-extL : (a : Nat) (T : Tr a) (f g : FTup -> FEl)
         -> ((X : FTup) -> Eq (length X) a -> Eq (f X) (g X))
         -> Den a T f -> Den a T g
Den-extL a       (stop v)              f g e d =
  \ X lx -> Eq-trans (d X lx) (e X lx)
Den-extL (suc a) (node iv ivr ov cont) f g e d =
  mkSigma (\ X lx -> Eq-trans (fst d X lx) (e X lx))
    (\ c lc v ->
       Den-extL a (cont c lc v)
         (\ Y -> f (ins c (fcpl v) Y)) (\ Y -> g (ins c (fcpl v) Y))
         (\ Y ly ->
            e (ins c (fcpl v) Y)
              (Eq-trans
                (ins-len c (fcpl v) Y
                  (Eq-transport (\ z -> LeN c z) (Eq-sym ly) lc))
                (Eq-cong suc ly)))
         (snd d c lc v))

------------------------------------------------------------------------
-- zerf
------------------------------------------------------------------------

zerfTr-den : (a : Nat) -> Den a (zerfTr a) (evalF zerf)
zerfTr-den a X lx = refl

------------------------------------------------------------------------
-- proj i
--
-- Freezing coordinate `i` gives the numeral; freezing any other gives
-- the projection again, at the re-indexed coordinate `sd c i`.
------------------------------------------------------------------------

projTr-den : (a i : Nat) (li : LeN (suc i) a)
           -> Den a (projTr a i li) (\ X -> nth (fbot zero) i X)
projTr-den zero    i       ()
projTr-den (suc a) i li = mkSigma main cn
  where
    main : (X : FTup) -> Eq (length X) (suc a)
         -> Eq (sem (suc a) (projTr (suc a) i li) X) (nth (fbot zero) i X)
    main X lx = projTr-sem a i li X

    cn : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
       -> Den a (projCont a i li c lc v)
              (\ Y -> nth (fbot zero) i (ins c (fcpl v) Y))
    cn c lc v = go (EqNat-dec i c) refl
      where
        go : (D : Dec (Eq i c)) -> Eq (EqNat-dec i c) D
           -> Den a (projCont a i li c lc v)
                  (\ Y -> nth (fbot zero) i (ins c (fcpl v) Y))
        go (yes ei) eD =
          Eq-transport
            (\ T -> Den a T (\ Y -> nth (fbot zero) i (ins c (fcpl v) Y)))
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD))
            (\ Y ly ->
               Eq-sym
                 (Eq-trans
                   (Eq-cong (\ z -> nth (fbot zero) z (ins c (fcpl v) Y)) ei)
                   (nth-ins-eq c (fcpl v) Y)))
        go (no ne) eD =
          Eq-transport
            (\ T -> Den a T (\ Y -> nth (fbot zero) i (ins c (fcpl v) Y)))
            (Eq-sym (Eq-cong (projPick a i li c lc v) eD))
            (Den-ext a (projTr a (sd c i) (sd-range a c i lc li ne))
              (\ Y -> nth (fbot zero) (sd c i) Y)
              (\ Y -> nth (fbot zero) i (ins c (fcpl v) Y))
              (\ Y -> Eq-sym (nth-ins-ne c i ne (fcpl v) Y))
              (projTr-den a (sd c i) (sd-range a c i lc li ne)))

------------------------------------------------------------------------
-- succ
------------------------------------------------------------------------

succTr-den : Den (suc zero) succTr (evalF succ)
succTr-den = mkSigma main cn
  where
    main : (X : FTup) -> Eq (length X) (suc zero)
         -> Eq (sem (suc zero) succTr X) (evalF succ X)
    main X lx = succTr-sem X lx

    cn : (c : Nat) (lc : LeN (suc c) (suc zero)) (v : Nat)
       -> Den zero (stop (fcpl (suc v)))
              (\ Y -> evalF succ (ins c (fcpl v) Y))
    cn zero    lc v Y ly = refl
    cn (suc c) ()  v
