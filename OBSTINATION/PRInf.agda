{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PRInf
--
-- THE VALUE OF A PR TERM AT THE ALL-INFINITE POINT IS COMPUTABLE.
--
--     prVal     : (q : PR) (n : Nat) -> Wf q n -> D
--     prVal-lub : prVal q n wf IS the least upper bound of the chain
--                 evalF q (S^m(bot), ..., S^m(bot))
--
-- This is page 2 of min1.pdf ("on obtient directement la valeur de
-- f(A)"), for the all-infinite point: `Property.uoValue` reads a value
-- off the ultimate-obstination property, `Prop1.prop1` supplies that
-- property for every PR term, and this file proves that what comes out
-- is the Scott-continuous extension -- so it is not merely an element of
-- `D` but THE value, and it is produced by a total function.
--
-- Why the three cases land where they do at `A = (S^w(bot), ..., )`:
--
--   * Case 1 -- `f` is `S^m(0)` above a finite `A0`.  `A0` is below the
--     all-infinite point, so every coordinate of it is incomplete
--     (`cpl k` is NOT below `inf`: they are incomparable maximal-ish
--     elements), hence `A0 <= (S^M bot, ..., S^M bot)` for some `M`
--     (`below-inf-bot`), and the chain is `S^m(0)` from `M` on.
--
--   * Case 2 -- pinned at a coordinate whose value is incomplete and
--     FINITE.  IMPOSSIBLE here: every coordinate of the point is `inf`.
--     That is `IncompleteFinite inf = Empty`, and it is the only place
--     where being at the all-infinite point is used essentially.
--
--   * Case 3 -- at an infinite coordinate, with `phi`.  The chain is
--     `S^(phi m)(bot)` from `max k M` on, and `PhiOK` decides the lub:
--     `phi` constant gives `S^(phi k)(bot)`, `phi` strictly increasing
--     gives `S^w(bot)` -- for which one has to know that `phi` is then
--     UNBOUNDED (`sinc-up`) and that no member of the chain is complete.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PRInf where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR using (PR ; evalF)
open import OBSTINATION.Property using
  (UO ; uo1 ; uo2 ; uo3 ; uoValue ; getF ; Below ;
   IncompleteFinite ; ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.Prop1 using (Wf ; prop1)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.PrecInfCoord using (LeFTup-del)

------------------------------------------------------------------------
-- SMALL PLUMBING
--
-- Inlined rather than imported so that this file depends only on the
-- Proposition-1 cone: the value at the all-infinite point does NOT need
-- the trace.
------------------------------------------------------------------------

LeN-suc-not : (a : Nat) -> LeN (suc a) a -> Empty
LeN-suc-not zero    ()
LeN-suc-not (suc a) le = LeN-suc-not a le

embedTup-len : (X : FTup) -> Eq (length (embedTup X)) (length X)
embedTup-len nil         = refl
embedTup-len (cons x xs) = Eq-cong suc (embedTup-len xs)

LeTup-len : (A B : Tup) -> LeTup A B -> Eq (length A) (length B)
LeTup-len nil         nil         le = refl
LeTup-len nil         (cons _ _)  ()
LeTup-len (cons _ _)  nil         ()
LeTup-len (cons x xs) (cons y ys) le = Eq-cong suc (LeTup-len xs ys (snd le))

------------------------------------------------------------------------
-- THE ALL-INFINITE POINT
------------------------------------------------------------------------

infTup : Nat -> Tup
infTup zero    = nil
infTup (suc n) = cons inf (infTup n)

infTup-len : (n : Nat) -> Eq (length (infTup n)) n
infTup-len zero    = refl
infTup-len (suc n) = Eq-cong suc (infTup-len n)

infTup-get : (i n : Nat) -> LeN (suc i) n -> Eq (get i (infTup n)) inf
infTup-get i       zero    ()
infTup-get zero    (suc n) li = refl
infTup-get (suc i) (suc n) li = infTup-get i n li

infTup-out : (i n : Nat) -> Not (LeN (suc i) n) -> Eq (get i (infTup n)) botD
infTup-out i       zero    ni = refl
infTup-out zero    (suc n) ni = Empty-elim (ni tt)
infTup-out (suc i) (suc n) ni = infTup-out i n ni

-- a coordinate that IS infinite is in range
inf-range : (i n : Nat) -> Eq (get i (infTup n)) inf -> LeN (suc i) n
inf-range i n e = route (LeN-dec (suc i) n)
  where
    bad : Not (Eq botD inf)
    bad ()

    route : Dec (LeN (suc i) n) -> LeN (suc i) n
    route (yes l)  = l
    route (no  nl) =
      Empty-elim (bad (Eq-trans (Eq-sym (infTup-out i n nl)) e))

------------------------------------------------------------------------
-- THE CHAIN OF FINITE APPROXIMANTS
------------------------------------------------------------------------

botF : Nat -> Nat -> FTup
botF zero    m = nil
botF (suc n) m = cons (fbot m) (botF n m)

botF-len : (n m : Nat) -> Eq (length (botF n m)) n
botF-len zero    m = refl
botF-len (suc n) m = Eq-cong suc (botF-len n m)

botF-get : (i n m : Nat) -> LeN (suc i) n -> Eq (getF i (botF n m)) (fbot m)
botF-get i       zero    m ()
botF-get zero    (suc n) m li = refl
botF-get (suc i) (suc n) m li = botF-get i n m li

botF-mono : (n m m' : Nat) -> LeN m m' -> LeFTup (botF n m) (botF n m')
botF-mono zero    m m' l = tt
botF-mono (suc n) m m' l = mkSigma l (botF-mono n m m' l)

------------------------------------------------------------------------
-- A FINITE POINT BELOW THE ALL-INFINITE ONE IS BELOW SOME `botF n M`
--
-- The content is that `cpl k` is NOT below `inf`: a coordinate that has
-- already produced a `0` cannot approximate `S^w(bot)`.  So every
-- coordinate of `A0` is an `fbot`, and the max of their heights does it.
------------------------------------------------------------------------

below-inf-el : (x : FEl) -> LeD (embed x) inf -> Sigma Nat (\ k -> Eq x (fbot k))
below-inf-el (fbot k) le = mkSigma k refl
below-inf-el (fcpl k) ()

below-inf-bot : (A0 : FTup) (n : Nat) -> Below A0 (infTup n)
              -> Sigma Nat (\ M -> (m : Nat) -> LeN M m -> LeFTup A0 (botF n m))
below-inf-bot nil         zero    bel = mkSigma zero (\ m lm -> tt)
below-inf-bot nil         (suc n) ()
below-inf-bot (cons x xs) zero    ()
below-inf-bot (cons x xs) (suc n) bel =
  route (below-inf-el x (fst bel)) (below-inf-bot xs n (snd bel))
  where
    Res : Set
    Res =
      Sigma Nat (\ M -> (m : Nat) -> LeN M m
        -> LeFTup (cons x xs) (botF (suc n) m))

    route : Sigma Nat (\ k -> Eq x (fbot k))
          -> Sigma Nat (\ M -> (m : Nat) -> LeN M m -> LeFTup xs (botF n m))
          -> Res
    route (mkSigma k ek) (mkSigma M con) = mkSigma (maxN k M) go
      where
        go : (m : Nat) -> LeN (maxN k M) m
           -> LeFTup (cons x xs) (botF (suc n) m)
        go m lm =
          mkSigma
            (Eq-transport (\ z -> LeD (embed z) (bot m)) (Eq-sym ek)
              (LeN-trans {k} {maxN k M} {m} (maxN-le-l k M) lm))
            (con m (LeN-trans {M} {maxN k M} {m} (maxN-le-r k M) lm))

below-len : (A0 : FTup) (n : Nat) -> Below A0 (infTup n) -> Eq (length A0) n
below-len A0 n bel =
  Eq-trans (Eq-sym (embedTup-len A0))
    (Eq-trans (LeTup-len (embedTup A0) (infTup n) bel) (infTup-len n))

------------------------------------------------------------------------
-- A STRICTLY INCREASING `phi` IS UNBOUNDED
------------------------------------------------------------------------

addN : Nat -> Nat -> Nat
addN zero    b = b
addN (suc a) b = suc (addN a b)

addN-ge-r : (a b : Nat) -> LeN b (addN a b)
addN-ge-r zero    b = LeN-refl b
addN-ge-r (suc a) b =
  LeN-trans {b} {addN a b} {suc (addN a b)} (addN-ge-r a b)
    (LeN-suc (addN a b))

addN-ge-l : (a b : Nat) -> LeN a (addN a b)
addN-ge-l zero    b = tt
addN-ge-l (suc a) b = addN-ge-l a b

sinc-up : (k : Nat) (phi : Nat -> Nat) -> StrictIncFrom k phi
        -> (t : Nat) -> LeN (addN t (phi k)) (phi (addN t k))
sinc-up k phi si zero    = LeN-refl (phi k)
sinc-up k phi si (suc t) =
  LeN-trans {suc (addN t (phi k))} {suc (phi (addN t k))}
    {phi (suc (addN t k))}
    (sinc-up k phi si t) (si (addN t k) (addN-ge-r t k))

------------------------------------------------------------------------
-- THE CHAIN, AND WHAT IT MEANS TO BE ITS LUB
------------------------------------------------------------------------

Chain : PR -> Nat -> Nat -> FEl
Chain q n m = evalF q (botF n m)

chain-mono : (q : PR) (n m m' : Nat) -> LeN m m'
           -> LeD (embed (Chain q n m)) (embed (Chain q n m'))
chain-mono q n m m' l = evalF-mono q (botF-mono n m m' l)

IsLub : PR -> Nat -> D -> Set
IsLub q n d =
  Pair ((m : Nat) -> LeD (embed (Chain q n m)) d)
       ((e : D) -> ((m : Nat) -> LeD (embed (Chain q n m)) e) -> LeD d e)

------------------------------------------------------------------------
-- CASE 3, THE TWO SUB-CASES
------------------------------------------------------------------------

c3hit : (q : PR) (n : Nat) (A0 : FTup) (i k : Nat) (phi : Nat -> Nat)
      -> Below A0 (infTup n)
      -> Eq (get i (infTup n)) inf
      -> ((X : FTup) (m : Nat) -> Eq (length X) (length A0) -> LeN k m
          -> Eq (getF i X) (fbot m) -> LeFTup (del i A0) (del i X)
          -> Eq (evalF q X) (fbot (phi m)))
      -> Sigma Nat (\ K -> Pair (LeN k K)
           ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m))))
c3hit q n A0 i k phi bel einf hyp = route (below-inf-bot A0 n bel)
  where
    lin : LeN (suc i) n
    lin = inf-range i n einf

    lenA0 : Eq (length A0) n
    lenA0 = below-len A0 n bel

    route : Sigma Nat (\ M -> (m : Nat) -> LeN M m -> LeFTup A0 (botF n m))
          -> Sigma Nat (\ K -> Pair (LeN k K)
               ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m))))
    route (mkSigma M con) = mkSigma (maxN k M) (mkSigma (maxN-le-l k M) go)
      where
        go : (m : Nat) -> LeN (maxN k M) m -> Eq (Chain q n m) (fbot (phi m))
        go m lm =
          hyp (botF n m) m
            (Eq-trans (botF-len n m) (Eq-sym lenA0))
            (LeN-trans {k} {maxN k M} {m} (maxN-le-l k M) lm)
            (botF-get i n m lin)
            (LeFTup-del i
              (con m (LeN-trans {M} {maxN k M} {m} (maxN-le-r k M) lm)))

case3-const : (q : PR) (n k : Nat) (phi : Nat -> Nat) -> ConstFrom k phi
            -> (K : Nat) -> LeN k K
            -> ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m)))
            -> IsLub q n (bot (phi k))
case3-const q n k phi cf K lkK hit = mkSigma ub lb
  where
    hitc : (m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi k))
    hitc m lm =
      Eq-trans (hit m lm)
        (Eq-cong fbot (cf m (LeN-trans {k} {K} {m} lkK lm)))

    ub : (m : Nat) -> LeD (embed (Chain q n m)) (bot (phi k))
    ub m =
      Eq-transport (\ z -> LeD (embed (Chain q n m)) (embed z))
        (hitc (maxN K m) (maxN-le-l K m))
        (chain-mono q n m (maxN K m) (maxN-le-r K m))

    lb : (e : D) -> ((m : Nat) -> LeD (embed (Chain q n m)) e)
       -> LeD (bot (phi k)) e
    lb e he =
      Eq-transport (\ z -> LeD (embed z) e) (hitc K (LeN-refl K)) (he K)

case3-sinc : (q : PR) (n k : Nat) (phi : Nat -> Nat) -> StrictIncFrom k phi
           -> (K : Nat) -> LeN k K
           -> ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m)))
           -> IsLub q n inf
case3-sinc q n k phi si K lkK hit = mkSigma ub lb
  where
    ----------------------------------------------------------------
    -- no member of the chain is complete, so all of them are below
    -- `S^w(bot)`
    ----------------------------------------------------------------
    ub : (m : Nat) -> LeD (embed (Chain q n m)) inf
    ub m = shp (Chain q n m) refl
      where
        up : LeD (embed (Chain q n m)) (bot (phi (maxN K m)))
        up =
          Eq-transport (\ z -> LeD (embed (Chain q n m)) (embed z))
            (hit (maxN K m) (maxN-le-l K m))
            (chain-mono q n m (maxN K m) (maxN-le-r K m))

        shp : (y : FEl) -> Eq (Chain q n m) y -> LeD (embed y) inf
        shp (fbot j) e = tt
        shp (fcpl j) e =
          Empty-elim
            (Eq-transport (\ z -> LeD (embed z) (bot (phi (maxN K m)))) e up)

    ----------------------------------------------------------------
    -- and their heights are unbounded, so nothing finite bounds them
    ----------------------------------------------------------------
    capped : (j : Nat) -> ((m : Nat) -> LeN K m -> LeN (phi m) j) -> Empty
    capped j cap =
      LeN-suc-not j (LeN-trans {suc j} {phi m0} {j} big (cap m0 mK))
      where
        t0 : Nat
        t0 = suc (addN j K)

        m0 : Nat
        m0 = addN t0 k

        mK : LeN K m0
        mK =
          LeN-trans {K} {t0} {m0}
            (LeN-trans {K} {addN j K} {t0} (addN-ge-r j K)
              (LeN-suc (addN j K)))
            (addN-ge-l t0 k)

        sj : LeN (suc j) (addN t0 (phi k))
        sj =
          LeN-trans {suc j} {t0} {addN t0 (phi k)}
            (addN-ge-l j K) (addN-ge-l t0 (phi k))

        big : LeN (suc j) (phi m0)
        big =
          LeN-trans {suc j} {addN t0 (phi k)} {phi m0} sj
            (sinc-up k phi si t0)

    lb : (e : D) -> ((m : Nat) -> LeD (embed (Chain q n m)) e) -> LeD inf e
    lb (bot j) he =
      Empty-elim
        (capped j
          (\ m lm ->
             Eq-transport (\ z -> LeD (embed z) (bot j)) (hit m lm) (he m)))
    lb (cpl j) he =
      Empty-elim
        (capped j
          (\ m lm ->
             Eq-transport (\ z -> LeD (embed z) (cpl j)) (hit m lm) (he m)))
    lb inf     he = tt

------------------------------------------------------------------------
-- WHAT `uoValue` COMPUTES AT THE ALL-INFINITE POINT IS THE LUB
------------------------------------------------------------------------

valOK : (q : PR) (n : Nat) (u : UO (evalF q) (infTup n)) -> IsLub q n (uoValue u)
------------------------------------------------------------------------
-- Case 1: eventually the numeral `m0`
------------------------------------------------------------------------
valOK q n (uo1 (mkSigma A0 (mkSigma bel (mkSigma m0 hyp)))) =
  route (below-inf-bot A0 n bel)
  where
    route : Sigma Nat (\ M -> (m : Nat) -> LeN M m -> LeFTup A0 (botF n m))
          -> IsLub q n (cpl m0)
    route (mkSigma M con) = mkSigma ub lb
      where
        hit : (m : Nat) -> LeN M m -> Eq (Chain q n m) (fcpl m0)
        hit m lm = hyp (botF n m) (con m lm)

        ub : (m : Nat) -> LeD (embed (Chain q n m)) (cpl m0)
        ub m =
          Eq-transport (\ z -> LeD (embed (Chain q n m)) (embed z))
            (hit (maxN M m) (maxN-le-l M m))
            (chain-mono q n m (maxN M m) (maxN-le-r M m))

        lb : (e : D) -> ((m : Nat) -> LeD (embed (Chain q n m)) e)
           -> LeD (cpl m0) e
        lb e he =
          Eq-transport (\ z -> LeD (embed z) e) (hit M (LeN-refl M)) (he M)
------------------------------------------------------------------------
-- Case 2: IMPOSSIBLE -- every coordinate of the point is infinite
------------------------------------------------------------------------
valOK q n
  (uo2 (mkSigma A0 (mkSigma bel (mkSigma m0 (mkSigma i (mkSigma li
         (mkSigma icf (mkSigma eqA hyp)))))))) =
  Empty-elim (Eq-transport (\ z -> IncompleteFinite z) (infTup-get i n lin) icf)
  where
    lin : LeN (suc i) n
    lin = Eq-transport (\ z -> LeN (suc i) z) (below-len A0 n bel) li
------------------------------------------------------------------------
-- Case 3: the infinite coordinate, and `PhiOK` decides the lub
------------------------------------------------------------------------
valOK q n
  (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf (mkSigma k
         (mkSigma eA0 (mkSigma phi (mkSigma (inl cf) hyp)))))))))=
  route (c3hit q n A0 i k phi bel einf hyp)
  where
    route : Sigma Nat (\ K -> Pair (LeN k K)
              ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m))))
          -> IsLub q n (bot (phi k))
    route (mkSigma K (mkSigma lkK hit)) =
      case3-const q n k phi cf K lkK hit
valOK q n
  (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf (mkSigma k
         (mkSigma eA0 (mkSigma phi (mkSigma (inr si) hyp)))))))))=
  route (c3hit q n A0 i k phi bel einf hyp)
  where
    route : Sigma Nat (\ K -> Pair (LeN k K)
              ((m : Nat) -> LeN K m -> Eq (Chain q n m) (fbot (phi m))))
          -> IsLub q n inf
    route (mkSigma K (mkSigma lkK hit)) = case3-sinc q n k phi si K lkK hit

------------------------------------------------------------------------
-- THE THEOREM
--
--   f (S^w(bot), ..., S^w(bot))  is COMPUTABLE, for every PR term `f`:
--   `prVal` is a total function producing an explicit element of `D`,
--   and it IS the value -- the least upper bound of the chain.
------------------------------------------------------------------------

prUO : (q : PR) (n : Nat) -> Wf q n -> UO (evalF q) (infTup n)
prUO q n wf =
  prop1 q (infTup n)
    (Eq-transport (\ z -> Wf q z) (Eq-sym (infTup-len n)) wf)

prVal : (q : PR) (n : Nat) -> Wf q n -> D
prVal q n wf = uoValue (prUO q n wf)

prVal-lub : (q : PR) (n : Nat) (wf : Wf q n) -> IsLub q n (prVal q n wf)
prVal-lub q n wf = valOK q n (prUO q n wf)

-- the two halves, spelled out
prVal-ub : (q : PR) (n : Nat) (wf : Wf q n) (m : Nat)
         -> LeD (embed (evalF q (botF n m))) (prVal q n wf)
prVal-ub q n wf = fst (prVal-lub q n wf)

prVal-least : (q : PR) (n : Nat) (wf : Wf q n) (e : D)
            -> ((m : Nat) -> LeD (embed (evalF q (botF n m))) e)
            -> LeD (prVal q n wf) e
prVal-least q n wf = snd (prVal-lub q n wf)
