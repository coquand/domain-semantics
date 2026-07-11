{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBaseConst
--
-- Base constancy for primitive recursion at the infinite first argument
-- (min1.pdf p.3, sub-case 1 of the second principal case).  Suppose h is
-- governed at its recursion-result coordinate (coordinate 1) by a numeric
-- witness phi on the region  coord0 >= S^{n0}(bot), coord1 >= S^{k0}(bot),
-- tail >= Y0  (the "hgerm"), and let  S^N(bot) = f(S^{n0}(bot), Y0)  with
-- k0 <= N.  Then, for every  n <= n0  and every finite  X >= Y0,
--
--        f(S^n(bot), X)  =  f(S^n(bot), Y0).
--
-- That is, the recursion value is CONSTANT in the tail, for first
-- arguments of height up to n0.  The proof is min1.pdf's direct Berry
-- stability computation:
--
--   h(S^n b, S^k b, Y0) = h(S^n b, S^k b, X) /\ h(S^n b, S^N b, Y0)   (stab)
--                       = h(S^n b, S^k b, X) /\ h(S^n b, S^N b, X)     (dagger)
--                       = h(S^n b, S^k b, X)                           (meet-le)
--
-- with the anchor `dagger` (the k = N case) obtained from stability, the
-- germ at n0, and monotonicity.  No cross-meet exclusion is needed.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBaseConst where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Meet
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Stability using (stable)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono ; precFun)

------------------------------------------------------------------------
-- Small lattice helpers
------------------------------------------------------------------------

minN-comm : (m n : Nat) -> Eq (minN m n) (minN n m)
minN-comm zero    n       = Eq-sym (minN-zero-r n)
minN-comm (suc m) zero    = refl
minN-comm (suc m) (suc n) = Eq-cong suc (minN-comm m n)

-- meet absorbs the smaller (right) element:  b <= a  ==>  a /\ b = b
meetF-le-r : {a b : FEl} -> LeF b a -> Eq (meetF a b) b
meetF-le-r {fbot j} {fbot k} le = Eq-cong fbot (Eq-trans (minN-comm j k) (minN-l {k} {j} le))
meetF-le-r {fbot j} {fcpl k} ()
meetF-le-r {fcpl j} {fbot k} le = refl
meetF-le-r {fcpl j} {fcpl k} le =
  Eq-cong fcpl (Eq-trans (Eq-cong (\ z -> minN z k) (Eq-sym le)) (minN-l {k} {k} (LeN-refl k)))

-- meet absorbs the smaller (left) element:  a <= b  ==>  a /\ b = a
meetF-le-l : {a b : FEl} -> LeF a b -> Eq (meetF a b) a
meetF-le-l {fbot j} {fbot k} le = Eq-cong fbot (minN-l {j} {k} le)
meetF-le-l {fbot j} {fcpl k} le = refl
meetF-le-l {fcpl j} {fbot k} ()
meetF-le-l {fcpl j} {fcpl k} le =
  Eq-cong fcpl (Eq-trans (Eq-cong (\ z -> minN j z) (Eq-sym le)) (minN-l {j} {j} (LeN-refl j)))

meetT-le-r : {A B : FTup} -> LeFTup B A -> Eq (meetT A B) B
meetT-le-r {nil}      {nil}      le = refl
meetT-le-r {nil}      {cons _ _} ()
meetT-le-r {cons a as} {nil}     le = refl
meetT-le-r {cons a as} {cons b bs} le =
  cons-eq (meetF-le-r {a} {b} (fst le)) (meetT-le-r {as} {bs} (snd le))

-- from an order to boundedness (common upper bound = the larger element)
Bnd-ge : {a b : FEl} -> LeF b a -> Bnd a b
Bnd-ge {a} {b} le = bnd-from-ub {a} {b} {a} (LeF-refl a) le

BndT-ge : {A B : FTup} -> LeFTup B A -> BndT A B
BndT-ge {nil}       {nil}      le = tt
BndT-ge {nil}       {cons _ _} ()
BndT-ge {cons a as} {nil}      ()
BndT-ge {cons a as} {cons b bs} le = mkSigma (Bnd-ge {a} {b} (fst le)) (BndT-ge {as} {bs} (snd le))

-- an element below S^N(bot) is itself some S^v(bot) with v <= N
below-fbot : {x : FEl} {N : Nat} -> LeF x (fbot N) ->
  Sigma Nat (\ v -> Pair (Eq x (fbot v)) (LeN v N))
below-fbot {fbot v} {N} le = mkSigma v (mkSigma refl le)
below-fbot {fcpl v} {N} ()

------------------------------------------------------------------------
-- The base-constancy argument, parameterised by the coordinate-1 germ.
------------------------------------------------------------------------

-- Minimal germ: base constancy needs h's value ONLY at coord0 = n0,
-- coord1 = N (a fixed incomplete value fbot pN), on the tail region.
-- (Both the Case-3-at-coord-1 sub-case and the Case-2-at-coord-1 constant
-- sub-case of the dispatch discharge this.)
module _ (rd : RecData) (n0 N pN : Nat) (Y0 : FTup)
  (Neq : Eq (PF (RecData.G rd) (RecData.H rd) (cons (fbot n0) Y0)) (fbot N))
  (germN0 : (X : FTup) -> LeFTup Y0 X ->
     Eq (RecData.H rd (cons (fbot n0) (cons (fbot N) X))) (fbot pN))
  where
  open RecData rd

  ----------------------------------------------------------------------
  -- Anchor (min1.pdf: the k = N equality):
  --   h(S^n b, S^N b, Y0) = h(S^n b, S^N b, X)   for n <= n0, X >= Y0.
  ----------------------------------------------------------------------

  dagger : (n : Nat) (X : FTup) -> LeN n n0 -> LeFTup Y0 X ->
    Eq (H (cons (fbot n) (cons (fbot N) Y0)))
       (H (cons (fbot n) (cons (fbot N) X)))
  dagger n X ln leX =
    Eq-trans (Eq-sym (Eq-cong (H) meqA))
      (Eq-trans (stableH {T} {S} bndA)
        (Eq-trans (Eq-cong (\ z -> meetF (H T) z) hS-eq)
                  (meetF-le-l {H T} {fbot pN} hT-le)))
    where
      T = cons (fbot n)  (cons (fbot N) X)
      S = cons (fbot n0) (cons (fbot N) Y0)
      meqA : Eq (meetT T S) (cons (fbot n) (cons (fbot N) Y0))
      meqA = cons-eq (Eq-cong fbot (minN-l {n} {n0} ln))
               (cons-eq (Eq-cong fbot (minN-l {N} {N} (LeN-refl N))) (meetT-le-r {X} {Y0} leX))
      bndA : BndT T S
      bndA = mkSigma tt (mkSigma tt (BndT-ge {X} {Y0} leX))
      hS-eq : Eq (H S) (fbot pN)
      hS-eq = germN0 Y0 (LeFTup-refl Y0)
      hT-le : LeF (H T) (fbot pN)
      hT-le = Eq-transport (\ z -> LeF (H T) z) (germN0 X leX)
                (monoH {T} {cons (fbot n0) (cons (fbot N) X)}
                  (mkSigma ln (mkSigma (LeF-refl (fbot N)) (LeFTup-refl X))))

  ----------------------------------------------------------------------
  -- Tail-independence of h at coordinate 1 = S^v(bot), v <= N.
  ----------------------------------------------------------------------

  h-indep : (n v : Nat) (X : FTup) -> LeN n n0 -> LeN v N -> LeFTup Y0 X ->
    Eq (H (cons (fbot n) (cons (fbot v) X)))
       (H (cons (fbot n) (cons (fbot v) Y0)))
  h-indep n v X ln lv leX =
    Eq-sym
      (Eq-trans (Eq-sym (Eq-cong (H) meqB))
        (Eq-trans (stableH {U} {V} bndB)
          (Eq-trans (Eq-cong (\ z -> meetF (H U) z) (dagger n X ln leX))
                    (meetF-le-l {H U} {H W} hUW-le))))
    where
      U = cons (fbot n) (cons (fbot v) X)
      V = cons (fbot n) (cons (fbot N) Y0)
      W = cons (fbot n) (cons (fbot N) X)
      meqB : Eq (meetT U V) (cons (fbot n) (cons (fbot v) Y0))
      meqB = cons-eq (Eq-cong fbot (minN-l {n} {n} (LeN-refl n)))
               (cons-eq (Eq-cong fbot (minN-l {v} {N} lv)) (meetT-le-r {X} {Y0} leX))
      bndB : BndT U V
      bndB = mkSigma tt (mkSigma tt (BndT-ge {X} {Y0} leX))
      hUW-le : LeF (H U) (H W)
      hUW-le = monoH {U} {W}
                 (mkSigma (LeF-refl (fbot n)) (mkSigma lv (LeFTup-refl X)))

  ----------------------------------------------------------------------
  -- Base constancy:  f(S^n b, X) = f(S^n b, Y0)  for n <= n0, X >= Y0.
  ----------------------------------------------------------------------

  base-const : (n : Nat) (X : FTup) -> LeN n n0 -> LeFTup Y0 X ->
    Eq (PF G H (cons (fbot n) X)) (PF G H (cons (fbot n) Y0))
  base-const zero     X ln leX = refl
  base-const (suc n') X ln leX =
    Eq-trans (Eq-cong (\ z -> H (cons (fbot n') (cons z X))) ih) mid
    where
      ln' : LeN n' n0
      ln' = LeN-trans {n'} {suc n'} {n0} (LeN-suc n') ln
      vX vY0 : FEl
      vX  = PF G H (cons (fbot n') X)
      vY0 = PF G H (cons (fbot n') Y0)
      ih : Eq vX vY0
      ih = base-const n' X ln' leX
      vY0-le-N : LeF vY0 (fbot N)
      vY0-le-N = Eq-transport (\ z -> LeF vY0 z) Neq
                   (PF-mono G H monoG monoH {cons (fbot n') Y0} {cons (fbot n0) Y0}
                     (mkSigma ln' (LeFTup-refl Y0)))
      bf = below-fbot {vY0} {N} vY0-le-N
      v      = fst bf
      vY0eq  : Eq vY0 (fbot v)
      vY0eq  = fst (snd bf)
      lvN    : LeN v N
      lvN    = snd (snd bf)
      mid : Eq (H (cons (fbot n') (cons vY0 X)))
               (H (cons (fbot n') (cons vY0 Y0)))
      mid = Eq-transport
              (\ w -> Eq (H (cons (fbot n') (cons w X)))
                         (H (cons (fbot n') (cons w Y0))))
              (Eq-sym vY0eq)
              (h-indep n' v X ln' lvN leX)
