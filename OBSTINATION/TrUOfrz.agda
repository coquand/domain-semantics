{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrUOfrz
--
-- PROPOSITION 1 SURVIVES FREEZING A COORDINATE TO A NUMERAL.
--
-- `TrVerdict` reduces the value half of MP1 to `UO F A` -- but MP1 is a
-- STRUCTURAL invariant: every continuation of the trace has to satisfy it
-- too, and a continuation denotes the FROZEN function
-- `\ Y -> F (ins c (fcpl v) Y)`.  So what is needed is not `UO (evalF q)`
-- alone but
--
--     UOfrz a F  =  UO F at every point of arity `a`
--                 , and UOfrz (a-1) of every freezing of F
--
-- and `uofrz-PR` proves `UOfrz a (evalF q)` for every PR term `q` well
-- formed at arity `a`.  The point is that freezing IS a PR operation:
--
--     \ Y -> evalF q (ins c (fcpl v) Y)  =  evalF (comp q [ ... ])
--
-- where the argument list is the identity substitution with the numeral
-- `S^v(0)` (`num v`) spliced in at `c` and the remaining projections
-- re-indexed by `TraceDef.sd` -- exactly the re-indexing `nth-ins-ne`
-- already uses.  The arity drops by one, so the recursion is on `a`, not
-- on the term (the term GROWS).
--
-- `UO F A` only ever mentions `F` at tuples of length `length A`
-- (`Case1`'s `LeFTup A0 X` forces it, `Case2`/`Case3` say it outright),
-- so it transports along agreement at that length -- `UO-ext`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrUOfrz where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property using (UO ; uo1 ; uo2 ; uo3 ; getF)
open import OBSTINATION.Prop1 using (Wf ; AllWf ; prop1)
open import OBSTINATION.TraceDef using
  (sd ; sd-range ; tup ; tup-len ; tup-nth ; tup-out)
open import OBSTINATION.TrDen using
  (ins ; ins-len ; nth-ins-eq ; nth-ins-ne ; nth-out)
open import OBSTINATION.TrVerdict using (embedTup-len ; LeTup-len)

------------------------------------------------------------------------
-- `UO` DEPENDS ON `F` ONLY AT THE ARITY OF THE POINT
------------------------------------------------------------------------

LeFTup-len : (X Y : FTup) -> LeFTup X Y -> Eq (length X) (length Y)
LeFTup-len X Y le =
  Eq-trans (Eq-sym (embedTup-len X))
    (Eq-trans (LeTup-len (embedTup X) (embedTup Y) le) (embedTup-len Y))

UO-ext : (F G : FTup -> FEl) (A : Tup)
       -> ((X : FTup) -> Eq (length X) (length A) -> Eq (F X) (G X))
       -> UO F A -> UO G A
UO-ext F G A e (uo1 (mkSigma A0 (mkSigma bel (mkSigma m hyp)))) =
  uo1 (mkSigma A0 (mkSigma bel (mkSigma m hyp')))
  where
    A0len : Eq (length A0) (length A)
    A0len = Eq-trans (Eq-sym (embedTup-len A0)) (LeTup-len (embedTup A0) A bel)

    hyp' : (X : FTup) -> LeFTup A0 X -> Eq (G X) (fcpl m)
    hyp' X le =
      Eq-trans
        (Eq-sym (e X (Eq-trans (Eq-sym (LeFTup-len A0 X le)) A0len)))
        (hyp X le)
UO-ext F G A e
  (uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma li
         (mkSigma inc (mkSigma eqA hyp)))))))) =
  uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma li
         (mkSigma inc (mkSigma eqA hyp')))))))
  where
    A0len : Eq (length A0) (length A)
    A0len = Eq-trans (Eq-sym (embedTup-len A0)) (LeTup-len (embedTup A0) A bel)

    hyp' : (X : FTup) -> Eq (length X) (length A0)
         -> Eq (getF i X) (getF i A0)
         -> LeFTup (del i A0) (del i X) -> Eq (G X) (fbot m)
    hyp' X lx eg ld =
      Eq-trans (Eq-sym (e X (Eq-trans lx A0len))) (hyp X lx eg ld)
UO-ext F G A e
  (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf (mkSigma k
         (mkSigma eA0 (mkSigma phi (mkSigma pk hyp)))))))))=
  uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma einf (mkSigma k
         (mkSigma eA0 (mkSigma phi (mkSigma pk hyp'))))))))
  where
    A0len : Eq (length A0) (length A)
    A0len = Eq-trans (Eq-sym (embedTup-len A0)) (LeTup-len (embedTup A0) A bel)

    hyp' : (X : FTup) (m : Nat) -> Eq (length X) (length A0) -> LeN k m
         -> Eq (getF i X) (fbot m)
         -> LeFTup (del i A0) (del i X) -> Eq (G X) (fbot (phi m))
    hyp' X m lx lk eg ld =
      Eq-trans (Eq-sym (e X (Eq-trans lx A0len))) (hyp X m lx lk eg ld)

------------------------------------------------------------------------
-- THE FREEZING-CLOSED FORM OF PROPOSITION 1
------------------------------------------------------------------------

UOfrz : (a : Nat) -> (FTup -> FEl) -> Set
UOfrz zero    F = Top
UOfrz (suc a) F =
  Pair ((A : Tup) -> Eq (length A) (suc a) -> UO F A)
       ((c : Nat) -> LeN (suc c) (suc a) -> (v : Nat)
        -> UOfrz a (\ Y -> F (ins c (fcpl v) Y)))

UOfrz-ext : (a : Nat) (F G : FTup -> FEl)
          -> ((X : FTup) -> Eq (length X) a -> Eq (F X) (G X))
          -> UOfrz a F -> UOfrz a G
UOfrz-ext zero    F G e uf = tt
UOfrz-ext (suc a) F G e uf =
  mkSigma
    (\ A la -> UO-ext F G A (\ X lx -> e X (Eq-trans lx la)) (fst uf A la))
    (\ c lc v ->
       UOfrz-ext a (\ Y -> F (ins c (fcpl v) Y)) (\ Y -> G (ins c (fcpl v) Y))
         (\ Y ly ->
            e (ins c (fcpl v) Y)
              (Eq-trans
                (ins-len c (fcpl v) Y
                  (Eq-transport (\ z -> LeN c z) (Eq-sym ly) lc))
                (Eq-cong suc ly)))
         (snd uf c lc v))

------------------------------------------------------------------------
-- NUMERALS
------------------------------------------------------------------------

num : Nat -> PR
num zero    = zerf
num (suc v) = comp succ (cons (num v) nil)

num-eval : (v : Nat) (Y : FTup) -> Eq (evalF (num v) Y) (fcpl v)
num-eval zero    Y = refl
num-eval (suc v) Y = Eq-cong sucF (num-eval v Y)

num-wf : (v n : Nat) -> Wf (num v) n
num-wf zero    n = tt
num-wf (suc v) n = mkSigma tt (mkSigma (num-wf v n) tt)

------------------------------------------------------------------------
-- ARGUMENT LISTS FROM A FUNCTION OF THE INDEX
------------------------------------------------------------------------

listOf : Nat -> (Nat -> PR) -> List PR
listOf zero    f = nil
listOf (suc n) f = cons (f zero) (listOf n (\ j -> f (suc j)))

listOf-len : (n : Nat) (f : Nat -> PR) -> Eq (length (listOf n f)) n
listOf-len zero    f = refl
listOf-len (suc n) f = Eq-cong suc (listOf-len n (\ j -> f (suc j)))

allWf-listOf : (n : Nat) (f : Nat -> PR) (a : Nat)
             -> ((j : Nat) -> LeN (suc j) n -> Wf (f j) a)
             -> AllWf (listOf n f) a
allWf-listOf zero    f a h = tt
allWf-listOf (suc n) f a h =
  mkSigma (h zero tt)
    (allWf-listOf n (\ j -> f (suc j)) a (\ j lj -> h (suc j) lj))

mapE-listOf : (n : Nat) (f : Nat -> PR) (Y : FTup)
            -> Eq (mapE (listOf n f) Y) (tup n (\ j -> evalF (f j) Y))
mapE-listOf zero    f Y = refl
mapE-listOf (suc n) f Y =
  Eq-cong (cons (evalF (f zero) Y)) (mapE-listOf n (\ j -> f (suc j)) Y)

------------------------------------------------------------------------
-- THE IDENTITY SUBSTITUTION WITH A NUMERAL SPLICED IN AT `c`
------------------------------------------------------------------------

argPick : (c v j : Nat) -> Dec (Eq j c) -> PR
argPick c v j (yes _) = num v
argPick c v j (no  _) = proj (sd c j)

argAt : Nat -> Nat -> Nat -> PR
argAt c v j = argPick c v j (EqNat-dec j c)

argAt-wf : (a c v j : Nat) -> LeN (suc c) (suc a) -> LeN (suc j) (suc a)
         -> Wf (argAt c v j) a
argAt-wf a c v j lc lj = go (EqNat-dec j c) refl
  where
    go : (D : Dec (Eq j c)) -> Eq (EqNat-dec j c) D -> Wf (argAt c v j) a
    go (yes ej) e =
      Eq-transport (\ q -> Wf q a)
        (Eq-sym (Eq-cong (argPick c v j) e)) (num-wf v a)
    go (no  nj) e =
      Eq-transport (\ q -> Wf q a)
        (Eq-sym (Eq-cong (argPick c v j) e)) (sd-range a c j lc lj nj)

argAt-eval : (c v j : Nat) (Y : FTup)
           -> Eq (evalF (argAt c v j) Y)
                 (nth (fbot zero) j (ins c (fcpl v) Y))
argAt-eval c v j Y = go (EqNat-dec j c) refl
  where
    go : (D : Dec (Eq j c)) -> Eq (EqNat-dec j c) D
       -> Eq (evalF (argAt c v j) Y) (nth (fbot zero) j (ins c (fcpl v) Y))
    go (yes ej) e =
      Eq-trans (Eq-cong (\ q -> evalF q Y) (Eq-cong (argPick c v j) e))
        (Eq-trans (num-eval v Y)
          (Eq-sym
            (Eq-trans
              (Eq-cong (\ z -> nth (fbot zero) z (ins c (fcpl v) Y)) ej)
              (nth-ins-eq c (fcpl v) Y))))
    go (no nj) e =
      Eq-trans (Eq-cong (\ q -> evalF q Y) (Eq-cong (argPick c v j) e))
        (Eq-sym (nth-ins-ne c j nj (fcpl v) Y))

------------------------------------------------------------------------
-- two tuples of the same length agreeing everywhere are equal
------------------------------------------------------------------------

tup-ext : (X X' : FTup) -> Eq (length X) (length X')
        -> ((j : Nat) -> Eq (nth (fbot zero) j X) (nth (fbot zero) j X'))
        -> Eq X X'
tup-ext nil         nil         e h = refl
tup-ext nil         (cons _ _)  () h
tup-ext (cons _ _)  nil         () h
tup-ext (cons x xs) (cons y ys) e h =
  Eq-trans (Eq-cong (\ z -> cons z xs) (h zero))
    (Eq-cong (cons y) (tup-ext xs ys (suc-inj e) (\ j -> h (suc j))))

------------------------------------------------------------------------
-- FREEZING A COORDINATE IS A PR OPERATION
------------------------------------------------------------------------

frzPR : Nat -> Nat -> Nat -> PR -> PR
frzPR a c v q = comp q (listOf (suc a) (argAt c v))

frzPR-wf : (a c v : Nat) -> LeN (suc c) (suc a) -> (q : PR) -> Wf q (suc a)
         -> Wf (frzPR a c v q) a
frzPR-wf a c v lc q wq =
  mkSigma
    (Eq-transport (\ z -> Wf q z)
      (Eq-sym (listOf-len (suc a) (argAt c v))) wq)
    (allWf-listOf (suc a) (argAt c v) a (\ j lj -> argAt-wf a c v j lc lj))

frzPR-eval : (a c v : Nat) -> LeN (suc c) (suc a) -> (q : PR)
             (Y : FTup) -> Eq (length Y) a
           -> Eq (evalF (frzPR a c v q) Y) (evalF q (ins c (fcpl v) Y))
frzPR-eval a c v lc q Y ly =
  Eq-cong (evalF q)
    (Eq-trans (mapE-listOf (suc a) (argAt c v) Y) tupEq)
  where
    lcY : LeN c (length Y)
    lcY = Eq-transport (\ z -> LeN c z) (Eq-sym ly) lc

    insLen : Eq (length (ins c (fcpl v) Y)) (suc a)
    insLen =
      Eq-trans (ins-len c (fcpl v) Y lcY) (Eq-cong suc ly)

    lens : Eq (length (tup (suc a) (\ j -> evalF (argAt c v j) Y)))
              (length (ins c (fcpl v) Y))
    lens =
      Eq-trans (tup-len (suc a) (\ j -> evalF (argAt c v j) Y))
        (Eq-sym insLen)

    coord : (j : Nat)
          -> Eq (nth (fbot zero) j (tup (suc a) (\ d -> evalF (argAt c v d) Y)))
                (nth (fbot zero) j (ins c (fcpl v) Y))
    coord j = route (LeN-dec (suc j) (suc a))
      where
        route : Dec (LeN (suc j) (suc a))
              -> Eq (nth (fbot zero) j
                      (tup (suc a) (\ d -> evalF (argAt c v d) Y)))
                    (nth (fbot zero) j (ins c (fcpl v) Y))
        route (yes lj) =
          Eq-trans
            (tup-nth (suc a) (\ d -> evalF (argAt c v d) Y) j lj)
            (argAt-eval c v j Y)
        route (no nj) =
          Eq-trans
            (tup-out (suc a) (\ d -> evalF (argAt c v d) Y) j nj)
            (Eq-sym
              (nth-out (fbot zero) j (ins c (fcpl v) Y)
                (\ l -> nj (Eq-transport (\ z -> LeN (suc j) z) insLen l))))

    tupEq : Eq (tup (suc a) (\ j -> evalF (argAt c v j) Y))
               (ins c (fcpl v) Y)
    tupEq =
      tup-ext (tup (suc a) (\ j -> evalF (argAt c v j) Y))
        (ins c (fcpl v) Y) lens coord

------------------------------------------------------------------------
-- PROPOSITION 1, CLOSED UNDER FREEZING
------------------------------------------------------------------------

uofrz-PR : (a : Nat) (q : PR) -> Wf q a -> UOfrz a (evalF q)
uofrz-PR zero    q wq = tt
uofrz-PR (suc a) q wq =
  mkSigma
    (\ A la -> prop1 q A (Eq-transport (\ z -> Wf q z) (Eq-sym la) wq))
    (\ c lc v ->
       UOfrz-ext a (evalF (frzPR a c v q))
         (\ Y -> evalF q (ins c (fcpl v) Y))
         (\ Y ly -> frzPR-eval a c v lc q Y ly)
         (uofrz-PR a (frzPR a c v q) (frzPR-wf a c v lc q wq)))
