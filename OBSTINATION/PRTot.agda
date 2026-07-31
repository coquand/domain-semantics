{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PRTot
--
-- **TOTALITY: A PR TERM APPLIED TO NUMERALS RETURNS A NUMERAL.**
--
--     evalF-tot : (q : PR) (X : FTup) -> Wf q (length X) -> AllCpl X
--               -> IsCpl (evalF q X)
--
-- This is the ingredient `TrUOFail` shows is missing from MP1.  At an
-- ALL-COMPLETE point `A` the three cases of `Property.UO` leave no room --
-- Case 2 wants an incomplete finite coordinate, Case 3 an infinite one --
-- so Case 1 must hold and the value must be a NUMERAL.  Nothing in a
-- trace knows that (`stop (fbot 0)` has full MP1), so `Prop 1 from MP1`
-- has to carry totality separately; here it is, by the same induction
-- that defines `evalF`.
--
-- The recursion clause is the only one with content: with the recursion
-- argument a numeral `S^j(0)`, `precF` unrolls exactly `j` times and each
-- layer is `h` applied to numerals, so an induction on `j` inside the
-- induction on the term does it (`precF-cpl`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PRTot where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; sucF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using
  (PR ; zerf ; proj ; succ ; comp ; prec ; evalF ; mapE ; precF)
open import OBSTINATION.Prop1 using (Wf ; AllWf)
open import OBSTINATION.TrSat using (IsCpl)

------------------------------------------------------------------------
-- ALL COORDINATES ARE NUMERALS
------------------------------------------------------------------------

AllCpl : FTup -> Set
AllCpl nil         = Top
AllCpl (cons x xs) = Pair (IsCpl x) (AllCpl xs)

allCpl-nth : (X : FTup) -> AllCpl X -> (i : Nat) -> LeN (suc i) (length X)
           -> IsCpl (nth (fbot zero) i X)
allCpl-nth nil         ac i       ()
allCpl-nth (cons x xs) ac zero    li = fst ac
allCpl-nth (cons x xs) ac (suc i) li = allCpl-nth xs (snd ac) i li

sucF-cpl : (x : FEl) -> IsCpl x -> IsCpl (sucF x)
sucF-cpl (fbot k) ()
sucF-cpl (fcpl k) ic = tt

------------------------------------------------------------------------
-- THE ARGUMENT LIST OF A COMPOSITION
------------------------------------------------------------------------

mapE-len : (hs : List PR) (X : FTup) -> Eq (length (mapE hs X)) (length hs)
mapE-len nil         X = refl
mapE-len (cons p ps) X = Eq-cong suc (mapE-len ps X)

------------------------------------------------------------------------
-- TOTALITY
------------------------------------------------------------------------

mutual
  evalF-tot : (q : PR) (X : FTup) -> Wf q (length X) -> AllCpl X
            -> IsCpl (evalF q X)
  evalF-tot zerf     X            wf ac = tt
  evalF-tot (proj i) X            wf ac = allCpl-nth X ac i wf
  evalF-tot succ     nil          () ac
  evalF-tot succ     (cons x xs)  wf ac = sucF-cpl x (fst ac)
  ----------------------------------------------------------------------
  -- composition: the arguments are numerals, so the outer term applies
  ----------------------------------------------------------------------
  evalF-tot (comp g hs) X wf ac =
    evalF-tot g (mapE hs X)
      (Eq-transport (\ z -> Wf g z) (Eq-sym (mapE-len hs X)) (fst wf))
      (mapE-cpl hs X (snd wf) ac)
  ----------------------------------------------------------------------
  -- primitive recursion: the recursion argument is a numeral, so the
  -- unrolling is finite
  ----------------------------------------------------------------------
  evalF-tot (prec g h) nil         wf ac = Empty-elim (bad wf)
    where
      bad : Sigma Nat (\ m -> Pair (Eq zero (suc m))
              (Pair (Wf g m) (Wf h (suc (suc m))))) -> Empty
      bad (mkSigma m (mkSigma () _))
  evalF-tot (prec g h) (cons a Y)  wf ac = go a (fst ac) refl
    where
      m : Nat
      m = fst wf

      lenY : Eq (length Y) m
      lenY = suc-inj (fst (snd wf))

      wg : Wf g m
      wg = fst (snd (snd wf))

      wh : Wf h (suc (suc m))
      wh = snd (snd (snd wf))

      go : (x : FEl) -> IsCpl x -> Eq x a -> IsCpl (precF g h a Y)
      go (fbot k) ()  e
      go (fcpl k) tt  e =
        Eq-transport (\ z -> IsCpl (precF g h z Y)) e
          (precF-cpl g h m wg wh k Y lenY (snd ac))

  --------------------------------------------------------------------
  -- the arguments of a composition are numerals
  --------------------------------------------------------------------
  mapE-cpl : (hs : List PR) (X : FTup) -> AllWf hs (length X) -> AllCpl X
           -> AllCpl (mapE hs X)
  mapE-cpl nil         X aw ac = tt
  mapE-cpl (cons p ps) X aw ac =
    mkSigma (evalF-tot p X (fst aw) ac) (mapE-cpl ps X (snd aw) ac)

  --------------------------------------------------------------------
  -- and the recursion unrolls `k` times, each layer applying `h` to
  -- numerals
  --------------------------------------------------------------------
  precF-cpl : (g h : PR) (m : Nat) -> Wf g m -> Wf h (suc (suc m))
            -> (k : Nat) (Y : FTup) -> Eq (length Y) m -> AllCpl Y
            -> IsCpl (precF g h (fcpl k) Y)
  precF-cpl g h m wg wh zero    Y lenY ac =
    evalF-tot g Y (Eq-transport (\ z -> Wf g z) (Eq-sym lenY) wg) ac
  precF-cpl g h m wg wh (suc k) Y lenY ac =
    evalF-tot h (cons (fcpl k) (cons (precF g h (fcpl k) Y) Y))
      (Eq-transport (\ z -> Wf h (suc (suc z))) (Eq-sym lenY) wh)
      (mkSigma tt (mkSigma (precF-cpl g h m wg wh k Y lenY ac) ac))
