{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.GProj
--
-- Guarded projections, the inner functions that carry the "ambient tail"
-- of a composition.  The primitive-recursion step  f(S x, Y) = h(x,
-- f(x,Y), Y)  feeds h not only computed values but the argument tuple Y
-- itself; to reuse the generic composition (CompDispatch) we must present
-- those pass-through coordinates as genuine UOFuns.
--
-- A plain projection  X |-> getF p X  is NOT ultimate-obstinate at every
-- point (at an all-complete tuple of length <= p it is a constant S^0(bot)
-- with no incomplete/infinite coordinate to pin).  The guarded projection
-- `gproj p` fixes this by returning the COMPLETE default S^0(0) out of
-- range, which is trivially Case 1.  In range it agrees with getF, so a
-- tuple of them reconstructs the tail (`mapU-gprojs`).
--
-- Also here: UO-pointwise-len, transporting UO along an equality of the
-- underlying function that need only hold on tuples of the ambient length
-- (all the universal quantifiers of the property pin that length).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.GProj where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Prop1Base using
  (botLike ; Below-botLike ; length-botLike ; prop1-proj)
open import OBSTINATION.Extension using (LeFTup-length)
open import OBSTINATION.Refine using (Below-length)
open import OBSTINATION.CompPull using (UOFun ; Mono ; mapU)

------------------------------------------------------------------------
-- UO along a length-restricted pointwise equality
------------------------------------------------------------------------

UO-pointwise-len : {f f' : FTup -> FEl} {A : Tup} ->
  ((X : FTup) -> Eq (length X) (length A) -> Eq (f X) (f' X)) ->
  UO f A -> UO f' A
UO-pointwise-len {f} {f'} {A} pw
  (uo1 (mkSigma A0 (mkSigma bel (mkSigma m univ)))) =
  uo1 (mkSigma A0 (mkSigma bel (mkSigma m univ')))
  where
    univ' : (X : FTup) -> LeFTup A0 X -> Eq (f' X) (fcpl m)
    univ' X leX =
      Eq-trans (Eq-sym (pw X (Eq-trans (Eq-sym (LeFTup-length leX)) (Below-length bel))))
        (univ X leX)
UO-pointwise-len {f} {f'} {A} pw
  (uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma ir
    (mkSigma inc (mkSigma eq univ)))))))) =
  uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma ir (mkSigma inc
    (mkSigma eq univ')))))))
  where
    univ' : (X : FTup) -> Eq (length X) (length A0) -> Eq (getF i X) (getF i A0) ->
            LeFTup (del i A0) (del i X) -> Eq (f' X) (fbot m)
    univ' X lx cx dx =
      Eq-trans (Eq-sym (pw X (Eq-trans lx (Below-length bel)))) (univ X lx cx dx)
UO-pointwise-len {f} {f'} {A} pw
  (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei (mkSigma k (mkSigma ea
    (mkSigma phi (mkSigma pok univ))))))))) =
  uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei (mkSigma k (mkSigma ea
    (mkSigma phi (mkSigma pok univ'))))))))
  where
    univ' : (X : FTup) (p : Nat) -> Eq (length X) (length A0) -> LeN k p ->
            Eq (getF i X) (fbot p) -> LeFTup (del i A0) (del i X) ->
            Eq (f' X) (fbot (phi p))
    univ' X p lx pk cx dx =
      Eq-trans (Eq-sym (pw X (Eq-trans lx (Below-length bel)))) (univ X p lx pk cx dx)

------------------------------------------------------------------------
-- A small arithmetic fact
------------------------------------------------------------------------

le-not-lt : (p n : Nat) -> Not (LeN (suc p) n) -> LeN n p
le-not-lt p       zero     np = tt
le-not-lt zero    (suc n') np = Empty-elim (np tt)
le-not-lt (suc p) (suc n') np = le-not-lt p n' np

------------------------------------------------------------------------
-- The guarded projection
------------------------------------------------------------------------

gproj : Nat -> FTup -> FEl
gproj p       nil         = fcpl zero
gproj zero    (cons x xs) = x
gproj (suc p) (cons x xs) = gproj p xs

-- in range it is the ordinary coordinate
gproj-in-range : (p : Nat) (X : FTup) ->
  LeN (suc p) (length X) -> Eq (gproj p X) (getF p X)
gproj-in-range zero    (cons x xs) le = refl
gproj-in-range (suc p) (cons x xs) le = gproj-in-range p xs le
gproj-in-range p       nil         ()

-- out of range it is the complete default
gproj-out : (p : Nat) (X : FTup) -> LeN (length X) p -> Eq (gproj p X) (fcpl zero)
gproj-out p       nil         le = refl
gproj-out zero    (cons x xs) ()
gproj-out (suc p) (cons x xs) le = gproj-out p xs le

-- monotone
gproj-mono : (p : Nat) -> Mono (gproj p)
gproj-mono p       {nil}       {nil}       le = LeF-refl (fcpl zero)
gproj-mono p       {nil}       {cons _ _}  ()
gproj-mono p       {cons _ _}  {nil}       ()
gproj-mono zero    {cons x xs} {cons y ys} le = fst le
gproj-mono (suc p) {cons x xs} {cons y ys} le = gproj-mono p {xs} {ys} (snd le)

-- ultimate obstination at every point
gproj-UO : (p : Nat) -> UOall (gproj p)
gproj-UO p A with LeN-dec (suc p) (length A)
... | yes plt =
  UO-pointwise-len
    (\ X lenX -> Eq-sym (gproj-in-range p X
                   (Eq-transport (\ n -> LeN (suc p) n) (Eq-sym lenX) plt)))
    (prop1-proj p A plt)
... | no  pge =
  uo1 (mkSigma (botLike A) (mkSigma (Below-botLike A) (mkSigma zero univ)))
  where
    univ : (X : FTup) -> LeFTup (botLike A) X -> Eq (gproj p X) (fcpl zero)
    univ X leX = gproj-out p X
      (Eq-transport (\ n -> LeN n p) (Eq-sym lenXA) (le-not-lt p (length A) pge))
      where
        lenXA : Eq (length X) (length A)
        lenXA = Eq-trans (Eq-sym (LeFTup-length leX)) (length-botLike A)

gprojU : Nat -> UOFun
gprojU p = mkSigma (gproj p) (mkSigma (gproj-UO p) (gproj-mono p))

------------------------------------------------------------------------
-- A tuple of guarded projections reconstructs the ambient tail
------------------------------------------------------------------------

-- gprojsFrom b n = [gproj b, gproj (b+1), ..., gproj (b+n-1)]
gprojsFrom : Nat -> Nat -> List UOFun
gprojsFrom b zero    = nil
gprojsFrom b (suc n) = cons (gprojU b) (gprojsFrom (suc b) n)

-- shifting the base past a prepended element
slide : (b n : Nat) (x0 : FEl) (xs : FTup) ->
  Eq (mapU (gprojsFrom (suc b) n) (cons x0 xs)) (mapU (gprojsFrom b n) xs)
slide b zero    x0 xs = refl
slide b (suc n) x0 xs = Eq-cong (cons (gproj b xs)) (slide (suc b) n x0 xs)

-- the full-length tuple of guarded projections is the identity
mapU-gprojs : (X : FTup) -> Eq (mapU (gprojsFrom zero (length X)) X) X
mapU-gprojs nil          = refl
mapU-gprojs (cons x0 xs) =
  Eq-cong (cons x0) (Eq-trans (slide zero (length xs) x0 xs) (mapU-gprojs xs))
