{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompPull
--
-- The composition workhorse, GENERALIZED to an arbitrary tuple of inner
-- functions.  An inner function is packaged as a `UOFun`: a finite
-- function  f : FTup -> FEl  together with a proof that it satisfies
-- ultimate obstination everywhere (`UOall f`) and that it is monotone
-- (`Mono f`).  A composition is then  g o <f_1,...,f_k>  for a list
-- `fs : List UOFun`.
--
-- Given the inner point  B = <ext f_1 A, ..., ext f_k A> : D^k and any
-- finite witness B0 <= B, one can PULL BACK to a finite A0 <= A with
--
--     X >= A0   ==>   mapU fs X  >=  B0.
--
-- This is what turns g's obstination witness at B into an obstination
-- witness for  g o <f_1,...,f_k>  at A.  The proof folds `refine` (one
-- coordinate at a time) and joins the resulting per-coordinate
-- approximants with the least-upper-bound property.
--
-- Instantiating `fs` to the tuple of `evalF h`'s of a `List PR` recovers
-- the composition case of Proposition 1 (see CompDispatch); other
-- instances (const, projections, the recursive restriction) drive the
-- primitive-recursion finite-recurrence case.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompPull where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (ext)
open import OBSTINATION.Refine using (refine)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below)
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike)

------------------------------------------------------------------------
-- Monotone finite functions, and the obstination-carrying package UOFun
------------------------------------------------------------------------

Mono : (FTup -> FEl) -> Set
Mono f = {X Y : FTup} -> LeFTup X Y -> LeF (f X) (f Y)

-- a finite function bundled with its two structural properties
UOFun : Set
UOFun = Sigma (FTup -> FEl) (\ f -> Pair (UOall f) (Mono f))

ufn : UOFun -> (FTup -> FEl)
ufn u = fst u

ufnUO : (u : UOFun) -> UOall (ufn u)
ufnUO u = fst (snd u)

ufnMono : (u : UOFun) -> Mono (ufn u)
ufnMono u = snd (snd u)

------------------------------------------------------------------------
-- Runtime action of an inner tuple, and the inner point of extensions
------------------------------------------------------------------------

-- mapU fs X  =  <f_1 X, ..., f_k X>   (finite)
mapU : List UOFun -> FTup -> FTup
mapU nil         X = nil
mapU (cons u us) X = cons (ufn u X) (mapU us X)

-- innerPt fs A  =  <ext f_1 A, ..., ext f_k A>   (in D^k)
innerPtU : List UOFun -> Tup -> Tup
innerPtU nil         A = nil
innerPtU (cons u us) A = cons (ext (ufn u) (ufnUO u) A) (innerPtU us A)

-- the composite function  g o <f_1,...,f_k>
compFn : (FTup -> FEl) -> List UOFun -> FTup -> FEl
compFn gf fs X = gf (mapU fs X)

------------------------------------------------------------------------
-- Ultimate obstination is a pointwise-equality invariant: it only sees
-- a function through the values it takes, so replacing f by a pointwise
-- equal f' preserves UO (and, indeed, the read-off extension value).
------------------------------------------------------------------------

UO-pointwise : {f f' : FTup -> FEl} {A : Tup} ->
  ((X : FTup) -> Eq (f X) (f' X)) -> UO f A -> UO f' A
UO-pointwise pw (uo1 (mkSigma A0 (mkSigma bel (mkSigma m univ)))) =
  uo1 (mkSigma A0 (mkSigma bel (mkSigma m
    (\ X leX -> Eq-trans (Eq-sym (pw X)) (univ X leX)))))
UO-pointwise pw (uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i
  (mkSigma ir (mkSigma inc (mkSigma eq univ)))))))) =
  uo2 (mkSigma A0 (mkSigma bel (mkSigma m (mkSigma i (mkSigma ir (mkSigma inc
    (mkSigma eq (\ X lx cx dx -> Eq-trans (Eq-sym (pw X)) (univ X lx cx dx)))))))))
UO-pointwise pw (uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei
  (mkSigma k (mkSigma ea (mkSigma phi (mkSigma pok univ))))))))) =
  uo3 (mkSigma A0 (mkSigma bel (mkSigma i (mkSigma ei (mkSigma k (mkSigma ea
    (mkSigma phi (mkSigma pok
      (\ X p lx pk cx dx -> Eq-trans (Eq-sym (pw X)) (univ X p lx pk cx dx))))))))))

------------------------------------------------------------------------
-- transitivity of the pointwise order on finite tuples
------------------------------------------------------------------------

LeFTup-trans : {A B C : FTup} -> LeFTup A B -> LeFTup B C -> LeFTup A C
LeFTup-trans {A} {B} {C} p q = LeTup-trans {embedTup A} {embedTup B} {embedTup C} p q

------------------------------------------------------------------------
-- Pull-back
------------------------------------------------------------------------

pullback : (fs : List UOFun) (A : Tup) (B0 : FTup) ->
  Below B0 (innerPtU fs A) ->
  Sigma FTup (\ A0 ->
    Pair (Below A0 A)
      ((X : FTup) -> LeFTup A0 X -> LeFTup B0 (mapU fs X)))
pullback nil         A nil          bel =
  mkSigma (botLike A) (mkSigma (Below-botLike A) (\ X _ -> tt))
pullback nil         A (cons _ _)   ()
pullback (cons u us) A (cons b0 B0') bel =
  let rh     = refine (ufn u) (ufnUO u) A b0 (fst bel)
      A0h    = fst rh
      belowh = fst (snd rh)
      leh    = snd (snd rh)
      rec    = pullback us A B0' (snd bel)
      A0'    = fst rec
      below' = fst (snd rec)
      univ'  = snd (snd rec)
      A0     = joinT A0h A0'
      bndA   = BndT-from-Below belowh below'
      univ : (X : FTup) -> LeFTup A0 X ->
             LeFTup (cons b0 B0') (mapU (cons u us) X)
      univ X leX =
        let leA0hX = LeFTup-trans (join-ubT-l bndA) leX
            leA0'X = LeFTup-trans (join-ubT-r bndA) leX
        in mkSigma (LeF-trans {b0} {ufn u A0h} {ufn u X}
                      leh (ufnMono u {A0h} {X} leA0hX))
                   (univ' X leA0'X)
  in mkSigma A0 (mkSigma (Below-joinT belowh below') univ)
