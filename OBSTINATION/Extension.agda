{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Extension
--
-- The Scott-continuous extension of a function satisfying ultimate
-- obstination (min1.pdf, page 2: "on peut calculer l'extension
-- Scott-continue de f sur D^n").  Its value at A is read off the
-- property -- this is exactly `uoValue`.
--
-- The foundational lemma is AGREEMENT ON FINITE POINTS: the extension
-- restricted to a finite tuple X (embedded into D^n) equals the finite
-- value f X.  This is what connects the extension back to the finite
-- interpreter, and is used by the composition and recursion cases.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Extension where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property

------------------------------------------------------------------------
-- The extension: value read off the property at each point.
------------------------------------------------------------------------

ext : (f : FTup -> FEl) -> UOall f -> Tup -> D
ext f uoall A = uoValue (uoall A)

------------------------------------------------------------------------
-- Elementary facts about embed / get / del on finite tuples
------------------------------------------------------------------------

bot-inj : {j k : Nat} -> Eq (bot j) (bot k) -> Eq j k
bot-inj refl = refl

cpl-inj : {j k : Nat} -> Eq (cpl j) (cpl k) -> Eq j k
cpl-inj refl = refl

embed-inj : {x y : FEl} -> Eq (embed x) (embed y) -> Eq x y
embed-inj {fbot j} {fbot k} p = Eq-cong fbot (bot-inj p)
embed-inj {fbot j} {fcpl k} ()
embed-inj {fcpl j} {fbot k} ()
embed-inj {fcpl j} {fcpl k} p = Eq-cong fcpl (cpl-inj p)

embed-not-inf : {w : FEl} -> Eq (embed w) inf -> Empty
embed-not-inf {fbot k} ()
embed-not-inf {fcpl k} ()

-- get on an embedded finite tuple is the embedding of getF
get-embedTup : (i : Nat) (X : FTup) -> Eq (get i (embedTup X)) (embed (getF i X))
get-embedTup i       nil         = refl
get-embedTup zero    (cons x xs) = refl
get-embedTup (suc i) (cons x xs) = get-embedTup i xs

-- pointwise order forces equal length and is preserved by deletion
LeFTup-length : {A B : FTup} -> LeFTup A B -> Eq (length A) (length B)
LeFTup-length {nil}      {nil}      le = refl
LeFTup-length {nil}      {cons _ _} ()
LeFTup-length {cons _ _} {nil}      ()
LeFTup-length {cons a A} {cons b B} le = Eq-cong suc (LeFTup-length {A} {B} (snd le))

del-LeFTup : (i : Nat) {A B : FTup} -> LeFTup A B -> LeFTup (del i A) (del i B)
del-LeFTup i       {nil}      {nil}      le = tt
del-LeFTup i       {nil}      {cons _ _} ()
del-LeFTup i       {cons _ _} {nil}      ()
del-LeFTup zero    {cons a A} {cons b B} le = snd le
del-LeFTup (suc i) {cons a A} {cons b B} le = mkSigma (fst le) (del-LeFTup i {A} {B} (snd le))

------------------------------------------------------------------------
-- Agreement on finite points
------------------------------------------------------------------------

agree-aux : (f : FTup -> FEl) (X : FTup) (u : UO f (embedTup X)) ->
  Eq (uoValue u) (embed (f X))
-- Case 1: f X = fcpl m, extension value cpl m
agree-aux f X (uo1 (mkSigma A0 (mkSigma below (mkSigma m univ)))) =
  Eq-sym (Eq-cong embed (univ X below))
-- Case 2: f X = fbot m, extension value bot m
agree-aux f X (uo2 (mkSigma A0 (mkSigma below
  (mkSigma m (mkSigma i (mkSigma _ (mkSigma incompl (mkSigma eqA0 univ)))))))) =
  Eq-sym (Eq-cong embed
    (univ X
      (Eq-sym (LeFTup-length below))
      (Eq-sym (embed-inj (Eq-trans eqA0 (get-embedTup i X))))
      (del-LeFTup i below)))
-- Case 3: impossible at a finite point (get i (embedTup X) is never inf)
agree-aux f X (uo3 (mkSigma A0 (mkSigma below (mkSigma i (mkSigma eqinf rest))))) =
  Empty-elim (embed-not-inf (Eq-trans (Eq-sym (get-embedTup i X)) eqinf))

agreement : (f : FTup -> FEl) (uoall : UOall f) (X : FTup) ->
  Eq (ext f uoall (embedTup X)) (embed (f X))
agreement f uoall X = agree-aux f X (uoall (embedTup X))
