{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Arity
--
-- Arity-restricted obstination, and the guard that turns it into total
-- obstination.
--
-- A primitive-recursive term p of arity n interprets to a function
-- evalF p that satisfies the property ONLY at tuples of length n
-- (elsewhere it is out-of-arity junk).  This is captured by
--
--     UOn n f  =  (A : Tup) -> length A = n -> UO f A.
--
-- To feed such a function to the composition machinery (which asks for a
-- TOTAL `UOall`), pad it: `guard n f` equals f on length-n inputs and is
-- the constant S^0(0) elsewhere, so it is UOall.  Since every place that
-- consumes the guard only ever evaluates it on length-n tuples, the guard
-- is interchangeable with f there.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Arity where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Meet using (Bnd ; BndT ; meetF ; meetT)
open import OBSTINATION.Extension using (LeFTup-length)
open import OBSTINATION.Prop1Base using (botLike ; Below-botLike ; length-botLike)
open import OBSTINATION.GProj using (UO-pointwise-len)
open import OBSTINATION.CompPull using (Mono)
open import OBSTINATION.PrecFun using (Stable)

------------------------------------------------------------------------
-- Arity-restricted obstination.
------------------------------------------------------------------------

UOn : Nat -> (FTup -> FEl) -> Set
UOn n f = (A : Tup) -> Eq (length A) n -> UO f A

------------------------------------------------------------------------
-- The guard.
------------------------------------------------------------------------

guard : Nat -> (FTup -> FEl) -> FTup -> FEl
guard n f X with EqNat-dec (length X) n
... | yes _ = f X
... | no  _ = fcpl zero

guard-eq : (n : Nat) (f : FTup -> FEl) (X : FTup) -> Eq (length X) n ->
  Eq (guard n f X) (f X)
guard-eq n f X e with EqNat-dec (length X) n
... | yes _ = refl
... | no  k = Empty-elim (k e)

guard-off : (n : Nat) (f : FTup -> FEl) (X : FTup) -> Not (Eq (length X) n) ->
  Eq (guard n f X) (fcpl zero)
guard-off n f X k with EqNat-dec (length X) n
... | yes p = Empty-elim (k p)
... | no  _ = refl

------------------------------------------------------------------------
-- The guard is UOall.
------------------------------------------------------------------------

guard-uoall : (n : Nat) (f : FTup -> FEl) -> UOn n f -> UOall (guard n f)
guard-uoall n f uon A with EqNat-dec (length A) n
... | yes p =
      UO-pointwise-len
        (\ X lenXA -> Eq-sym (guard-eq n f X (Eq-trans lenXA p)))
        (uon A p)
... | no  k =
      uo1 (mkSigma (botLike A) (mkSigma (Below-botLike A) (mkSigma zero univ)))
  where
    univ : (X : FTup) -> LeFTup (botLike A) X -> Eq (guard n f X) (fcpl zero)
    univ X leX =
      guard-off n f X
        (\ e -> k (Eq-trans (Eq-sym (Eq-trans (Eq-sym (LeFTup-length leX))
                                              (length-botLike A))) e))

------------------------------------------------------------------------
-- The guard preserves monotonicity and stability.
--
-- Comparable (LeFTup) or bounded (BndT) tuples have EQUAL length, so both
-- sides of the guard take the SAME branch; where the branch is f, the
-- claim reduces to that of f, and where it is the constant it is trivial.
------------------------------------------------------------------------

BndT-length : {A B : FTup} -> BndT A B -> Eq (length A) (length B)
BndT-length {nil}       {nil}      bd = refl
BndT-length {nil}       {cons _ _} ()
BndT-length {cons _ _}  {nil}      ()
BndT-length {cons a A}  {cons b B} bd = Eq-cong suc (BndT-length {A} {B} (snd bd))

meetT-length : {A B : FTup} -> BndT A B -> Eq (length (meetT A B)) (length A)
meetT-length {nil}       {nil}      bd = refl
meetT-length {nil}       {cons _ _} ()
meetT-length {cons _ _}  {nil}      ()
meetT-length {cons a A}  {cons b B} bd = Eq-cong suc (meetT-length {A} {B} (snd bd))

guard-mono : (n : Nat) (f : FTup -> FEl) -> Mono f -> Mono (guard n f)
guard-mono n f mf {X} {Y} le = go (EqNat-dec (length X) n)
  where
    go : Dec (Eq (length X) n) -> LeF (guard n f X) (guard n f Y)
    go (yes p) =
      Eq-transport (\ u -> LeF u (guard n f Y)) (Eq-sym (guard-eq n f X p))
        (Eq-transport (\ v -> LeF (f X) v)
          (Eq-sym (guard-eq n f Y (Eq-trans (Eq-sym (LeFTup-length le)) p)))
          (mf le))
    go (no  p) =
      Eq-transport (\ u -> LeF u (guard n f Y)) (Eq-sym (guard-off n f X p))
        (Eq-transport (\ v -> LeF (fcpl zero) v)
          (Eq-sym (guard-off n f Y (\ e -> p (Eq-trans (LeFTup-length le) e))))
          (LeF-refl (fcpl zero)))

guard-stable : (n : Nat) (f : FTup -> FEl) -> Stable f -> Stable (guard n f)
guard-stable n f sf {A} {B} bd = go (EqNat-dec (length A) n)
  where
    go : Dec (Eq (length A) n) ->
      Eq (guard n f (meetT A B)) (meetF (guard n f A) (guard n f B))
    go (yes p) =
      Eq-transport (\ u -> Eq (guard n f (meetT A B)) (meetF u (guard n f B)))
        (Eq-sym (guard-eq n f A p))
        (Eq-transport (\ v -> Eq (guard n f (meetT A B)) (meetF (f A) v))
          (Eq-sym (guard-eq n f B (Eq-trans (Eq-sym (BndT-length bd)) p)))
          (Eq-transport (\ w -> Eq w (meetF (f A) (f B)))
            (Eq-sym (guard-eq n f (meetT A B) (Eq-trans (meetT-length bd) p)))
            (sf bd)))
    go (no  p) =
      Eq-transport (\ u -> Eq (guard n f (meetT A B)) (meetF u (guard n f B)))
        (Eq-sym (guard-off n f A p))
        (Eq-transport (\ v -> Eq (guard n f (meetT A B)) (meetF (fcpl zero) v))
          (Eq-sym (guard-off n f B (\ e -> p (Eq-trans (BndT-length bd) e))))
          (guard-off n f (meetT A B) (\ e -> p (Eq-trans (Eq-sym (meetT-length bd)) e))))
