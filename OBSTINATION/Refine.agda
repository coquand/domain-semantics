{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Refine
--
-- Compactness / refinement of the extension (min1.pdf, page 2, last
-- line): if u is finite with u <= f(A) (the extension at A), then one
-- can compute a finite A0 <= A with u <= f(A0).  Finite information in
-- the output comes from finite information in the input.
--
-- Proof by the case of the property at A:
--   * Case 1 / Case 2 / Case 3-constant: the extension value is finite
--     and already realised at the witness A0.
--   * Case 3-increasing: the extension value is S^omega(bot); use
--     phi-escape to pick a stage m with phi m past the bound, and set
--     coordinate i of A0 to S^m(bot).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Refine where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (ext)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)

------------------------------------------------------------------------
-- Length / deletion lemmas for repl, and a general Below-replacement
------------------------------------------------------------------------

del-repl : (i : Nat) (v : FEl) (T : FTup) -> Eq (del i (repl i v T)) (del i T)
del-repl i       v nil         = refl
del-repl zero    v (cons x xs) = refl
del-repl (suc i) v (cons x xs) = Eq-cong (cons x) (del-repl i v xs)

Below-repl-into : (i : Nat) (v : FEl) (A0 : FTup) (A : Tup) ->
  Below A0 A -> LeD (embed v) (get i A) -> Below (repl i v A0) A
Below-repl-into i       v nil          A          bel ub = bel
Below-repl-into zero    v (cons a A0') nil         () ub
Below-repl-into zero    v (cons a A0') (cons d A') bel ub = mkSigma ub (snd bel)
Below-repl-into (suc i) v (cons a A0') nil         () ub
Below-repl-into (suc i) v (cons a A0') (cons d A') bel ub =
  mkSigma (fst bel) (Below-repl-into i v A0' A' (snd bel) ub)

------------------------------------------------------------------------
-- Below forces equal length; an infinite coordinate is in range
------------------------------------------------------------------------

Below-length : {A0 : FTup} {A : Tup} -> Below A0 A -> Eq (length A0) (length A)
Below-length {nil}       {nil}       bel = refl
Below-length {nil}       {cons _ _}  ()
Below-length {cons _ _}  {nil}       ()
Below-length {cons a A0'} {cons d A'} bel = Eq-cong suc (Below-length {A0'} {A'} (snd bel))

get-inf-in-range : (i : Nat) (A : Tup) -> Eq (get i A) inf -> LeN (suc i) (length A)
get-inf-in-range zero    (cons d A') e = tt
get-inf-in-range (suc i) (cons d A') e = get-inf-in-range i A' e
get-inf-in-range i       nil         ()

------------------------------------------------------------------------
-- Refinement
------------------------------------------------------------------------

refine-aux : (f : FTup -> FEl) (A : Tup) (u : FEl) (pf : UO f A) ->
  LeD (embed u) (uoValue pf) ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (LeF u (f A0)))
-- Case 1
refine-aux f A u (uo1 (mkSigma A0 (mkSigma below (mkSigma m univ)))) le =
  mkSigma A0 (mkSigma below
    (Eq-transport (\ z -> LeD (embed u) z)
      (Eq-sym (Eq-cong embed (univ A0 (LeFTup-refl A0)))) le))
-- Case 2
refine-aux f A u (uo2 (mkSigma A0 (mkSigma below
  (mkSigma m (mkSigma i (mkSigma _ (mkSigma incompl (mkSigma eqA0 univ)))))))) le =
  mkSigma A0 (mkSigma below
    (Eq-transport (\ z -> LeD (embed u) z)
      (Eq-sym (Eq-cong embed (univ A0 refl refl (LeFTup-refl (del i A0))))) le))
-- Case 3, phi constant: extension value bot (phi k), realised at A0
refine-aux f A u (uo3 (mkSigma A0 (mkSigma below (mkSigma i (mkSigma eqinf
  (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma (inl cst) univ))))))))) le =
  mkSigma A0 (mkSigma below
    (Eq-transport (\ z -> LeD (embed u) z)
      (Eq-sym (Eq-cong embed
        (univ A0 k refl (LeN-refl k) eqA0 (LeFTup-refl (del i A0))))) le))
-- Case 3, phi strictly increasing: extension value inf; u must be fbot p
refine-aux f A (fcpl p) (uo3 (mkSigma A0 (mkSigma below (mkSigma i (mkSigma eqinf
  (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma (inr sinc) univ))))))))) ()
refine-aux f A (fbot p) (uo3 (mkSigma A0 (mkSigma below (mkSigma i (mkSigma eqinf
  (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma (inr sinc) univ))))))))) le =
  let esc  = phi-escape k phi sinc p
      mm   = fst esc
      kle  = fst (snd esc)
      ple  = snd (snd esc)
      irng : LeN (suc i) (length A0)
      irng = Eq-transport (\ n -> LeN (suc i) n)
               (Eq-sym (Below-length below)) (get-inf-in-range i A eqinf)
      X    = repl i (fbot mm) A0
      ub   : LeD (bot mm) (get i A)
      ub   = Eq-transport (\ z -> LeD (bot mm) z) (Eq-sym eqinf) tt
      below' : Below X A
      below' = Below-repl-into i (fbot mm) A0 A below ub
      fXeq : Eq (f X) (fbot (phi mm))
      fXeq = univ X mm (length-repl i (fbot mm) A0) kle
               (getF-repl i (fbot mm) A0 irng)
               (Eq-transport (\ W -> LeFTup (del i A0) W)
                 (Eq-sym (del-repl i (fbot mm) A0)) (LeFTup-refl (del i A0)))
      leF : LeF (fbot p) (f X)
      leF = Eq-transport (\ z -> LeD (bot p) z)
              (Eq-sym (Eq-cong embed fXeq)) ple
  in mkSigma X (mkSigma below' leF)

-- top-level statement in terms of the extension
refine : (f : FTup -> FEl) (uoall : UOall f) (A : Tup) (u : FEl) ->
  LeD (embed u) (ext f uoall A) ->
  Sigma FTup (\ A0 -> Pair (Below A0 A) (LeF u (f A0)))
refine f uoall A u le = refine-aux f A u (uoall A) le
