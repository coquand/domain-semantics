{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.ExtMono
--
-- Monotonicity of the Scott-continuous extension read off the ultimate-
-- obstination property (min1.pdf p.2: "on peut calculer l'extension
-- Scott-continue de f").  If  A <= B  in D^n then  ext f A <= ext f B.
--
-- Two ingredients:
--   * ext-ub : for a finite A0 <= A,  f A0 <= ext f A.  Proved per case
--     of the property by joining A0 with the case witness A1: their join
--     J is finite, still <= A, and >= A0, and lands inside the region on
--     which the universal clause fixes f J to the extension value; then
--     f A0 <= f J by monotonicity.  (At the pinned coordinate the join
--     absorbs to the witness because A0's coordinate is already <= it.)
--   * refine (compactness) gives, for finite u <= ext f A, a finite
--     A0 <= A with u <= f A0.
-- Together with the finite-approximation principle LeD-from-finite (an
-- element of D is determined by the finite elements below it), these give
-- ext-mono, the prerequisite for the fixpoint-sequence argument (the
-- infinite / incomplete-finite recursion argument).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.ExtMono where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (ext ; get-embedTup ; del-LeFTup)
open import OBSTINATION.Refine using (refine ; Below-length)
open import OBSTINATION.Meet using (joinT ; joinF ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using
  (BndT-from-Below ; Below-joinT ; getF-joinT ; joinF-absorb-r)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot)
open import OBSTINATION.CompPull using (Mono)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

-- below an incomplete finite element there are no complete elements
le-inf-any : (w : FEl) (p : Nat) -> LeD (embed w) (bot p) -> LeD (embed w) inf
le-inf-any (fbot k) p le = tt
le-inf-any (fcpl k) p ()

-- the length of a join of equal-length tuples
length-joinT : (A0 A1 : FTup) -> Eq (length A0) (length A1) ->
  Eq (length (joinT A0 A1)) (length A1)
length-joinT nil         nil         leq = refl
length-joinT nil         (cons _ _)  ()
length-joinT (cons _ _)  nil         ()
length-joinT (cons a A0) (cons b A1) leq = Eq-cong suc (length-joinT A0 A1 (suc-inj leq))

LeN-suc-not : (l : Nat) -> Not (LeN (suc l) l)
LeN-suc-not zero     = \ ()
LeN-suc-not (suc l') = LeN-suc-not l'

-- an element of D is determined by the finite elements below it
LeD-from-finite : (d e : D) ->
  ((u : FEl) -> LeD (embed u) d -> LeD (embed u) e) -> LeD d e
LeD-from-finite (bot k) e h = h (fbot k) (LeN-refl k)
LeD-from-finite (cpl k) e h = h (fcpl k) refl
LeD-from-finite inf (bot l) h = Empty-elim (LeN-suc-not l (h (fbot (suc l)) tt))
LeD-from-finite inf (cpl l) h = Empty-elim (LeN-suc-not l (h (fbot (suc l)) tt))
LeD-from-finite inf inf     h = tt

------------------------------------------------------------------------
-- ext is an upper bound of f over finite approximants
------------------------------------------------------------------------

ext-ub-aux : (f : FTup -> FEl) -> Mono f -> (A : Tup) (A0 : FTup) ->
  Below A0 A -> (pf : UO f A) -> LeD (embed (f A0)) (uoValue pf)
-- Case 1
ext-ub-aux f mono A A0 below0 (uo1 (mkSigma A1 (mkSigma below1 (mkSigma m univ)))) =
  Eq-transport (\ z -> LeD (embed (f A0)) z)
    (Eq-cong embed (univ (joinT A0 A1) (join-ubT-r bnd)))
    (mono {A0} {joinT A0 A1} (join-ubT-l bnd))
  where
    bnd = BndT-from-Below below0 below1
-- Case 2
ext-ub-aux f mono A A0 below0
  (uo2 (mkSigma A1 (mkSigma below1 (mkSigma m (mkSigma i (mkSigma irange
    (mkSigma incompl (mkSigma eqA0inv univ)))))))) =
  Eq-transport (\ z -> LeD (embed (f A0)) z)
    (Eq-cong embed (univ J lenJA1 getFiJ delA1J))
    (mono {A0} {J} (join-ubT-l bnd))
  where
    bnd = BndT-from-Below below0 below1
    J   = joinT A0 A1
    lenA01 : Eq (length A0) (length A1)
    lenA01 = Eq-trans (Below-length below0) (Eq-sym (Below-length below1))
    coordA0-le-A1 : LeF (getF i A0) (getF i A1)
    coordA0-le-A1 =
      Eq-transport (\ z -> LeD (embed (getF i A0)) z) (Eq-sym eqA0inv)
        (Eq-transport (\ z -> LeD z (get i A)) (get-embedTup i A0) (LeTup-get i below0))
    getFiJ : Eq (getF i J) (getF i A1)
    getFiJ = Eq-trans (getF-joinT i A0 A1 lenA01) (joinF-absorb-r coordA0-le-A1)
    lenJA1 : Eq (length J) (length A1)
    lenJA1 = length-joinT A0 A1 lenA01
    delA1J : LeFTup (del i A1) (del i J)
    delA1J = del-LeFTup i (join-ubT-r bnd)
-- Case 3, phi constant
ext-ub-aux f mono A A0 below0
  (uo3 (mkSigma A1 (mkSigma below1 (mkSigma i (mkSigma eqinf (mkSigma k (mkSigma eqA0
    (mkSigma phi (mkSigma (inl cst) univ))))))))) =
  Eq-transport (\ z -> LeD (embed (f A0)) (bot z)) (cst p kp)
    (Eq-transport (\ z -> LeD (embed (f A0)) z)
      (Eq-cong embed (univ J p lenJA1 kp getFiJ delA1J))
      (mono {A0} {J} (join-ubT-l bnd)))
  where
    bnd = BndT-from-Below below0 below1
    J   = joinT A0 A1
    lenA01 : Eq (length A0) (length A1)
    lenA01 = Eq-trans (Below-length below0) (Eq-sym (Below-length below1))
    sext : Sigma Nat (\ s -> Eq (getF i A0) (fbot s))
    sext = le-inf-fbot (getF i A0)
      (Eq-transport (\ z -> LeD (embed (getF i A0)) z) eqinf
        (Eq-transport (\ z -> LeD z (get i A)) (get-embedTup i A0) (LeTup-get i below0)))
    s = fst sext
    p = maxN s k
    kp : LeN k p
    kp = maxN-le-r s k
    getFiJ : Eq (getF i J) (fbot p)
    getFiJ = Eq-trans (getF-joinT i A0 A1 lenA01)
               (Eq-trans (Eq-cong (\ a -> joinF a (getF i A1)) (snd sext))
                         (Eq-cong (\ b -> joinF (fbot s) b) eqA0))
    lenJA1 : Eq (length J) (length A1)
    lenJA1 = length-joinT A0 A1 lenA01
    delA1J : LeFTup (del i A1) (del i J)
    delA1J = del-LeFTup i (join-ubT-r bnd)
-- Case 3, phi strictly increasing (extension value inf)
ext-ub-aux f mono A A0 below0
  (uo3 (mkSigma A1 (mkSigma below1 (mkSigma i (mkSigma eqinf (mkSigma k (mkSigma eqA0
    (mkSigma phi (mkSigma (inr sinc) univ))))))))) =
  le-inf-any (f A0) (phi p)
    (Eq-transport (\ z -> LeD (embed (f A0)) z)
      (Eq-cong embed (univ J p lenJA1 kp getFiJ delA1J))
      (mono {A0} {J} (join-ubT-l bnd)))
  where
    bnd = BndT-from-Below below0 below1
    J   = joinT A0 A1
    lenA01 : Eq (length A0) (length A1)
    lenA01 = Eq-trans (Below-length below0) (Eq-sym (Below-length below1))
    sext : Sigma Nat (\ s -> Eq (getF i A0) (fbot s))
    sext = le-inf-fbot (getF i A0)
      (Eq-transport (\ z -> LeD (embed (getF i A0)) z) eqinf
        (Eq-transport (\ z -> LeD z (get i A)) (get-embedTup i A0) (LeTup-get i below0)))
    s = fst sext
    p = maxN s k
    kp : LeN k p
    kp = maxN-le-r s k
    getFiJ : Eq (getF i J) (fbot p)
    getFiJ = Eq-trans (getF-joinT i A0 A1 lenA01)
               (Eq-trans (Eq-cong (\ a -> joinF a (getF i A1)) (snd sext))
                         (Eq-cong (\ b -> joinF (fbot s) b) eqA0))
    lenJA1 : Eq (length J) (length A1)
    lenJA1 = length-joinT A0 A1 lenA01
    delA1J : LeFTup (del i A1) (del i J)
    delA1J = del-LeFTup i (join-ubT-r bnd)

ext-ub : (f : FTup -> FEl) (mono : Mono f) (uoall : UOall f) (A : Tup)
  (A0 : FTup) -> Below A0 A -> LeD (embed (f A0)) (ext f uoall A)
ext-ub f mono uoall A A0 below0 = ext-ub-aux f mono A A0 below0 (uoall A)

------------------------------------------------------------------------
-- Monotonicity of the extension
------------------------------------------------------------------------

ext-mono : (f : FTup -> FEl) (mono : Mono f) (uoall : UOall f) {A B : Tup} ->
  LeTup A B -> LeD (ext f uoall A) (ext f uoall B)
ext-mono f mono uoall {A} {B} leAB =
  LeD-from-finite (ext f uoall A) (ext f uoall B) go
  where
    go : (u : FEl) -> LeD (embed u) (ext f uoall A) -> LeD (embed u) (ext f uoall B)
    go u ule =
      LeD-trans {embed u} {embed (f A0)} {ext f uoall B}
        u-le-fA0 (ext-ub f mono uoall B A0 belA0B)
      where
        r        = refine f uoall A u ule
        A0       = fst r
        belA0A   = fst (snd r)
        u-le-fA0 = snd (snd r)
        belA0B : Below A0 B
        belA0B = LeTup-trans {embedTup A0} {A} {B} belA0A leAB
