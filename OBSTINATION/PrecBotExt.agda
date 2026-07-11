{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotExt
--
-- "Finite value below the extension": for a monotone function f with an
-- obstination witness pf at Y, every finite point Y0 <= Y has
--
--        embed (f Y0)  <=  uoValue pf.
--
-- Proof by the case of pf: join Y0 with the case witness A0 (both are
-- <= Y, hence bounded); the join lands in the case's universal region
-- (at a pinned coordinate the join absorbs, since Y0's coordinate is
-- already below A0's), so f(join) is the extension value, and
-- monotonicity gives f Y0 <= f(join).
--
-- Together with `refine` (which realises any u <= uoValue on a region)
-- this pins the EXACT value of a recursion restriction on a region --
-- the input `base-const` needs to flatten the coord-1 coupling.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotExt where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (get-embedTup ; del-LeFTup ; LeFTup-length)
open import OBSTINATION.Refine using (Below-length ; get-inf-in-range ; del-repl ; Below-repl-into)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below ; getF-joinT ; joinF-absorb-r)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot)
open import OBSTINATION.LeReassemble using (LeFTup-from-del)

------------------------------------------------------------------------
-- Below Y0 Y  ==>  length Y0 = length A0  when A0 is also Below Y
------------------------------------------------------------------------

Below-len-eq : {A0 B0 : FTup} {Y : Tup} -> Below A0 Y -> Below B0 Y ->
  Eq (length A0) (length B0)
Below-len-eq belA belB = Eq-trans (Below-length belA) (Eq-sym (Below-length belB))

-- coordinate order of two finite approximants that are pinned at i in A0
coord-le-pin : (i : Nat) {A0 Y0 : FTup} {Y : Tup} ->
  Below Y0 Y -> Eq (embed (getF i A0)) (get i Y) ->
  LeF (getF i Y0) (getF i A0)
coord-le-pin i {A0} {Y0} {Y} belY0 eqinv =
  Eq-transport (\ z -> LeD (embed (getF i Y0)) z) (Eq-sym eqinv)
    (Eq-transport (\ z -> LeD z (get i Y)) (get-embedTup i Y0) (LeTup-get i belY0))

------------------------------------------------------------------------
-- Shared Case-3 machinery: a universal point J' >= Y0 at coordinate i
-- pinned to a threshold p = max(k, q) that dominates Y0's coordinate,
-- with  f J' = fbot (phi p).
------------------------------------------------------------------------

module FcExt3 (f : FTup -> FEl)
  (mono : {X X' : FTup} -> LeFTup X X' -> LeF (f X) (f X'))
  (Y : Tup) (A0 : FTup) (belA0 : Below A0 Y) (i : Nat)
  (eqinf : Eq (get i Y) inf) (k : Nat) (eqA0 : Eq (getF i A0) (fbot k))
  (phi : Nat -> Nat)
  (univ : (X : FTup) (m : Nat) -> Eq (length X) (length A0) -> LeN k m ->
     Eq (getF i X) (fbot m) -> LeFTup (del i A0) (del i X) -> Eq (f X) (fbot (phi m)))
  (Y0 : FTup) (belY0 : Below Y0 Y)
  where

  coordY0-le : LeD (embed (getF i Y0)) inf
  coordY0-le = Eq-transport (\ z -> LeD (embed (getF i Y0)) z) eqinf
                 (Eq-transport (\ z -> LeD z (get i Y)) (get-embedTup i Y0) (LeTup-get i belY0))
  qext = le-inf-fbot (getF i Y0) coordY0-le
  q    = fst qext
  qeq  = snd qext
  p    = maxN k q
  J    = joinT Y0 A0
  bnd  = BndT-from-Below belY0 belA0
  belJ : Below J Y
  belJ = Below-joinT belY0 belA0
  irangeJ : LeN (suc i) (length J)
  irangeJ = Eq-transport (\ n -> LeN (suc i) n) (Eq-sym (Below-length belJ))
              (get-inf-in-range i Y eqinf)
  J' : FTup
  J' = repl i (fbot p) J
  fJ' : Eq (f J') (fbot (phi p))
  fJ' = univ J' p (Eq-trans (length-repl i (fbot p) J) (Eq-sym (Below-len-eq belA0 belJ)))
          (maxN-le-l k q) (getF-repl i (fbot p) J irangeJ)
          (Eq-transport (\ W -> LeFTup (del i A0) W) (Eq-sym (del-repl i (fbot p) J))
            (del-LeFTup i (join-ubT-r bnd)))
  leY0J' : LeFTup Y0 J'
  leY0J' = LeFTup-from-del i Y0 J'
    (Eq-trans (Below-length belY0)
      (Eq-sym (Eq-trans (length-repl i (fbot p) J) (Below-length belJ))))
    (Eq-transport (\ z -> LeF z (getF i J')) (Eq-sym qeq)
      (Eq-transport (\ z -> LeF (fbot q) z) (Eq-sym (getF-repl i (fbot p) J irangeJ))
        (maxN-le-r k q)))
    (Eq-transport (\ W -> LeFTup (del i Y0) W) (Eq-sym (del-repl i (fbot p) J))
      (del-LeFTup i (join-ubT-l bnd)))

------------------------------------------------------------------------
-- The bound, per case.
------------------------------------------------------------------------

fc-le-ext : (f : FTup -> FEl) ->
  ({X X' : FTup} -> LeFTup X X' -> LeF (f X) (f X')) ->
  (Y : Tup) (pf : UO f Y) (Y0 : FTup) -> Below Y0 Y ->
  LeD (embed (f Y0)) (uoValue pf)
-- Case 1: value cpl m.  f Y0 <= f(Y0 v A0) = cpl m.
fc-le-ext f mono Y (uo1 (mkSigma A0 (mkSigma belA0 (mkSigma m univ)))) Y0 belY0 =
  LeD-trans {embed (f Y0)} {embed (f J)} {cpl m}
    (mono {Y0} {J} (join-ubT-l bnd))
    (Eq-transport (\ z -> LeD (embed z) (cpl m)) (Eq-sym fJ) (LeD-refl (cpl m)))
  where
    J = joinT Y0 A0
    bnd = BndT-from-Below belY0 belA0
    fJ : Eq (f J) (fcpl m)
    fJ = univ J (join-ubT-r bnd)
-- Case 2: value bot m.  Join absorbs at coordinate i, so f(Y0 v A0) = bot m.
fc-le-ext f mono Y
  (uo2 (mkSigma A0 (mkSigma belA0 (mkSigma m (mkSigma i (mkSigma irange
    (mkSigma incompl (mkSigma eqinv univ)))))))) Y0 belY0 =
  LeD-trans {embed (f Y0)} {embed (f J)} {bot m}
    (mono {Y0} {J} (join-ubT-l bnd))
    (Eq-transport (\ z -> LeD (embed z) (bot m)) (Eq-sym fJ) (LeD-refl (bot m)))
  where
    J = joinT Y0 A0
    bnd = BndT-from-Below belY0 belA0
    lenJ-A0 : Eq (length J) (length A0)
    lenJ-A0 = Eq-trans (Below-length (Below-joinT belY0 belA0)) (Eq-sym (Below-length belA0))
    coordJ : Eq (getF i J) (getF i A0)
    coordJ = Eq-trans (getF-joinT i Y0 A0 (Below-len-eq belY0 belA0))
               (joinF-absorb-r (coord-le-pin i {A0} {Y0} {Y} belY0 eqinv))
    fJ : Eq (f J) (fbot m)
    fJ = univ J lenJ-A0 coordJ (del-LeFTup i (join-ubT-r bnd))
-- Case 3: value bot (phi k) if constant, inf if increasing.
fc-le-ext f mono Y
  (uo3 (mkSigma A0 (mkSigma belA0 (mkSigma i (mkSigma eqinf (mkSigma k
    (mkSigma eqA0 (mkSigma phi (mkSigma (inl cst) univ))))))))) Y0 belY0 =
  LeD-trans {embed (f Y0)} {embed (f J')} {bot (phi k)}
    (mono {Y0} {J'} leY0J')
    (Eq-transport (\ z -> LeD (embed z) (bot (phi k)))
      (Eq-sym (Eq-trans fJ' (Eq-cong fbot (cst p (maxN-le-l k q)))))
      (LeD-refl (bot (phi k))))
  where
    open FcExt3 f mono Y A0 belA0 i eqinf k eqA0 phi univ Y0 belY0
-- Case 3-increasing: value inf.  f Y0 is incomplete (bot j), hence <= inf.
fc-le-ext f mono Y
  (uo3 (mkSigma A0 (mkSigma belA0 (mkSigma i (mkSigma eqinf (mkSigma k
    (mkSigma eqA0 (mkSigma phi (mkSigma (inr sinc) univ))))))))) Y0 belY0 =
  bot-below (f Y0) (Eq-transport (\ z -> LeF (f Y0) z) fJ' (mono {Y0} {J'} leY0J'))
  where
    open FcExt3 f mono Y A0 belA0 i eqinf k eqA0 phi univ Y0 belY0
    bot-below : (w : FEl) -> LeF w (fbot (phi p)) -> LeD (embed w) inf
    bot-below (fbot j) le = tt
    bot-below (fcpl j) ()
