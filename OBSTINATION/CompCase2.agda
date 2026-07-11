{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompCase2
--
-- Composition, the Case-2 branch.  g is eventually constant incomplete
-- (value S^m(bot)) at inner coordinate i, so f_i's extension at A is
-- finite incomplete: f_i is in Case 2 (finite witness coordinate i',
-- -> composite Case 2) or Case 3-constant (infinite witness coordinate
-- i', -> composite Case 3-constant), both with the same value S^m(bot).
-- Case 1 (complete) and Case 3-increasing (inf) are excluded by the
-- incomplete-finite value.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompCase2 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (get-embedTup ; del-LeFTup ; embed-inj)
open import OBSTINATION.CompPull using
  (UOFun ; mapU ; innerPtU ; compFn ; pullback ; LeFTup-trans)
open import OBSTINATION.CompIndex using (nthFn ; nthUO ; index-innerU ; length-innerPtU)
open import OBSTINATION.CompMapE using (getF-mapU ; length-mapU)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below ; getF-joinT ; joinF-absorb-r)
open import OBSTINATION.Refine using (Below-repl-into ; del-repl ; Below-length ; get-inf-in-range)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)
open import OBSTINATION.LeReassemble using (LeFTup-from-del)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot)

------------------------------------------------------------------------
-- Sub-case: f_i in Case 2  ->  composite in Case 2
------------------------------------------------------------------------

case2-from-uo2 : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup)
  (B0 : FTup) (belowB : Below B0 (innerPtU fs A)) (m i : Nat)
  (i-lt : LeN (suc i) (length fs))
  (univG : (Y : FTup) -> Eq (length Y) (length B0) -> Eq (getF i Y) (getF i B0) ->
             LeFTup (del i B0) (del i Y) -> Eq (gf Y) (fbot m))
  (A0H : FTup) (belowH : Below A0H A) (mHH i' : Nat)
  (i'-rangeH : LeN (suc i') (length A0H))
  (incomplH : IncompleteFinite (get i' A))
  (eqA0Hinv : Eq (embed (getF i' A0H)) (get i' A))
  (univH : (X : FTup) -> Eq (length X) (length A0H) -> Eq (getF i' X) (getF i' A0H) ->
             LeFTup (del i' A0H) (del i' X) -> Eq (nthFn i fs X) (fbot mHH))
  (iB0eq : Eq (getF i B0) (fbot mHH)) ->
  Case2 (compFn gf fs) A
case2-from-uo2 gf fs A B0 belowB m i i-lt univG
  A0H belowH mHH i' i'-rangeH incomplH eqA0Hinv univH iB0eq =
  mkSigma A0F (mkSigma belowJT
    (mkSigma m (mkSigma i' (mkSigma i'-range (mkSigma incomplH (mkSigma eqA0Finv univF))))))
  where
    pb      = pullback fs A B0 belowB
    A0p     = fst pb
    below-p = fst (snd pb)
    pull    = snd (snd pb)
    A0F     = joinT A0p A0H
    bndpH   = BndT-from-Below below-p belowH
    belowJT = Below-joinT below-p belowH
    lenAp-AH = Eq-trans (Below-length below-p) (Eq-sym (Below-length belowH))
    A0p-le-A0H : LeF (getF i' A0p) (getF i' A0H)
    A0p-le-A0H =
      Eq-transport (\ z -> LeD (embed (getF i' A0p)) z) (Eq-sym eqA0Hinv)
        (Eq-transport (\ z -> LeD z (get i' A)) (get-embedTup i' A0p) (LeTup-get i' below-p))
    getF-A0F : Eq (getF i' A0F) (getF i' A0H)
    getF-A0F = Eq-trans (getF-joinT i' A0p A0H lenAp-AH) (joinF-absorb-r A0p-le-A0H)
    i'-range : LeN (suc i') (length A0F)
    i'-range = Eq-transport (\ n -> LeN (suc i') n)
                 (Eq-trans (Below-length belowH) (Eq-sym (Below-length belowJT))) i'-rangeH
    eqA0Finv : Eq (embed (getF i' A0F)) (get i' A)
    eqA0Finv = Eq-trans (Eq-cong embed getF-A0F) eqA0Hinv
    univF : (X : FTup) -> Eq (length X) (length A0F) -> Eq (getF i' X) (getF i' A0F) ->
            LeFTup (del i' A0F) (del i' X) -> Eq (compFn gf fs X) (fbot m)
    univF X lenX coordX delX =
      univG (mapU fs X) lenMap-B0 gmap delB0-map
      where
        coordX'  = Eq-trans coordX getF-A0F
        delA0p-X = LeFTup-trans (del-LeFTup i' (join-ubT-l bndpH)) delX
        delA0H-X = LeFTup-trans (del-LeFTup i' (join-ubT-r bndpH)) delX
        coordA0p-X : LeF (getF i' A0p) (getF i' X)
        coordA0p-X = Eq-transport (\ z -> LeF (getF i' A0p) z) (Eq-sym coordX') A0p-le-A0H
        lenX-A   = Eq-trans lenX (Below-length belowJT)
        lenX-A0p = Eq-trans (Below-length below-p) (Eq-sym lenX-A)
        X-ge-A0p = LeFTup-from-del i' A0p X lenX-A0p coordA0p-X delA0p-X
        hiX  = univH X (Eq-trans lenX-A (Eq-sym (Below-length belowH))) coordX' delA0H-X
        gmap = Eq-trans (getF-mapU i fs X i-lt) (Eq-trans hiX (Eq-sym iB0eq))
        delB0-map = del-LeFTup i (pull X X-ge-A0p)
        lenMap-B0 = Eq-trans (length-mapU fs X)
                      (Eq-sym (Eq-trans (Below-length belowB) (length-innerPtU fs A)))

------------------------------------------------------------------------
-- Sub-case: f_i in Case 3-constant  ->  composite in Case 3-constant
------------------------------------------------------------------------

case2-from-uo3inl : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup)
  (B0 : FTup) (belowB : Below B0 (innerPtU fs A)) (m i : Nat)
  (i-lt : LeN (suc i) (length fs))
  (univG : (Y : FTup) -> Eq (length Y) (length B0) -> Eq (getF i Y) (getF i B0) ->
             LeFTup (del i B0) (del i Y) -> Eq (gf Y) (fbot m))
  (A0H : FTup) (belowH : Below A0H A) (i' : Nat)
  (eqinfH : Eq (get i' A) inf) (kH : Nat) (eqA0H : Eq (getF i' A0H) (fbot kH))
  (phiH : Nat -> Nat) (cstH : ConstFrom kH phiH)
  (univH : (X : FTup) (p : Nat) -> Eq (length X) (length A0H) -> LeN kH p ->
             Eq (getF i' X) (fbot p) -> LeFTup (del i' A0H) (del i' X) ->
             Eq (nthFn i fs X) (fbot (phiH p)))
  (iB0eq : Eq (getF i B0) (fbot (phiH kH))) ->
  Case3 (compFn gf fs) A
case2-from-uo3inl gf fs A B0 belowB m i i-lt univG
  A0H belowH i' eqinfH kH eqA0H phiH cstH univH iB0eq =
  mkSigma A0F (mkSigma belowA0F (mkSigma i' (mkSigma eqinfH
    (mkSigma kF (mkSigma eqA0F (mkSigma (\ _ -> m) (mkSigma (inl (\ _ _ -> refl)) univF)))))))
  where
    pb      = pullback fs A B0 belowB
    A0p     = fst pb
    below-p = fst (snd pb)
    pull    = snd (snd pb)
    coordA0p-le : LeD (embed (getF i' A0p)) inf
    coordA0p-le =
      Eq-transport (\ z -> LeD (embed (getF i' A0p)) z) eqinfH
        (Eq-transport (\ z -> LeD z (get i' A)) (get-embedTup i' A0p) (LeTup-get i' below-p))
    qext = le-inf-fbot (getF i' A0p) coordA0p-le
    q    = fst qext
    qeq  = snd qext
    kF   = maxN kH q
    JT      = joinT A0p A0H
    bndpH   = BndT-from-Below below-p belowH
    belowJT = Below-joinT below-p belowH
    i'-ltJT : LeN (suc i') (length JT)
    i'-ltJT = Eq-transport (\ n -> LeN (suc i') n) (Eq-sym (Below-length belowJT))
                (get-inf-in-range i' A eqinfH)
    A0F   = repl i' (fbot kF) JT
    eqA0F = getF-repl i' (fbot kF) JT i'-ltJT
    belowA0F = Below-repl-into i' (fbot kF) JT A belowJT
                 (Eq-transport (\ z -> LeD (bot kF) z) (Eq-sym eqinfH) tt)
    lenA0F-A = Eq-trans (length-repl i' (fbot kF) JT) (Below-length belowJT)
    univF : (X : FTup) (p : Nat) -> Eq (length X) (length A0F) -> LeN kF p ->
            Eq (getF i' X) (fbot p) -> LeFTup (del i' A0F) (del i' X) ->
            Eq (compFn gf fs X) (fbot m)
    univF X p lenX pkF coordX delX =
      univG (mapU fs X) lenMap-B0 gmap delB0-map
      where
        p-ge-kH = LeN-trans {kH} {kF} {p} (maxN-le-l kH q) pkF
        p-ge-q  = LeN-trans {q} {kF} {p} (maxN-le-r kH q) pkF
        delJT : LeFTup (del i' JT) (del i' X)
        delJT = Eq-transport (\ W -> LeFTup W (del i' X)) (del-repl i' (fbot kF) JT) delX
        delA0p-X = LeFTup-trans (del-LeFTup i' (join-ubT-l bndpH)) delJT
        delA0H-X = LeFTup-trans (del-LeFTup i' (join-ubT-r bndpH)) delJT
        coordA0p-X : LeF (getF i' A0p) (getF i' X)
        coordA0p-X =
          Eq-transport (\ z -> LeF (getF i' A0p) z) (Eq-sym coordX)
            (Eq-transport (\ z -> LeF z (fbot p)) (Eq-sym qeq) p-ge-q)
        lenX-A   = Eq-trans lenX lenA0F-A
        lenX-A0p = Eq-trans (Below-length below-p) (Eq-sym lenX-A)
        X-ge-A0p = LeFTup-from-del i' A0p X lenX-A0p coordA0p-X delA0p-X
        hiX  = univH X p (Eq-trans lenX-A (Eq-sym (Below-length belowH))) p-ge-kH coordX delA0H-X
        hiX' = Eq-trans hiX (Eq-cong fbot (cstH p p-ge-kH))
        gmap = Eq-trans (getF-mapU i fs X i-lt) (Eq-trans hiX' (Eq-sym iB0eq))
        delB0-map = del-LeFTup i (pull X X-ge-A0p)
        lenMap-B0 = Eq-trans (length-mapU fs X)
                      (Eq-sym (Eq-trans (Below-length belowB) (length-innerPtU fs A)))

------------------------------------------------------------------------
-- Dispatch on f_i's obstination, then assemble.
------------------------------------------------------------------------

case2-body : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup)
  (B0 : FTup) (belowB : Below B0 (innerPtU fs A)) (m i : Nat)
  (i-lt : LeN (suc i) (length fs))
  (univG : (Y : FTup) -> Eq (length Y) (length B0) -> Eq (getF i Y) (getF i B0) ->
             LeFTup (del i B0) (del i Y) -> Eq (gf Y) (fbot m))
  (pf : UO (nthFn i fs) A) ->
  IncompleteFinite (uoValue pf) ->
  Eq (embed (getF i B0)) (uoValue pf) ->
  UO (compFn gf fs) A
case2-body gf fs A B0 belowB m i i-lt univG
  (uo1 (mkSigma _ (mkSigma _ (mkSigma m1 _)))) incf vc = Empty-elim incf
case2-body gf fs A B0 belowB m i i-lt univG
  (uo2 (mkSigma A0H (mkSigma belowH (mkSigma mHH (mkSigma i' (mkSigma i'-rangeH
    (mkSigma incomplH (mkSigma eqA0Hinv univH)))))))) incf vc =
  uo2 (case2-from-uo2 gf fs A B0 belowB m i i-lt univG
         A0H belowH mHH i' i'-rangeH incomplH eqA0Hinv univH (embed-inj vc))
case2-body gf fs A B0 belowB m i i-lt univG
  (uo3 (mkSigma A0H (mkSigma belowH (mkSigma i' (mkSigma eqinfH
    (mkSigma kH (mkSigma eqA0H (mkSigma phiH (mkSigma (inl cstH) univH))))))))) incf vc =
  uo3 (case2-from-uo3inl gf fs A B0 belowB m i i-lt univG
         A0H belowH i' eqinfH kH eqA0H phiH cstH univH (embed-inj vc))
case2-body gf fs A B0 belowB m i i-lt univG
  (uo3 (mkSigma A0H (mkSigma belowH (mkSigma i' (mkSigma eqinfH
    (mkSigma kH (mkSigma eqA0H (mkSigma phiH (mkSigma (inr sincH) univH))))))))) incf vc =
  Empty-elim incf

comp-Case2-build : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup) ->
  Case2 gf (innerPtU fs A) ->
  UO (compFn gf fs) A
comp-Case2-build gf fs A
  (mkSigma B0 (mkSigma belowB (mkSigma m (mkSigma i (mkSigma i-range
    (mkSigma incomplB (mkSigma eqB0inv univG))))))) =
  case2-body gf fs A B0 belowB m i i-lt univG (nthUO i fs A) incf vc
  where
    i-lt : LeN (suc i) (length fs)
    i-lt = Eq-transport (\ n -> LeN (suc i) n)
             (Eq-trans (Below-length belowB) (length-innerPtU fs A)) i-range
    incf : IncompleteFinite (uoValue (nthUO i fs A))
    incf = Eq-transport IncompleteFinite (index-innerU i fs A i-lt) incomplB
    vc : Eq (embed (getF i B0)) (uoValue (nthUO i fs A))
    vc = Eq-trans eqB0inv (index-innerU i fs A i-lt)
