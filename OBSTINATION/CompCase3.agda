{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.CompCase3
--
-- Composition, the Case-3 branch (phi-class closed under composition).
-- If g is in Case 3 at the inner point B = <ext f_j A>, then its witness
-- coordinate i has B(i) = inf, so the i-th inner function f_i is itself
-- in Case 3-increasing at A, with witness coordinate i' and function
-- phi_H.  The composite g o <f_1,...,f_k> is then in Case 3 at A, at
-- coordinate i', with  phi_F = phi_G o phi_H.
--
-- The witness A0F sets coordinate i' to S^{k_F}(bot) over the join of
-- the pull-back approximant (for the other inner coordinates) and f_i's
-- own approximant; the threshold k_F is chosen (via phi-escape) so that
-- phi_H(p) >= k_G for p >= k_F.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.CompCase3 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.Extension using (get-embedTup ; del-LeFTup)
open import OBSTINATION.CompPull using
  (UOFun ; mapU ; innerPtU ; compFn ; pullback ; LeFTup-trans)
open import OBSTINATION.CompIndex using (nthFn ; nthUO ; index-innerU ; length-innerPtU)
open import OBSTINATION.CompMapE using (getF-mapU ; length-mapU)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.PhiComp using (sinc-mono-le ; sinc-mono-lt)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below)
open import OBSTINATION.Refine using (Below-repl-into ; del-repl ; Below-length ; get-inf-in-range)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)
open import OBSTINATION.LeReassemble using (LeFTup-from-del)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot ; Case3Inr ; extract-inr)

------------------------------------------------------------------------
-- The Case-3 branch, given f_i's Case-3-increasing data (case3-body),
-- assembled from g's Case-3 data at the inner point (comp-Case3-build).
------------------------------------------------------------------------

case3-body : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup)
  (B0 : FTup) (belowB : Below B0 (innerPtU fs A)) (i : Nat)
  (eqinfB : Eq (get i (innerPtU fs A)) inf) (kG : Nat)
  (eqB0 : Eq (getF i B0) (fbot kG)) (phiG : Nat -> Nat)
  (phiokG : PhiOK kG phiG)
  (univG : (Y : FTup) (m : Nat) -> Eq (length Y) (length B0) ->
             LeN kG m -> Eq (getF i Y) (fbot m) ->
             LeFTup (del i B0) (del i Y) -> Eq (gf Y) (fbot (phiG m)))
  (i-lt : LeN (suc i) (length fs)) ->
  Case3Inr (nthFn i fs) A ->
  Case3 (compFn gf fs) A
case3-body gf fs A B0 belowB i eqinfB kG eqB0 phiG phiokG univG i-lt
  (mkSigma A0H (mkSigma belowH (mkSigma i' (mkSigma eqinfA
    (mkSigma kH (mkSigma eqA0H (mkSigma phiH (mkSigma sincH univH)))))))) =
  mkSigma A0F (mkSigma belowA0F (mkSigma i' (mkSigma eqinfA
    (mkSigma kF (mkSigma eqA0F (mkSigma phiF (mkSigma phiokF univF)))))))
  where
    lenB-hs = length-innerPtU fs A
    esc   = phi-escape kH phiH sincH kG
    p0    = fst esc
    kH-p0 = fst (snd esc)
    kG-p0 = snd (snd esc)
    pb      = pullback fs A B0 belowB
    A0p     = fst pb
    below-p = fst (snd pb)
    pull    = snd (snd pb)
    coordA0p-le : LeD (embed (getF i' A0p)) inf
    coordA0p-le =
      Eq-transport (\ z -> LeD (embed (getF i' A0p)) z) eqinfA
        (Eq-transport (\ z -> LeD z (get i' A)) (get-embedTup i' A0p)
          (LeTup-get i' below-p))
    qext = le-inf-fbot (getF i' A0p) coordA0p-le
    q    = fst qext
    qeq  = snd qext
    kF   = maxN p0 q
    phiF : Nat -> Nat
    phiF p = phiG (phiH p)
    JT      = joinT A0p A0H
    bndpH   = BndT-from-Below below-p belowH
    belowJT = Below-joinT below-p belowH
    i'-ltJT : LeN (suc i') (length JT)
    i'-ltJT = Eq-transport (\ n -> LeN (suc i') n) (Eq-sym (Below-length belowJT))
                (get-inf-in-range i' A eqinfA)
    A0F   = repl i' (fbot kF) JT
    eqA0F = getF-repl i' (fbot kF) JT i'-ltJT
    ubkF : LeD (bot kF) (get i' A)
    ubkF = Eq-transport (\ z -> LeD (bot kF) z) (Eq-sym eqinfA) tt
    belowA0F = Below-repl-into i' (fbot kF) JT A belowJT ubkF
    lenA0F-A = Eq-trans (length-repl i' (fbot kF) JT) (Below-length belowJT)
    phiH-ge-kG : (p : Nat) -> LeN kF p -> LeN kG (phiH p)
    phiH-ge-kG p pkF =
      LeN-trans {kG} {phiH p0} {phiH p} kG-p0
        (sinc-mono-le kH phiH sincH p0 p kH-p0 (LeN-trans {p0} {kF} {p} (maxN-le-l p0 q) pkF))
    univF : (X : FTup) (p : Nat) -> Eq (length X) (length A0F) ->
            LeN kF p -> Eq (getF i' X) (fbot p) ->
            LeFTup (del i' A0F) (del i' X) ->
            Eq (compFn gf fs X) (fbot (phiF p))
    univF X p lenX pkF coordX delX =
      univG (mapU fs X) (phiH p) lenMap-B0 (phiH-ge-kG p pkF) gmap delB0-map
      where
        p-ge-p0 = LeN-trans {p0} {kF} {p} (maxN-le-l p0 q) pkF
        p-ge-q  = LeN-trans {q} {kF} {p} (maxN-le-r p0 q) pkF
        p-ge-kH = LeN-trans {kH} {p0} {p} kH-p0 p-ge-p0
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
        hiX = univH X p (Eq-trans lenX-A (Eq-sym (Below-length belowH)))
                p-ge-kH coordX delA0H-X
        gmap = Eq-trans (getF-mapU i fs X i-lt) hiX
        delB0-map = del-LeFTup i (pull X X-ge-A0p)
        lenMap-B0 = Eq-trans (length-mapU fs X)
                      (Eq-sym (Eq-trans (Below-length belowB) lenB-hs))
    phiokF : PhiOK kF phiF
    phiokF = phiokF-build phiokG
      where
        phiokF-build : PhiOK kG phiG -> PhiOK kF phiF
        phiokF-build (inl cstG) = inl (\ p pkF ->
          Eq-trans (cstG (phiH p) (phiH-ge-kG p pkF))
            (Eq-sym (cstG (phiH kF) (phiH-ge-kG kF (LeN-refl kF)))))
        phiokF-build (inr sincG) = inr (\ p pkF ->
          sinc-mono-lt kG phiG sincG (phiH p) (phiH (suc p))
            (phiH-ge-kG p pkF)
            (sincH p (LeN-trans {kH} {p0} {p} kH-p0
              (LeN-trans {p0} {kF} {p} (maxN-le-l p0 q) pkF))))

comp-Case3-build : (gf : FTup -> FEl) (fs : List UOFun) (A : Tup) ->
  Case3 gf (innerPtU fs A) ->
  Case3 (compFn gf fs) A
comp-Case3-build gf fs A
  (mkSigma B0 (mkSigma belowB (mkSigma i (mkSigma eqinfB
    (mkSigma kG (mkSigma eqB0 (mkSigma phiG (mkSigma phiokG univG)))))))) =
  case3-body gf fs A B0 belowB i eqinfB kG eqB0 phiG phiokG univG
    i-lt (extract-inr (nthFn i fs) A (nthUO i fs A) ext-hi-inf)
  where
    lenB-hs = length-innerPtU fs A
    i-lt : LeN (suc i) (length fs)
    i-lt = Eq-transport (\ n -> LeN (suc i) n) lenB-hs
             (get-inf-in-range i (innerPtU fs A) eqinfB)
    ext-hi-inf : Eq (uoValue (nthUO i fs A)) inf
    ext-hi-inf = Eq-trans (Eq-sym (index-innerU i fs A i-lt)) eqinfB
