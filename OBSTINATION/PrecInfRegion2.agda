{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfRegion2
--
-- Region builder for sub-case 5 of the infinite recursion: h is Case 3 at
-- its coordinate 0 (the recursion depth), h(S^n(bot), r, X) = S^{phi(n)}
-- (bot).  Then f(S^{n+1}(bot), X) = S^{phi(n)}(bot), so f is Case 3 at its
-- OWN coordinate 0, with witness function  psi(p) = phi(p-1)  (min1.pdf
-- p.4).  The value computation is `f-depth`; the witness function's
-- PhiOK is `phipred-ok`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfRegion2 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.PrecInf using (f-depth ; f-const)
open import OBSTINATION.PrecFun using (RecData ; PF)

------------------------------------------------------------------------
-- predecessor, and the witness function phi(p-1)
------------------------------------------------------------------------

pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n

pred-ge : (n0s p : Nat) -> LeN (suc n0s) p -> LeN n0s (pred p)
pred-ge n0s zero    ()
pred-ge n0s (suc p) le = le

phipred-ok : (phi : Nat -> Nat) (kc n0s : Nat) -> LeN kc n0s ->
  PhiOK kc phi -> PhiOK (suc n0s) (\ p -> phi (pred p))
phipred-ok phi kc n0s kcn0s (inl cst) = inl cst'
  where
    cst' : ConstFrom (suc n0s) (\ p -> phi (pred p))
    cst' p le =
      Eq-trans (cst (pred p) (LeN-trans {kc} {n0s} {pred p} kcn0s (pred-ge n0s p le)))
        (Eq-sym (cst n0s kcn0s))
phipred-ok phi kc n0s kcn0s (inr sinc) = inr sinc'
  where
    sinc' : StrictIncFrom (suc n0s) (\ p -> phi (pred p))
    sinc' zero    ()
    sinc' (suc p) le = sinc p (LeN-trans {kc} {n0s} {p} kcn0s le)

------------------------------------------------------------------------
-- Sub-case 5 region builder
------------------------------------------------------------------------

module _ (rd : RecData) where
  open RecData rd

  prec-inf-Case3Depth-region : (phi : Nat -> Nat) (n0 k0 kc : Nat)
    (Y0 : FTup) (Y : Tup) ->
    Below Y0 Y ->
    PhiOK kc phi ->
    (reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))) ->
    (hgerm : (n : Nat) (r : FEl) (X : FTup) -> LeN kc n -> LeD (bot k0) (embed r) ->
               LeFTup Y0 X -> Eq (H (cons (fbot n) (cons r X))) (fbot (phi n))) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Case3Depth-region phi n0 k0 kc Y0 Y belY0 phiok reach hgerm =
    uo3 (mkSigma (cons (fbot (suc n0s)) Y0)
          (mkSigma (mkSigma tt belY0)
            (mkSigma zero (mkSigma refl (mkSigma (suc n0s) (mkSigma refl
              (mkSigma psif (mkSigma psifok univ))))))))
    where
      n0s = maxN n0 kc
      psif : Nat -> Nat
      psif p = phi (pred p)
      psifok : PhiOK (suc n0s) psif
      psifok = phipred-ok phi kc n0s (maxN-le-r n0 kc) phiok
      univ : (W : FTup) (p : Nat) ->
             Eq (length W) (length (cons (fbot (suc n0s)) Y0)) ->
             LeN (suc n0s) p -> Eq (getF zero W) (fbot p) ->
             LeFTup (del zero (cons (fbot (suc n0s)) Y0)) (del zero W) ->
             Eq (PF G H W) (fbot (psif p))
      univ nil p ()
      univ (cons a X') zero    lenW ()
      univ (cons a X') (suc n') lenW pk coordW delW =
        Eq-transport (\ z -> Eq (PF G H (cons z X')) (fbot (phi n')))
          (Eq-sym coordW)
          (f-depth rd phi n0s k0 X' reach'' hgerm'' n' pk)
        where
          reach'' : (b : FEl) -> LeF (fbot n0s) b ->
                    LeD (bot k0) (embed (PF G H (cons b X')))
          reach'' b lb = reach b X'
            (LeD-trans {bot n0} {bot n0s} {embed b} (maxN-le-l n0 kc) lb) delW
          hgerm'' : (n : Nat) (r : FEl) -> LeN n0s n -> LeD (bot k0) (embed r) ->
                    Eq (H (cons (fbot n) (cons r X'))) (fbot (phi n))
          hgerm'' n r ln lr =
            hgerm n r X' (LeN-trans {kc} {n0s} {n} (maxN-le-r n0 kc) ln) lr delW

  ------------------------------------------------------------------------
  -- Constant-value coordinate-0 builder: h is eventually constant S^m(bot)
  -- on the region (h Case 1-incomplete-ish: value fixed by coord 0 or the
  -- recursion result with a CONSTANT phi).  Then f is Case 3-constant at
  -- its coordinate 0.  Covers sub-case 4 with phi constant, and the
  -- incomplete-value first principal case with a coordinate-0 controller.
  ------------------------------------------------------------------------

  prec-inf-Const0-region : (m n0 k0 : Nat) (Y0 : FTup) (Y : Tup) ->
    Below Y0 Y ->
    (reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))) ->
    (hgerm : (a r : FEl) (X : FTup) -> LeF (fbot n0) a -> LeD (bot k0) (embed r) ->
               LeFTup Y0 X -> Eq (H (cons a (cons r X))) (fbot m)) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Const0-region m n0 k0 Y0 Y belY0 reach hgerm =
    uo3 (mkSigma (cons (fbot (suc n0)) Y0)
          (mkSigma (mkSigma tt belY0)
            (mkSigma zero (mkSigma refl (mkSigma (suc n0) (mkSigma refl
              (mkSigma (\ _ -> m) (mkSigma (inl (\ _ _ -> refl)) univ))))))))
    where
      univ : (W : FTup) (p : Nat) ->
             Eq (length W) (length (cons (fbot (suc n0)) Y0)) ->
             LeN (suc n0) p -> Eq (getF zero W) (fbot p) ->
             LeFTup (del zero (cons (fbot (suc n0)) Y0)) (del zero W) ->
             Eq (PF G H W) (fbot m)
      univ nil p ()
      univ (cons a X') p lenW pk coordW delW =
        f-const rd (fbot m) n0 k0 X'
          (\ b lb -> reach b X' lb delW)
          (\ b r lb lr -> hgerm b r X' lb lr delW)
          a (Eq-transport (\ z -> LeF (fbot (suc n0)) z) (Eq-sym coordW) pk)

