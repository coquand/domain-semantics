{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfRegion
--
-- Region builders for the infinite-recursion case: given that h's germ
-- takes a prescribed value on the region (a "regional hgerm"), build f's
-- ultimate-obstination witness at (S^omega(bot), Y).  Each builder just
-- pins the appropriate coordinate and delegates the value computation to
-- the recurrence engine `f-const` (PrecInf).  The coordinate-index work
-- that produces the regional hgerm from h's actual witness is done later
-- (the dispatch).
--
--   * prec-inf-Case1-region : h eventually complete S^m(0) -> f Case 1.
--   * prec-inf-Case2-region : h pinned at a Y-coordinate c (incomplete
--       finite), value S^m(bot) -> f Case 2 at coordinate (suc c).
--   * prec-inf-Case3Y-region : h pinned at a Y-coordinate c (infinite),
--       value S^{phi(p)}(bot) -> f Case 3 at coordinate (suc c).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfRegion where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.LeReassemble using (LeFTup-from-del)
open import OBSTINATION.PrecInf using (f-const)
open import OBSTINATION.PrecFun using (RecData ; PF)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- Sub-case 1: h eventually complete -> f Case 1
  ------------------------------------------------------------------------

  prec-inf-Case1-region : (m n0 k0 : Nat) (Y0 : FTup) (Y : Tup) ->
    Below Y0 Y ->
    (reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))) ->
    (hgerm : (a r : FEl) (X : FTup) -> LeF (fbot n0) a -> LeD (bot k0) (embed r) ->
               LeFTup Y0 X -> Eq (H (cons a (cons r X))) (fcpl m)) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Case1-region m n0 k0 Y0 Y belY0 reach hgerm =
    uo1 (mkSigma (cons (fbot (suc n0)) Y0) (mkSigma (mkSigma tt belY0) (mkSigma m univ)))
    where
      univ : (W : FTup) -> LeFTup (cons (fbot (suc n0)) Y0) W ->
             Eq (PF G H W) (fcpl m)
      univ nil ()
      univ (cons a X') leW =
        f-const rd (fcpl m) n0 k0 X'
          (\ b lb -> reach b X' lb (snd leW))
          (\ b r lb lr -> hgerm b r X' lb lr (snd leW))
          a (fst leW)

  ------------------------------------------------------------------------
  -- Sub-case 2: h pinned at a Y-coordinate (incomplete finite) -> f Case 2
  ------------------------------------------------------------------------

  prec-inf-Case2-region : (m n0 k0 c : Nat) (Y0 : FTup) (Y : Tup) ->
    Below Y0 Y ->
    LeN (suc c) (length Y0) ->
    IncompleteFinite (get c Y) ->
    Eq (embed (getF c Y0)) (get c Y) ->
    (reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))) ->
    (hgerm : (a r : FEl) (X : FTup) -> LeF (fbot n0) a -> LeD (bot k0) (embed r) ->
               LeFTup Y0 X -> Eq (getF c X) (getF c Y0) ->
               Eq (H (cons a (cons r X))) (fbot m)) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Case2-region m n0 k0 c Y0 Y belY0 crange cincompl cpin reach hgerm =
    uo2 (mkSigma (cons (fbot (suc n0)) Y0)
          (mkSigma (mkSigma tt belY0)
            (mkSigma m (mkSigma (suc c) (mkSigma crange (mkSigma cincompl (mkSigma cpin univ)))))))
    where
      univ : (W : FTup) -> Eq (length W) (length (cons (fbot (suc n0)) Y0)) ->
             Eq (getF (suc c) W) (getF (suc c) (cons (fbot (suc n0)) Y0)) ->
             LeFTup (del (suc c) (cons (fbot (suc n0)) Y0)) (del (suc c) W) ->
             Eq (PF G H W) (fbot m)
      univ nil () coordW delW
      univ (cons a X') lenW coordW delW =
        f-const rd (fbot m) n0 k0 X'
          (\ b lb -> reach b X' lb X'geY0)
          (\ b r lb lr -> hgerm b r X' lb lr X'geY0 coordW)
          a (fst delW)
        where
          lenY0X' : Eq (length Y0) (length X')
          lenY0X' = Eq-sym (suc-inj lenW)
          X'geY0 : LeFTup Y0 X'
          X'geY0 = LeFTup-from-del c Y0 X' lenY0X'
                     (Eq-transport (\ z -> LeF (getF c Y0) z) (Eq-sym coordW) (LeF-refl (getF c Y0)))
                     (snd delW)

  ------------------------------------------------------------------------
  -- Sub-case 3: h pinned at a Y-coordinate (infinite) -> f Case 3
  ------------------------------------------------------------------------

  prec-inf-Case3Y-region : (phi : Nat -> Nat) (n0 k0 kc c : Nat)
    (Y0 : FTup) (Y : Tup) ->
    Below Y0 Y ->
    Eq (get c Y) inf ->
    Eq (getF c Y0) (fbot kc) ->
    PhiOK kc phi ->
    (reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))) ->
    (hgerm : (a r : FEl) (X : FTup) (p : Nat) -> LeF (fbot n0) a ->
               LeD (bot k0) (embed r) -> LeFTup Y0 X -> LeN kc p ->
               Eq (getF c X) (fbot p) -> Eq (H (cons a (cons r X))) (fbot (phi p))) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Case3Y-region phi n0 k0 kc c Y0 Y belY0 cinf cval phiok reach hgerm =
    uo3 (mkSigma (cons (fbot (suc n0)) Y0)
          (mkSigma (mkSigma tt belY0)
            (mkSigma (suc c) (mkSigma cinf (mkSigma kc (mkSigma cval (mkSigma phi (mkSigma phiok univ))))))))
    where
      univ : (W : FTup) (p : Nat) -> Eq (length W) (length (cons (fbot (suc n0)) Y0)) ->
             LeN kc p -> Eq (getF (suc c) W) (fbot p) ->
             LeFTup (del (suc c) (cons (fbot (suc n0)) Y0)) (del (suc c) W) ->
             Eq (PF G H W) (fbot (phi p))
      univ nil p () kcp coordW delW
      univ (cons a X') p lenW kcp coordW delW =
        f-const rd (fbot (phi p)) n0 k0 X'
          (\ b lb -> reach b X' lb X'geY0)
          (\ b r lb lr -> hgerm b r X' p lb lr X'geY0 kcp coordW)
          a (fst delW)
        where
          lenY0X' : Eq (length Y0) (length X')
          lenY0X' = Eq-sym (suc-inj lenW)
          cvalLe : LeF (getF c Y0) (getF c X')
          cvalLe = Eq-transport (\ z -> LeF z (getF c X')) (Eq-sym cval)
                     (Eq-transport (\ z -> LeF (fbot kc) z) (Eq-sym coordW) kcp)
          X'geY0 : LeFTup Y0 X'
          X'geY0 = LeFTup-from-del c Y0 X' lenY0X' cvalLe (snd delW)
