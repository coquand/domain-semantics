{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfSub4
--
-- Sub-case 4 (the crux) of primitive recursion at the infinite first
-- argument (min1.pdf p.3-4): h is governed at its recursion-result
-- coordinate (coordinate 1) by a STRICTLY INCREASING witness phi.  Then
-- f = prec g h is Case 3 at its OWN coordinate 0, with witness function
--
--     psi(n0) = N,   psi(n+1) = phi(psi n),
--
-- where  S^N(bot) = f(S^{n0}(bot), Y0).  The construction:
--
--   * base constancy (PrecBaseConst.base-const): f(S^{n0}b, X) = S^N b
--     for X >= Y0;
--   * the depth recurrence (`f-psi-val`): f(S^m b, X) = S^{psi m} b for
--     m >= n0, X >= Y0 -- an induction on the offset m - n0, applying the
--     germ at coordinate 1 = S^{psi m}(bot), which stays >= S^{k0}(bot)
--     by f-monotonicity (psi is non-decreasing);
--   * the witness psi is constant (if N = phi N) or strictly increasing
--     (if N < phi N), decided by comparing N and phi N (N <= phi N holds
--     by f-monotonicity).  Either way PhiOK n0 psi (`Psi`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfSub4 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.PhiProps using (addN ; LeN-addN-l)
open import OBSTINATION.PhiComp using (le-to-addN)
open import OBSTINATION.Psi using (psi ; psi-base ; psi-rec ; psi-ok-const ; psi-ok-sinc)
open import OBSTINATION.PrecBaseConst using (base-const)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono)

-- from  j <= k  and  j /= k  to  suc j <= k
le-neq-lt : (j k : Nat) -> LeN j k -> Not (Eq j k) -> LeN (suc j) k
le-neq-lt zero    zero    le ne = Empty-elim (ne refl)
le-neq-lt zero    (suc k) le ne = tt
le-neq-lt (suc j) zero    () ne
le-neq-lt (suc j) (suc k) le ne = le-neq-lt j k le (\ e -> ne (Eq-cong suc e))

------------------------------------------------------------------------
-- The strict-increasing sub-case, parameterised by the coordinate-1 germ.
------------------------------------------------------------------------

module _ (rd : RecData) (n0 k0 N : Nat) (phi : Nat -> Nat) (Y0 : FTup)
  (leKN : LeN k0 N)
  (Neq : Eq (PF (RecData.G rd) (RecData.H rd) (cons (fbot n0) Y0)) (fbot N))
  (psiok-in : Or (Eq N (phi N)) (StrictIncFrom k0 phi))
  (hgerm : (n k : Nat) (X : FTup) -> LeN n0 n -> LeN k0 k -> LeFTup Y0 X ->
             Eq (RecData.H rd (cons (fbot n) (cons (fbot k) X))) (fbot (phi k)))
  where
  open RecData rd

  psiF : Nat -> Nat
  psiF = psi phi N n0

  germN0 : (X : FTup) -> LeFTup Y0 X ->
    Eq (H (cons (fbot n0) (cons (fbot N) X))) (fbot (phi N))
  germN0 X leX = hgerm n0 N X (LeN-refl n0) leKN leX

  bc : (n : Nat) (X : FTup) -> LeN n n0 -> LeFTup Y0 X ->
       Eq (PF G H (cons (fbot n) X)) (PF G H (cons (fbot n) Y0))
  bc = base-const rd n0 N (phi N) Y0 Neq germN0

  ----------------------------------------------------------------------
  -- The depth recurrence, as a combined induction carrying psi m >= k0.
  ----------------------------------------------------------------------

  fpsi : (l : Nat) (X : FTup) -> LeFTup Y0 X ->
    Pair (Eq (PF G H (cons (fbot (addN n0 l)) X)) (fbot (psiF (addN n0 l))))
         (LeN k0 (psiF (addN n0 l)))
  fpsi zero X leX = mkSigma valEq bnd
    where
      valEq : Eq (PF G H (cons (fbot n0) X)) (fbot (psiF n0))
      valEq = Eq-trans (bc n0 X (LeN-refl n0) leX)
                (Eq-trans Neq (Eq-cong fbot (Eq-sym (psi-base phi N n0))))
      bnd : LeN k0 (psiF n0)
      bnd = Eq-transport (\ z -> LeN k0 z) (Eq-sym (psi-base phi N n0)) leKN
  fpsi (suc l) X leX = mkSigma valEq' bnd'
    where
      m = addN n0 l
      n0m : LeN n0 m
      n0m = LeN-addN-l n0 l
      ih = fpsi l X leX
      ihVal : Eq (PF G H (cons (fbot m) X)) (fbot (psiF m))
      ihVal = fst ih
      ihBnd : LeN k0 (psiF m)
      ihBnd = snd ih
      valEq' : Eq (PF G H (cons (fbot (suc m)) X)) (fbot (psiF (suc m)))
      valEq' =
        Eq-trans (Eq-cong (\ z -> H (cons (fbot m) (cons z X))) ihVal)
          (Eq-trans (hgerm m (psiF m) X n0m ihBnd leX)
                    (Eq-cong fbot (Eq-sym (psi-rec phi N n0 m n0m))))
      le-psi : LeN (psiF m) (psiF (suc m))
      le-psi =
        Eq-transport (\ w -> LeD w (bot (psiF (suc m)))) (Eq-cong embed ihVal)
          (Eq-transport (\ w -> LeD (embed (PF G H (cons (fbot m) X))) w)
            (Eq-cong embed valEq')
            (PF-mono G H monoG monoH {cons (fbot m) X} {cons (fbot (suc m)) X}
              (mkSigma (LeN-suc m) (LeFTup-refl X))))
      bnd' : LeN k0 (psiF (suc m))
      bnd' = LeN-trans {k0} {psiF m} {psiF (suc m)} ihBnd le-psi

  f-psi-val : (m : Nat) -> LeN n0 m -> (X : FTup) -> LeFTup Y0 X ->
    Eq (PF G H (cons (fbot m) X)) (fbot (psiF m))
  f-psi-val m n0m X leX =
    Eq-transport (\ z -> Eq (PF G H (cons (fbot z) X)) (fbot (psiF z)))
      (snd r) (fst (fpsi (fst r) X leX))
    where r = le-to-addN n0 m n0m

  ----------------------------------------------------------------------
  -- N <= phi N by f-monotonicity, hence PhiOK n0 psi.
  ----------------------------------------------------------------------

  leN-phiN : LeN N (phi N)
  leN-phiN =
    Eq-transport (\ z -> LeN N z) sucEq
      (Eq-transport (\ w -> LeD (bot N) w) (Eq-cong embed psiN1)
        (Eq-transport (\ w -> LeD w (embed (PF G H (cons (fbot (suc n0)) Y0))))
          (Eq-cong embed Neq)
          (PF-mono G H monoG monoH {cons (fbot n0) Y0} {cons (fbot (suc n0)) Y0}
            (mkSigma (LeN-suc n0) (LeFTup-refl Y0)))))
    where
      psiN1 : Eq (PF G H (cons (fbot (suc n0)) Y0)) (fbot (psiF (suc n0)))
      psiN1 = f-psi-val (suc n0) (LeN-suc n0) Y0 (LeFTup-refl Y0)
      sucEq : Eq (psiF (suc n0)) (phi N)
      sucEq = Eq-trans (psi-rec phi N n0 n0 (LeN-refl n0)) (Eq-cong phi (psi-base phi N n0))

  phiok : PhiOK n0 psiF
  phiok with EqNat-dec N (phi N)
  ... | yes e = psi-ok-const phi N n0 e
  ... | no ne = go psiok-in
    where
      go : Or (Eq N (phi N)) (StrictIncFrom k0 phi) -> PhiOK n0 psiF
      go (inl e)    = Empty-elim (ne e)
      go (inr sinc) = psi-ok-sinc phi N n0 k0 sinc leKN (le-neq-lt N (phi N) leN-phiN ne)

  ----------------------------------------------------------------------
  -- f is Case 3 at coordinate 0 with witness psi.
  ----------------------------------------------------------------------

  prec-inf-Sub4 : (Y : Tup) -> Below Y0 Y -> UO (PF G H) (cons inf Y)
  prec-inf-Sub4 Y belY0 =
    uo3 (mkSigma (cons (fbot n0) Y0) (mkSigma (mkSigma tt belY0)
      (mkSigma zero (mkSigma refl (mkSigma n0 (mkSigma refl
        (mkSigma psiF (mkSigma phiok univ))))))))
    where
      univ : (W : FTup) (m : Nat) ->
             Eq (length W) (length (cons (fbot n0) Y0)) -> LeN n0 m ->
             Eq (getF zero W) (fbot m) ->
             LeFTup (del zero (cons (fbot n0) Y0)) (del zero W) ->
             Eq (PF G H W) (fbot (psiF m))
      univ nil m ()
      univ (cons a X') m lenW n0m coordW delW =
        Eq-transport (\ z -> Eq (PF G H (cons z X')) (fbot (psiF m)))
          (Eq-sym coordW) (f-psi-val m n0m X' delW)
