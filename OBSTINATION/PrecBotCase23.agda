{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotCase23
--
-- The three "value on a region" witness builders for the finite-
-- incomplete first argument  cons (bot (suc c)) Y.  Each ABSTRACTS the
-- value computation away from the h-dispatch: the caller supplies a
-- proof that  precF g h  takes the required value on the relevant region,
-- and these builders package it as the corresponding UO case.
--
--   * `prec-bot-Case2-coord0` : coordinate 0 controls -- f is eventually
--     constant incomplete with coord0 PINNED to S^{c+1}(bot).  (Used when
--     h is controlled by coord0 or by coord1-with-constant-Fc.)
--   * `prec-bot-Case2-Ycoord` : a Y-coordinate j controls (finite) -- f is
--     Case 2 at coordinate  suc j,  coord0 free to grow.
--   * `prec-bot-Case3-Ycoord` : a Y-coordinate j controls (infinite) -- f
--     is Case 3 at coordinate  suc j,  same phi.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotCase23 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.PrecBotEngine using (FcFun)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- Coordinate 0 controls: Case 2 at coordinate 0 (coord0 pinned).
  ------------------------------------------------------------------------

  prec-bot-Case2-coord0 : (c mh : Nat) (Y : Tup) (A0t : FTup) ->
    Below A0t Y ->
    ((X' : FTup) -> LeFTup A0t X' ->
       Eq (H (cons (fbot c) (cons (FcFun rd c X') X'))) (fbot mh)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  prec-bot-Case2-coord0 c mh Y A0t belA0t hval =
    uo2 (mkSigma A0 (mkSigma belA0
      (mkSigma mh (mkSigma zero (mkSigma tt (mkSigma tt (mkSigma refl univ)))))))
    where
      A0 : FTup
      A0 = cons (fbot (suc c)) A0t
      belA0 : Below A0 (cons (bot (suc c)) Y)
      belA0 = mkSigma (LeD-refl (bot (suc c))) belA0t
      univ : (X : FTup) -> Eq (length X) (length A0) ->
             Eq (getF zero X) (getF zero A0) -> LeFTup (del zero A0) (del zero X) ->
             Eq (PF G H X) (fbot mh)
      univ nil ()
      univ (cons x xs) lenX coordX delX =
        Eq-transport (\ w -> Eq (precFun G H w xs) (fbot mh)) (Eq-sym coordX)
          (hval xs delX)

  ------------------------------------------------------------------------
  -- A finite Y-coordinate j controls: Case 2 at coordinate  suc j.
  ------------------------------------------------------------------------

  prec-bot-Case2-Ycoord : (c mh j : Nat) (Y : Tup) (A0t : FTup) ->
    Below A0t Y ->
    LeN (suc j) (length A0t) ->
    IncompleteFinite (get j Y) ->
    Eq (embed (getF j A0t)) (get j Y) ->
    ((x : FEl) (xs : FTup) -> LeF (fbot (suc c)) x ->
       Eq (length xs) (length A0t) ->
       Eq (getF j xs) (getF j A0t) ->
       LeFTup (del j A0t) (del j xs) ->
       Eq (precFun G H x xs) (fbot mh)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  prec-bot-Case2-Ycoord c mh j Y A0t belA0t jrange incompl eqinv hval =
    uo2 (mkSigma A0 (mkSigma belA0
      (mkSigma mh (mkSigma (suc j) (mkSigma jrange' (mkSigma incompl (mkSigma eqinv' univ)))))))
    where
      A0 : FTup
      A0 = cons (fbot (suc c)) A0t
      belA0 : Below A0 (cons (bot (suc c)) Y)
      belA0 = mkSigma (LeD-refl (bot (suc c))) belA0t
      jrange' : LeN (suc (suc j)) (length A0)
      jrange' = jrange
      eqinv' : Eq (embed (getF (suc j) A0)) (get (suc j) (cons (bot (suc c)) Y))
      eqinv' = eqinv
      univ : (X : FTup) -> Eq (length X) (length A0) ->
             Eq (getF (suc j) X) (getF (suc j) A0) ->
             LeFTup (del (suc j) A0) (del (suc j) X) ->
             Eq (PF G H X) (fbot mh)
      univ nil ()
      univ (cons x xs) lenX coordX delX =
        hval x xs (fst delX) (suc-inj lenX) coordX (snd delX)

  ------------------------------------------------------------------------
  -- An infinite Y-coordinate j controls: Case 3 at coordinate  suc j.
  ------------------------------------------------------------------------

  prec-bot-Case3-Ycoord : (c j k : Nat) (phi : Nat -> Nat)
    (Y : Tup) (A0t : FTup) ->
    Below A0t Y ->
    Eq (get j Y) inf ->
    Eq (getF j A0t) (fbot k) ->
    PhiOK k phi ->
    ((x : FEl) (xs : FTup) (p : Nat) -> LeF (fbot (suc c)) x ->
       Eq (length xs) (length A0t) -> LeN k p ->
       Eq (getF j xs) (fbot p) ->
       LeFTup (del j A0t) (del j xs) ->
       Eq (precFun G H x xs) (fbot (phi p))) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  prec-bot-Case3-Ycoord c j k phi Y A0t belA0t eqinf eqA0 phiok hval =
    uo3 (mkSigma A0 (mkSigma belA0
      (mkSigma (suc j) (mkSigma eqinf' (mkSigma k (mkSigma eqA0
        (mkSigma phi (mkSigma phiok univ))))))))
    where
      A0 : FTup
      A0 = cons (fbot (suc c)) A0t
      belA0 : Below A0 (cons (bot (suc c)) Y)
      belA0 = mkSigma (LeD-refl (bot (suc c))) belA0t
      eqinf' : Eq (get (suc j) (cons (bot (suc c)) Y)) inf
      eqinf' = eqinf
      univ : (X : FTup) (p : Nat) -> Eq (length X) (length A0) -> LeN k p ->
             Eq (getF (suc j) X) (fbot p) ->
             LeFTup (del (suc j) A0) (del (suc j) X) ->
             Eq (PF G H X) (fbot (phi p))
      univ nil p ()
      univ (cons x xs) p lenX pk coordX delX =
        hval x xs p (fst delX) (suc-inj lenX) pk coordX (snd delX)
