{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfReconcile
--
-- Region reconciliation for the second principal case (min1.pdf p.3:
-- "on peut toujours supposer que n0 et Y0 ont ete choisis assez grand").
-- h's ultimate-obstination witness at Q = (S^w b, S^w b, Y) supplies a
-- region  (n0h, Y0h);  `f-reaches` supplies another  (n0r, Y0r)  on which
-- the recursion result already reaches S^{k0}(bot).  We enlarge to the
-- common region  (max n0h n0r, join Y0h Y0r)  on which BOTH hold, and on
-- which  f(S^{n0}b, Y0) >= S^{k0}(bot).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfReconcile where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Meet using (BndT ; joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (BndT-from-Below ; Below-joinT)
open import OBSTINATION.PrecFun using (RecData ; PF)

------------------------------------------------------------------------
-- The reconciled region
------------------------------------------------------------------------

record Reconciled (rd : RecData) (Y : Tup) (k0 n0h : Nat) (Y0h : FTup) : Set where
  open RecData rd
  field
    rN0    : Nat
    rY0    : FTup
    rBel   : Below rY0 Y
    rGeH   : LeFTup Y0h rY0
    rN0GeH : LeN n0h rN0
    rReach : (a : FEl) (X : FTup) -> LeF (fbot rN0) a -> LeFTup rY0 X ->
               LeD (bot k0) (embed (PF G H (cons a X)))
    rFval  : LeD (bot k0) (embed (PF G H (cons (fbot rN0) rY0)))

open Reconciled public

reconcile : (rd : RecData) (Y : Tup) (k0 n0h : Nat) (Y0h : FTup)
  (n0r : Nat) (Y0r : FTup) ->
  Below Y0h Y -> Below Y0r Y ->
  ((a : FEl) (X : FTup) -> LeF (fbot n0r) a -> LeFTup Y0r X ->
     LeD (bot k0) (embed (PF (RecData.G rd) (RecData.H rd) (cons a X)))) ->
  Reconciled rd Y k0 n0h Y0h
reconcile rd Y k0 n0h Y0h n0r Y0r belH belR reachr = record
  { rN0    = maxN n0h n0r
  ; rY0    = joinT Y0h Y0r
  ; rBel   = Below-joinT belH belR
  ; rGeH   = join-ubT-l bnd
  ; rN0GeH = maxN-le-l n0h n0r
  ; rReach = rreach
  ; rFval  = rreach (fbot (maxN n0h n0r)) (joinT Y0h Y0r)
                    (LeF-refl (fbot (maxN n0h n0r))) (LeFTup-refl (joinT Y0h Y0r))
  }
  where
    open RecData rd
    bnd : BndT Y0h Y0r
    bnd = BndT-from-Below belH belR
    geR : LeFTup Y0r (joinT Y0h Y0r)
    geR = join-ubT-r bnd
    rreach : (a : FEl) (X : FTup) -> LeF (fbot (maxN n0h n0r)) a -> LeFTup (joinT Y0h Y0r) X ->
               LeD (bot k0) (embed (PF G H (cons a X)))
    rreach a X la lX =
      reachr a X
        (LeF-trans {fbot n0r} {fbot (maxN n0h n0r)} {a} (maxN-le-r n0h n0r) la)
        (LeTup-trans {embedTup Y0r} {embedTup (joinT Y0h Y0r)} {embedTup X} geR lX)
