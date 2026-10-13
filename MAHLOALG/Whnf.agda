{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/Whnf.agda
--
-- A term whose denotation has a value weak-head normalises
-- syntactically, to a weak-head normal form with a syntactic shape,
-- denoting a weak-head shape with the same value.
------------------------------------------------------------------------

module MAHLOALG.Whnf where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Conv
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Den
open import MAHLO.Concrete.Std
open import MAHLOINJ.Valid.HeadRed
open import MAHLOALG.Sim
open import MAHLOALG.Shape

hrsWhs : {n : Num} {t w : Expr n} -> HRs t w -> Whs (den t idE) (den w idE)
hrsWhs hrs-refl = whs-refl
hrsWhs (hrs-step r rs) = go (hrDen idE r)
  where
    go : _ -> _
    go (inl w) = whs-step w (hrsWhs rs)
    go (inr (e , h)) = transport (\ x -> Whs x _) (Eq-sym e) (hrsWhs rs)

private
  whs-on : {a b c : Tm} -> Whs a b -> Whs a c -> WhNF b -> Whs c b
  whs-on p whs-refl nf = p
  whs-on whs-refl (whs-step s q) nf = Empty-elim (nf s)
  whs-on (whs-step s p) (whs-step s' q) nf = whs-on (transport (\ x -> Whs x _) (Wh-det s s') p) q nf

  whs-nf : {a b : Tm} -> WhNF a -> Whs a b -> Eq a b
  whs-nf nf whs-refl = refl
  whs-nf nf (whs-step s p) = Empty-elim (nf s)

record WhnfRes {n : Num} (t : Expr n) (v : Tm) : Set where
  constructor whnfres
  field
    w   : Expr n
    rs  : HRs t w
    nr  : NoRed w
    sh  : SynSh w
    wsh : WShape (den w idE)
    dv  : den w idE ⇓ v

whnfOf : {n : Num} (t : Expr n) {v : Tm} -> den t idE ⇓ v -> WhnfRes t v
whnfOf t {v} dv = whnfres w rs nr (synSh w nr wsh) wsh (⇓-conv (cv-red (hrsRed idE rs)) dv)
  where
    k = wn dv
    sy = synWN idE t k
    w = fst sy
    rs = fst (snd sy)
    nr = snd (snd sy)
    toS = whs-on (fst (snd k)) (hrsWhs rs) (wshape-nf (snd (snd k)))
    wsh = transport WShape (Eq-sym (whs-nf (nfDen w nr) toS)) (snd (snd k))
