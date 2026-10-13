{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Eta.agda
--
-- eta-normal forms, computed:  etanf  eta-contracts bottom-up
--   \x. r x  -->  r     (when r is a shift, decided syntactically)
--   (e.1, e.2) --> e     (decided by syntactic equality)
-- eta-equality of values is  Eq (etanf v) (etanf w).
------------------------------------------------------------------------

module MAHLO.Concrete.Eta where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc ; cong2 ; cong4)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.DecEq

-- remove the variable 0 (junk if it occurs)
down : Sb
down zero    = tvar zero
down (suc i) = tvar i

unshift : Tm -> Tm
unshift = sub down

unshift-shift : (e : Tm) -> Eq (unshift (shift e)) e
unshift-shift e = Eq-trans (sub-ren-gen down suc tvar (\ i -> refl) e) (sub-id-gen tvar (\ i -> refl) e)

------------------------------------------------------------------------
-- the contractions
------------------------------------------------------------------------

etaLamTest : (r : Tm) -> Dec (Eq (shift (unshift r)) r) -> Tm
etaLamTest r (yes _) = unshift r
etaLamTest r (no _)  = tlam (tapp r (tvar zero))

etaLamApp : Tm -> Tm -> Tm
etaLamApp r (tvar zero) = etaLamTest r (deceq (shift (unshift r)) r)
etaLamApp r (tvar (suc i)) = tlam (tapp r (tvar (suc i)))
etaLamApp r (tlam y0) = tlam (tapp r (tlam y0))
etaLamApp r (tapp y0 y1) = tlam (tapp r (tapp y0 y1))
etaLamApp r (tpi y0 y1) = tlam (tapp r (tpi y0 y1))
etaLamApp r (tsig y0 y1) = tlam (tapp r (tsig y0 y1))
etaLamApp r (tpair y0 y1) = tlam (tapp r (tpair y0 y1))
etaLamApp r (tfst y0) = tlam (tapp r (tfst y0))
etaLamApp r (tsnd y0) = tlam (tapp r (tsnd y0))
etaLamApp r tnat = tlam (tapp r tnat)
etaLamApp r tze = tlam (tapp r tze)
etaLamApp r (tsc y0) = tlam (tapp r (tsc y0))
etaLamApp r (trec y0 y1 y2 y3) = tlam (tapp r (trec y0 y1 y2 y3))
etaLamApp r tV = tlam (tapp r tV)
etaLamApp r (tU y0 y1) = tlam (tapp r (tU y0 y1))

etaLam : Tm -> Tm
etaLam (tapp r u) = etaLamApp r u
etaLam (tvar y0) = tlam (tvar y0)
etaLam (tlam y0) = tlam (tlam y0)
etaLam (tpi y0 y1) = tlam (tpi y0 y1)
etaLam (tsig y0 y1) = tlam (tsig y0 y1)
etaLam (tpair y0 y1) = tlam (tpair y0 y1)
etaLam (tfst y0) = tlam (tfst y0)
etaLam (tsnd y0) = tlam (tsnd y0)
etaLam tnat = tlam tnat
etaLam tze = tlam tze
etaLam (tsc y0) = tlam (tsc y0)
etaLam (trec y0 y1 y2 y3) = tlam (trec y0 y1 y2 y3)
etaLam tV = tlam tV
etaLam (tU y0 y1) = tlam (tU y0 y1)

etaPairTest : (e e' : Tm) -> Dec (Eq e e') -> Tm
etaPairTest e e' (yes _) = e
etaPairTest e e' (no _)  = tpair (tfst e) (tsnd e')

etaPair1 : Tm -> Tm -> Tm
etaPair1 e (tsnd e') = etaPairTest e e' (deceq e e')
etaPair1 e (tvar y0) = tpair (tfst e) (tvar y0)
etaPair1 e (tlam y0) = tpair (tfst e) (tlam y0)
etaPair1 e (tapp y0 y1) = tpair (tfst e) (tapp y0 y1)
etaPair1 e (tpi y0 y1) = tpair (tfst e) (tpi y0 y1)
etaPair1 e (tsig y0 y1) = tpair (tfst e) (tsig y0 y1)
etaPair1 e (tpair y0 y1) = tpair (tfst e) (tpair y0 y1)
etaPair1 e (tfst y0) = tpair (tfst e) (tfst y0)
etaPair1 e tnat = tpair (tfst e) tnat
etaPair1 e tze = tpair (tfst e) tze
etaPair1 e (tsc y0) = tpair (tfst e) (tsc y0)
etaPair1 e (trec y0 y1 y2 y3) = tpair (tfst e) (trec y0 y1 y2 y3)
etaPair1 e tV = tpair (tfst e) tV
etaPair1 e (tU y0 y1) = tpair (tfst e) (tU y0 y1)

etaPair : Tm -> Tm -> Tm
etaPair (tfst e) b = etaPair1 e b
etaPair (tvar y0) b = tpair (tvar y0) b
etaPair (tlam y0) b = tpair (tlam y0) b
etaPair (tapp y0 y1) b = tpair (tapp y0 y1) b
etaPair (tpi y0 y1) b = tpair (tpi y0 y1) b
etaPair (tsig y0 y1) b = tpair (tsig y0 y1) b
etaPair (tpair y0 y1) b = tpair (tpair y0 y1) b
etaPair (tsnd y0) b = tpair (tsnd y0) b
etaPair tnat b = tpair tnat b
etaPair tze b = tpair tze b
etaPair (tsc y0) b = tpair (tsc y0) b
etaPair (trec y0 y1 y2 y3) b = tpair (trec y0 y1 y2 y3) b
etaPair tV b = tpair tV b
etaPair (tU y0 y1) b = tpair (tU y0 y1) b

etanf : Tm -> Tm
etanf (tvar i) = tvar i
etanf (tlam b) = etaLam (etanf b)
etanf (tapp t u) = tapp (etanf t) (etanf u)
etanf (tpi A F) = tpi (etanf A) (etanf F)
etanf (tsig A F) = tsig (etanf A) (etanf F)
etanf (tpair a b) = etaPair (etanf a) (etanf b)
etanf (tfst t) = tfst (etanf t)
etanf (tsnd t) = tsnd (etanf t)
etanf tnat = tnat
etanf tze = tze
etanf (tsc t) = tsc (etanf t)
etanf (trec C z s n) = trec (etanf C) (etanf z) (etanf s) (etanf n)
etanf tV = tV
etanf (tU f g) = tU (etanf f) (etanf g)

------------------------------------------------------------------------
-- the contractions fire on their redexes
------------------------------------------------------------------------

etaLamTest-yes : (r : Tm) (d : Dec (Eq (shift (unshift r)) r)) ->
                 Eq (shift (unshift r)) r -> Eq (etaLamTest r d) (unshift r)
etaLamTest-yes r (yes _) e = refl
etaLamTest-yes r (no f) e = Empty-elim (f e)

etaLamTest-no : (r : Tm) (d : Dec (Eq (shift (unshift r)) r)) ->
                (Eq (shift (unshift r)) r -> Empty) -> Eq (etaLamTest r d) (tlam (tapp r (tvar zero)))
etaLamTest-no r (yes e) f = Empty-elim (f e)
etaLamTest-no r (no _) f = refl

etaLam-shift : (e : Tm) -> Eq (etaLam (tapp (shift e) (tvar zero))) e
etaLam-shift e =
  Eq-trans (etaLamTest-yes (shift e) (deceq (shift (unshift (shift e))) (shift e))
                             (Eq-cong shift (unshift-shift e)))
           (unshift-shift e)

etaPairTest-yes : (e e' : Tm) (d : Dec (Eq e e')) -> Eq e e' -> Eq (etaPairTest e e' d) e
etaPairTest-yes e e' (yes _) _ = refl
etaPairTest-yes e e' (no f) q = Empty-elim (f q)

etaPairTest-no : (e e' : Tm) (d : Dec (Eq e e')) -> (Eq e e' -> Empty) ->
                 Eq (etaPairTest e e' d) (tpair (tfst e) (tsnd e'))
etaPairTest-no e e' (yes q) f = Empty-elim (f q)
etaPairTest-no e e' (no _) f = refl

etaPair-same : (e : Tm) -> Eq (etaPair (tfst e) (tsnd e)) e
etaPair-same e = etaPairTest-yes e e (deceq e e) refl

