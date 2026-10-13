{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/EtaDec.agda
--
-- Decomposition of eta-equality (equality of computed eta-normal forms,
-- Concrete/Eta) along the shapes of values:
--   lambda/lambda, lambda/neutral, pair/pair, pair/neutral;
-- and the class of an eta-normal form (constructors and neutrals keep
-- theirs; a lambda or a pair may become neutral by contraction).
--
-- NB: untyped eta identifies  \x. r x  and  (r.1, r.2)  (both contract
-- to r), which the untyped algorithm does not; completeness therefore
-- needs well-typedness at a common type (Pi /= Sigma) for that case.
------------------------------------------------------------------------

module MAHLOALG.EtaDec where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.DecEq
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.EtaLemmas
open import MAHLO.Concrete.Ext using (retr-suc)

------------------------------------------------------------------------
-- classes
------------------------------------------------------------------------

data Cls : Set where
  cL cP cN cPi cSig cNat cZe cSc cV cU : Cls

cls : Tm -> Cls
cls (tvar _) = cN
cls (tlam _) = cL
cls (tapp _ _) = cN
cls (tpi _ _) = cPi
cls (tsig _ _) = cSig
cls (tpair _ _) = cP
cls (tfst _) = cN
cls (tsnd _) = cN
cls tnat = cNat
cls tze = cZe
cls (tsc _) = cSc
cls (trec _ _ _ _) = cN
cls tV = cV
cls (tU _ _) = cU

ne-cls : {u : Tm} -> Ne u -> Eq (cls u) cN
ne-cls ne-var = refl
ne-cls (ne-app u v) = refl
ne-cls (ne-fst u) = refl
ne-cls (ne-snd u) = refl
ne-cls (ne-rec C z s n) = refl

------------------------------------------------------------------------
-- lambda
------------------------------------------------------------------------

data LamCls (c : Tm) : Set where
  lam-keep : Eq (etaLam c) (tlam c) -> LamCls c
  lam-contr : (r : Tm) -> Eq c (tapp r (tvar zero)) -> Eq (shift (unshift r)) r -> Eq (etaLam c) (unshift r) -> LamCls c

private
  testCls : (r : Tm) -> Dec (Eq (shift (unshift r)) r) -> LamCls (tapp r (tvar zero))
  testCls r (yes e) = lam-contr r refl e (etaLamTest-yes r (deceq (shift (unshift r)) r) e)
  testCls r (no f) = lam-keep (etaLamTest-no r (deceq (shift (unshift r)) r) f)

  appCls : (r u : Tm) -> LamCls (tapp r u)
  appCls r (tvar zero) = testCls r (deceq (shift (unshift r)) r)
  appCls r (tvar (suc i)) = lam-keep refl
  appCls r (tlam y0) = lam-keep refl
  appCls r (tapp y0 y1) = lam-keep refl
  appCls r (tpi y0 y1) = lam-keep refl
  appCls r (tsig y0 y1) = lam-keep refl
  appCls r (tpair y0 y1) = lam-keep refl
  appCls r (tfst y0) = lam-keep refl
  appCls r (tsnd y0) = lam-keep refl
  appCls r tnat = lam-keep refl
  appCls r tze = lam-keep refl
  appCls r (tsc y0) = lam-keep refl
  appCls r (trec y0 y1 y2 y3) = lam-keep refl
  appCls r tV = lam-keep refl
  appCls r (tU y0 y1) = lam-keep refl

lamCls : (c : Tm) -> LamCls c
lamCls (tapp r u) = appCls r u
lamCls (tvar y0) = lam-keep refl
lamCls (tlam y0) = lam-keep refl
lamCls (tpi y0 y1) = lam-keep refl
lamCls (tsig y0 y1) = lam-keep refl
lamCls (tpair y0 y1) = lam-keep refl
lamCls (tfst y0) = lam-keep refl
lamCls (tsnd y0) = lam-keep refl
lamCls tnat = lam-keep refl
lamCls tze = lam-keep refl
lamCls (tsc y0) = lam-keep refl
lamCls (trec y0 y1 y2 y3) = lam-keep refl
lamCls tV = lam-keep refl
lamCls (tU y0 y1) = lam-keep refl

private
  tlamInj : {a b : Tm} -> Eq (tlam a) (tlam b) -> Eq a b
  tlamInj refl = refl

  tappInj1 : {a b c d : Tm} -> Eq (tapp a b) (tapp c d) -> Eq a c
  tappInj1 refl = refl

  -- the head of a contracted value is neutral
  contrNe : {r : Tm} -> Val (tapp r (tvar zero)) -> Ne r
  contrNe (v-ne (ne-app n v)) = n

  ne-not-lam : {a b : Tm} -> Eq (tlam a) b -> Ne b -> Empty
  ne-not-lam refl ()

  ne-not-pair : {a b c : Tm} -> Eq (tpair a b) c -> Ne c -> Empty
  ne-not-pair refl ()

  unshiftNe : {r : Tm} -> Ne r -> Ne (unshift r)
  unshiftNe n = ne-sub downVar n

-- the class of an eta-contracted abstraction
clsLam : {c : Tm} -> Val c -> (Eq (cls (etaLam c)) cL) + (Eq (cls (etaLam c)) cN)
clsLam {c} vc = go (lamCls c)
  where
    go : LamCls c -> _
    go (lam-keep e) = inl (Eq-cong cls e)
    go (lam-contr r e sh e') =
      inr (Eq-trans (Eq-cong cls e') (ne-cls (unshiftNe (contrNe (transport Val e vc)))))

-- lambda / lambda
E-lam : {c1 c2 : Tm} -> Val c1 -> Val c2 -> Eq (etaLam c1) (etaLam c2) -> Eq c1 c2
E-lam {c1} {c2} v1 v2 e = go (lamCls c1) (lamCls c2)
  where
    go : LamCls c1 -> LamCls c2 -> Eq c1 c2
    go (lam-keep k1) (lam-keep k2) = tlamInj (Eq-trans (Eq-sym k1) (Eq-trans e k2))
    go (lam-contr r1 q1 s1 k1) (lam-contr r2 q2 s2 k2) =
      Eq-trans q1 (Eq-trans (Eq-cong (\ x -> tapp x (tvar zero))
                     (Eq-trans (Eq-sym s1) (Eq-trans (Eq-cong shift (Eq-trans (Eq-sym k1) (Eq-trans e k2))) s2)))
                   (Eq-sym q2))
    go (lam-keep k1) (lam-contr r2 q2 s2 k2) =
      Empty-elim (ne-not-lam (Eq-trans (Eq-sym k1) (Eq-trans e k2)) (unshiftNe (contrNe (transport Val q2 v2))))
    go (lam-contr r1 q1 s1 k1) (lam-keep k2) =
      Empty-elim (ne-not-lam (Eq-trans (Eq-sym k2) (Eq-trans (Eq-sym e) k1)) (unshiftNe (contrNe (transport Val q1 v1))))

-- lambda / neutral
E-lamNe : {c e2 : Tm} -> Val c -> Ne e2 -> Eq (etaLam c) e2 -> Eq c (tapp (shift e2) (tvar zero))
E-lamNe {c} vc n2 e = go (lamCls c)
  where
    go : LamCls c -> _
    go (lam-keep k) = Empty-elim (ne-not-lam (Eq-trans (Eq-sym k) e) n2)
    go (lam-contr r q s k) =
      Eq-trans q (Eq-cong (\ x -> tapp x (tvar zero)) (Eq-trans (Eq-sym s) (Eq-cong shift (Eq-trans (Eq-sym k) e))))

-- eta-normal form of  (shift u) x0
etanf-shift-app : (u : Tm) -> Eq (etanf (tapp (shift u) (tvar zero))) (tapp (shift (etanf u)) (tvar zero))
etanf-shift-app u = Eq-cong (\ x -> tapp x (tvar zero)) (etanf-ren retr-suc u)

------------------------------------------------------------------------
-- pairs
------------------------------------------------------------------------

data PairCls (a b : Tm) : Set where
  pair-keep : Eq (etaPair a b) (tpair a b) -> PairCls a b
  pair-contr : (e : Tm) -> Eq a (tfst e) -> Eq b (tsnd e) -> Eq (etaPair a b) e -> PairCls a b

private
  ptestCls : (e e' : Tm) -> Dec (Eq e e') -> PairCls (tfst e) (tsnd e')
  ptestCls e e' (yes q) = pair-contr e refl (Eq-cong tsnd (Eq-sym q)) (etaPairTest-yes e e' (deceq e e') q)
  ptestCls e e' (no f) = pair-keep (etaPairTest-no e e' (deceq e e') f)

  pair1Cls : (e b : Tm) -> PairCls (tfst e) b
  pair1Cls e (tsnd e') = ptestCls e e' (deceq e e')
  pair1Cls e (tvar y0) = pair-keep refl
  pair1Cls e (tlam y0) = pair-keep refl
  pair1Cls e (tapp y0 y1) = pair-keep refl
  pair1Cls e (tpi y0 y1) = pair-keep refl
  pair1Cls e (tsig y0 y1) = pair-keep refl
  pair1Cls e (tpair y0 y1) = pair-keep refl
  pair1Cls e (tfst y0) = pair-keep refl
  pair1Cls e tnat = pair-keep refl
  pair1Cls e tze = pair-keep refl
  pair1Cls e (tsc y0) = pair-keep refl
  pair1Cls e (trec y0 y1 y2 y3) = pair-keep refl
  pair1Cls e tV = pair-keep refl
  pair1Cls e (tU y0 y1) = pair-keep refl

pairCls : (a b : Tm) -> PairCls a b
pairCls (tfst e) b = pair1Cls e b
pairCls (tvar y0) b = pair-keep refl
pairCls (tlam y0) b = pair-keep refl
pairCls (tapp y0 y1) b = pair-keep refl
pairCls (tpi y0 y1) b = pair-keep refl
pairCls (tsig y0 y1) b = pair-keep refl
pairCls (tpair y0 y1) b = pair-keep refl
pairCls (tsnd y0) b = pair-keep refl
pairCls tnat b = pair-keep refl
pairCls tze b = pair-keep refl
pairCls (tsc y0) b = pair-keep refl
pairCls (trec y0 y1 y2 y3) b = pair-keep refl
pairCls tV b = pair-keep refl
pairCls (tU y0 y1) b = pair-keep refl

private
  tpairInj : {a b c d : Tm} -> Eq (tpair a b) (tpair c d) -> Eq a c * Eq b d
  tpairInj refl = refl , refl

  tfstInj : {a b : Tm} -> Eq (tfst a) (tfst b) -> Eq a b
  tfstInj refl = refl

  fstNe : {e : Tm} -> Val (tfst e) -> Ne e
  fstNe (v-ne (ne-fst n)) = n

clsPair : {a b : Tm} -> Val a -> (Eq (cls (etaPair a b)) cP) + (Eq (cls (etaPair a b)) cN)
clsPair {a} {b} va = go (pairCls a b)
  where
    go : PairCls a b -> _
    go (pair-keep k) = inl (Eq-cong cls k)
    go (pair-contr e q1 q2 k) = inr (Eq-trans (Eq-cong cls k) (ne-cls (fstNe (transport Val q1 va))))

-- pair / pair
E-pair : {a b a' b' : Tm} -> Val a -> Val a' -> Eq (etaPair a b) (etaPair a' b') -> Eq a a' * Eq b b'
E-pair {a} {b} {a'} {b'} va va' e = go (pairCls a b) (pairCls a' b')
  where
    go : PairCls a b -> PairCls a' b' -> Eq a a' * Eq b b'
    go (pair-keep k1) (pair-keep k2) = tpairInj (Eq-trans (Eq-sym k1) (Eq-trans e k2))
    go (pair-contr e1 p1 q1 k1) (pair-contr e2 p2 q2 k2) =
      let ee = Eq-trans (Eq-sym k1) (Eq-trans e k2)
      in Eq-trans p1 (Eq-trans (Eq-cong tfst ee) (Eq-sym p2)) , Eq-trans q1 (Eq-trans (Eq-cong tsnd ee) (Eq-sym q2))
    go (pair-keep k1) (pair-contr e2 p2 q2 k2) =
      Empty-elim (ne-not-pair (Eq-trans (Eq-sym k1) (Eq-trans e k2)) (fstNe (transport Val p2 va')))
    go (pair-contr e1 p1 q1 k1) (pair-keep k2) =
      Empty-elim (ne-not-pair (Eq-trans (Eq-sym k2) (Eq-trans (Eq-sym e) k1)) (fstNe (transport Val p1 va)))

-- pair / neutral
E-pairNe : {a b e2 : Tm} -> Ne e2 -> Eq (etaPair a b) e2 -> Eq a (tfst e2) * Eq b (tsnd e2)
E-pairNe {a} {b} n2 e = go (pairCls a b)
  where
    go : PairCls a b -> _
    go (pair-keep k) = Empty-elim (ne-not-pair (Eq-trans (Eq-sym k) e) n2)
    go (pair-contr e1 p q k) =
      let ee = Eq-trans (Eq-sym k) e in Eq-trans p (Eq-cong tfst ee) , Eq-trans q (Eq-cong tsnd ee)
