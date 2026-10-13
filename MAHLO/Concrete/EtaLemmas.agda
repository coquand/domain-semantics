{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/EtaLemmas.agda
--
--  * eta-contraction of a value is a value (plan Sec. 6.2): the
--    contracted term is neutral, and lambdas and pairs never occur in
--    head positions of values, so no beta/pi/iota-redex is created;
--  * etanf commutes with renamings that have a retraction (injective
--    renamings), used for the fresh variable of (A3).
------------------------------------------------------------------------

module MAHLO.Concrete.EtaLemmas where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc ; cong2 ; cong4)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.DecEq
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta

------------------------------------------------------------------------
-- variable substitutions preserve neutrals and values
------------------------------------------------------------------------

VarS : Sb -> Set
VarS s = (i : Num) -> Sigma Num (\ j -> Eq (s i) (tvar j))

liftVar : {s : Sb} -> VarS s -> VarS (liftS s)
liftVar vs zero = zero , refl
liftVar vs (suc i) = suc (fst (vs i)) , Eq-cong shift (snd (vs i))

mutual
  ne-sub : {s : Sb} -> VarS s -> {u : Tm} -> Ne u -> Ne (sub s u)
  ne-sub vs (ne-var {i}) = transport Ne (Eq-sym (snd (vs i))) ne-var
  ne-sub vs (ne-app u v) = ne-app (ne-sub vs u) (val-sub vs v)
  ne-sub vs (ne-fst u) = ne-fst (ne-sub vs u)
  ne-sub vs (ne-snd u) = ne-snd (ne-sub vs u)
  ne-sub vs (ne-rec C z s n) = ne-rec (val-sub vs C) (val-sub vs z) (val-sub vs s) (ne-sub vs n)

  val-sub : {s : Sb} -> VarS s -> {v : Tm} -> Val v -> Val (sub s v)
  val-sub vs (v-ne u) = v-ne (ne-sub vs u)
  val-sub vs (v-lam b) = v-lam (val-sub (liftVar vs) b)
  val-sub vs (v-pair a b) = v-pair (val-sub vs a) (val-sub vs b)
  val-sub vs (v-pi a b) = v-pi (val-sub vs a) (val-sub vs b)
  val-sub vs (v-sig a b) = v-sig (val-sub vs a) (val-sub vs b)
  val-sub vs v-nat = v-nat
  val-sub vs v-ze = v-ze
  val-sub vs (v-sc a) = v-sc (val-sub vs a)
  val-sub vs v-V = v-V
  val-sub vs (v-U a b) = v-U (val-sub vs a) (val-sub vs b)

downVar : VarS down
downVar zero = zero , refl
downVar (suc i) = i , refl

renVar : (r : Rn) -> VarS (\ i -> tvar (r i))
renVar r i = r i , refl

ne-ren : (r : Rn) {u : Tm} -> Ne u -> Ne (ren r u)
ne-ren r {u} n = transport Ne (Eq-sym (ren-as-sub r u)) (ne-sub (renVar r) n)

val-ren : (r : Rn) {v : Tm} -> Val v -> Val (ren r v)
val-ren r {v} n = transport Val (Eq-sym (ren-as-sub r v)) (val-sub (renVar r) n)

------------------------------------------------------------------------
-- eta-contraction preserves values
------------------------------------------------------------------------

etaLamTest-val : (r : Tm) -> Ne r -> (d : Dec (Eq (shift (unshift r)) r)) ->
                 Val (etaLamTest r d)
etaLamTest-val r nr (yes _) = v-ne (ne-sub downVar nr)
etaLamTest-val r nr (no _) = v-lam (v-ne (ne-app nr (v-ne ne-var)))

etaLamApp-val : (r u : Tm) -> Ne r -> Val u -> Val (etaLamApp r u)
etaLamApp-val r (tvar zero) nr vu = etaLamTest-val r nr (deceq (shift (unshift r)) r)
etaLamApp-val r (tvar (suc i)) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tlam y0) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tapp y0 y1) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tpi y0 y1) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tsig y0 y1) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tpair y0 y1) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tfst y0) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tsnd y0) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r tnat nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r tze nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tsc y0) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (trec y0 y1 y2 y3) nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r tV nr vu = v-lam (v-ne (ne-app nr vu))
etaLamApp-val r (tU y0 y1) nr vu = v-lam (v-ne (ne-app nr vu))

etaLam-val : {c : Tm} -> Val c -> Val (etaLam c)
etaLam-val (v-ne (ne-app {u} {v} nr vu)) = etaLamApp-val u v nr vu
etaLam-val (v-ne ne-var) = v-lam (v-ne ne-var)
etaLam-val (v-ne (ne-fst n)) = v-lam (v-ne (ne-fst n))
etaLam-val (v-ne (ne-snd n)) = v-lam (v-ne (ne-snd n))
etaLam-val (v-ne (ne-rec a b c n)) = v-lam (v-ne (ne-rec a b c n))
etaLam-val (v-lam b) = v-lam (v-lam b)
etaLam-val (v-pair a b) = v-lam (v-pair a b)
etaLam-val (v-pi a b) = v-lam (v-pi a b)
etaLam-val (v-sig a b) = v-lam (v-sig a b)
etaLam-val v-nat = v-lam v-nat
etaLam-val v-ze = v-lam v-ze
etaLam-val (v-sc a) = v-lam (v-sc a)
etaLam-val v-V = v-lam v-V
etaLam-val (v-U a b) = v-lam (v-U a b)

etaPairTest-val : (e e' : Tm) -> Ne e -> Ne e' -> (d : Dec (Eq e e')) -> Val (etaPairTest e e' d)
etaPairTest-val e e' n n' (yes _) = v-ne n
etaPairTest-val e e' n n' (no _) = v-pair (v-ne (ne-fst n)) (v-ne (ne-snd n'))

etaPair1-val : (e b : Tm) -> Ne e -> Val b -> Val (etaPair1 e b)
etaPair1-val e (tsnd e') n (v-ne (ne-snd n')) = etaPairTest-val e e' n n' (deceq e e')
etaPair1-val e (tvar y0) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tlam y0) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tapp y0 y1) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tpi y0 y1) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tsig y0 y1) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tpair y0 y1) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tfst y0) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e tnat n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e tze n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tsc y0) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (trec y0 y1 y2 y3) n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e tV n vb = v-pair (v-ne (ne-fst n)) vb
etaPair1-val e (tU y0 y1) n vb = v-pair (v-ne (ne-fst n)) vb

etaPair-val : {a b : Tm} -> Val a -> Val b -> Val (etaPair a b)
etaPair-val {tfst e} {b} (v-ne (ne-fst n)) vb = etaPair1-val e b n vb
etaPair-val (v-ne ne-var) vb = v-pair (v-ne ne-var) vb
etaPair-val (v-ne (ne-app n v)) vb = v-pair (v-ne (ne-app n v)) vb
etaPair-val (v-ne (ne-snd n)) vb = v-pair (v-ne (ne-snd n)) vb
etaPair-val (v-ne (ne-rec a b c n)) vb = v-pair (v-ne (ne-rec a b c n)) vb
etaPair-val (v-lam a) vb = v-pair (v-lam a) vb
etaPair-val (v-pair a b) vb = v-pair (v-pair a b) vb
etaPair-val (v-pi a b) vb = v-pair (v-pi a b) vb
etaPair-val (v-sig a b) vb = v-pair (v-sig a b) vb
etaPair-val v-nat vb = v-pair v-nat vb
etaPair-val v-ze vb = v-pair v-ze vb
etaPair-val (v-sc a) vb = v-pair (v-sc a) vb
etaPair-val v-V vb = v-pair v-V vb
etaPair-val (v-U a b) vb = v-pair (v-U a b) vb

mutual
  etanf-ne : {u : Tm} -> Ne u -> Ne (etanf u)
  etanf-ne ne-var = ne-var
  etanf-ne (ne-app u v) = ne-app (etanf-ne u) (etanf-val v)
  etanf-ne (ne-fst u) = ne-fst (etanf-ne u)
  etanf-ne (ne-snd u) = ne-snd (etanf-ne u)
  etanf-ne (ne-rec C z s n) = ne-rec (etanf-val C) (etanf-val z) (etanf-val s) (etanf-ne n)

  -- the eta-normal form of a value is a value
  etanf-val : {v : Tm} -> Val v -> Val (etanf v)
  etanf-val (v-ne u) = v-ne (etanf-ne u)
  etanf-val (v-lam b) = etaLam-val (etanf-val b)
  etanf-val (v-pair a b) = etaPair-val (etanf-val a) (etanf-val b)
  etanf-val (v-pi a b) = v-pi (etanf-val a) (etanf-val b)
  etanf-val (v-sig a b) = v-sig (etanf-val a) (etanf-val b)
  etanf-val v-nat = v-nat
  etanf-val v-ze = v-ze
  etanf-val (v-sc a) = v-sc (etanf-val a)
  etanf-val v-V = v-V
  etanf-val (v-U a b) = v-U (etanf-val a) (etanf-val b)


------------------------------------------------------------------------
-- renamings with a retraction
------------------------------------------------------------------------

record Retr (r r' : Rn) : Set where
  constructor retr
  field rt : (i : Num) -> Eq (r' (r i)) i

liftRetr : {r r' : Rn} -> Retr r r' -> Retr (liftR r) (liftR r')
liftRetr {r} {r'} rr = retr h
  where
    h : (i : Num) -> Eq (liftR r' (liftR r i)) i
    h zero = refl
    h (suc i) = Eq-cong suc (Retr.rt rr i)

ren-id : (t : Tm) -> Eq (ren (\ i -> i) t) t
ren-id t = Eq-trans (ren-as-sub (\ i -> i) t) (sub-id-gen tvar (\ i -> refl) t)

ren-retract : {r r' : Rn} -> Retr r r' -> (t : Tm) -> Eq (ren r' (ren r t)) t
ren-retract {r} {r'} rr t = Eq-trans (ren-ren-gen r' r (\ i -> i) (Retr.rt rr) t) (ren-id t)

ren-inj : {r r' : Rn} -> Retr r r' -> {a b : Tm} -> Eq (ren r a) (ren r b) -> Eq a b
ren-inj {r} {r'} rr {a} {b} e =
  Eq-trans (Eq-sym (ren-retract rr a)) (Eq-trans (Eq-cong (ren r') e) (ren-retract rr b))

-- "x is a shift"
IsSh : Tm -> Set
IsSh x = Eq (shift (unshift x)) x

isSh-shift : (z : Tm) -> IsSh (shift z)
isSh-shift z = Eq-cong shift (unshift-shift z)

isSh-ren : {r r' : Rn} -> Retr r r' -> (x : Tm) -> IsSh x -> IsSh (ren (liftR r) x)
isSh-ren {r} rr x p =
  transport IsSh (Eq-trans (Eq-sym (ren-shift-comm r (unshift x))) (Eq-cong (ren (liftR r)) p))
    (isSh-shift (ren r (unshift x)))

isSh-unren : {r r' : Rn} -> Retr r r' -> (x : Tm) -> IsSh (ren (liftR r) x) -> IsSh x
isSh-unren {r} {r'} rr x p =
  transport IsSh e (isSh-shift (ren r' (unshift (ren (liftR r) x))))
  where
    e : Eq (shift (ren r' (unshift (ren (liftR r) x)))) x
    e = Eq-trans (Eq-sym (ren-shift-comm r' (unshift (ren (liftR r) x))))
          (Eq-trans (Eq-cong (ren (liftR r')) p) (ren-retract (liftRetr rr) x))

unshift-ren : {r r' : Rn} -> Retr r r' -> (x : Tm) -> IsSh x ->
              Eq (unshift (ren (liftR r) x)) (ren r (unshift x))
unshift-ren {r} rr x p =
  Eq-trans (Eq-cong (\ z -> unshift (ren (liftR r) z)) (Eq-sym p))
    (Eq-trans (Eq-cong unshift (ren-shift-comm r (unshift x))) (unshift-shift (ren r (unshift x))))

etaLamTest-ren : {r r' : Rn} -> Retr r r' -> (x : Tm) ->
                 (d : Dec (IsSh x)) (d' : Dec (IsSh (ren (liftR r) x))) ->
                 Eq (etaLamTest (ren (liftR r) x) d') (ren r (etaLamTest x d))
etaLamTest-ren rr x (yes p) d' =
  Eq-trans (etaLamTest-yes _ d' (isSh-ren rr x p)) (unshift-ren rr x p)
etaLamTest-ren rr x (no f) d' =
  etaLamTest-no _ d' (\ q -> f (isSh-unren rr x q))

etaLamApp-ren : {r r' : Rn} -> Retr r r' -> (x u : Tm) ->
                Eq (etaLamApp (ren (liftR r) x) (ren (liftR r) u)) (ren r (etaLamApp x u))
etaLamApp-ren {r} rr x (tvar zero) =
  etaLamTest-ren rr x (deceq (shift (unshift x)) x)
    (deceq (shift (unshift (ren (liftR r) x))) (ren (liftR r) x))
etaLamApp-ren rr x (tvar (suc i)) = refl
etaLamApp-ren rr x (tlam y0) = refl
etaLamApp-ren rr x (tapp y0 y1) = refl
etaLamApp-ren rr x (tpi y0 y1) = refl
etaLamApp-ren rr x (tsig y0 y1) = refl
etaLamApp-ren rr x (tpair y0 y1) = refl
etaLamApp-ren rr x (tfst y0) = refl
etaLamApp-ren rr x (tsnd y0) = refl
etaLamApp-ren rr x tnat = refl
etaLamApp-ren rr x tze = refl
etaLamApp-ren rr x (tsc y0) = refl
etaLamApp-ren rr x (trec y0 y1 y2 y3) = refl
etaLamApp-ren rr x tV = refl
etaLamApp-ren rr x (tU y0 y1) = refl

etaLam-ren : {r r' : Rn} -> Retr r r' -> (c : Tm) ->
             Eq (etaLam (ren (liftR r) c)) (ren r (etaLam c))
etaLam-ren rr (tapp x u) = etaLamApp-ren rr x u
etaLam-ren rr (tvar y0) = refl
etaLam-ren rr (tlam y0) = refl
etaLam-ren rr (tpi y0 y1) = refl
etaLam-ren rr (tsig y0 y1) = refl
etaLam-ren rr (tpair y0 y1) = refl
etaLam-ren rr (tfst y0) = refl
etaLam-ren rr (tsnd y0) = refl
etaLam-ren rr tnat = refl
etaLam-ren rr tze = refl
etaLam-ren rr (tsc y0) = refl
etaLam-ren rr (trec y0 y1 y2 y3) = refl
etaLam-ren rr tV = refl
etaLam-ren rr (tU y0 y1) = refl

etaPairTest-ren : {r r' : Rn} -> Retr r r' -> (e e' : Tm) ->
                  (d : Dec (Eq e e')) (d' : Dec (Eq (ren r e) (ren r e'))) ->
                  Eq (etaPairTest (ren r e) (ren r e') d') (ren r (etaPairTest e e' d))
etaPairTest-ren rr e e' (yes p) d' = etaPairTest-yes _ _ d' (Eq-cong (ren _) p)
etaPairTest-ren rr e e' (no f) d' = etaPairTest-no _ _ d' (\ q -> f (ren-inj rr q))

etaPair1-ren : {r r' : Rn} -> Retr r r' -> (e b : Tm) ->
               Eq (etaPair1 (ren r e) (ren r b)) (ren r (etaPair1 e b))
etaPair1-ren {r} rr e (tsnd e') = etaPairTest-ren rr e e' (deceq e e') (deceq (ren r e) (ren r e'))
etaPair1-ren rr e (tvar y0) = refl
etaPair1-ren rr e (tlam y0) = refl
etaPair1-ren rr e (tapp y0 y1) = refl
etaPair1-ren rr e (tpi y0 y1) = refl
etaPair1-ren rr e (tsig y0 y1) = refl
etaPair1-ren rr e (tpair y0 y1) = refl
etaPair1-ren rr e (tfst y0) = refl
etaPair1-ren rr e tnat = refl
etaPair1-ren rr e tze = refl
etaPair1-ren rr e (tsc y0) = refl
etaPair1-ren rr e (trec y0 y1 y2 y3) = refl
etaPair1-ren rr e tV = refl
etaPair1-ren rr e (tU y0 y1) = refl

etaPair-ren : {r r' : Rn} -> Retr r r' -> (a b : Tm) ->
              Eq (etaPair (ren r a) (ren r b)) (ren r (etaPair a b))
etaPair-ren rr (tfst e) b = etaPair1-ren rr e b
etaPair-ren rr (tvar y0) b = refl
etaPair-ren rr (tlam y0) b = refl
etaPair-ren rr (tapp y0 y1) b = refl
etaPair-ren rr (tpi y0 y1) b = refl
etaPair-ren rr (tsig y0 y1) b = refl
etaPair-ren rr (tpair y0 y1) b = refl
etaPair-ren rr (tsnd y0) b = refl
etaPair-ren rr tnat b = refl
etaPair-ren rr tze b = refl
etaPair-ren rr (tsc y0) b = refl
etaPair-ren rr (trec y0 y1 y2 y3) b = refl
etaPair-ren rr tV b = refl
etaPair-ren rr (tU y0 y1) b = refl

-- etanf commutes with renamings that have a retraction
etanf-ren : {r r' : Rn} -> Retr r r' -> (t : Tm) -> Eq (etanf (ren r t)) (ren r (etanf t))
etanf-ren rr (tvar i) = refl
etanf-ren {r} rr (tlam b) =
  Eq-trans (Eq-cong etaLam (etanf-ren (liftRetr rr) b)) (etaLam-ren rr (etanf b))
etanf-ren rr (tapp t u) = cong2 tapp (etanf-ren rr t) (etanf-ren rr u)
etanf-ren rr (tpi A F) = cong2 tpi (etanf-ren rr A) (etanf-ren rr F)
etanf-ren rr (tsig A F) = cong2 tsig (etanf-ren rr A) (etanf-ren rr F)
etanf-ren rr (tpair a b) =
  Eq-trans (cong2 etaPair (etanf-ren rr a) (etanf-ren rr b)) (etaPair-ren rr (etanf a) (etanf b))
etanf-ren rr (tfst t) = Eq-cong tfst (etanf-ren rr t)
etanf-ren rr (tsnd t) = Eq-cong tsnd (etanf-ren rr t)
etanf-ren rr tnat = refl
etanf-ren rr tze = refl
etanf-ren rr (tsc t) = Eq-cong tsc (etanf-ren rr t)
etanf-ren rr (trec C z s n) =
  cong4 trec (etanf-ren rr C) (etanf-ren rr z) (etanf-ren rr s) (etanf-ren rr n)
etanf-ren rr tV = refl
etanf-ren rr (tU f g) = cong2 tU (etanf-ren rr f) (etanf-ren rr g)

