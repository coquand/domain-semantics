{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Values.agda
--
-- Neutral values and values (plan Sec. 6.2), normalisation by
-- arbitrary reduction:  a ⇓ v  :=  a ->* v  with v a value.  Values are
-- normal, so by Church-Rosser normal values are unique and ⇓ is closed
-- under conversion (no standardisation needed).
------------------------------------------------------------------------

module MAHLO.Concrete.Values where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Confluence
open import MAHLO.Concrete.Conv

mutual
  data Ne : Tm -> Set where
    ne-var : {i : Num} -> Ne (tvar i)
    ne-app : {u v : Tm} -> Ne u -> Val v -> Ne (tapp u v)
    ne-fst : {u : Tm} -> Ne u -> Ne (tfst u)
    ne-snd : {u : Tm} -> Ne u -> Ne (tsnd u)
    ne-rec : {C z s n : Tm} -> Val C -> Val z -> Val s -> Ne n -> Ne (trec C z s n)

  data Val : Tm -> Set where
    v-ne   : {u : Tm} -> Ne u -> Val u
    v-lam  : {b : Tm} -> Val b -> Val (tlam b)
    v-pair : {a b : Tm} -> Val a -> Val b -> Val (tpair a b)
    v-pi   : {a b : Tm} -> Val a -> Val b -> Val (tpi a b)
    v-sig  : {a b : Tm} -> Val a -> Val b -> Val (tsig a b)
    v-nat  : Val tnat
    v-ze   : Val tze
    v-sc   : {a : Tm} -> Val a -> Val (tsc a)
    v-V    : Val tV
    v-U    : {a b : Tm} -> Val a -> Val b -> Val (tU a b)

------------------------------------------------------------------------
-- Values are normal
------------------------------------------------------------------------

mutual
  ne-normal : {u w : Tm} -> Ne u -> Step u w -> Empty
  ne-normal ne-var ()
  ne-normal (ne-app () v) s-beta
  ne-normal (ne-app u v) (s-app1 s) = ne-normal u s
  ne-normal (ne-app u v) (s-app2 s) = val-normal v s
  ne-normal (ne-fst ()) s-fstp
  ne-normal (ne-fst u) (s-fst s) = ne-normal u s
  ne-normal (ne-snd ()) s-sndp
  ne-normal (ne-snd u) (s-snd s) = ne-normal u s
  ne-normal (ne-rec C z s0 ()) s-rec0
  ne-normal (ne-rec C z s0 ()) s-recS
  ne-normal (ne-rec C z s0 n) (s-rec1 s) = val-normal C s
  ne-normal (ne-rec C z s0 n) (s-rec2 s) = val-normal z s
  ne-normal (ne-rec C z s0 n) (s-rec3 s) = val-normal s0 s
  ne-normal (ne-rec C z s0 n) (s-rec4 s) = ne-normal n s

  val-normal : {v w : Tm} -> Val v -> Step v w -> Empty
  val-normal (v-ne u) s = ne-normal u s
  val-normal (v-lam b) (s-lam s) = val-normal b s
  val-normal (v-pair a b) (s-pair1 s) = val-normal a s
  val-normal (v-pair a b) (s-pair2 s) = val-normal b s
  val-normal (v-pi a b) (s-pi1 s) = val-normal a s
  val-normal (v-pi a b) (s-pi2 s) = val-normal b s
  val-normal (v-sig a b) (s-sig1 s) = val-normal a s
  val-normal (v-sig a b) (s-sig2 s) = val-normal b s
  val-normal v-nat ()
  val-normal v-ze ()
  val-normal (v-sc a) (s-sc s) = val-normal a s
  val-normal v-V ()
  val-normal (v-U a b) (s-U1 s) = val-normal a s
  val-normal (v-U a b) (s-U2 s) = val-normal b s

-- a value only reduces to itself
val-red : {v w : Tm} -> Val v -> Red v w -> Eq w v
val-red v r-refl = refl
val-red v (r-step s r) = Empty-elim (val-normal v s)

------------------------------------------------------------------------
-- Normalisation
------------------------------------------------------------------------

_⇓_ : Tm -> Tm -> Set
a ⇓ v = Red a v * Val v

infix 4 _⇓_

-- normal values are unique
⇓-unique : {a v w : Tm} -> a ⇓ v -> a ⇓ w -> Eq v w
⇓-unique (p , vv) (q , vw) =
  let s = confluent p q in
  Eq-trans (Eq-sym (val-red vv (fst (snd s)))) (val-red vw (snd (snd s)))

-- a value is convertible only to terms reducing to it
conv-val : {a v : Tm} -> Conv a v -> Val v -> a ⇓ v
conv-val (c , (p , q)) vv = transport (Red _) (val-red vv q) p , vv

-- ⇓ is closed under conversion
⇓-conv : {a a' v : Tm} -> Conv a a' -> a ⇓ v -> a' ⇓ v
⇓-conv e (p , vv) = conv-val (cv-trans (cv-sym e) (cv-red p)) vv

-- values are values of themselves
⇓-self : {v : Tm} -> Val v -> v ⇓ v
⇓-self vv = r-refl , vv
