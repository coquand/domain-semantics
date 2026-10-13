{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/FixpointSpike.agda
--
-- Feasibility spike for Lemma 14 (the fixed point): the CONSTRUCTIVE
-- part of the transfinite iteration, at the first limit omega.
--   * end-extension is reflexive and transitive;
--   * the union of an omega-chain of candidates is a candidate, and it
--     is the least upper bound for end-extension;
--   * iterating Gamma from a seed X0 with X0 << Gamma(X0) gives
--         X_omega << Gamma(X_omega)      (the "unfold" half of Fixpoint).
-- What is NOT here, and is the real content of Lemma 14: the converse
-- Gamma(X_theta) << X_theta at a closure stage theta (termination).
-- See NEXT_SESSION_FIXPOINT.md.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
open import MAHLO.Syntax using (Num ; zero ; suc)

module MAHLO.FixpointSpike (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Gamma TM
open import MAHLO.EndExt TM

private
  ~-refl : {P : Rel} -> P ~ P
  ~-refl = (\ x -> x) , (\ x -> x)

------------------------------------------------------------------------
-- End-extension is a preorder
------------------------------------------------------------------------

<<-refl : (X : Cand) -> X << X
<<-refl X = record { inc = \ r -> r ; end = \ r r' -> r' ; int = \ a r -> ~-refl }

<<-trans : {X Y Z : Cand} -> X << Y -> Y << Z -> X << Z
<<-trans E1 E2 = record
  { inc = \ r -> _<<_.inc E2 (_<<_.inc E1 r)
  ; end = \ r r' -> _<<_.end E1 r (_<<_.end E2 (_<<_.inc E1 r) r')
  ; int = \ a r -> ~-trans (_<<_.int E1 a r) (_<<_.int E2 a (_<<_.inc E1 r)) }

------------------------------------------------------------------------
-- The order on Num
------------------------------------------------------------------------

data Le : Num -> Num -> Set where
  le-refl : {n : Num} -> Le n n
  le-suc  : {m n : Num} -> Le m n -> Le m (suc n)

le-zero : (n : Num) -> Le zero n
le-zero zero = le-refl
le-zero (suc n) = le-suc (le-zero n)

le-ss : {m n : Num} -> Le m n -> Le (suc m) (suc n)
le-ss le-refl = le-refl
le-ss (le-suc p) = le-suc (le-ss p)

max : Num -> Num -> Num
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

le-max1 : (m n : Num) -> Le m (max m n)
le-max1 zero n = le-zero n
le-max1 (suc m) zero = le-refl
le-max1 (suc m) (suc n) = le-ss (le-max1 m n)

le-max2 : (m n : Num) -> Le n (max m n)
le-max2 zero n = le-refl
le-max2 (suc m) zero = le-zero (suc m)
le-max2 (suc m) (suc n) = le-ss (le-max2 m n)

------------------------------------------------------------------------
-- The union of an omega-chain
------------------------------------------------------------------------

module Chain (X : Num -> Cand) (E : (n : Num) -> X n << X (suc n)) where

  chain : {m n : Num} -> Le m n -> X m << X n
  chain {m} le-refl = <<-refl (X m)
  chain (le-suc p) = <<-trans (chain p) (E _)

  private
    module XC (n : Num) = Cand (X n)

    up : {m n : Num} {a b : D} -> Le m n -> XC.R m a b -> XC.R n a b
    up p r = _<<_.inc (chain p) r

    upI : {m n : Num} {a v v' : D} -> Le m n -> XC.R m a a -> XC.I m a v v' -> XC.I n a v v'
    upI {a = a} p r i = fst (_<<_.int (chain p) a r) i

    downI : {m n : Num} {a v v' : D} -> Le m n -> XC.R m a a -> XC.I n a v v' -> XC.I m a v v'
    downI {a = a} p r i = snd (_<<_.int (chain p) a r) i

    rl : {n : Num} {a b : D} -> XC.R n a b -> XC.R n a a
    rl {n} = IsPER.rl (XC.R-per n)
    rr : {n : Num} {a b : D} -> XC.R n a b -> XC.R n b b
    rr {n} = IsPER.rr (XC.R-per n)

  RU : Rel
  RU a b = Sigma Num (\ n -> XC.R n a b)

  IU : D -> Rel
  IU a v v' = Sigma Num (\ n -> XC.R n a a * XC.I n a v v')

  private
    RU-per : IsPER RU
    RU-per = record
      { sy = \ { (n , r) -> n , IsPER.sy (XC.R-per n) r }
      ; tr = \ { {a} {b} {c} (m , r) (n , r') ->
                 max m n , IsPER.tr (XC.R-per (max m n)) (up (le-max1 m n) r) (up (le-max2 m n) r') } }

    IU-per : (a : D) -> RU a a -> IsPER (IU a)
    IU-per a _ = record
      { sy = \ { (m , (r , i)) -> m , (r , IsPER.sy (XC.I-per m a r) i) }
      ; tr = \ { (m , (r , i)) (n , (r' , j)) ->
                 let k = max m n ; p = le-max1 m n ; q = le-max2 m n in
                 k , (up p r , IsPER.tr (XC.I-per k a (up p r)) (upI p r i) (upI q r' j)) } }

    IU-resp1 : {a b : D} -> RU a b -> IU a <= IU b
    IU-resp1 {a} {b} (n , r) (m , (r1 , i)) =
      max m n , (up (le-max2 m n) (rr r) ,
                 fst (XC.I-resp (max m n) (up (le-max2 m n) r)) (upI (le-max1 m n) r1 i))

    IU-resp : {a b : D} -> RU a b -> IU a ~ IU b
    IU-resp x = IU-resp1 x , IU-resp1 (IsPER.sy RU-per x)

  Uw : Cand
  Uw = record
    { R = RU
    ; I = IU
    ; R-per = RU-per
    ; I-per = IU-per
    ; I-resp = IU-resp
    ; seed-ne = \ n -> zero , XC.seed-ne zero n
    ; ne-int = \ n nn ->
        (\ { (m , (r , i)) -> fst (XC.ne-int m n nn) i }) ,
        (\ s -> zero , (XC.seed-ne zero nn , snd (XC.ne-int zero n nn) s))
    ; ne-only = \ { nn (m , r) -> XC.ne-only m nn r }
    ; seed-nat = zero , XC.seed-nat zero
    ; nat-int = (\ { (m , (r , i)) -> fst (XC.nat-int m) i }) ,
                (\ s -> zero , (XC.seed-nat zero , snd (XC.nat-int zero) s))
    ; nat-only = \ { (m , r) -> XC.nat-only m r }
    ; R-safe = \ { (m , r) -> XC.R-safe m r }
    ; I-lo = \ { a (n , r) x -> n , (r , XC.I-lo n a r x) }
    ; I-hi = \ { a (n , r) (m , (r1 , i)) -> XC.I-hi m a r1 i }
    ; R-cl = \ { e (n , r) -> n , XC.R-cl n e r }
    ; I-idx = \ e ->
        (\ { (m , (r , i)) -> m , (CandCl.R-self (X m) r e , fst (XC.I-idx m e) i) }) ,
        (\ { (m , (r , i)) -> m , (CandCl.R-self (X m) r (~~-sym e) , snd (XC.I-idx m e) i) })
    ; I-el = \ { e (m , (r , i)) -> m , (r , XC.I-el m e i) }
    ; I-er = \ { e (m , (r , i)) -> m , (r , XC.I-er m e i) } }

  -- every stage is end-extended by the union
  upper : (n : Num) -> X n << Uw
  upper n = record
    { inc = \ r -> n , r
    ; end = \ { {a} {b} r (m , r') ->
                _<<_.end (chain (le-max1 n m)) r (up (le-max2 n m) r') }
    ; int = \ a r ->
        (\ i -> n , (r , i)) ,
        (\ { (m , (r1 , i)) ->
             downI (le-max1 n m) r (upI (le-max2 n m) r1 i) }) }

  -- and it is the least such
  least : {Z : Cand} -> ((n : Num) -> X n << Z) -> Uw << Z
  least H = record
    { inc = \ { (n , r) -> _<<_.inc (H n) r }
    ; end = \ { (n , r) r' -> n , _<<_.end (H n) r r' }
    ; int = \ { a (n , r) ->
        (\ { (m , (r1 , i)) -> fst (_<<_.int (H m) a r1) i }) ,
        (\ j -> n , (r , snd (_<<_.int (H n) a r) j)) } }

------------------------------------------------------------------------
-- Iterating Gamma omega times
------------------------------------------------------------------------

module Iter (X0 : Cand) (B : X0 << Gam X0) where

  it : Num -> Cand
  it zero = X0
  it (suc n) = Gam (it n)

  step : (n : Num) -> it n << it (suc n)
  step zero = B
  step (suc n) = mono (it n) (it (suc n)) (step n)

  open Chain it step public

  -- X_omega << Gamma(X_omega): half of the Fixpoint record
  unfold-omega : Uw << Gam Uw
  unfold-omega = least (\ n -> <<-trans (step n) (mono (it n) Uw (upper n)))

  -- the missing half, which is Lemma 14's content (termination):
  --   fold : Gam Uw << Uw
  -- fails in general at omega: e.g. a Pi-code whose family has
  -- members first appearing at the stages 1, 2, 3, ... lies in
  -- Gam(Uw) but in no X_n.
