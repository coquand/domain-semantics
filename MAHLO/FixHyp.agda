{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/FixHyp.agda
--
-- The hypotheses of the fixed point theorem of fix.pdf (Coquand 1995,
-- "A Topos Theoretic Fix Point Theorem") for the poset of candidates
-- ordered by end-extension, and the derivation of the Fixpoint record.
--
-- Proved here (constructively, predicatively):
--   (1) Cand with << is a preorder;
--   (2) the seed is a candidate, below EVERY candidate;
--   (3) Gamma : Cand -> Cand, and Gamma is <<-monotone with no side
--       condition (P1's EndExt.mono);
--   (4) unions of Set-indexed directed families: candidate, lub;
--   (5) conditional binary joins: if X, Y << Z then X v Y is the lub.
--   (4) and (5) are one construction: the union of a Set-indexed family
--   whose members are pairwise bounded.
-- Not provable predicatively, and isolated as hypotheses:
--   FixThm     the theorem of fix.pdf, for posets with LARGE directed
--              sups (sups of families of the carrier's own size).  The
--              small-sup version is refutable (FixCounter.agda).
--   LargeSups  every Set1-indexed directed family of candidates has a
--              lub.  This is the impredicative step (see below).
--   PFix       the merged principle: every <<-monotone endomap of Cand
--              has a <<-fixed point.  FixThm + LargeSups => PFix => Fixpoint.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.FixHyp (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Gamma TM
open import MAHLO.EndExt TM
open import MAHLO.Fixpoint TM
open import MAHLO.FixpointSpike TM using (<<-refl ; <<-trans)

------------------------------------------------------------------------
-- Large sums and pairs
------------------------------------------------------------------------

record Ex1 (A : Set1) (B : A -> Set) : Set1 where
  constructor ex1
  field
    wit : A
    prf : B wit

record Ex1' (A : Set1) (B : A -> Set1) : Set1 where
  constructor ex1'
  field
    wit : A
    prf : B wit

record And1 (A B : Set1) : Set1 where
  constructor and1
  field
    l : A
    r : B

data Two : Set where
  tt ff : Two

private
  ~-refl : {P : Rel} -> P ~ P
  ~-refl = (\ x -> x) , (\ x -> x)

------------------------------------------------------------------------
-- (2) The seed candidate, least among ALL candidates
------------------------------------------------------------------------

module Seed where
  R0 : Rel
  R0 a b = N a b + ((a ~~ Nat) * (b ~~ Nat))

  I0 : D -> Rel
  I0 a v v' = (N a a * S v v') + ((a ~~ Nat) * NatR v v')

  private
    neNat : {a : D} -> N a a -> a ~~ Nat -> Empty
    neNat n e = ne-Nat (N-self e n)

    I0-ne : {a : D} -> N a a -> I0 a ~ S
    I0-ne n = (\ { (inl (_ , s)) -> s ; (inr (e , _)) -> Empty-elim (neNat n e) }) ,
              (\ s -> inl (n , s))

    I0-nat : {a : D} -> a ~~ Nat -> I0 a ~ NatR
    I0-nat e = (\ { (inl (n , _)) -> Empty-elim (neNat n e) ; (inr (_ , r)) -> r }) ,
               (\ r -> inr (e , r))

    R0-sym : {a b : D} -> R0 a b -> R0 b a
    R0-sym (inl n) = inl (N-sym n)
    R0-sym (inr (e , e')) = inr (e' , e)

    R0-trans : {a b c : D} -> R0 a b -> R0 b c -> R0 a c
    R0-trans (inl n) (inl m) = inl (N-trans n m)
    R0-trans (inl n) (inr (e , _)) = Empty-elim (neNat (IsPER.rr N-per n) e)
    R0-trans (inr (_ , e)) (inl m) = Empty-elim (neNat (IsPER.rl N-per m) e)
    R0-trans (inr (e , _)) (inr (_ , e')) = inr (e , e')

    R0-per : IsPER R0
    R0-per = record { sy = R0-sym ; tr = R0-trans }

    I0-of : {a : D} -> R0 a a -> IsPER (I0 a)
    I0-of (inl n) = per-~ (~-sym (I0-ne n)) S-per
    I0-of (inr (e , _)) = per-~ (~-sym (I0-nat e)) NatR-per

    I0-resp : {a b : D} -> R0 a b -> I0 a ~ I0 b
    I0-resp (inl n) = ~-trans (I0-ne (IsPER.rl N-per n)) (~-sym (I0-ne (IsPER.rr N-per n)))
    I0-resp (inr (e , e')) = ~-trans (I0-nat e) (~-sym (I0-nat e'))

    I0-idx1 : {a a' : D} -> a ~~ a' -> I0 a <= I0 a'
    I0-idx1 e (inl (n , s)) = inl (N-self e n , s)
    I0-idx1 e (inr (e1 , r)) = inr (~~-trans (~~-sym e) e1 , r)

  seed : Cand
  seed = record
    { R = R0
    ; I = I0
    ; R-per = R0-per
    ; I-per = \ a r -> I0-of r
    ; I-resp = I0-resp
    ; seed-ne = inl
    ; ne-int = \ n nn -> I0-ne nn
    ; ne-only = \ { nn (inl m) -> m ; nn (inr (e , _)) -> Empty-elim (neNat nn e) }
    ; seed-nat = inr (~~-refl , ~~-refl)
    ; nat-int = I0-nat ~~-refl
    ; nat-only = \ { (inl m) -> Empty-elim (ne-Nat m) ; (inr (_ , e)) -> e }
    ; R-safe = \ { (inl n) -> N-S n ; (inr (e , e')) -> S-back e e' S-Nat }
    ; I-lo = \ { a (inl n) m -> inl (n , N-S m) ; a (inr (e , _)) m -> inr (e , N-NatR m) }
    ; I-hi = \ { a r (inl (_ , s)) -> s ; a r (inr (_ , x)) -> NatR-S x }
    ; R-cl = \ { e (inl n) -> inl (N-resp e n)
               ; e (inr (e1 , e2)) -> inr (~~-trans (~~-sym e) e1 , e2) }
    ; I-idx = \ e -> I0-idx1 e , I0-idx1 (~~-sym e)
    ; I-el = \ { e (inl (n , s)) -> inl (n , S-resp e s)
               ; e (inr (e1 , r)) -> inr (e1 , NatR-resp e r) }
    ; I-er = \ { e (inl (n , s)) -> inl (n , S-clR e s)
               ; e (inr (e1 , r)) -> inr (e1 , NatR-clR e r) } }

  -- the seed is below every candidate
  seed-least : (X : Cand) -> seed << X
  seed-least X = record
    { inc = \ { (inl n) -> seed-ne n
              ; (inr (e , e')) -> CandCl.R-cl2 X (~~-sym e) (~~-sym e') seed-nat }
    ; end = \ { (inl n) r -> inl (ne-only n r)
              ; (inr (e , _)) r -> inr (e , nat-only (R-cl e r)) }
    ; int = \ { a (inl n) -> ~-trans (I0-ne n) (~-sym (ne-int a n))
              ; a (inr (e , _)) -> ~-trans (I0-nat e) (~-sym (~-trans (I-idx e) nat-int)) } }
    where open Cand X

open Seed public using (seed ; seed-least)

------------------------------------------------------------------------
-- (3) Gamma preserves the poset and is monotone
------------------------------------------------------------------------

-- every candidate, in particular every Gamma X, is above the seed
seed-Gam : (X : Cand) -> seed << Gam X
seed-Gam X = seed-least (Gam X)

-- monotonicity holds for ALL candidates, without side condition
Gam-mono : {X Y : Cand} -> X << Y -> Gam X << Gam Y
Gam-mono {X} {Y} E = mono X Y E

------------------------------------------------------------------------
-- (4)+(5) The union of a pairwise-bounded Set-indexed family
------------------------------------------------------------------------

record Bound (X Y : Cand) : Set1 where
  constructor bound
  field
    W  : Cand
    bl : X << W
    br : Y << W

module Union (I : Set) (X : I -> Cand) (i0 : I) (bnd : (i j : I) -> Bound (X i) (X j)) where

  private
    module XC (i : I) = Cand (X i)
    W : I -> I -> Cand
    W i j = Bound.W (bnd i j)
    l : (i j : I) -> X i << W i j
    l i j = Bound.bl (bnd i j)
    r : (i j : I) -> X j << W i j
    r i j = Bound.br (bnd i j)
    module WC (i j : I) = Cand (W i j)

    -- move an element of the interpretation along end-extensions
    toW : {i j : I} {a v v' : D} -> XC.R i a a -> XC.I i a v v' -> WC.I i j a v v'
    toW {i} {j} {a} p x = fst (_<<_.int (l i j) a p) x

    toWr : {i j : I} {a v v' : D} -> XC.R j a a -> XC.I j a v v' -> WC.I i j a v v'
    toWr {i} {j} {a} p x = fst (_<<_.int (r i j) a p) x

    fromW : {i j : I} {a v v' : D} -> XC.R i a a -> WC.I i j a v v' -> XC.I i a v v'
    fromW {i} {j} {a} p x = snd (_<<_.int (l i j) a p) x

    rl : {i : I} {a b : D} -> XC.R i a b -> XC.R i a a
    rl {i} = IsPER.rl (XC.R-per i)
    rr : {i : I} {a b : D} -> XC.R i a b -> XC.R i b b
    rr {i} = IsPER.rr (XC.R-per i)

  RU : Rel
  RU a b = Sigma I (\ i -> XC.R i a b)

  IU : D -> Rel
  IU a v v' = Sigma I (\ i -> XC.R i a a * XC.I i a v v')

  private
    -- transitivity through the common bound; end-extension brings it back
    RU-trans : {a b c : D} -> RU a b -> RU b c -> RU a c
    RU-trans {a} {b} {c} (i , p) (j , q) =
      i , _<<_.end (l i j) (rl p)
            (IsPER.tr (WC.R-per i j) (_<<_.inc (l i j) p) (_<<_.inc (r i j) q))

    RU-per : IsPER RU
    RU-per = record { sy = \ { (i , p) -> i , IsPER.sy (XC.R-per i) p } ; tr = RU-trans }

    IU-per : (a : D) -> RU a a -> IsPER (IU a)
    IU-per a _ = record
      { sy = \ { (i , (p , x)) -> i , (p , IsPER.sy (XC.I-per i a p) x) }
      ; tr = \ { (i , (p , x)) (j , (q , y)) ->
                 i , (p , fromW {i} {j} p
                            (IsPER.tr (WC.I-per i j a (_<<_.inc (l i j) p))
                               (toW {i} {j} p x) (toWr {i} {j} q y))) } }

    IU-resp1 : {a b : D} -> RU a b -> IU a <= IU b
    IU-resp1 {a} {b} (j , p) (i , (q , x)) =
      j , (rr p ,
           snd (_<<_.int (r i j) b (rr p))
             (fst (WC.I-resp i j (_<<_.inc (r i j) p)) (toW {i} {j} q x)))

  Un : Cand
  Un = record
    { R = RU
    ; I = IU
    ; R-per = RU-per
    ; I-per = IU-per
    ; I-resp = \ x -> IU-resp1 x , IU-resp1 (IsPER.sy RU-per x)
    ; seed-ne = \ n -> i0 , XC.seed-ne i0 n
    ; ne-int = \ n nn ->
        (\ { (i , (p , x)) -> fst (XC.ne-int i n nn) x }) ,
        (\ s -> i0 , (XC.seed-ne i0 nn , snd (XC.ne-int i0 n nn) s))
    ; ne-only = \ { nn (i , p) -> XC.ne-only i nn p }
    ; seed-nat = i0 , XC.seed-nat i0
    ; nat-int = (\ { (i , (p , x)) -> fst (XC.nat-int i) x }) ,
                (\ s -> i0 , (XC.seed-nat i0 , snd (XC.nat-int i0) s))
    ; nat-only = \ { (i , p) -> XC.nat-only i p }
    ; R-safe = \ { (i , p) -> XC.R-safe i p }
    ; I-lo = \ { a (i , p) x -> i , (p , XC.I-lo i a p x) }
    ; I-hi = \ { a (i , p) (j , (q , x)) -> XC.I-hi j a q x }
    ; R-cl = \ { e (i , p) -> i , XC.R-cl i e p }
    ; I-idx = \ e ->
        (\ { (i , (p , x)) -> i , (CandCl.R-self (X i) p e , fst (XC.I-idx i e) x) }) ,
        (\ { (i , (p , x)) -> i , (CandCl.R-self (X i) p (~~-sym e) , snd (XC.I-idx i e) x) })
    ; I-el = \ { e (i , (p , x)) -> i , (p , XC.I-el i e x) }
    ; I-er = \ { e (i , (p , x)) -> i , (p , XC.I-er i e x) } }

  -- every member is end-extended by the union
  upper : (i : I) -> X i << Un
  upper i = record
    { inc = \ p -> i , p
    ; end = \ { p (j , q) -> _<<_.end (l i j) p (_<<_.inc (r i j) q) }
    ; int = \ a p ->
        (\ x -> i , (p , x)) ,
        (\ { (j , (q , y)) -> fromW {i} {j} p (toWr {i} {j} q y) }) }

  -- and it is the least upper bound
  least : {Z : Cand} -> ((i : I) -> X i << Z) -> Un << Z
  least H = record
    { inc = \ { (i , p) -> _<<_.inc (H i) p }
    ; end = \ { (i , p) q -> i , _<<_.end (H i) p q }
    ; int = \ { a (i , p) ->
        (\ { (j , (q , x)) -> fst (_<<_.int (H j) a q) x }) ,
        (\ y -> i , (p , snd (_<<_.int (H i) a p) y)) } }

-- (4) directed families (indexed by a Set)
Directed : (I : Set) -> (I -> Cand) -> Set
Directed I X = (i j : I) -> Sigma I (\ k -> (X i << X k) * (X j << X k))

module DirSup (I : Set) (X : I -> Cand) (i0 : I) (d : Directed I X) =
  Union I X i0 (\ i j -> let k = d i j in
                         bound (X (fst k)) (fst (snd k)) (snd (snd k)))

-- (5) conditional binary joins
module Join (A B Z : Cand) (pA : A << Z) (pB : B << Z) where
  private
    fam : Two -> Cand
    fam tt = A
    fam ff = B
    toZ : (b : Two) -> fam b << Z
    toZ tt = pA
    toZ ff = pB
    module J = Union Two fam tt (\ i j -> bound Z (toZ i) (toZ j))

  join : Cand
  join = J.Un

  join-l : A << join
  join-l = J.upper tt

  join-r : B << join
  join-r = J.upper ff

  join-least : {Y : Cand} -> A << Y -> B << Y -> join << Y
  join-least hA hB = J.least h
    where
      h : (b : Two) -> fam b << _
      h tt = hA
      h ff = hB

------------------------------------------------------------------------
-- The fixed point theorem of fix.pdf, with LARGE directed sups
------------------------------------------------------------------------

-- directed families indexed by a Set1 (a "subset" of a carrier in Set1)
Dir1 : {Car : Set1} -> (Car -> Car -> Set) -> (I : Set1) -> (I -> Car) -> Set1
Dir1 le I x = (i j : I) -> Ex1 I (\ k -> le (x i) (x k) * le (x j) (x k))

record LargeDCPO : Set2 where
  field
    Car     : Set1
    _≤_     : Car -> Car -> Set
    ≤-refl  : (x : Car) -> x ≤ x
    ≤-trans : {x y z : Car} -> x ≤ y -> y ≤ z -> x ≤ z
    bot     : Car
    bot-least : (x : Car) -> bot ≤ x
    dsup    : (I : Set1) (x : I -> Car) -> I -> Dir1 _≤_ I x -> Car
    dsup-ub : (I : Set1) (x : I -> Car) (i0 : I) (d : Dir1 _≤_ I x) (i : I) ->
              x i ≤ dsup I x i0 d
    dsup-least : (I : Set1) (x : I -> Car) (i0 : I) (d : Dir1 _≤_ I x) (z : Car) ->
                 ((i : I) -> x i ≤ z) -> dsup I x i0 d ≤ z
    join    : (x y z : Car) -> x ≤ z -> y ≤ z -> Car
    join-l  : (x y z : Car) (p : x ≤ z) (q : y ≤ z) -> x ≤ join x y z p q
    join-r  : (x y z : Car) (p : x ≤ z) (q : y ≤ z) -> y ≤ join x y z p q
    join-least : (x y z : Car) (p : x ≤ z) (q : y ≤ z) (w : Car) -> x ≤ w -> y ≤ w ->
                 join x y z p q ≤ w

-- Coquand 1995: a monotone map on such a poset has a fixed point
-- (constructive, but impredicative: not provable here)
record FixThm : Set3 where
  field
    fix : (P : LargeDCPO) (f : LargeDCPO.Car P -> LargeDCPO.Car P) ->
          ({x y : LargeDCPO.Car P} -> LargeDCPO._≤_ P x y -> LargeDCPO._≤_ P (f x) (f y)) ->
          Ex1 (LargeDCPO.Car P)
              (\ x0 -> LargeDCPO._≤_ P x0 (f x0) * LargeDCPO._≤_ P (f x0) x0)

-- The impredicative step for candidates: lubs of Set1-indexed directed
-- families.  Classically: take  R a b := || Sigma i. R_i a b ||  and
-- similarly for I.  In type theory this is PROPOSITIONAL RESIZING of the
-- truncated large sums, PROVIDED all relations are proposition-valued:
-- the fields ne-int, ne-only, nat-int, nat-only, R-safe, I-hi map the
-- union INTO the base relations N, S, NatR and ~~, so with proof-relevant
-- base relations (as in the concrete model) one also needs those to be
-- propositions, or a large unique choice to leave the truncation.
record LargeSups : Set2 where
  field
    lsup       : (I : Set1) (X : I -> Cand) -> I -> Dir1 _<<_ I X -> Cand
    lsup-ub    : (I : Set1) (X : I -> Cand) (i0 : I) (d : Dir1 _<<_ I X) (i : I) ->
                 X i << lsup I X i0 d
    lsup-least : (I : Set1) (X : I -> Cand) (i0 : I) (d : Dir1 _<<_ I X) (Z : Cand) ->
                 ((i : I) -> X i << Z) -> lsup I X i0 d << Z

-- The merged principle: every <<-monotone endomap of Cand has a fixed point
record PFix : Set2 where
  field
    pfix : (G : Cand -> Cand) -> ({X Y : Cand} -> X << Y -> G X << G Y) ->
           Ex1 Cand (\ V -> (V << G V) * (G V << V))

------------------------------------------------------------------------
-- Derivations
------------------------------------------------------------------------

-- the candidates form a large dcpo, given LargeSups
candDCPO : LargeSups -> LargeDCPO
candDCPO L = record
  { Car = Cand ; _≤_ = _<<_ ; ≤-refl = <<-refl ; ≤-trans = <<-trans
  ; bot = seed ; bot-least = seed-least
  ; dsup = LargeSups.lsup L ; dsup-ub = LargeSups.lsup-ub L ; dsup-least = LargeSups.lsup-least L
  ; join = \ A B Z p q -> Join.join A B Z p q
  ; join-l = \ A B Z p q -> Join.join-l A B Z p q
  ; join-r = \ A B Z p q -> Join.join-r A B Z p q
  ; join-least = \ A B Z p q Y hA hB -> Join.join-least A B Z p q hA hB }

-- FixThm + LargeSups  =>  PFix
pfix-of : FixThm -> LargeSups -> PFix
pfix-of T L = record { pfix = \ G m -> FixThm.fix T (candDCPO L) G m }

-- PFix  =>  Fixpoint  (Gamma is monotone with no side condition)
fixpoint-of-pfix : PFix -> Fixpoint
fixpoint-of-pfix P =
  let r = PFix.pfix P Gam Gam-mono in
  record { V = Ex1.wit r ; unfold = fst (Ex1.prf r) ; fold = snd (Ex1.prf r) }

fixpoint : FixThm -> LargeSups -> Fixpoint
fixpoint T L = fixpoint-of-pfix (pfix-of T L)
