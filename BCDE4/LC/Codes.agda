{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Codes
--
-- Canonical codes of levels from decidability of level equality:
--
--   ldec-from-dec : (T : LCtx) -> decidable (Valid T) -> LDec T
--
-- An enumeration  enum : Nat -> LExpr  with a section  index  (Cantor
-- pairing; decoding by fuel, the fuel being stored in the index), and
-- lcode l = the least i with Valid T (enum i) l (bounded search below
-- index l).  Equal levels have the same witnesses, hence the same least
-- witness.
------------------------------------------------------------------------

module BCDE4.LC.Codes where

open import BCDE4.Basic
open import BCDE4.Levels

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus-zero : (n : Nat) -> Eq (n + zero) n
plus-zero zero    = refl
plus-zero (suc n) = Eq-cong suc (plus-zero n)

plus-suc : (m n : Nat) -> Eq (m + suc n) (suc (m + n))
plus-suc zero    n = refl
plus-suc (suc m) n = Eq-cong suc (plus-suc m n)

Le-split : (j i : Nat) -> Le j i -> Either (Lt j i) (Eq j i)
Le-split zero    zero    _ = inr refl
Le-split zero    (suc i) _ = inl tt
Le-split (suc j) zero    ()
Le-split (suc j) (suc i) h = split (Le-split j i h)
  where
    split : Either (Lt j i) (Eq j i) -> Either (Lt (suc j) (suc i)) (Eq (suc j) (suc i))
    split (inl lt) = inl lt
    split (inr e)  = inr (Eq-cong suc e)

cmp : (a b : Nat) -> Either (Eq a b) (Either (Lt a b) (Lt b a))
cmp zero    zero    = inl refl
cmp zero    (suc b) = inr (inl tt)
cmp (suc a) zero    = inr (inr tt)
cmp (suc a) (suc b) = lift (cmp a b)
  where
    lift : Either (Eq a b) (Either (Lt a b) (Lt b a)) ->
           Either (Eq (suc a) (suc b)) (Either (Lt (suc a) (suc b)) (Lt (suc b) (suc a)))
    lift (inl e) = inl (Eq-cong suc e)
    lift (inr x) = inr x

------------------------------------------------------------------------
-- Cantor pairing: unpair enumerates the diagonals
--   (0,0), (0,1),(1,0), (0,2),(1,1),(2,0), ...
------------------------------------------------------------------------

NN : Set
NN = Pair Nat Nat

step : NN -> NN
step (mkSigma a zero)    = mkSigma zero (suc a)
step (mkSigma a (suc b)) = mkSigma (suc a) b

unpair : Nat -> NN
unpair zero    = mkSigma zero zero
unpair (suc n) = step (unpair n)

tri : Nat -> Nat
tri zero    = zero
tri (suc s) = suc (s + tri s)

pair : Nat -> Nat -> Nat
pair a b = a + tri (a + b)

-- walking along a diagonal
unpair-walk : (a b n : Nat) -> Eq (unpair n) (mkSigma zero (a + b)) ->
  Eq (unpair (a + n)) (mkSigma a b)
unpair-walk zero    b n e = e
unpair-walk (suc a) b n e =
  Eq-cong step (unpair-walk a (suc b) n (Eq-trans e (Eq-cong (mkSigma zero) (Eq-sym (plus-suc a b)))))

unpair-tri : (s : Nat) -> Eq (unpair (tri s)) (mkSigma zero s)
unpair-tri zero    = refl
unpair-tri (suc s) =
  Eq-cong step (unpair-walk s zero (tri s)
    (Eq-trans (unpair-tri s) (Eq-cong (mkSigma zero) (Eq-sym (plus-zero s)))))

unpair-pair : (a b : Nat) -> Eq (unpair (pair a b)) (mkSigma a b)
unpair-pair a b = unpair-walk a b (tri (a + b)) (unpair-tri (a + b))

------------------------------------------------------------------------
-- Enumeration of level expressions
------------------------------------------------------------------------

-- codes: tag 0 = variable, 1 = successor, 2 = sup
code : LExpr -> Nat
code (lvar i)   = pair zero i
code (lnext l)  = pair (suc zero) (code l)
code (lsup l m) = pair (suc (suc zero)) (pair (code l) (code m))

depth : LExpr -> Nat
depth (lvar i)   = zero
depth (lnext l)  = suc (depth l)
depth (lsup l m) = suc (max (depth l) (depth m))

-- decoding with fuel
mutual
  dec : Nat -> Nat -> LExpr
  dec f n = decP f (unpair n)

  decP : Nat -> NN -> LExpr
  decP f (mkSigma t k) = decT t f k

  decT : Nat -> Nat -> Nat -> LExpr
  decT zero                zero    i = lvar i
  decT zero                (suc f) i = lvar i
  decT (suc zero)          zero    k = lvar zero
  decT (suc zero)          (suc f) k = lnext (dec f k)
  decT (suc (suc t))       zero    k = lvar zero
  decT (suc (suc t))       (suc f) k = lsup (dec f (fst (unpair k))) (dec f (snd (unpair k)))

dec-code : (l : LExpr) (f : Nat) -> Le (depth l) f -> Eq (dec f (code l)) l
dec-code (lvar i)   zero    h = Eq-cong (decP zero) (unpair-pair zero i)
dec-code (lvar i)   (suc f) h = Eq-cong (decP (suc f)) (unpair-pair zero i)
dec-code (lnext l)  zero    ()
dec-code (lnext l)  (suc f) h =
  Eq-trans (Eq-cong (decP (suc f)) (unpair-pair (suc zero) (code l)))
           (Eq-cong lnext (dec-code l f h))
dec-code (lsup l m) zero    ()
dec-code (lsup l m) (suc f) h =
  Eq-trans (Eq-cong (decP (suc f)) (unpair-pair (suc (suc zero)) (pair (code l) (code m))))
  (Eq-trans (Eq-cong (\ p -> lsup (dec f (fst p)) (dec f (snd p))) (unpair-pair (code l) (code m)))
            (Eq-cong2 lsup
              (dec-code l f (Le-trans (depth l) (max (depth l) (depth m)) f (Le-max-l (depth l) (depth m)) h))
              (dec-code m f (Le-trans (depth m) (max (depth l) (depth m)) f (Le-max-r (depth l) (depth m)) h))))

enum : Nat -> LExpr
enum n = enumP (unpair n)
  where
    enumP : NN -> LExpr
    enumP (mkSigma d c) = dec d c

index : LExpr -> Nat
index l = pair (depth l) (code l)

enum-index : (l : LExpr) -> Eq (enum (index l)) l
enum-index l =
  Eq-trans (Eq-cong (\ p -> dec (fst p) (snd p)) (unpair-pair (depth l) (code l)))
           (dec-code l (depth l) (Le-refl (depth l)))

------------------------------------------------------------------------
-- Least witnesses of a decidable predicate
------------------------------------------------------------------------

Least : (Nat -> Set) -> Nat -> Set
Least P r = Pair (P r) ((j : Nat) -> Lt j r -> P j -> Empty)

least-unique : {P Q : Nat -> Set} -> ((i : Nat) -> P i -> Q i) -> ((i : Nat) -> Q i -> P i) ->
  {r r' : Nat} -> Least P r -> Least Q r' -> Eq r r'
least-unique {P} {Q} pq qp {r} {r'} lp lq = go (cmp r r')
  where
    go : Either (Eq r r') (Either (Lt r r') (Lt r' r)) -> Eq r r'
    go (inl e)       = e
    go (inr (inl lt)) = absurd (snd lq r lt (pq r (fst lp)))
    go (inr (inr lt)) = absurd (snd lp r' lt (qp r' (fst lq)))

module Search (P : Nat -> Set) (d : (i : Nat) -> Either (P i) (P i -> Empty)) where

  caseE : {A B C : Set} -> Either A B -> (A -> C) -> (B -> C) -> C
  caseE (inl a) f g = f a
  caseE (inr b) f g = g b

  -- search upwards from i, with k steps left before the known witness b
  go : (b : Nat) -> P b -> (i k : Nat) -> Eq (i + k) b ->
       ((j : Nat) -> Lt j i -> P j -> Empty) -> Sigma Nat (Least P)
  go b pb i zero    e inv =
    mkSigma i (mkSigma (Eq-transport P (Eq-sym (Eq-trans (Eq-sym (plus-zero i)) e)) pb) inv)
  go b pb i (suc k) e inv =
    caseE (d i)
      (\ p -> mkSigma i (mkSigma p inv))
      (\ np -> go b pb (suc i) k (Eq-trans (Eq-sym (plus-suc i k)) e) (inv' np))
    where
      inv' : (P i -> Empty) -> (j : Nat) -> Lt j (suc i) -> P j -> Empty
      inv' np j lt pj = ext (Le-split j i lt)
        where
          ext : Either (Lt j i) (Eq j i) -> Empty
          ext (inl lt') = inv j lt' pj
          ext (inr e')  = np (Eq-transport P e' pj)

  least : (b : Nat) -> P b -> Sigma Nat (Least P)
  least b pb = go b pb zero b refl (\ j ())

------------------------------------------------------------------------
-- Canonical codes from decidability
------------------------------------------------------------------------

ldec-from-dec : (T : LCtx) -> ((l m : LExpr) -> Either (Valid T l m) (Valid T l m -> Empty)) -> LDec T
ldec-from-dec T D = record
  { lcode       = lc
  ; lcode-sound = sound
  ; ldec        = enum
  ; ldec-code   = \ l -> fst (snd (search l))
  }
  where
    Pl : LExpr -> Nat -> Set
    Pl l i = Valid T (enum i) l

    search : (l : LExpr) -> Sigma Nat (Least (Pl l))
    search l = Search.least (Pl l) (\ i -> D (enum i) l) (index l)
                 (Eq-transport (\ x -> Valid T x l) (Eq-sym (enum-index l)) v-refl)

    lc : LExpr -> Nat
    lc l = fst (search l)

    sound : {l m : LExpr} -> Valid T l m -> Eq (lc l) (lc m)
    sound {l} {m} v =
      least-unique (\ i p -> v-trans p v) (\ i q -> v-trans q (v-sym v))
        (snd (search l)) (snd (search m))
