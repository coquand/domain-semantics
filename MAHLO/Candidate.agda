{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Candidate.agda
--
-- PERs, the function-space construction Fun, and candidates
-- (mahlo-plan.tex, Definition 3).  An interpretation is a total map
-- D -> Rel; only its values on the carrier matter.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.Candidate (TM : TermModel) where

open TermModel TM

Rel : Set1
Rel = D -> D -> Set

_<=_ : Rel -> Rel -> Set
P <= Q = {a b : D} -> P a b -> Q a b

_~_ : Rel -> Rel -> Set
P ~ Q = (P <= Q) * (Q <= P)

~-sym : {P Q : Rel} -> P ~ Q -> Q ~ P
~-sym (h , k) = k , h

~-trans : {P Q T : Rel} -> P ~ Q -> Q ~ T -> P ~ T
~-trans (h , k) (h' , k') = (\ p -> h' (h p)) , (\ t -> k (k' t))

record IsPER (R : Rel) : Set where
  field
    sy : {a b : D} -> R a b -> R b a
    tr : {a b c : D} -> R a b -> R b c -> R a c

  rl : {a b : D} -> R a b -> R a a
  rl p = tr p (sy p)

  rr : {a b : D} -> R a b -> R b b
  rr p = tr (sy p) p

per-~ : {P Q : Rel} -> P ~ Q -> IsPER P -> IsPER Q
per-~ (h , k) pp = record
  { sy = \ q -> h (IsPER.sy pp (k q))
  ; tr = \ q q' -> h (IsPER.tr pp (k q) (k q')) }

N-per : IsPER N
N-per = record { sy = N-sym ; tr = N-trans }

S-per : IsPER S
S-per = record { sy = S-sym ; tr = S-trans }

NatR-per : IsPER NatR
NatR-per = record { sy = NatR-sym ; tr = NatR-trans }

------------------------------------------------------------------------
-- Candidates
------------------------------------------------------------------------

record Cand : Set1 where
  field
    R       : Rel
    I       : D -> Rel
    R-per   : IsPER R
    I-per   : (a : D) -> R a a -> IsPER (I a)
    I-resp  : {a b : D} -> R a b -> I a ~ I b
    -- (C1) the fixed seed
    seed-ne  : N <= R
    ne-int   : (n : D) -> N n n -> I n ~ S
    ne-only  : {n b : D} -> N n n -> R n b -> N n b
    seed-nat : R Nat Nat
    nat-int  : I Nat ~ NatR
    nat-only : {b : D} -> R Nat b -> b ~~ Nat
    -- (C3) safety
    R-safe : R <= S
    I-lo   : (a : D) -> R a a -> N <= I a
    I-hi   : (a : D) -> R a a -> I a <= S
    -- closure under the equality of D
    R-cl   : {a a' b : D} -> a ~~ a' -> R a b -> R a' b
    I-idx  : {a a' : D} -> a ~~ a' -> I a ~ I a'
    I-el   : {a v w v' : D} -> v ~~ w -> I a v v' -> I a w v'
    I-er   : {a v v' w' : D} -> v' ~~ w' -> I a v v' -> I a v w'

------------------------------------------------------------------------
-- The function space
------------------------------------------------------------------------

Fun : Rel -> (D -> Rel) -> Rel
Fun IA IF f f' = (v v' : D) -> IA v v' -> IF v (app f v) (app f' v')

module _ (IA : Rel) (IF : D -> Rel)
         (pA : IsPER IA)
         (rF : {v v' : D} -> IA v v' -> IF v ~ IF v')
         (pF : (v : D) -> IA v v -> IsPER (IF v)) where

  private
    module A = IsPER pA

  Fun-per : IsPER (Fun IA IF)
  Fun-per = record { sy = sy' ; tr = tr' }
    where
      sy' : {f f' : D} -> Fun IA IF f f' -> Fun IA IF f' f
      sy' h v v' i =
        fst (rF (A.sy i))
          (IsPER.sy (pF v' (A.rr i)) (h v' v (A.sy i)))
      tr' : {f f' f'' : D} -> Fun IA IF f f' -> Fun IA IF f' f'' -> Fun IA IF f f''
      tr' h k v v' i =
        IsPER.tr (pF v (A.rl i)) (h v v' i)
          (snd (rF i) (k v' v' (A.rr i)))

  Fun-lo : ({v v' : D} -> IA v v' -> S v v') ->
           ((v : D) -> IA v v -> N <= IF v) -> N <= Fun IA IF
  Fun-lo hiA loF n v v' i = loF v (A.rl i) (ne-app n (hiA i))

  Fun-hi : (N <= IA) -> ((v : D) -> IA v v -> IF v <= S) -> Fun IA IF <= S
  Fun-hi loA hiF {f} {f'} h =
    let x  = fst (ext f f')
        nx = fst (snd (ext f f'))
        k  = snd (snd (ext f f'))
    in k (hiF x (loA nx) (h x x (loA nx)))

Fun-cong : (IA IA' : Rel) (IF IF' : D -> Rel) -> IsPER IA ->
           IA ~ IA' -> ((v : D) -> IA v v -> IF v ~ IF' v) ->
           Fun IA IF ~ Fun IA' IF'
Fun-cong IA IA' IF IF' pA eA eF =
  (\ h v v' i ->
     let j = snd eA i in
     fst (eF v (IsPER.rl pA j)) (h v v' j)) ,
  (\ h v v' j ->
     let i = fst eA j in
     snd (eF v (IsPER.rl pA j)) (h v v' i))

------------------------------------------------------------------------
-- The space of dependent pairs (the Sigma analogue of Fun)
------------------------------------------------------------------------

SigF : Rel -> (D -> Rel) -> Rel
SigF IA IF p p' = IA (pr1 p) (pr1 p') * IF (pr1 p) (pr2 p) (pr2 p')

module _ (IA : Rel) (IF : D -> Rel)
         (pA : IsPER IA)
         (rF : {v v' : D} -> IA v v' -> IF v ~ IF v')
         (pF : (v : D) -> IA v v -> IsPER (IF v)) where

  private
    module A = IsPER pA

  SigF-per : IsPER (SigF IA IF)
  SigF-per = record { sy = sy' ; tr = tr' }
    where
      sy' : {p p' : D} -> SigF IA IF p p' -> SigF IA IF p' p
      sy' (i , j) =
        A.sy i , fst (rF i) (IsPER.sy (pF _ (A.rl i)) j)
      tr' : {p p' p'' : D} -> SigF IA IF p p' -> SigF IA IF p' p'' -> SigF IA IF p p''
      tr' (i , j) (i' , j') =
        A.tr i i' , IsPER.tr (pF _ (A.rl i)) j (snd (rF i) j')

  SigF-lo : (N <= IA) -> ((v : D) -> IA v v -> N <= IF v) -> N <= SigF IA IF
  SigF-lo loA loF n = i , loF _ (A.rl i) (ne-snd n)
    where i = loA (ne-fst n)

  SigF-hi : (IA <= S) -> ((v : D) -> IA v v -> IF v <= S) -> SigF IA IF <= S
  SigF-hi hiA hiF (i , j) = ext-pair (hiA i) (hiF _ (A.rl i) j)

SigF-cong : (IA IA' : Rel) (IF IF' : D -> Rel) -> IsPER IA ->
            IA ~ IA' -> ((v : D) -> IA v v -> IF v ~ IF' v) ->
            SigF IA IF ~ SigF IA' IF'
SigF-cong IA IA' IF IF' pA eA eF =
  (\ { (i , j) -> fst eA i , fst (eF _ (IsPER.rl pA i)) j }) ,
  (\ { (i , j) -> snd eA i , snd (eF _ (IsPER.rl pA (snd eA i))) j })

------------------------------------------------------------------------
-- Closure under the equality of D
------------------------------------------------------------------------

module CandCl (X : Cand) where
  open Cand X

  R-cl2 : {a b a' b' : D} -> a ~~ a' -> b ~~ b' -> R a b -> R a' b'
  R-cl2 e e' r = IsPER.sy R-per (R-cl e' (IsPER.sy R-per (R-cl e r)))

  R-self : {a a' : D} -> R a a -> a ~~ a' -> R a' a'
  R-self r e = R-cl2 e e r

  -- a ~~ a' and a in R give R a a'
  R-of~~ : {a a' : D} -> R a a -> a ~~ a' -> R a a'
  R-of~~ r e = R-cl2 ~~-refl e r

  I-cl2 : {a v v' w w' : D} -> v ~~ w -> v' ~~ w' -> I a v v' -> I a w w'
  I-cl2 e e' i = I-er e' (I-el e i)

-- a relation closed under ~~ on the left; with symmetry also on the right
ClL : Rel -> Set
ClL P = {v w v' : D} -> v ~~ w -> P v v' -> P w v'

ClR : Rel -> Set
ClR P = {v v' w' : D} -> v' ~~ w' -> P v v' -> P v w'

clR-of : {P : Rel} -> IsPER P -> ClL P -> ClR P
clR-of pp cl e p = IsPER.sy pp (cl e (IsPER.sy pp p))

-- both sides at once
cl2 : {P : Rel} -> ClL P -> ClR P -> {v v' w w' : D} -> v ~~ w -> v' ~~ w' -> P v v' -> P w w'
cl2 cl cr e e' p = cr e' (cl e p)

N-self : {a b : D} -> a ~~ b -> N a a -> N b b
N-self e n = N-resp e (clR-of N-per N-resp e n)

-- S on representatives
S-back : {a b x y : D} -> a ~~ x -> b ~~ y -> S x y -> S a b
S-back e e' s = clR-of S-per S-resp (~~-sym e') (S-resp (~~-sym e) s)

N-clL : ClL N
N-clL = N-resp
N-clR : ClR N
N-clR = clR-of N-per N-resp
S-clL : ClL S
S-clL = S-resp
S-clR : ClR S
S-clR = clR-of S-per S-resp
NatR-clL : ClL NatR
NatR-clL = NatR-resp
NatR-clR : ClR NatR
NatR-clR = clR-of NatR-per NatR-resp

-- Fun is closed if its families are
Fun-clL : {IA : Rel} {IF : D -> Rel} -> ((w : D) -> ClL (IF w)) -> ClL (Fun IA IF)
Fun-clL cF e h v v' i = cF v (app-cong e ~~-refl) (h v v' i)

Fun-clR : {IA : Rel} {IF : D -> Rel} -> ((w : D) -> ClR (IF w)) -> ClR (Fun IA IF)
Fun-clR cF e h v v' i = cF v (app-cong e ~~-refl) (h v v' i)

-- equivalent data give equivalent function spaces (pointwise, no PER)
Fun-~ : {IA IA' : Rel} {IF IF' : D -> Rel} -> IA ~ IA' -> ((w : D) -> IF w ~ IF' w) ->
        Fun IA IF ~ Fun IA' IF'
Fun-~ eA eF =
  (\ h v v' i -> fst (eF v) (h v v' (snd eA i))) ,
  (\ h v v' i -> snd (eF v) (h v v' (fst eA i)))

SigF-~ : {IA IA' : Rel} {IF IF' : D -> Rel} -> IA ~ IA' -> ((w : D) -> IF w ~ IF' w) ->
         SigF IA IF ~ SigF IA' IF'
SigF-~ eA eF =
  (\ { (i , j) -> fst eA i , fst (eF _) j }) ,
  (\ { (i , j) -> snd eA i , snd (eF _) j })

-- SigF is closed if its first component is and the family respects ~~
SigF-clL : {IA : Rel} {IF : D -> Rel} -> ClL IA ->
           ({a a' : D} -> a ~~ a' -> IF a ~ IF a') -> ((w : D) -> ClL (IF w)) ->
           ClL (SigF IA IF)
SigF-clL cA idx cF e (i , j) =
  cA (pr1-cong e) i , cF _ (pr2-cong e) (fst (idx (pr1-cong e)) j)

SigF-clR : {IA : Rel} {IF : D -> Rel} -> ClR IA -> ((w : D) -> ClR (IF w)) ->
           ClR (SigF IA IF)
SigF-clR cA cF e (i , j) = cA (pr1-cong e) i , cF _ (pr2-cong e) j
