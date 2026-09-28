{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Equiv
--
-- Theorem 2.2 of Bezem–Coquand (TCS 2022, "Loop-checking and the
-- uniform word problem for join-semilattices with an inflationary
-- endomorphism"): an equation l = m is valid in the theory Th iff every
-- atom of m is derivable (Horn clauses of Th, with shifts and
-- predecessor clauses) from the atoms of l, and conversely.
--
--   der-shift      : derivations are stable under upward shifts
--   der-sound      : derivable atoms lie below the level
--   der-complete   : a valid equation gives derivability
--   valid-from-der : derivability both ways gives validity
--   der-from-valid : validity gives derivability both ways
------------------------------------------------------------------------

module BCDE4.LC.Equiv where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

plus-suc : (m n : Nat) -> Eq (m + suc n) (suc (m + n))
plus-suc zero    n = refl
plus-suc (suc m) n = Eq-cong suc (plus-suc m n)

plus-assoc : (m n p : Nat) -> Eq ((m + n) + p) (m + (n + p))
plus-assoc zero    n p = refl
plus-assoc (suc m) n p = Eq-cong suc (plus-assoc m n p)

shiftA-comp : (s t : Nat) (a : Atom) -> Eq (shiftA s (shiftA t a)) (shiftA (s + t) a)
shiftA-comp s t a = Eq-cong (mkSigma (fst a)) (Eq-sym (plus-assoc s t (snd a)))

------------------------------------------------------------------------
-- 1. Derivations are stable under upward shifts
------------------------------------------------------------------------

ShiftP : Nat -> (Atom -> Set) -> Atom -> Set
ShiftP s P a = Sigma Atom (\ a' -> Pair (P a') (Eq a (shiftA s a')))

der-shift : {Th : LCtx} {P : Atom -> Set} (s : Nat) {b : Atom} ->
  Der Th P b -> Der Th (ShiftP s P) (shiftA s b)
der-shift s {b} (d-hyp p) = d-hyp (mkSigma b (mkSigma p refl))
der-shift {Th} {P} s (d-pred {x} {k} d) =
  d-pred (Eq-transport (\ n -> Der Th (ShiftP s P) (mkSigma x n)) (plus-suc s k) (der-shift s d))
der-shift {Th} {P} s (d-clause {c} mc t ds) =
  Eq-transport (Der Th (ShiftP s P)) (Eq-sym (shiftA-comp s t (head c)))
    (d-clause mc (s + t) (\ a ma ->
      Eq-transport (Der Th (ShiftP s P)) (shiftA-comp s t a) (der-shift s (ds a ma))))

------------------------------------------------------------------------
-- The order  l ≥ m  :=  l ∨ m = l
------------------------------------------------------------------------

module _ {Th : LCtx} where

  Geq : LExpr -> LExpr -> Set
  Geq l m = Valid Th (lsup l m) l

  geq-refl : {l : LExpr} -> Geq l l
  geq-refl = v-idem

  geq-trans : {l m p : LExpr} -> Geq l m -> Geq m p -> Geq l p
  geq-trans h1 h2 =
    v-trans (v-sup (v-sym h1) v-refl) (v-trans v-assoc (v-trans (v-sup v-refl h2) h1))

  geq-resp : {l m m' : LExpr} -> Geq l m -> Valid Th m m' -> Geq l m'
  geq-resp h e = v-trans (v-sup v-refl (v-sym e)) h

  geq-of-eq : {l m : LExpr} -> Valid Th l m -> Geq l m
  geq-of-eq e = v-trans (v-sup v-refl (v-sym e)) v-idem

  geq-antisym : {l m : LExpr} -> Geq l m -> Geq m l -> Valid Th l m
  geq-antisym h1 h2 = v-trans (v-sym h1) (v-trans v-comm h2)

  geq-sup-intro : {l a b : LExpr} -> Geq l a -> Geq l b -> Geq l (lsup a b)
  geq-sup-intro h1 h2 = v-trans (v-sym v-assoc) (v-trans (v-sup h1 v-refl) h2)

  geq-sup-l : {a b : LExpr} -> Geq (lsup a b) a
  geq-sup-l = v-trans v-assoc (v-trans (v-sup v-refl v-comm)
                (v-trans (v-sym v-assoc) (v-sup v-idem v-refl)))

  geq-sup-r : {a b : LExpr} -> Geq (lsup a b) b
  geq-sup-r = v-trans v-assoc (v-sup v-refl v-idem)

  geq-next : {l m : LExpr} -> Geq l m -> Geq (lnext l) (lnext m)
  geq-next h = v-trans (v-sym v-nsup) (v-next h)

  geq-infl : {l : LExpr} -> Geq (lnext l) l
  geq-infl = v-trans v-comm v-infl

------------------------------------------------------------------------
-- Iterated successor
------------------------------------------------------------------------

nx : Nat -> LExpr -> LExpr
nx zero    l = l
nx (suc k) l = lnext (nx k l)

nx-next : (s : Nat) (l : LExpr) -> Eq (nx s (lnext l)) (lnext (nx s l))
nx-next zero    l = refl
nx-next (suc s) l = Eq-cong lnext (nx-next s l)

atomL-shift : (s : Nat) (a : Atom) -> Eq (atomL (shiftA s a)) (nx s (atomL a))
atomL-shift zero    a = refl
atomL-shift (suc s) a = Eq-cong lnext (atomL-shift s a)

module _ {Th : LCtx} where

  valid-nx : (s : Nat) {l m : LExpr} -> Valid Th l m -> Valid Th (nx s l) (nx s m)
  valid-nx zero    e = e
  valid-nx (suc s) e = v-next (valid-nx s e)

  geq-nx : (s : Nat) {l m : LExpr} -> Geq {Th} l m -> Geq {Th} (nx s l) (nx s m)
  geq-nx zero    h = h
  geq-nx (suc s) h = geq-next (geq-nx s h)

  nx-sup : (s : Nat) (a b : LExpr) -> Valid Th (nx s (lsup a b)) (lsup (nx s a) (nx s b))
  nx-sup zero    a b = v-refl
  nx-sup (suc s) a b = v-trans (v-next (nx-sup s a b)) v-nsup

------------------------------------------------------------------------
-- A level is the join of its atoms
------------------------------------------------------------------------

  atom-below : (L : LExpr) {a : Atom} -> Mem a (atomsL L) -> Geq {Th} L (atomL a)
  atom-below (lvar i) here = v-idem
  atom-below (lvar i) (there ())
  atom-below (lsup L M) {a} ma with mem-++-split (atomsL L) (atomsL M) ma
  ... | inl h = geq-trans geq-sup-l (atom-below L h)
  ... | inr h = geq-trans geq-sup-r (atom-below M h)
  atom-below (lnext L) {a} ma =
    let r = mem-map-inv (shiftA (suc zero)) (atomsL L) ma
    in Eq-transport (\ X -> Geq {Th} (lnext L) (atomL X)) (Eq-sym (snd (snd r)))
         (geq-next (atom-below L (fst (snd r))))

  join : (l L : LExpr) (s : Nat) ->
    ((a : Atom) -> Mem a (atomsL L) -> Geq {Th} l (nx s (atomL a))) -> Geq {Th} l (nx s L)
  join l (lvar i) s h = h (mkSigma i zero) here
  join l (lsup L M) s h =
    geq-resp (geq-sup-intro
                (join l L s (\ a ma -> h a (mem-++-l (atomsL L) (atomsL M) ma)))
                (join l M s (\ a ma -> h a (mem-++-r (atomsL L) (atomsL M) ma))))
             (v-sym (nx-sup s L M))
  join l (lnext L) s h =
    Eq-transport (Geq {Th} l) (Eq-sym (nx-next s L))
      (join l L (suc s) (\ a ma ->
        Eq-transport (Geq {Th} l) (nx-next s (atomL a))
          (h (shiftA (suc zero) a) (mem-map (shiftA (suc zero)) (atomsL L) ma))))

------------------------------------------------------------------------
-- Clauses of a theory come from valid equations
------------------------------------------------------------------------

ClauseInfo : LCtx -> Clause -> Set
ClauseInfo Th c =
  Sigma LExpr (\ L -> Sigma LExpr (\ M -> Sigma Atom (\ h ->
    Pair (Valid Th L M) (Pair (Mem h (atomsL M)) (Eq c (mkClause (atomsL L) h))))))

clause-inv : (Th : LCtx) {c : Clause} -> Mem c (clausesTh Th) -> ClauseInfo Th c
clause-inv lnil ()
clause-inv (lcons (ceq l m) Th) {c} mc
  with mem-++-split (clausesC (ceq l m)) (clausesTh Th) mc
... | inr h =
  let r = clause-inv Th h
  in mkSigma (fst r) (mkSigma (fst (snd r)) (mkSigma (fst (snd (snd r)))
       (mkSigma (valid-ent (ent-wk (ceq l m)) (fst (snd (snd (snd r)))))
                (snd (snd (snd (snd r)))))))
... | inl h with mem-++-split (map (mkClause (atomsL l)) (atomsL m))
                              (map (mkClause (atomsL m)) (atomsL l)) h
...   | inl h' =
  let r = mem-map-inv (mkClause (atomsL l)) (atomsL m) h'
  in mkSigma l (mkSigma m (mkSigma (fst r) (mkSigma (v-hyp lhere) (snd r))))
...   | inr h' =
  let r = mem-map-inv (mkClause (atomsL m)) (atomsL l) h'
  in mkSigma m (mkSigma l (mkSigma (fst r) (mkSigma (v-sym (v-hyp lhere)) (snd r))))

clause-mem-l : {Th : LCtx} {l m : LExpr} {b : Atom} -> LMem (ceq l m) Th ->
  Mem b (atomsL m) -> Mem (mkClause (atomsL l) b) (clausesTh Th)
clause-mem-l {lcons _ Th} {l} {m} lhere mb =
  mem-++-l (clausesC (ceq l m)) (clausesTh Th)
    (mem-++-l (map (mkClause (atomsL l)) (atomsL m)) (map (mkClause (atomsL m)) (atomsL l))
      (mem-map (mkClause (atomsL l)) (atomsL m) mb))
clause-mem-l {lcons d Th} (lthere h) mb = mem-++-r (clausesC d) (clausesTh Th) (clause-mem-l h mb)

clause-mem-r : {Th : LCtx} {l m : LExpr} {a : Atom} -> LMem (ceq l m) Th ->
  Mem a (atomsL l) -> Mem (mkClause (atomsL m) a) (clausesTh Th)
clause-mem-r {lcons _ Th} {l} {m} lhere ma =
  mem-++-l (clausesC (ceq l m)) (clausesTh Th)
    (mem-++-r (map (mkClause (atomsL l)) (atomsL m)) (map (mkClause (atomsL m)) (atomsL l))
      (mem-map (mkClause (atomsL m)) (atomsL l) ma))
clause-mem-r {lcons d Th} (lthere h) ma = mem-++-r (clausesC d) (clausesTh Th) (clause-mem-r h ma)

------------------------------------------------------------------------
-- 2. Soundness
------------------------------------------------------------------------

sound-clause : {Th : LCtx} (l : LExpr) {c : Clause} (s : Nat) -> ClauseInfo Th c ->
  ((a : Atom) -> Mem a (body c) -> Geq {Th} l (atomL (shiftA s a))) ->
  Geq {Th} l (atomL (shiftA s (head c)))
sound-clause {Th} l s (mkSigma L (mkSigma M (mkSigma h (mkSigma e (mkSigma mh refl))))) ih =
  Eq-transport (Geq {Th} l) (Eq-sym (atomL-shift s h))
    (geq-trans (join l L s (\ a ma -> Eq-transport (Geq {Th} l) (atomL-shift s a) (ih a ma)))
      (geq-trans (geq-of-eq (valid-nx s e)) (geq-nx s (atom-below M mh))))

der-sound-P : {Th : LCtx} {P : Atom -> Set} (l : LExpr) ->
  ((a : Atom) -> P a -> Geq {Th} l (atomL a)) ->
  {b : Atom} -> Der Th P b -> Geq {Th} l (atomL b)
der-sound-P l hP (d-hyp p)  = hP _ p
der-sound-P l hP (d-pred d) = geq-trans (der-sound-P l hP d) geq-infl
der-sound-P {Th} l hP (d-clause mc s ds) =
  sound-clause l s (clause-inv Th mc) (\ a ma -> der-sound-P l hP (ds a ma))

der-sound : {Th : LCtx} (l : LExpr) {b : Atom} -> Der Th (InL (atomsL l)) b ->
  Valid Th (lsup l (atomL b)) l
der-sound l = der-sound-P l (\ a ma -> atom-below l ma)

------------------------------------------------------------------------
-- 3. Completeness
------------------------------------------------------------------------

DerAll : LCtx -> List Atom -> List Atom -> Set
DerAll Th A B = (b : Atom) -> Mem b B -> Der Th (InL A) b

module _ {Th : LCtx} where

  incl-all : {A B : List Atom} -> ((b : Atom) -> Mem b B -> Mem b A) -> DerAll Th A B
  incl-all f b mb = d-hyp (f b mb)

  refl-all : (A : List Atom) -> DerAll Th A A
  refl-all A b mb = d-hyp mb

  trans-all : {A B C : List Atom} -> DerAll Th A B -> DerAll Th B C -> DerAll Th A C
  trans-all f g c mc = der-cut f (g c mc)

  sup-all : {A A' B B' : List Atom} -> DerAll Th A A' -> DerAll Th B B' ->
    DerAll Th (A ++ B) (A' ++ B')
  sup-all {A} {A'} {B} {B'} f g b mb with mem-++-split A' B' mb
  ... | inl h = der-mono (\ a ma -> mem-++-l A B ma) (f b h)
  ... | inr h = der-mono (\ a ma -> mem-++-r A B ma) (g b h)

  next-all : {A B : List Atom} -> DerAll Th A B ->
    DerAll Th (map (shiftA (suc zero)) A) (map (shiftA (suc zero)) B)
  next-all {A} {B} f b mb =
    let r = mem-map-inv (shiftA (suc zero)) B mb
    in Eq-transport (Der Th (InL (map (shiftA (suc zero)) A))) (Eq-sym (snd (snd r)))
         (der-mono back (der-shift (suc zero) (f (fst r) (fst (snd r)))))
    where
      back : (a : Atom) -> ShiftP (suc zero) (InL A) a -> Mem a (map (shiftA (suc zero)) A)
      back a (mkSigma a' (mkSigma ma' e)) =
        Eq-transport (\ X -> Mem X (map (shiftA (suc zero)) A)) (Eq-sym e)
          (mem-map (shiftA (suc zero)) A ma')

  infl-all : (A : List Atom) -> DerAll Th (map (shiftA (suc zero)) A) (A ++ map (shiftA (suc zero)) A)
  infl-all A b mb with mem-++-split A (map (shiftA (suc zero)) A) mb
  ... | inl h = d-pred (d-hyp (mem-map (shiftA (suc zero)) A h))
  ... | inr h = d-hyp h

comm-incl : (A B : List Atom) (b : Atom) -> Mem b (B ++ A) -> Mem b (A ++ B)
comm-incl A B b mb with mem-++-split B A mb
... | inl h = mem-++-r A B h
... | inr h = mem-++-l A B h

idem-incl : (A : List Atom) (b : Atom) -> Mem b (A ++ A) -> Mem b A
idem-incl A b mb with mem-++-split A A mb
... | inl h = h
... | inr h = h

++-assoc : {X : Set} (A B C : List X) -> Eq ((A ++ B) ++ C) (A ++ (B ++ C))
++-assoc []       B C = refl
++-assoc (x ∷ A) B C = Eq-cong (x ∷_) (++-assoc A B C)

map-++ : {X Y : Set} (f : X -> Y) (A B : List X) -> Eq (map f (A ++ B)) (map f A ++ map f B)
map-++ f []       B = refl
map-++ f (x ∷ A) B = Eq-cong (f x ∷_) (map-++ f A B)

eq-all : {Th : LCtx} {A B : List Atom} -> Eq A B -> Pair (DerAll Th A B) (DerAll Th B A)
eq-all {Th} {A} refl = mkSigma (refl-all A) (refl-all A)

DerBoth : LCtx -> LExpr -> LExpr -> Set
DerBoth Th l m = Pair (DerAll Th (atomsL l) (atomsL m)) (DerAll Th (atomsL m) (atomsL l))

complete : {Th : LCtx} {l m : LExpr} -> Valid Th l m -> DerBoth Th l m
complete (v-hyp h) =
  mkSigma (\ b mb -> d-clause (clause-mem-l h mb) zero (\ a ma -> d-hyp ma))
          (\ a ma -> d-clause (clause-mem-r h ma) zero (\ b mb -> d-hyp mb))
complete {l = l} v-refl = mkSigma (refl-all (atomsL l)) (refl-all (atomsL l))
complete (v-sym d) = let r = complete d in mkSigma (snd r) (fst r)
complete (v-trans d d') =
  let r = complete d ; r' = complete d'
  in mkSigma (trans-all (fst r) (fst r')) (trans-all (snd r') (snd r))
complete (v-sup d d') =
  let r = complete d ; r' = complete d'
  in mkSigma (sup-all (fst r) (fst r')) (sup-all (snd r) (snd r'))
complete (v-next d) =
  let r = complete d in mkSigma (next-all (fst r)) (next-all (snd r))
complete {l = lsup l _} v-idem =
  mkSigma (incl-all (\ b mb -> mem-++-l (atomsL l) (atomsL l) mb))
          (incl-all (idem-incl (atomsL l)))
complete {l = lsup l m} v-comm =
  mkSigma (incl-all (comm-incl (atomsL l) (atomsL m)))
          (incl-all (comm-incl (atomsL m) (atomsL l)))
complete {l = lsup (lsup l m) p} v-assoc = eq-all (++-assoc (atomsL l) (atomsL m) (atomsL p))
complete {l = lnext (lsup l m)} v-nsup = eq-all (map-++ (shiftA (suc zero)) (atomsL l) (atomsL m))
complete {l = lsup l _} v-infl =
  mkSigma (incl-all (\ b mb -> mem-++-r (atomsL l) (map (shiftA (suc zero)) (atomsL l)) mb))
          (infl-all (atomsL l))

der-complete : {Th : LCtx} {l m : LExpr} -> Valid Th l m ->
  (b : Atom) -> Mem b (atomsL m) -> Der Th (InL (atomsL l)) b
der-complete d = fst (complete d)

------------------------------------------------------------------------
-- 4. The characterisation (Theorem 2.2)
------------------------------------------------------------------------

valid-from-der : {Th : LCtx} (l m : LExpr) ->
  ((b : Atom) -> Mem b (atomsL m) -> Der Th (InL (atomsL l)) b) ->
  ((a : Atom) -> Mem a (atomsL l) -> Der Th (InL (atomsL m)) a) ->
  Valid Th l m
valid-from-der {Th} l m f g =
  geq-antisym {Th} (join {Th} l m zero (\ b mb -> der-sound l (f b mb)))
              (join {Th} m l zero (\ a ma -> der-sound m (g a ma)))

der-from-valid : {Th : LCtx} {l m : LExpr} -> Valid Th l m ->
  Pair ((b : Atom) -> Mem b (atomsL m) -> Der Th (InL (atomsL l)) b)
       ((a : Atom) -> Mem a (atomsL l) -> Der Th (InL (atomsL m)) a)
der-from-valid = complete
