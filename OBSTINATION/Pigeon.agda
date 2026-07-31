{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.Pigeon
--
-- THE FINITE PIGEONHOLE, AND THE BOUNDED SEARCH IT NEEDS.
--
-- `pigeon r f` : r+1 points into r values must repeat.  This was proved
-- inside `IterCycle`, whose other contents drag in the whole domain/tuple
-- development; the statement itself needs nothing but `Prelude`, and the
-- trace-side block modules (`BlkOrbit`) need exactly this and nothing else.
-- So it lives here, and `IterCycle` re-exports it unchanged.
--
-- Induction on r.  At suc r, let v = f (suc r) be the last value and ask
-- whether v is already attained below.  If it is, that IS the repeat.  If
-- it is not, collapse the value `r` onto `v` -- legitimate exactly because
-- v is not attained below, so the collapse cannot merge two points that
-- disagreed -- which brings the first r+1 points into r values, and the
-- induction hypothesis applies.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.Pigeon where

open import OBSTINATION.Prelude

------------------------------------------------------------------------
-- Arithmetic odds and ends
------------------------------------------------------------------------

le-ne-lt : (a b : Nat) -> LeN a b -> Not (Eq a b) -> LeN (suc a) b
le-ne-lt zero    zero    le ne = Empty-elim (ne refl)
le-ne-lt zero    (suc b) le ne = tt
le-ne-lt (suc a) zero    () ne
le-ne-lt (suc a) (suc b) le ne = le-ne-lt a b le (\ e -> ne (Eq-cong suc e))

LeN-suc-not : (a : Nat) -> LeN (suc a) a -> Empty
LeN-suc-not zero    ()
LeN-suc-not (suc a) le = LeN-suc-not a le

------------------------------------------------------------------------
-- A branch on numeric equality, without a Dec in the way
--
-- Defined by recursion on the two numbers rather than through `EqNat-dec`,
-- so that `ifEq-yes` / `ifEq-no` are provable by the same recursion; a
-- `Dec` hidden inside the definition would not reduce.
------------------------------------------------------------------------

ifEq : Nat -> Nat -> Nat -> Nat -> Nat
ifEq zero    zero    v w = v
ifEq zero    (suc t) v w = w
ifEq (suc z) zero    v w = w
ifEq (suc z) (suc t) v w = ifEq z t v w

ifEq-yes : (z t v w : Nat) -> Eq z t -> Eq (ifEq z t v w) v
ifEq-yes zero    zero    v w e = refl
ifEq-yes zero    (suc t) v w ()
ifEq-yes (suc z) zero    v w ()
ifEq-yes (suc z) (suc t) v w e = ifEq-yes z t v w (suc-inj e)

ifEq-no : (z t v w : Nat) -> Not (Eq z t) -> Eq (ifEq z t v w) w
ifEq-no zero    zero    v w ne = Empty-elim (ne refl)
ifEq-no zero    (suc t) v w ne = refl
ifEq-no (suc z) zero    v w ne = refl
ifEq-no (suc z) (suc t) v w ne = ifEq-no z t v w (\ e -> ne (Eq-cong suc e))

------------------------------------------------------------------------
-- Bounded search, returning the witness on success
------------------------------------------------------------------------

BFind : Nat -> (Nat -> Set) -> Set
BFind r P = Sigma Nat (\ j -> Pair (LeN (suc j) r) (P j))

BNone : Nat -> (Nat -> Set) -> Set
BNone r P = (j : Nat) -> LeN (suc j) r -> Not (P j)

bounded-find : (r : Nat) (P : Nat -> Set) -> ((j : Nat) -> Dec (P j)) ->
  Or (BFind r P) (BNone r P)
bounded-find zero    P dec = inr (\ j ())
bounded-find (suc r) P dec =
  step (dec zero) (bounded-find r (\ j -> P (suc j)) (\ j -> dec (suc j)))
  where
    step : Dec (P zero) ->
           Or (BFind r (\ j -> P (suc j))) (BNone r (\ j -> P (suc j))) ->
           Or (BFind (suc r) P) (BNone (suc r) P)
    step (yes p0) h = inl (mkSigma zero (mkSigma tt p0))
    step (no np0) (inl (mkSigma j (mkSigma lt pj))) =
      inl (mkSigma (suc j) (mkSigma lt pj))
    step (no np0) (inr h) = inr none
      where
        none : BNone (suc r) P
        none zero    lt = np0
        none (suc j) lt = h j lt

------------------------------------------------------------------------
-- PIGEONHOLE: r+1 points into r values must repeat
------------------------------------------------------------------------

Repeat : Nat -> (Nat -> Nat) -> Set
Repeat r f = Sigma Nat (\ a -> Sigma Nat (\ b ->
  Pair (LeN (suc a) b) (Pair (LeN b r) (Eq (f a) (f b)))))

pigeon : (r : Nat) (f : Nat -> Nat) ->
  ((j : Nat) -> LeN j r -> LeN (suc (f j)) r) -> Repeat r f
pigeon zero    f h = Empty-elim (h zero tt)
pigeon (suc r) f h =
  route (bounded-find (suc r) (\ j -> Eq (f j) v) (\ j -> EqNat-dec (f j) v))
  where
    v : Nat
    v = f (suc r)

    vr : LeN v r
    vr = h (suc r) (LeN-refl (suc r))

    route : Or (BFind (suc r) (\ j -> Eq (f j) v))
               (BNone (suc r) (\ j -> Eq (f j) v)) -> Repeat (suc r) f
    -- v is already attained at j <= r: that is the repeat
    route (inl (mkSigma j (mkSigma lt e))) =
      mkSigma j (mkSigma (suc r) (mkSigma lt (mkSigma (LeN-refl (suc r)) e)))
    -- v is not attained below: collapse the value r onto v and recurse
    route (inr nf) = recover (pigeon r f' h')
      where
        f' : Nat -> Nat
        f' j = ifEq (f j) r v (f j)

        h' : (j : Nat) -> LeN j r -> LeN (suc (f' j)) r
        h' j lj = decide (EqNat-dec (f j) r)
          where
            fjr : LeN (f j) r
            fjr = h j (LeN-trans {j} {r} {suc r} lj (LeN-suc r))

            decide : Dec (Eq (f j) r) -> LeN (suc (f' j)) r
            decide (yes e) =
              Eq-transport (\ z -> LeN (suc z) r)
                (Eq-sym (ifEq-yes (f j) r v (f j) e))
                (le-ne-lt v r vr vner)
              where
                vner : Not (Eq v r)
                vner ev = nf j lj (Eq-trans e (Eq-sym ev))
            decide (no ne) =
              Eq-transport (\ z -> LeN (suc z) r)
                (Eq-sym (ifEq-no (f j) r v (f j) ne))
                (le-ne-lt (f j) r fjr ne)

        recover : Repeat r f' -> Repeat (suc r) f
        recover (mkSigma a (mkSigma b (mkSigma ab (mkSigma br e')))) =
          mkSigma a (mkSigma b (mkSigma ab
            (mkSigma (LeN-trans {b} {r} {suc r} br (LeN-suc r))
                     (back (EqNat-dec (f a) r) (EqNat-dec (f b) r)))))
          where
            aleb : LeN a b
            aleb = LeN-trans {a} {suc a} {b} (LeN-suc a) ab

            ar' : LeN a r
            ar' = LeN-trans {a} {b} {r} aleb br

            back : Dec (Eq (f a) r) -> Dec (Eq (f b) r) -> Eq (f a) (f b)
            back (yes ea) (yes eb) = Eq-trans ea (Eq-sym eb)
            back (yes ea) (no nb)  =
              Empty-elim (nf b br
                (Eq-trans (Eq-sym (ifEq-no (f b) r v (f b) nb))
                  (Eq-trans (Eq-sym e') (ifEq-yes (f a) r v (f a) ea))))
            back (no na)  (yes eb) =
              Empty-elim (nf a ar'
                (Eq-trans (Eq-sym (ifEq-no (f a) r v (f a) na))
                  (Eq-trans e' (ifEq-yes (f b) r v (f b) eb))))
            back (no na)  (no nb)  =
              Eq-trans (Eq-sym (ifEq-no (f a) r v (f a) na))
                (Eq-trans e' (ifEq-no (f b) r v (f b) nb))
