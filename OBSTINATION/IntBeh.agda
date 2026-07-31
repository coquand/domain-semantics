{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IntBeh
--
-- THE INTENTIONAL BEHAVIOUR OF A prc, AT THE LEVEL OF `PR.evalF`.
--
-- After OBSTINATION.TraceNbComp, Theorem 14 of R. David, "Decidability
-- results for primitive recursive algorithms", TCS 300 (2003), reduces to
-- the ARITHMETIC statement
--
--     a |-> height (evalF f (S^a(bot) , Y))   is in C_pr
--
-- -- the paper's "intentional behaviour" `f(S^n(bot)) = S^{g(n)}(bot)` of
-- the Comment after Definition 10 -- proved by induction on f with no
-- traces in sight.  This file does the RECURSION clause, which is the only
-- one with content:
--
--   prec-iter-Cpr : (h stabilises in its FIRST argument from N on)
--                 -> (its behaviour in the SECOND is F, always incomplete)
--                 -> Cpr F -> Expanding F
--                 -> Cpr (a |-> height (evalF (prec g h) (S^a(bot) , Y)))
--
-- because `evalF (prec g h) (S^{a+1}(bot) , Y) = evalF h (S^a(bot) ,
-- evalF (prec g h) (S^a(bot),Y) , Y)` holds DEFINITIONALLY (`PR.precF`),
-- so once the dependence on the first argument has stabilised the whole
-- thing is the ITERATION `G(a+1) = F(G(a))`, and `Classes.cpr-iter`
-- applies.  The shift by N is absorbed by `Classes.cpr-fchg` composed
-- with `predIter` (the N-fold predecessor, which is in C_pr because
-- `predN` is one of the four base functions).
--
-- The stabilisation hypothesis is exactly what
-- `TraceTrunc.trunc-stab` + `TraceTrunc.desc-bounded` deliver: ultimate
-- obstination says h cannot read both of its first two arguments
-- unboundedly, so the first one is eventually irrelevant.
--
-- Also here, and needed for `cpr-fchg`: `evalF-mono`, the value-level
-- monotonicity of the interpretation (the analogue of `TraceMono`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IntBeh where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Classes

------------------------------------------------------------------------
-- Heights, and monotonicity of `evalF`
------------------------------------------------------------------------

hgt : FEl -> Nat
hgt (fbot k) = k
hgt (fcpl k) = k

fbot-inj : (a b : Nat) -> Eq (fbot a) (fbot b) -> Eq a b
fbot-inj a b e = Eq-cong hgt e

LeF-hgt : (x y : FEl) -> LeF x y -> LeN (hgt x) (hgt y)
LeF-hgt (fbot m) (fbot n) le = le
LeF-hgt (fbot m) (fcpl n) le = le
LeF-hgt (fcpl m) (fbot n) ()
LeF-hgt (fcpl m) (fcpl n) le = Eq-transport (\ z -> LeN m z) le (LeN-refl m)

LeFs : FTup -> FTup -> Set
LeFs nil         nil         = Top
LeFs nil         (cons _ _)  = Empty
LeFs (cons _ _)  nil         = Empty
LeFs (cons x xs) (cons y ys) = Pair (LeF x y) (LeFs xs ys)

LeFs-refl : (xs : FTup) -> LeFs xs xs
LeFs-refl nil         = tt
LeFs-refl (cons x xs) = mkSigma (LeF-refl x) (LeFs-refl xs)

LeF-nth : (i : Nat) (xs ys : FTup) -> LeFs xs ys
        -> LeF (nth (fbot zero) i xs) (nth (fbot zero) i ys)
LeF-nth i       nil         nil         le = LeF-refl (fbot zero)
LeF-nth i       nil         (cons _ _)  ()
LeF-nth i       (cons _ _)  nil         ()
LeF-nth zero    (cons x xs) (cons y ys) le = fst le
LeF-nth (suc i) (cons x xs) (cons y ys) le = LeF-nth i xs ys (snd le)

sucF-mono : (x y : FEl) -> LeF x y -> LeF (sucF x) (sucF y)
sucF-mono (fbot m) (fbot n) le = le
sucF-mono (fbot m) (fcpl n) le = le
sucF-mono (fcpl m) (fbot n) ()
sucF-mono (fcpl m) (fcpl n) le = Eq-cong suc le

mutual
  evalF-mono : (p : PR) (xs ys : FTup) -> LeFs xs ys
             -> LeF (evalF p xs) (evalF p ys)
  evalF-mono zerf     xs ys le = refl
  evalF-mono (proj i) xs ys le = LeF-nth i xs ys le
  evalF-mono succ nil         nil         le = LeN-refl zero
  evalF-mono succ nil         (cons _ _)  ()
  evalF-mono succ (cons _ _)  nil         ()
  evalF-mono succ (cons x xs) (cons y ys) le = sucF-mono x y (fst le)
  evalF-mono (comp g hs) xs ys le =
    evalF-mono g (mapE hs xs) (mapE hs ys) (mapE-mono hs xs ys le)
  evalF-mono (prec g h) nil         nil         le = LeN-refl zero
  evalF-mono (prec g h) nil         (cons _ _)  ()
  evalF-mono (prec g h) (cons _ _)  nil         ()
  evalF-mono (prec g h) (cons a Y)  (cons b Z)  le =
    precF-mono g h a b Y Z (fst le) (snd le)

  mapE-mono : (ps : List PR) (xs ys : FTup) -> LeFs xs ys
            -> LeFs (mapE ps xs) (mapE ps ys)
  mapE-mono nil         xs ys le = tt
  mapE-mono (cons p ps) xs ys le =
    mkSigma (evalF-mono p xs ys le) (mapE-mono ps xs ys le)

  precF-mono : (g h : PR) (a b : FEl) (Y Z : FTup) -> LeF a b -> LeFs Y Z
             -> LeF (precF g h a Y) (precF g h b Z)
  precF-mono g h (fbot zero) b Y Z lf ls = LeD-botD (embed (precF g h b Z))
  precF-mono g h (fcpl zero) (fbot k) Y Z () ls
  precF-mono g h (fcpl zero) (fcpl k) Y Z lf ls =
    Eq-transport (\ z -> LeF (evalF g Y) (precF g h (fcpl z) Z)) lf
      (evalF-mono g Y Z ls)
  precF-mono g h (fbot (suc j)) (fbot zero) Y Z () ls
  precF-mono g h (fbot (suc j)) (fcpl zero) Y Z () ls
  precF-mono g h (fbot (suc j)) (fbot (suc k)) Y Z lf ls =
    evalF-mono h (cons (fbot j) (cons (precF g h (fbot j) Y) Y))
                 (cons (fbot k) (cons (precF g h (fbot k) Z) Z))
      (mkSigma lf (mkSigma (precF-mono g h (fbot j) (fbot k) Y Z lf ls) ls))
  precF-mono g h (fbot (suc j)) (fcpl (suc k)) Y Z lf ls =
    evalF-mono h (cons (fbot j) (cons (precF g h (fbot j) Y) Y))
                 (cons (fcpl k) (cons (precF g h (fcpl k) Z) Z))
      (mkSigma lf (mkSigma (precF-mono g h (fbot j) (fcpl k) Y Z lf ls) ls))
  precF-mono g h (fcpl (suc j)) (fbot k) Y Z () ls
  precF-mono g h (fcpl (suc j)) (fcpl k) Y Z lf ls =
    Eq-transport (\ z -> LeF (precF g h (fcpl (suc j)) Y) (precF g h (fcpl z) Z))
      lf
      (evalF-mono h (cons (fcpl j) (cons (precF g h (fcpl j) Y) Y))
                    (cons (fcpl j) (cons (precF g h (fcpl j) Z) Z))
        (mkSigma (LeF-refl (fcpl j))
          (mkSigma (precF-mono g h (fcpl j) (fcpl j) Y Z (LeF-refl (fcpl j)) ls)
                   ls)))

------------------------------------------------------------------------
-- The N-fold predecessor is in C_pr
------------------------------------------------------------------------

predIter : Nat -> Nat -> Nat
predIter zero    n = n
predIter (suc N) n = predIter N (predN n)

Cpr-predIter : (N : Nat) -> Cpr (predIter N)
Cpr-predIter zero    = cpr-base ic
Cpr-predIter (suc N) = cpr-comp (Cpr-predIter N) (cpr-base pc)

add-predIter : (N n : Nat) -> LeN N n -> Eq (add N (predIter N n)) n
add-predIter zero    n       le = add-zero-l n
add-predIter (suc N) zero    ()
add-predIter (suc N) (suc n) le =
  Eq-trans (add-suc-l N (predIter N n)) (Eq-cong suc (add-predIter N n le))

------------------------------------------------------------------------
-- THE RECURSION CLAUSE
------------------------------------------------------------------------

prec-iter-Cpr : (g h : PR) (Y : FTup) (N : Nat) (F Gm : Nat -> Nat)
              -> ((a : Nat) -> Eq (evalF (prec g h) (cons (fbot a) Y))
                                  (fbot (Gm a)))
              -> ((a b : Nat) -> LeN N a
                    -> Eq (evalF h (cons (fbot a) (cons (fbot b) Y)))
                          (evalF h (cons (fbot N) (cons (fbot b) Y))))
              -> ((b : Nat) -> Eq (evalF h (cons (fbot N) (cons (fbot b) Y)))
                                  (fbot (F b)))
              -> Cpr F -> Expanding F
              -> Cpr Gm
prec-iter-Cpr g h Y N F Gm inc stab defF cprF expF =
  cpr-fchg {\ n -> G2 (predIter N n)} {Gm}
    (cpr-comp cprG2 (Cpr-predIter N)) incGm fchg
  where
    -- the recursion equation, from N on
    step : (a : Nat) -> LeN N a -> Eq (Gm (suc a)) (F (Gm a))
    step a le =
      fbot-inj (Gm (suc a)) (F (Gm a))
        (Eq-trans (Eq-sym (inc (suc a)))
          (Eq-trans (Eq-cong (\ z -> evalF h (cons (fbot a) (cons z Y)))
                       (inc a))
            (Eq-trans (stab a (Gm a) le) (defF (Gm a)))))

    G2 : Nat -> Nat
    G2 n = Gm (add N n)

    step2 : (n : Nat) -> Eq (G2 (suc n)) (F (G2 n))
    step2 n = step (add N n) (add-ge N n)

    cprG2 : Cpr G2
    cprG2 = cpr-iter cprF expF step2

    -- monotonicity of the intentional behaviour
    incGm : Increasing Gm
    incGm m n le =
      Eq-transport (\ z -> LeN z (Gm n))
        (Eq-cong hgt (inc m))
        (Eq-transport (\ z -> LeN (hgt (evalF (prec g h) (cons (fbot m) Y))) z)
          (Eq-cong hgt (inc n))
          (LeF-hgt (evalF (prec g h) (cons (fbot m) Y))
                   (evalF (prec g h) (cons (fbot n) Y))
            (evalF-mono (prec g h) (cons (fbot m) Y) (cons (fbot n) Y)
              (mkSigma le (LeFs-refl Y)))))

    fchg : FiniteChange (\ n -> G2 (predIter N n)) Gm
    fchg = mkSigma N (\ n le -> Eq-cong Gm (add-predIter N n le))
