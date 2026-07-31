{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecChain
--
-- THE RECURSION CHAIN, READ OFF THE STEP TERM'S TRACE ALONE.
--
--     f (bot   , Y) = bot
--     f (S^(j+1) bot , Y) = g ( S^j bot , f (S^j bot , Y) , Y )
--
-- (the manuscript's `g` is `TrPrec`'s step term, whose trace is `Th`).
-- While the recursive value `V j` is INCOMPLETE, every coordinate of the
-- step term's argument tuple
--
--     avT L j  =  ( S^j(bot) , V j , S^(L 1)(bot) , ... )
--
-- is a `fbot`, so the tuple is a `botTup` and `TrSat.sem-bot` collapses
-- the step term's semantics to a single lookup:
--
--     V (j+1)  =  ovh (NJ j)  ,   NJ j = nOf a ivh ivhr (heights of avT L j)
--
-- No continuation is ever entered -- a continuation is entered only at a
-- coordinate that has gone complete (`TraceDef.brf`), and none has.
--
-- That identity is the whole content of this file, and it is what lets
-- `TrPrecDecMP` decide "does the chain ever become a numeral?" from the
-- step term's OWN Verdict (MP1) instead of from Proposition 1 applied to
-- the recursion itself.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecChain where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (nOf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; cpl-max ; leF-hgt ; MonoTr ; botTup ; sem-bot)
open import OBSTINATION.TrPrec using (module R)

------------------------------------------------------------------------
-- TUPLES: congruence IN RANGE
--
-- `tup p f` reads `f` only below `p`, so pointwise equality below `p` is
-- all a congruence needs -- and all the chain has, since `avf` disagrees
-- with the `botTup` form outside the arity.
------------------------------------------------------------------------

tup-cong-le : (p : Nat) (f g : Nat -> FEl)
            -> ((c : Nat) -> LeN (suc c) p -> Eq (f c) (g c))
            -> Eq (tup p f) (tup p g)
tup-cong-le zero    f g e = refl
tup-cong-le (suc p) f g e =
  Eq-trans (Eq-cong (\ z -> cons z (tup p (\ d -> f (suc d)))) (e zero tt))
    (Eq-cong (cons (g zero))
      (tup-cong-le p (\ d -> f (suc d)) (\ d -> g (suc d))
        (\ d ld -> e (suc d) ld)))

------------------------------------------------------------------------
-- INCOMPLETE ELEMENTS
------------------------------------------------------------------------

-- `x` is incomplete, said as an equation so that it can be transported
Bt : FEl -> Set
Bt x = Eq x (fbot (hgt x))

bt-notCpl : (x : FEl) -> Bt x -> Not (IsCpl x)
bt-notCpl (fbot k) e ic = ic
bt-notCpl (fcpl k) e ic = fcpl-not-fbot k (hgt (fcpl k)) e
  where
    fcpl-not-fbot : (u v : Nat) -> Not (Eq (fcpl u) (fbot v))
    fcpl-not-fbot u v ()

notCpl-bt : (x : FEl) -> Not (IsCpl x) -> Bt x
notCpl-bt (fbot k) nc = refl
notCpl-bt (fcpl k) nc = Empty-elim (nc tt)

------------------------------------------------------------------------
-- THE CHAIN
------------------------------------------------------------------------

module CH (p : Nat)
          (ivh : Nat -> Nat)
          (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
          (ovh : Nat -> FEl)
          (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                 -> Tr (suc p))
          (L : Nat -> Nat)
          where

  a : Nat
  a = suc (suc p)

  Th : Tr a
  Th = node ivh ivhr ovh conth

  V : Nat -> FEl
  V = R.Vd p Th L

  XT : Nat -> FTup
  XT = R.avT p Th L

  -- the heights the step term's replay sees at depth `j`
  AV : Nat -> Nat -> Nat
  AV j = hts (XT j)

  -- ... and how far it replays there
  NJ : Nat -> Nat
  NJ j = nOf a ivh ivhr (AV j)

  --------------------------------------------------------------------
  -- the coordinates, in range
  --------------------------------------------------------------------

  av-nth : (j c : Nat) -> LeN (suc c) a
         -> Eq (nth (fbot zero) c (XT j)) (R.avf p Th L j c)
  av-nth j c lc = tup-nth a (R.avf p Th L j) c lc

  AV-in : (j c : Nat) -> LeN (suc c) a -> Eq (AV j c) (hgt (R.avf p Th L j c))
  AV-in j c lc = Eq-cong hgt (av-nth j c lc)

  AV-out : (c : Nat) -> Not (LeN (suc c) a) -> (j : Nat) -> Eq (AV j c) zero
  AV-out c nc j = Eq-cong hgt (tup-out a (R.avf p Th L j) c nc)

  -- coordinate 0 is the recursion argument, and it grows by one per depth
  AV-zero : (j : Nat) -> Eq (AV j zero) j
  AV-zero j = AV-in j zero tt

  -- coordinate 1 is the recursive value
  AV-one : (j : Nat) -> Eq (AV j (suc zero)) (hgt (V j))
  AV-one j = AV-in j (suc zero) tt

  -- everything above is a parameter, fixed once and for all
  AV-par : (i j j' : Nat) -> LeN (suc (suc (suc i))) a
         -> Eq (AV j (suc (suc i))) (AV j' (suc (suc i)))
  AV-par i j j' li =
    Eq-trans (AV-in j (suc (suc i)) li) (Eq-sym (AV-in j' (suc (suc i)) li))

  --------------------------------------------------------------------
  -- WHILE THE VALUE IS INCOMPLETE THE TUPLE IS A `botTup`
  --------------------------------------------------------------------

  botify : (j : Nat) -> Bt (V j) -> Eq (XT j) (botTup a (AV j))
  botify j bv = tup-cong-le a (R.avf p Th L j) (\ c -> fbot (AV j c)) pt
    where
      pt : (c : Nat) -> LeN (suc c) a -> Eq (R.avf p Th L j c) (fbot (AV j c))
      pt c lc =
        Eq-transport (\ z -> Eq (R.avf p Th L j c) (fbot z))
          (Eq-sym (AV-in j c lc)) (shape c lc)
        where
          shape : (d : Nat) -> LeN (suc d) a
                -> Eq (R.avf p Th L j d) (fbot (hgt (R.avf p Th L j d)))
          shape zero             ld = refl
          shape (suc zero)       ld = bv
          shape (suc (suc i))    ld = refl

  --------------------------------------------------------------------
  -- ... SO THE CHAIN STEP IS A SINGLE LOOKUP IN THE STEP TERM'S TRACE
  --------------------------------------------------------------------

  step : (j : Nat) -> Bt (V j) -> Eq (V (suc j)) (ovh (NJ j))
  step j bv =
    Eq-trans (Eq-cong (\ X -> sem a Th X) (botify j bv))
      (sem-bot a Th (AV j) (\ c nc -> AV-out c nc j))
