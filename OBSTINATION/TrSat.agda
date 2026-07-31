{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrSat
--
-- SATURATION: A BLOCKED COMPUTATION DOES NOT SEE ITS OTHER ARGUMENTS GROW.
--
-- This is the core both correctness proofs rest on, and it is min1.pdf's
-- Case 2 read at the level of traces: if the replay is stuck on
-- coordinate `c`, then raising every OTHER coordinate changes nothing.
--
--     sem-sat : X <= X'  ->  X and X' agree at `blockOn T X`
--             ->  sem T X = sem T X'
--
-- Two facts make it go through:
--
--   * `nOf-stick` -- the replay sticks at the SAME step against `X'`: it
--     gets at least as far (`nOf-ge` + `Adv-mono`), and no further, since
--     the step it is stuck on needs a level of a coordinate that has not
--     grown (`nOf-le`);
--   * completeness is MAXIMAL (`cpl-max`): if the stuck coordinate of `X`
--     is a numeral then so is that of `X'`, and they are equal -- so the
--     freeze branch is taken on both sides, with the same numeral, and
--     the induction goes into the continuation, where `Agr` transports
--     along `nth-del`.
--
-- `MonoTr` -- the value `ov` grows with the replay depth -- is needed for
-- the "already total" branch: `X'` may drive the replay further, and only
-- monotonicity says the answer there is still the same numeral.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrSat where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup ; LeFTup ; embedTup)
open import OBSTINATION.ReplayLv using
  (lv ; Adv ; Adv-mono ; nOf ; nOf-mono ; nOf-cong ; nOf-ge ; nOf-le ;
   nOf-below-adv ; stuck)
open import OBSTINATION.TraceDef

------------------------------------------------------------------------
-- finite elements: heights and maximality of the total ones
------------------------------------------------------------------------

IsCpl : FEl -> Set
IsCpl (fbot _) = Empty
IsCpl (fcpl _) = Top

leF-hgt : (x y : FEl) -> LeF x y -> LeN (hgt x) (hgt y)
leF-hgt (fbot j) (fbot k) le = le
leF-hgt (fbot j) (fcpl k) le = le
leF-hgt (fcpl j) (fbot k) ()
leF-hgt (fcpl j) (fcpl k) le =
  Eq-transport (\ z -> LeN j z) le (LeN-refl j)

cpl-max : (x y : FEl) -> LeF x y -> IsCpl x -> Eq x y
cpl-max (fbot j) y        le ()
cpl-max (fcpl j) (fbot k) () c
cpl-max (fcpl j) (fcpl k) le c = Eq-cong fcpl le

------------------------------------------------------------------------
-- pointwise order on tuples, and `del`
------------------------------------------------------------------------

LeX : FTup -> FTup -> Set
LeX X X' = (c : Nat) -> LeF (nth (fbot zero) c X) (nth (fbot zero) c X')

-- A monotone function of a tuple OF A GIVEN ARITY.  The arity cannot be
-- dropped: `LeX` compares by coordinate, with `fbot zero` out of range,
-- so `LeX (cons (fbot zero) nil) nil` holds -- and `evalF succ` sends
-- those to `fbot 1` and `fbot 0`.  Every use compares two tuples of the
-- term's own arity anyway.
MonoF : Nat -> (FTup -> FEl) -> Set
MonoF a f = (X X' : FTup) -> Eq (length X) a -> Eq (length X') a
          -> LeX X X' -> LeF (f X) (f X')

nth-del : (i c : Nat) (X : FTup)
        -> Eq (nth (fbot zero) c (del i X)) (nth (fbot zero) (su i c) X)
nth-del i       c       nil         = refl
nth-del zero    c       (cons x xs) = refl
nth-del (suc i) zero    (cons x xs) = refl
nth-del (suc i) (suc c) (cons x xs) = nth-del i c xs

LeX-del : (i : Nat) (X X' : FTup) -> LeX X X' -> LeX (del i X) (del i X')
LeX-del i X X' lx c =
  Eq-transport (\ z -> LeF z (nth (fbot zero) c (del i X')))
    (Eq-sym (nth-del i c X))
    (Eq-transport (\ z -> LeF (nth (fbot zero) (su i c) X) z)
      (Eq-sym (nth-del i c X')) (lx (su i c)))

-- at equal lengths `LeX` IS the structural order
LeX-LeFTup : (X X' : FTup) -> Eq (length X) (length X') -> LeX X X' -> LeFTup X X'
LeX-LeFTup nil         nil         e  le = tt
LeX-LeFTup nil         (cons y ys) () le
LeX-LeFTup (cons x xs) nil         () le
LeX-LeFTup (cons x xs) (cons y ys) e  le =
  mkSigma (le zero) (LeX-LeFTup xs ys (suc-inj e) (\ c -> le (suc c)))

LeX-hts : (X X' : FTup) -> LeX X X' -> (c : Nat) -> LeN (hts X c) (hts X' c)
LeX-hts X X' lx c =
  leF-hgt (nth (fbot zero) c X) (nth (fbot zero) c X') (lx c)

------------------------------------------------------------------------
-- THE REPLAY STICKS AT THE SAME STEP
------------------------------------------------------------------------

nOf-stick : (a : Nat) (iv : Nat -> Nat)
            (ivr : (n : Nat) -> LeN (suc (iv n)) a)
            (av av' : Nat -> Nat) -> ((c : Nat) -> LeN (av c) (av' c))
          -> Eq (av (iv (nOf a iv ivr av))) (av' (iv (nOf a iv ivr av)))
          -> Eq (nOf a iv ivr av) (nOf a iv ivr av')
nOf-stick a iv ivr av av' le eq =
  LeN-antisym {nOf a iv ivr av} {nOf a iv ivr av'} ge lo
  where
    n : Nat
    n = nOf a iv ivr av

    ge : LeN n (nOf a iv ivr av')
    ge = nOf-ge a iv ivr av' n
           (\ m lm -> Adv-mono a iv ivr av av' le m
                        (nOf-below-adv a iv ivr av m lm))

    nadv' : Not (Adv a iv ivr av' n)
    nadv' ad =
      stuck a iv ivr av
        (Eq-transport (\ z -> LeN (suc (lv a iv ivr (iv n) n)) z) (Eq-sym eq) ad)

    lo : LeN (nOf a iv ivr av') n
    lo = nOf-le a iv ivr av' n nadv'

------------------------------------------------------------------------
-- MONOTONE TRACES
------------------------------------------------------------------------

MonoTr : (a : Nat) -> Tr a -> Set
MonoTr a       (stop v)              = Top
MonoTr (suc a) (node iv ivr ov cont) =
  Pair ((m n : Nat) -> LeN m n -> LeF (ov m) (ov n))
       ((c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat) -> MonoTr a (cont c lc v))

------------------------------------------------------------------------
-- THE AGREEMENT HYPOTHESIS
------------------------------------------------------------------------

Agr : Or Top Nat -> FTup -> FTup -> Set
Agr (inl tt) X X' = Top
Agr (inr c)  X X' = Eq (nth (fbot zero) c X) (nth (fbot zero) c X')

------------------------------------------------------------------------
-- pushing the agreement into a continuation
------------------------------------------------------------------------

agDown : (i : Nat) (r : Or Top Nat) (X X' : FTup)
       -> Agr (shiftOr i r) X X' -> Agr r (del i X) (del i X')
agDown i (inl tt) X X' ag = tt
agDown i (inr j)  X X' ag =
  Eq-trans (nth-del i j X) (Eq-trans ag (Eq-sym (nth-del i j X')))

------------------------------------------------------------------------
-- SATURATION
------------------------------------------------------------------------

sem-sat : (a : Nat) (T : Tr a) -> MonoTr a T -> (X X' : FTup) -> LeX X X'
        -> Agr (blockOn a T X) X X'
        -> Eq (sem a T X) (sem a T X')
sem-sat a       (stop v)              mt X X' lx ag = refl
sem-sat (suc a) (node iv ivr ov cont) mt X X' lx ag = go (ov n) refl
  where
    n : Nat
    n = nOf (suc a) iv ivr (hts X)

    n' : Nat
    n' = nOf (suc a) iv ivr (hts X')

    nle : LeN n n'
    nle = nOf-mono (suc a) iv ivr (hts X) (hts X') (LeX-hts X X' lx)

    Tn : Tr a
    Tn = cont (iv n) (ivr n) (hts X (iv n))

    ALT : FEl
    ALT = sem a Tn (del (iv n) X)

    BLK : Or Top Nat
    BLK = shiftOr (iv n) (blockOn a Tn (del (iv n) X))

    nn : Eq (hts X (iv n)) (hts X' (iv n)) -> Eq n n'
    nn eh = nOf-stick (suc a) iv ivr (hts X) (hts X') (LeX-hts X X' lx) eh

    ------------------------------------------------------------------
    -- already total: `X'` may drive the replay further, but a total
    -- value is maximal, so the answer does not move
    ------------------------------------------------------------------
    total : (w : Nat) -> Eq (ov n) (fcpl w)
          -> Eq (sem (suc a) (node iv ivr ov cont) X)
                (sem (suc a) (node iv ivr ov cont) X')
    total w e =
      Eq-trans (Eq-cong (\ z -> hlt z BL) e)
        (Eq-sym (Eq-cong (\ z -> hlt z BL') e'))
      where
        BL : FEl
        BL = brf (ov n) ALT (nth (fbot zero) (iv n) X)

        BL' : FEl
        BL' = brf (ov n')
                (sem a (cont (iv n') (ivr n') (hts X' (iv n'))) (del (iv n') X'))
                (nth (fbot zero) (iv n') X')

        e' : Eq (ov n') (fcpl w)
        e' =
          Eq-trans
            (Eq-sym (cpl-max (ov n) (ov n') (fst mt n n' nle)
              (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt)))
            e

    ------------------------------------------------------------------
    -- not total: the replay is stuck on coordinate `iv n`
    ------------------------------------------------------------------
    partial : (w : Nat) -> Eq (ov n) (fbot w)
            -> Eq (sem (suc a) (node iv ivr ov cont) X)
                  (sem (suc a) (node iv ivr ov cont) X')
    partial w e = br (nth (fbot zero) (iv n) X) refl
      where
        br : (y : FEl) -> Eq (nth (fbot zero) (iv n) X) y
           -> Eq (sem (suc a) (node iv ivr ov cont) X)
                 (sem (suc a) (node iv ivr ov cont) X')
        ----------------------------------------------------------------
        -- BLOCKED: `Agr` says that coordinate did not move at all
        ----------------------------------------------------------------
        br (fbot j) ey = Eq-trans lhs (Eq-sym rhs)
          where
            blkEq : Eq (blockOn (suc a) (node iv ivr ov cont) X) (inr (iv n))
            blkEq =
              Eq-trans
                (Eq-cong
                  (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e)
                (Eq-cong (\ z -> bb (iv n) BLK z) ey)

            agc : Eq (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
            agc = Eq-transport (\ r -> Agr r X X') blkEq ag

            nEq : Eq n n'
            nEq = nn (Eq-cong hgt agc)

            lhs : Eq (sem (suc a) (node iv ivr ov cont) X) (fbot w)
            lhs =
              Eq-trans (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT z)) ey)
                (Eq-trans (Eq-cong (\ z -> hlt z (ov n)) e) e)

            ALT' : FEl
            ALT' = sem a (cont (iv n) (ivr n) (hts X' (iv n))) (del (iv n) X')

            eyX' : Eq (nth (fbot zero) (iv n) X') (fbot j)
            eyX' = Eq-trans (Eq-sym agc) ey

            rhs : Eq (sem (suc a) (node iv ivr ov cont) X') (fbot w)
            rhs =
              Eq-trans
                (Eq-cong
                  (\ z -> hlt (ov z)
                            (brf (ov z)
                              (sem a (cont (iv z) (ivr z) (hts X' (iv z)))
                                (del (iv z) X'))
                              (nth (fbot zero) (iv z) X')))
                  (Eq-sym nEq))
                (Eq-trans
                  (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT' z)) eyX')
                  (Eq-trans (Eq-cong (\ z -> hlt z (ov n)) e) e))
        ----------------------------------------------------------------
        -- A NUMERAL: total values are maximal, so `X'` has the SAME
        -- numeral there; both sides freeze and the induction goes on
        ----------------------------------------------------------------
        br (fcpl j) ey = Eq-trans left (Eq-trans mid (Eq-sym right))
          where
            agc : Eq (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
            agc =
              cpl-max (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
                (lx (iv n))
                (Eq-transport (\ z -> IsCpl z) (Eq-sym ey) tt)

            hEq : Eq (hts X (iv n)) (hts X' (iv n))
            hEq = Eq-cong hgt agc

            nEq : Eq n n'
            nEq = nn hEq

            eyX' : Eq (nth (fbot zero) (iv n) X') (fcpl j)
            eyX' = Eq-trans (Eq-sym agc) ey

            blkEq : Eq (blockOn (suc a) (node iv ivr ov cont) X) BLK
            blkEq =
              Eq-trans
                (Eq-cong
                  (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e)
                (Eq-cong (\ z -> bb (iv n) BLK z) ey)

            agIn : Agr (blockOn a Tn (del (iv n) X)) (del (iv n) X) (del (iv n) X')
            agIn =
              agDown (iv n) (blockOn a Tn (del (iv n) X)) X X'
                (Eq-transport (\ r -> Agr r X X') blkEq ag)

            ALT2 : FEl
            ALT2 = sem a Tn (del (iv n) X')

            ALT' : FEl
            ALT' = sem a (cont (iv n) (ivr n) (hts X' (iv n))) (del (iv n) X')

            left : Eq (sem (suc a) (node iv ivr ov cont) X) ALT
            left =
              Eq-trans (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT z)) ey)
                (Eq-cong (\ z -> hlt z ALT) e)

            mid : Eq ALT ALT'
            mid =
              Eq-trans
                (sem-sat a Tn (snd mt (iv n) (ivr n) (hts X (iv n)))
                  (del (iv n) X) (del (iv n) X') (LeX-del (iv n) X X' lx) agIn)
                (Eq-cong (\ z -> sem a (cont (iv n) (ivr n) z) (del (iv n) X')) hEq)

            right : Eq (sem (suc a) (node iv ivr ov cont) X') ALT'
            right =
              Eq-trans
                (Eq-cong
                  (\ z -> hlt (ov z)
                            (brf (ov z)
                              (sem a (cont (iv z) (ivr z) (hts X' (iv z)))
                                (del (iv z) X'))
                              (nth (fbot zero) (iv z) X')))
                  (Eq-sym nEq))
                (Eq-trans
                  (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT' z)) eyX')
                  (Eq-cong (\ z -> hlt z ALT') e))

    go : (y : FEl) -> Eq (ov n) y
       -> Eq (sem (suc a) (node iv ivr ov cont) X)
             (sem (suc a) (node iv ivr ov cont) X')
    go (fbot w) e = partial w e
    go (fcpl w) e = total w e

------------------------------------------------------------------------
-- THE VALUE AT AN ALL-INCOMPLETE TUPLE IS `ov` AT THE REPLAY DEPTH
--
-- On the incomplete cone no freeze can fire, so `sem` is just `ov` read
-- where the replay sticks.  This is the bridge between the two ways of
-- talking about a trace -- as a function (`sem`) and as a walk with a
-- value sequence (`iv`, `ov`) -- and it is what lets the composite's
-- `vals k` be read as "each argument evaluated at the levels obtained so
-- far".
------------------------------------------------------------------------

botTup : Nat -> (Nat -> Nat) -> FTup
botTup a av = tup a (\ c -> fbot (av c))

hts-botTup : (a : Nat) (av : Nat -> Nat)
           -> ((c : Nat) -> Not (LeN (suc c) a) -> Eq (av c) zero)
           -> (c : Nat) -> Eq (hts (botTup a av) c) (av c)
hts-botTup a av out c = route (LeN-dec (suc c) a)
  where
    route : Dec (LeN (suc c) a) -> Eq (hts (botTup a av) c) (av c)
    route (yes lc) = Eq-cong hgt (tup-nth a (\ d -> fbot (av d)) c lc)
    route (no  nc) =
      Eq-trans (Eq-cong hgt (tup-out a (\ d -> fbot (av d)) c nc))
        (Eq-sym (out c nc))

nth-botTup : (a : Nat) (av : Nat -> Nat) (c : Nat) -> LeN (suc c) a
           -> Eq (nth (fbot zero) c (botTup a av)) (fbot (av c))
nth-botTup a av c lc = tup-nth a (\ d -> fbot (av d)) c lc

sem-bot : (a : Nat) (T : Tr a) (av : Nat -> Nat)
        -> ((c : Nat) -> Not (LeN (suc c) a) -> Eq (av c) zero)
        -> Eq (sem a T (botTup a av)) (ovOf T (nOfOf a T av))
sem-bot a       (stop v)              av out = refl
sem-bot (suc a) (node iv ivr ov cont) av out =
  Eq-trans nEq
    (Eq-trans (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT z)) yEq)
      (hlt-idem (ov n)))
  where
    n : Nat
    n = nOf (suc a) iv ivr av

    nEq : Eq (sem (suc a) (node iv ivr ov cont) (botTup (suc a) av))
             (hlt (ov n)
               (brf (ov n)
                 (sem a (cont (iv n) (ivr n) (hts (botTup (suc a) av) (iv n)))
                   (del (iv n) (botTup (suc a) av)))
                 (nth (fbot zero) (iv n) (botTup (suc a) av))))
    nEq =
      Eq-cong
        (\ z -> hlt (ov z)
                  (brf (ov z)
                    (sem a (cont (iv z) (ivr z) (hts (botTup (suc a) av) (iv z)))
                      (del (iv z) (botTup (suc a) av)))
                    (nth (fbot zero) (iv z) (botTup (suc a) av))))
        (nOf-cong (suc a) iv ivr (hts (botTup (suc a) av)) av
          (hts-botTup (suc a) av out))

    ALT : FEl
    ALT = sem a (cont (iv n) (ivr n) (hts (botTup (suc a) av) (iv n)))
            (del (iv n) (botTup (suc a) av))

    yEq : Eq (nth (fbot zero) (iv n) (botTup (suc a) av)) (fbot (av (iv n)))
    yEq = nth-botTup (suc a) av (iv n) (ivr n)

    hlt-idem : (y : FEl) -> Eq (hlt y y) y
    hlt-idem (fbot w) = refl
    hlt-idem (fcpl w) = refl

------------------------------------------------------------------------
-- SATURATION FOR `blockOn` TOO
--
-- Same case analysis as `sem-sat`: a blocked computation not only keeps
-- its value when the other coordinates grow, it stays blocked on the
-- SAME coordinate.
------------------------------------------------------------------------

blockOn-sat : (a : Nat) (T : Tr a) -> MonoTr a T -> (X X' : FTup) -> LeX X X'
            -> Agr (blockOn a T X) X X'
            -> Eq (blockOn a T X) (blockOn a T X')
blockOn-sat a       (stop v)              mt X X' lx ag = refl
blockOn-sat (suc a) (node iv ivr ov cont) mt X X' lx ag = go (ov n) refl
  where
    n : Nat
    n = nOf (suc a) iv ivr (hts X)

    n' : Nat
    n' = nOf (suc a) iv ivr (hts X')

    nle : LeN n n'
    nle = nOf-mono (suc a) iv ivr (hts X) (hts X') (LeX-hts X X' lx)

    Tn : Tr a
    Tn = cont (iv n) (ivr n) (hts X (iv n))

    BLK : Or Top Nat
    BLK = shiftOr (iv n) (blockOn a Tn (del (iv n) X))

    nn : Eq (hts X (iv n)) (hts X' (iv n)) -> Eq n n'
    nn eh = nOf-stick (suc a) iv ivr (hts X) (hts X') (LeX-hts X X' lx) eh

    total : (w : Nat) -> Eq (ov n) (fcpl w)
          -> Eq (blockOn (suc a) (node iv ivr ov cont) X)
                (blockOn (suc a) (node iv ivr ov cont) X')
    total w e =
      Eq-trans (Eq-cong (\ z -> hb z BL) e)
        (Eq-sym (Eq-cong (\ z -> hb z BL') e'))
      where
        BL : Or Top Nat
        BL = bb (iv n) BLK (nth (fbot zero) (iv n) X)

        BL' : Or Top Nat
        BL' = bb (iv n')
                (shiftOr (iv n')
                  (blockOn a (cont (iv n') (ivr n') (hts X' (iv n')))
                    (del (iv n') X')))
                (nth (fbot zero) (iv n') X')

        e' : Eq (ov n') (fcpl w)
        e' =
          Eq-trans
            (Eq-sym (cpl-max (ov n) (ov n') (fst mt n n' nle)
              (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt)))
            e

    partial : (w : Nat) -> Eq (ov n) (fbot w)
            -> Eq (blockOn (suc a) (node iv ivr ov cont) X)
                  (blockOn (suc a) (node iv ivr ov cont) X')
    partial w e = br (nth (fbot zero) (iv n) X) refl
      where
        br : (y : FEl) -> Eq (nth (fbot zero) (iv n) X) y
           -> Eq (blockOn (suc a) (node iv ivr ov cont) X)
                 (blockOn (suc a) (node iv ivr ov cont) X')
        br (fbot j) ey = Eq-trans lhs (Eq-sym rhs)
          where
            blkEq : Eq (blockOn (suc a) (node iv ivr ov cont) X) (inr (iv n))
            blkEq =
              Eq-trans
                (Eq-cong
                  (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e)
                (Eq-cong (\ z -> bb (iv n) BLK z) ey)

            agc : Eq (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
            agc = Eq-transport (\ r -> Agr r X X') blkEq ag

            nEq : Eq n n'
            nEq = nn (Eq-cong hgt agc)

            lhs : Eq (blockOn (suc a) (node iv ivr ov cont) X) (inr (iv n))
            lhs = blkEq

            BLK' : Or Top Nat
            BLK' = shiftOr (iv n)
                     (blockOn a (cont (iv n) (ivr n) (hts X' (iv n)))
                       (del (iv n) X'))

            eyX' : Eq (nth (fbot zero) (iv n) X') (fbot j)
            eyX' = Eq-trans (Eq-sym agc) ey

            rhs : Eq (blockOn (suc a) (node iv ivr ov cont) X') (inr (iv n))
            rhs =
              Eq-trans
                (Eq-cong
                  (\ z -> hb (ov z)
                            (bb (iv z)
                              (shiftOr (iv z)
                                (blockOn a (cont (iv z) (ivr z) (hts X' (iv z)))
                                  (del (iv z) X')))
                              (nth (fbot zero) (iv z) X')))
                  (Eq-sym nEq))
                (Eq-trans
                  (Eq-cong (\ z -> hb z (bb (iv n) BLK' (nth (fbot zero) (iv n) X'))) e)
                  (Eq-cong (\ z -> bb (iv n) BLK' z) eyX'))
        br (fcpl j) ey = Eq-trans left (Eq-trans mid (Eq-sym right))
          where
            agc : Eq (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
            agc =
              cpl-max (nth (fbot zero) (iv n) X) (nth (fbot zero) (iv n) X')
                (lx (iv n))
                (Eq-transport (\ z -> IsCpl z) (Eq-sym ey) tt)

            hEq : Eq (hts X (iv n)) (hts X' (iv n))
            hEq = Eq-cong hgt agc

            nEq : Eq n n'
            nEq = nn hEq

            eyX' : Eq (nth (fbot zero) (iv n) X') (fcpl j)
            eyX' = Eq-trans (Eq-sym agc) ey

            blkEq : Eq (blockOn (suc a) (node iv ivr ov cont) X) BLK
            blkEq =
              Eq-trans
                (Eq-cong
                  (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e)
                (Eq-cong (\ z -> bb (iv n) BLK z) ey)

            agIn : Agr (blockOn a Tn (del (iv n) X)) (del (iv n) X) (del (iv n) X')
            agIn =
              agDown (iv n) (blockOn a Tn (del (iv n) X)) X X'
                (Eq-transport (\ r -> Agr r X X') blkEq ag)

            BLK' : Or Top Nat
            BLK' = shiftOr (iv n)
                     (blockOn a (cont (iv n) (ivr n) (hts X' (iv n)))
                       (del (iv n) X'))

            left : Eq (blockOn (suc a) (node iv ivr ov cont) X) BLK
            left = blkEq

            mid : Eq BLK BLK'
            mid =
              Eq-cong (shiftOr (iv n))
                (Eq-trans
                  (blockOn-sat a Tn (snd mt (iv n) (ivr n) (hts X (iv n)))
                    (del (iv n) X) (del (iv n) X') (LeX-del (iv n) X X' lx) agIn)
                  (Eq-cong
                    (\ z -> blockOn a (cont (iv n) (ivr n) z) (del (iv n) X')) hEq))

            right : Eq (blockOn (suc a) (node iv ivr ov cont) X') BLK'
            right =
              Eq-trans
                (Eq-cong
                  (\ z -> hb (ov z)
                            (bb (iv z)
                              (shiftOr (iv z)
                                (blockOn a (cont (iv z) (ivr z) (hts X' (iv z)))
                                  (del (iv z) X')))
                              (nth (fbot zero) (iv z) X')))
                  (Eq-sym nEq))
                (Eq-trans
                  (Eq-cong (\ z -> hb z (bb (iv n) BLK' (nth (fbot zero) (iv n) X'))) e)
                  (Eq-cong (\ z -> bb (iv n) BLK' z) eyX'))

    go : (y : FEl) -> Eq (ov n) y
       -> Eq (blockOn (suc a) (node iv ivr ov cont) X)
             (blockOn (suc a) (node iv ivr ov cont) X')
    go (fbot w) e = partial w e
    go (fcpl w) e = total w e
