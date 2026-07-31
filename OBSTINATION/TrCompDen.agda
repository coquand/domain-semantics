{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompDen
--
-- CORRECTNESS OF THE COMPOSITE TRACE:
--
--     Den p Tg g  ->  (each) Den a (Ths i) (h i)
--                 ->  Den a (compTr p Tg a Ths) (\ X -> g (h_ X))
--
-- The two branches of `sem` are settled by quite different means.
--
--   * The FREEZE branch is free: the composite's continuation is the
--     composite of the arguments' continuations, so the induction
--     hypothesis on the arity applies, and `ins-del` puts the numeral
--     back where the freeze took it out.
--
--   * The BLOCKED branch is the theorem.  `sem-bot` says each argument's
--     recorded value is what it denotes at the levels obtained so far,
--     `botTup (suc a) LK`; those levels are below `X` (`levels-below`),
--     so `vals K <= V` by monotonicity of the `h i`; and at the
--     coordinate `g` is waiting on, the two AGREE -- because the composite
--     sticks exactly where the selected argument sticks (`nOf-stick`,
--     via `stuck-level`).  `sem-sat` then equates `g`'s answers.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompDen where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using
  (bump ; bump-ne ; lv ; nOf ; nOf-cong ; levels-below ; nOf-below-adv)
open import OBSTINATION.WalkAffine using (stuck-level)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrDen
open import OBSTINATION.TrWalk
open import OBSTINATION.TrSat
open import OBSTINATION.TrComp
open import OBSTINATION.TrPrec using (InRange ; blockOn-range)

------------------------------------------------------------------------
-- monotone functions of a tuple
------------------------------------------------------------------------

-- `MonoF` itself lives in `TrSat`, next to `LeX`

LeX-ins : (c : Nat) (x : FEl) (Y Y' : FTup) -> LeX Y Y'
        -> LeX (ins c x Y) (ins c x Y')
LeX-ins c x Y Y' ly i = route (EqNat-dec i c)
  where
    atC : LeF (nth (fbot zero) c (ins c x Y)) (nth (fbot zero) c (ins c x Y'))
    atC =
      Eq-transport (\ z -> LeF z (nth (fbot zero) c (ins c x Y')))
        (Eq-sym (nth-ins-eq c x Y))
        (Eq-transport (\ z -> LeF x z) (Eq-sym (nth-ins-eq c x Y')) (LeF-refl x))

    route : Dec (Eq i c)
          -> LeF (nth (fbot zero) i (ins c x Y)) (nth (fbot zero) i (ins c x Y'))
    route (yes e) =
      Eq-transport
        (\ z -> LeF (nth (fbot zero) z (ins c x Y))
                    (nth (fbot zero) z (ins c x Y')))
        (Eq-sym e) atC
    route (no ne) =
      Eq-transport (\ z -> LeF z (nth (fbot zero) i (ins c x Y')))
        (Eq-sym (nth-ins-ne c i ne x Y))
        (Eq-transport (\ z -> LeF (nth (fbot zero) (sd c i) Y) z)
          (Eq-sym (nth-ins-ne c i ne x Y')) (ly (sd c i)))

------------------------------------------------------------------------
-- tuples
------------------------------------------------------------------------

tup-cong : (p : Nat) (f g : Nat -> FEl) -> ((i : Nat) -> Eq (f i) (g i))
         -> Eq (tup p f) (tup p g)
tup-cong zero    f g e = refl
tup-cong (suc p) f g e =
  Eq-trans (Eq-cong (\ z -> cons z (tup p (\ j -> f (suc j)))) (e zero))
    (Eq-cong (cons (g zero)) (tup-cong p (\ j -> f (suc j)) (\ j -> g (suc j))
      (\ j -> e (suc j))))

-- at arity zero a trace is a constant
ov0 : (T : Tr zero) (X : FTup) -> Eq (ovOf T zero) (sem zero T X)
ov0 (stop v) X = refl

------------------------------------------------------------------------
-- `blockOn` at an all-incomplete tuple
------------------------------------------------------------------------

blkBot : (a : Nat) -> Tr a -> (Nat -> Nat) -> Or Top Nat
blkBot a       (stop v)              av = inl tt
blkBot (suc a) (node iv ivr ov cont) av =
  hb (ov (nOf (suc a) iv ivr av)) (inr (iv (nOf (suc a) iv ivr av)))

blockOn-bot : (a : Nat) (T : Tr a) (av : Nat -> Nat)
            -> ((c : Nat) -> Not (LeN (suc c) a) -> Eq (av c) zero)
            -> Eq (blockOn a T (botTup a av)) (blkBot a T av)
blockOn-bot a       (stop v)              av out = refl
blockOn-bot (suc a) (node iv ivr ov cont) av out =
  Eq-trans nEq (Eq-cong (\ z -> hb (ov n) (bb (iv n) BLK z)) yEq)
  where
    n : Nat
    n = nOf (suc a) iv ivr av

    BLK : Or Top Nat
    BLK = shiftOr (iv n)
            (blockOn a (cont (iv n) (ivr n) (hts (botTup (suc a) av) (iv n)))
              (del (iv n) (botTup (suc a) av)))

    nEq : Eq (blockOn (suc a) (node iv ivr ov cont) (botTup (suc a) av))
             (hb (ov n)
               (bb (iv n) BLK (nth (fbot zero) (iv n) (botTup (suc a) av))))
    nEq =
      Eq-cong
        (\ z -> hb (ov z)
                  (bb (iv z)
                    (shiftOr (iv z)
                      (blockOn a
                        (cont (iv z) (ivr z) (hts (botTup (suc a) av) (iv z)))
                        (del (iv z) (botTup (suc a) av))))
                    (nth (fbot zero) (iv z) (botTup (suc a) av))))
        (nOf-cong (suc a) iv ivr (hts (botTup (suc a) av)) av
          (hts-botTup (suc a) av out))

    yEq : Eq (nth (fbot zero) (iv n) (botTup (suc a) av)) (fbot (av (iv n)))
    yEq = nth-botTup (suc a) av (iv n) (ivr n)

------------------------------------------------------------------------
-- a total value means nothing is being waited for
------------------------------------------------------------------------

sem-total : (a : Nat) (T : Tr a) (X : FTup) -> IsCpl (sem a T X)
          -> Eq (blockOn a T X) (inl tt)
sem-total a       (stop v)              X ic = refl
sem-total (suc a) (node iv ivr ov cont) X ic = go (ov n) refl
  where
    n : Nat
    n = nOf (suc a) iv ivr (hts X)

    Tn : Tr a
    Tn = cont (iv n) (ivr n) (hts X (iv n))

    ALT : FEl
    ALT = sem a Tn (del (iv n) X)

    BLK : Or Top Nat
    BLK = shiftOr (iv n) (blockOn a Tn (del (iv n) X))

    go : (y : FEl) -> Eq (ov n) y -> Eq (blockOn (suc a) (node iv ivr ov cont) X)
                                        (inl tt)
    go (fcpl w) e =
      Eq-cong (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e
    go (fbot w) e = br (nth (fbot zero) (iv n) X) refl
      where
        br : (y : FEl) -> Eq (nth (fbot zero) (iv n) X) y
           -> Eq (blockOn (suc a) (node iv ivr ov cont) X) (inl tt)
        br (fbot j) ey =
          Empty-elim
            (Eq-transport (\ z -> IsCpl z) e
              (Eq-transport (\ z -> IsCpl z)
                (Eq-trans (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT z)) ey)
                  (Eq-cong (\ z -> hlt z (ov n)) e)) ic))
        br (fcpl j) ey =
          Eq-trans
            (Eq-trans
              (Eq-cong (\ z -> hb z (bb (iv n) BLK (nth (fbot zero) (iv n) X))) e)
              (Eq-cong (\ z -> bb (iv n) BLK z) ey))
            (Eq-cong (shiftOr (iv n))
              (sem-total a Tn (del (iv n) X)
                (Eq-transport (\ z -> IsCpl z)
                  (Eq-trans (Eq-cong (\ z -> hlt (ov n) (brf (ov n) ALT z)) ey)
                    (Eq-cong (\ z -> hlt z ALT) e)) ic)))

------------------------------------------------------------------------
-- the shape of `blockOn` at an all-incomplete tuple
------------------------------------------------------------------------

blkBot-shape : (a : Nat) (T : Tr a) (av : Nat -> Nat)
             -> Or (Eq (blkBot a T av) (inl tt))
                   (Eq (blkBot a T av) (inr (ivOf T (nOfOf a T av))))
blkBot-shape a       (stop v)              av = inl refl
blkBot-shape (suc a) (node iv ivr ov cont) av = go (ov n) refl
  where
    n : Nat
    n = nOf (suc a) iv ivr av

    go : (y : FEl) -> Eq (ov n) y
       -> Or (Eq (hb (ov n) (inr (iv n))) (inl tt))
             (Eq (hb (ov n) (inr (iv n))) (inr (iv n)))
    go (fcpl w) e = inl (Eq-cong (\ z -> hb z (inr (iv n))) e)
    go (fbot w) e = inr (Eq-cong (\ z -> hb z (inr (iv n))) e)

------------------------------------------------------------------------
-- misc
------------------------------------------------------------------------

leF-bot : (m : Nat) (y : FEl) -> LeN m (hgt y) -> LeF (fbot m) y
leF-bot m (fbot k) le = le
leF-bot m (fcpl k) le = le

monoTr-cont : (a : Nat) (T : Tr (suc a)) -> MonoTr (suc a) T
            -> (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
            -> MonoTr a (contOf T c lc v)
monoTr-cont a (stop w)              mt c lc v = tt
monoTr-cont a (node iv ivr ov cont) mt c lc v = snd mt c lc v

------------------------------------------------------------------------
-- CORRECTNESS OF THE COMPOSITE TRACE
------------------------------------------------------------------------

compTr-den :
    (p : Nat) (Tg : Tr p) (g : FTup -> FEl) -> MonoTr p Tg -> Den p Tg g
  -> (a : Nat) (Ths : Nat -> Tr a) (h : Nat -> FTup -> FEl)
  -> ((i : Nat) -> MonoTr a (Ths i)) -> ((i : Nat) -> MonoF a (h i))
  -> ((i : Nat) -> Den a (Ths i) (h i))
  -> Den a (compTr p Tg a Ths) (\ X -> g (tup p (\ i -> h i X)))
compTr-den p Tg g mg dg zero Ths h mTh mh dh = base
  where
    base : (X : FTup) -> Eq (length X) zero
         -> Eq (sem p Tg (tup p (\ i -> ovOf (Ths i) zero)))
               (g (tup p (\ i -> h i X)))
    base X lx =
      Eq-trans
        (Eq-cong (sem p Tg)
          (tup-cong p (\ i -> ovOf (Ths i) zero) (\ i -> h i X)
            (\ i -> Eq-trans (ov0 (Ths i) X)
                      (den-sem zero (Ths i) (h i) (dh i) X lx))))
        (den-sem p Tg g dg (tup p (\ i -> h i X)) (tup-len p (\ i -> h i X)))
compTr-den p Tg g mg dg (suc a) Ths h mTh mh dh = mkSigma main conts
  where
    module WW = W p Tg a Ths

    conts : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
          -> Den a (compTr p Tg a (\ i -> contOf (Ths i) c lc v))
                 (\ Y -> g (tup p (\ i -> h i (ins c (fcpl v) Y))))
    conts c lc v =
      compTr-den p Tg g mg dg a (\ i -> contOf (Ths i) c lc v)
        (\ i Y -> h i (ins c (fcpl v) Y))
        (\ i -> monoTr-cont a (Ths i) (mTh i) c lc v)
        (\ i Y Y' ly ly' l ->
           mh i (ins c (fcpl v) Y) (ins c (fcpl v) Y')
             (insLen Y ly) (insLen Y' ly') (LeX-ins c (fcpl v) Y Y' l))
        (\ i -> den-cont a (Ths i) (h i) (dh i) c lc v)
      where
        insLen : (Y : FTup) -> Eq (length Y) a
               -> Eq (length (ins c (fcpl v) Y)) (suc a)
        insLen Y ly =
          Eq-trans
            (ins-len c (fcpl v) Y
              (Eq-transport (\ z -> LeN c z) (Eq-sym ly) lc))
            (Eq-cong suc ly)

    main : (X : FTup) -> Eq (length X) (suc a)
         -> Eq (sem (suc a) (compTr p Tg (suc a) Ths) X)
               (g (tup p (\ i -> h i X)))
    main X lx = go (WW.ovf K) refl
      where
        K : Nat
        K = nOf (suc a) WW.ivf WW.ivfr (hts X)

        LK : Nat -> Nat
        LK = WW.L K

        cK : Nat
        cK = WW.ivf K

        V : FTup
        V = tup p (\ i -> h i X)

        ALT : FEl
        ALT = sem a (compTr p Tg a
                      (\ i -> contOf (Ths i) cK (WW.ivfr K) (hts X cK)))
                (del cK X)

        BL : FEl
        BL = brf (WW.ovf K) ALT (nth (fbot zero) cK X)

        lvL : (c : Nat) -> Eq (lv (suc a) WW.ivf WW.ivfr c K) (LK c)
        lvL c = lv-L (suc a) WW.ivf WW.ivfr WW.L (\ _ -> refl) (\ _ _ -> refl) K c

        belowX : (c : Nat) -> LeN (LK c) (hts X c)
        belowX c =
          Eq-transport (\ z -> LeN z (hts X c)) (lvL c)
            (levels-below (suc a) WW.ivf WW.ivfr (hts X) K
              (nOf-below-adv (suc a) WW.ivf WW.ivfr (hts X)) c)

        stuckX : Eq (LK cK) (hts X cK)
        stuckX =
          Eq-transport (\ z -> Eq z (hts X cK)) (lvL cK)
            (stuck-level (suc a) WW.ivf WW.ivfr (hts X))

        L-out0 : (k c : Nat) -> Not (LeN (suc c) (suc a)) -> Eq (WW.L k c) zero
        L-out0 zero    c nc = refl
        L-out0 (suc k) c nc =
          Eq-trans
            (bump-ne (WW.ivf k) (WW.L k) c
              (\ e -> nc (Eq-transport (\ z -> LeN (suc z) (suc a))
                            (Eq-sym e) (WW.ivfr k))))
            (L-out0 k c nc)

        L-out : (c : Nat) -> Not (LeN (suc c) (suc a)) -> Eq (LK c) zero
        L-out c nc = L-out0 K c nc

        BT : FTup
        BT = botTup (suc a) LK

        BTlen : Eq (length BT) (suc a)
        BTlen = tup-len (suc a) (\ c -> fbot (LK c))

        leBot : LeX BT X
        leBot c = route (LeN-dec (suc c) (suc a))
          where
            route : Dec (LeN (suc c) (suc a))
                  -> LeF (nth (fbot zero) c BT) (nth (fbot zero) c X)
            route (yes lc) =
              Eq-transport (\ z -> LeF z (nth (fbot zero) c X))
                (Eq-sym (nth-botTup (suc a) LK c lc))
                (leF-bot (LK c) (nth (fbot zero) c X) (belowX c))
            route (no nc) =
              Eq-transport (\ z -> LeF z (nth (fbot zero) c X))
                (Eq-sym (tup-out (suc a) (\ d -> fbot (LK d)) c nc))
                (leF-bot zero (nth (fbot zero) c X) tt)

        valsE : (i : Nat) -> LeN (suc i) p
              -> Eq (nth (fbot zero) i (WW.vals K)) (h i BT)
        valsE i li =
          Eq-trans (tup-nth p (\ j -> ovOf (Ths j) (WW.dep K j)) i li)
            (Eq-trans (Eq-sym (sem-bot (suc a) (Ths i) LK L-out))
              (den-sem (suc a) (Ths i) (h i) (dh i) BT BTlen))

        lex : LeX (WW.vals K) V
        lex i = route (LeN-dec (suc i) p)
          where
            route : Dec (LeN (suc i) p)
                  -> LeF (nth (fbot zero) i (WW.vals K)) (nth (fbot zero) i V)
            route (yes li) =
              Eq-transport (\ z -> LeF z (nth (fbot zero) i V))
                (Eq-sym (valsE i li))
                (Eq-transport (\ z -> LeF (h i BT) z)
                  (Eq-sym (tup-nth p (\ j -> h j X) i li))
                  (mh i BT X BTlen lx leBot))
            route (no ni) =
              Eq-transport (\ z -> LeF z (nth (fbot zero) i V))
                (Eq-sym (tup-out p (\ j -> ovOf (Ths j) (WW.dep K j)) i ni))
                (Eq-transport (\ z -> LeF (fbot zero) z)
                  (Eq-sym (tup-out p (\ j -> h j X) i ni))
                  (LeF-refl (fbot zero)))

        gEq : Agr (blockOn p Tg (WW.vals K)) (WW.vals K) V -> Eq (WW.ovf K) (g V)
        gEq agr =
          Eq-trans (sem-sat p Tg mg (WW.vals K) V lex agr)
            (den-sem p Tg g dg V (tup-len p (\ i -> h i X)))

        go : (y : FEl) -> Eq (WW.ovf K) y
           -> Eq (sem (suc a) (compTr p Tg (suc a) Ths) X) (g V)
        ------------------------------------------------------------------
        -- `g` has already answered: nothing is being waited for
        ------------------------------------------------------------------
        go (fcpl w) e = Eq-trans semTot (gEq agrTot)
          where
            semTot : Eq (sem (suc a) (compTr p Tg (suc a) Ths) X) (WW.ovf K)
            semTot = Eq-trans (Eq-cong (\ z -> hlt z BL) e) (Eq-sym e)

            agrTot : Agr (blockOn p Tg (WW.vals K)) (WW.vals K) V
            agrTot =
              Eq-transport (\ r -> Agr r (WW.vals K) V)
                (Eq-sym (sem-total p Tg (WW.vals K)
                          (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt)))
                tt
        go (fbot w) e = br (nth (fbot zero) cK X) refl
          where
            br : (y : FEl) -> Eq (nth (fbot zero) cK X) y
               -> Eq (sem (suc a) (compTr p Tg (suc a) Ths) X) (g V)
            ------------------------------------------------------------
            -- BLOCKED: the composite sticks where the selected argument
            -- sticks, so `vals K` and `V` agree at the coordinate `g`
            -- is waiting on
            ------------------------------------------------------------
            br (fbot j) ey = Eq-trans semBlk (gEq agrBlk)
              where
                semBlk : Eq (sem (suc a) (compTr p Tg (suc a) Ths) X) (WW.ovf K)
                semBlk =
                  Eq-trans
                    (Eq-cong (\ z -> hlt (WW.ovf K) (brf (WW.ovf K) ALT z)) ey)
                    (Eq-cong (\ z -> hlt z (WW.ovf K)) e)

                agrBlk : Agr (blockOn p Tg (WW.vals K)) (WW.vals K) V
                agrBlk = go2 (blockOn p Tg (WW.vals K)) refl
                  where
                    go2 : (r : Or Top Nat) -> Eq (blockOn p Tg (WW.vals K)) r
                        -> Agr r (WW.vals K) V
                    go2 (inl tt) er = tt
                    go2 (inr c)  er =
                      Eq-trans (valsE c lc) (Eq-trans hEq
                        (Eq-sym (tup-nth p (\ j -> h j X) c lc)))
                      where
                        lc : LeN (suc c) p
                        lc = Eq-transport (\ z -> InRange p z) er
                               (blockOn-range p Tg (WW.vals K))

                        selE : Eq (WW.selC K) c
                        selE = Eq-cong orC er

                        iE : Eq (ivOf (Ths c) (nOfOf (suc a) (Ths c) LK)) cK
                        iE =
                          Eq-sym (Eq-cong (\ z -> ivOf (Ths z) (WW.dep K z)) selE)

                        atK : Eq (nth (fbot zero) cK BT) (nth (fbot zero) cK X)
                        atK =
                          Eq-trans (nth-botTup (suc a) LK cK (WW.ivfr K))
                            (Eq-trans
                              (Eq-cong fbot (Eq-trans stuckX (Eq-cong hgt ey)))
                              (Eq-sym ey))

                        agr2 : Agr (blockOn (suc a) (Ths c) BT) BT X
                        agr2 = route (blkBot-shape (suc a) (Ths c) LK)
                          where
                            bEq : Eq (blockOn (suc a) (Ths c) BT)
                                     (blkBot (suc a) (Ths c) LK)
                            bEq = blockOn-bot (suc a) (Ths c) LK L-out

                            route : Or (Eq (blkBot (suc a) (Ths c) LK) (inl tt))
                                       (Eq (blkBot (suc a) (Ths c) LK)
                                          (inr (ivOf (Ths c)
                                                 (nOfOf (suc a) (Ths c) LK))))
                                  -> Agr (blockOn (suc a) (Ths c) BT) BT X
                            route (inl q) =
                              Eq-transport (\ r -> Agr r BT X)
                                (Eq-sym (Eq-trans bEq q)) tt
                            route (inr q) =
                              Eq-transport (\ r -> Agr r BT X)
                                (Eq-sym (Eq-trans bEq q))
                                (Eq-transport
                                  (\ z -> Eq (nth (fbot zero) z BT)
                                             (nth (fbot zero) z X))
                                  (Eq-sym iE) atK)

                        hEq : Eq (h c BT) (h c X)
                        hEq =
                          Eq-trans
                            (Eq-sym (den-sem (suc a) (Ths c) (h c) (dh c) BT BTlen))
                            (Eq-trans
                              (sem-sat (suc a) (Ths c) (mTh c) BT X leBot agr2)
                              (den-sem (suc a) (Ths c) (h c) (dh c) X lx))
            ------------------------------------------------------------
            -- FREEZE: the continuation is the composite of the
            -- continuations, and `ins-del` puts the numeral back
            ------------------------------------------------------------
            br (fcpl v) ey = Eq-trans semFrz (Eq-trans contD insD)
              where
                semFrz : Eq (sem (suc a) (compTr p Tg (suc a) Ths) X) ALT
                semFrz =
                  Eq-trans
                    (Eq-cong (\ z -> hlt (WW.ovf K) (brf (WW.ovf K) ALT z)) ey)
                    (Eq-cong (\ z -> hlt z ALT) e)

                lenCK : LeN (suc cK) (length X)
                lenCK =
                  Eq-transport (\ z -> LeN (suc cK) z) (Eq-sym lx) (WW.ivfr K)

                contD : Eq ALT
                          (g (tup p (\ i -> h i
                               (ins cK (fcpl (hts X cK)) (del cK X)))))
                contD =
                  den-sem a
                    (compTr p Tg a
                      (\ i -> contOf (Ths i) cK (WW.ivfr K) (hts X cK)))
                    (\ Y -> g (tup p (\ i -> h i (ins cK (fcpl (hts X cK)) Y))))
                    (conts cK (WW.ivfr K) (hts X cK))
                    (del cK X)
                    (suc-inj (Eq-trans (del-len cK X lenCK) lx))

                hv : Eq (fcpl (hts X cK)) (nth (fbot zero) cK X)
                hv = Eq-trans (Eq-cong fcpl (Eq-cong hgt ey)) (Eq-sym ey)

                insD : Eq (g (tup p (\ i -> h i
                             (ins cK (fcpl (hts X cK)) (del cK X))))) (g V)
                insD =
                  Eq-cong (\ Y -> g (tup p (\ i -> h i Y)))
                    (Eq-trans (Eq-cong (\ z -> ins cK z (del cK X)) hv)
                      (ins-del cK X lenCK))
