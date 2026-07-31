{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrVerdict
--
-- MIN1.PDF'S THREE CASES ARE PROPOSITION 1, READ ALONG THE WALK'S OWN
-- LEVEL CHAIN.
--
-- Half of MP1 -- `Verdict ov` -- needs no new combinatorics at all.  It
-- follows from `Property.UO` (Proposition 1, already proved for every PR
-- term in `Prop1`) TOGETHER WITH the other half, `EvConstN iv`.
--
-- The bridge is `ov-bot`.  For any `node iv ivr ov cont`,
--
--     ov k  =  sem (node ..) (botTup (suc a) (lv . k))
--
-- -- the value at replay depth `k` is the trace evaluated at ITS OWN
-- levels after `k` steps.  (`sem-bot` gives the value as `ov` at the
-- replay depth, and `nOf-own` says the walk replayed against its own
-- levels gets exactly `k` steps: every earlier step advances because the
-- level it needs was raised, and step `k` cannot because it was not.)
-- With `Den`, that reads
--
--     ov k = F (botTup (suc a) (lv . k)) .
--
-- Now let `N` be the threshold of `EvConstN iv` and `I = iv N`.  Past
-- `N` the walk raises ONLY coordinate `I`, so
--
--     ov (N + t) = F ( A0 with coordinate I set to S^(l_I(N) + t)(bot) ) ,
--
-- the other coordinates frozen at `l_c(N)`.  That is EXACTLY the family
-- `UO` speaks about, at the point `A` whose coordinate `I` is
-- `S^omega(bot)` and whose other coordinates are `S^(l_c(N))(bot)`:
--
--   * `UO`'s Case 1 -- `F` is `S^m(0)` above a finite `A0` -- gives
--     `EvTot ov`  (min1.pdf Case 1);
--   * `UO`'s Case 2 -- pinned at a coordinate `i` with `A(i)` incomplete
--     FINITE, so `i /= I` -- gives `ov` eventually CONSTANT
--     (min1.pdf Case 2);
--   * `UO`'s Case 3 -- at the infinite coordinate, which must be `I` --
--     hands over its own `phi`, and `hgt (ov (N+t)) = phi (l_I(N) + t)`
--     (min1.pdf Cases 2 and 3, according to `PhiOK phi`).
--
-- This is the formal content of IMG_0269: the trace's value sequence IS
-- the term evaluated along `x_I := S(x_I)` with the other variables held
-- fixed, and Proposition 1 is precisely the statement about that
-- sequence.
--
-- So of MP1 only `EvConstN iv` -- the SEQUENTIALITY INDEX -- is left to
-- prove structurally.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrVerdict where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property using
  (UO ; uo1 ; uo2 ; uo3 ; getF ; IncompleteFinite)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r ; LeN-suc-not)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1 using
  (PhiOK ; plus-ge-l ; phiok-reindex ; phiok-cong-from ; phiok-shift-r)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; bump-ne ; lv ; Adv ; nOf ; nOf-ge ; nOf-le)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrDen
open import OBSTINATION.TrWalk using (den-sem)
open import OBSTINATION.TrMono using (lev-mono)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict)

------------------------------------------------------------------------
-- TUPLES OVER `D`
------------------------------------------------------------------------

dtup : Nat -> (Nat -> D) -> Tup
dtup zero    f = nil
dtup (suc n) f = cons (f zero) (dtup n (\ j -> f (suc j)))

dtup-len : (n : Nat) (f : Nat -> D) -> Eq (length (dtup n f)) n
dtup-len zero    f = refl
dtup-len (suc n) f = Eq-cong suc (dtup-len n (\ j -> f (suc j)))

dtup-nth : (n : Nat) (f : Nat -> D) (c : Nat) -> LeN (suc c) n
         -> Eq (get c (dtup n f)) (f c)
dtup-nth zero    f c       ()
dtup-nth (suc n) f zero    lc = refl
dtup-nth (suc n) f (suc c) lc = dtup-nth n (\ j -> f (suc j)) c lc

dtup-out : (n : Nat) (f : Nat -> D) (c : Nat) -> Not (LeN (suc c) n)
         -> Eq (get c (dtup n f)) botD
dtup-out zero    f c       nc = refl
dtup-out (suc n) f zero    nc = Empty-elim (nc tt)
dtup-out (suc n) f (suc c) nc = dtup-out n (\ j -> f (suc j)) c nc

get-embedTup : (c : Nat) (X : FTup)
             -> Eq (get c (embedTup X)) (embed (getF c X))
get-embedTup c       nil         = refl
get-embedTup zero    (cons x xs) = refl
get-embedTup (suc c) (cons x xs) = get-embedTup c xs

embedTup-len : (X : FTup) -> Eq (length (embedTup X)) (length X)
embedTup-len nil         = refl
embedTup-len (cons x xs) = Eq-cong suc (embedTup-len xs)

LeTup-len : (A B : Tup) -> LeTup A B -> Eq (length A) (length B)
LeTup-len nil         nil         le = refl
LeTup-len nil         (cons _ _)  ()
LeTup-len (cons _ _)  nil         ()
LeTup-len (cons x xs) (cons y ys) le = Eq-cong suc (LeTup-len xs ys (snd le))

------------------------------------------------------------------------
-- SMALL FACTS ABOUT `D`
------------------------------------------------------------------------

bot-not-inf : (j : Nat) -> Not (Eq (bot j) inf)
bot-not-inf j ()

embed-bot : (x : FEl) (m : Nat) -> Eq (embed x) (bot m) -> Eq x (fbot m)
embed-bot (fbot j) m refl = refl
embed-bot (fcpl j) m ()

below-bot : (x : FEl) (m : Nat) -> LeD (embed x) (bot m) -> Eq x (fbot (hgt x))
below-bot (fbot j) m le = refl
below-bot (fcpl j) m ()

below-bot-le : (x : FEl) (m : Nat) -> LeD (embed x) (bot m) -> LeN (hgt x) m
below-bot-le (fbot j) m le = le
below-bot-le (fcpl j) m ()

below-inf : (x : FEl) -> LeD (embed x) inf -> Eq x (fbot (hgt x))
below-inf (fbot j) le = refl
below-inf (fcpl j) ()

notCpl-shape : (x : FEl) -> Not (IsCpl x) -> Eq x (fbot (hgt x))
notCpl-shape (fbot j) nc = refl
notCpl-shape (fcpl j) nc = Empty-elim (nc tt)

fbot-notCpl : (x : FEl) (m : Nat) -> Eq x (fbot m) -> Not (IsCpl x)
fbot-notCpl x m e ic = Eq-transport (\ z -> IsCpl z) e ic

------------------------------------------------------------------------
-- THE POINT `A`: coordinate `I` infinite, the rest frozen at `L`
------------------------------------------------------------------------

orD : {A : Set} -> D -> D -> Dec A -> D
orD x y (yes _) = x
orD x y (no  _) = y

ptD : Nat -> (Nat -> Nat) -> Nat -> D
ptD I L c = orD inf (bot (L c)) (EqNat-dec c I)

ptD-I : (I : Nat) (L : Nat -> Nat) -> Eq (ptD I L I) inf
ptD-I I L = go (EqNat-dec I I) refl
  where
    go : (D0 : Dec (Eq I I)) -> Eq (EqNat-dec I I) D0 -> Eq (ptD I L I) inf
    go (yes _)  e = Eq-cong (orD inf (bot (L I))) e
    go (no  ne) e = Empty-elim (ne refl)

ptD-ne : (I : Nat) (L : Nat -> Nat) (c : Nat) -> Not (Eq c I)
       -> Eq (ptD I L c) (bot (L c))
ptD-ne I L c nc = go (EqNat-dec c I) refl
  where
    go : (D0 : Dec (Eq c I)) -> Eq (EqNat-dec c I) D0
       -> Eq (ptD I L c) (bot (L c))
    go (yes e) _  = Empty-elim (nc e)
    go (no  _) e  = Eq-cong (orD inf (bot (L c))) e

------------------------------------------------------------------------
-- THE WALK REPLAYED AGAINST ITS OWN LEVELS
------------------------------------------------------------------------

module W (a : Nat) (iv : Nat -> Nat)
         (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a)) where

  lvk : Nat -> Nat -> Nat
  lvk k c = lv (suc a) iv ivr c k

  lvk-step : (k c : Nat) -> Eq (lvk (suc k) c) (bump (iv k) (lvk k) c)
  lvk-step k c = refl

  lvk-mono : (m n : Nat) -> LeN m n -> (c : Nat) -> LeN (lvk m c) (lvk n c)
  lvk-mono = lev-mono iv lvk lvk-step

  lvk-out : (c : Nat) -> Not (LeN (suc c) (suc a)) -> (k : Nat)
          -> Eq (lvk k c) zero
  lvk-out c nc zero    = refl
  lvk-out c nc (suc k) =
    Eq-trans
      (bump-ne (iv k) (lvk k) c
        (\ e -> nc (Eq-transport (\ z -> LeN (suc z) (suc a))
                      (Eq-sym e) (ivr k))))
      (lvk-out c nc k)

  -- THE WALK GETS EXACTLY `k` STEPS AGAINST ITS OWN LEVELS AT STEP `k`
  nOf-own : (k : Nat) -> Eq (nOf (suc a) iv ivr (lvk k)) k
  nOf-own k = LeN-antisym {nOf (suc a) iv ivr (lvk k)} {k} lo ge
    where
      ge : LeN k (nOf (suc a) iv ivr (lvk k))
      ge = nOf-ge (suc a) iv ivr (lvk k) k adv
        where
          adv : (n : Nat) -> LeN (suc n) k -> Adv (suc a) iv ivr (lvk k) n
          adv n ln =
            Eq-transport (\ z -> LeN z (lvk k (iv n)))
              (bump-eq (iv n) (lvk n) (iv n) refl)
              (lvk-mono (suc n) k ln (iv n))

      lo : LeN (nOf (suc a) iv ivr (lvk k)) k
      lo = nOf-le (suc a) iv ivr (lvk k) k
             (\ ad -> LeN-suc-not (lvk k (iv k)) ad)

------------------------------------------------------------------------
-- THE VALUE SEQUENCE IS THE FUNCTION ALONG THE LEVEL CHAIN
------------------------------------------------------------------------

ov-bot : (a : Nat) (iv : Nat -> Nat)
         (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a))
         (ov : Nat -> FEl)
         (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
       -> (k : Nat)
       -> Eq (sem (suc a) (node iv ivr ov cont)
               (botTup (suc a) (W.lvk a iv ivr k)))
             (ov k)
ov-bot a iv ivr ov cont k =
  Eq-trans
    (sem-bot (suc a) (node iv ivr ov cont) (W.lvk a iv ivr k)
      (\ c nc -> W.lvk-out a iv ivr c nc k))
    (Eq-cong ov (W.nOf-own a iv ivr k))

------------------------------------------------------------------------
-- THE VERDICT
------------------------------------------------------------------------

module V (a : Nat) (iv : Nat -> Nat)
         (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a))
         (ov : Nat -> FEl)
         (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
         (F : FTup -> FEl)
         (dn : Den (suc a) (node iv ivr ov cont) F)
         (mono : (m n : Nat) -> LeN m n -> LeF (ov m) (ov n))
         (N : Nat) (stab : (n : Nat) -> LeN N n -> Eq (iv n) (iv N))
         where

  open W a iv ivr

  I : Nat
  I = iv N

  lI : LeN (suc I) (suc a)
  lI = ivr N

  LN : Nat -> Nat
  LN = lvk N

  --------------------------------------------------------------------
  -- past the threshold only coordinate `I` moves
  --------------------------------------------------------------------

  lvk-fix : (c : Nat) -> Not (Eq c I) -> (t : Nat)
          -> Eq (lvk (plus t N) c) (LN c)
  lvk-fix c nc zero    = refl
  lvk-fix c nc (suc t) =
    Eq-trans
      (bump-ne (iv (plus t N)) (lvk (plus t N)) c
        (\ e -> nc (Eq-trans e (stab (plus t N) (plus-ge-r t N)))))
      (lvk-fix c nc t)

  lvk-run : (t : Nat) -> Eq (lvk (plus t N) I) (plus t (LN I))
  lvk-run zero    = refl
  lvk-run (suc t) =
    Eq-trans
      (bump-eq (iv (plus t N)) (lvk (plus t N)) I
        (Eq-sym (stab (plus t N) (plus-ge-r t N))))
      (Eq-cong suc (lvk-run t))

  --------------------------------------------------------------------
  -- the family of finite tuples, and the point above it
  --------------------------------------------------------------------

  XT : Nat -> FTup
  XT t = botTup (suc a) (lvk (plus t N))

  XTlen : (t : Nat) -> Eq (length (XT t)) (suc a)
  XTlen t = tup-len (suc a) (\ c -> fbot (lvk (plus t N) c))

  XT-nth : (t c : Nat) -> LeN (suc c) (suc a)
         -> Eq (getF c (XT t)) (fbot (lvk (plus t N) c))
  XT-nth t c lc = nth-botTup (suc a) (lvk (plus t N)) c lc

  XT-out : (t c : Nat) -> Not (LeN (suc c) (suc a))
         -> Eq (getF c (XT t)) (fbot zero)
  XT-out t c nc = tup-out (suc a) (\ d -> fbot (lvk (plus t N) d)) c nc

  XT-I : (t : Nat) -> Eq (getF I (XT t)) (fbot (plus t (LN I)))
  XT-I t = Eq-trans (XT-nth t I lI) (Eq-cong fbot (lvk-run t))

  XT-ne : (t c : Nat) -> LeN (suc c) (suc a) -> Not (Eq c I)
        -> Eq (getF c (XT t)) (fbot (LN c))
  XT-ne t c lc nc = Eq-trans (XT-nth t c lc) (Eq-cong fbot (lvk-fix c nc t))

  -- the value sequence, past the threshold
  ovX : (t : Nat) -> Eq (ov (plus t N)) (F (XT t))
  ovX t =
    Eq-trans (Eq-sym (ov-bot a iv ivr ov cont (plus t N)))
      (den-sem (suc a) (node iv ivr ov cont) F dn (XT t) (XTlen t))

  A : Tup
  A = dtup (suc a) (ptD I LN)

  Alen : Eq (length A) (suc a)
  Alen = dtup-len (suc a) (ptD I LN)

  getA-I : Eq (get I A) inf
  getA-I = Eq-trans (dtup-nth (suc a) (ptD I LN) I lI) (ptD-I I LN)

  getA-ne : (c : Nat) -> LeN (suc c) (suc a) -> Not (Eq c I)
          -> Eq (get c A) (bot (LN c))
  getA-ne c lc nc =
    Eq-trans (dtup-nth (suc a) (ptD I LN) c lc) (ptD-ne I LN c nc)

  -- only `I` is infinite
  getA-inf : (c : Nat) -> Eq (get c A) inf -> Eq c I
  getA-inf c e = route (LeN-dec (suc c) (suc a))
    where
      route : Dec (LeN (suc c) (suc a)) -> Eq c I
      route (no nc) =
        Empty-elim
          (bot-not-inf zero
            (Eq-trans (Eq-sym (dtup-out (suc a) (ptD I LN) c nc)) e))
      route (yes lc) = route2 (EqNat-dec c I)
        where
          route2 : Dec (Eq c I) -> Eq c I
          route2 (yes ec) = ec
          route2 (no  nc) =
            Empty-elim
              (bot-not-inf (LN c)
                (Eq-trans (Eq-sym (getA-ne c lc nc)) e))

  --------------------------------------------------------------------
  -- what a finite approximant `A0 <= A` looks like
  --------------------------------------------------------------------

  module Approx (A0 : FTup) (bel : LeTup (embedTup A0) A) where

    A0len : Eq (length A0) (suc a)
    A0len =
      Eq-trans (Eq-sym (embedTup-len A0))
        (Eq-trans (LeTup-len (embedTup A0) A bel) Alen)

    A0at : (c : Nat) -> LeD (embed (getF c A0)) (get c A)
    A0at c =
      Eq-transport (\ z -> LeD z (get c A)) (get-embedTup c A0)
        (LeTup-get c {embedTup A0} {A} bel)

    -- the height `A0` asks for at the infinite coordinate
    k0 : Nat
    k0 = hgt (getF I A0)

    A0-I : Eq (getF I A0) (fbot k0)
    A0-I =
      below-inf (getF I A0)
        (Eq-transport (\ z -> LeD (embed (getF I A0)) z) getA-I (A0at I))

    A0-ne : (c : Nat) -> LeN (suc c) (suc a) -> Not (Eq c I)
          -> LeN (hgt (getF c A0)) (LN c)
    A0-ne c lc nc =
      below-bot-le (getF c A0) (LN c)
        (Eq-transport (\ z -> LeD (embed (getF c A0)) z)
          (getA-ne c lc nc) (A0at c))

    A0-ne-shape : (c : Nat) -> LeN (suc c) (suc a) -> Not (Eq c I)
                -> Eq (getF c A0) (fbot (hgt (getF c A0)))
    A0-ne-shape c lc nc =
      below-bot (getF c A0) (LN c)
        (Eq-transport (\ z -> LeD (embed (getF c A0)) z)
          (getA-ne c lc nc) (A0at c))

    -- ... so `A0` is below every member of the family, from `k0` on
    leX : (t : Nat) -> LeN k0 t -> LeX A0 (XT t)
    leX t lt c = route (LeN-dec (suc c) (suc a))
      where
        route : Dec (LeN (suc c) (suc a))
              -> LeF (getF c A0) (getF c (XT t))
        route (no nc) =
          Eq-transport (\ z -> LeF z (getF c (XT t)))
            (Eq-sym
              (nth-out (fbot zero) c A0
                (\ l -> nc (Eq-transport (\ z -> LeN (suc c) z) A0len l))))
            (Eq-transport (\ z -> LeF (fbot zero) z)
              (Eq-sym (XT-out t c nc)) tt)
        route (yes lc) = route2 (EqNat-dec c I)
          where
            atI : LeF (fbot k0) (fbot (plus t (LN I)))
            atI = LeN-trans {k0} {t} {plus t (LN I)} lt (plus-ge-l t (LN I))

            route2 : Dec (Eq c I) -> LeF (getF c A0) (getF c (XT t))
            route2 (yes ec) =
              Eq-transport
                (\ z -> LeF (getF z A0) (getF z (XT t))) (Eq-sym ec)
                (Eq-transport (\ z -> LeF z (getF I (XT t))) (Eq-sym A0-I)
                  (Eq-transport (\ z -> LeF (fbot k0) z) (Eq-sym (XT-I t))
                    atI))
            route2 (no nc) =
              Eq-transport (\ z -> LeF z (getF c (XT t)))
                (Eq-sym (A0-ne-shape c lc nc))
                (Eq-transport (\ z -> LeF (fbot (hgt (getF c A0))) z)
                  (Eq-sym (XT-ne t c lc nc)) (A0-ne c lc nc))

    lenXA : (t : Nat) -> Eq (length (XT t)) (length A0)
    lenXA t = Eq-trans (XTlen t) (Eq-sym A0len)

    leF : (t : Nat) -> LeN k0 t -> LeFTup A0 (XT t)
    leF t lt =
      LeX-LeFTup A0 (XT t) (Eq-sym (lenXA t)) (leX t lt)

    -- and below it after deleting a coordinate
    leF-del : (i : Nat) -> LeN (suc i) (suc a) -> (t : Nat) -> LeN k0 t
            -> LeFTup (del i A0) (del i (XT t))
    leF-del i li t lt =
      LeX-LeFTup (del i A0) (del i (XT t)) dlen
        (LeX-del i A0 (XT t) (leX t lt))
      where
        dlen : Eq (length (del i A0)) (length (del i (XT t)))
        dlen =
          suc-inj
            (Eq-trans
              (del-len i A0
                (Eq-transport (\ z -> LeN (suc i) z) (Eq-sym A0len) li))
              (Eq-trans A0len
                (Eq-trans (Eq-sym (XTlen t))
                  (Eq-sym
                    (del-len i (XT t)
                      (Eq-transport (\ z -> LeN (suc i) z)
                        (Eq-sym (XTlen t)) li))))))

  --------------------------------------------------------------------
  -- reading off the verdict
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- incompleteness at arbitrarily large depths IS incompleteness
  --------------------------------------------------------------------

  notCpl-down : (n n' : Nat) -> LeN n n' -> Not (IsCpl (ov n')) -> Not (IsCpl (ov n))
  notCpl-down n n' le nc ic =
    nc (Eq-transport (\ z -> IsCpl z) (cpl-max (ov n) (ov n') (mono n n' le) ic) ic)

  never-of : (t0 : Nat) -> ((t : Nat) -> LeN t0 t -> Not (IsCpl (ov (plus t N))))
           -> Never ov
  never-of t0 h n =
    notCpl-shape (ov n)
      (notCpl-down n (plus (plus t0 n) N) big (h (plus t0 n) (plus-ge-l t0 n)))
    where
      big : LeN n (plus (plus t0 n) N)
      big =
        LeN-trans {n} {plus t0 n} {plus (plus t0 n) N}
          (plus-ge-r t0 n) (plus-ge-l (plus t0 n) N)

  hov : Nat -> Nat
  hov n = hgt (ov n)

  -- `hov` past the threshold, as a sequence in `t`
  hovT : Nat -> Nat
  hovT t = hov (plus t N)

  phiok-lift : PhiOK hovT -> PhiOK hov
  phiok-lift = phiok-reindex hov hovT N (\ t -> refl)

  verdict : UO F A -> Verdict ov
  ------------------------------------------------------------------
  -- UO Case 1: eventually a numeral
  ------------------------------------------------------------------
  verdict (uo1 (mkSigma A0 (mkSigma bel (mkSigma m hyp)))) =
    inl (mkSigma (plus AP.k0 N) isc)
    where
      module AP = Approx A0 bel

      hit : Eq (ov (plus AP.k0 N)) (fcpl m)
      hit =
        Eq-trans (ovX AP.k0)
          (hyp (XT AP.k0) (AP.leF AP.k0 (LeN-refl AP.k0)))

      isc : IsCpl (ov (plus AP.k0 N))
      isc = Eq-transport (\ z -> IsCpl z) (Eq-sym hit) tt
  ------------------------------------------------------------------
  -- UO Case 2: pinned at a FINITE incomplete coordinate, so not `I`
  ------------------------------------------------------------------
  verdict (uo2 (mkSigma A0 (mkSigma bel
            (mkSigma m (mkSigma i (mkSigma li (mkSigma incf
              (mkSigma eqA hyp)))))))) =
    inr (mkSigma
          (never-of AP.k0 (\ t lt -> fbot-notCpl (ov (plus t N)) m (hit t lt)))
          (phiok-lift (phiok-cong-from (\ _ -> m) hovT AP.k0 agree
                        (mkSigma zero (inl (\ z lz -> refl))))))
    where
      module AP = Approx A0 bel

      li' : LeN (suc i) (suc a)
      li' = Eq-transport (\ z -> LeN (suc i) z) AP.A0len li

      ni : Not (Eq i I)
      ni ei =
        Eq-transport (\ z -> IncompleteFinite z)
          (Eq-trans (Eq-cong (\ z -> get z A) ei) getA-I) incf

      A0i : Eq (getF i A0) (fbot (LN i))
      A0i =
        embed-bot (getF i A0) (LN i)
          (Eq-trans eqA (getA-ne i li' ni))

      same : (t : Nat) -> Eq (getF i (XT t)) (getF i A0)
      same t = Eq-trans (XT-ne t i li' ni) (Eq-sym A0i)

      hit : (t : Nat) -> LeN AP.k0 t -> Eq (ov (plus t N)) (fbot m)
      hit t lt =
        Eq-trans (ovX t)
          (hyp (XT t) (AP.lenXA t) (same t) (AP.leF-del i li' t lt))

      agree : (t : Nat) -> LeN AP.k0 t -> Eq m (hovT t)
      agree t lt = Eq-sym (Eq-cong hgt (hit t lt))
  ------------------------------------------------------------------
  -- UO Case 3: at the infinite coordinate, which must be `I`
  ------------------------------------------------------------------
  verdict (uo3 (mkSigma A0 (mkSigma bel
            (mkSigma i (mkSigma einf (mkSigma k (mkSigma eA0
              (mkSigma phi (mkSigma pk hyp))))))))) =
    inr (mkSigma
          (never-of AP.k0
            (\ t lt ->
               fbot-notCpl (ov (plus t N)) (phi (plus t (LN I))) (hit t lt)))
          (phiok-lift
            (phiok-cong-from (\ t -> phi (plus t (LN I))) hovT AP.k0 agree
              (phiok-shift-r phi (mkSigma k pk) (LN I)))))
    where
      module AP = Approx A0 bel

      ei : Eq i I
      ei = getA-inf i einf

      li' : LeN (suc i) (suc a)
      li' = Eq-transport (\ z -> LeN (suc z) (suc a)) (Eq-sym ei) lI

      -- the threshold `UO` returns IS the height `A0` has at `I`
      kk : Eq k AP.k0
      kk =
        Eq-cong hgt
          (Eq-trans (Eq-sym eA0)
            (Eq-trans (Eq-cong (\ z -> getF z A0) ei) AP.A0-I))

      atI : (t : Nat) -> Eq (getF i (XT t)) (fbot (plus t (LN I)))
      atI t =
        Eq-transport (\ z -> Eq (getF z (XT t)) (fbot (plus t (LN I))))
          (Eq-sym ei) (XT-I t)

      ge-k : (t : Nat) -> LeN AP.k0 t -> LeN k (plus t (LN I))
      ge-k t lt =
        Eq-transport (\ z -> LeN z (plus t (LN I))) (Eq-sym kk)
          (LeN-trans {AP.k0} {t} {plus t (LN I)} lt (plus-ge-l t (LN I)))

      hit : (t : Nat) -> LeN AP.k0 t
          -> Eq (ov (plus t N)) (fbot (phi (plus t (LN I))))
      hit t lt =
        Eq-trans (ovX t)
          (hyp (XT t) (plus t (LN I)) (AP.lenXA t) (ge-k t lt) (atI t)
            (AP.leF-del i li' t lt))

      agree : (t : Nat) -> LeN AP.k0 t -> Eq (phi (plus t (LN I))) (hovT t)
      agree t lt = Eq-sym (Eq-cong hgt (hit t lt))

------------------------------------------------------------------------
-- MIN1.PDF'S THREE CASES, FROM PROPOSITION 1 AND THE INDEX CLAUSE
------------------------------------------------------------------------

verdict-of : (a : Nat) (iv : Nat -> Nat)
             (ivr : (n : Nat) -> LeN (suc (iv n)) (suc a))
             (ov : Nat -> FEl)
             (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
             (F : FTup -> FEl)
           -> Den (suc a) (node iv ivr ov cont) F
           -> MonoTr (suc a) (node iv ivr ov cont)
           -> ((A : Tup) -> Eq (length A) (suc a) -> UO F A)
           -> EvConstN iv
           -> Verdict ov
verdict-of a iv ivr ov cont F dn mt uo (mkSigma N stab) =
  V.verdict a iv ivr ov cont F dn (fst mt) N stab
    (uo (V.A a iv ivr ov cont F dn (fst mt) N stab)
        (V.Alen a iv ivr ov cont F dn (fst mt) N stab))
