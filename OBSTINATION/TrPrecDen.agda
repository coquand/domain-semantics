{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecDen
--
-- CORRECTNESS OF THE RECURSION TRACE:
--
--     precTr-den  : Den p Tg g -> Den (2+p) Th h
--                 -> Den (suc p) (precTr p Tg Th) (precFun g h)
--     precTr-mono : ... -> MonoTr (suc p) (precTr p Tg Th)
--
-- The three branches of `sem` go as in `TrCompDen.compTr-den`: an already
-- TOTAL value is maximal, a FROZEN coordinate is the continuation plus
-- `ins-del`, and BLOCKED is the theorem.
--
-- The blocked branch is `prec-sat`, and it is NOT an instance of
-- `TrSat.sem-sat`.  `sem-sat` compares `sem` with `sem`; what is wanted
-- here is a statement about the FUNCTION the trace is supposed to denote,
-- and applying `sem-sat` to `precTr` itself gives a tautology.  So it is
-- proved directly, by induction on the RECURSION DEPTH, with `sem-sat`
-- used at the STEP term only, splitting on `blockOn Th (avT L j)` through
-- `qsel`.  Only the "blocked on the recursive value" case uses the
-- induction hypothesis; the other three are monotonicity.
--
-- `Vd-den` is the bridge: the chain `Vd L 0 , Vd L 1 , ...` IS
-- `f(bot,Y) , f(S bot,Y) , ...` with the parameters frozen at the levels
-- `L`, and at `j = L 0` its tuple is `botTup (suc p) L` definitionally.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecDen where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using
  (bump-ne ; lv ; nOf ; levels-below ; nOf-below-adv)
open import OBSTINATION.WalkAffine using (stuck-level)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrDen
open import OBSTINATION.TrWalk
open import OBSTINATION.TrComp using (compTr)
open import OBSTINATION.TrCompDen using
  (compTr-den ; monoTr-cont ; leF-bot ; LeX-ins)
open import OBSTINATION.TrPrec using
  (module R ; module P ; module N ; qsel ; argPr ; precTr ; precCont)
open import OBSTINATION.TrPrecFun
open import OBSTINATION.TrMono using (compTr-mono ; projTr-mono ; lev-mono)
open import OBSTINATION.TrPrecFrz using (tup-le)

------------------------------------------------------------------------
-- THE TUPLE THE RECURSION SEES AT DEPTH `j`
--
-- Coordinate 0 is the recursion argument, at depth `j`; the parameters
-- are at the levels `L` has obtained for them.  This is exactly
-- `botTup (suc p) L` when `j` is `L 0`, which is how the main walk uses
-- it.
------------------------------------------------------------------------

parTup : Nat -> (Nat -> Nat) -> FTup
parTup p L = tup p (\ i -> fbot (L (suc i)))

avP : Nat -> (Nat -> Nat) -> Nat -> FTup
avP p L j = cons (fbot j) (parTup p L)

avP-len : (p : Nat) (L : Nat -> Nat) (j : Nat) -> Eq (length (avP p L j)) (suc p)
avP-len p L j = Eq-cong suc (tup-len p (\ i -> fbot (L (suc i))))

------------------------------------------------------------------------
-- `Vd` IS THE RECURSION, AT AN INCOMPLETE FIRST ARGUMENT
--
-- The chain `Vd L 0 , Vd L 1 , ...` is precisely
-- `f (bot,Y) , f (S bot,Y) , ...` for the parameters `Y` frozen at the
-- levels `L`.  Only the step term appears: the base `g` is out of reach
-- of an incomplete recursion argument.
------------------------------------------------------------------------

Vd-den : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
       -> Den (suc (suc p)) Th h
       -> (L : Nat -> Nat) (j : Nat)
       -> Eq (R.Vd p Th L j) (precFun g h (avP p L j))
Vd-den p Th g h dh L zero    = refl
Vd-den p Th g h dh L (suc j) =
  Eq-trans
    (den-sem (suc (suc p)) Th h dh (R.avT p Th L j)
      (tup-len (suc (suc p)) (R.avf p Th L j)))
    (Eq-cong (\ z -> h (cons (fbot j) (cons z (parTup p L))))
      (Vd-den p Th g h dh L j))

------------------------------------------------------------------------
-- SATURATION FOR THE RECURSION ITSELF
--
-- If at depth `j` the recursion is blocked on coordinate `Qd L j`, then
-- raising every OTHER coordinate does not move its value.  This is
-- `TrSat.sem-sat` for the trace `precTr` -- but it cannot be obtained
-- FROM `sem-sat`, because `sem-sat` compares `sem` with `sem`, and what
-- is wanted is a statement about the FUNCTION the trace is supposed to
-- denote.  So it is proved directly, by induction on the recursion depth,
-- with `sem-sat` used at the STEP term only.
--
-- The four cases are the four values of `blockOn` on the step term, read
-- through `qsel`: nothing (`inl tt`) and the recursion argument
-- (`inr 0`) both make `f` demand its own coordinate 0; the recursive
-- value (`inr 1`) makes the walk DESCEND, and is the only case that uses
-- the induction hypothesis; a parameter (`inr (2+i)`) is passed straight
-- through.
------------------------------------------------------------------------

prec-sat : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
         -> Den (suc (suc p)) Th h -> MonoTr (suc (suc p)) Th
         -> MonoF p g -> MonoF (suc (suc p)) h
         -> (L : Nat -> Nat) (j : Nat) (X : FTup)
         -> Eq (length X) (suc p)
         -> LeX (avP p L j) X
         -> Agr (inr (R.Qd p Th L j)) (avP p L j) X
         -> Eq (R.Vd p Th L j) (precFun g h X)
prec-sat p Th g h dh mth mg mh L zero    nil        () lex agr
prec-sat p Th g h dh mth mg mh L (suc j) nil        () lex agr
prec-sat p Th g h dh mth mg mh L zero    (cons x Y) lx lex agr =
  Eq-cong (\ z -> precA g h z Y) agr
prec-sat p Th g h dh mth mg mh L (suc j) (cons x Y) lx lex agr =
  Eq-trans
    (den-sem (suc (suc p)) Th h dh (R.avT p Th L j)
      (tup-len (suc (suc p)) (R.avf p Th L j)))
    (Eq-trans hsat (Eq-sym (precA-unf g h j x Y lx0)))
  where
    lx0 : LeF (fbot (suc j)) x
    lx0 = lex zero

    ltl : LeX (parTup p L) Y
    ltl = LeX-tail (fbot (suc j)) x (parTup p L) Y lex

    x2 : FEl
    x2 = pre x

    X2 : FTup
    X2 = cons x2 Y

    lexIH : LeX (avP p L j) X2
    lexIH = LeX-cons (fbot j) x2 (parTup p L) Y (pre-le j x lx0) ltl

    -- the recursive value can only have grown
    VdLe : LeF (R.Vd p Th L j) (precA g h x2 Y)
    VdLe =
      Eq-transport (\ z -> LeF z (precA g h x2 Y))
        (Eq-sym (Vd-den p Th g h dh L j))
        (precFun-mono p g h mg mh (avP p L j) X2 (avP-len p L j) lx lexIH)

    Z : FTup
    Z = cons x2 (cons (precA g h x2 Y) Y)

    Zlen : Eq (length Z) (suc (suc p))
    Zlen = Eq-cong suc lx

    leZ : LeX (R.avT p Th L j) Z
    leZ =
      LeX-cons (fbot j) x2 (cons (R.Vd p Th L j) (parTup p L))
        (cons (precA g h x2 Y) Y) (pre-le j x lx0)
        (LeX-cons (R.Vd p Th L j) (precA g h x2 Y) (parTup p L) Y VdLe ltl)

    ------------------------------------------------------------------
    -- the step term is blocked on the same thing at the bigger tuple
    ------------------------------------------------------------------

    agrZ : Agr (blockOn (suc (suc p)) Th (R.avT p Th L j)) (R.avT p Th L j) Z
    agrZ = ago (blockOn (suc (suc p)) Th (R.avT p Th L j)) refl
      where
        ago : (r : Or Top Nat)
            -> Eq (blockOn (suc (suc p)) Th (R.avT p Th L j)) r
            -> Agr r (R.avT p Th L j) Z
        ago (inl tt)                er = tt
        ago (inr zero)              er =
          Eq-cong pre
            (Eq-transport (\ z -> Agr (inr z) (avP p L (suc j)) (cons x Y))
              (Eq-cong (qsel (R.Qd p Th L j)) er) agr)
        ago (inr (suc (suc i)))     er =
          Eq-transport (\ z -> Agr (inr z) (avP p L (suc j)) (cons x Y))
            (Eq-cong (qsel (R.Qd p Th L j)) er) agr
        ago (inr (suc zero))        er =
          prec-sat p Th g h dh mth mg mh L j X2 lx lexIH agrIH
          where
            agrD : Agr (inr (R.Qd p Th L j)) (avP p L (suc j)) (cons x Y)
            agrD =
              Eq-transport (\ z -> Agr (inr z) (avP p L (suc j)) (cons x Y))
                (Eq-cong (qsel (R.Qd p Th L j)) er) agr

            down : (q : Nat) -> Eq (R.Qd p Th L j) q
                 -> Agr (inr q) (avP p L j) X2
            down zero    eq =
              Eq-cong pre
                (Eq-transport (\ z -> Agr (inr z) (avP p L (suc j)) (cons x Y))
                  eq agrD)
            down (suc c) eq =
              Eq-transport (\ z -> Agr (inr z) (avP p L (suc j)) (cons x Y))
                eq agrD

            agrIH : Agr (inr (R.Qd p Th L j)) (avP p L j) X2
            agrIH = down (R.Qd p Th L j) refl

    hsat : Eq (h (R.avT p Th L j)) (h Z)
    hsat =
      Eq-trans
        (Eq-sym
          (den-sem (suc (suc p)) Th h dh (R.avT p Th L j)
            (tup-len (suc (suc p)) (R.avf p Th L j))))
        (Eq-trans
          (sem-sat (suc (suc p)) Th mth (R.avT p Th L j) Z leZ agrZ)
          (den-sem (suc (suc p)) Th h dh Z Zlen))

------------------------------------------------------------------------
-- A TOTAL RECURSION ARGUMENT: THE BASE TERM AT LAST
--
-- Freezing coordinate 0 to the numeral `v` is "the recursion argument is
-- total", and there `f` unfolds all the way down to `g`:
--
--     f (0       , Y) = g (Y)
--     f (S^(v+1) 0 , Y) = h ( S^v(0) , f (S^v 0 , Y) , Y )
--
-- so `N.atNum v` is a tower of `v` compositions on top of `Tg`, and its
-- correctness is `compTr-den` applied `v` times.
------------------------------------------------------------------------

tup-eta : (Y : FTup) -> Eq (tup (length Y) (\ i -> nth (fbot zero) i Y)) Y
tup-eta nil         = refl
tup-eta (cons y ys) = Eq-cong (cons y) (tup-eta ys)

tup-eta-len : (n : Nat) (Y : FTup) -> Eq (length Y) n
            -> Eq (tup n (\ i -> nth (fbot zero) i Y)) Y
tup-eta-len n Y ly =
  Eq-transport (\ z -> Eq (tup z (\ i -> nth (fbot zero) i Y)) Y) ly (tup-eta Y)

------------------------------------------------------------------------
-- `MonoTr` for the tower
------------------------------------------------------------------------

argPr-mono : (p i : Nat) -> MonoTr p (argPr p i (LeN-dec (suc i) p))
argPr-mono p i = go (LeN-dec (suc i) p) refl
  where
    go : (D : Dec (LeN (suc i) p)) -> Eq (LeN-dec (suc i) p) D
       -> MonoTr p (argPr p i (LeN-dec (suc i) p))
    go (yes li) eD =
      Eq-transport (\ T -> MonoTr p T) (Eq-sym (Eq-cong (argPr p i) eD))
        (projTr-mono p i li)
    go (no  ni) eD =
      Eq-transport (\ T -> MonoTr p T) (Eq-sym (Eq-cong (argPr p i) eD)) tt

argPr-den : (p i : Nat)
          -> Den p (argPr p i (LeN-dec (suc i) p)) (\ Y -> nth (fbot zero) i Y)
argPr-den p i = go (LeN-dec (suc i) p) refl
  where
    go : (D : Dec (LeN (suc i) p)) -> Eq (LeN-dec (suc i) p) D
       -> Den p (argPr p i (LeN-dec (suc i) p)) (\ Y -> nth (fbot zero) i Y)
    go (yes li) eD =
      Eq-transport (\ T -> Den p T (\ Y -> nth (fbot zero) i Y))
        (Eq-sym (Eq-cong (argPr p i) eD)) (projTr-den p i li)
    go (no  ni) eD =
      Eq-transport (\ T -> Den p T (\ Y -> nth (fbot zero) i Y))
        (Eq-sym (Eq-cong (argPr p i) eD))
        (\ Y ly ->
           Eq-sym
             (nth-out (fbot zero) i Y
               (\ l -> ni (Eq-transport (\ z -> LeN (suc i) z) ly l))))

atNum-mono : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) (h : FTup -> FEl)
           -> Den (suc (suc p)) Th h -> MonoF (suc (suc p)) h -> MonoTr p Tg
           -> (v : Nat) -> MonoTr p (N.atNum p Tg Th v)
atNum-mono p Tg Th h dh mh mtg zero    = mtg
atNum-mono p Tg Th h dh mh mtg (suc v) =
  compTr-mono (suc (suc p)) Th h dh mh p (N.argsA p Tg Th v) am
  where
    am : (i : Nat) -> MonoTr p (N.argsA p Tg Th v i)
    am zero          = tt
    am (suc zero)    = atNum-mono p Tg Th h dh mh mtg v
    am (suc (suc i)) = argPr-mono p i

------------------------------------------------------------------------
-- ... and its correctness
------------------------------------------------------------------------

atNum-den : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
          -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
          -> MonoF p g -> MonoF (suc (suc p)) h
          -> Den p Tg g -> Den (suc (suc p)) Th h
          -> (v : Nat) -> Den p (N.atNum p Tg Th v) (\ Y -> precA g h (fcpl v) Y)
atNum-den p Tg Th g h mtg mth mg mh dg dh zero    = dg
atNum-den p Tg Th g h mtg mth mg mh dg dh (suc v) =
  Den-extL p (N.atNum p Tg Th (suc v))
    (\ Y -> h (tup (suc (suc p)) (\ i -> hh i Y)))
    (\ Y -> precA g h (fcpl (suc v)) Y)
    ext
    (compTr-den (suc (suc p)) Th h mth dh p (N.argsA p Tg Th v) hh
      am hm dm)
  where
    hh : Nat -> FTup -> FEl
    hh zero          Y = fcpl v
    hh (suc zero)    Y = precA g h (fcpl v) Y
    hh (suc (suc i)) Y = nth (fbot zero) i Y

    am : (i : Nat) -> MonoTr p (N.argsA p Tg Th v i)
    am zero          = tt
    am (suc zero)    = atNum-mono p Tg Th h dh mh mtg v
    am (suc (suc i)) = argPr-mono p i

    hm : (i : Nat) -> MonoF p (hh i)
    hm zero          = \ A B la lb l -> LeF-refl (fcpl v)
    hm (suc zero)    =
      \ A B la lb l ->
        precA-mono p g h mg mh (fcpl v) (fcpl v) (LeF-refl (fcpl v)) A B la lb l
    hm (suc (suc i)) = \ A B la lb l -> l i

    dm : (i : Nat) -> Den p (N.argsA p Tg Th v i) (hh i)
    dm zero          = \ A la -> refl
    dm (suc zero)    = atNum-den p Tg Th g h mtg mth mg mh dg dh v
    dm (suc (suc i)) = argPr-den p i

    ext : (Y : FTup) -> Eq (length Y) p
        -> Eq (h (tup (suc (suc p)) (\ i -> hh i Y)))
              (precA g h (fcpl (suc v)) Y)
    ext Y ly =
      Eq-cong (\ Z -> h (cons (fcpl v) (cons (precA g h (fcpl v) Y) Z)))
        (tup-eta-len p Y ly)

------------------------------------------------------------------------
-- `MonoTr` FOR THE RECURSION TRACE
--
-- `ovP k` is the recursion at the levels obtained after `k` steps, so its
-- monotonicity is `precFun-mono` composed with "the levels never go down"
-- (`lev-mono`).  The continuations are the tower `N.atNum` at coordinate
-- 0, and the recursion of the frozen sub-traces at a parameter.
------------------------------------------------------------------------

precTr-ovm : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
           -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
           -> (m n : Nat) -> LeN m n -> LeF (P.ovP p Th m) (P.ovP p Th n)
precTr-ovm p Th g h dh mg mh m n le =
  Eq-transport (\ z -> LeF z (P.ovP p Th n)) (Eq-sym (vd m))
    (Eq-transport (\ z -> LeF (precFun g h (bt m)) z) (Eq-sym (vd n))
      (precFun-mono p g h mg mh (bt m) (bt n) (btlen m) (btlen n) leb))
  where
    module PP = P p Th

    bt : Nat -> FTup
    bt k = botTup (suc p) (PP.Lv k)

    btlen : (k : Nat) -> Eq (length (bt k)) (suc p)
    btlen k = tup-len (suc p) (\ c -> fbot (PP.Lv k c))

    vd : (k : Nat) -> Eq (PP.ovP k) (precFun g h (bt k))
    vd k = Vd-den p Th g h dh (PP.Lv k) (PP.Lv k zero)

    leb : LeX (bt m) (bt n)
    leb =
      tup-le (suc p) (\ c -> fbot (PP.Lv m c)) (\ c -> fbot (PP.Lv n c))
        (\ c lc -> lev-mono PP.ivP PP.Lv (\ _ _ -> refl) m n le c)

precTr-mono : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
            -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
            -> MonoF p g -> MonoF (suc (suc p)) h
            -> Den p Tg g -> Den (suc (suc p)) Th h
            -> MonoTr (suc p) (precTr p Tg Th)
precTr-mono zero    Tg Th g h mtg mth mg mh dg dh =
  mkSigma (precTr-ovm zero Th g h dh mg mh) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc zero)) (v : Nat)
        -> MonoTr zero (precCont zero Tg Th c lc v)
    cns zero    lc v = atNum-mono zero Tg Th h dh mh mtg v
    cns (suc i) ()  v
precTr-mono (suc p) Tg Th g h mtg mth mg mh dg dh =
  mkSigma (precTr-ovm (suc p) Th g h dh mg mh) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc (suc p))) (v : Nat)
        -> MonoTr (suc p) (precCont (suc p) Tg Th c lc v)
    cns zero    lc v = atNum-mono (suc p) Tg Th h dh mh mtg v
    cns (suc i) lc v =
      precTr-mono p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
        (\ Y -> g (ins i (fcpl v) Y))
        (\ Z -> h (ins (suc (suc i)) (fcpl v) Z))
        (monoTr-cont p Tg mtg i lc v)
        (monoTr-cont (suc (suc p)) Th mth (suc (suc i)) lc v)
        (\ A B la lb l -> mg (ins i (fcpl v) A) (ins i (fcpl v) B)
                             (insG A la) (insG B lb)
                             (LeX-ins i (fcpl v) A B l))
        (\ A B la lb l -> mh (ins (suc (suc i)) (fcpl v) A)
                             (ins (suc (suc i)) (fcpl v) B)
                             (insH A la) (insH B lb)
                             (LeX-ins (suc (suc i)) (fcpl v) A B l))
        (den-cont p Tg g dg i lc v)
        (den-cont (suc (suc p)) Th h dh (suc (suc i)) lc v)
      where
        insG : (A : FTup) -> Eq (length A) p
             -> Eq (length (ins i (fcpl v) A)) (suc p)
        insG A la =
          Eq-trans
            (ins-len i (fcpl v) A
              (Eq-transport (\ z -> LeN i z) (Eq-sym la) lc))
            (Eq-cong suc la)

        insH : (A : FTup) -> Eq (length A) (suc (suc p))
             -> Eq (length (ins (suc (suc i)) (fcpl v) A)) (suc (suc (suc p)))
        insH A la =
          Eq-trans
            (ins-len (suc (suc i)) (fcpl v) A
              (Eq-transport (\ z -> LeN (suc (suc i)) z) (Eq-sym la) lc))
            (Eq-cong suc la)

------------------------------------------------------------------------
-- THE MAIN WALK OF `precTr` DENOTES THE RECURSION
--
-- The three branches of `sem`, exactly as in `TrCompDen.compTr-den`:
--
--   * `ovP K` already TOTAL -- a total value is maximal, and the recursion
--     at the levels obtained so far is below the recursion at `X`;
--   * BLOCKED -- `prec-sat`, with the agreement supplied by `stuck-level`:
--     the walk sticks exactly at the level available at `cK`;
--   * FROZEN -- the continuation, and `ins-del` puts the numeral back.
--
-- The continuations are a HYPOTHESIS here: they are what the induction on
-- the arity in `precTr-den` supplies.
------------------------------------------------------------------------

precTr-main : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
            -> MonoTr (suc (suc p)) Th -> MonoF p g -> MonoF (suc (suc p)) h
            -> Den (suc (suc p)) Th h
            -> ((c : Nat) (lc : LeN (suc c) (suc p)) (v : Nat)
                -> Den p (precCont p Tg Th c lc v)
                       (\ Y -> precFun g h (ins c (fcpl v) Y)))
            -> (X : FTup) -> Eq (length X) (suc p)
            -> Eq (sem (suc p) (precTr p Tg Th) X) (precFun g h X)
precTr-main p Tg Th g h mth mg mh dh dcn X lx = go (PP.ovP K) refl
  where
    module PP = P p Th

    K : Nat
    K = nOf (suc p) PP.ivP PP.ivPr (hts X)

    LK : Nat -> Nat
    LK = PP.Lv K

    cK : Nat
    cK = PP.ivP K

    ALT : FEl
    ALT = sem p (precCont p Tg Th cK (PP.ivPr K) (hts X cK)) (del cK X)

    BL : FEl
    BL = brf (PP.ovP K) ALT (nth (fbot zero) cK X)

    lvL : (c : Nat) -> Eq (lv (suc p) PP.ivP PP.ivPr c K) (LK c)
    lvL c = lv-L (suc p) PP.ivP PP.ivPr PP.Lv (\ _ -> refl) (\ _ _ -> refl) K c

    belowX : (c : Nat) -> LeN (LK c) (hts X c)
    belowX c =
      Eq-transport (\ z -> LeN z (hts X c)) (lvL c)
        (levels-below (suc p) PP.ivP PP.ivPr (hts X) K
          (nOf-below-adv (suc p) PP.ivP PP.ivPr (hts X)) c)

    stuckX : Eq (LK cK) (hts X cK)
    stuckX =
      Eq-transport (\ z -> Eq z (hts X cK)) (lvL cK)
        (stuck-level (suc p) PP.ivP PP.ivPr (hts X))

    BT : FTup
    BT = botTup (suc p) LK

    BTlen : Eq (length BT) (suc p)
    BTlen = tup-len (suc p) (\ c -> fbot (LK c))

    leBot : LeX BT X
    leBot c = route (LeN-dec (suc c) (suc p))
      where
        route : Dec (LeN (suc c) (suc p))
              -> LeF (nth (fbot zero) c BT) (nth (fbot zero) c X)
        route (yes lc) =
          Eq-transport (\ z -> LeF z (nth (fbot zero) c X))
            (Eq-sym (nth-botTup (suc p) LK c lc))
            (leF-bot (LK c) (nth (fbot zero) c X) (belowX c))
        route (no nc) =
          Eq-transport (\ z -> LeF z (nth (fbot zero) c X))
            (Eq-sym (tup-out (suc p) (\ d -> fbot (LK d)) c nc))
            (leF-bot zero (nth (fbot zero) c X) tt)

    ovEq : Eq (PP.ovP K) (precFun g h BT)
    ovEq = Vd-den p Th g h dh LK (LK zero)

    go : (y : FEl) -> Eq (PP.ovP K) y
       -> Eq (sem (suc p) (precTr p Tg Th) X) (precFun g h X)
    ------------------------------------------------------------------
    -- the recursion has already produced a total value
    ------------------------------------------------------------------
    go (fcpl w) e = Eq-trans semTot totEq
      where
        semTot : Eq (sem (suc p) (precTr p Tg Th) X) (PP.ovP K)
        semTot = Eq-trans (Eq-cong (\ z -> hlt z BL) e) (Eq-sym e)

        totEq : Eq (PP.ovP K) (precFun g h X)
        totEq =
          Eq-trans ovEq
            (cpl-max (precFun g h BT) (precFun g h X)
              (precFun-mono p g h mg mh BT X BTlen lx leBot)
              (Eq-transport (\ z -> IsCpl z) ovEq
                (Eq-transport (\ z -> IsCpl z) (Eq-sym e) tt)))
    go (fbot w) e = br (nth (fbot zero) cK X) refl
      where
        br : (y : FEl) -> Eq (nth (fbot zero) cK X) y
           -> Eq (sem (suc p) (precTr p Tg Th) X) (precFun g h X)
        ----------------------------------------------------------------
        -- BLOCKED on `cK`, and `X` has not grown there
        ----------------------------------------------------------------
        br (fbot jj) ey = Eq-trans semBlk blkEq
          where
            semBlk : Eq (sem (suc p) (precTr p Tg Th) X) (PP.ovP K)
            semBlk =
              Eq-trans
                (Eq-cong (\ z -> hlt (PP.ovP K) (brf (PP.ovP K) ALT z)) ey)
                (Eq-cong (\ z -> hlt z (PP.ovP K)) e)

            atK : Eq (nth (fbot zero) cK BT) (nth (fbot zero) cK X)
            atK =
              Eq-trans (nth-botTup (suc p) LK cK (PP.ivPr K))
                (Eq-trans (Eq-cong fbot (Eq-trans stuckX (Eq-cong hgt ey)))
                  (Eq-sym ey))

            blkEq : Eq (PP.ovP K) (precFun g h X)
            blkEq = prec-sat p Th g h dh mth mg mh LK (LK zero) X lx leBot atK
        ----------------------------------------------------------------
        -- FROZEN: coordinate `cK` turned out to be a numeral
        ----------------------------------------------------------------
        br (fcpl v) ey = Eq-trans semFrz (Eq-trans contD insD)
          where
            semFrz : Eq (sem (suc p) (precTr p Tg Th) X) ALT
            semFrz =
              Eq-trans
                (Eq-cong (\ z -> hlt (PP.ovP K) (brf (PP.ovP K) ALT z)) ey)
                (Eq-cong (\ z -> hlt z ALT) e)

            lenCK : LeN (suc cK) (length X)
            lenCK = Eq-transport (\ z -> LeN (suc cK) z) (Eq-sym lx) (PP.ivPr K)

            contD : Eq ALT (precFun g h (ins cK (fcpl (hts X cK)) (del cK X)))
            contD =
              den-sem p (precCont p Tg Th cK (PP.ivPr K) (hts X cK))
                (\ Y -> precFun g h (ins cK (fcpl (hts X cK)) Y))
                (dcn cK (PP.ivPr K) (hts X cK))
                (del cK X)
                (suc-inj (Eq-trans (del-len cK X lenCK) lx))

            hv : Eq (fcpl (hts X cK)) (nth (fbot zero) cK X)
            hv = Eq-trans (Eq-cong fcpl (Eq-cong hgt ey)) (Eq-sym ey)

            insD : Eq (precFun g h (ins cK (fcpl (hts X cK)) (del cK X)))
                      (precFun g h X)
            insD =
              Eq-cong (precFun g h)
                (Eq-trans (Eq-cong (\ z -> ins cK z (del cK X)) hv)
                  (ins-del cK X lenCK))

------------------------------------------------------------------------
-- THE RECURSION TRACE DENOTES THE RECURSION
------------------------------------------------------------------------

precTr-den : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
           -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
           -> MonoF p g -> MonoF (suc (suc p)) h
           -> Den p Tg g -> Den (suc (suc p)) Th h
           -> Den (suc p) (precTr p Tg Th) (precFun g h)
precTr-den zero    Tg Th g h mtg mth mg mh dg dh =
  mkSigma (precTr-main zero Tg Th g h mth mg mh dh cns) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc zero)) (v : Nat)
        -> Den zero (precCont zero Tg Th c lc v)
               (\ Y -> precFun g h (ins c (fcpl v) Y))
    cns zero    lc v = atNum-den zero Tg Th g h mtg mth mg mh dg dh v
    cns (suc i) ()  v
precTr-den (suc p) Tg Th g h mtg mth mg mh dg dh =
  mkSigma (precTr-main (suc p) Tg Th g h mth mg mh dh cns) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc (suc p))) (v : Nat)
        -> Den (suc p) (precCont (suc p) Tg Th c lc v)
               (\ Y -> precFun g h (ins c (fcpl v) Y))
    cns zero    lc v = atNum-den (suc p) Tg Th g h mtg mth mg mh dg dh v
    cns (suc i) lc v =
      Den-ext (suc p)
        (precTr p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v))
        (precFun (\ Y -> g (ins i (fcpl v) Y))
                 (\ Z -> h (ins (suc (suc i)) (fcpl v) Z)))
        (\ Y -> precFun g h (ins (suc i) (fcpl v) Y))
        (precFun-ins g h i v)
        (precTr-den p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
          (\ Y -> g (ins i (fcpl v) Y))
          (\ Z -> h (ins (suc (suc i)) (fcpl v) Z))
          (monoTr-cont p Tg mtg i lc v)
          (monoTr-cont (suc (suc p)) Th mth (suc (suc i)) lc v)
          (\ A B la lb l -> mg (ins i (fcpl v) A) (ins i (fcpl v) B)
                              (insG A la) (insG B lb)
                              (LeX-ins i (fcpl v) A B l))
          (\ A B la lb l -> mh (ins (suc (suc i)) (fcpl v) A)
                              (ins (suc (suc i)) (fcpl v) B)
                              (insH A la) (insH B lb)
                              (LeX-ins (suc (suc i)) (fcpl v) A B l))
          (den-cont p Tg g dg i lc v)
          (den-cont (suc (suc p)) Th h dh (suc (suc i)) lc v))
      where
        insG : (A : FTup) -> Eq (length A) p
             -> Eq (length (ins i (fcpl v) A)) (suc p)
        insG A la =
          Eq-trans
            (ins-len i (fcpl v) A
              (Eq-transport (\ z -> LeN i z) (Eq-sym la) lc))
            (Eq-cong suc la)

        insH : (A : FTup) -> Eq (length A) (suc (suc p))
             -> Eq (length (ins (suc (suc i)) (fcpl v) A)) (suc (suc (suc p)))
        insH A la =
          Eq-trans
            (ins-len (suc (suc i)) (fcpl v) A
              (Eq-transport (\ z -> LeN (suc (suc i)) z) (Eq-sym la) lc))
            (Eq-cong suc la)
