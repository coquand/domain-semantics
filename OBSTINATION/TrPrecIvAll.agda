{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecIvAll
--
-- MP1'S INDEX CLAUSE FOR THE WHOLE RECURSION TRACE.
--
-- `TrPrecIvP.precTr-ivP` settles the TOP NODE of `precTr`.  `IvAll` is
-- structural, so what is left is every continuation:
--
--     precCont p Tg Th zero    lc v = atNum v
--     precCont (suc p) Tg Th (suc i) lc v =
--       precTr p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
--
-- Two recursions, on two different arguments, and they do NOT interleave:
--
--   * `atNum` recurses on the NUMERAL.  `atNum 0 = Tg`;
--     `atNum (v+1) = compTr Th (argsA v)`, whose arguments are a numeral,
--     `atNum v`, and projections -- so `TrSelStab.compTr-ivAll-full`
--     applies, and its `MP1T` obligation for `atNum v` is discharged by
--     `TrMP1Red.mp1T-from-iv`, which is GENERAL: `Den` + `MonoTr` +
--     `UOfrz` + `IvAll` give `MP1T`.  Nothing about `precTr` is used.
--
--   * the parameter continuations recurse on the ARITY, at the FROZEN
--     base and step -- and `TrPrecFun.precFun-ins` says that freezing a
--     parameter of a recursion IS the recursion of the frozen base and
--     step, so the hypothesis `UOfrz (suc p) (precFun g h)` reproduces
--     itself one arity down (`UOfrz-ext`).
--
-- `UOfrz` rather than bare `UO` is exactly what makes this go through:
-- the recursive value's own continuations denote frozen functions, and
-- Proposition 1 for those is `TrUOfrz.uofrz-PR`.  Freezing coordinate 0
-- to `fcpl v` turns `precFun g h` into `\ Y -> precA g h (fcpl v) Y`,
-- which is what `atNum v` denotes -- so the same hypothesis serves both
-- recursions.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecIvAll where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (MonoTr ; MonoF)
open import OBSTINATION.TrDen using (Den ; ins ; ins-len)
open import OBSTINATION.TrWalk using (den-cont)
open import OBSTINATION.TrCompDen using (monoTr-cont ; LeX-ins)
open import OBSTINATION.TrMP1 using
  (MP1T ; IvAll ; mp1T-ivAll ; projTr-mp1)
open import OBSTINATION.TrMP1Red using (mp1T-from-iv)
open import OBSTINATION.TrSelStab using (compTr-ivAll-full)
open import OBSTINATION.TrUOfrz using (UOfrz ; UOfrz-ext)
open import OBSTINATION.TrPrecFun using (precFun ; precA ; precFun-ins)
open import OBSTINATION.TrPrec using (module N ; argPr ; precTr ; precCont)
open import OBSTINATION.TrPrecDen using (atNum-mono ; atNum-den ; argPr-mono)
open import OBSTINATION.TrPrecIvP using (precTr-ivP)

------------------------------------------------------------------------
-- PLUMBING
------------------------------------------------------------------------

mp1T-cont : (a : Nat) (T : Tr (suc a)) -> MP1T (suc a) T
          -> (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
          -> MP1T a (contOf T c lc v)
mp1T-cont a (stop w)              m1 c lc v = tt
mp1T-cont a (node iv ivr ov cont) m1 c lc v = snd (snd m1) c lc v

argPr-mp1 : (p i : Nat) -> MP1T p (argPr p i (LeN-dec (suc i) p))
argPr-mp1 p i = go (LeN-dec (suc i) p) refl
  where
    go : (D : Dec (LeN (suc i) p)) -> Eq (LeN-dec (suc i) p) D
       -> MP1T p (argPr p i (LeN-dec (suc i) p))
    go (yes li) eD =
      Eq-transport (\ T -> MP1T p T) (Eq-sym (Eq-cong (argPr p i) eD))
        (projTr-mp1 p i li)
    go (no  ni) eD =
      Eq-transport (\ T -> MP1T p T) (Eq-sym (Eq-cong (argPr p i) eD)) tt

------------------------------------------------------------------------
-- THE NUMERAL RECURSION
--
-- `atNum v` denotes `\ Y -> precA g h (fcpl v) Y`, which IS `precFun g h`
-- with coordinate 0 frozen to `fcpl v` (`ins zero x Y = cons x Y`), so
-- its `UOfrz` is the `c = 0` component of the hypothesis.
------------------------------------------------------------------------

atNum-ivAll : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p)))
              (g h : FTup -> FEl)
            -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
            -> MP1T p Tg -> MP1T (suc (suc p)) Th
            -> Den p Tg g -> Den (suc (suc p)) Th h
            -> MonoF p g -> MonoF (suc (suc p)) h
            -> ((v : Nat) -> UOfrz p (\ Y -> precA g h (fcpl v) Y))
            -> (v : Nat) -> IvAll p (N.atNum p Tg Th v)
atNum-ivAll p Tg Th g h mtg mth m1g m1th dg dh mg mh ufA zero =
  mp1T-ivAll p Tg m1g
atNum-ivAll p Tg Th g h mtg mth m1g m1th dg dh mg mh ufA (suc v) =
  compTr-ivAll-full (suc (suc p)) Th mth m1th p (N.argsA p Tg Th v) am m1a
  where
    am : (i : Nat) -> MonoTr p (N.argsA p Tg Th v i)
    am zero          = tt
    am (suc zero)    = atNum-mono p Tg Th h dh mh mtg v
    am (suc (suc i)) = argPr-mono p i

    m1a : (i : Nat) -> MP1T p (N.argsA p Tg Th v i)
    m1a zero       = tt
    m1a (suc zero) =
      mp1T-from-iv p (N.atNum p Tg Th v) (\ Y -> precA g h (fcpl v) Y)
        (atNum-den p Tg Th g h mtg mth mg mh dg dh v)
        (atNum-mono p Tg Th h dh mh mtg v)
        (ufA v)
        (atNum-ivAll p Tg Th g h mtg mth m1g m1th dg dh mg mh ufA v)
    m1a (suc (suc i)) = argPr-mp1 p i

------------------------------------------------------------------------
-- THE ARITY RECURSION, AND THE INDEX CLAUSE FOR `precTr`
------------------------------------------------------------------------

precTr-ivAll : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p)))
               (g h : FTup -> FEl)
             -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
             -> MP1T p Tg -> MP1T (suc (suc p)) Th
             -> Den p Tg g -> Den (suc (suc p)) Th h
             -> MonoF p g -> MonoF (suc (suc p)) h
             -> UOfrz (suc p) (precFun g h)
             -> IvAll (suc p) (precTr p Tg Th)
precTr-ivAll zero Tg Th g h mtg mth m1g m1th dg dh mg mh uf =
  mkSigma (precTr-ivP zero Th g h mth m1th dh mg mh (fst uf)) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc zero)) (v : Nat)
        -> IvAll zero (precCont zero Tg Th c lc v)
    cns zero    lc v =
      atNum-ivAll zero Tg Th g h mtg mth m1g m1th dg dh mg mh
        (\ w -> snd uf zero tt w) v
    cns (suc i) ()  v
precTr-ivAll (suc p) Tg Th g h mtg mth m1g m1th dg dh mg mh uf =
  mkSigma (precTr-ivP (suc p) Th g h mth m1th dh mg mh (fst uf)) cns
  where
    cns : (c : Nat) (lc : LeN (suc c) (suc (suc p))) (v : Nat)
        -> IvAll (suc p) (precCont (suc p) Tg Th c lc v)
    cns zero lc v =
      atNum-ivAll (suc p) Tg Th g h mtg mth m1g m1th dg dh mg mh
        (\ w -> snd uf zero tt w) v
    cns (suc i) lc v =
      precTr-ivAll p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
        (\ Y -> g (ins i (fcpl v) Y))
        (\ Z -> h (ins (suc (suc i)) (fcpl v) Z))
        (monoTr-cont p Tg mtg i lc v)
        (monoTr-cont (suc (suc p)) Th mth (suc (suc i)) lc v)
        (mp1T-cont p Tg m1g i lc v)
        (mp1T-cont (suc (suc p)) Th m1th (suc (suc i)) lc v)
        (den-cont p Tg g dg i lc v)
        (den-cont (suc (suc p)) Th h dh (suc (suc i)) lc v)
        (\ A B la lb l -> mg (ins i (fcpl v) A) (ins i (fcpl v) B)
                             (insG A la) (insG B lb)
                             (LeX-ins i (fcpl v) A B l))
        (\ A B la lb l -> mh (ins (suc (suc i)) (fcpl v) A)
                             (ins (suc (suc i)) (fcpl v) B)
                             (insH A la) (insH B lb)
                             (LeX-ins (suc (suc i)) (fcpl v) A B l))
        ufc
      where
        insG : (A : FTup) -> Eq (length A) p
             -> Eq (length (ins i (fcpl v) A)) (suc p)
        insG A la =
          Eq-trans
            (ins-len i (fcpl v) A
              (Eq-transport (\ z -> LeN i z) (Eq-sym la) lc))
            (Eq-cong suc la)

        insH : (A : FTup) -> Eq (length A) (suc (suc p))
             -> Eq (length (ins (suc (suc i)) (fcpl v) A))
                   (suc (suc (suc p)))
        insH A la =
          Eq-trans
            (ins-len (suc (suc i)) (fcpl v) A
              (Eq-transport (\ z -> LeN (suc (suc i)) z) (Eq-sym la) lc))
            (Eq-cong suc la)

        -- freezing a PARAMETER of a recursion IS the recursion of the
        -- frozen base and step (`precFun-ins`)
        ufc : UOfrz (suc p)
                (precFun (\ Y -> g (ins i (fcpl v) Y))
                         (\ Z -> h (ins (suc (suc i)) (fcpl v) Z)))
        ufc =
          UOfrz-ext (suc p)
            (\ Y -> precFun g h (ins (suc i) (fcpl v) Y))
            (precFun (\ Y -> g (ins i (fcpl v) Y))
                     (\ Z -> h (ins (suc (suc i)) (fcpl v) Z)))
            (\ X lx -> Eq-sym (precFun-ins g h i v X))
            (snd uf (suc i) lc v)
