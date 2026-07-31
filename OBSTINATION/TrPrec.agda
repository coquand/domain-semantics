{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrec
--
-- THE TRACE OF A PRIMITIVE RECURSION.
--
--     f (bot  , Y) = bot
--     f (0    , Y) = g (Y)
--     f (S x  , Y) = h (x , f (x,Y) , Y)
--
-- `f` has arity `suc p` (coordinate 0 = `x`, `1+i` = the parameters),
-- `g` has arity `p`, `h` has arity `suc (suc p)` (0 = `x`, 1 = the
-- recursive value, `2+i` = the parameters).
--
-- THE MAIN WALK is at an INCOMPLETE recursion argument, so only the third
-- clause fires and `g` does not appear.  At levels `L` (coordinate 0 = the
-- depth, `1+i` = the parameter levels) the value and the demand are read
-- off `h` at the tuple
--
--     avf L j  =  ( S^j(bot) , Vd L j , S^(L 1)(bot) , ... )
--
--     Vd L 0 = bot            Vd L (j+1) = sem     h (avf L j)
--     Qd L 0 = 0              Qd L (j+1) = qsel (Qd L j) (blockOn h (avf L j))
--
-- `qsel` is the descent: `h` waiting on its coordinate 0 means `f` wants
-- more `x`; on coordinate 1 means the walk DESCENDS one depth; on `2+i`
-- means `f` wants parameter `1+i`.
--
-- THE BASE `g` APPEARS ONLY IN A CONTINUATION -- freezing coordinate 0 to
-- a numeral is exactly "the recursion argument is total":
--
--     cont 0 _ 0     = Tg
--     cont 0 _ (v+1) = comp h ( S^v(0) , cont 0 _ v , proj_0 ... proj_(p-1) )
--
-- built with `TrComp.compTr`.  Freezing a PARAMETER instead just freezes
-- it in `g` and in `h`, and recurses on `p`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrec where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (bump ; nOf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrComp using (compTr)

------------------------------------------------------------------------
-- `blockOn` really does return a coordinate in range
------------------------------------------------------------------------

InRange : Nat -> Or Top Nat -> Set
InRange a (inl tt) = Top
InRange a (inr c)  = LeN (suc c) a

su-range : (a c j : Nat) -> LeN (suc c) (suc a) -> LeN (suc j) a
         -> LeN (suc (su c j)) (suc a)
su-range a       zero    j       lc lj = lj
su-range zero    (suc c) j       lc ()
su-range (suc a) (suc c) zero    lc lj = tt
su-range (suc a) (suc c) (suc j) lc lj = su-range a c j lc lj

shiftOr-range : (a c : Nat) -> LeN (suc c) (suc a) -> (r : Or Top Nat)
              -> InRange a r -> InRange (suc a) (shiftOr c r)
shiftOr-range a c lc (inl tt) ir = tt
shiftOr-range a c lc (inr j)  ir = su-range a c j lc ir

hb-range : (a : Nat) (y : FEl) (r : Or Top Nat) -> InRange a r
         -> InRange a (hb y r)
hb-range a (fcpl w) r ir = tt
hb-range a (fbot w) r ir = ir

bb-range : (a c : Nat) -> LeN (suc c) a -> (alt : Or Top Nat) -> InRange a alt
         -> (y : FEl) -> InRange a (bb c alt y)
bb-range a c lc alt ia (fbot w) = lc
bb-range a c lc alt ia (fcpl w) = ia

mutual
  blockOn-range : (a : Nat) (T : Tr a) (X : FTup) -> InRange a (blockOn a T X)
  blockOn-range a       (stop v)              X = tt
  blockOn-range (suc a) (node iv ivr ov cont) X =
    blockAt-range a iv ov cont X (nOf (suc a) iv ivr (hts X)) ivr

  blockAt-range : (a : Nat) (iv : Nat -> Nat) (ov : Nat -> FEl)
                -> (cont : (c : Nat) -> LeN (suc c) (suc a) -> (v : Nat) -> Tr a)
                -> (X : FTup) -> (n : Nat)
                -> (ivr : (m : Nat) -> LeN (suc (iv m)) (suc a))
                -> InRange (suc a) (blockAt a iv ov cont X n ivr)
  blockAt-range a iv ov cont X n ivr =
    hb-range (suc a) (ov n) _
      (bb-range (suc a) (iv n) (ivr n) _
        (shiftOr-range a (iv n) (ivr n)
          (blockOn a (cont (iv n) (ivr n) (hts X (iv n))) (del (iv n) X))
          (blockOn-range a (cont (iv n) (ivr n) (hts X (iv n))) (del (iv n) X)))
        (nth (fbot zero) (iv n) X))

------------------------------------------------------------------------
-- THE VALUE AND THE DEMAND AT FIXED PARAMETER LEVELS
------------------------------------------------------------------------

-- the descent: which of `f`'s coordinates does `h`'s demand become?
qsel : Nat -> Or Top Nat -> Nat
qsel prev (inl tt)              = zero
qsel prev (inr zero)            = zero
qsel prev (inr (suc zero))      = prev
qsel prev (inr (suc (suc i)))   = suc i

qsel-range : (p prev : Nat) -> LeN (suc prev) (suc p)
           -> (r : Or Top Nat) -> InRange (suc (suc p)) r
           -> LeN (suc (qsel prev r)) (suc p)
qsel-range p prev lp (inl tt)            ir = tt
qsel-range p prev lp (inr zero)          ir = tt
qsel-range p prev lp (inr (suc zero))    ir = lp
qsel-range p prev lp (inr (suc (suc i))) ir = ir

module R (p : Nat) (Th : Tr (suc (suc p))) where

  mutual
    Vd : (Nat -> Nat) -> Nat -> FEl
    Vd L zero    = fbot zero
    Vd L (suc j) = sem (suc (suc p)) Th (avT L j)

    avT : (Nat -> Nat) -> Nat -> FTup
    avT L j = tup (suc (suc p)) (avf L j)

    avf : (Nat -> Nat) -> Nat -> Nat -> FEl
    avf L j zero             = fbot j
    avf L j (suc zero)       = Vd L j
    avf L j (suc (suc i))    = fbot (L (suc i))

  Qd : (Nat -> Nat) -> Nat -> Nat
  Qd L zero    = zero
  Qd L (suc j) = qsel (Qd L j) (blockOn (suc (suc p)) Th (avT L j))

  Qd-range : (L : Nat -> Nat) (m : Nat) -> LeN (suc (Qd L m)) (suc p)
  Qd-range L zero    = tt
  Qd-range L (suc j) =
    qsel-range p (Qd L j) (Qd-range L j)
      (blockOn (suc (suc p)) Th (avT L j))
      (blockOn-range (suc (suc p)) Th (avT L j))

------------------------------------------------------------------------
-- THE WALK OF `f` ITSELF
------------------------------------------------------------------------

module P (p : Nat) (Th : Tr (suc (suc p))) where

  open R p Th public

  mutual
    Lv : Nat -> Nat -> Nat
    Lv zero    c = zero
    Lv (suc k) c = bump (ivP k) (Lv k) c

    ivP : Nat -> Nat
    ivP k = Qd (Lv k) (Lv k zero)

  ivPr : (k : Nat) -> LeN (suc (ivP k)) (suc p)
  ivPr k = Qd-range (Lv k) (Lv k zero)

  ovP : Nat -> FEl
  ovP k = Vd (Lv k) (Lv k zero)

------------------------------------------------------------------------
-- THE RECURSION ARGUMENT IS A NUMERAL: `g` FINALLY APPEARS
--
--   f (0     , Y) = g (Y)
--   f (S^(v+1) 0 , Y) = h ( S^v(0) , f (S^v(0) , Y) , Y )
------------------------------------------------------------------------

-- the parameter arguments of the step term: the projections, when they
-- are in range.  TOP-LEVEL, so that a proof can case on the decision --
-- a `where`-bound helper is lifted with the module telescope and is then
-- unreachable.
argPr : (p i : Nat) -> Dec (LeN (suc i) p) -> Tr p
argPr p i (yes li) = projTr p i li
argPr p i (no  _)  = stop (fbot zero)

module N (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p))) where

  mutual
    atNum : Nat -> Tr p
    atNum zero    = Tg
    atNum (suc v) = compTr (suc (suc p)) Th p (argsA v)

    argsA : Nat -> Nat -> Tr p
    argsA v zero             = stop (fcpl v)
    argsA v (suc zero)       = atNum v
    argsA v (suc (suc i))    = argPr p i (LeN-dec (suc i) p)

------------------------------------------------------------------------
-- THE TRACE OF `prec g h`
------------------------------------------------------------------------

-- The node is built UNIFORMLY in `p` -- the case analysis lives in the
-- separate top-level `precCont` -- so that `precTr p Tg Th` reduces to a
-- `node` even when `p` is a variable.  Without that, no statement about
-- `sem (precTr p Tg Th)` could be proved for an abstract arity.
mutual
  precTr : (p : Nat) -> Tr p -> Tr (suc (suc p)) -> Tr (suc p)
  precTr p Tg Th =
    node (P.ivP p Th) (P.ivPr p Th) (P.ovP p Th) (precCont p Tg Th)

  precCont : (p : Nat) -> Tr p -> Tr (suc (suc p))
           -> (c : Nat) -> LeN (suc c) (suc p) -> (v : Nat) -> Tr p
  precCont p       Tg Th zero    lc v = N.atNum p Tg Th v
  precCont zero    Tg Th (suc i) ()  v
  precCont (suc p) Tg Th (suc i) lc v =
    precTr p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
