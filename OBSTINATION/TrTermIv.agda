{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrTermIv
--
-- MP1 FOR THE TRACE OF EVERY PR TERM.
--
--     traceOf-ivAll : IvAll n (traceOf q n wf)
--     traceOf-MP1   : MP1T  n (traceOf q n wf)
--
-- The induction on the PR term, with the three constructions supplying
-- the clauses that are not immediate:
--
--   * `comp` (and `succ`, which is `succ o proj 0`) by
--     `TrSelStab.compTr-ivAll-full`;
--   * `prec` by `TrPrecIvAll.precTr-ivAll`, whose `UOfrz` hypothesis is
--     `TrUOfrz.uofrz-PR` transported along `TrPrecFun.precFun-eval`;
--   * and `TrMP1Red.traceOf-mp1` turns each `IvAll` into the `MP1T` the
--     next construction needs -- the value half being Proposition 1, not
--     an independent obligation.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrTermIv where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; zerf ; succ ; proj ; comp ; prec ; evalF)
open import OBSTINATION.Prop1 using (Wf ; AllWf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (MonoTr)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMono using
  (zerfTr-mono ; succTr-mono ; projTr-mono)
open import OBSTINATION.TrMP1 using
  (MP1T ; IvAll ; mp1T-ivAll ; zerfTr-mp1 ; succTr-mp1 ; projTr-mp1)
open import OBSTINATION.TrMP1Red using (traceOf-mp1)
open import OBSTINATION.TrSelStab using (compTr-ivAll-full)
open import OBSTINATION.TrUOfrz using (UOfrz ; UOfrz-ext ; uofrz-PR)
open import OBSTINATION.TrPrecFun using (precFun ; precFun-eval)
open import OBSTINATION.TrPrec using (precTr)
open import OBSTINATION.TrPrecIvAll using (precTr-ivAll)
open import OBSTINATION.TrTerm using
  (precTr-at ; evalF-MonoF ; traceOf ; traceList ; traceOf-ok ; traceList-ok)

------------------------------------------------------------------------
-- THE ARITY SPLIT, FOR `IvAll`
------------------------------------------------------------------------

precTr-at-iv : (n m : Nat) (e : Eq n (suc m))
               (Tg : Tr m) (Th : Tr (suc (suc m)))
             -> IvAll (suc m) (precTr m Tg Th)
             -> IvAll n (precTr-at n m e Tg Th)
precTr-at-iv n m refl Tg Th r = r

------------------------------------------------------------------------
-- THE INDUCTION
------------------------------------------------------------------------

mutual
  traceOf-ivAll : (q : PR) (n : Nat) (wf : Wf q n) -> IvAll n (traceOf q n wf)
  traceOf-ivAll zerf     n wf = mp1T-ivAll n (zerfTr n) (zerfTr-mp1 n)
  traceOf-ivAll (proj i) n wf =
    mp1T-ivAll n (projTr n i wf) (projTr-mp1 n i wf)
  ----------------------------------------------------------------------
  -- succ = succ o proj 0
  ----------------------------------------------------------------------
  traceOf-ivAll succ n wf =
    compTr-ivAll-full (suc zero) succTr succTr-mono succTr-mp1 n Ths mTh m1Th
    where
      Ths : Nat -> Tr n
      Ths _ = projTr n zero wf

      mTh : (i : Nat) -> MonoTr n (Ths i)
      mTh i = projTr-mono n zero wf

      m1Th : (i : Nat) -> MP1T n (Ths i)
      m1Th i = projTr-mp1 n zero wf
  ----------------------------------------------------------------------
  -- composition
  ----------------------------------------------------------------------
  traceOf-ivAll (comp g hs) n wf =
    compTr-ivAll-full (length hs) Tg
      (fst (traceOf-ok g (length hs) (fst wf)))
      (traceOf-mp1 g (length hs) (fst wf)
        (traceOf-ivAll g (length hs) (fst wf)))
      n (traceList hs n (snd wf))
      (\ i -> fst (traceList-ok hs n (snd wf) i))
      (\ i -> traceList-mp1 hs n (snd wf) i)
    where
      Tg : Tr (length hs)
      Tg = traceOf g (length hs) (fst wf)
  ----------------------------------------------------------------------
  -- primitive recursion
  ----------------------------------------------------------------------
  traceOf-ivAll (prec g h) n wf =
    precTr-at-iv n m e Tg Th
      (precTr-ivAll m Tg Th (evalF g) (evalF h)
        (fst okg) (fst okh)
        (traceOf-mp1 g m wg (traceOf-ivAll g m wg))
        (traceOf-mp1 h (suc (suc m)) wh (traceOf-ivAll h (suc (suc m)) wh))
        (snd okg) (snd okh)
        (evalF-MonoF g m) (evalF-MonoF h (suc (suc m)))
        uf)
    where
      m : Nat
      m = fst wf

      e : Eq n (suc m)
      e = fst (snd wf)

      wg : Wf g m
      wg = fst (snd (snd wf))

      wh : Wf h (suc (suc m))
      wh = snd (snd (snd wf))

      Tg : Tr m
      Tg = traceOf g m wg

      Th : Tr (suc (suc m))
      Th = traceOf h (suc (suc m)) wh

      okg : Pair (MonoTr m Tg) (Den m Tg (evalF g))
      okg = traceOf-ok g m wg

      okh : Pair (MonoTr (suc (suc m)) Th) (Den (suc (suc m)) Th (evalF h))
      okh = traceOf-ok h (suc (suc m)) wh

      -- Proposition 1, closed under freezing, for the recursion itself
      uf : UOfrz (suc m) (precFun (evalF g) (evalF h))
      uf =
        UOfrz-ext (suc m) (evalF (prec g h))
          (precFun (evalF g) (evalF h))
          (\ X lx -> Eq-sym (precFun-eval g h X))
          (Eq-transport (\ z -> UOfrz z (evalF (prec g h))) e
            (uofrz-PR n (prec g h) wf))

  traceList-mp1 : (hs : List PR) (n : Nat) (aw : AllWf hs n) (i : Nat)
                -> MP1T n (traceList hs n aw i)
  traceList-mp1 nil         n aw i    = zerfTr-mp1 n
  traceList-mp1 (cons q qs) n aw zero =
    traceOf-mp1 q n (fst aw) (traceOf-ivAll q n (fst aw))
  traceList-mp1 (cons q qs) n aw (suc i) = traceList-mp1 qs n (snd aw) i

------------------------------------------------------------------------
-- THE THEOREM: MP1 HOLDS FOR THE TRACE OF EVERY PR TERM
------------------------------------------------------------------------

traceOf-MP1 : (q : PR) (n : Nat) (wf : Wf q n) -> MP1T n (traceOf q n wf)
traceOf-MP1 q n wf = traceOf-mp1 q n wf (traceOf-ivAll q n wf)
