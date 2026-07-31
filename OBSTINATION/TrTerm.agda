{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrTerm
--
-- THE TRACE OF A PR TERM, AND ITS CORRECTNESS.
--
--     traceOf    : (q : PR) (n : Nat) -> Wf q n -> Tr n
--     traceOf-ok : MonoTr n (traceOf q n wf)
--                , Den n (traceOf q n wf) (evalF q)
--
-- by induction on the term.  `Wf` is `Prop1`'s well-formedness at an
-- arity: it is what supplies `i < n` for a projection and the splitting
-- `n = suc m` for a recursion, so the arities of the sub-traces line up.
--
-- `MonoTr` and `Den` have to be proved TOGETHER: `compTr-den` wants
-- `MonoTr` of every argument trace, and `compTr-mono` wants `Den` of the
-- outer one.  Neither is derivable from the other after the fact.
--
-- Three points where the statement is not quite the naive one:
--
--   * `MonoF` is arity-indexed.  `evalF succ` is NOT monotone for `LeX`
--     without it: `LeX (cons (fbot 0) nil) nil` holds, and `succ` sends
--     those to `fbot 1` and `fbot 0`.
--   * `succ` at arity `n` is the trace of `succ o proj 0`, since `succTr`
--     itself has arity exactly 1.
--   * the arguments of a composition are indexed by `Nat`, not by the
--     list, so the recursion goes through `traceList` -- `nth zerf i hs`
--     is not a structural sub-term of `comp g hs`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrTerm where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup ; LeFTup)
open import OBSTINATION.PR using
  (PR ; zerf ; proj ; succ ; comp ; prec ; evalF ; mapE)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Prop1 using (Wf ; AllWf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (LeX ; MonoF ; MonoTr ; LeX-LeFTup)
open import OBSTINATION.TrDen
open import OBSTINATION.TrWalk using (den-sem)
open import OBSTINATION.TrComp using (compTr)
open import OBSTINATION.TrCompDen using (compTr-den)
open import OBSTINATION.TrPrec using (precTr)
open import OBSTINATION.TrPrecFun using (precFun ; precFun-eval)
open import OBSTINATION.TrMono using
  (compTr-mono ; projTr-mono ; succTr-mono ; zerfTr-mono)
open import OBSTINATION.TrPrecDen using (precTr-den ; precTr-mono)

------------------------------------------------------------------------
-- MONOTONICITY OF `evalF` AT A FIXED ARITY
------------------------------------------------------------------------

evalF-MonoF : (q : PR) (a : Nat) -> MonoF a (evalF q)
evalF-MonoF q a X X' lx lx' le =
  evalF-mono q {X} {X'} (LeX-LeFTup X X' (Eq-trans lx (Eq-sym lx')) le)

------------------------------------------------------------------------
-- THE ARGUMENTS OF A COMPOSITION, INDEXED BY `Nat`
------------------------------------------------------------------------

mapE-tup : (hs : List PR) (X : FTup)
         -> Eq (mapE hs X) (tup (length hs) (\ i -> evalF (nth zerf i hs) X))
mapE-tup nil         X = refl
mapE-tup (cons q qs) X = Eq-cong (cons (evalF q X)) (mapE-tup qs X)

------------------------------------------------------------------------
-- `succ` AT AN ARBITRARY ARITY
------------------------------------------------------------------------

succ-ext : (n : Nat) -> LeN (suc zero) n -> (X : FTup) -> Eq (length X) n
         -> Eq (evalF succ (tup (suc zero) (\ i -> nth (fbot zero) zero X)))
               (evalF succ X)
succ-ext n w nil        lx =
  Empty-elim (Eq-transport (\ z -> LeN (suc zero) z) (Eq-sym lx) w)
succ-ext n w (cons x xs) lx = refl

------------------------------------------------------------------------
-- THE ARITY SPLIT OF A RECURSION
------------------------------------------------------------------------

precTr-at : (n m : Nat) -> Eq n (suc m) -> Tr m -> Tr (suc (suc m)) -> Tr n
precTr-at n m refl Tg Th = precTr m Tg Th

precTr-at-ok : (n m : Nat) (e : Eq n (suc m)) (Tg : Tr m) (Th : Tr (suc (suc m)))
               (f : FTup -> FEl)
             -> Pair (MonoTr (suc m) (precTr m Tg Th))
                     (Den (suc m) (precTr m Tg Th) f)
             -> Pair (MonoTr n (precTr-at n m e Tg Th))
                     (Den n (precTr-at n m e Tg Th) f)
precTr-at-ok n m refl Tg Th f r = r

------------------------------------------------------------------------
-- THE TRACE OF A TERM
------------------------------------------------------------------------

mutual
  traceOf : (q : PR) (n : Nat) -> Wf q n -> Tr n
  traceOf zerf        n wf = zerfTr n
  traceOf (proj i)    n wf = projTr n i wf
  traceOf succ        n wf =
    compTr (suc zero) succTr n (\ _ -> projTr n zero wf)
  traceOf (comp g hs) n wf =
    compTr (length hs) (traceOf g (length hs) (fst wf)) n
      (traceList hs n (snd wf))
  traceOf (prec g h)  n wf =
    precTr-at n (fst wf) (fst (snd wf))
      (traceOf g (fst wf) (fst (snd (snd wf))))
      (traceOf h (suc (suc (fst wf))) (snd (snd (snd wf))))

  traceList : (hs : List PR) (n : Nat) -> AllWf hs n -> Nat -> Tr n
  traceList nil         n aw i       = zerfTr n
  traceList (cons q qs) n aw zero    = traceOf q n (fst aw)
  traceList (cons q qs) n aw (suc i) = traceList qs n (snd aw) i

------------------------------------------------------------------------
-- ... DENOTES THE TERM, AND IS MONOTONE
------------------------------------------------------------------------

mutual
  traceOf-ok : (q : PR) (n : Nat) (wf : Wf q n)
             -> Pair (MonoTr n (traceOf q n wf))
                     (Den n (traceOf q n wf) (evalF q))
  traceOf-ok zerf     n wf = mkSigma (zerfTr-mono n) (zerfTr-den n)
  traceOf-ok (proj i) n wf =
    mkSigma (projTr-mono n i wf) (projTr-den n i wf)
  ----------------------------------------------------------------------
  -- succ = succ o proj 0
  ----------------------------------------------------------------------
  traceOf-ok succ     n wf = mkSigma mo de
    where
      Ths : Nat -> Tr n
      Ths _ = projTr n zero wf

      mTh : (i : Nat) -> MonoTr n (Ths i)
      mTh i = projTr-mono n zero wf

      dTh : (i : Nat) -> Den n (Ths i) (\ X -> nth (fbot zero) zero X)
      dTh i = projTr-den n zero wf

      hm : (i : Nat) -> MonoF n (\ X -> nth (fbot zero) zero X)
      hm i = \ A B la lb l -> l zero

      mo : MonoTr n (compTr (suc zero) succTr n Ths)
      mo =
        compTr-mono (suc zero) succTr (evalF succ) succTr-den
          (evalF-MonoF succ (suc zero)) n Ths mTh

      de : Den n (compTr (suc zero) succTr n Ths) (evalF succ)
      de =
        Den-extL n (compTr (suc zero) succTr n Ths)
          (\ X -> evalF succ (tup (suc zero) (\ i -> nth (fbot zero) zero X)))
          (evalF succ) (succ-ext n wf)
          (compTr-den (suc zero) succTr (evalF succ) succTr-mono succTr-den
            n Ths (\ i X -> nth (fbot zero) zero X) mTh hm dTh)
  ----------------------------------------------------------------------
  -- composition
  ----------------------------------------------------------------------
  traceOf-ok (comp g hs) n wf = mkSigma mo de
    where
      Tg : Tr (length hs)
      Tg = traceOf g (length hs) (fst wf)

      Ths : Nat -> Tr n
      Ths = traceList hs n (snd wf)

      hf : Nat -> FTup -> FEl
      hf i = evalF (nth zerf i hs)

      mo : MonoTr n (compTr (length hs) Tg n Ths)
      mo =
        compTr-mono (length hs) Tg (evalF g)
          (snd (traceOf-ok g (length hs) (fst wf)))
          (evalF-MonoF g (length hs)) n Ths
          (\ i -> fst (traceList-ok hs n (snd wf) i))

      de : Den n (compTr (length hs) Tg n Ths) (evalF (comp g hs))
      de =
        Den-ext n (compTr (length hs) Tg n Ths)
          (\ X -> evalF g (tup (length hs) (\ i -> hf i X)))
          (evalF (comp g hs))
          (\ X -> Eq-cong (evalF g) (Eq-sym (mapE-tup hs X)))
          (compTr-den (length hs) Tg (evalF g)
            (fst (traceOf-ok g (length hs) (fst wf)))
            (snd (traceOf-ok g (length hs) (fst wf)))
            n Ths hf
            (\ i -> fst (traceList-ok hs n (snd wf) i))
            (\ i -> evalF-MonoF (nth zerf i hs) n)
            (\ i -> snd (traceList-ok hs n (snd wf) i)))
  ----------------------------------------------------------------------
  -- primitive recursion
  ----------------------------------------------------------------------
  traceOf-ok (prec g h) n wf =
    precTr-at-ok n m e Tg Th (evalF (prec g h))
      (mkSigma
        (precTr-mono m Tg Th (evalF g) (evalF h)
          (fst okg) (fst okh)
          (evalF-MonoF g m) (evalF-MonoF h (suc (suc m)))
          (snd okg) (snd okh))
        (Den-ext (suc m) (precTr m Tg Th)
          (precFun (evalF g) (evalF h)) (evalF (prec g h))
          (precFun-eval g h)
          (precTr-den m Tg Th (evalF g) (evalF h)
            (fst okg) (fst okh)
            (evalF-MonoF g m) (evalF-MonoF h (suc (suc m)))
            (snd okg) (snd okh))))
    where
      m : Nat
      m = fst wf

      e : Eq n (suc m)
      e = fst (snd wf)

      Tg : Tr m
      Tg = traceOf g m (fst (snd (snd wf)))

      Th : Tr (suc (suc m))
      Th = traceOf h (suc (suc m)) (snd (snd (snd wf)))

      okg : Pair (MonoTr m Tg) (Den m Tg (evalF g))
      okg = traceOf-ok g m (fst (snd (snd wf)))

      okh : Pair (MonoTr (suc (suc m)) Th) (Den (suc (suc m)) Th (evalF h))
      okh = traceOf-ok h (suc (suc m)) (snd (snd (snd wf)))

  traceList-ok : (hs : List PR) (n : Nat) (aw : AllWf hs n) (i : Nat)
               -> Pair (MonoTr n (traceList hs n aw i))
                       (Den n (traceList hs n aw i) (evalF (nth zerf i hs)))
  traceList-ok nil         n aw i       =
    mkSigma (zerfTr-mono n) (zerfTr-den n)
  traceList-ok (cons q qs) n aw zero    = traceOf-ok q n (fst aw)
  traceList-ok (cons q qs) n aw (suc i) = traceList-ok qs n (snd aw) i

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

traceOf-den : (q : PR) (n : Nat) (wf : Wf q n)
            -> Den n (traceOf q n wf) (evalF q)
traceOf-den q n wf = snd (traceOf-ok q n wf)

traceOf-sem : (q : PR) (n : Nat) (wf : Wf q n) (X : FTup) -> Eq (length X) n
            -> Eq (sem n (traceOf q n wf) X) (evalF q X)
traceOf-sem q n wf X lx =
  den-sem n (traceOf q n wf) (evalF q) (traceOf-den q n wf) X lx
