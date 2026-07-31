{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrTermMP1
--
-- **MP1 FOR THE TRACE OF EVERY PR TERM, WITHOUT PROPOSITION 1.**
--
--     traceOf-MP1np : (q : PR) (n : Nat) (wf : Wf q n) -> MP1T n (traceOf q n wf)
--
-- The same induction as `TrTermIv.traceOf-MP1`, but carrying `MP1T`
-- directly instead of `IvAll` plus `TrMP1Red.mp1T-from-iv` -- which is
-- where Proposition 1 entered, through `TrUOfrz.uofrz-PR`.  Every clause
-- now has its own Prop-1-free proof:
--
--   index, comp  --  `TrSelStab.compTr-ivAll-full`   (always was)
--   index, prec  --  `TrPrecIvPMP.precTr-ivP-mp`
--   value, comp  --  `TrCompMP1.compTr-verdict`
--   value, prec  --  `TrPrecOvP.ovP-verdict`
--
-- and the two structural recursions -- `compTr-MP1T` on the outer arity,
-- `precTr-MP1` on the arity of the recursion, with `atNum-MP1` for the
-- numeral continuations -- simply thread them.  `UOfrz` has disappeared:
-- `atNum-MP1` recurses on itself where `atNum-ivAll` called
-- `mp1T-from-iv`.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrTermMP1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; zerf ; proj ; succ ; comp ; prec ; evalF)
open import OBSTINATION.Prop1 using (Wf ; AllWf)
open import OBSTINATION.TraceDef
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TrSat using (MonoTr ; MonoF ; LeX)
open import OBSTINATION.TrDen using (Den ; ins ; ins-len ; succTr-den)
open import OBSTINATION.TrWalk using (den-cont)
open import OBSTINATION.TrMono using
  (compTr-mono ; succTr-mono ; projTr-mono ; zerfTr-mono)
open import OBSTINATION.TrCompDen using (monoTr-cont ; LeX-ins)
open import OBSTINATION.TrMP1 using
  (MP1T ; zerfTr-mp1 ; succTr-mp1 ; projTr-mp1)
open import OBSTINATION.TrComp using (module W ; compTr)
open import OBSTINATION.TrMPT using (mp1-mpT)
open import OBSTINATION.TrSelStab using (compTr-ivAll-full)
open import OBSTINATION.TrCompMP1 using (compTr-verdict)
open import OBSTINATION.TrPrec using
  (module N ; module P ; argPr ; precTr ; precCont)
open import OBSTINATION.TrPrecDen using (atNum-mono ; argPr-mono)
open import OBSTINATION.TrPrecIvPMP using (precTr-ivP-mp)
open import OBSTINATION.TrPrecOvP using (ovP-verdict)
open import OBSTINATION.TrTerm using
  (traceOf ; traceList ; traceOf-ok ; traceList-ok ; precTr-at ; evalF-MonoF)

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
-- MP1 FOR A COMPOSITE, BY RECURSION ON THE OUTER ARITY
------------------------------------------------------------------------

compTr-MP1T : (p : Nat) (Tg : Tr p) (g : FTup -> FEl)
            -> Den p Tg g -> MonoF p g
            -> MonoTr p Tg -> MP1T p Tg
            -> (a : Nat) (Ths : Nat -> Tr a)
            -> ((i : Nat) -> MonoTr a (Ths i))
            -> ((i : Nat) -> MP1T a (Ths i))
            -> MP1T a (compTr p Tg a Ths)
compTr-MP1T p Tg g dg mg mtg m1g zero    Ths mTh m1h = tt
compTr-MP1T p Tg g dg mg mtg m1g (suc a) Ths mTh m1h =
  mkSigma (fst (compTr-ivAll-full p Tg mtg (mp1-mpT p Tg mtg m1g) (suc a) Ths
                  mTh (\ i -> mp1-mpT (suc a) (Ths i) (mTh i) (m1h i))))
    (mkSigma (compTr-verdict p Tg mtg m1g a Ths mTh m1h ovm) cns)
  where
    ovm : (m n : Nat) -> LeN m n
        -> LeF (W.ovf p Tg a Ths m) (W.ovf p Tg a Ths n)
    ovm = fst (compTr-mono p Tg g dg mg (suc a) Ths mTh)

    cns : (c : Nat) (lc : LeN (suc c) (suc a)) (v : Nat)
        -> MP1T a (compTr p Tg a (\ i -> contOf (Ths i) c lc v))
    cns c lc v =
      compTr-MP1T p Tg g dg mg mtg m1g a (\ i -> contOf (Ths i) c lc v)
        (\ i -> monoTr-cont a (Ths i) (mTh i) c lc v)
        (\ i -> mp1T-cont a (Ths i) (m1h i) c lc v)

------------------------------------------------------------------------
-- MP1 FOR THE RECURSION
------------------------------------------------------------------------

mutual
  --------------------------------------------------------------------
  -- the numeral continuations: `atNum v` is `g` at `v = 0` and a
  -- composition above it.  Where `atNum-ivAll` had to invoke
  -- `mp1T-from-iv` -- and so Proposition 1 -- this recurses on itself.
  --------------------------------------------------------------------
  atNum-MP1 : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p)))
              (g h : FTup -> FEl)
            -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
            -> MP1T p Tg -> MP1T (suc (suc p)) Th
            -> Den p Tg g -> Den (suc (suc p)) Th h
            -> MonoF p g -> MonoF (suc (suc p)) h
            -> (v : Nat) -> MP1T p (N.atNum p Tg Th v)
  atNum-MP1 p Tg Th g h mtg mth m1g m1th dg dh mg mh zero = m1g
  atNum-MP1 p Tg Th g h mtg mth m1g m1th dg dh mg mh (suc v) =
    compTr-MP1T (suc (suc p)) Th h dh mh mth m1th p (N.argsA p Tg Th v) am m1a
    where
      am : (i : Nat) -> MonoTr p (N.argsA p Tg Th v i)
      am zero          = tt
      am (suc zero)    = atNum-mono p Tg Th h dh mh mtg v
      am (suc (suc i)) = argPr-mono p i

      m1a : (i : Nat) -> MP1T p (N.argsA p Tg Th v i)
      m1a zero          = tt
      m1a (suc zero)    =
        atNum-MP1 p Tg Th g h mtg mth m1g m1th dg dh mg mh v
      m1a (suc (suc i)) = argPr-mp1 p i

  --------------------------------------------------------------------
  -- and the recursion itself
  --------------------------------------------------------------------
  precTr-MP1 : (p : Nat) (Tg : Tr p) (Th : Tr (suc (suc p)))
               (g h : FTup -> FEl)
             -> MonoTr p Tg -> MonoTr (suc (suc p)) Th
             -> MP1T p Tg -> MP1T (suc (suc p)) Th
             -> Den p Tg g -> Den (suc (suc p)) Th h
             -> MonoF p g -> MonoF (suc (suc p)) h
             -> MP1T (suc p) (precTr p Tg Th)
  precTr-MP1 zero Tg Th g h mtg mth m1g m1th dg dh mg mh =
    mkSigma ivc (mkSigma (ovP-verdict zero Th mth m1th g h dh mg mh ivc) cns)
    where
      ivc : EvConstN (P.ivP zero Th)
      ivc =
        precTr-ivP-mp zero Th g h mth
          (mp1-mpT (suc (suc zero)) Th mth m1th) dh mg mh

      cns : (c : Nat) (lc : LeN (suc c) (suc zero)) (v : Nat)
          -> MP1T zero (precCont zero Tg Th c lc v)
      cns zero    lc v =
        atNum-MP1 zero Tg Th g h mtg mth m1g m1th dg dh mg mh v
      cns (suc i) ()  v
  precTr-MP1 (suc p) Tg Th g h mtg mth m1g m1th dg dh mg mh =
    mkSigma ivc
      (mkSigma (ovP-verdict (suc p) Th mth m1th g h dh mg mh ivc) cns)
    where
      ivc : EvConstN (P.ivP (suc p) Th)
      ivc =
        precTr-ivP-mp (suc p) Th g h mth
          (mp1-mpT (suc (suc (suc p))) Th mth m1th) dh mg mh

      cns : (c : Nat) (lc : LeN (suc c) (suc (suc p))) (v : Nat)
          -> MP1T (suc p) (precCont (suc p) Tg Th c lc v)
      cns zero lc v =
        atNum-MP1 (suc p) Tg Th g h mtg mth m1g m1th dg dh mg mh v
      cns (suc i) lc v =
        precTr-MP1 p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
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

precTr-at-mp1 : (n m : Nat) (e : Eq n (suc m))
                (Tg : Tr m) (Th : Tr (suc (suc m)))
              -> MP1T (suc m) (precTr m Tg Th)
              -> MP1T n (precTr-at n m e Tg Th)
precTr-at-mp1 n m refl Tg Th r = r

------------------------------------------------------------------------
-- THE THEOREM: MP1 FOR THE TRACE OF EVERY PR TERM
------------------------------------------------------------------------

mutual
  traceOf-MP1np : (q : PR) (n : Nat) (wf : Wf q n) -> MP1T n (traceOf q n wf)
  traceOf-MP1np zerf     n wf = zerfTr-mp1 n
  traceOf-MP1np (proj i) n wf = projTr-mp1 n i wf
  ----------------------------------------------------------------------
  -- succ = succ o proj 0
  ----------------------------------------------------------------------
  traceOf-MP1np succ n wf =
    compTr-MP1T (suc zero) succTr (evalF succ) succTr-den
      (evalF-MonoF succ (suc zero)) succTr-mono succTr-mp1 n Ths mTh m1Th
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
  traceOf-MP1np (comp g hs) n wf =
    compTr-MP1T (length hs) Tg (evalF g) (snd okg) (evalF-MonoF g (length hs))
      (fst okg) (traceOf-MP1np g (length hs) (fst wf))
      n (traceList hs n (snd wf))
      (\ i -> fst (traceList-ok hs n (snd wf) i))
      (\ i -> traceList-MP1np hs n (snd wf) i)
    where
      Tg : Tr (length hs)
      Tg = traceOf g (length hs) (fst wf)

      okg : Pair (MonoTr (length hs) Tg) (Den (length hs) Tg (evalF g))
      okg = traceOf-ok g (length hs) (fst wf)
  ----------------------------------------------------------------------
  -- primitive recursion
  ----------------------------------------------------------------------
  traceOf-MP1np (prec g h) n wf =
    precTr-at-mp1 n m e Tg Th
      (precTr-MP1 m Tg Th (evalF g) (evalF h)
        (fst okg) (fst okh)
        (traceOf-MP1np g m wg)
        (traceOf-MP1np h (suc (suc m)) wh)
        (snd okg) (snd okh)
        (evalF-MonoF g m) (evalF-MonoF h (suc (suc m))))
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

  traceList-MP1np : (hs : List PR) (n : Nat) (aw : AllWf hs n) (i : Nat)
                  -> MP1T n (traceList hs n aw i)
  traceList-MP1np nil         n aw i       = zerfTr-mp1 n
  traceList-MP1np (cons q qs) n aw zero    = traceOf-MP1np q n (fst aw)
  traceList-MP1np (cons q qs) n aw (suc i) = traceList-MP1np qs n (snd aw) i
