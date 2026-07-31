{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrMP1Red
--
-- MP1 REDUCES TO ITS INDEX HALF.
--
--     traceOf-mp1 : IvAll n (traceOf q n wf) -> MP1T n (traceOf q n wf)
--
-- `MP1T` asks for two things at every node of the trace: that the
-- SEQUENTIALITY INDEX `iv` is eventually constant, and that the VALUE
-- sequence `ov` falls into one of min1.pdf's three cases.  The second is
-- not an independent obligation:
--
--   * `TrVerdict.ov-bot` -- `ov k` is the denoted function at the walk's
--     OWN levels after `k` steps;
--   * so past the threshold of `EvConstN iv` the value sequence is the
--     function along `x_I := S(x_I)`, everything else frozen;
--   * and `Property.UO` -- Proposition 1, proved for every PR term in
--     `Prop1` -- is exactly the statement about that sequence
--     (`TrVerdict.verdict-of`);
--   * `TrUOfrz.uofrz-PR` supplies it for the frozen functions too, which
--     is what the continuations denote.
--
-- So nothing about `compTr` or `precTr` is needed for the value half --
-- and what is left OPEN in MP1 is exactly `IvAll`: the index clause, for
-- the composite and the recursion walks.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrMP1Red where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; evalF)
open import OBSTINATION.Prop1 using (Wf)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrDen using (Den ; ins)
open import OBSTINATION.TrSat using (MonoTr)
open import OBSTINATION.TrCompDen using (monoTr-cont)
open import OBSTINATION.TrMP1 using (MP1T ; IvAll)
open import OBSTINATION.TrVerdict using (verdict-of)
open import OBSTINATION.TrUOfrz using (UOfrz ; uofrz-PR)
open import OBSTINATION.TrTerm using (traceOf ; traceOf-ok ; traceOf-den)

------------------------------------------------------------------------
-- THE REDUCTION, FOR AN ARBITRARY TRACE
------------------------------------------------------------------------

mp1T-from-iv : (a : Nat) (T : Tr a) (F : FTup -> FEl)
             -> Den a T F -> MonoTr a T -> UOfrz a F -> IvAll a T -> MP1T a T
mp1T-from-iv a       (stop v)              F dn mt uf ia = tt
mp1T-from-iv (suc a) (node iv ivr ov cont) F dn mt uf ia =
  mkSigma (fst ia)
    (mkSigma (verdict-of a iv ivr ov cont F dn mt (fst uf) (fst ia))
      (\ c lc v ->
         mp1T-from-iv a (cont c lc v) (\ Y -> F (ins c (fcpl v) Y))
           (snd dn c lc v)
           (monoTr-cont a (node iv ivr ov cont) mt c lc v)
           (snd uf c lc v) (snd ia c lc v)))

------------------------------------------------------------------------
-- ... AND FOR THE TRACE OF A PR TERM
------------------------------------------------------------------------

traceOf-mp1 : (q : PR) (n : Nat) (wf : Wf q n)
            -> IvAll n (traceOf q n wf) -> MP1T n (traceOf q n wf)
traceOf-mp1 q n wf ia =
  mp1T-from-iv n (traceOf q n wf) (evalF q)
    (traceOf-den q n wf) (fst (traceOf-ok q n wf)) (uofrz-PR n q wf) ia
