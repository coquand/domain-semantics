{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperOrder.agda  (MIN/ — Pi + U fragment)
--
-- RE-FOUNDED, TERMINATING-FREE.  Formerly an 1215-line block with 11
-- termination-pragmas (the EvalFun <-> order cycle).  The order
-- is now built by structural recursion on a stage index in the
-- MIN/LeqStage* family and collapsed by stability; PaperOrder is a thin
-- re-export of that family, name-for-name compatible with the old
-- public interface.
--
--   * MIN.LeqStage          : Comp/Coherent/Sup/NotBot + the stratified
--                             order bundle (LeqC/leiC, OB, RANK).
--   * MIN.LeqStageComp      : structural Comp/Coherent/Sup lemmas.
--   * MIN.LeqStageBridge    : the re-founded core -- EvalFun (structural
--                             over leiC), LeCode/LeFunCode (structural,
--                             so they still unfold definitionally),
--                             applyEl, and the EvalFun<->OB.ev /
--                             LeCode<->LeqC bridges.
--   * MIN.LeqStageInterface : the order properties on the structural
--                             LeCode/EvalFun (refl/trans/Sup-*/Comp-down/
--                             LeCode-Comp/EvalFun-mon/-mon-arg/
--                             Coherent-EvalFun/Comp-value-EvalFun).
--   * MIN.LeqStageEval2     : leFinEl/leFun + soundness, comp-EvalFun,
--                             EvalFun-append-eq.
--
-- 0 TERMINATING, 0 postulates -- across the whole family.
------------------------------------------------------------------------

module MIN.PaperOrder where

open import MIN.LeqStage          public
open import MIN.LeqStageComp      public
open import MIN.LeqStageStable    public
open import MIN.LeqStageBridge    public
open import MIN.LeqStageInterface public
open import MIN.LeqStageEval2     public
