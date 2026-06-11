{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperOrder.agda  (MIN/ — Pi + U fragment)
--
-- RE-FOUNDED.  Formerly an 1215-line block with 11
-- non-structural recursions (the EvalFun <-> order cycle).  The order
-- is now built by structural recursion on a stage index in the
-- MIN/LeqStage* family and collapsed by stability; PaperOrder is a thin
-- re-export of that family, name-for-name compatible with the old
-- public interface.
--
--   * CAST.LeqStage          : Comp/Coherent/Sup/NotBot + the stratified
--                             order bundle (LeqC/leiC, OB, RANK).
--   * CAST.LeqStageComp      : structural Comp/Coherent/Sup lemmas.
--   * CAST.LeqStageBridge    : the re-founded core -- EvalFun (structural
--                             over leiC), LeCode/LeFunCode (structural,
--                             so they still unfold definitionally),
--                             applyEl, and the EvalFun<->OB.ev /
--                             LeCode<->LeqC bridges.
--   * CAST.LeqStageInterface : the order properties on the structural
--                             LeCode/EvalFun (refl/trans/Sup-*/Comp-down/
--                             LeCode-Comp/EvalFun-mon/-mon-arg/
--                             Coherent-EvalFun/Comp-value-EvalFun).
--   * CAST.LeqStageEval2     : leFinEl/leFun + soundness, comp-EvalFun,
--                             EvalFun-append-eq.
--
-- 0 postulates -- across the whole family.
------------------------------------------------------------------------

module CAST.PaperOrder where

open import CAST.LeqStage          public
open import CAST.LeqStageComp      public
open import CAST.LeqStageStable    public
open import CAST.LeqStageBridge    public
open import CAST.LeqStageInterface public
open import CAST.LeqStageEval2     public
