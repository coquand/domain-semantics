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
--   * ERT.Dom.OrderStage          : Comp/Coherent/Sup/NotBot + the stratified
--                             order bundle (LeqC/leiC, OB, RANK).
--   * ERT.Dom.OrderComp      : structural Comp/Coherent/Sup lemmas.
--   * ERT.Dom.OrderBridge    : the re-founded core -- EvalFun (structural
--                             over leiC), LeCode/LeFunCode (structural,
--                             so they still unfold definitionally),
--                             applyEl, and the EvalFun<->OB.ev /
--                             LeCode<->LeqC bridges.
--   * ERT.Dom.OrderInterface : the order properties on the structural
--                             LeCode/EvalFun (refl/trans/Sup-*/Comp-down/
--                             LeCode-Comp/EvalFun-mon/-mon-arg/
--                             Coherent-EvalFun/Comp-value-EvalFun).
--   * ERT.Dom.OrderEval     : leFinEl/leFun + soundness, comp-EvalFun,
--                             EvalFun-append-eq.
--
-- 0 postulates -- across the whole family.
------------------------------------------------------------------------

module ERT.Dom.Order where

open import ERT.Dom.OrderStage          public
open import ERT.Dom.OrderComp      public
open import ERT.Dom.OrderStable    public
open import ERT.Dom.OrderBridge    public
open import ERT.Dom.OrderInterface public
open import ERT.Dom.OrderEval     public
