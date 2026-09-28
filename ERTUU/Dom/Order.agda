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
--   * ERTUU.Dom.OrderStage          : Comp/Coherent/Sup/NotBot + the stratified
--                             order bundle (LeqC/leiC, OB, RANK).
--   * ERTUU.Dom.OrderComp      : structural Comp/Coherent/Sup lemmas.
--   * ERTUU.Dom.OrderBridge    : the re-founded core -- EvalFun (structural
--                             over leiC), LeCode/LeFunCode (structural,
--                             so they still unfold definitionally),
--                             applyEl, and the EvalFun<->OB.ev /
--                             LeCode<->LeqC bridges.
--   * ERTUU.Dom.OrderInterface : the order properties on the structural
--                             LeCode/EvalFun (refl/trans/Sup-*/Comp-down/
--                             LeCode-Comp/EvalFun-mon/-mon-arg/
--                             Coherent-EvalFun/Comp-value-EvalFun).
--   * ERTUU.Dom.OrderEval     : leFinEl/leFun + soundness, comp-EvalFun,
--                             EvalFun-append-eq.
--
-- 0 postulates -- across the whole family.
------------------------------------------------------------------------

module ERTUU.Dom.Order where

open import ERTUU.Dom.OrderStage          public
open import ERTUU.Dom.OrderComp      public
open import ERTUU.Dom.OrderStable    public
open import ERTUU.Dom.OrderBridge    public
open import ERTUU.Dom.OrderInterface public
open import ERTUU.Dom.OrderEval     public
