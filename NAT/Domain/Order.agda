{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperOrder.agda  (NAT/ — Pi + U fragment)
--
-- RE-FOUNDED.  Formerly an 1215-line block with 11
-- non-structural recursions (the EvalFun <-> order cycle).  The order
-- is now built by structural recursion on a stage index in the
-- NAT/LeqStage* family and collapsed by stability; PaperOrder is a thin
-- re-export of that family, name-for-name compatible with the old
-- public interface.
--
--   * NAT.Domain.OrderStage          : Comp/Coherent/Sup/NotBot + the stratified
--                             order bundle (LeqC/leiC, OB, RANK).
--   * NAT.Domain.OrderComp      : structural Comp/Coherent/Sup lemmas.
--   * NAT.Domain.OrderBridge    : the re-founded core -- EvalFun (structural
--                             over leiC), LeCode/LeFunCode (structural,
--                             so they still unfold definitionally),
--                             applyEl, and the EvalFun<->OB.ev /
--                             LeCode<->LeqC bridges.
--   * NAT.Domain.OrderInterface : the order properties on the structural
--                             LeCode/EvalFun (refl/trans/Sup-*/Comp-down/
--                             LeCode-Comp/EvalFun-mon/-mon-arg/
--                             Coherent-EvalFun/Comp-value-EvalFun).
--   * NAT.Domain.OrderEval     : leFinEl/leFun + soundness, comp-EvalFun,
--                             EvalFun-append-eq.
--
-- 0 postulates -- across the whole family.
------------------------------------------------------------------------

module NAT.Domain.Order where

open import NAT.Domain.OrderStage          public
open import NAT.Domain.OrderComp      public
open import NAT.Domain.OrderStable    public
open import NAT.Domain.OrderBridge    public
open import NAT.Domain.OrderInterface public
open import NAT.Domain.OrderEval     public
