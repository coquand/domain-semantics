{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/Order.agda        (L1 -- the public order interface)
--
-- One import for the whole finite-element Scott domain of
-- henderson.pdf section III:
--
--   Sup / Comp / Coherent            (OrderStage, OrderComp)
--   EvalFun / applyEl / LeCode       (OrderBridge, structural)
--   refl / trans / Sup-lub / ...     (OrderInterface)
--
-- The stage index is INTERNAL: nothing re-exported here mentions it.
------------------------------------------------------------------------

module LAZY.Domain.Order where

open import LAZY.Domain.OrderStage     public
  using ( Sup ; supAt
        ; Comp ; CompFun ; CompStepFun ; CompStepStep
        ; Coherent ; CoherentFun ; CoherentWith ; CFcons ; mkCF )
open import LAZY.Domain.OrderComp      public
open import LAZY.Domain.OrderBridge    public
  using ( EvalFun ; EvalFun-step ; applyEl ; LeCode ; LeFunCode )
open import LAZY.Domain.OrderInterface public
