{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Final.agda  --  the P3 deliverable
--
-- The hypotheses of MAHLOINJ/Inversion (record InjHyp) are discharged:
--   Pi-inj, Sig-inj   by the logical relation and its fundamental lemma
--                     (MAHLOINJ/Valid, MAHLOINJ/Adq), at the identity
--                     substitution and the bottom environment;
--   U-Pi, U-Sig, U-Nat  by the finite-element model alone
--                     (MAHLOINJ/Model/NoConf).
-- Inversion of typing and subject reduction then hold unconditionally.
-- No postulates, no pragmas.
------------------------------------------------------------------------

module MAHLOINJ.Final where

open import MAHLO.Basic
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Inversion.Hyp
import MAHLOINJ.Adq.Inj as I
import MAHLOINJ.Model.NoConf as N
import MAHLOINJ.Inversion.Inv
import MAHLOINJ.Inversion.SR

injHyp : InjHyp
injHyp = record
  { Pi-inj  = I.Pi-inj
  ; Sig-inj = I.Sig-inj
  ; U-Pi    = N.U-Pi
  ; U-Sig   = N.U-Sig
  ; U-Nat   = N.U-Nat }

open I public using (Pi-inj ; Sig-inj)
open N public using (U-Pi ; U-Sig ; U-Nat)

-- inversion of typing for every term former, and subject reduction
module Inversion = MAHLOINJ.Inversion.Inv injHyp
module SubjectReduction = MAHLOINJ.Inversion.SR injHyp

open SubjectReduction public using (sr)
