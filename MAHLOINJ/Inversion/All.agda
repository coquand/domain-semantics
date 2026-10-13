{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Inversion/All.agda
--
--   Hyp   InjHyp: Pi/Sigma-injectivity, U(f,g) not Pi/Sigma/Nat
--   Inv   inversion of typing for every term former (plan Lemma 18)
--   SR    subject reduction for weak-head beta/pi/iota
------------------------------------------------------------------------

module MAHLOINJ.Inversion.All where

import MAHLOINJ.Inversion.Hyp
import MAHLOINJ.Inversion.Inv
import MAHLOINJ.Inversion.SR
