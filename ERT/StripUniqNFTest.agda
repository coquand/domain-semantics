{-# OPTIONS --without-K --exact-split #-}

-- The counterexample to the proof of Lemma 4.17 (Gap417), now settled
-- by the normalisation-free Lemma 4.18.
module ERT.StripUniqNFTest where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta using (isType-U)
open import ERT.Gap417
open import ERT.StripUniqNF

gap-closed : ConvTm empty u0 u1 U2
gap-closed = term-uniq-conv-NF du0 du1 refl (conv-Ty-refl (isType-U wf0))
