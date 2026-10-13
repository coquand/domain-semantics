{-# OPTIONS --without-K --exact-split --safe #-}
module MAHLO.TypingTest where

open import MAHLO.Syntax
open import MAHLO.Typing

-- OpF = Pi A:V. (A -> V) -> V  is a closed type
opF-type : IsType empty OpF
opF-type = isty-Pi (isty-V wf-empty)
  (isty-Pi (isty-Pi (isty-el (ty-var w1)) (isty-V w2)) (isty-V w3))
  where
    w1 = wf-extend (isty-V wf-empty)
    w2 = wf-extend (isty-el (ty-var w1))
    w3 = wf-extend (isty-Pi (isty-el (ty-var w1)) (isty-V w2))

-- \x:Nat. S x : Nat -> Nat
sucFun : HasType empty (Lam Nat (Suc x0)) (Arr Nat Nat)
sucFun = ty-Lam nT (isty-el (ty-Nat-V w)) (ty-Suc (ty-var w))
  where
    nT = isty-el (ty-Nat-V wf-empty)
    w  = wf-extend nT
