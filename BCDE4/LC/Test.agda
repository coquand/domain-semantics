{-# OPTIONS --without-K --exact-split #-}

-- The loop-checking decision procedure computes (closed tests by refl).
module BCDE4.LC.Test where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Decide using (decValid)

data B : Set where
  yes no : B

isYes : {X Y : Set} -> Either X Y -> B
isYes (inl _) = yes
isYes (inr _) = no

a b : LExpr
a = lvar zero
b = lvar (suc zero)

-- α ≤ β  (i.e. α ⊔ β = β)
Th1 : LCtx
Th1 = lcons (ceq (lsup a b) b) lnil

-- α ≤ β ⊢ α⁺ ⊔ β⁺ = β⁺
t1 : Eq (isYes (decValid Th1 (lsup (lnext a) (lnext b)) (lnext b))) yes
t1 = refl

-- α ≤ β ⊬ α = β
t2 : Eq (isYes (decValid Th1 a b)) no
t2 = refl

-- ⊬ α = β
t3 : Eq (isYes (decValid lnil a b)) no
t3 = refl

-- α ≤ β, β ≤ α ⊢ α = β
t4 : Eq (isYes (decValid (lcons (ceq (lsup b a) a) Th1) a b)) yes
t4 = refl

-- α⁺ ≤ α (a loop) ⊢ α⁺⁺⁺ ⊔ α = α   (loop certificate: all of α is derivable)
t5 : Eq (isYes (decValid (lcons (ceq (lsup (lnext a) a) a) lnil) (lsup (lnext (lnext (lnext a))) a) a)) yes
t5 = refl
