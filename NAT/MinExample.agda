{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- MinExample.agda  —  the recursive  min : Nat → Nat → Nat  encoded with
-- Y (general recursion) and the DEPENDENT caseNat eliminator.
--
--   min 0     y     = 0
--   min (S x) 0     = 0
--   min (S x) (S y) = S (min x y)
--
-- min's motive is constant (result is always Nat), so dependency is not
-- needed here — but we deliberately use the dependent `ty-Case-dep` with
-- the constant motive  C := NatT  to exercise it.  Every dependent
-- substitution collapses:  subst1 NatT M = NatT  and  subSucC NatT = NatT.
------------------------------------------------------------------------

module NAT.MinExample where

open import NAT.Domain.Basic using ( Nat ; zero ; suc )
open import NAT.Syntax.Raw using
  ( Expr ; Var ; Lam ; App ; Pi ; NatT ; Zero ; Suc ; Case ; Y
  ; Fin ; fzero ; fsuc )
open import NAT.Syntax.Typing using
  ( Ctx ; empty ; extend ; WfCtx ; wf-empty ; wf-extend ; HasType
  ; ty-var ; ty-NatT ; ty-Zero ; ty-Suc ; ty-Pi ; ty-Lam ; ty-App
  ; ty-Y ; ty-Case-dep )

------------------------------------------------------------------------
-- Types and de Bruijn variables
------------------------------------------------------------------------

-- Nat → Nat  and  Nat → Nat → Nat   (closed, so weakening is the identity)
NN : {n : Nat} -> Expr n
NN = Pi NatT NatT

NNN : {n : Nat} -> Expr n
NNN = Pi NatT (Pi NatT NatT)

-- variables (innermost binder = index 0)
v0 : {n : Nat} -> Expr (suc n)
v0 = Var fzero
v1 : {n : Nat} -> Expr (suc (suc n))
v1 = Var (fsuc fzero)
v4 : {n : Nat} -> Expr (suc (suc (suc (suc (suc n)))))
v4 = Var (fsuc (fsuc (fsuc (fsuc fzero))))

------------------------------------------------------------------------
-- The term
--
--   min = Y (λ self. λ x. λ y.
--             case x of
--               0      → 0                                  -- min 0 y = 0
--               S x'   → case y of
--                          0    → 0                          -- min (S x') 0 = 0
--                          S y' → S (self x' y'))            -- = S (min x' y')
------------------------------------------------------------------------

-- context depth: [self, x, y, x', y']  (Expr 5)
leaf : Expr 5
leaf = Suc (App (App v4 v1) v0)          -- S (self x' y')

innerCase : Expr 4                        -- case y of 0 → 0 ; S y' → S (self x' y')
innerCase = Case v1 Zero (Lam NatT leaf)

outerCase : Expr 3                        -- case x of 0 → 0 ; S x' → innerCase
outerCase = Case v1 Zero (Lam NatT innerCase)

minFun : Expr 0                           -- λ self. λ x. λ y. outerCase
minFun = Lam NNN (Lam NatT (Lam NatT outerCase))

min : Expr 0
min = Y minFun

------------------------------------------------------------------------
-- Well-typedness :  ⊢ min : Nat → Nat → Nat
------------------------------------------------------------------------

-- the five contexts and their well-formedness witnesses
G1 : Ctx 1
G1 = extend empty NNN                     -- self : Nat→Nat→Nat
G2 : Ctx 2
G2 = extend G1 NatT                       -- x
G3 : Ctx 3
G3 = extend G2 NatT                       -- y
G4 : Ctx 4
G4 = extend G3 NatT                       -- x'
G5 : Ctx 5
G5 = extend G4 NatT                       -- y'

wf0 : WfCtx empty
wf0 = wf-empty
wf1 : WfCtx G1
wf1 = wf-extend (ty-Pi (ty-NatT wf0) (ty-Pi (ty-NatT (wf-extend (ty-NatT wf0)))
                                            (ty-NatT (wf-extend (ty-NatT (wf-extend (ty-NatT wf0)))))))
wf2 : WfCtx G2
wf2 = wf-extend (ty-NatT wf1)
wf3 : WfCtx G3
wf3 = wf-extend (ty-NatT wf2)
wf4 : WfCtx G4
wf4 = wf-extend (ty-NatT wf3)
wf5 : WfCtx G5
wf5 = wf-extend (ty-NatT wf4)

-- the leaf:  S (self x' y') : Nat
d-self-x' : HasType G5 (App v4 v1) (Pi NatT NatT)
d-self-x' =
  ty-App (ty-NatT wf5) (ty-Pi (ty-NatT (wf-extend (ty-NatT wf5)))
                              (ty-NatT (wf-extend (ty-NatT (wf-extend (ty-NatT wf5))))))
    (ty-var wf5) (ty-var wf5)

d-leaf : HasType G5 leaf NatT
d-leaf =
  ty-Suc (ty-App (ty-NatT wf5) (ty-NatT (wf-extend (ty-NatT wf5)))
            d-self-x' (ty-var wf5))

-- inner case (on y) : Nat   via dependent Case, constant motive C = NatT
d-innerCase : HasType G4 innerCase NatT
d-innerCase =
  ty-Case-dep (ty-NatT wf5) (ty-var wf4) (ty-Zero wf4)
    (ty-Lam (ty-NatT wf4) (ty-NatT wf5) d-leaf)

-- outer case (on x) : Nat
d-outerCase : HasType G3 outerCase NatT
d-outerCase =
  ty-Case-dep (ty-NatT wf4) (ty-var wf3) (ty-Zero wf3)
    (ty-Lam (ty-NatT wf3) (ty-NatT wf4) d-innerCase)

-- the body  λ self. λ x. λ y. outerCase  :  NNN → NNN
d-minFun : HasType empty minFun (Pi NNN NNN)
d-minFun =
  ty-Lam
    (ty-Pi (ty-NatT wf0) (ty-Pi (ty-NatT (wf-extend (ty-NatT wf0)))
                                (ty-NatT (wf-extend (ty-NatT (wf-extend (ty-NatT wf0)))))))
    (ty-Pi (ty-NatT wf1) (ty-Pi (ty-NatT wf2) (ty-NatT wf3)))
    (ty-Lam (ty-NatT wf1)
       (ty-Pi (ty-NatT wf2) (ty-NatT wf3))
       (ty-Lam (ty-NatT wf2) (ty-NatT wf3) d-outerCase))

-- finally  ⊢ min : Nat → Nat → Nat
d-min : HasType empty min NNN
d-min = ty-Y (ty-Pi (ty-NatT wf0) (ty-Pi (ty-NatT (wf-extend (ty-NatT wf0)))
                                         (ty-NatT (wf-extend (ty-NatT (wf-extend (ty-NatT wf0)))))))
             d-minFun
