{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOVE/Typing.agda
--
-- A verbatim copy of the frozen MAHLO/Typing.agda, over MAHLOVE/Syntax,
-- EXTENDED by an elimination rule for the Mahlo universe V (the
-- "closed" Mahlo universe of Palmgren): ty-VElim, its computation
-- rules conv-VElim-Nat/Pi/Sigma/U and the congruence conv-VElim.
-- All new rules are marked NEW.  MAHLOVE/Palmgren.agda derives a closed
-- term of  Pi X:V. X  from them.
--
-- Original header:
--
-- Declarative typing and judgemental equality of the annotated Russell
-- Mahlo theory, mahlo-plan.tex Sec. 1.2:
--   * subsumption  U_{f,g} <= V  (terms and equalities),
--   * closure of every universe (V or U_{f,g}) under Pi, Sigma, Nat,
--   * U_{f,g} : V, closure under fhat/ghat with family  \x:A.B,
--   * delta-equations, in V ONLY,
--   * rule (R'): equality in U_{f,g} is the restriction of that in V,
--   * Pi with beta and eta (as funext), Sigma with beta and surjective
--     pairing (as pair extensionality), Nat with rec.
--
-- Judgements:  WfCtx G,  IsType G A,  HasType G t A,  TyEq G A B,
-- ConvTm G t u A.  V has no type; it is only a type (isty-V).
--
-- Families are Lam-terms:  PiB A B = Pi A (Lam A B)  etc. (Syntax).
-- Following MIN, rules carry extra "grey" premises (typings of
-- components) so that inductions on derivations can recurse on them.
-- Derivable rules omitted on purpose: congruence for Lam (funext +
-- beta) and for Pair (pair extensionality + projection beta).
------------------------------------------------------------------------

module MAHLOVE.Typing where

open import MAHLOVE.Basic using (Eq)
open import MAHLOVE.Syntax

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data Ctx : Num -> Set where
  empty  : Ctx zero
  extend : {n : Num} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Num} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

------------------------------------------------------------------------
-- Universes:  u is V or some U(f,g)
------------------------------------------------------------------------

data Univ {n : Num} (u : Expr n) : Set where
  univ-V : Eq u V -> Univ u
  univ-U : (f g : Expr n) -> Eq u (Ucode f g) -> Univ u

------------------------------------------------------------------------
-- NEW: contexts and types of the cases of V-elimination
--
-- For a motive C (scope suc n, the bound variable ranges over V):
--   Pi case    A : V, B : A -> V, iA : C[A], iB : Pi y:A. C[B y]
--              |- cP : C[Pi A (\y. B y)]
--   Sigma case the same, with Sigma
--   U case     f : OpF, g : OpG f,
--              if : Pi a:V. Pi b:a->V. C[f a b],
--              ig : Pi a:V. Pi b:a->V. Pi c:f a b. C[g a b c]
--              |- cU : C[U(f,g)]
------------------------------------------------------------------------

ctxPS : {n : Num} -> Ctx n -> Expr (suc n) -> Ctx (suc (suc (suc (suc n))))
ctxPS G C = extend (extend (extend (extend G V) (Arr x0 V)) (inst w2 C x1))
                   (PiB x2 (inst w4 C (App x2 x0)))

resPi : {n : Num} -> Expr (suc n) -> Expr (suc (suc (suc (suc n))))
resPi C = inst w4 C (PiB x3 (App x3 x0))

resSig : {n : Num} -> Expr (suc n) -> Expr (suc (suc (suc (suc n))))
resSig C = inst w4 C (SigmaB x3 (App x3 x0))

IHfT : {n : Num} -> Expr (suc n) -> Expr (suc (suc n))
IHfT C = PiB V (PiB (Arr x0 V) (inst w4 C (App (App x3 x1) x0)))

IHgT : {n : Num} -> Expr (suc n) -> Expr (suc (suc (suc n)))
IHgT C = PiB V (PiB (Arr x0 V) (PiB (App (App x4 x1) x0)
           (inst w6 C (App (App (App x4 x2) x1) x0))))

ctxU : {n : Num} -> Ctx n -> Expr (suc n) -> Ctx (suc (suc (suc (suc n))))
ctxU G C = extend (extend (extend (extend G OpF) (OpG x0)) (IHfT C)) (IHgT C)

resU : {n : Num} -> Expr (suc n) -> Expr (suc (suc (suc (suc n))))
resU C = inst w4 C (Ucode x3 x2)

------------------------------------------------------------------------
-- Judgements (mutual)
------------------------------------------------------------------------

data WfCtx   : {n : Num} -> Ctx n -> Set
data IsType  : {n : Num} -> Ctx n -> Expr n -> Set
data HasType : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set
data TyEq    : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

------------------------------------------------------------------------
-- WfCtx
------------------------------------------------------------------------

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Num} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- IsType
------------------------------------------------------------------------

data IsType where

  isty-V : {n : Num} {G : Ctx n}
    -> WfCtx G
    -> IsType G V

  -- an element of a universe is a type (A : U_{f,g} gives A : V)
  isty-el : {n : Num} {G : Ctx n} {A : Expr n}
    -> HasType G A V
    -> IsType G A

  isty-Pi : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (PiB A B)

  isty-Sigma : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType G (SigmaB A B)

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

data HasType where

  ty-var : {n : Num} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  ty-conv : {n : Num} {G : Ctx n} {t A B : Expr n}
    -> HasType G t A
    -> TyEq G A B
    -> HasType G t B

  -- subsumption  U_{f,g} <= V
  ty-sub : {n : Num} {G : Ctx n} {A f g : Expr n}
    -> HasType G A (Ucode f g)
    -> HasType G A V

  -- closure of a universe u under Pi, Sigma, Nat
  ty-Pi : {n : Num} {G : Ctx n} {u A : Expr n} {B : Expr (suc n)}
    -> Univ u
    -> HasType G A u
    -> HasType (extend G A) B (wkExpr u)
    -> HasType G (PiB A B) u

  ty-Sigma : {n : Num} {G : Ctx n} {u A : Expr n} {B : Expr (suc n)}
    -> Univ u
    -> HasType G A u
    -> HasType (extend G A) B (wkExpr u)
    -> HasType G (SigmaB A B) u

  ty-Nat-V : {n : Num} {G : Ctx n}
    -> WfCtx G
    -> HasType G Nat V

  ty-Nat-U : {n : Num} {G : Ctx n} {f g : Expr n}
    -> HasType G (Ucode f g) V
    -> HasType G Nat (Ucode f g)

  -- the subuniverse of an operator (f,g)
  ty-Ucode : {n : Num} {G : Ctx n} {f g : Expr n}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> HasType G (Ucode f g) V

  ty-Fhat : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> HasType G (Fhat f g A (Lam A B)) (Ucode f g)

  ty-Ghat : {n : Num} {G : Ctx n} {f g A c : Expr n} {B : Expr (suc n)}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> HasType G c (Fhat f g A (Lam A B))
    -> HasType G (Ghat f g A (Lam A B) c) (Ucode f g)

  -- Pi
  ty-Lam : {n : Num} {G : Ctx n} {A : Expr n} {B t : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) t B
    -> HasType G (Lam A t) (PiB A B)

  ty-App : {n : Num} {G : Ctx n} {A t a : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t (PiB A B)
    -> HasType G a A
    -> HasType G (App t a) (subst1 B a)

  -- Sigma
  ty-Pair : {n : Num} {G : Ctx n} {A t u : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t A
    -> HasType G u (subst1 B t)
    -> HasType G (Pair t u) (SigmaB A B)

  ty-Fst : {n : Num} {G : Ctx n} {A t : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t (SigmaB A B)
    -> HasType G (Fst t) A

  ty-Snd : {n : Num} {G : Ctx n} {A t : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t (SigmaB A B)
    -> HasType G (Snd t) (subst1 B (Fst t))

  -- Nat
  ty-Zero : {n : Num} {G : Ctx n}
    -> WfCtx G
    -> HasType G Zero Nat

  ty-Suc : {n : Num} {G : Ctx n} {t : Expr n}
    -> HasType G t Nat
    -> HasType G (Suc t) Nat

  ty-Rec : {n : Num} {G : Ctx n} {z s k : Expr n} {C : Expr (suc n)}
    -> IsType (extend G Nat) C
    -> HasType G z (subst1 C Zero)
    -> HasType G s (RecStep C)
    -> HasType G k Nat
    -> HasType G (Rec (Lam Nat C) z s k) (subst1 C k)

  -- NEW: elimination of V
  ty-VElim : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN t : Expr n}
             {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> HasType G t V
    -> HasType G (VElim C cN cP cS cU t) (subst1 C t)

------------------------------------------------------------------------
-- TyEq
------------------------------------------------------------------------

data TyEq where

  tyeq-refl : {n : Num} {G : Ctx n} {A : Expr n}
    -> IsType G A
    -> TyEq G A A

  tyeq-sym : {n : Num} {G : Ctx n} {A B : Expr n}
    -> TyEq G A B
    -> TyEq G B A

  tyeq-trans : {n : Num} {G : Ctx n} {A B C : Expr n}
    -> TyEq G A B
    -> TyEq G B C
    -> TyEq G A C

  -- equal elements of V are equal types
  tyeq-el : {n : Num} {G : Ctx n} {A B : Expr n}
    -> ConvTm G A B V
    -> TyEq G A B

  tyeq-Pi : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType (extend G A) B'
    -> TyEq G A A'
    -> TyEq (extend G A) B B'
    -> TyEq G (PiB A B) (PiB A' B')

  tyeq-Sigma : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> IsType (extend G A) B'
    -> TyEq G A A'
    -> TyEq (extend G A) B B'
    -> TyEq G (SigmaB A B) (SigmaB A' B')

------------------------------------------------------------------------
-- ConvTm
------------------------------------------------------------------------

data ConvTm where

  -- equivalence and type conversion
  conv-refl : {n : Num} {G : Ctx n} {t A : Expr n}
    -> HasType G t A
    -> ConvTm G t t A

  conv-sym : {n : Num} {G : Ctx n} {t u A : Expr n}
    -> ConvTm G t u A
    -> ConvTm G u t A

  conv-trans : {n : Num} {G : Ctx n} {t u v A : Expr n}
    -> ConvTm G t u A
    -> ConvTm G u v A
    -> ConvTm G t v A

  conv-conv : {n : Num} {G : Ctx n} {t u A B : Expr n}
    -> ConvTm G t u A
    -> TyEq G A B
    -> ConvTm G t u B

  -- subsumption for equality, and its converse (R')
  conv-sub : {n : Num} {G : Ctx n} {A B f g : Expr n}
    -> ConvTm G A B (Ucode f g)
    -> ConvTm G A B V

  conv-R' : {n : Num} {G : Ctx n} {A B f g : Expr n}
    -> HasType G A (Ucode f g)
    -> HasType G B (Ucode f g)
    -> ConvTm G A B V
    -> ConvTm G A B (Ucode f g)

  -- delta, in V only
  conv-delta-f : {n : Num} {G : Ctx n} {f g A : Expr n} {B : Expr (suc n)}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> ConvTm G (Fhat f g A (Lam A B)) (App (App f A) (Lam A B)) V

  conv-delta-g : {n : Num} {G : Ctx n} {f g A c : Expr n} {B : Expr (suc n)}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> HasType G c (Fhat f g A (Lam A B))
    -> ConvTm G (Ghat f g A (Lam A B) c) (App (App (App g A) (Lam A B)) c) V

  -- Pi: beta, eta (funext)
  conv-beta : {n : Num} {G : Ctx n} {A a : Expr n} {B t : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType (extend G A) t B
    -> HasType G a A
    -> ConvTm G (App (Lam A t) a) (subst1 t a) (subst1 B a)

  conv-funext : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t (PiB A B)
    -> HasType G t' (PiB A B)
    -> ConvTm (extend G A) (App (wkExpr t) x0) (App (wkExpr t') x0) B
    -> ConvTm G t t' (PiB A B)

  -- Sigma: beta, surjective pairing (pair extensionality)
  conv-fst-beta : {n : Num} {G : Ctx n} {A t u : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t A
    -> HasType G u (subst1 B t)
    -> ConvTm G (Fst (Pair t u)) t A

  conv-snd-beta : {n : Num} {G : Ctx n} {A t u : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t A
    -> HasType G u (subst1 B t)
    -> ConvTm G (Snd (Pair t u)) u (subst1 B t)

  conv-pairext : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> HasType G t (SigmaB A B)
    -> HasType G t' (SigmaB A B)
    -> ConvTm G (Fst t) (Fst t') A
    -> ConvTm G (Snd t) (Snd t') (subst1 B (Fst t))
    -> ConvTm G t t' (SigmaB A B)

  -- Nat: iota
  conv-rec-zero : {n : Num} {G : Ctx n} {z s : Expr n} {C : Expr (suc n)}
    -> IsType (extend G Nat) C
    -> HasType G z (subst1 C Zero)
    -> HasType G s (RecStep C)
    -> ConvTm G (Rec (Lam Nat C) z s Zero) z (subst1 C Zero)

  conv-rec-suc : {n : Num} {G : Ctx n} {z s k : Expr n} {C : Expr (suc n)}
    -> IsType (extend G Nat) C
    -> HasType G z (subst1 C Zero)
    -> HasType G s (RecStep C)
    -> HasType G k Nat
    -> ConvTm G (Rec (Lam Nat C) z s (Suc k))
                (App (App s k) (Rec (Lam Nat C) z s k)) (subst1 C (Suc k))

  -- congruences
  conv-App : {n : Num} {G : Ctx n} {A t t' a a' : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm G t t' (PiB A B)
    -> ConvTm G a a' A
    -> ConvTm G (App t a) (App t' a') (subst1 B a)

  conv-Fst : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm G t t' (SigmaB A B)
    -> ConvTm G (Fst t) (Fst t') A

  conv-Snd : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)}
    -> IsType G A
    -> IsType (extend G A) B
    -> ConvTm G t t' (SigmaB A B)
    -> ConvTm G (Snd t) (Snd t') (subst1 B (Fst t))

  conv-Pi : {n : Num} {G : Ctx n} {u A A' : Expr n} {B B' : Expr (suc n)}
    -> Univ u
    -> HasType G A u
    -> HasType (extend G A) B (wkExpr u)
    -> HasType (extend G A) B' (wkExpr u)
    -> ConvTm G A A' u
    -> ConvTm (extend G A) B B' (wkExpr u)
    -> ConvTm G (PiB A B) (PiB A' B') u

  conv-Sigma : {n : Num} {G : Ctx n} {u A A' : Expr n} {B B' : Expr (suc n)}
    -> Univ u
    -> HasType G A u
    -> HasType (extend G A) B (wkExpr u)
    -> HasType (extend G A) B' (wkExpr u)
    -> ConvTm G A A' u
    -> ConvTm (extend G A) B B' (wkExpr u)
    -> ConvTm G (SigmaB A B) (SigmaB A' B') u

  conv-Suc : {n : Num} {G : Ctx n} {t t' : Expr n}
    -> ConvTm G t t' Nat
    -> ConvTm G (Suc t) (Suc t') Nat

  conv-Rec : {n : Num} {G : Ctx n} {z z' s s' k k' : Expr n} {C C' : Expr (suc n)}
    -> IsType (extend G Nat) C
    -> IsType (extend G Nat) C'
    -> TyEq (extend G Nat) C C'
    -> ConvTm G z z' (subst1 C Zero)
    -> ConvTm G s s' (RecStep C)
    -> ConvTm G k k' Nat
    -> ConvTm G (Rec (Lam Nat C) z s k) (Rec (Lam Nat C') z' s' k') (subst1 C k)

  conv-Ucode : {n : Num} {G : Ctx n} {f f' g g' : Expr n}
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> ConvTm G f f' OpF
    -> ConvTm G g g' (OpG f)
    -> ConvTm G (Ucode f g) (Ucode f' g') V

  conv-Fhat : {n : Num} {G : Ctx n} {f f' g g' A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G f f' OpF
    -> ConvTm G g g' (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> HasType (extend G A) B' (wkExpr (Ucode f g))
    -> ConvTm G A A' (Ucode f g)
    -> ConvTm (extend G A) B B' (wkExpr (Ucode f g))
    -> ConvTm G (Fhat f g A (Lam A B)) (Fhat f' g' A' (Lam A' B')) (Ucode f g)

  conv-Ghat : {n : Num} {G : Ctx n} {f f' g g' A A' c c' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G f f' OpF
    -> ConvTm G g g' (OpG f)
    -> HasType G A (Ucode f g)
    -> HasType (extend G A) B (wkExpr (Ucode f g))
    -> HasType (extend G A) B' (wkExpr (Ucode f g))
    -> ConvTm G A A' (Ucode f g)
    -> ConvTm (extend G A) B B' (wkExpr (Ucode f g))
    -> ConvTm G c c' (Fhat f g A (Lam A B))
    -> ConvTm G (Ghat f g A (Lam A B) c) (Ghat f' g' A' (Lam A' B') c') (Ucode f g)

  -- NEW: computation rules of V-elimination
  conv-VElim-Nat : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN : Expr n}
                   {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> ConvTm G (VElim C cN cP cS cU Nat) cN (subst1 C Nat)

  conv-VElim-Pi : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN A : Expr n}
                  {B : Expr (suc n)} {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> HasType G A V
    -> HasType (extend G A) B V
    -> ConvTm G (VElim C cN cP cS cU (PiB A B))
                (substExpr (sub4 A (Lam A B) (VElim C cN cP cS cU A)
                                 (Lam A (velimR wkRen C cN cP cS cU B))) cP)
                (subst1 C (PiB A B))

  conv-VElim-Sigma : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN A : Expr n}
                     {B : Expr (suc n)} {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> HasType G A V
    -> HasType (extend G A) B V
    -> ConvTm G (VElim C cN cP cS cU (SigmaB A B))
                (substExpr (sub4 A (Lam A B) (VElim C cN cP cS cU A)
                                 (Lam A (velimR wkRen C cN cP cS cU B))) cS)
                (subst1 C (SigmaB A B))

  conv-VElim-U : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN f g : Expr n}
                 {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> HasType G f OpF
    -> HasType G g (OpG f)
    -> ConvTm G (VElim C cN cP cS cU (Ucode f g))
                (substExpr (sub4 f g
                   (Lam V (Lam (Arr x0 V)
                      (velimR w2 C cN cP cS cU (App (App (renExpr w2 f) x1) x0))))
                   (Lam V (Lam (Arr x0 V) (Lam (App (App (renExpr w2 f) x1) x0)
                      (velimR w3 C cN cP cS cU (App (App (App (renExpr w3 g) x2) x1) x0))))))
                   cU)
                (subst1 C (Ucode f g))

  -- NEW: congruence in the eliminated term
  conv-VElim : {n : Num} {G : Ctx n} {C : Expr (suc n)} {cN t t' : Expr n}
               {cP cS cU : Expr (suc (suc (suc (suc n))))}
    -> IsType (extend G V) C
    -> HasType G cN (subst1 C Nat)
    -> HasType (ctxPS G C) cP (resPi C)
    -> HasType (ctxPS G C) cS (resSig C)
    -> HasType (ctxU G C) cU (resU C)
    -> ConvTm G t t' V
    -> ConvTm G (VElim C cN cP cS cU t) (VElim C cN cP cS cU t') (subst1 C t)
