{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- TypingRules.agda
--
-- Typing and conversion rules for dependent type theory with U : U.
-- Three judgment forms:
--   WfCtx Γ           Γ ⊢
--   HasType Γ M A     Γ ⊢ M : A
--   ConvTm Γ M N A    Γ ⊢ M = N : A
------------------------------------------------------------------------

module TypingRules where

open import Basic using (Nat ; zero ; suc)
open import RawSyntax using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Prop ; Pi ; Lam ; App ; wkExpr ; subst1)

------------------------------------------------------------------------
-- Ctx — typing contexts as snoc-lists
------------------------------------------------------------------------

data Ctx : Nat -> Set where
  empty  : Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

------------------------------------------------------------------------
-- lookup — extract the type of a variable, weakened into scope
------------------------------------------------------------------------

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

------------------------------------------------------------------------
-- Judgments (mutual)
------------------------------------------------------------------------

data WfCtx  : {n : Nat} -> Ctx n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

------------------------------------------------------------------------
-- WfCtx — well-formed contexts
------------------------------------------------------------------------

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> HasType G A U
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- HasType — typing
------------------------------------------------------------------------

data HasType where

  -- Γ ⊢   (x : A in Γ)
  -- ─────────────────────
  -- Γ ⊢ x : A
  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  -- Γ ⊢ M : A   Γ ⊢ A = B : U   Γ ⊢ B : U
  -- ──────────────────────────────────────
  -- Γ ⊢ M : B
  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTm G A B U
    -> HasType G B U
    -> HasType G M B

  -- Γ ⊢
  -- ─────────
  -- Γ ⊢ U : U
  ty-U : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G U U

  -- Γ ⊢
  -- ─────────────
  -- Γ ⊢ Prop : U
  ty-Prop : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G Prop U

  -- Γ ⊢ A : Prop
  -- ─────────────
  -- Γ ⊢ A : U
  ty-Prop-U : {n : Nat} {G : Ctx n} {A : Expr n}
    -> HasType G A Prop
    -> HasType G A U

  -- Γ ⊢ A : U   Γ, x:A ⊢ B : U
  -- ─────────────────────────────
  -- Γ ⊢ Π(x:A)B : U
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G (Pi A B) U

  -- Γ ⊢ A : U   Γ, x:A ⊢ B : Prop
  -- ────────────────────────────────
  -- Γ ⊢ Π(x:A)B : Prop
  ty-Pi-Prop : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B Prop
    -> HasType G (Pi A B) Prop

  -- Γ ⊢ A : U   Γ, x:A ⊢ B : U   Γ, x:A ⊢ N : B
  -- ─────────────────────────────────────────────────
  -- Γ ⊢ λ(x:A)N : Π(x:A)B
  ty-Lam : {n : Nat} {G : Ctx n} {A : Expr n} {B M : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType (extend G A) M B
    -> HasType G (Lam A M) (Pi A B)

  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f : Π(x:A)B   Γ ⊢ a : A
  -- ─────────────────────────────────────────────────────────────
  -- Γ ⊢ f a : B[x/a]
  ty-App : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f a : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G f (Pi A B)
    -> HasType G a A
    -> HasType G (App f a) (subst1 B a)

------------------------------------------------------------------------
-- ConvTm — definitional equality of terms at a type
------------------------------------------------------------------------

data ConvTm where

  -- Γ ⊢ M : A
  -- ──────────────
  -- Γ ⊢ M = M : A
  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A
    -> ConvTm G M M A

  -- Γ ⊢ M = N : A
  -- ──────────────
  -- Γ ⊢ N = M : A
  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N M A

  -- Γ ⊢ M = N : A   Γ ⊢ N = P : A
  -- ───────────────────────────────
  -- Γ ⊢ M = P : A
  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N P A
    -> ConvTm G M P A

  -- Γ ⊢ M = N : A   Γ ⊢ A = B : U   Γ ⊢ B : U
  -- ─────────────────────────────────────────────
  -- Γ ⊢ M = N : B
  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTm G A B U
    -> HasType G B U
    -> ConvTm G M N B

  -- β-rule:
  -- Γ ⊢ A : U   Γ, x:A ⊢ B : U   Γ, x:A ⊢ M : B   Γ ⊢ a : A
  -- ──────────────────────────────────────────────────────────────
  -- Γ ⊢ (λ(x:A)M) a = M[x/a] : B[x/a]
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B M : Expr (suc n)}
    {a : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType (extend G A) M B
    -> HasType G a A
    -> ConvTm G (App (Lam A M) a) (subst1 M a) (subst1 B a)

  -- Proof-irrelevance:
  -- Γ ⊢ A : Prop   Γ ⊢ M : A   Γ ⊢ N : A
  -- ─────────────────────────────────────────
  -- Γ ⊢ M = N : A
  conv-Prop : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> HasType G A Prop
    -> HasType G M A
    -> HasType G N A
    -> ConvTm G M N A

  -- Congruence: Pi
  -- Γ ⊢ A = A' : U   Γ, x:A ⊢ B = B' : U
  -- ───────────────────────────────────────
  -- Γ ⊢ Π(x:A)B = Π(x:A')B' : U
  conv-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G (Pi A B) (Pi A' B') U

  -- Extensional function equality:
  -- Γ ⊢ A : U   Γ, x:A ⊢ f x = g x : B   Γ ⊢ f : Π(x:A)B   Γ ⊢ g : Π(x:A)B
  -- ──────────────────────────────────────────────────────────────────────────────
  -- Γ ⊢ f = g : Π(x:A)B
  --
  -- where f x = App (wkExpr f) (Var fzero) in the extended context.
  conv-funext : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f g : Expr n}
    -> HasType G A U
    -> ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                            (App (wkExpr g) (Var fzero)) B
    -> HasType G f (Pi A B)
    -> HasType G g (Pi A B)
    -> ConvTm G f g (Pi A B)

  -- Congruence: App (function slot)
  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f = f' : Π(x:A)B   Γ ⊢ a : A
  -- ──────────────────────────────────────────────────────────────────
  -- Γ ⊢ f a = f' a : B[x/a]
  conv-App-fun : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f f' a : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G f f' (Pi A B)
    -> HasType G a A
    -> ConvTm G (App f a) (App f' a) (subst1 B a)

  -- Congruence: App (argument slot)
  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f : Π(x:A)B   Γ ⊢ a = a' : A
  -- ──────────────────────────────────────────────────────────────────
  -- Γ ⊢ f a = f a' : B[x/a]
  conv-App-arg : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f a a' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G f (Pi A B)
    -> ConvTm G a a' A
    -> ConvTm G (App f a) (App f a') (subst1 B a)
