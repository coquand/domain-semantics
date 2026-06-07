{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- TypingRulesSigma.agda
--
-- Typing and conversion rules extended with Sigma types.
-- Parallel version of TypingRules.agda.
--
-- New judgment forms for Sigma:
--   ty-Sigma    Γ ⊢ Σ(x:A)B : U
--   ty-MkPair   Γ ⊢ (M,N) : Σ(x:A)B
--   ty-Fst      Γ ⊢ π₁ M : A
--   ty-Snd      Γ ⊢ π₂ M : B[x/π₁ M]
--   conv-beta-fst   (π₁(M,N)) = M
--   conv-beta-snd   (π₂(M,N)) = N
--   conv-Sigma      congruence for Σ
------------------------------------------------------------------------

module SigmaProp.TypingRulesSigma where

open import SigmaProp.BasicSigma using (Nat ; zero ; suc)
open import SigmaProp.RawSyntaxSigma using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Prop ; Pi ; Lam ; App ; Sigma ; MkPair ; Fst ; Snd ;
  wkExpr ; subst1)

------------------------------------------------------------------------
-- Ctx — typing contexts as snoc-lists
------------------------------------------------------------------------

data Ctx : Nat -> Set where
  empty  : Ctx zero
  extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

------------------------------------------------------------------------
-- lookup
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
-- WfCtx
------------------------------------------------------------------------

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Nat} {G : Ctx n} {A : Expr n}
    -> HasType G A U
    -> WfCtx (extend G A)

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

data HasType where

  ty-var : {n : Nat} {G : Ctx n} {i : Fin n}
    -> WfCtx G
    -> HasType G (Var i) (lookup G i)

  ty-conv : {n : Nat} {G : Ctx n} {M A B : Expr n}
    -> HasType G M A
    -> ConvTm G A B U
    -> HasType G B U
    -> HasType G M B

  ty-U : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G U U

  ty-Prop : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G Prop U

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

  -- Γ ⊢ A : U   Γ, x:A ⊢ B : U
  -- ─────────────────────────────
  -- Γ ⊢ Σ(x:A)B : U
  ty-Sigma : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G (Sigma A B) U

  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ M : A   Γ ⊢ N : B[x/M]
  -- ─────────────────────────────────────────────────────────────
  -- Γ ⊢ (M,N) : Σ(x:A)B
  ty-MkPair : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M A
    -> HasType G N (subst1 B M)
    -> HasType G (MkPair M N) (Sigma A B)

  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ M : Σ(x:A)B
  -- ─────────────────────────────────────────────────
  -- Γ ⊢ π₁ M : A
  ty-Fst : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M (Sigma A B)
    -> HasType G (Fst M) A

  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ M : Σ(x:A)B
  -- ─────────────────────────────────────────────────
  -- Γ ⊢ π₂ M : B[x/π₁ M]
  ty-Snd : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M (Sigma A B)
    -> HasType G (Snd M) (subst1 B (Fst M))

------------------------------------------------------------------------
-- ConvTm
------------------------------------------------------------------------

data ConvTm where

  conv-refl : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A
    -> ConvTm G M M A

  conv-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N M A

  conv-trans : {n : Nat} {G : Ctx n} {M N P A : Expr n}
    -> ConvTm G M N A
    -> ConvTm G N P A
    -> ConvTm G M P A

  conv-conv : {n : Nat} {G : Ctx n} {M N A B : Expr n}
    -> ConvTm G M N A
    -> ConvTm G A B U
    -> HasType G B U
    -> ConvTm G M N B

  -- β for application
  conv-beta : {n : Nat} {G : Ctx n} {A : Expr n} {B M : Expr (suc n)}
    {a : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType (extend G A) M B
    -> HasType G a A
    -> ConvTm G (App (Lam A M) a) (subst1 M a) (subst1 B a)

  -- Proof-irrelevance
  conv-Prop : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> HasType G A Prop
    -> HasType G M A
    -> HasType G N A
    -> ConvTm G M N A

  -- Prop-to-U subtyping for conversions:
  -- Γ ⊢ M = N : Prop
  -- ──────────────────
  -- Γ ⊢ M = N : U
  conv-Prop-U : {n : Nat} {G : Ctx n} {M N : Expr n}
    -> ConvTm G M N Prop
    -> ConvTm G M N U

  -- Congruence: Pi
  conv-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G (Pi A B) (Pi A' B') U

  -- Congruence: Pi at Prop (codomain in Prop)
  conv-Pi-Prop : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' Prop
    -> ConvTm G (Pi A B) (Pi A' B') Prop

  -- Function extensionality
  conv-funext : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f g : Expr n}
    -> HasType G A U
    -> ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                            (App (wkExpr g) (Var fzero)) B
    -> HasType G f (Pi A B)
    -> HasType G g (Pi A B)
    -> ConvTm G f g (Pi A B)

  -- Congruence: App (function)
  conv-App-fun : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f f' a : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G f f' (Pi A B)
    -> HasType G a A
    -> ConvTm G (App f a) (App f' a) (subst1 B a)

  -- Congruence: App (argument)
  conv-App-arg : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {f a a' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G f (Pi A B)
    -> ConvTm G a a' A
    -> ConvTm G (App f a) (App f a') (subst1 B a)

  -- Congruence: Sigma
  conv-Sigma : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G (Sigma A B) (Sigma A' B') U

  -- β for fst: π₁(M,N) = M
  conv-beta-fst : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M A
    -> HasType G N (subst1 B M)
    -> ConvTm G (Fst (MkPair M N)) M A

  -- β for snd: π₂(M,N) = N
  conv-beta-snd : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M A
    -> HasType G N (subst1 B M)
    -> ConvTm G (Snd (MkPair M N)) N (subst1 B M)

  -- Surjective pairing (η for Sigma):
  -- Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ M : Σ(x:A)B
  -- ──────────────────────────────────────────────────
  -- Γ ⊢ (π₁ M, π₂ M) = M : Σ(x:A)B
  conv-pair-eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M (Sigma A B)
    -> ConvTm G (MkPair (Fst M) (Snd M)) M (Sigma A B)

  -- Congruence: MkPair (first component)
  conv-MkPair-fst : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M M' N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G M M' A
    -> HasType G N (subst1 B M)
    -> ConvTm G (MkPair M N) (MkPair M' N) (Sigma A B)

  -- Congruence: MkPair (second component)
  conv-MkPair-snd : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M N N' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G M A
    -> ConvTm G N N' (subst1 B M)
    -> ConvTm G (MkPair M N) (MkPair M N') (Sigma A B)

  -- Congruence: Fst
  conv-Fst : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M M' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G M M' (Sigma A B)
    -> ConvTm G (Fst M) (Fst M') A

  -- Congruence: Snd
  conv-Snd : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    {M M' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> ConvTm G M M' (Sigma A B)
    -> ConvTm G (Snd M) (Snd M') (subst1 B (Fst M))
