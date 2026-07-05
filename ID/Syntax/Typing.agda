{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Syntax.Typing
--
-- Typing and conversion rules. Minimal version with only Pi and U.
-- Parallel version of TypingRules.agda.
------------------------------------------------------------------------

module ID.Syntax.Typing where

open import ID.Domain.Basic using (Nat ; zero ; suc)
open import ID.Syntax.Raw using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App ; Id ; Ref ; J ;
  wkExpr ; subst1 ; motiveTy ; baseTy)

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

  -- Γ ⊢ A : U   Γ, x:A ⊢ B : U
  -- ─────────────────────────────
  -- Γ ⊢ Π(x:A)B : U
  ty-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G (Pi A B) U

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

  -- Γ ⊢ A : U   Γ ⊢ a : A   Γ ⊢ b : A
  -- ──────────────────────────────────
  -- Γ ⊢ Id A a b : U
  ty-Id : {n : Nat} {G : Ctx n} {A a b : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> HasType G b A
    -> HasType G (Id A a b) U

  -- Γ ⊢ A : U   Γ ⊢ a : A
  -- ─────────────────────────
  -- Γ ⊢ Ref a : Id A a a
  ty-Ref : {n : Nat} {G : Ctx n} {A a : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> HasType G (Ref a) (Id A a a)

  -- Martin-Löf's ORIGINAL J with a fully-dependent motive
  --   C : (x y : A) → Id A x y → U
  -- and base
  --   d : (x : A) → C x x (Ref x).
  -- The eliminator J C d p at p : Id A a b has type C a b p, and reduces (on a
  -- literal Ref a0) to  d a0 : C a0 a0 (Ref a0)  — the SAME type, so subject
  -- reduction is direct (no Id-injectivity).  De Bruijn encodings (inlined):
  --   motive type  C : Pi A (Pi A↑ (Pi (Id A↑↑ x y) U))     x = Var 1, y = Var 0
  --   base type    d : Pi A (App (App (App C↑ x) x) (Ref x))     x = Var 0
  --   result type  J C d p : App (App (App C a) b) p
  ty-J : {n : Nat} {G : Ctx n} {A a b C d p : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> HasType G b A
    -> HasType G C (motiveTy A)
    -> HasType G d (baseTy A C)
    -> HasType G p (Id A a b)
    -> HasType G (J C d p) (App (App (App C a) b) p)

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

  -- Congruence: Pi
  -- Extra (popl18-style "grey") premises dA/dB/dB': the domain typing and the
  -- two codomain typings, so that the adequacy fundamental theorem can recurse
  -- on them as genuine subterms (rather than on typing-ConvTm presuppositions),
  -- which is what lets the conv-Pi case be structural.
  conv-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType (extend G A) B' U
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G (Pi A B) (Pi A' B') U

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

  -- Congruence: Id  (grey premises = LHS component typings, popl18 style)
  conv-Id : {n : Nat} {G : Ctx n} {A A' a a' b b' : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> HasType G b A
    -> ConvTm G A A' U
    -> ConvTm G a a' A
    -> ConvTm G b b' A
    -> ConvTm G (Id A a b) (Id A' a' b') U

  -- β for J (ML original): J C d (Ref a0) reduces to  d a0.  INTRINSIC
  -- conversion (as conv-beta), so subject reduction is non-circular.  Because
  -- the proof is the LITERAL diagonal `Ref a0 : Id A a0 a0`, both sides have the
  -- SAME type  App (App (App C a0) a0) (Ref a0)  ( = subst1 of the base body at
  -- a0 ), so there are NO endpoint/motive-equality premises and NO Id-injectivity.
  conv-J-beta : {n : Nat} {G : Ctx n} {A a0 C d : Expr n}
    -> HasType G A U
    -> HasType G a0 A
    -> HasType G C (motiveTy A)
    -> HasType G d (baseTy A C)
    -> ConvTm G (J C d (Ref a0)) (App d a0) (App (App (App C a0) a0) (Ref a0))

  -- Congruence: Ref  (grey premise A:U)
  conv-Ref : {n : Nat} {G : Ctx n} {A a a' : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> ConvTm G a a' A
    -> ConvTm G (Ref a) (Ref a') (Id A a a)

  -- Congruence: J  (grey premises = LHS component typings)
  conv-J : {n : Nat} {G : Ctx n} {A a b C C' d d' p p' : Expr n}
    -> HasType G A U
    -> HasType G a A
    -> HasType G b A
    -> HasType G C (motiveTy A)
    -> HasType G d (baseTy A C)
    -> HasType G p (Id A a b)
    -> ConvTm G C C' (motiveTy A)
    -> ConvTm G d d' (baseTy A C)
    -> ConvTm G p p' (Id A a b)
    -> ConvTm G (J C d p) (J C' d' p') (App (App (App C a) b) p)
