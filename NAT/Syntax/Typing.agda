{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- NAT.Syntax.Typing
--
-- Typing and conversion rules. Minimal version with only Pi and U.
-- Parallel version of TypingRules.agda.
------------------------------------------------------------------------

module NAT.Syntax.Typing where

open import NAT.Domain.Basic using (Nat ; zero ; suc)
open import NAT.Syntax.Raw using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App ; Y ; NatT ; Zero ; Suc ; Case ;
  wkExpr ; subst1 ; subSucC)

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

  -- Γ ⊢ A : U   Γ ⊢ g : Π(x:A)A   (non-dependent: A → A)
  -- ────────────────────────────────────────────────────
  -- Γ ⊢ Y g : A
  ty-Y : {n : Nat} {G : Ctx n} {A : Expr n} {g : Expr n}
    -> HasType G A U
    -> HasType G g (Pi A (wkExpr A))
    -> HasType G (Y g) A

  -- Γ ⊢ Nat : U
  ty-NatT : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G NatT U

  -- Γ ⊢ 0 : Nat
  ty-Zero : {n : Nat} {G : Ctx n}
    -> WfCtx G
    -> HasType G Zero NatT

  -- Γ ⊢ m : Nat   ⟹   Γ ⊢ S m : Nat
  ty-Suc : {n : Nat} {G : Ctx n} {m : Expr n}
    -> HasType G m NatT
    -> HasType G (Suc m) NatT

  -- Non-dependent caseNat (simple eliminator):
  -- Γ ⊢ C : U   Γ ⊢ M : Nat   Γ ⊢ a : C   Γ ⊢ b : Π(Nat) C
  -- ─────────────────────────────────────────────────────────
  -- Γ ⊢ case M a b : C      (case 0 a b → a, case (S n) a b → b n)
  ty-Case : {n : Nat} {G : Ctx n} {C M a b : Expr n}
    -> HasType G C U
    -> HasType G M NatT
    -> HasType G a C
    -> HasType G b (Pi NatT (wkExpr C))
    -> HasType G (Case M a b) C

  -- Dependent caseNat (large eliminator).  Motive C : Nat ⊢ U.
  -- Γ,n:Nat ⊢ C : U   Γ ⊢ M : Nat   Γ ⊢ a : C[0]   Γ ⊢ b : Π(n:Nat) C[S n]
  -- ────────────────────────────────────────────────────────────────────────
  -- Γ ⊢ case M a b : C[M]
  ty-Case-dep : {n : Nat} {G : Ctx n} {C : Expr (suc n)} {M a b : Expr n}
    -> HasType (extend G NatT) C U
    -> HasType G M NatT
    -> HasType G a (subst1 C Zero)
    -> HasType G b (Pi NatT (subSucC C))
    -> HasType G (Case M a b) (subst1 C M)

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

  -- Y unfolding (intrinsic, like conv-beta — no circularity):
  --   Y g = g (Y g) : A    (App g (Y g) : subst1 (wk A) (Y g) = A)
  conv-Y : {n : Nat} {G : Ctx n} {A : Expr n} {g : Expr n}
    -> HasType G A U
    -> HasType G g (Pi A (wkExpr A))
    -> ConvTm G (Y g) (App g (Y g)) A

  -- Y congruence (standard term-former congruence, like conv-App-fun):
  --   g = g' : Π(x:A)A   ⟹   Y g = Y g' : A
  conv-Y-cong : {n : Nat} {G : Ctx n} {A : Expr n} {g g' : Expr n}
    -> HasType G A U
    -> ConvTm G g g' (Pi A (wkExpr A))
    -> ConvTm G (Y g) (Y g') A

  -- caseNat computation rules (intrinsic, like conv-beta; no circularity)
  conv-case-zero : {n : Nat} {G : Ctx n} {C a b : Expr n}
    -> HasType G C U
    -> HasType G a C
    -> HasType G b (Pi NatT (wkExpr C))
    -> ConvTm G (Case Zero a b) a C

  conv-case-suc : {n : Nat} {G : Ctx n} {C m a b : Expr n}
    -> HasType G C U
    -> HasType G m NatT
    -> HasType G a C
    -> HasType G b (Pi NatT (wkExpr C))
    -> ConvTm G (Case (Suc m) a b) (App b m) C

  -- Dependent caseNat computation rules (intrinsic, like conv-beta).
  conv-case-zero-dep : {n : Nat} {G : Ctx n} {C : Expr (suc n)} {a b : Expr n}
    -> HasType (extend G NatT) C U
    -> HasType G a (subst1 C Zero)
    -> HasType G b (Pi NatT (subSucC C))
    -> ConvTm G (Case Zero a b) a (subst1 C Zero)

  -- App b m : subst1 (subSucC C) m = subst1 C (Suc m)  (the types line up).
  conv-case-suc-dep : {n : Nat} {G : Ctx n} {C : Expr (suc n)} {m a b : Expr n}
    -> HasType (extend G NatT) C U
    -> HasType G m NatT
    -> HasType G a (subst1 C Zero)
    -> HasType G b (Pi NatT (subSucC C))
    -> ConvTm G (Case (Suc m) a b) (App b m) (subst1 C (Suc m))

  -- Congruence: Suc
  conv-Suc : {n : Nat} {G : Ctx n} {m m' : Expr n}
    -> ConvTm G m m' NatT
    -> ConvTm G (Suc m) (Suc m') NatT

  -- Congruence: Case (scrutinee + branches)
  conv-Case : {n : Nat} {G : Ctx n} {C M M' a a' b b' : Expr n}
    -> HasType G C U
    -> ConvTm G M M' NatT
    -> ConvTm G a a' C
    -> ConvTm G b b' (Pi NatT (wkExpr C))
    -> ConvTm G (Case M a b) (Case M' a' b') C

  -- Congruence: dependent Case.  Result type uses the LEFT scrutinee M
  -- (the right side Case M' a' b' is naturally at C[M'] ≡ C[M] since M≡M').
  conv-Case-dep : {n : Nat} {G : Ctx n} {C : Expr (suc n)} {M M' a a' b b' : Expr n}
    -> HasType (extend G NatT) C U
    -> ConvTm G M M' NatT
    -> ConvTm G a a' (subst1 C Zero)
    -> ConvTm G b b' (Pi NatT (subSucC C))
    -> ConvTm G (Case M a b) (Case M' a' b') (subst1 C M)
