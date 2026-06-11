{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.TypingRules
--
-- Typing and conversion rules. Minimal version with only Pi and U.
-- Parallel version of TypingRules.agda.
------------------------------------------------------------------------

module CAST.TypingRules where

open import CAST.Basic using (Nat ; zero ; suc)
open import CAST.RawSyntax using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App ; Id ; refl ; sym ; pi1 ; pi2 ; cast ;
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

  -- Γ ⊢ A : U   Γ ⊢ B : U
  -- ─────────────────────────  (proof-irrelevant equality of types)
  -- Γ ⊢ Id A B : U
  ty-Id : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G (Id A B) U

  -- Γ ⊢ A : U
  -- ──────────────────────  reflexivity proof
  -- Γ ⊢ refl : Id A A
  ty-refl : {n : Nat} {G : Ctx n} {A : Expr n}
    -> HasType G A U
    -> HasType G refl (Id A A)

  -- Γ ⊢ p : Id A B   ->   Γ ⊢ sym p : Id B A
  ty-sym : {n : Nat} {G : Ctx n} {A B p : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G p (Id A B)
    -> HasType G (sym p) (Id B A)

  -- Γ ⊢ p : Id (Π A B) (Π C D)   ->   Γ ⊢ pi1 p : Id A C
  ty-pi1 : {n : Nat} {G : Ctx n} {A C : Expr n} {B D : Expr (suc n)} {p : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G C U
    -> HasType (extend G C) D U
    -> HasType G p (Id (Pi A B) (Pi C D))
    -> HasType G (pi1 p) (Id A C)

  -- Γ ⊢ p : Id (Π A B) (Π C D)   Γ ⊢ N : A
  -- ───────────────────────────────────────────────────────────────
  -- Γ ⊢ pi2 p N : Id (B[N]) (D[cast A C (pi1 p) N])
  ty-pi2 : {n : Nat} {G : Ctx n} {A C : Expr n} {B D : Expr (suc n)} {p N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G C U
    -> HasType (extend G C) D U
    -> HasType G p (Id (Pi A B) (Pi C D))
    -> HasType G N A
    -> HasType G (pi2 p N) (Id (subst1 B N) (subst1 D (cast A C (pi1 p) N)))

  -- Γ ⊢ A : U   Γ ⊢ B : U   Γ ⊢ p : Id A B   Γ ⊢ M : A
  -- ───────────────────────────────────────────────────────
  -- Γ ⊢ cast A B p M : B
  ty-cast : {n : Nat} {G : Ctx n} {A B p M : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G p (Id A B)
    -> HasType G M A
    -> HasType G (cast A B p M) B

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

  -- Congruence for Id (primitive former; not derivable).  popl18-style grey
  -- typing premises so adequacy can recurse on genuine subterms.
  conv-Id : {n : Nat} {G : Ctx n} {A B A' B' : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G A' U
    -> HasType G B' U
    -> ConvTm G A A' U
    -> ConvTm G B B' U
    -> ConvTm G (Id A B) (Id A' B') U

  -- cast fires on the refl proof:  cast A B refl M  =  M : B.
  -- `refl` in the term means (by ty-refl + ty-conv) that A ≡ B already, so
  -- the coercion is the identity.  The convertibility is a CONSEQUENCE of the
  -- proof being refl (Lean-style ι-rule), recorded here as the premise.
  conv-cast-refl : {n : Nat} {G : Ctx n} {A B M : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G M A
    -> ConvTm G A B U
    -> ConvTm G (cast A B refl M) M B

  -- Proof irrelevance for Id (it is a Prop): any two proofs are convertible.
  conv-Id-irr : {n : Nat} {G : Ctx n} {A B p q : Expr n}
    -> HasType G p (Id A B)
    -> HasType G q (Id A B)
    -> ConvTm G p q (Id A B)

  -- Congruence for cast (an element of an arbitrary type, so it needs its own
  -- congruence; proofs related by irrelevance, hence no proof-conv premise).
  conv-cast-cong : {n : Nat} {G : Ctx n} {A B A' B' p p' M M' : Expr n}
    -> HasType G A U
    -> HasType G B U
    -> HasType G p (Id A B)
    -> HasType G M A
    -> HasType G A' U
    -> HasType G B' U
    -> HasType G p' (Id A' B')
    -> HasType G M' A'
    -> ConvTm G A A' U
    -> ConvTm G B B' U
    -> ConvTm G M M' A
    -> ConvTm G (cast A B p M) (cast A' B' p' M') B

  -- Congruence for pi1 (horizontal: components convertible).
  conv-pi1 : {n : Nat} {G : Ctx n} {A C A' C' : Expr n}
    {B D B' D' : Expr (suc n)} {p p' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G C U
    -> HasType (extend G C) D U
    -> HasType G p (Id (Pi A B) (Pi C D))
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G C C' U
    -> ConvTm (extend G C) D D' U
    -> ConvTm G p p' (Id (Pi A B) (Pi C D))
    -> ConvTm G (pi1 p) (pi1 p') (Id A C)

  -- Congruence for pi2.
  conv-pi2 : {n : Nat} {G : Ctx n} {A C A' C' : Expr n}
    {B D B' D' : Expr (suc n)} {p p' N N' : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G C U
    -> HasType (extend G C) D U
    -> HasType G p (Id (Pi A B) (Pi C D))
    -> HasType G N A
    -> ConvTm G A A' U
    -> ConvTm (extend G A) B B' U
    -> ConvTm G C C' U
    -> ConvTm (extend G C) D D' U
    -> ConvTm G p p' (Id (Pi A B) (Pi C D))
    -> ConvTm G N N' A
    -> ConvTm G (pi2 p N) (pi2 p' N') (Id (subst1 B N) (subst1 D (cast A C (pi1 p) N)))

  -- coe-Pi: the cubical-style iota-reduction for a cast between Pi types,
  -- paired with headred-cast-Pi.  Mirror of conv-beta (component typings as
  -- grey premises).  N' = cast C A (pi1 (sym p)) N : A.
  conv-cast-Pi : {n : Nat} {G : Ctx n} {A C : Expr n} {B D : Expr (suc n)}
    {p M N : Expr n}
    -> HasType G A U
    -> HasType (extend G A) B U
    -> HasType G C U
    -> HasType (extend G C) D U
    -> HasType G p (Id (Pi A B) (Pi C D))
    -> HasType G M (Pi A B)
    -> HasType G N C
    -> ConvTm G (App (cast (Pi A B) (Pi C D) p M) N)
                (cast (subst1 B (cast C A (pi1 (sym p)) N)) (subst1 D N)
                      (sym (pi2 (sym p) N))
                      (App M (cast C A (pi1 (sym p)) N)))
                (subst1 D N)
