{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SigmaEtaExt.agda
--
-- Equivalence between the pair-η rule and the extensionality rule for
-- Σ-types, in the presence of Beta-Fst, Beta-Snd and the MkPair
-- congruences.
--
--   Eta :  M : Σ(x:A)B  ⊢  ⟨π₁ M, π₂ M⟩ = M : Σ(x:A)B
--
--   Ext :  M, N : Σ(x:A)B ,
--          π₁ M = π₁ N : A ,
--          π₂ M = π₂ N : B[π₁ M]
--          ⊢  M = N : Σ(x:A)B
--
-- Both directions are derivable. 0 postulates.
------------------------------------------------------------------------

module SigmaEtaExt where

open import BasicSigma using (Nat ; suc)
open import RawSyntaxSigma using
  (Expr ; U ; Sigma ; MkPair ; Fst ; Snd ; subst1)
open import TypingRulesSigma using
  (Ctx ; extend ;
   HasType ; ty-MkPair ; ty-Fst ; ty-Snd ;
   ConvTm ; conv-sym ; conv-trans ; conv-conv ;
   conv-beta-fst ; conv-beta-snd ; conv-pair-eta ;
   conv-MkPair-fst ; conv-MkPair-snd)
open import SubstitutionLemmaSigma using
  (subst-HasType ; subst1-WtSub ; subst1-cong-ConvTm ; typing-WfCtx)

------------------------------------------------------------------------
-- The two statements as types
------------------------------------------------------------------------

Eta : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Set
Eta G A B =
  {M : Expr _}
  -> HasType G M (Sigma A B)
  -> ConvTm G (MkPair (Fst M) (Snd M)) M (Sigma A B)

Ext : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Set
Ext G A B =
  {M N : Expr _}
  -> HasType G M (Sigma A B)
  -> HasType G N (Sigma A B)
  -> ConvTm G (Fst M) (Fst N) A
  -> ConvTm G (Snd M) (Snd N) (subst1 B (Fst M))
  -> ConvTm G M N (Sigma A B)

------------------------------------------------------------------------
-- Direction 1: Eta ⇒ Ext
--
-- M = ⟨π₁ M, π₂ M⟩                  (sym pair-η on M)
--   = ⟨π₁ N, π₂ M⟩                  (MkPair-Fst, using π₁ M = π₁ N)
--   = ⟨π₁ N, π₂ N⟩                  (MkPair-Snd, using π₂ M = π₂ N at B[π₁ N])
--   = N                              (pair-η on N)
--
-- The only subtlety is that the user-supplied cv2 lives at B[π₁ M],
-- but MkPair-Snd requires the equality at B[π₁ N].  We convert via
-- the substitution-congruence lemma on the type family B.
------------------------------------------------------------------------

eta->ext : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> HasType G A U
  -> HasType (extend G A) B U
  -> Eta G A B
  -> Ext G A B
eta->ext {G = G} {A = A} {B = B} dA dB eta {M} {N} dM dN cv1 cv2 =
  let
    dFstM = ty-Fst dA dB dM
    dFstN = ty-Fst dA dB dN
    dSndM = ty-Snd dA dB dM

    -- B[π₁ M] = B[π₁ N] : U, from π₁ M = π₁ N : A
    convB = subst1-cong-ConvTm dA dB dFstM dFstN cv1

    -- B[π₁ N] : U
    dBFstN = subst-HasType (subst1-WtSub dA dFstN) (typing-WfCtx dA) dB

    -- Transport cv2 from B[π₁ M] to B[π₁ N]
    cv2' = conv-conv cv2 convB dBFstN

    step1 = conv-sym (conv-pair-eta dA dB dM)
    step2 = conv-MkPair-fst dA dB cv1 dSndM
    step3 = conv-MkPair-snd dA dB dFstN cv2'
    step4 = conv-pair-eta dA dB dN
  in
    conv-trans step1 (conv-trans step2 (conv-trans step3 step4))

------------------------------------------------------------------------
-- Direction 2: Ext ⇒ Eta
--
-- Let P = ⟨π₁ M, π₂ M⟩.  Then
--   π₁ M = π₁ P : A            (sym Beta-Fst)
--   π₂ M = π₂ P : B[π₁ M]      (sym Beta-Snd)
-- so by Ext we get M = P, whence P = M by symmetry.
-- No type conversion is needed in this direction because the target
-- B[π₁ M] of Ext lines up with the conclusion of Beta-Snd.
------------------------------------------------------------------------

ext->eta : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> HasType G A U
  -> HasType (extend G A) B U
  -> Ext G A B
  -> Eta G A B
ext->eta dA dB ext {M} dM =
  let
    dFstM = ty-Fst dA dB dM
    dSndM = ty-Snd dA dB dM
    dP    = ty-MkPair dA dB dFstM dSndM

    cv1 = conv-sym (conv-beta-fst dA dB dFstM dSndM)
    cv2 = conv-sym (conv-beta-snd dA dB dFstM dSndM)
  in
    conv-sym (ext dM dP cv1 cv2)
