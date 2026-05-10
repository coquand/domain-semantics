{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.Uniqueness
--
-- The uniqueness lemma (slide 17 of the TYPES 2026 talk):
--
--   (Type uniqueness)  If Γ ⊢ A type and Γ ⊢ B type in T_T with
--                      |A| = |B|, then Γ ⊢ A = B.
--
--   (Term uniqueness)  If Γ ⊢ u₀ : A₀ and Γ ⊢ u₁ : A₁ in T_T with
--                      |u₀| = |u₁|, then either:
--                      (1) Γ ⊢ A₀ = A₁  and  Γ ⊢ u₀ = u₁ : A₀; or
--                      (2) there exist levels n₀, n₁, k and codes
--                          v₀, v₁ : U_k with
--                            Γ ⊢ A₀ = U_{n₀},
--                            Γ ⊢ A₁ = U_{n₁},
--                            Γ ⊢ u₀ = ↑^{n₀}_k(v₀) : A₀,
--                            Γ ⊢ u₁ = ↑^{n₁}_k(v₁) : A₁,
--                            Γ ⊢ v₀ = v₁ : U_k.
--
-- The proof goes by mutual induction on the size of A and u₀, and
-- crucially uses U-injectivity, U/Π no-confusion, and Π-injectivity
-- (all from Sterbac.Postulates).
------------------------------------------------------------------------

module Sterbac.Uniqueness where

open import Sterbac.Basic
import Sterbac.RussellSyntax  as R
import Sterbac.RussellTyping  as RT
import Sterbac.TarskiSyntax   as T
import Sterbac.TarskiTyping   as TT
import Sterbac.Erasure        as E
import Sterbac.TarskiMeta     as TM
open import Sterbac.Postulates

------------------------------------------------------------------------
-- Size of a Tarski expression
------------------------------------------------------------------------

size : {n : Nat} -> T.Expr n -> Nat
size (T.Var _)        = 1
size (T.Pi A B)       = suc (size A + size B)
size (T.U _)          = 1
size (T.El _ a)       = suc (size a)
size (T.Lam A B b)    = suc (size A + size B + size b)
size (T.App A B c a)  = suc (size A + size B + size c + size a)
size (T.PiCode _ a b) = suc (size a + size b)
size (T.UCode _ _)    = 1
size (T.Lift _ _ a)   = suc (size a)

------------------------------------------------------------------------
-- Statement of the type-uniqueness lemma
------------------------------------------------------------------------

TypeUniqStatement : Set
TypeUniqStatement =
  {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
  -> TT.IsType G A
  -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.ConvTy G A B

------------------------------------------------------------------------
-- Statement of the term-uniqueness lemma
------------------------------------------------------------------------

-- A "lift step" is a code-level relationship: either u is convertible
-- to v directly (when m = k, i.e., no actual lift needed) or u is
-- convertible to the proper lift Lift m k v (with k < m).  This
-- decomposition is forced by Tarski's strict Lift constructor; the
-- Rocq formalisation uses a unified `cLift` with k ≤ m and the rule
-- `cLift l l u = u`, but here we keep Lift strict and split at the
-- meta-level.
data LiftStep {n : Nat} (G : TT.Ctx n)
              (u : T.Expr n) (m k : Nat)
              (v A : T.Expr n) : Set where
  trivial : Eq m k -> TT.ConvTm G u v A -> LiftStep G u m k v A
  proper  : Lt k m -> TT.ConvTm G u (T.Lift m k v) A
                   -> LiftStep G u m k v A

record CommonLift {n : Nat} (G : TT.Ctx n)
                  (u₀ u₁ A₀ A₁ : T.Expr n) : Set where
  constructor mkCommonLift
  field
    n₀  : Nat
    n₁  : Nat
    k   : Nat
    v₀  : T.Expr n
    v₁  : T.Expr n
    A₀≡U : TT.ConvTy G A₀ (T.U n₀)
    A₁≡U : TT.ConvTy G A₁ (T.U n₁)
    u₀≡  : LiftStep G u₀ n₀ k v₀ A₀
    u₁≡  : LiftStep G u₁ n₁ k v₁ A₁
    v₀≡v₁ : TT.ConvTm G v₀ v₁ (T.U k)

TermUniqResult : {n : Nat} -> TT.Ctx n
              -> T.Expr n -> T.Expr n -> T.Expr n -> T.Expr n -> Set
TermUniqResult G u₀ u₁ A₀ A₁ =
  Either
    (Pair (TT.ConvTy G A₀ A₁)
          (TT.ConvTm G u₀ u₁ A₀))
    (CommonLift G u₀ u₁ A₀ A₁)

TermUniqStatement : Set
TermUniqStatement =
  {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ : T.Expr n}
  -> TT.HasType G u₀ A₀
  -> TT.HasType G u₁ A₁
  -> Eq (E.erase u₀) (E.erase u₁)
  -> TermUniqResult G u₀ u₁ A₀ A₁

------------------------------------------------------------------------
-- Inversion records
------------------------------------------------------------------------

record InvVar {n : Nat} (G : TT.Ctx n) (i : Fin n) (Ty : T.Expr n) : Set where
  constructor mkInvVar
  field
    dG : TT.WfCtx G
    Tconv : TT.ConvTy G (TT.lookup G i) Ty

record InvLam {n : Nat} (G : TT.Ctx n) (A : T.Expr n)
              (B b : T.Expr (suc n)) (Ty : T.Expr n) : Set where
  constructor mkInvLam
  field
    dA : TT.IsType G A
    dB : TT.IsType (TT.extend G A) B
    db : TT.HasType (TT.extend G A) b B
    Tconv : TT.ConvTy G (T.Pi A B) Ty

record InvApp {n : Nat} (G : TT.Ctx n) (A : T.Expr n)
              (B : T.Expr (suc n)) (c a : T.Expr n) (Ty : T.Expr n) : Set where
  constructor mkInvApp
  field
    dA : TT.IsType G A
    dB : TT.IsType (TT.extend G A) B
    dc : TT.HasType G c (T.Pi A B)
    da : TT.HasType G a A
    Tconv : TT.ConvTy G (T.subst1 B a) Ty

record InvPiCode {n : Nat} (G : TT.Ctx n) (l : Nat)
                 (a : T.Expr n) (b : T.Expr (suc n))
                 (Ty : T.Expr n) : Set where
  constructor mkInvPiCode
  field
    da : TT.HasType G a (T.U l)
    db : TT.HasType (TT.extend G (T.El l a)) b (T.U l)
    Tconv : TT.ConvTy G (T.U l) Ty

record InvUCode {n : Nat} (G : TT.Ctx n) (m k : Nat) (Ty : T.Expr n) : Set where
  constructor mkInvUCode
  field
    dG : TT.WfCtx G
    h : Lt k m
    Tconv : TT.ConvTy G (T.U m) Ty

record InvLift {n : Nat} (G : TT.Ctx n) (m k : Nat) (a : T.Expr n)
               (Ty : T.Expr n) : Set where
  constructor mkInvLift
  field
    h : Lt k m
    da : TT.HasType G a (T.U k)
    Tconv : TT.ConvTy G (T.U m) Ty

------------------------------------------------------------------------
-- Inversion lemmas (peel ty-conv)
------------------------------------------------------------------------

inv-Var : {n : Nat} {G : TT.Ctx n} {i : Fin n} {Ty : T.Expr n}
  -> TT.HasType G (T.Var i) Ty -> InvVar G i Ty
inv-Var (TT.ty-var {i = i} dG) =
  mkInvVar dG (TT.conv-Ty-refl (TM.wfCtx-lookup dG i))
inv-Var (TT.ty-conv d c) =
  let r = inv-Var d
  in mkInvVar (InvVar.dG r) (TT.conv-Ty-trans (InvVar.Tconv r) c)

inv-Lam : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
          {B b : T.Expr (suc n)} {Ty : T.Expr n}
  -> TT.HasType G (T.Lam A B b) Ty -> InvLam G A B b Ty
inv-Lam (TT.ty-Lam dA dB db) =
  mkInvLam dA dB db (TT.conv-Ty-refl (TT.is-Ty-Pi dA dB))
inv-Lam (TT.ty-conv d c) =
  let r = inv-Lam d
  in mkInvLam (InvLam.dA r) (InvLam.dB r) (InvLam.db r)
              (TT.conv-Ty-trans (InvLam.Tconv r) c)

inv-App : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
          {B : T.Expr (suc n)} {c a : T.Expr n} {Ty : T.Expr n}
  -> TT.HasType G (T.App A B c a) Ty -> InvApp G A B c a Ty
inv-App (TT.ty-App dA dB dc da) =
  mkInvApp dA dB dc da
    (TT.conv-Ty-refl (TM.subst-IsType (TM.subst1-WtSub dA da)
                                       (TM.isType-WfCtx dA) dB))
inv-App (TT.ty-conv d c) =
  let r = inv-App d
  in mkInvApp (InvApp.dA r) (InvApp.dB r) (InvApp.dc r) (InvApp.da r)
              (TT.conv-Ty-trans (InvApp.Tconv r) c)

inv-PiCode : {n : Nat} {G : TT.Ctx n} {l : Nat}
             {a : T.Expr n} {b : T.Expr (suc n)} {Ty : T.Expr n}
  -> TT.HasType G (T.PiCode l a b) Ty -> InvPiCode G l a b Ty
inv-PiCode (TT.ty-PiCode {l = l} da db) =
  mkInvPiCode da db (TT.conv-Ty-refl (TT.is-Ty-U {l = l} (TM.typing-WfCtx da)))
inv-PiCode (TT.ty-conv d c) =
  let r = inv-PiCode d
  in mkInvPiCode (InvPiCode.da r) (InvPiCode.db r)
                 (TT.conv-Ty-trans (InvPiCode.Tconv r) c)

inv-UCode : {n : Nat} {G : TT.Ctx n} {m k : Nat} {Ty : T.Expr n}
  -> TT.HasType G (T.UCode m k) Ty -> InvUCode G m k Ty
inv-UCode (TT.ty-UCode {m = m} dG h) =
  mkInvUCode dG h (TT.conv-Ty-refl (TT.is-Ty-U {l = m} dG))
inv-UCode (TT.ty-conv d c) =
  let r = inv-UCode d
  in mkInvUCode (InvUCode.dG r) (InvUCode.h r)
                (TT.conv-Ty-trans (InvUCode.Tconv r) c)

inv-Lift : {n : Nat} {G : TT.Ctx n} {m k : Nat}
           {a : T.Expr n} {Ty : T.Expr n}
  -> TT.HasType G (T.Lift m k a) Ty -> InvLift G m k a Ty
inv-Lift (TT.ty-Lift {m = m} h da) =
  mkInvLift h da (TT.conv-Ty-refl (TT.is-Ty-U {l = m} (TM.typing-WfCtx da)))
inv-Lift (TT.ty-conv d c) =
  let r = inv-Lift d
  in mkInvLift (InvLift.h r) (InvLift.da r)
               (TT.conv-Ty-trans (InvLift.Tconv r) c)

------------------------------------------------------------------------
-- Russell-syntax constructor injectivity (for matching erasure equalities)
------------------------------------------------------------------------

R-Pi-inj : {n : Nat} {A A' : R.Expr n} {B B' : R.Expr (suc n)}
  -> Eq (R.Pi A B) (R.Pi A' B') -> Pair (Eq A A') (Eq B B')
R-Pi-inj refl = mkSigma refl refl

R-U-inj : {n : Nat} {l l' : Nat}
  -> Eq (R.U {n = n} l) (R.U l') -> Eq l l'
R-U-inj refl = refl

R-Var-inj : {n : Nat} {i j : Fin n}
  -> Eq (R.Var i) (R.Var j) -> Eq i j
R-Var-inj refl = refl

R-Lam-inj : {n : Nat} {A A' : R.Expr n} {B B' b b' : R.Expr (suc n)}
  -> Eq (R.Lam A B b) (R.Lam A' B' b')
  -> Pair (Eq A A') (Pair (Eq B B') (Eq b b'))
R-Lam-inj refl = mkSigma refl (mkSigma refl refl)

R-App-inj : {n : Nat} {A A' c c' a a' : R.Expr n} {B B' : R.Expr (suc n)}
  -> Eq (R.App A B c a) (R.App A' B' c' a')
  -> Pair (Eq A A') (Pair (Eq B B') (Pair (Eq c c') (Eq a a')))
R-App-inj refl = mkSigma refl (mkSigma refl (mkSigma refl refl))

------------------------------------------------------------------------
-- Constructor distinctness on Russell side (for absurd cases)
------------------------------------------------------------------------

R-U-Pi-noconf : {n : Nat} {l : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
  -> Eq (R.U l) (R.Pi A B) -> Empty
R-U-Pi-noconf ()

R-U-Lam-noconf : {n : Nat} {l : Nat} {A : R.Expr n} {B b : R.Expr (suc n)}
  -> Eq (R.U l) (R.Lam A B b) -> Empty
R-U-Lam-noconf ()

R-U-App-noconf : {n : Nat} {l : Nat} {A c a : R.Expr n} {B : R.Expr (suc n)}
  -> Eq (R.U l) (R.App A B c a) -> Empty
R-U-App-noconf ()

R-U-Var-noconf : {n : Nat} {l : Nat} {i : Fin n}
  -> Eq (R.U l) (R.Var i) -> Empty
R-U-Var-noconf ()

R-Pi-Lam-noconf : {n : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
                  {A' : R.Expr n} {B' b' : R.Expr (suc n)}
  -> Eq (R.Pi A B) (R.Lam A' B' b') -> Empty
R-Pi-Lam-noconf ()

R-Pi-App-noconf : {n : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
                  {A' c' a' : R.Expr n} {B' : R.Expr (suc n)}
  -> Eq (R.Pi A B) (R.App A' B' c' a') -> Empty
R-Pi-App-noconf ()

R-Pi-Var-noconf : {n : Nat} {A : R.Expr n} {B : R.Expr (suc n)} {i : Fin n}
  -> Eq (R.Pi A B) (R.Var i) -> Empty
R-Pi-Var-noconf ()

R-Pi-U-noconf : {n : Nat} {l : Nat} {A : R.Expr n} {B : R.Expr (suc n)}
  -> Eq (R.Pi A B) (R.U l) -> Empty
R-Pi-U-noconf ()

R-Lam-Var-noconf : {n : Nat} {A : R.Expr n} {B b : R.Expr (suc n)} {i : Fin n}
  -> Eq (R.Lam A B b) (R.Var i) -> Empty
R-Lam-Var-noconf ()

R-Lam-App-noconf : {n : Nat} {A A' c' a' : R.Expr n}
                   {B b : R.Expr (suc n)} {B' : R.Expr (suc n)}
  -> Eq (R.Lam A B b) (R.App A' B' c' a') -> Empty
R-Lam-App-noconf ()

R-App-Var-noconf : {n : Nat} {A c a : R.Expr n} {B : R.Expr (suc n)} {i : Fin n}
  -> Eq (R.App A B c a) (R.Var i) -> Empty
R-App-Var-noconf ()

------------------------------------------------------------------------
-- A few small Le helpers
------------------------------------------------------------------------

Le-cases : (a b : Nat) -> Le a b -> Either (Eq a b) (Lt a b)
Le-cases zero    zero    _ = inl refl
Le-cases zero    (suc b) _ = inr tt
Le-cases (suc a) zero    ()
Le-cases (suc a) (suc b) h with Le-cases a b h
... | inl refl = inl refl
... | inr h'   = inr h'

------------------------------------------------------------------------
-- LiftStep utilities
------------------------------------------------------------------------

liftStep-conv-Ty : {n : Nat} {G : TT.Ctx n} {u : T.Expr n} {m k : Nat}
                   {v : T.Expr n} {A B : T.Expr n}
  -> TT.ConvTy G A B
  -> LiftStep G u m k v A -> LiftStep G u m k v B
liftStep-conv-Ty c (trivial e tm) = trivial e (TT.conv-conv tm c)
liftStep-conv-Ty c (proper  h tm) = proper  h (TT.conv-conv tm c)

------------------------------------------------------------------------
-- T.Pi / T.U / T.El cannot be terms (no HasType producer)
------------------------------------------------------------------------

no-Pi-HasType : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
                {B : T.Expr (suc n)} {Ty : T.Expr n}
  -> TT.HasType G (T.Pi A B) Ty -> Empty
no-Pi-HasType (TT.ty-conv d _) = no-Pi-HasType d

no-U-HasType : {n : Nat} {G : TT.Ctx n} {l : Nat} {Ty : T.Expr n}
  -> TT.HasType G (T.U l) Ty -> Empty
no-U-HasType (TT.ty-conv d _) = no-U-HasType d

no-El-HasType : {n : Nat} {G : TT.Ctx n} {l : Nat} {a : T.Expr n}
                {Ty : T.Expr n}
  -> TT.HasType G (T.El l a) Ty -> Empty
no-El-HasType (TT.ty-conv d _) = no-El-HasType d

------------------------------------------------------------------------
-- The two lemmas
------------------------------------------------------------------------

-- term-uniq is the central remaining work; type-uniq below depends on
-- it.  Strategy: case-split on the typing derivations after peeling
-- ty-conv (using the inversion lemmas above).  The hard subcases are
--
--   * (App, App) — needs a cross-substitution congruence
--     `subst1-cong-Ty : ConvTm G a a' A → ConvTy G (subst1 B a) (subst1 B a')`
--     which is not yet in Sterbac.TarskiMeta.  Provable by mutual
--     induction on B's IsType derivation, lifting the ConvTm through
--     binders.
--   * (Lift, *), (*, Lift), (UCode, UCode) — produce the 2nd case
--     (CommonLift / LiftStep) using `conv-Lift-Lift`, `conv-Lift-UCode`,
--     and the `LiftStep` `trivial`/`proper` cases.
postulate
  term-uniq : TermUniqStatement

----------------------------------------------------------------------
-- type-uniq  —  complete proof, depends on term-uniq above.
----------------------------------------------------------------------

{-# TERMINATING #-}
type-uniq : TypeUniqStatement

-- (U, U)
type-uniq (TT.is-Ty-U {l = l1} dG) (TT.is-Ty-U {l = l2} _) refl =
  TT.conv-Ty-refl (TT.is-Ty-U {l = l1} dG)

-- (U, Pi) — impossible (erasure heads U vs Pi)
type-uniq (TT.is-Ty-U _) (TT.is-Ty-Pi _ _) ()

-- (U, El a) — case on shape of a
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.Var i} da) ()
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.Pi A' B'} da) eq =
  absurd (no-Pi-HasType da)
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.U l'} da) eq =
  absurd (no-U-HasType da)
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.El l' a'} da) eq =
  absurd (no-El-HasType da)
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.Lam _ _ _} da) ()
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.App _ _ _ _} da) ()
type-uniq (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.PiCode _ _ _} da) ()
type-uniq {G = G} (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.UCode m l'} da) refl =
  -- erase (UCode m l') = R.U l' = R.U l1, so l' = l1.
  -- da : HasType G (UCode m l1) (U l2), so m = l2 by inv + U-inj.
  let r = inv-UCode da
      m≡l2 = U-inj-Ty-T (InvUCode.Tconv r)
  in Eq-transport (\ k -> TT.ConvTy G (T.U l1) (T.El k (T.UCode m l1)))
       m≡l2
       (TT.conv-Ty-sym (TT.conv-Ty-El-UCode {m = m} {l = l1}
                                            (InvUCode.dG r) (InvUCode.h r)))
type-uniq {G = G} (TT.is-Ty-U {l = l1} dG)
          (TT.is-Ty-El {a = T.Lift m k a''} da) eq =
  -- da : HasType G (Lift m k a'') (U l2), so m = l2 by inv + U-inj.
  -- Recurse on (U l1, El k a'').
  let r = inv-Lift da
      m≡l2 = U-inj-Ty-T (InvLift.Tconv r)
      h = InvLift.h r
      da'' = InvLift.da r
      recur : TT.ConvTy G (T.U l1) (T.El k a'')
      recur = type-uniq (TT.is-Ty-U {l = l1} dG)
                        (TT.is-Ty-El {l = k} da'') eq
      shrink : TT.ConvTy G (T.El m (T.Lift m k a'')) (T.El k a'')
      shrink = TT.conv-Ty-El-Lift {m = m} {l = k} h da''
      bridge : TT.ConvTy G (T.U l1) (T.El m (T.Lift m k a''))
      bridge = TT.conv-Ty-trans recur (TT.conv-Ty-sym shrink)
  in Eq-transport (\ j -> TT.ConvTy G (T.U l1) (T.El j (T.Lift m k a'')))
       m≡l2 bridge

-- (Pi, U) — impossible
type-uniq (TT.is-Ty-Pi _ _) (TT.is-Ty-U _) ()

-- (Pi, Pi)
type-uniq (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          (TT.is-Ty-Pi {A = A2} {B = B2} dA2 dB2) eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      cA = type-uniq dA1 dA2 eqA
      dB2' = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA) dB2
      cB = type-uniq dB1 dB2' eqB
  in TT.conv-Ty-Pi cA cB

-- (Pi, El a) — case on shape of a
type-uniq (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          (TT.is-Ty-El {a = T.Var i} da) ()
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.Pi A' B'} da) eq =
  absurd (no-Pi-HasType da)
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.U l'} da) eq =
  absurd (no-U-HasType da)
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.El l' a'} da) eq =
  absurd (no-El-HasType da)
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.Lam _ _ _} da) ()
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.App _ _ _ _} da) ()
type-uniq (TT.is-Ty-Pi dA1 dB1)
          (TT.is-Ty-El {a = T.UCode _ _} da) ()
type-uniq {G = G} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          (TT.is-Ty-El {a = T.PiCode l' a' b'} da) eq =
  -- erase (PiCode l' a' b') = R.Pi (erase a') (erase b').
  -- erase (Pi A1 B1) = R.Pi (erase A1) (erase B1).
  -- So erase A1 = erase a' and erase B1 = erase b'.
  -- da : HasType G (PiCode l' a' b') (U l2). By inv + U-inj, l' = l2.
  let mkSigma eqA eqB = R-Pi-inj eq
      r = inv-PiCode da
      l'≡l2 = U-inj-Ty-T (InvPiCode.Tconv r)
      da' = InvPiCode.da r          -- HasType G a' (U l')
      db' = InvPiCode.db r          -- HasType (extend G (El l' a')) b' (U l')
      a'-IT = TT.is-Ty-El {l = l'} da'
      b'-IT = TT.is-Ty-El {l = l'} db'
      cA : TT.ConvTy G A1 (T.El l' a')
      cA = type-uniq dA1 a'-IT eqA
      b'-IT-inA1 : TT.IsType (TT.extend G A1) (T.El l' b')
      b'-IT-inA1 = TM.ctx-conv-IsType a'-IT dA1 (TT.conv-Ty-sym cA) b'-IT
      cB : TT.ConvTy (TT.extend G A1) B1 (T.El l' b')
      cB = type-uniq dB1 b'-IT-inA1 eqB
      bridge : TT.ConvTy G (T.Pi A1 B1) (T.Pi (T.El l' a') (T.El l' b'))
      bridge = TT.conv-Ty-Pi cA cB
      elPiCode : TT.ConvTy G (T.El l' (T.PiCode l' a' b'))
                              (T.Pi (T.El l' a') (T.El l' b'))
      elPiCode = TT.conv-Ty-El-PiCode {l = l'} da' db'
      result : TT.ConvTy G (T.Pi A1 B1) (T.El l' (T.PiCode l' a' b'))
      result = TT.conv-Ty-trans bridge (TT.conv-Ty-sym elPiCode)
  in Eq-transport (\ j -> TT.ConvTy G (T.Pi A1 B1)
                                     (T.El j (T.PiCode l' a' b')))
       l'≡l2 result
type-uniq {G = G} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          (TT.is-Ty-El {a = T.Lift m k a''} da) eq =
  let r = inv-Lift da
      m≡l2 = U-inj-Ty-T (InvLift.Tconv r)
      h = InvLift.h r
      da'' = InvLift.da r
      recur : TT.ConvTy G (T.Pi A1 B1) (T.El k a'')
      recur = type-uniq (TT.is-Ty-Pi dA1 dB1)
                        (TT.is-Ty-El {l = k} da'') eq
      shrink : TT.ConvTy G (T.El m (T.Lift m k a'')) (T.El k a'')
      shrink = TT.conv-Ty-El-Lift {m = m} {l = k} h da''
      bridge : TT.ConvTy G (T.Pi A1 B1) (T.El m (T.Lift m k a''))
      bridge = TT.conv-Ty-trans recur (TT.conv-Ty-sym shrink)
  in Eq-transport (\ j -> TT.ConvTy G (T.Pi A1 B1)
                                     (T.El j (T.Lift m k a'')))
       m≡l2 bridge

-- (El a, U) — symmetric to (U, El)
type-uniq dA@(TT.is-Ty-El _) dB@(TT.is-Ty-U _) eq =
  TT.conv-Ty-sym (type-uniq dB dA (Eq-sym eq))

-- (El a, Pi) — symmetric to (Pi, El)
type-uniq dA@(TT.is-Ty-El _) dB@(TT.is-Ty-Pi _ _) eq =
  TT.conv-Ty-sym (type-uniq dB dA (Eq-sym eq))

-- (El a1, El a2)
type-uniq {G = G} (TT.is-Ty-El {a = a1} {l = l1} da1)
                  (TT.is-Ty-El {a = a2} {l = l2} da2) eq =
  -- Apply term-uniq to da1, da2.
  case-tu (term-uniq da1 da2 eq)
  where
    case-tu : TermUniqResult G a1 a2 (T.U l1) (T.U l2)
      -> TT.ConvTy G (T.El l1 a1) (T.El l2 a2)
    case-tu (inl (mkSigma cTy ctm)) =
      -- cTy : ConvTy G (U l1) (U l2), so l1 = l2 by U-inj
      -- ctm : ConvTm G a1 a2 (U l1)
      let l1≡l2 = U-inj-Ty-T cTy
          elConv : TT.ConvTy G (T.El l1 a1) (T.El l1 a2)
          elConv = TT.conv-Ty-El {l = l1} ctm
      in Eq-transport (\ k -> TT.ConvTy G (T.El l1 a1) (T.El k a2))
           l1≡l2 elConv
    case-tu (inr cl) =
      let n0 = CommonLift.n₀ cl
          n1 = CommonLift.n₁ cl
          k  = CommonLift.k  cl
          v0 = CommonLift.v₀ cl
          v1 = CommonLift.v₁ cl
          -- A₀≡U : ConvTy G (U l1) (U n0), so l1 = n0
          l1≡n0 = U-inj-Ty-T (CommonLift.A₀≡U cl)
          l2≡n1 = U-inj-Ty-T (CommonLift.A₁≡U cl)
          -- step-a1 : ConvTy G (El l1 a1) (El k v0)
          step-a1 : TT.ConvTy G (T.El l1 a1) (T.El k v0)
          step-a1 = step-from-LiftStep l1 n0 k v0 a1
                      l1≡n0 (CommonLift.u₀≡ cl)
          step-a2 : TT.ConvTy G (T.El l2 a2) (T.El k v1)
          step-a2 = step-from-LiftStep l2 n1 k v1 a2
                      l2≡n1 (CommonLift.u₁≡ cl)
          -- v0 ≡ v1 : U k → El k v0 ≡ El k v1
          v-conv : TT.ConvTy G (T.El k v0) (T.El k v1)
          v-conv = TT.conv-Ty-El {l = k} (CommonLift.v₀≡v₁ cl)
      in TT.conv-Ty-trans step-a1
           (TT.conv-Ty-trans v-conv (TT.conv-Ty-sym step-a2))
      where
        -- Build (El l a) ≡ (El k v) given LiftStep G a m k v (U l)
        -- where l ≡ m.
        step-from-LiftStep : (l m k' : Nat) (v a : T.Expr _)
          -> Eq l m -> LiftStep G a m k' v (T.U l)
          -> TT.ConvTy G (T.El l a) (T.El k' v)
        step-from-LiftStep l m k' v a refl (trivial m≡k' tm) =
          -- l = m, m = k' so l = k'.
          -- tm : ConvTm G a v (U l).  conv-Ty-El gives (El l a) ≡ (El l v).
          -- Transport: (El l v) → (El k' v) via m≡k'.
          Eq-transport (\ j -> TT.ConvTy G (T.El l a) (T.El j v))
            m≡k' (TT.conv-Ty-El {l = l} tm)
        step-from-LiftStep l m k' v a refl (proper k'<m tm) =
          -- l = m, k' < m. tm : ConvTm G a (Lift m k' v) (U l).
          -- conv-Ty-El : (El l a) ≡ (El l (Lift m k' v))
          -- conv-Ty-El-Lift : (El m (Lift m k' v)) ≡ (El k' v)
          let invL = inv-Lift (TM.presup-r-ConvTm tm)
              ELLift : TT.ConvTy G (T.El m (T.Lift m k' v)) (T.El k' v)
              ELLift = TT.conv-Ty-El-Lift {m = m} {l = k'}
                         (InvLift.h invL) (InvLift.da invL)
          in TT.conv-Ty-trans (TT.conv-Ty-El {l = l} tm) ELLift
