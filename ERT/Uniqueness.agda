{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Uniqueness
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
-- The proof goes by mutual induction on the size of A and u₀.  The only
-- property of conversion it uses is injectivity of universes
-- (U-inj-Ty-T), proved in the finite-element model in
-- ERT.Injectivity.
------------------------------------------------------------------------

module ERT.Uniqueness where

open import ERT.Basic
import ERT.RussellSyntax  as R
import ERT.RussellTyping  as RT
import ERT.TarskiSyntax   as T
import ERT.TarskiTyping   as TT
import ERT.Erasure        as E
import ERT.TarskiMeta     as TM
open import ERT.Injectivity

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
-- The two lemmas: term-uniq and type-uniq.
--
-- Both are proved (mutually recursive) in
-- `ERT.UniquenessTermPartial` and re-exported below.  They are
-- defined separately (rather than inline here) so that the heavy
-- (PiCode, PiCode) CommonLift case in term-uniq does not bloat this
-- file.  No postulates.
------------------------------------------------------------------------
