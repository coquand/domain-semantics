{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Uniqueness
--
-- Paper Lemma 4.10 for U : U.  With a single universe the erasure
-- never identifies two terms with different heads (the only term
-- erasing to U is UCode, the only one erasing to Π is PiCode), so the
-- "common lift" alternative of the cumulative case disappears:
--
--   type-uniq : A, B types,  |A| = |B|        ->  A = B
--   term-uniq : u₀ : A₀, u₁ : A₁, |u₀| = |u₁|  ->  A₀ = A₁  and  u₀ = u₁ : A₀
--   uniq-El   : B type, a : U,  |B| = |a|      ->  B = El a
--
-- Structural recursion on the (implicit) Tarski expressions.  No
-- property of conversion (injectivity, no-confusion) is used.
------------------------------------------------------------------------

module ERTUU.Uniqueness where

open import ERTUU.Basic
import ERTUU.RussellSyntax  as R
import ERTUU.TarskiSyntax   as T
import ERTUU.TarskiTyping   as TT
import ERTUU.Erasure        as E
import ERTUU.TarskiMeta     as TM
import ERTUU.TarskiMetaCong as TMC

------------------------------------------------------------------------
-- Statements
------------------------------------------------------------------------

TypeUniqStatement : Set
TypeUniqStatement =
  {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
  -> TT.IsType G A -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.ConvTy G A B

TermUniqResult : {n : Nat} -> TT.Ctx n -> T.Expr n -> T.Expr n -> T.Expr n -> T.Expr n -> Set
TermUniqResult G u₀ u₁ A₀ A₁ = Pair (TT.ConvTy G A₀ A₁) (TT.ConvTm G u₀ u₁ A₀)

TermUniqStatement : Set
TermUniqStatement =
  {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ : T.Expr n}
  -> TT.HasType G u₀ A₀ -> TT.HasType G u₁ A₁
  -> Eq (E.erase u₀) (E.erase u₁)
  -> TermUniqResult G u₀ u₁ A₀ A₁

extract-conv-same : {n : Nat} {G : TT.Ctx n} {u₀ u₁ A : T.Expr n}
  -> TermUniqResult G u₀ u₁ A A -> TT.ConvTm G u₀ u₁ A
extract-conv-same r = snd r

------------------------------------------------------------------------
-- Inversion (peeling ty-conv)
------------------------------------------------------------------------

record InvPiCode {n : Nat} (G : TT.Ctx n) (a : T.Expr n) (b : T.Expr (suc n))
                 (Ty : T.Expr n) : Set where
  constructor mkInvPiCode
  field
    da : TT.HasType G a T.U
    db : TT.HasType (TT.extend G (T.El a)) b T.U
    Tconv : TT.ConvTy G T.U Ty

record InvUCode {n : Nat} (G : TT.Ctx n) (Ty : T.Expr n) : Set where
  constructor mkInvUCode
  field
    dG : TT.WfCtx G
    Tconv : TT.ConvTy G T.U Ty

inv-PiCode : {n : Nat} {G : TT.Ctx n} {a : T.Expr n} {b : T.Expr (suc n)} {Ty : T.Expr n}
  -> TT.HasType G (T.PiCode a b) Ty -> InvPiCode G a b Ty
inv-PiCode (TT.ty-PiCode da db) =
  mkInvPiCode da db (TT.conv-Ty-refl (TT.is-Ty-U (TM.typing-WfCtx da)))
inv-PiCode (TT.ty-conv d c) =
  let r = inv-PiCode d
  in mkInvPiCode (InvPiCode.da r) (InvPiCode.db r) (TT.conv-Ty-trans (InvPiCode.Tconv r) c)

inv-UCode : {n : Nat} {G : TT.Ctx n} {Ty : T.Expr n}
  -> TT.HasType G T.UCode Ty -> InvUCode G Ty
inv-UCode (TT.ty-UCode dG) = mkInvUCode dG (TT.conv-Ty-refl (TT.is-Ty-U dG))
inv-UCode (TT.ty-conv d c) =
  let r = inv-UCode d
  in mkInvUCode (InvUCode.dG r) (TT.conv-Ty-trans (InvUCode.Tconv r) c)

-- Types are not terms.
no-Pi-HasType : {n : Nat} {G : TT.Ctx n} {A : T.Expr n} {B : T.Expr (suc n)} {Ty : T.Expr n}
  -> TT.HasType G (T.Pi A B) Ty -> Empty
no-Pi-HasType (TT.ty-conv d _) = no-Pi-HasType d

no-U-HasType : {n : Nat} {G : TT.Ctx n} {Ty : T.Expr n}
  -> TT.HasType G T.U Ty -> Empty
no-U-HasType (TT.ty-conv d _) = no-U-HasType d

no-El-HasType : {n : Nat} {G : TT.Ctx n} {a : T.Expr n} {Ty : T.Expr n}
  -> TT.HasType G (T.El a) Ty -> Empty
no-El-HasType (TT.ty-conv d _) = no-El-HasType d

------------------------------------------------------------------------
-- Russell constructor injectivity
------------------------------------------------------------------------

R-Pi-inj : {n : Nat} {A A' : R.Expr n} {B B' : R.Expr (suc n)}
  -> Eq (R.Pi A B) (R.Pi A' B') -> Pair (Eq A A') (Eq B B')
R-Pi-inj refl = mkSigma refl refl

R-Lam-inj : {n : Nat} {A A' : R.Expr n} {B B' b b' : R.Expr (suc n)}
  -> Eq (R.Lam A B b) (R.Lam A' B' b') -> Pair (Eq A A') (Pair (Eq B B') (Eq b b'))
R-Lam-inj refl = mkSigma refl (mkSigma refl refl)

R-App-inj : {n : Nat} {A A' c c' a a' : R.Expr n} {B B' : R.Expr (suc n)}
  -> Eq (R.App A B c a) (R.App A' B' c' a')
  -> Pair (Eq A A') (Pair (Eq B B') (Pair (Eq c c') (Eq a a')))
R-App-inj refl = mkSigma refl (mkSigma refl (mkSigma refl refl))

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

-- moving the right-hand type along a conversion
conv-right : {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ B : T.Expr n}
  -> TermUniqResult G u₀ u₁ A₀ A₁ -> TT.ConvTy G A₁ B -> TermUniqResult G u₀ u₁ A₀ B
conv-right (mkSigma cTy ctm) c = mkSigma (TT.conv-Ty-trans cTy c) ctm

term-uniq : TermUniqStatement
type-uniq : TypeUniqStatement
uniq-El : {n : Nat} {G : TT.Ctx n} {B : T.Expr n} {a : T.Expr n}
  -> TT.IsType G B -> TT.HasType G a T.U
  -> Eq (E.erase B) (E.erase a)
  -> TT.ConvTy G B (T.El a)

-- ty-conv peeling
term-uniq (TT.ty-conv d c) dM₁ eq =
  let mkSigma cTy ctm = term-uniq d dM₁ eq
  in mkSigma (TT.conv-Ty-trans (TT.conv-Ty-sym c) cTy) (TT.conv-conv ctm c)
-- (one clause per left head, so that every clause holds definitionally)
term-uniq dM₀@(TT.ty-var _)        (TT.ty-conv d c) eq = conv-right (term-uniq dM₀ d eq) c
term-uniq dM₀@(TT.ty-Lam _ _ _)    (TT.ty-conv d c) eq = conv-right (term-uniq dM₀ d eq) c
term-uniq dM₀@(TT.ty-App _ _ _ _)  (TT.ty-conv d c) eq = conv-right (term-uniq dM₀ d eq) c
term-uniq dM₀@(TT.ty-PiCode _ _)   (TT.ty-conv d c) eq = conv-right (term-uniq dM₀ d eq) c
term-uniq dM₀@(TT.ty-UCode _)      (TT.ty-conv d c) eq = conv-right (term-uniq dM₀ d eq) c

-- (Var, Var)
term-uniq (TT.ty-var {i = i} dG) (TT.ty-var dG') refl =
  mkSigma (TT.conv-Ty-refl (TM.wfCtx-lookup dG i)) (TT.conv-refl (TT.ty-var dG))

-- (Lam, Lam)
term-uniq {G = G} (TT.ty-Lam {A = A1} {B = B1} {b = b1} dA1 dB1 db1)
                  (TT.ty-Lam {A = A2} {B = B2} {b = b2} dA2 dB2 db2) eq =
  let mkSigma eqA (mkSigma eqB eqb) = R-Lam-inj eq
      cA = type-uniq dA1 dA2 eqA
      dB2' = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA) dB2
      db2' = TM.ctx-conv-HasType dA2 dA1 (TT.conv-Ty-sym cA) db2
      cB = type-uniq dB1 dB2' eqB
      db2'' = TT.ty-conv db2' (TT.conv-Ty-sym cB)
      cb = extract-conv-same (term-uniq db1 db2'' eqb)
      lam-body-conv = TT.conv-cong-Lam-body dA1 dB1 cb
      lam-Ty-conv = TM.mk-conv-cong-Lam-Ty cA cB (TM.presup-r-ConvTm cb)
  in mkSigma (TM.mk-conv-Ty-Pi cA cB) (TT.conv-trans lam-body-conv lam-Ty-conv)

-- (App, App)
term-uniq {G = G} (TT.ty-App {A = A1} {B = B1} {c = c1} {a = a1} dA1 dB1 dc1 da1)
                  (TT.ty-App {A = A2} {B = B2} {c = c2} {a = a2} dA2 dB2 dc2 da2) eq =
  let mkSigma eqA (mkSigma eqB (mkSigma eqc eqa)) = R-App-inj eq
      cA = type-uniq dA1 dA2 eqA
      dB2'  = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA) dB2
      cB    = type-uniq dB1 dB2' eqB
      da2-c = TT.ty-conv da2 (TT.conv-Ty-sym cA)
      dc2-c = TT.ty-conv dc2 (TT.conv-Ty-sym (TM.mk-conv-Ty-Pi cA cB))
      ca = extract-conv-same (term-uniq da1 da2-c eqa)
      cc = extract-conv-same (term-uniq dc1 dc2-c eqc)
      BsubstCong = TMC.subst1-cong-Ty ca dA1 dB1
      step1 = TT.conv-cong-App-fun dA1 dB1 cc da1
      step2 = TT.conv-cong-App-arg dA1 dB1 dc2-c ca BsubstCong
      step3 = TT.conv-conv (TM.mk-conv-cong-App-Ty cA cB dc2-c da2-c)
                           (TT.conv-Ty-sym BsubstCong)
      subst1-tyConv =
        TT.conv-Ty-trans BsubstCong
          (TM.subst-ConvTy (TM.subst1-WtSub dA1 da2-c) (TM.isType-WfCtx dA1) cB)
  in mkSigma subst1-tyConv (TT.conv-trans step1 (TT.conv-trans step2 step3))

-- (PiCode, PiCode)
term-uniq {G = G} (TT.ty-PiCode {a = a1} {b = b1} da1 db1)
                  (TT.ty-PiCode {a = a2} {b = b2} da2 db2) eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      ca = extract-conv-same (term-uniq da1 da2 eqA)
      db2' = TM.ctx-conv-HasType (TT.is-Ty-El da2) (TT.is-Ty-El da1)
               (TT.conv-Ty-sym (TT.conv-Ty-El ca)) db2
      cb = extract-conv-same (term-uniq db1 db2' eqB)
  in mkSigma (TT.conv-Ty-refl (TT.is-Ty-U (TM.typing-WfCtx da1)))
             (TT.conv-cong-PiCode da1 ca cb)

-- (UCode, UCode)
term-uniq (TT.ty-UCode dG) (TT.ty-UCode _) refl =
  mkSigma (TT.conv-Ty-refl (TT.is-Ty-U dG)) (TT.conv-refl (TT.ty-UCode dG))

-- different heads: impossible by erasure
term-uniq (TT.ty-var _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-var _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-var _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-var _) (TT.ty-UCode _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-var _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-UCode _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-var _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-UCode _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-var _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-UCode _) ()
term-uniq (TT.ty-UCode _) (TT.ty-var _) ()
term-uniq (TT.ty-UCode _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-UCode _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-UCode _) (TT.ty-PiCode _ _) ()

-- type-uniq
type-uniq (TT.is-Ty-U dG) (TT.is-Ty-U _) refl = TT.conv-Ty-refl (TT.is-Ty-U dG)
type-uniq (TT.is-Ty-U _) (TT.is-Ty-Pi _ _) ()
type-uniq (TT.is-Ty-Pi _ _) (TT.is-Ty-U _) ()
type-uniq (TT.is-Ty-Pi dA1 dB1) (TT.is-Ty-Pi dA2 dB2) eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      cA = type-uniq dA1 dA2 eqA
      dB2' = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA) dB2
      cB = type-uniq dB1 dB2' eqB
  in TM.mk-conv-Ty-Pi cA cB
type-uniq dB@(TT.is-Ty-U _) (TT.is-Ty-El da) eq = uniq-El dB da eq
type-uniq dB@(TT.is-Ty-Pi _ _) (TT.is-Ty-El da) eq = uniq-El dB da eq
type-uniq (TT.is-Ty-El da) dB@(TT.is-Ty-U _) eq =
  TT.conv-Ty-sym (uniq-El dB da (Eq-sym eq))
type-uniq (TT.is-Ty-El da) dB@(TT.is-Ty-Pi _ _) eq =
  TT.conv-Ty-sym (uniq-El dB da (Eq-sym eq))
type-uniq dB@(TT.is-Ty-El _) (TT.is-Ty-El da) eq = uniq-El dB da eq

-- uniq-El: B = El a1
uniq-El (TT.is-Ty-El da1) da2 eq =
  TT.conv-Ty-El (extract-conv-same (term-uniq da1 da2 eq))
-- B = U: a must be UCode
uniq-El {a = T.Var i} (TT.is-Ty-U dG) da ()
uniq-El {a = T.Pi A' B'} (TT.is-Ty-U dG) da eq = absurd (no-Pi-HasType da)
uniq-El {a = T.U} (TT.is-Ty-U dG) da eq = absurd (no-U-HasType da)
uniq-El {a = T.El a'} (TT.is-Ty-U dG) da eq = absurd (no-El-HasType da)
uniq-El {a = T.Lam _ _ _} (TT.is-Ty-U dG) da ()
uniq-El {a = T.App _ _ _ _} (TT.is-Ty-U dG) da ()
uniq-El {a = T.PiCode _ _} (TT.is-Ty-U dG) da ()
uniq-El {a = T.UCode} (TT.is-Ty-U dG) da refl =
  TT.conv-Ty-sym (TT.conv-Ty-El-UCode dG)
-- B = Pi A1 B1: a must be PiCode
uniq-El {a = T.Var i} (TT.is-Ty-Pi dA1 dB1) da ()
uniq-El {a = T.Pi A' B'} (TT.is-Ty-Pi dA1 dB1) da eq = absurd (no-Pi-HasType da)
uniq-El {a = T.U} (TT.is-Ty-Pi dA1 dB1) da eq = absurd (no-U-HasType da)
uniq-El {a = T.El a'} (TT.is-Ty-Pi dA1 dB1) da eq = absurd (no-El-HasType da)
uniq-El {a = T.Lam _ _ _} (TT.is-Ty-Pi dA1 dB1) da ()
uniq-El {a = T.App _ _ _ _} (TT.is-Ty-Pi dA1 dB1) da ()
uniq-El {a = T.UCode} (TT.is-Ty-Pi dA1 dB1) da ()
uniq-El {G = G} {a = T.PiCode a' b'} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1) da eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      r = inv-PiCode da
      da' = InvPiCode.da r
      db' = InvPiCode.db r
      a'-IT = TT.is-Ty-El da'
      cA : TT.ConvTy G A1 (T.El a')
      cA = uniq-El dA1 da' eqA
      db'-inA1 : TT.HasType (TT.extend G A1) b' T.U
      db'-inA1 = TM.ctx-conv-HasType a'-IT dA1 (TT.conv-Ty-sym cA) db'
      cB : TT.ConvTy (TT.extend G A1) B1 (T.El b')
      cB = uniq-El dB1 db'-inA1 eqB
  in TT.conv-Ty-trans (TM.mk-conv-Ty-Pi cA cB)
       (TT.conv-Ty-sym (TT.conv-Ty-El-PiCode da' db'))
