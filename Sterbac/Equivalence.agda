{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.Equivalence
--
-- Soundness of erasure (every Tarski derivation maps to a Russell
-- derivation under |·|), plus lift-back machinery and the final
-- equivalence statement.
--
-- This file is postulate-free: every erase-* is a structural
-- recursion on the corresponding Tarski judgement.
------------------------------------------------------------------------

module Sterbac.Equivalence where

open import Sterbac.Basic
import Sterbac.RussellSyntax  as R
import Sterbac.RussellTyping  as RT
import Sterbac.TarskiSyntax   as T
import Sterbac.TarskiTyping   as TT
import Sterbac.Erasure        as E
open import Sterbac.Uniqueness

------------------------------------------------------------------------
-- Context-level erasure
------------------------------------------------------------------------

eraseCtx : {n : Nat} -> TT.Ctx n -> RT.Ctx n
eraseCtx TT.empty        = RT.empty
eraseCtx (TT.extend G A) = RT.extend (eraseCtx G) (E.erase A)

------------------------------------------------------------------------
-- Cumulativity helpers
--
-- We need to lift Russell-side HasType / ConvTm at U_l to U_l' for
-- any l ≤ l', via repeated application of ty-cum / conv-cum.
------------------------------------------------------------------------

infixl 20 _+k_

_+k_ : Nat -> Nat -> Nat
l +k zero    = l
l +k (suc k) = suc (l +k k)

+k-suc-shift : (l k : Nat) -> Eq (suc l +k k) (suc (l +k k))
+k-suc-shift l zero    = refl
+k-suc-shift l (suc k) = Eq-cong suc (+k-suc-shift l k)

-- Le l l' is witnessed by some k with l +k k = l'
diff-le : (l l' : Nat) -> Le l l' -> Sigma Nat (\ k -> Eq (l +k k) l')
diff-le zero    zero     _ = mkSigma 0 refl
diff-le zero    (suc l') _ with diff-le zero l' tt
... | mkSigma k eq = mkSigma (suc k) (Eq-cong suc eq)
diff-le (suc l) zero     ()
diff-le (suc l) (suc l') h with diff-le l l' h
... | mkSigma k eq =
  mkSigma k (Eq-trans (+k-suc-shift l k) (Eq-cong suc eq))

-- cum-by k applies ty-cum k times
cum-by : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} {l : Nat}
       (k : Nat)
     -> RT.HasType G A (R.U l)
     -> RT.HasType G A (R.U (l +k k))
cum-by zero    d = d
cum-by (suc k) d = RT.ty-cum (cum-by k d)

cum-up : {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
       (l l' : Nat) -> Le l l'
     -> RT.HasType G A (R.U l)
     -> RT.HasType G A (R.U l')
cum-up l l' h d with diff-le l l' h
... | mkSigma k refl = cum-by k d

cum-by-Tm : {n : Nat} {G : RT.Ctx n} {M N : R.Expr n} {l : Nat}
          (k : Nat)
        -> RT.ConvTm G M N (R.U l)
        -> RT.ConvTm G M N (R.U (l +k k))
cum-by-Tm zero    d = d
cum-by-Tm (suc k) d = RT.conv-cum (cum-by-Tm k d)

cum-up-Tm : {n : Nat} {G : RT.Ctx n} {M N : R.Expr n}
          (l l' : Nat) -> Le l l'
        -> RT.ConvTm G M N (R.U l)
        -> RT.ConvTm G M N (R.U l')
cum-up-Tm l l' h d with diff-le l l' h
... | mkSigma k refl = cum-by-Tm k d

------------------------------------------------------------------------
-- Lt → Le
------------------------------------------------------------------------

Le-suc-self : (l : Nat) -> Le l (suc l)
Le-suc-self zero    = tt
Le-suc-self (suc l) = Le-suc-self l

Lt-to-Le : {l l' : Nat} -> Lt l l' -> Le l l'
Lt-to-Le {zero}  {suc l'} _ = tt
Lt-to-Le {suc l} {suc l'} h = Lt-to-Le {l} {l'} h

------------------------------------------------------------------------
-- Erasure commutes with context lookup
------------------------------------------------------------------------

lookup-erase : {n : Nat} (G : TT.Ctx n) (i : Fin n)
  -> Eq (RT.lookup (eraseCtx G) i) (E.erase (TT.lookup G i))
lookup-erase (TT.extend G A) fzero    = Eq-sym (E.erase-wk A)
lookup-erase (TT.extend G A) (fsuc i) =
  Eq-trans (Eq-cong R.wkExpr (lookup-erase G i))
           (Eq-sym (E.erase-wk (TT.lookup G i)))

------------------------------------------------------------------------
-- Mutual erasure-soundness
------------------------------------------------------------------------

mutual

  erase-WfCtx : {n : Nat} {G : TT.Ctx n}
    -> TT.WfCtx G
    -> RT.WfCtx (eraseCtx G)
  erase-WfCtx TT.wf-empty         = RT.wf-empty
  erase-WfCtx (TT.wf-extend dA)   = RT.wf-extend (erase-IsType dA)

  erase-IsType : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
    -> TT.IsType G A
    -> RT.IsType (eraseCtx G) (E.erase A)
  erase-IsType (TT.is-Ty-U {l = l} dG) =
    RT.is-Ty-from-U (RT.ty-U {l = l} (erase-WfCtx dG))
  erase-IsType (TT.is-Ty-Pi dA dB) with erase-IsType dA | erase-IsType dB
  ... | RT.is-Ty-from-U {l = la} dA' | RT.is-Ty-from-U {l = lb} dB' =
    let m = max la lb
        dA'' = cum-up la m (Le-max-l la lb) dA'
        dB'' = cum-up lb m (Le-max-r la lb) dB'
    in RT.is-Ty-from-U (RT.ty-Pi dA'' dB'')
  erase-IsType (TT.is-Ty-El {l = l} da) =
    RT.is-Ty-from-U (erase-HasType da)

  erase-HasType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
    -> TT.HasType G M A
    -> RT.HasType (eraseCtx G) (E.erase M) (E.erase A)
  erase-HasType (TT.ty-var {G = G} {i = i} dG) =
    Eq-transport (\ T -> RT.HasType (eraseCtx G) (R.Var i) T)
      (lookup-erase G i)
      (RT.ty-var (erase-WfCtx dG))
  erase-HasType (TT.ty-conv dM dAB) =
    RT.ty-conv (erase-HasType dM) (erase-ConvTy dAB)
  erase-HasType (TT.ty-Lam dA dB db) =
    RT.ty-Lam (erase-IsType dA) (erase-IsType dB) (erase-HasType db)
  erase-HasType (TT.ty-App {G = G} {A = A} {B = B} {c = c} {a = a}
                            dA dB dc da) =
    Eq-transport
      (\ T -> RT.HasType (eraseCtx G)
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.ty-App (erase-IsType dA) (erase-IsType dB)
                 (erase-HasType dc) (erase-HasType da))
  erase-HasType (TT.ty-PiCode {l = l} da db) =
    RT.ty-Pi (erase-HasType da) (erase-HasType db)
  erase-HasType (TT.ty-UCode {m = m} {l = l} dG h) =
    cum-up (suc l) m h (RT.ty-U {l = l} (erase-WfCtx dG))
  erase-HasType (TT.ty-Lift {m = m} {l = l} h da) =
    cum-up l m (Lt-to-Le {l} {m} h) (erase-HasType da)

  erase-ConvTy : {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
    -> TT.ConvTy G A B
    -> RT.ConvTy (eraseCtx G) (E.erase A) (E.erase B)
  erase-ConvTy (TT.conv-Ty-refl dA) =
    RT.conv-Ty-refl (erase-IsType dA)
  erase-ConvTy (TT.conv-Ty-sym d) =
    RT.conv-Ty-sym (erase-ConvTy d)
  erase-ConvTy (TT.conv-Ty-trans d1 d2) =
    RT.conv-Ty-trans (erase-ConvTy d1) (erase-ConvTy d2)
  erase-ConvTy (TT.conv-Ty-Pi dA dB) =
    RT.conv-Ty-Pi (erase-ConvTy dA) (erase-ConvTy dB)
  erase-ConvTy (TT.conv-Ty-El daa') =
    RT.conv-Ty-from-U (erase-ConvTm daa')
  erase-ConvTy (TT.conv-Ty-El-UCode {l = l} dG h) =
    RT.conv-Ty-refl (RT.is-Ty-from-U (RT.ty-U {l = l} (erase-WfCtx dG)))
  erase-ConvTy (TT.conv-Ty-El-PiCode {l = l} da db) =
    RT.conv-Ty-refl
      (RT.is-Ty-from-U (RT.ty-Pi (erase-HasType da) (erase-HasType db)))
  erase-ConvTy (TT.conv-Ty-El-Lift {l = l} h da) =
    RT.conv-Ty-refl (RT.is-Ty-from-U (erase-HasType da))

  erase-ConvTm : {n : Nat} {G : TT.Ctx n} {M N A : T.Expr n}
    -> TT.ConvTm G M N A
    -> RT.ConvTm (eraseCtx G) (E.erase M) (E.erase N) (E.erase A)
  erase-ConvTm (TT.conv-refl dM) =
    RT.conv-refl (erase-HasType dM)
  erase-ConvTm (TT.conv-sym d) =
    RT.conv-sym (erase-ConvTm d)
  erase-ConvTm (TT.conv-trans d1 d2) =
    RT.conv-trans (erase-ConvTm d1) (erase-ConvTm d2)
  erase-ConvTm (TT.conv-conv dMN dAB) =
    RT.conv-conv (erase-ConvTm dMN) (erase-ConvTy dAB)
  erase-ConvTm (TT.conv-cong-Lam-body dA dB db) =
    RT.conv-cong-Lam-body (erase-IsType dA) (erase-IsType dB)
                          (erase-ConvTm db)
  erase-ConvTm (TT.conv-cong-Lam-Ty dA dB db) =
    RT.conv-cong-Lam-Ty (erase-ConvTy dA) (erase-ConvTy dB)
                        (erase-HasType db)
  erase-ConvTm (TT.conv-cong-App-fun {G = G} {A = A} {B = B}
                                      {c = c} {c' = c'} {a = a}
                                      dA dB dc da) =
    Eq-transport
      (\ T -> RT.ConvTm (eraseCtx G)
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
              (R.App (E.erase A) (E.erase B) (E.erase c') (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-fun (erase-IsType dA) (erase-IsType dB)
                            (erase-ConvTm dc) (erase-HasType da))
  erase-ConvTm (TT.conv-cong-App-arg {G = G} {A = A} {B = B}
                                      {c = c} {a = a} {a' = a'}
                                      dA dB dc da Bsubst-conv) =
    Eq-transport
      (\ T -> RT.ConvTm (eraseCtx G)
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a')) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-arg (erase-IsType dA) (erase-IsType dB)
                            (erase-HasType dc) (erase-ConvTm da)
                            (Eq-transport
                              (\ X -> RT.ConvTy (eraseCtx G) X _)
                              (E.erase-subst1 B a)
                              (Eq-transport
                                (\ Y -> RT.ConvTy (eraseCtx G) _ Y)
                                (E.erase-subst1 B a')
                                (erase-ConvTy Bsubst-conv))))
  erase-ConvTm (TT.conv-cong-App-Ty {G = G} {A = A} {A' = A'}
                                     {B = B} {B' = B'} {c = c} {a = a}
                                     dA dB dc da) =
    Eq-transport
      (\ T -> RT.ConvTm (eraseCtx G)
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
              (R.App (E.erase A') (E.erase B') (E.erase c) (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-Ty (erase-ConvTy dA) (erase-ConvTy dB)
                           (erase-HasType dc) (erase-HasType da))
  erase-ConvTm (TT.conv-cong-PiCode {l = l} daa' dbb') =
    RT.conv-cong-Pi (erase-ConvTm daa') (erase-ConvTm dbb')
  erase-ConvTm (TT.conv-cong-Lift {m = m} {l = l} h daa') =
    cum-up-Tm l m (Lt-to-Le {l} {m} h) (erase-ConvTm daa')
  erase-ConvTm (TT.conv-beta {G = G} {A = A} {B = B} {b = b} {a = a}
                              dA dB db da) =
    Eq-transport
      (\ T -> RT.ConvTm (eraseCtx G)
              (R.App (E.erase A) (E.erase B)
                     (R.Lam (E.erase A) (E.erase B) (E.erase b)) (E.erase a))
              (E.erase (T.subst1 b a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (Eq-transport
        (\ M -> RT.ConvTm (eraseCtx G)
                (R.App (E.erase A) (E.erase B)
                       (R.Lam (E.erase A) (E.erase B) (E.erase b)) (E.erase a))
                M (R.subst1 (E.erase B) (E.erase a)))
        (Eq-sym (E.erase-subst1 b a))
        (RT.conv-beta (erase-IsType dA) (erase-IsType dB)
                      (erase-HasType db) (erase-HasType da)))
  erase-ConvTm (TT.conv-eta {G = G} {A = A} {B = B} {c = c} dA dB dc) =
    let body-eq = Eq-cong4 R.App
                    (E.erase-wk A)
                    (E.erase-ren (liftRen wkRen) B)
                    (E.erase-wk c)
                    (refl {x = R.Var fzero})
        lam-eq  = Eq-cong (R.Lam (E.erase A) (E.erase B)) body-eq
        rhs     = RT.conv-eta (erase-IsType dA) (erase-IsType dB)
                              (erase-HasType dc)
    in Eq-transport
        (\ M -> RT.ConvTm (eraseCtx G) (E.erase c) M
                (R.Pi (E.erase A) (E.erase B)))
        (Eq-sym lam-eq) rhs
  erase-ConvTm (TT.conv-Lift-Lift {nu = nu} {m = m} {l = l} hlm hmnu da) =
    RT.conv-refl (cum-up l nu
      (Le-trans l m nu (Lt-to-Le {l} {m} hlm) (Lt-to-Le {m} {nu} hmnu))
      (erase-HasType da))
  erase-ConvTm (TT.conv-Lift-UCode {m = m} {l = l} {nu = nu} dG hnul hlm) =
    RT.conv-refl (cum-up (suc nu) m
      (Le-trans (suc nu) l m hnul (Lt-to-Le {l} {m} hlm))
      (RT.ty-U {l = nu} (erase-WfCtx dG)))
  erase-ConvTm (TT.conv-Lift-PiCode {m = m} {l = l} h da db) =
    RT.conv-refl (cum-up l m (Lt-to-Le {l} {m} h)
      (RT.ty-Pi (erase-HasType da) (erase-HasType db)))

------------------------------------------------------------------------
-- Lift-back: existence
--
-- A Russell derivation lifts to *some* Tarski derivation with the
-- prescribed erasure. We package the lift as a record carrying the
-- chosen Tarski context, the chosen Tarski terms, the erasure
-- equalities, and the Tarski derivation.
------------------------------------------------------------------------

record LiftIsType {n : Nat} (G : RT.Ctx n) (A : R.Expr n) : Set where
  constructor mkLiftIsType
  field
    G' : TT.Ctx n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    der : TT.IsType G' A'

record LiftHasType {n : Nat} (G : RT.Ctx n) (M A : R.Expr n) : Set where
  constructor mkLiftHasType
  field
    G' : TT.Ctx n
    M' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    A≡ : Eq (E.erase A') A
    der : TT.HasType G' M' A'

record LiftConvTy {n : Nat} (G : RT.Ctx n) (A B : R.Expr n) : Set where
  constructor mkLiftConvTy
  field
    G' : TT.Ctx n
    A' : T.Expr n
    B' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    B≡ : Eq (E.erase B') B
    der : TT.ConvTy G' A' B'

record LiftConvTm {n : Nat} (G : RT.Ctx n) (M N A : R.Expr n) : Set where
  constructor mkLiftConvTm
  field
    G' : TT.Ctx n
    M' : T.Expr n
    N' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    N≡ : Eq (E.erase N') N
    A≡ : Eq (E.erase A') A
    der : TT.ConvTm G' M' N' A'

postulate
  lift-IsType :
    {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
    -> RT.IsType G A
    -> LiftIsType G A

  lift-HasType :
    {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
    -> RT.HasType G M A
    -> LiftHasType G M A

  lift-ConvTy :
    {n : Nat} {G : RT.Ctx n} {A B : R.Expr n}
    -> RT.ConvTy G A B
    -> LiftConvTy G A B

  lift-ConvTm :
    {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n}
    -> RT.ConvTm G M N A
    -> LiftConvTm G M N A

------------------------------------------------------------------------
-- Final theorem record
------------------------------------------------------------------------

record Equivalence : Set₁ where
  field
    sound-IsType  : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
                  -> TT.IsType G A -> RT.IsType (eraseCtx G) (E.erase A)
    sound-HasType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
                  -> TT.HasType G M A
                  -> RT.HasType (eraseCtx G) (E.erase M) (E.erase A)
    lifts-IsType  : {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
                  -> RT.IsType G A -> LiftIsType G A
    lifts-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
                  -> RT.HasType G M A -> LiftHasType G M A
    uniq-Ty : TypeUniqStatement
    uniq-Tm : TermUniqStatement

equivalence : Equivalence
equivalence = record
  { sound-IsType  = erase-IsType
  ; sound-HasType = erase-HasType
  ; lifts-IsType  = lift-IsType
  ; lifts-HasType = lift-HasType
  ; uniq-Ty       = type-uniq
  ; uniq-Tm       = term-uniq
  }
