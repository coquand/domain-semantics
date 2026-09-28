{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.EraseDeriv
--
-- Paper Lemma 4.6 (correction of erasure): every Tarski derivation maps
-- to a Russell derivation under |·|.  Structural recursion on the
-- Tarski judgement; independent of the uniqueness lemma and of any
-- assumption.  (Moved out of ERTUU.Equivalence so that the model
-- of ERTUU.Model can use it to prove the injectivity facts the
-- uniqueness lemma relies on.)
------------------------------------------------------------------------

module ERTUU.EraseDeriv where

open import ERTUU.Basic
import ERTUU.RussellSyntax  as R
import ERTUU.RussellTyping  as RT
import ERTUU.TarskiSyntax   as T
import ERTUU.TarskiTyping   as TT
import ERTUU.Erasure        as E
import ERTUU.TarskiMeta     as TM
import ERTUU.RussellMeta    as RM

------------------------------------------------------------------------
-- Russell context erasure
------------------------------------------------------------------------

eraseCtx : {n : Nat} -> TT.Ctx n -> RT.Ctx n
eraseCtx TT.empty        = RT.empty
eraseCtx (TT.extend G A) = RT.extend (eraseCtx G) (E.erase A)

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
  erase-IsType (TT.is-Ty-U dG) =
    RT.is-Ty-from-U (RT.ty-U (erase-WfCtx dG))
  erase-IsType (TT.is-Ty-Pi dA dB) with erase-IsType dA | erase-IsType dB
  ... | RT.is-Ty-from-U dA' | RT.is-Ty-from-U dB' =
    RT.is-Ty-from-U (RT.ty-Pi dA' dB')
  erase-IsType (TT.is-Ty-El da) =
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
  erase-HasType (TT.ty-PiCode da db) =
    RT.ty-Pi (erase-HasType da) (erase-HasType db)
  erase-HasType (TT.ty-UCode dG) = RT.ty-U (erase-WfCtx dG)

  erase-ConvTy : {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
    -> TT.ConvTy G A B
    -> RT.ConvTy (eraseCtx G) (E.erase A) (E.erase B)
  erase-ConvTy (TT.conv-Ty-refl dA) =
    RT.conv-Ty-refl (erase-IsType dA)
  erase-ConvTy (TT.conv-Ty-sym d) =
    RT.conv-Ty-sym (erase-ConvTy d)
  erase-ConvTy (TT.conv-Ty-trans d1 d2) =
    RT.conv-Ty-trans (erase-ConvTy d1) (erase-ConvTy d2)
  erase-ConvTy (TT.conv-Ty-Pi _ dA dB) =
    RM.mk-conv-Ty-Pi (erase-ConvTy dA) (erase-ConvTy dB)
  erase-ConvTy (TT.conv-Ty-El daa') =
    RT.conv-Ty-from-U (erase-ConvTm daa')
  erase-ConvTy (TT.conv-Ty-El-UCode dG) =
    RT.conv-Ty-refl (RT.is-Ty-from-U (RT.ty-U (erase-WfCtx dG)))
  erase-ConvTy (TT.conv-Ty-El-PiCode da db) =
    RT.conv-Ty-refl
      (RT.is-Ty-from-U (RT.ty-Pi (erase-HasType da) (erase-HasType db)))
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
                          (RM.presup-l-ConvTm (erase-ConvTm db)) (erase-ConvTm db)
  erase-ConvTm (TT.conv-cong-Lam-Ty _ dA dB db) =
    RM.mk-conv-cong-Lam-Ty (erase-ConvTy dA) (erase-ConvTy dB)
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
                                     _ dA dB dc da) =
    Eq-transport
      (\ T -> RT.ConvTm (eraseCtx G)
              (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
              (R.App (E.erase A') (E.erase B') (E.erase c) (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RM.mk-conv-cong-App-Ty (erase-ConvTy dA) (erase-ConvTy dB)
                           (erase-HasType dc) (erase-HasType da))
  erase-ConvTm (TT.conv-cong-PiCode _ daa' dbb') =
    RM.mk-conv-cong-Pi (erase-ConvTm daa') (erase-ConvTm dbb')
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