{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.EraseDeriv
--
-- Lemma 4.6 (sterbac1.pdf; bcde.pdf App. B): every T_T derivation
-- erases to a T_R derivation.  Structural recursion on the derivation.
-- The Tarski code formers erase to universe rules of the cumulative
-- Russell system (U^m_l ↦ U_l : U_m, ↑^m_l a ↦ cumulativity), the
-- decoding and lift equations to reflexivity, and the level-equality
-- rules of the codes to conv-U-lvl or to reflexivity.
------------------------------------------------------------------------

module BCDE4.EraseDeriv where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax as R
import BCDE4.RussellTyping as RT
import BCDE4.TarskiSyntax  as T
import BCDE4.TarskiTyping  as TT
import BCDE4.Erasure       as E
import BCDE4.RussellMeta   as RM

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

eraseCtx : {n : Nat} -> TT.Ctx n -> RT.Ctx n
eraseCtx (TT.empty Th)   = RT.empty Th
eraseCtx (TT.extend G A) = RT.extend (eraseCtx G) (E.erase A)

lctx-erase : {n : Nat} (G : TT.Ctx n) -> Eq (RT.lctx (eraseCtx G)) (TT.lctx G)
lctx-erase (TT.empty Th)   = refl
lctx-erase (TT.extend G A) = lctx-erase G

eraseCtx-addC : {n : Nat} (G : TT.Ctx n) (c : Constr) ->
  Eq (eraseCtx (TT.addC G c)) (RT.addC (eraseCtx G) c)
eraseCtx-addC (TT.empty Th)   c = refl
eraseCtx-addC (TT.extend G A) c = Eq-cong (\ X -> RT.extend X (E.erase A)) (eraseCtx-addC G c)

eraseCtx-addL : {n : Nat} (G : TT.Ctx n) -> Eq (eraseCtx (TT.addL G)) (RT.addL (eraseCtx G))
eraseCtx-addL (TT.empty Th)   = refl
eraseCtx-addL (TT.extend G A) = Eq-cong2 RT.extend (eraseCtx-addL G) (E.erase-lshift A)

lookup-erase : {n : Nat} (G : TT.Ctx n) (i : Fin n)
  -> Eq (RT.lookup (eraseCtx G) i) (E.erase (TT.lookup G i))
lookup-erase (TT.extend G A) fzero    = Eq-sym (E.erase-wk A)
lookup-erase (TT.extend G A) (fsuc i) =
  Eq-trans (Eq-cong R.wkExpr (lookup-erase G i)) (Eq-sym (E.erase-wk (TT.lookup G i)))

-- the level facts of a Tarski context hold in its erasure
lv : {n : Nat} (G : TT.Ctx n) {P : LCtx -> Set} -> P (TT.lctx G) -> P (RT.lctx (eraseCtx G))
lv G {P} p = Eq-transport P (Eq-sym (lctx-erase G)) p

-- moving a judgement along a context equation
ctx : {n : Nat} {X Y : RT.Ctx n} (P : RT.Ctx n -> Set) -> Eq X Y -> P Y -> P X
ctx P e p = Eq-transport P (Eq-sym e) p

------------------------------------------------------------------------
-- Erasure of derivations
------------------------------------------------------------------------

mutual

  erase-WfCtx : {n : Nat} {G : TT.Ctx n} -> TT.WfCtx G -> RT.WfCtx (eraseCtx G)
  erase-WfCtx TT.wf-empty       = RT.wf-empty
  erase-WfCtx (TT.wf-extend dA) = RT.wf-extend (erase-IsType dA)

  erase-IsType : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
    -> TT.IsType G A -> RT.IsType (eraseCtx G) (E.erase A)
  erase-IsType (TT.is-U dG)     = RM.isType-U (erase-WfCtx dG)
  erase-IsType (TT.is-El da)    = RT.is-Ty-from-U (erase-HasType da)
  erase-IsType (TT.is-Pi dA dB) = RT.is-Pi (erase-IsType dA) (erase-IsType dB)
  erase-IsType (TT.is-Grd {G = G} {c = c} {A = A} dG dA) =
    RT.is-Grd (erase-WfCtx dG) (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
  erase-IsType (TT.is-LPi {G = G} {A = A} dG dA) =
    RT.is-LPi (erase-WfCtx dG) (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
  erase-IsType (TT.is-Emp dG)   = RM.isType-Emp (erase-WfCtx dG)

  erase-HasType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
    -> TT.HasType G M A -> RT.HasType (eraseCtx G) (E.erase M) (E.erase A)
  erase-HasType (TT.ty-var {G = G} {i = i} dG) =
    Eq-transport (\ T -> RT.HasType (eraseCtx G) (R.Var i) T) (lookup-erase G i) (RT.ty-var (erase-WfCtx dG))
  erase-HasType (TT.ty-conv dM dAB) = RT.ty-conv (erase-HasType dM) (erase-ConvTy dAB)
  erase-HasType (TT.ty-Lam dA dB db) =
    RT.ty-Lam (erase-IsType dA) (erase-IsType dB) (erase-HasType db)
  erase-HasType (TT.ty-App {G = G} {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    Eq-transport (\ T -> RT.HasType (eraseCtx G) (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.ty-App (erase-IsType dA) (erase-IsType dB) (erase-HasType dc) (erase-HasType da))
  erase-HasType (TT.ty-GLam {G = G} {c = c} {A = A} {t = t} dG dA dt) =
    RT.ty-GLam (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (ctx (\ X -> RT.HasType X (E.erase t) (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-HasType dt))
  erase-HasType (TT.ty-LLam {G = G} {A = A} {u = u} dG dA du) =
    RT.ty-LLam (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
      (ctx (\ X -> RT.HasType X (E.erase u) (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-HasType du))
  erase-HasType (TT.ty-LApp {G = G} {A = A} {t = t} {l = l} dA dt) =
    Eq-transport (\ T -> RT.HasType (eraseCtx G) (R.LApp (E.erase A) (E.erase t) l) T) (Eq-sym (E.erase-lsub1 A l))
      (RT.ty-LApp (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
                  (erase-HasType dt))
  erase-HasType (TT.ty-collapse {G = G} lp dA) =
    RT.ty-collapse (lv G {Loop} lp) (erase-IsType dA)
  erase-HasType (TT.ty-PiCode da db) = RT.ty-Pi (erase-HasType da) (erase-HasType db)
  erase-HasType (TT.ty-UCode {G = G} {m = m} {l = l} dG lt) =
    RT.ty-U (erase-WfCtx dG) (lv G {\ T -> LtL T l m} lt)
  erase-HasType (TT.ty-Lift {G = G} {m = m} {l = l} le da) =
    RT.ty-cum (erase-HasType da) (lv G {\ T -> LeL T l m} le)
  erase-HasType (TT.ty-EmpCode dG) = RT.ty-Emp (erase-WfCtx dG)

  erase-ConvTy : {n : Nat} {G : TT.Ctx n} {A B : T.Expr n}
    -> TT.ConvTy G A B -> RT.ConvTy (eraseCtx G) (E.erase A) (E.erase B)
  erase-ConvTy (TT.conv-Ty-refl dA) = RT.conv-Ty-refl (erase-IsType dA)
  erase-ConvTy (TT.conv-Ty-sym d) = RT.conv-Ty-sym (erase-ConvTy d)
  erase-ConvTy (TT.conv-Ty-trans d1 d2) = RT.conv-Ty-trans (erase-ConvTy d1) (erase-ConvTy d2)
  erase-ConvTy (TT.conv-Ty-Pi dA dB cA cB) =
    RT.conv-Ty-Pi (erase-IsType dA) (erase-IsType dB) (erase-ConvTy cA) (erase-ConvTy cB)
  erase-ConvTy (TT.conv-Ty-El d) = RT.conv-Ty-from-U (erase-ConvTm d)
  erase-ConvTy (TT.conv-Ty-Grd {G = G} {c = c} {A = A} {B = B} dG dA dAB) =
    RT.conv-Ty-Grd (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (ctx (\ X -> RT.ConvTy X (E.erase A) (E.erase B)) (Eq-sym (eraseCtx-addC G c)) (erase-ConvTy dAB))
  erase-ConvTy (TT.conv-Ty-LPi {G = G} {A = A} {B = B} dG dA dAB) =
    RT.conv-Ty-LPi (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
      (ctx (\ X -> RT.ConvTy X (E.erase A) (E.erase B)) (Eq-sym (eraseCtx-addL G)) (erase-ConvTy dAB))
  erase-ConvTy (TT.conv-Ty-Grd-beta {G = G} {c = c} v dA) =
    RT.conv-Ty-Grd-beta (lv G {\ T -> ValidC T c} v) (erase-IsType dA)
  erase-ConvTy (TT.conv-Ty-Grd-equiv {G = G} {c = c} {c' = c'} {A = A} dG q dA) =
    RT.conv-Ty-Grd-equiv (erase-WfCtx dG) (lv G {\ T -> EquivC T c c'} q)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
  erase-ConvTy (TT.conv-Ty-collapse {G = G} lp dA) = RT.conv-Ty-collapse (lv G {Loop} lp) (erase-IsType dA)
  erase-ConvTy (TT.conv-Ty-U-lvl {G = G} {l = l} {l' = l'} dG v) =
    RT.conv-Ty-from-U (RT.conv-U-lvl (erase-WfCtx dG) (lv G {\ T -> Valid T l l'} v) (RM.lt-next l))
  erase-ConvTy (TT.conv-Ty-El-lvl v da) = RT.conv-Ty-refl (RT.is-Ty-from-U (erase-HasType da))
  erase-ConvTy (TT.conv-Ty-El-UCode dG lt) = RT.conv-Ty-refl (RM.isType-U (erase-WfCtx dG))
  erase-ConvTy (TT.conv-Ty-El-PiCode da db) =
    RT.conv-Ty-refl (RT.is-Ty-from-U (RT.ty-Pi (erase-HasType da) (erase-HasType db)))
  erase-ConvTy (TT.conv-Ty-El-Lift le da) = RT.conv-Ty-refl (RT.is-Ty-from-U (erase-HasType da))
  erase-ConvTy (TT.conv-Ty-El-EmpCode dG) = RT.conv-Ty-refl (RM.isType-Emp (erase-WfCtx dG))

  erase-ConvTm : {n : Nat} {G : TT.Ctx n} {M N A : T.Expr n}
    -> TT.ConvTm G M N A -> RT.ConvTm (eraseCtx G) (E.erase M) (E.erase N) (E.erase A)
  erase-ConvTm (TT.conv-refl dM) = RT.conv-refl (erase-HasType dM)
  erase-ConvTm (TT.conv-sym d) = RT.conv-sym (erase-ConvTm d)
  erase-ConvTm (TT.conv-trans d1 d2) = RT.conv-trans (erase-ConvTm d1) (erase-ConvTm d2)
  erase-ConvTm (TT.conv-conv dMN dAB) = RT.conv-conv (erase-ConvTm dMN) (erase-ConvTy dAB)
  erase-ConvTm (TT.conv-cong-Lam-body dA dB db dbb) =
    RT.conv-cong-Lam-body (erase-IsType dA) (erase-IsType dB) (erase-HasType db) (erase-ConvTm dbb)
  erase-ConvTm (TT.conv-cong-Lam-Ty dA dB cA cB db) =
    RT.conv-cong-Lam-Ty (erase-IsType dA) (erase-IsType dB) (erase-ConvTy cA) (erase-ConvTy cB) (erase-HasType db)
  erase-ConvTm (TT.conv-cong-App-fun {G = G} {A = A} {B = B} {c = c} {c' = c'} {a = a} dA dB dc da) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
                           (R.App (E.erase A) (E.erase B) (E.erase c') (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-fun (erase-IsType dA) (erase-IsType dB) (erase-ConvTm dc) (erase-HasType da))
  erase-ConvTm (TT.conv-cong-App-arg {G = G} {A = A} {B = B} {c = c} {a = a} {a' = a'} dA dB dc da dBa) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
                           (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a')) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-arg (erase-IsType dA) (erase-IsType dB) (erase-HasType dc) (erase-ConvTm da)
        (Eq-transport (\ X -> RT.ConvTy (eraseCtx G) X (R.subst1 (E.erase B) (E.erase a'))) (E.erase-subst1 B a)
          (Eq-transport (RT.ConvTy (eraseCtx G) (E.erase (T.subst1 B a))) (E.erase-subst1 B a')
            (erase-ConvTy dBa))))
  erase-ConvTm (TT.conv-cong-App-Ty {G = G} {A = A} {A' = A'} {B = B} {B' = B'} {c = c} {a = a} dA dB cA cB dc da) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.App (E.erase A) (E.erase B) (E.erase c) (E.erase a))
                           (R.App (E.erase A') (E.erase B') (E.erase c) (E.erase a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (RT.conv-cong-App-Ty (erase-IsType dA) (erase-IsType dB) (erase-ConvTy cA) (erase-ConvTy cB)
        (erase-HasType dc) (erase-HasType da))
  erase-ConvTm (TT.conv-beta {G = G} {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G)
                    (R.App (E.erase A) (E.erase B) (R.Lam (E.erase A) (E.erase B) (E.erase b)) (E.erase a))
                    (E.erase (T.subst1 b a)) T)
      (Eq-sym (E.erase-subst1 B a))
      (Eq-transport (\ M -> RT.ConvTm (eraseCtx G)
                        (R.App (E.erase A) (E.erase B) (R.Lam (E.erase A) (E.erase B) (E.erase b)) (E.erase a))
                        M (R.subst1 (E.erase B) (E.erase a)))
        (Eq-sym (E.erase-subst1 b a))
        (RT.conv-beta (erase-IsType dA) (erase-IsType dB) (erase-HasType db) (erase-HasType da)))
  erase-ConvTm (TT.conv-eta {G = G} {A = A} {B = B} {c = c} dA dB dc) =
    Eq-transport (\ M -> RT.ConvTm (eraseCtx G) (E.erase c) M (R.Pi (E.erase A) (E.erase B)))
      (Eq-sym (Eq-cong (R.Lam (E.erase A) (E.erase B))
        (Eq-cong4 R.App (E.erase-wk A) (E.erase-ren (liftRen wkRen) B) (E.erase-wk c) refl)))
      (RT.conv-eta (erase-IsType dA) (erase-IsType dB) (erase-HasType dc))
  erase-ConvTm (TT.conv-cong-GLam {G = G} {c = c} {A = A} {t = t} {t' = t'} dG dA dt dtt) =
    RT.conv-cong-GLam (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (ctx (\ X -> RT.HasType X (E.erase t) (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-HasType dt))
      (ctx (\ X -> RT.ConvTm X (E.erase t) (E.erase t') (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-ConvTm dtt))
  erase-ConvTm (TT.conv-GLam-eta {G = G} {c = c} {A = A} {t = t} dG dA dt dt') =
    RT.conv-GLam-eta (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (erase-HasType dt)
      (ctx (\ X -> RT.HasType X (E.erase t) (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-HasType dt'))
  erase-ConvTm (TT.conv-GLam-beta {G = G} {c = c} v dA dt) =
    RT.conv-GLam-beta (lv G {\ T -> ValidC T c} v) (erase-IsType dA) (erase-HasType dt)
  erase-ConvTm (TT.conv-GLam-equiv {G = G} {c = c} {c' = c'} {A = A} {t = t} dG q dA dt) =
    RT.conv-GLam-equiv (erase-WfCtx dG) (lv G {\ T -> EquivC T c c'} q)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (ctx (\ X -> RT.HasType X (E.erase t) (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-HasType dt))
  erase-ConvTm (TT.conv-cong-LLam {G = G} {A = A} {u = u} {u' = u'} dG dA du duu) =
    RT.conv-cong-LLam (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
      (ctx (\ X -> RT.HasType X (E.erase u) (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-HasType du))
      (ctx (\ X -> RT.ConvTm X (E.erase u) (E.erase u') (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-ConvTm duu))
  erase-ConvTm (TT.conv-cong-GLam-Ty {G = G} {c = c} {A = A} {A' = A'} {t = t} dG dA dAA dt) =
    RT.conv-cong-GLam-Ty (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-IsType dA))
      (ctx (\ X -> RT.ConvTy X (E.erase A) (E.erase A')) (Eq-sym (eraseCtx-addC G c)) (erase-ConvTy dAA))
      (ctx (\ X -> RT.HasType X (E.erase t) (E.erase A)) (Eq-sym (eraseCtx-addC G c)) (erase-HasType dt))
  erase-ConvTm (TT.conv-cong-LLam-Ty {G = G} {A = A} {A' = A'} {u = u} dG dA dAA du) =
    RT.conv-cong-LLam-Ty (erase-WfCtx dG)
      (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
      (ctx (\ X -> RT.ConvTy X (E.erase A) (E.erase A')) (Eq-sym (eraseCtx-addL G)) (erase-ConvTy dAA))
      (ctx (\ X -> RT.HasType X (E.erase u) (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-HasType du))
  erase-ConvTm (TT.conv-cong-LApp-Ty {G = G} {A = A} {A' = A'} {t = t} {l = l} dA dAA dt) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.LApp (E.erase A) (E.erase t) l) (R.LApp (E.erase A') (E.erase t) l) T)
      (Eq-sym (E.erase-lsub1 A l))
      (RT.conv-cong-LApp-Ty (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
        (ctx (\ X -> RT.ConvTy X (E.erase A) (E.erase A')) (Eq-sym (eraseCtx-addL G)) (erase-ConvTy dAA))
        (erase-HasType dt))
  erase-ConvTm (TT.conv-cong-LApp-fun {G = G} {A = A} {t = t} {t' = t'} {l = l} dA dtt) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.LApp (E.erase A) (E.erase t) l) (R.LApp (E.erase A) (E.erase t') l) T)
      (Eq-sym (E.erase-lsub1 A l))
      (RT.conv-cong-LApp-fun (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
        (erase-ConvTm dtt))
  erase-ConvTm (TT.conv-cong-LApp-lvl {G = G} {A = A} {t = t} {l = l} {l' = l'} dA dt v dAA) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.LApp (E.erase A) (E.erase t) l) (R.LApp (E.erase A) (E.erase t) l') T)
      (Eq-sym (E.erase-lsub1 A l))
      (RT.conv-cong-LApp-lvl (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
        (erase-HasType dt) (lv G {\ T -> Valid T l l'} v)
        (Eq-transport (\ X -> RT.ConvTy (eraseCtx G) X (R.lsub1 (E.erase A) l')) (E.erase-lsub1 A l)
          (Eq-transport (RT.ConvTy (eraseCtx G) (E.erase (T.lsub1 A l))) (E.erase-lsub1 A l') (erase-ConvTy dAA))))
  erase-ConvTm (TT.conv-LApp-beta {G = G} {A = A} {u = u} {l = l} dA du) =
    Eq-transport (\ T -> RT.ConvTm (eraseCtx G) (R.LApp (E.erase A) (R.LLam (E.erase A) (E.erase u)) l) (E.erase (T.lsub1 u l)) T)
      (Eq-sym (E.erase-lsub1 A l))
      (Eq-transport (\ M -> RT.ConvTm (eraseCtx G) (R.LApp (E.erase A) (R.LLam (E.erase A) (E.erase u)) l) M (R.lsub1 (E.erase A) l))
        (Eq-sym (E.erase-lsub1 u l))
        (RT.conv-LApp-beta (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
          (ctx (\ X -> RT.HasType X (E.erase u) (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-HasType du))))
  erase-ConvTm (TT.conv-LApp-eta {G = G} {A = A} {t = t} dA dt) =
    Eq-transport (\ M -> RT.ConvTm (eraseCtx G) (E.erase t) M (R.LPi (E.erase A)))
      (Eq-sym (Eq-cong2 (\ Y M -> R.LLam (E.erase A) (R.LApp Y M (lvar zero)))
                        (E.erase-lsub (liftL lwkS) A) (E.erase-lshift t)))
      (RT.conv-LApp-eta (ctx (\ X -> RT.IsType X (E.erase A)) (Eq-sym (eraseCtx-addL G)) (erase-IsType dA))
        (erase-HasType dt))
  erase-ConvTm (TT.conv-collapse {G = G} lp dA dt) =
    RT.conv-collapse (lv G {Loop} lp) (erase-IsType dA) (erase-HasType dt)
  erase-ConvTm (TT.conv-cong-PiCode da db daa dbb) =
    RT.conv-cong-Pi (erase-HasType da) (erase-HasType db) (erase-ConvTm daa) (erase-ConvTm dbb)
  erase-ConvTm (TT.conv-cong-Lift {G = G} {m = m} {l = l} le d) =
    RT.conv-cum (erase-ConvTm d) (lv G {\ T -> LeL T l m} le)
  erase-ConvTm (TT.conv-Lift-refl {G = G} {m = m} {l = l} v da) =
    RT.conv-refl (RT.ty-cum (erase-HasType da) (lv G {\ T -> LeL T l m} (leL-refl v)))
  erase-ConvTm (TT.conv-Lift-Lift {G = G} {p = p} {l = l} lm mp da) =
    RT.conv-refl (RT.ty-cum (erase-HasType da) (lv G {\ T -> LeL T l p} (leL-trans lm mp)))
  erase-ConvTm (TT.conv-Lift-UCode {G = G} {m = m} {k = k} dG kl lm) =
    RT.conv-refl (RT.ty-U (erase-WfCtx dG) (lv G {\ T -> LtL T k m} (ltL-leL kl lm)))
  erase-ConvTm (TT.conv-Lift-PiCode {G = G} {m = m} {l = l} le da db) =
    RT.conv-refl (RT.ty-cum (RT.ty-Pi (erase-HasType da) (erase-HasType db)) (lv G {\ T -> LeL T l m} le))
  erase-ConvTm (TT.conv-Lift-EmpCode dG le) = RT.conv-refl (RT.ty-Emp (erase-WfCtx dG))
  erase-ConvTm (TT.conv-UCode-lvl {G = G} {m = m} {l = l} {l' = l'} dG v w lt) =
    RT.conv-U-lvl (erase-WfCtx dG) (lv G {\ T -> Valid T l l'} v) (lv G {\ T -> LtL T l m} lt)
  erase-ConvTm (TT.conv-Lift-lvl {G = G} {m = m} {l = l} v w le da) =
    RT.conv-refl (RT.ty-cum (erase-HasType da) (lv G {\ T -> LeL T l m} le))
  erase-ConvTm (TT.conv-PiCode-lvl v da db) = RT.conv-refl (RT.ty-Pi (erase-HasType da) (erase-HasType db))
  erase-ConvTm (TT.conv-EmpCode-lvl dG v) = RT.conv-refl (RT.ty-Emp (erase-WfCtx dG))
