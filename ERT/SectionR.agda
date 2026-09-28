{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.SectionR  —  paper Theorem 4.19 (section of strip)
--
-- Without normalisation (since 2026-09-25: uses StripUniqNF):
--
--   If Γ ⊢ J in T_P, then there is Γ' ⊢ J' in T_R with strip(Γ') = Γ and
--   strip(J') = J, unique up to conversion.
--
-- In fact the judgement lifts into EVERY well-formed T_R context Γ'
-- over Γ (lift-*).  The lift is by structural induction on the T_P
-- derivation; the annotations are read off the premises, and premises
-- that share a stripped term / type are reconciled by the uniqueness
-- lemmas of ERT.StripUniqNF (Lemma 4.18).  Uniqueness up to
-- conversion is Lemma 4.18 itself (term-uniq-NF, type-uniq-NF).
------------------------------------------------------------------------

module ERT.SectionR where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.RussellMetaCong using (subst1-cong-Ty)
open import ERT.Model.Strip using (strip ; stripCtx ; strip-subst1 ; strip-wk ; strip-lookup)
import ERT.Model.Core as C
import ERT.PTyping as P
open import ERT.StripUniqNF

------------------------------------------------------------------------
-- T_P: the context of a judgement is well formed
------------------------------------------------------------------------

mutual
  pwf-Ty : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A -> P.WfCtx G
  pwf-Ty (P.is-Ty-from-U d) = pwf-Tm d

  pwf-Tm : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A -> P.WfCtx G
  pwf-Tm (P.ty-var wf)         = wf
  pwf-Tm (P.ty-conv d _)       = pwf-Tm d
  pwf-Tm (P.ty-U wf)           = wf
  pwf-Tm (P.ty-cum d)          = pwf-Tm d
  pwf-Tm (P.ty-Pi dA _)        = pwf-Tm dA
  pwf-Tm (P.ty-Lam dA _ _)     = pwf-Ty dA
  pwf-Tm (P.ty-App dA _ _ _)   = pwf-Ty dA

------------------------------------------------------------------------
-- Small syntactic facts
------------------------------------------------------------------------

private
  strip-U-inv : {n : Nat} {l : Nat} (T : Expr n) -> Eq (strip T) (C.U l) -> Eq T (U l)
  strip-U-inv (U k)         refl = refl
  strip-U-inv (Var _)       ()
  strip-U-inv (Pi _ _)      ()
  strip-U-inv (Lam _ _ _)   ()
  strip-U-inv (App _ _ _ _) ()

  ext-eq : {n : Nat} {G G' : C.Ctx n} {A A' : C.Expr n} -> Eq G G' -> Eq A A' -> Eq (C.extend G A) (C.extend G' A')
  ext-eq refl refl = refl

  cong2 : {X Y Z : Set} (f : X -> Y -> Z) {x x' : X} {y y' : Y} -> Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
  cong2 f refl refl = refl

  atU : {n : Nat} {G : Ctx n} {M T : Expr n} {l : Nat} -> Eq (strip T) (C.U l) -> HasType G M T -> HasType G M (U l)
  atU {T = T} e d = Eq-transport (HasType _ _) (strip-U-inv T e) d

  atU-C : {n : Nat} {G : Ctx n} {M N T : Expr n} {l : Nat} -> Eq (strip T) (C.U l) -> ConvTm G M N T -> ConvTm G M N (U l)
  atU-C {T = T} e d = Eq-transport (ConvTm _ _ _) (strip-U-inv T e) d

------------------------------------------------------------------------
-- Lifts into a given T_R context
------------------------------------------------------------------------

record LTy {n : Nat} (G' : Ctx n) (A : C.Expr n) : Set where
  constructor mkLTy
  field
    A' : Expr n
    eA : Eq (strip A') A
    d  : IsType G' A'

record LTm {n : Nat} (G' : Ctx n) (M A : C.Expr n) : Set where
  constructor mkLTm
  field
    M' : Expr n
    A' : Expr n
    eM : Eq (strip M') M
    eA : Eq (strip A') A
    d  : HasType G' M' A'

record LCTy {n : Nat} (G' : Ctx n) (A B : C.Expr n) : Set where
  constructor mkLCTy
  field
    A' : Expr n
    B' : Expr n
    eA : Eq (strip A') A
    eB : Eq (strip B') B
    d  : ConvTy G' A' B'

record LCTm {n : Nat} (G' : Ctx n) (M N A : C.Expr n) : Set where
  constructor mkLCTm
  field
    M' : Expr n
    N' : Expr n
    A' : Expr n
    eM : Eq (strip M') M
    eN : Eq (strip N') N
    eA : Eq (strip A') A
    d  : ConvTm G' M' N' A'

module _ where

  private
    -- a lifted term moved to another lift of its type
    retype : {n : Nat} {G' : Ctx n} {M A : C.Expr n} (r : LTm G' M A) {T : Expr n} ->
      IsType G' T -> Eq (strip T) A -> HasType G' (LTm.M' r) T
    retype r dT eT =
      ty-conv (LTm.d r) (type-uniq-NF (typing-IsType (LTm.d r)) dT (Eq-trans (LTm.eA r) (Eq-sym eT)))

    retypeC : {n : Nat} {G' : Ctx n} {M N A : C.Expr n} (r : LCTm G' M N A) {T : Expr n} ->
      IsType G' T -> Eq (strip T) A -> ConvTm G' (LCTm.M' r) (LCTm.N' r) T
    retypeC r dT eT =
      conv-conv (LCTm.d r)
        (type-uniq-NF (typing-IsType (presup-l-ConvTm (LCTm.d r))) dT (Eq-trans (LCTm.eA r) (Eq-sym eT)))

    -- two lifts of the same term at the same type are convertible
    same : {n : Nat} {G' : Ctx n} {X Y T : Expr n} -> HasType G' X T -> HasType G' Y T ->
      Eq (strip X) (strip Y) -> ConvTm G' X Y T
    same dX dY e = term-uniq-conv-NF dX dY e (conv-Ty-refl (typing-IsType dX))

    -- two lifts of the same type are convertible
    sameTy : {n : Nat} {G' : Ctx n} {X Y : Expr n} {A : C.Expr n} -> IsType G' X -> IsType G' Y ->
      Eq (strip X) A -> Eq (strip Y) A -> ConvTy G' X Y
    sameTy dX dY eX eY = type-uniq-NF dX dY (Eq-trans eX (Eq-sym eY))

  mutual

    lift-IsType : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A ->
      (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LTy G' A
    lift-IsType (P.is-Ty-from-U d) G' wf e =
      let r = lift-HasType d G' wf e
      in mkLTy (LTm.M' r) (LTm.eM r) (is-Ty-from-U (atU (LTm.eA r) (LTm.d r)))

    lift-HasType : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A ->
      (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LTm G' M A
    lift-HasType (P.ty-var {i = i} _) G' wf e =
      mkLTm (Var i) (lookup G' i) refl
        (Eq-trans (strip-lookup G' i) (Eq-cong (\ X -> C.lookup X i) e)) (ty-var wf)
    lift-HasType (P.ty-conv d c) G' wf e =
      let r = lift-HasType d G' wf e
          q = lift-ConvTy c G' wf e
          b = sameTy (typing-IsType (LTm.d r)) (presup-l-ConvTy (LCTy.d q)) (LTm.eA r) (LCTy.eA q)
      in mkLTm (LTm.M' r) (LCTy.B' q) (LTm.eM r) (LCTy.eB q) (ty-conv (LTm.d r) (conv-Ty-trans b (LCTy.d q)))
    lift-HasType (P.ty-U {l = l} _) G' wf e = mkLTm (U l) (U (suc l)) refl refl (ty-U wf)
    lift-HasType (P.ty-cum {l = l} d) G' wf e =
      let r = lift-HasType d G' wf e
      in mkLTm (LTm.M' r) (U (suc l)) (LTm.eM r) refl (ty-cum (atU (LTm.eA r) (LTm.d r)))
    lift-HasType (P.ty-Pi {l = l} dA dB) G' wf e =
      let rA  = lift-HasType dA G' wf e
          dA' = atU (LTm.eA rA) (LTm.d rA)
          rB  = lift-HasType dB (extend G' (LTm.M' rA)) (wf-extend (is-Ty-from-U dA')) (ext-eq e (LTm.eM rA))
          dB' = atU (LTm.eA rB) (LTm.d rB)
      in mkLTm (Pi (LTm.M' rA) (LTm.M' rB)) (U l) (cong2 C.Pi (LTm.eM rA) (LTm.eM rB)) refl (ty-Pi dA' dB')
    lift-HasType (P.ty-Lam dA dB db) G' wf e =
      let a  = lift-IsType dA G' wf e
          G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b  = lift-IsType dB G1 wf1 e1
          t  = lift-HasType db G1 wf1 e1
      in mkLTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Pi (LTy.A' a) (LTy.A' b))
           (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
           (ty-Lam (LTy.d a) (LTy.d b) (retype t (LTy.d b) (LTy.eA b)))
    lift-HasType (P.ty-App dA dB dc da) G' wf e =
      let a  = lift-IsType dA G' wf e
          G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b  = lift-IsType dB G1 wf1 e1
          c  = lift-HasType dc G' wf e
          s  = lift-HasType da G' wf e
          dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
          da' = retype s (LTy.d a) (LTy.eA a)
      in mkLTm (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LTm.M' s)) (subst1 (LTy.A' b) (LTm.M' s))
           (cong2 C.App (LTm.eM c) (LTm.eM s))
           (Eq-trans (strip-subst1 (LTy.A' b) (LTm.M' s)) (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
           (ty-App (LTy.d a) (LTy.d b) dc' da')

    lift-ConvTy : {n : Nat} {G : C.Ctx n} {A B : C.Expr n} -> P.ConvTy G A B ->
      (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LCTy G' A B
    lift-ConvTy (P.conv-Ty-refl dA) G' wf e =
      let a = lift-IsType dA G' wf e in mkLCTy (LTy.A' a) (LTy.A' a) (LTy.eA a) (LTy.eA a) (conv-Ty-refl (LTy.d a))
    lift-ConvTy (P.conv-Ty-sym c) G' wf e =
      let q = lift-ConvTy c G' wf e in mkLCTy (LCTy.B' q) (LCTy.A' q) (LCTy.eB q) (LCTy.eA q) (conv-Ty-sym (LCTy.d q))
    lift-ConvTy (P.conv-Ty-trans c1 c2) G' wf e =
      let q1 = lift-ConvTy c1 G' wf e
          q2 = lift-ConvTy c2 G' wf e
          b  = sameTy (presup-r-ConvTy (LCTy.d q1)) (presup-l-ConvTy (LCTy.d q2)) (LCTy.eB q1) (LCTy.eA q2)
      in mkLCTy (LCTy.A' q1) (LCTy.B' q2) (LCTy.eA q1) (LCTy.eB q2)
           (conv-Ty-trans (LCTy.d q1) (conv-Ty-trans b (LCTy.d q2)))
    lift-ConvTy (P.conv-Ty-Pi dA dB cA cB) G' wf e =
      let a  = lift-IsType dA G' wf e
          G1 = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b  = lift-IsType dB G1 wf1 e1
          qA = lift-ConvTy cA G' wf e
          qB = lift-ConvTy cB G1 wf1 e1
          cA' = conv-Ty-trans (sameTy (LTy.d a) (presup-l-ConvTy (LCTy.d qA)) (LTy.eA a) (LCTy.eA qA)) (LCTy.d qA)
          cB' = conv-Ty-trans (sameTy (LTy.d b) (presup-l-ConvTy (LCTy.d qB)) (LTy.eA b) (LCTy.eA qB)) (LCTy.d qB)
      in mkLCTy (Pi (LTy.A' a) (LTy.A' b)) (Pi (LCTy.B' qA) (LCTy.B' qB))
           (cong2 C.Pi (LTy.eA a) (LTy.eA b)) (cong2 C.Pi (LCTy.eB qA) (LCTy.eB qB))
           (conv-Ty-Pi (LTy.d a) (LTy.d b) cA' cB')
    lift-ConvTy (P.conv-Ty-from-U d) G' wf e =
      let q = lift-ConvTm d G' wf e
      in mkLCTy (LCTm.M' q) (LCTm.N' q) (LCTm.eM q) (LCTm.eN q) (conv-Ty-from-U (atU-C (LCTm.eA q) (LCTm.d q)))

    lift-ConvTm : {n : Nat} {G : C.Ctx n} {M N A : C.Expr n} -> P.ConvTm G M N A ->
      (G' : Ctx n) -> WfCtx G' -> Eq (stripCtx G') G -> LCTm G' M N A
    lift-ConvTm (P.conv-refl d) G' wf e =
      let r = lift-HasType d G' wf e
      in mkLCTm (LTm.M' r) (LTm.M' r) (LTm.A' r) (LTm.eM r) (LTm.eM r) (LTm.eA r) (conv-refl (LTm.d r))
    lift-ConvTm (P.conv-sym d) G' wf e =
      let q = lift-ConvTm d G' wf e
      in mkLCTm (LCTm.N' q) (LCTm.M' q) (LCTm.A' q) (LCTm.eN q) (LCTm.eM q) (LCTm.eA q) (conv-sym (LCTm.d q))
    lift-ConvTm (P.conv-trans d1 d2) G' wf e =
      let q1 = lift-ConvTm d1 G' wf e
          q2 = lift-ConvTm d2 G' wf e
          u  = term-uniq-NF (presup-r-ConvTm (LCTm.d q1)) (presup-l-ConvTm (LCTm.d q2))
                 (Eq-trans (LCTm.eN q1) (Eq-sym (LCTm.eM q2))) (Eq-trans (LCTm.eA q1) (Eq-sym (LCTm.eA q2)))
      in mkLCTm (LCTm.M' q1) (LCTm.N' q2) (LCTm.A' q1) (LCTm.eM q1) (LCTm.eN q2) (LCTm.eA q1)
           (conv-trans (LCTm.d q1) (conv-trans (snd u) (conv-conv (LCTm.d q2) (conv-Ty-sym (fst u)))))
    lift-ConvTm (P.conv-conv d c) G' wf e =
      let q  = lift-ConvTm d G' wf e
          cq = lift-ConvTy c G' wf e
          b  = sameTy (typing-IsType (presup-l-ConvTm (LCTm.d q))) (presup-l-ConvTy (LCTy.d cq)) (LCTm.eA q) (LCTy.eA cq)
      in mkLCTm (LCTm.M' q) (LCTm.N' q) (LCTy.B' cq) (LCTm.eM q) (LCTm.eN q) (LCTy.eB cq)
           (conv-conv (LCTm.d q) (conv-Ty-trans b (LCTy.d cq)))
    lift-ConvTm (P.conv-cum {l = l} d) G' wf e =
      let q = lift-ConvTm d G' wf e
      in mkLCTm (LCTm.M' q) (LCTm.N' q) (U (suc l)) (LCTm.eM q) (LCTm.eN q) refl (conv-cum (atU-C (LCTm.eA q) (LCTm.d q)))
    lift-ConvTm (P.conv-cong-Pi {l = l} dA dB cA cB) G' wf e =
      let rA  = lift-HasType dA G' wf e
          dA' = atU (LTm.eA rA) (LTm.d rA)
          G1  = extend G' (LTm.M' rA) ; wf1 = wf-extend (is-Ty-from-U dA') ; e1 = ext-eq e (LTm.eM rA)
          rB  = lift-HasType dB G1 wf1 e1
          dB' = atU (LTm.eA rB) (LTm.d rB)
          qA  = lift-ConvTm cA G' wf e
          qB  = lift-ConvTm cB G1 wf1 e1
          cA0 = atU-C (LCTm.eA qA) (LCTm.d qA)
          cB0 = atU-C (LCTm.eA qB) (LCTm.d qB)
          cA' = conv-trans (same dA' (presup-l-ConvTm cA0) (Eq-trans (LTm.eM rA) (Eq-sym (LCTm.eM qA)))) cA0
          cB' = conv-trans (same dB' (presup-l-ConvTm cB0) (Eq-trans (LTm.eM rB) (Eq-sym (LCTm.eM qB)))) cB0
      in mkLCTm (Pi (LTm.M' rA) (LTm.M' rB)) (Pi (LCTm.N' qA) (LCTm.N' qB)) (U l)
           (cong2 C.Pi (LTm.eM rA) (LTm.eM rB)) (cong2 C.Pi (LCTm.eN qA) (LCTm.eN qB)) refl
           (conv-cong-Pi dA' dB' cA' cB')
    lift-ConvTm (P.conv-cong-Lam-body dA dB db0 cb) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          t   = lift-HasType db0 G1 wf1 e1
          db' = retype t (LTy.d b) (LTy.eA b)
          qc  = lift-ConvTm cb G1 wf1 e1
          cq  = retypeC qc (LTy.d b) (LTy.eA b)
          cb' = conv-trans (same db' (presup-l-ConvTm cq) (Eq-trans (LTm.eM t) (Eq-sym (LCTm.eM qc)))) cq
      in mkLCTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Lam (LTy.A' a) (LTy.A' b) (LCTm.N' qc)) (Pi (LTy.A' a) (LTy.A' b))
           (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Lam (LTy.eA a) (LCTm.eN qc)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
           (conv-cong-Lam-body (LTy.d a) (LTy.d b) db' cb')
    lift-ConvTm (P.conv-cong-Lam-dom dA dB cA db) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          qA  = lift-ConvTy cA G' wf e
          cA' = conv-Ty-trans (sameTy (LTy.d a) (presup-l-ConvTy (LCTy.d qA)) (LTy.eA a) (LCTy.eA qA)) (LCTy.d qA)
          t   = lift-HasType db G1 wf1 e1
          db' = retype t (LTy.d b) (LTy.eA b)
      in mkLCTm (Lam (LTy.A' a) (LTy.A' b) (LTm.M' t)) (Lam (LCTy.B' qA) (LTy.A' b) (LTm.M' t)) (Pi (LTy.A' a) (LTy.A' b))
           (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (cong2 C.Lam (LCTy.eB qA) (LTm.eM t)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
           (conv-cong-Lam-Ty (LTy.d a) (LTy.d b) cA' (conv-Ty-refl (LTy.d b)) db')
    lift-ConvTm (P.conv-cong-App-fun dA dB cc da) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          qc  = lift-ConvTm cc G' wf e
          cc' = retypeC qc (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
          s   = lift-HasType da G' wf e
          da' = retype s (LTy.d a) (LTy.eA a)
      in mkLCTm (App (LTy.A' a) (LTy.A' b) (LCTm.M' qc) (LTm.M' s)) (App (LTy.A' a) (LTy.A' b) (LCTm.N' qc) (LTm.M' s))
           (subst1 (LTy.A' b) (LTm.M' s))
           (cong2 C.App (LCTm.eM qc) (LTm.eM s)) (cong2 C.App (LCTm.eN qc) (LTm.eM s))
           (Eq-trans (strip-subst1 (LTy.A' b) (LTm.M' s)) (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
           (conv-cong-App-fun (LTy.d a) (LTy.d b) cc' da')
    lift-ConvTm (P.conv-cong-App-arg dA dB dc ca) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          c   = lift-HasType dc G' wf e
          dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
          qa  = lift-ConvTm ca G' wf e
          ca' = retypeC qa (LTy.d a) (LTy.eA a)
      in mkLCTm (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LCTm.M' qa)) (App (LTy.A' a) (LTy.A' b) (LTm.M' c) (LCTm.N' qa))
           (subst1 (LTy.A' b) (LCTm.M' qa))
           (cong2 C.App (LTm.eM c) (LCTm.eM qa)) (cong2 C.App (LTm.eM c) (LCTm.eN qa))
           (Eq-trans (strip-subst1 (LTy.A' b) (LCTm.M' qa)) (cong2 C.subst1 (LTy.eA b) (LCTm.eM qa)))
           (conv-cong-App-arg (LTy.d a) (LTy.d b) dc' ca' (subst1-cong-Ty ca' (LTy.d a) (LTy.d b)))
    lift-ConvTm (P.conv-beta dA dB db da) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          t   = lift-HasType db G1 wf1 e1
          db' = retype t (LTy.d b) (LTy.eA b)
          s   = lift-HasType da G' wf e
          da' = retype s (LTy.d a) (LTy.eA a)
          A'  = LTy.A' a ; B' = LTy.A' b ; b' = LTm.M' t ; a' = LTm.M' s
      in mkLCTm (App A' B' (Lam A' B' b') a') (subst1 b' a') (subst1 B' a')
           (cong2 C.App (cong2 C.Lam (LTy.eA a) (LTm.eM t)) (LTm.eM s))
           (Eq-trans (strip-subst1 b' a') (cong2 C.subst1 (LTm.eM t) (LTm.eM s)))
           (Eq-trans (strip-subst1 B' a') (cong2 C.subst1 (LTy.eA b) (LTm.eM s)))
           (conv-beta (LTy.d a) (LTy.d b) db' da')
    lift-ConvTm (P.conv-eta dA dB dc) G' wf e =
      let a   = lift-IsType dA G' wf e
          G1  = extend G' (LTy.A' a) ; wf1 = wf-extend (LTy.d a) ; e1 = ext-eq e (LTy.eA a)
          b   = lift-IsType dB G1 wf1 e1
          c   = lift-HasType dc G' wf e
          dc' = retype c (isType-Pi (LTy.d a) (LTy.d b)) (cong2 C.Pi (LTy.eA a) (LTy.eA b))
          A'  = LTy.A' a ; B' = LTy.A' b ; c' = LTm.M' c
      in mkLCTm c' (Lam A' B' (App (wkExpr A') (renExpr (liftRen wkRen) B') (wkExpr c') (Var fzero))) (Pi A' B')
           (LTm.eM c)
           (cong2 C.Lam (LTy.eA a)
              (Eq-cong (\ X -> C.App X (C.Var fzero)) (Eq-trans (strip-wk c') (Eq-cong C.wkExpr (LTm.eM c)))))
           (cong2 C.Pi (LTy.eA a) (LTy.eA b))
           (conv-eta (LTy.d a) (LTy.d b) dc')

  ----------------------------------------------------------------------
  -- Contexts: every well-formed T_P context has a well-formed lift
  -- (by recursion on the context)
  ----------------------------------------------------------------------

  record LCtx {n : Nat} (G : C.Ctx n) : Set where
    constructor mkLCtx
    field
      G'  : Ctx n
      eG  : Eq (stripCtx G') G
      wf  : WfCtx G'

  lift-WfCtx : {n : Nat} (G : C.Ctx n) -> P.WfCtx G -> LCtx G
  lift-WfCtx C.empty        P.wf-empty       = mkLCtx empty refl wf-empty
  lift-WfCtx (C.extend G A) (P.wf-extend dA) =
    let r = lift-WfCtx G (pwf-Ty dA)
        a = lift-IsType dA (LCtx.G' r) (LCtx.wf r) (LCtx.eG r)
    in mkLCtx (extend (LCtx.G' r) (LTy.A' a)) (ext-eq (LCtx.eG r) (LTy.eA a)) (wf-extend (LTy.d a))

  ----------------------------------------------------------------------
  -- Theorem 4.19
  ----------------------------------------------------------------------

  -- existence
  section-HasType : {n : Nat} {G : C.Ctx n} {M A : C.Expr n} -> P.HasType G M A ->
    Sigma (LCtx G) (\ r -> LTm (LCtx.G' r) M A)
  section-HasType {G = G} d =
    let r = lift-WfCtx G (pwf-Tm d)
    in mkSigma r (lift-HasType d (LCtx.G' r) (LCtx.wf r) (LCtx.eG r))

  section-IsType : {n : Nat} {G : C.Ctx n} {A : C.Expr n} -> P.IsType G A ->
    Sigma (LCtx G) (\ r -> LTy (LCtx.G' r) A)
  section-IsType {G = G} d =
    let r = lift-WfCtx G (pwf-Ty d)
    in mkSigma r (lift-IsType d (LCtx.G' r) (LCtx.wf r) (LCtx.eG r))

  -- uniqueness up to conversion (in any T_R context): Lemma 4.18
  section-uniq-Tm : {n : Nat} {G' : Ctx n} {M A : C.Expr n} (r1 r2 : LTm G' M A) ->
    Pair (ConvTy G' (LTm.A' r1) (LTm.A' r2)) (ConvTm G' (LTm.M' r1) (LTm.M' r2) (LTm.A' r1))
  section-uniq-Tm r1 r2 =
    term-uniq-NF (LTm.d r1) (LTm.d r2)
      (Eq-trans (LTm.eM r1) (Eq-sym (LTm.eM r2))) (Eq-trans (LTm.eA r1) (Eq-sym (LTm.eA r2)))

  section-uniq-Ty : {n : Nat} {G' : Ctx n} {A : C.Expr n} (r1 r2 : LTy G' A) ->
    ConvTy G' (LTy.A' r1) (LTy.A' r2)
  section-uniq-Ty r1 r2 = sameTy (LTy.d r1) (LTy.d r2) (LTy.eA r1) (LTy.eA r2)
