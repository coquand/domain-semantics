{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.StripUniq
--
-- Redundancy of the annotations of T_R (paper Lemma 4.18; Streicher,
-- Semantics of Type Theory, Thm 4.12/4.13 method), assuming only that
-- the typable terms of T_P have a β-normal form (PR.WN-P):
--
--   If Γ ⊢ u0 : A0 and Γ ⊢ u1 : A1 in T_R with strip u0 = strip u1 and
--   strip A0 = strip A1, then Γ ⊢ A0 = A1 and Γ ⊢ u0 = u1 : A0.
--
-- Proof.
-- (1) Normal forms (nf-conv / ne-conv, by induction on the β-normal
--     form of the stripping): the annotations are forced up to
--     conversion — for a neutral application by the type of its head
--     (ne-conv returns a common "principal" type P below both types),
--     for a λ by its (convertible) type, via Π-injectivity.  Cumulativity
--     only acts at the root, where it changes no syntax (SubTy).
-- (2) General terms: normalise strip(u), lift the SAME reduction
--     sequence to u0 and to u1 (RussellStep.liftStar: β ignores the
--     annotations), and use subject reduction (SubjectReductionR).
--
-- No postulates: normalisation is a module parameter.
------------------------------------------------------------------------

module ERT.StripUniq where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.RussellMetaCong using (subst1-cong-Ty)
open import ERT.RussellInversion
open import ERT.RussellStep
open import ERT.SubjectReductionR
open import ERT.PiInjectivityR using (PiInj-R)
open import ERT.Model.Strip using (strip ; stripCtx)
open import ERT.StripDeriv using (strip-HasType)
import ERT.Model.Core as C
import ERT.PReduction as PR

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  C-App-inj : {n : Nat} {c c' a a' : C.Expr n} -> Eq (C.App c a) (C.App c' a') -> Pair (Eq c c') (Eq a a')
  C-App-inj refl = mkSigma refl refl

  C-Lam-inj : {n : Nat} {A A' : C.Expr n} {b b' : C.Expr (suc n)} -> Eq (C.Lam A b) (C.Lam A' b') -> Pair (Eq A A') (Eq b b')
  C-Lam-inj refl = mkSigma refl refl

  C-Pi-inj : {n : Nat} {A A' : C.Expr n} {B B' : C.Expr (suc n)} -> Eq (C.Pi A B) (C.Pi A' B') -> Pair (Eq A A') (Eq B B')
  C-Pi-inj refl = mkSigma refl refl

  Le-cong : {k m l : Nat} -> Eq m l -> Le k m -> Le k l
  Le-cong refl h = h

  -- a product is below a type only when convertible to it
  Sub-from-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {T : Expr n} ->
    SubTy G (Pi A B) T -> ConvTy G (Pi A B) T
  Sub-from-Pi (sub-conv c)           = c
  Sub-from-Pi (sub-cum k m le cP cT) = absurd (Pi-U-noconf cP)

  -- a type above a universe is (convertible to) a larger universe
  record AboveU {n : Nat} (G : Ctx n) (l : Nat) (T : Expr n) : Set where
    constructor mkAboveU
    field
      lv  : Nat
      le  : Le l lv
      cnv : ConvTy G T (U lv)

  Sub-from-U : {n : Nat} {G : Ctx n} {l : Nat} {T : Expr n} -> SubTy G (U l) T -> AboveU G l T
  Sub-from-U {l = l} (sub-conv c)   = mkAboveU l (Le-refl l) (conv-Ty-sym c)
  Sub-from-U {l = l} (sub-cum k m le cP cT) = mkAboveU m (Le-cong' (U-inj-R cP) le) cT
    where
      Le-cong' : {a b c : Nat} -> Eq a b -> Le b c -> Le a c
      Le-cong' refl h = h

------------------------------------------------------------------------
-- (1) The lemma for β-normal strippings
------------------------------------------------------------------------

record NeRes {n : Nat} (G : Ctx n) (u0 u1 A0 A1 : Expr n) : Set where
  constructor mkNeRes
  field
    P    : Expr n
    conv : ConvTm G u0 u1 P
    s0   : SubTy G P A0
    s1   : SubTy G P A1

mutual

  ne-conv : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} {N : C.Expr n} -> PR.Ne N ->
    Eq (strip u0) N -> Eq (strip u1) N ->
    HasType G u0 A0 -> HasType G u1 A1 -> NeRes G u0 u1 A0 A1
  ne-conv {G = G} {u0 = Var i} {u1 = Var .i} PR.ne-var refl refl d0 d1 =
    let r0 = inv-Var d0 ; r1 = inv-Var d1
    in mkNeRes (lookup G i) (conv-refl (ty-var (fst r0))) (snd r0) (snd r1)
  ne-conv {u0 = Var _} {u1 = U _} PR.ne-var         refl ()
  ne-conv {u0 = Var _} {u1 = Pi _ _} PR.ne-var      refl ()
  ne-conv {u0 = Var _} {u1 = Lam _ _ _} PR.ne-var   refl ()
  ne-conv {u0 = Var _} {u1 = App _ _ _ _} PR.ne-var refl ()
  ne-conv {u0 = U _} PR.ne-var         ()
  ne-conv {u0 = Pi _ _} PR.ne-var      ()
  ne-conv {u0 = Lam _ _ _} PR.ne-var   ()
  ne-conv {u0 = App _ _ _ _} PR.ne-var ()
  ne-conv {G = G} {u0 = App C0 B0 f0 a0} {u1 = App C1 B1 f1 a1} (PR.ne-app nc na) refl e1 d0 d1 =
    let inj  = C-App-inj e1
        i0   = inv-App d0 ; i1 = inv-App d1
        dC0  = InvApp.dA i0 ; dB0 = InvApp.dB i0
        r    = ne-conv nc refl (fst inj) (InvApp.dc i0) (InvApp.dc i1)
        p0   = Sub-Pi (NeRes.s0 r)                       -- P = Π(C0,B0)
        p1   = Sub-Pi (NeRes.s1 r)                       -- P = Π(C1,B1)
        pinj = PiInj-R (conv-Ty-trans (conv-Ty-sym p0) p1)
        cC   = fst pinj ; cB = snd pinj
        cf   = conv-conv (NeRes.conv r) p0               -- f0 = f1 : Π(C0,B0)
        da1' = ty-conv (InvApp.da i1) (conv-Ty-sym cC)   -- a1 : C0
        ca   = nf-conv na refl (snd inj) (InvApp.da i0) da1' (conv-Ty-refl dC0)
        df1' = presup-r-ConvTm cf
        cBa  = subst1-cong-Ty ca dC0 dB0                 -- B0[a0] = B0[a1]
        step1 = conv-cong-App-fun dC0 dB0 cf (InvApp.da i0)
        step2 = conv-cong-App-arg dC0 dB0 df1' ca cBa
        step3 = conv-conv (conv-cong-App-Ty dC0 dB0 cC cB df1' da1') (conv-Ty-sym cBa)
        cBB  = conv-Ty-trans cBa (subst-ConvTy (subst1-WtSub dC0 da1') (isType-WfCtx dC0) cB)
    in mkNeRes (subst1 B0 a0) (conv-trans step1 (conv-trans step2 step3))
               (InvApp.sub i0) (Sub-conv-left cBB (InvApp.sub i1))
  ne-conv {u0 = App _ _ _ _} {u1 = Var _} (PR.ne-app nc na)     refl ()
  ne-conv {u0 = App _ _ _ _} {u1 = U _} (PR.ne-app nc na)       refl ()
  ne-conv {u0 = App _ _ _ _} {u1 = Pi _ _} (PR.ne-app nc na)    refl ()
  ne-conv {u0 = App _ _ _ _} {u1 = Lam _ _ _} (PR.ne-app nc na) refl ()
  ne-conv {u0 = Var _} (PR.ne-app nc na)     ()
  ne-conv {u0 = U _} (PR.ne-app nc na)       ()
  ne-conv {u0 = Pi _ _} (PR.ne-app nc na)    ()
  ne-conv {u0 = Lam _ _ _} (PR.ne-app nc na) ()

  nf-conv : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} {N : C.Expr n} -> PR.Nf N ->
    Eq (strip u0) N -> Eq (strip u1) N ->
    HasType G u0 A0 -> HasType G u1 A1 -> ConvTy G A0 A1 -> ConvTm G u0 u1 A0
  nf-conv (PR.nf-ne ne) e0 e1 d0 d1 cA =
    let r = ne-conv ne e0 e1 d0 d1 in lift-ConvTm (NeRes.conv r) (NeRes.s0 r)
  -- λ
  nf-conv {u0 = Lam C0 B0 b0} {u1 = Lam C1 B1 b1} (PR.nf-lam nA nb) refl e1 d0 d1 cA =
    let inj  = C-Lam-inj e1
        l0   = inv-Lam d0 ; l1 = inv-Lam d1
        dC0  = InvLam.dA l0 ; dB0 = InvLam.dB l0 ; db0 = InvLam.db l0
        cPi  = conv-Ty-trans (Sub-from-Pi (InvLam.sub l0))
                 (conv-Ty-trans cA (conv-Ty-sym (Sub-from-Pi (InvLam.sub l1))))
        pinj = PiInj-R cPi
        cC   = fst pinj ; cB = snd pinj
        db1' = ty-conv (ctx-conv-HasType (InvLam.dA l1) dC0 (conv-Ty-sym cC) (InvLam.db l1))
                       (conv-Ty-sym cB)                                       -- Γ.C0 ⊢ b1 : B0
        cb   = nf-conv nb refl (snd inj) db0 db1' (conv-Ty-refl dB0)
        step1 = conv-cong-Lam-body dC0 dB0 db0 cb
        step2 = conv-cong-Lam-Ty dC0 dB0 cC cB db1'
    in conv-conv (conv-trans step1 step2) (Sub-from-Pi (InvLam.sub l0))
  nf-conv {u0 = Lam _ _ _} {u1 = Var _} (PR.nf-lam nA nb)       refl ()
  nf-conv {u0 = Lam _ _ _} {u1 = U _} (PR.nf-lam nA nb)         refl ()
  nf-conv {u0 = Lam _ _ _} {u1 = Pi _ _} (PR.nf-lam nA nb)      refl ()
  nf-conv {u0 = Lam _ _ _} {u1 = App _ _ _ _} (PR.nf-lam nA nb) refl ()
  nf-conv {u0 = Var _} (PR.nf-lam nA nb)       ()
  nf-conv {u0 = U _} (PR.nf-lam nA nb)         ()
  nf-conv {u0 = Pi _ _} (PR.nf-lam nA nb)      ()
  nf-conv {u0 = App _ _ _ _} (PR.nf-lam nA nb) ()
  -- Π
  nf-conv {G = G} {u0 = Pi X0 Y0} {u1 = Pi X1 Y1} (PR.nf-pi nA nB) refl e1 d0 d1 cA =
    let inj  = C-Pi-inj e1
        p0   = inv-Pi d0 ; p1 = inv-Pi d1
        a0   = Sub-from-U (InvPi.sub p0) ; a1 = Sub-from-U (InvPi.sub p1)
        m    = AboveU.lv a0
        -- A0 = U m and A1 = U m1 with A0 = A1, hence m1 = m
        em   = U-inj-R (conv-Ty-trans (conv-Ty-sym (AboveU.cnv a1))
                          (conv-Ty-trans (conv-Ty-sym cA) (AboveU.cnv a0)))
        le1  = Le-cong {k = InvPi.lvl p1} em (AboveU.le a1)
        dX0  = cum-le (InvPi.lvl p0) m (AboveU.le a0) (InvPi.dA p0)
        dX1  = cum-le (InvPi.lvl p1) m le1 (InvPi.dA p1)
        dY0  = cum-le (InvPi.lvl p0) m (AboveU.le a0) (InvPi.dB p0)
        wfG  = typing-WfCtx (InvPi.dA p0)
        cX   = nf-conv nA refl (fst inj) dX0 dX1 (conv-Ty-refl (isType-U wfG))
        dY1  = cum-le (InvPi.lvl p1) m le1
                 (ctx-conv-HasType (is-Ty-from-U (InvPi.dA p1)) (is-Ty-from-U (InvPi.dA p0))
                    (conv-Ty-sym (conv-Ty-from-U cX)) (InvPi.dB p1))
        cY   = nf-conv nB refl (snd inj) dY0 dY1 (conv-Ty-refl (isType-U (typing-WfCtx dY0)))
    in conv-conv (conv-cong-Pi dX0 dY0 cX cY) (conv-Ty-sym (AboveU.cnv a0))
  nf-conv {u0 = Pi _ _} {u1 = Var _} (PR.nf-pi nA nB)       refl ()
  nf-conv {u0 = Pi _ _} {u1 = U _} (PR.nf-pi nA nB)         refl ()
  nf-conv {u0 = Pi _ _} {u1 = Lam _ _ _} (PR.nf-pi nA nB)   refl ()
  nf-conv {u0 = Pi _ _} {u1 = App _ _ _ _} (PR.nf-pi nA nB) refl ()
  nf-conv {u0 = Var _} (PR.nf-pi nA nB)       ()
  nf-conv {u0 = U _} (PR.nf-pi nA nB)         ()
  nf-conv {u0 = Lam _ _ _} (PR.nf-pi nA nB)   ()
  nf-conv {u0 = App _ _ _ _} (PR.nf-pi nA nB) ()
  -- U
  nf-conv {u0 = U l} {u1 = U .l} PR.nf-U refl refl d0 d1 cA = conv-refl d0
  nf-conv {u0 = U _} {u1 = Var _} PR.nf-U       refl ()
  nf-conv {u0 = U _} {u1 = Pi _ _} PR.nf-U      refl ()
  nf-conv {u0 = U _} {u1 = Lam _ _ _} PR.nf-U   refl ()
  nf-conv {u0 = U _} {u1 = App _ _ _ _} PR.nf-U refl ()
  nf-conv {u0 = Var _} PR.nf-U       ()
  nf-conv {u0 = Pi _ _} PR.nf-U      ()
  nf-conv {u0 = Lam _ _ _} PR.nf-U   ()
  nf-conv {u0 = App _ _ _ _} PR.nf-U ()

-- types with a β-normal stripping
nfTy-conv : {n : Nat} {G : Ctx n} {A B : Expr n} {N : C.Expr n} -> PR.Nf N ->
  Eq (strip A) N -> Eq (strip B) N -> IsType G A -> IsType G B -> ConvTy G A B
nfTy-conv nf e0 e1 (is-Ty-from-U {l = la} dA) (is-Ty-from-U {l = lb} dB) =
  conv-Ty-from-U
    (nf-conv nf e0 e1 (cum-le la (max la lb) (Le-max-l la lb) dA) (cum-le lb (max la lb) (Le-max-r la lb) dB)
       (conv-Ty-refl (isType-U (typing-WfCtx dA))))

------------------------------------------------------------------------
-- (2) General terms, assuming weak β-normalisation of T_P
------------------------------------------------------------------------

module _ (wn : PR.WN-P) where

  -- Lemma 4.17/4.18, type part
  type-uniq-R : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
    IsType G A0 -> IsType G A1 -> Eq (strip A0) (strip A1) -> ConvTy G A0 A1
  type-uniq-R {A0 = A0} {A1 = A1} (is-Ty-from-U d0) (is-Ty-from-U d1) e =
    let w   = wn (strip-HasType d0)
        L0  = liftStar (fst (snd w)) A0 refl
        L1  = liftStar (fst (snd w)) A1 (Eq-sym e)
        c0  = SR-star d0 (LiftedStar.red L0)
        c1  = SR-star d1 (LiftedStar.red L1)
        c   = nfTy-conv (snd (snd w)) (LiftedStar.eq L0) (LiftedStar.eq L1)
                (is-Ty-from-U (presup-r-ConvTm c0)) (is-Ty-from-U (presup-r-ConvTm c1))
    in conv-Ty-trans (conv-Ty-from-U c0) (conv-Ty-trans c (conv-Ty-sym (conv-Ty-from-U c1)))

  -- terms at convertible types
  term-uniq-conv-R : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
    HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> ConvTy G A0 A1 ->
    ConvTm G u0 u1 A0
  term-uniq-conv-R {u0 = u0} {u1 = u1} d0 d1 e cA =
    let w   = wn (strip-HasType d0)
        L0  = liftStar (fst (snd w)) u0 refl
        L1  = liftStar (fst (snd w)) u1 (Eq-sym e)
        c0  = SR-star d0 (LiftedStar.red L0)
        c1  = SR-star d1 (LiftedStar.red L1)
        c   = nf-conv (snd (snd w)) (LiftedStar.eq L0) (LiftedStar.eq L1)
                (presup-r-ConvTm c0) (presup-r-ConvTm c1) cA
    in conv-trans c0 (conv-trans c (conv-conv (conv-sym c1) (conv-Ty-sym cA)))

  -- Lemma 4.18
  term-uniq-R : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
    HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> Eq (strip A0) (strip A1) ->
    Pair (ConvTy G A0 A1) (ConvTm G u0 u1 A0)
  term-uniq-R d0 d1 eu eA =
    let cA = type-uniq-R (typing-IsType d0) (typing-IsType d1) eA
    in mkSigma cA (term-uniq-conv-R d0 d1 eu cA)
