{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Coerce
--
-- η-coercions and joins for the normalisation-free proof of Lemma 4.18
-- (ERT.StripUniqNF, extended to level and constraint products).
--
-- T_R has cumulativity only as subsumption between universes, so
-- terms whose types differ by universe levels under a binder are
-- related through η-expansions with cumulativity at the leaves:
--
--   coe_{Π(A,B) ≤ Π(A,L)} t = λ(A, L, coe_{B≤L} (app(A↑,B↑,t↑,v0)))
--   coe_{[α]A ≤ [α]L}     t = ⟨α⟩_L  coe_{A≤L} (t↑ α)
--   coe_{[ψ]A ≤ [ψ]L}     t = ⟨ψ⟩_L  coe_{A≤L} t
--
-- Join G T0 T1 L k0 k1: L is the "pointwise join" of T0 and T1 (they
-- agree up to conversion except for universe levels, also under Π, [α]
-- and [ψ]); k0, k1 are the coercions into L.  The universe join is
-- U_{k∨m} (up to level equality): there is no least level.
--
-- Joins are stable under term substitution, level substitution and
-- strengthening of the constraints (relevelling).
------------------------------------------------------------------------

module BCDE4.Coerce where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.RussellLsub
open import BCDE4.RussellRelevel using (Skel ; CEnt ; sk-extend ; skel-addC ; skel-addL ; ent-addC ; ent-addL ;
  relev-WfCtx ; relev-IsType ; relev-HasType ; relev-ConvTy ; relev-ConvTm ; wkC-HasType ; wkC-ConvTm ; wkC-WfCtx)
open import BCDE4.RussellInversion using (leL-supl ; U-resp ; U-resp-Tm)

------------------------------------------------------------------------
-- ψ holds in Γ,ψ
------------------------------------------------------------------------

valid-top : {Th : LCtx} (c : Constr) -> ValidC (lcons c Th) c
valid-top (ceq l m) = v-hyp lhere

valid-addC : {n : Nat} (G : Ctx n) (c : Constr) -> ValidC (lctx (addC G c)) c
valid-addC G c = Eq-transport (\ T -> ValidC T c) (Eq-sym (lctx-addC G c)) (valid-top c)

-- a term of type [ψ]A has type A in Γ,ψ
unguard-HasType : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n} ->
  IsType (addC G c) A -> HasType G t (Grd c A) -> HasType (addC G c) t A
unguard-HasType {G = G} {c} dA dt = ty-conv (wkC-HasType c dt) (conv-Ty-Grd-beta (valid-addC G c) dA)

unguard-ConvTm : {n : Nat} {G : Ctx n} {c : Constr} {A t t' : Expr n} ->
  IsType (addC G c) A -> ConvTm G t t' (Grd c A) -> ConvTm (addC G c) t t' A
unguard-ConvTm {G = G} {c} dA e = conv-conv (wkC-ConvTm c e) (conv-Ty-Grd-beta (valid-addC G c) dA)

------------------------------------------------------------------------
-- Application to the fresh variable
------------------------------------------------------------------------

liftWk : {n : Nat} -> Expr (suc n) -> Expr (suc (suc n))
liftWk B = renExpr (liftRen wkRen) B

-- app(A↑, B↑, t↑, v0)
appv0 : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n -> Expr (suc n)
appv0 A B t = App (wkExpr A) (liftWk B) (wkExpr t) (Var fzero)

isType-liftWk : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> IsType (extend (extend G A) (wkExpr A)) (liftWk B)
isType-liftWk {G = G} {A = A} dA dB =
  ren-IsType (liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A})) ent-refl (wf-extend (wk-IsType dA dA)) dB

hasType-liftWk : {n : Nat} {G : Ctx n} {A : Expr n} {b B : Expr (suc n)}
  -> IsType G A -> HasType (extend G A) b B
  -> HasType (extend (extend G A) (wkExpr A)) (liftWk b) (liftWk B)
hasType-liftWk {G = G} {A = A} dA db =
  ren-HasType (liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A})) ent-refl (wf-extend (wk-IsType dA dA)) db

appv0-ty : {n : Nat} {G : Ctx n} {A t : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> HasType G t (Pi A B)
  -> HasType (extend G A) (appv0 A B t) B
appv0-ty {G = G} {A = A} {t = t} {B = B} dA dB dt =
  Eq-transport (\ T -> HasType (extend G A) (appv0 A B t) T) (subst1-liftWk-cancel B)
    (ty-App (wk-IsType dA dA) (isType-liftWk dA dB) (wk-HasType dA dt) (ty-var (wf-extend dA)))

appv0-cong : {n : Nat} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> ConvTm G t t' (Pi A B)
  -> ConvTm (extend G A) (appv0 A B t) (appv0 A B t') B
appv0-cong {G = G} {A = A} {t = t} {t' = t'} {B = B} dA dB e =
  Eq-transport (\ T -> ConvTm (extend G A) (appv0 A B t) (appv0 A B t') T) (subst1-liftWk-cancel B)
    (conv-cong-App-fun (wk-IsType dA dA) (isType-liftWk dA dB) (wk-ConvTm dA e) (ty-var (wf-extend dA)))

-- app(A↑, B↑, λ(A,B,b)↑, v0) = b : B
lam-beta-v0 : {n : Nat} {G : Ctx n} {A : Expr n} {B b : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> HasType (extend G A) b B
  -> ConvTm (extend G A) (appv0 A B (Lam A B b)) b B
lam-beta-v0 {G = G} {A = A} {B = B} {b = b} dA dB db =
  Eq-transport (\ T -> ConvTm (extend G A) (appv0 A B (Lam A B b)) b T) (subst1-liftWk-cancel B)
    (Eq-transport (\ M -> ConvTm (extend G A) (appv0 A B (Lam A B b)) M (subst1 (liftWk B) (Var fzero)))
      (subst1-liftWk-cancel b)
      (conv-beta (wk-IsType dA dA) (isType-liftWk dA dB) (hasType-liftWk dA db) (ty-var (wf-extend dA))))

subst1-lift-liftWk : {n : Nat} (a : Expr n) (B : Expr (suc n))
  -> Eq (substExpr (liftSub (subst1Sub a)) (liftWk B)) B
subst1-lift-liftWk a B =
  Eq-trans (subst-ren (liftSub (subst1Sub a)) (liftRen wkRen) B)
    (Eq-trans (substExpr-ext _ idSub (\ { fzero -> refl ; (fsuc i) -> refl }) B) (substExpr-id B))

appv0-subst : {h g : Nat} (s : Sub h g) (A : Expr g) (B : Expr (suc g)) (t : Expr g)
  -> Eq (substExpr (liftSub s) (appv0 A B t)) (appv0 (substExpr s A) (substExpr (liftSub s) B) (substExpr s t))
appv0-subst s A B t = Eq-cong4 App (subst-wk-comm s A) (liftSub-liftSub-wk-comm s B) (subst-wk-comm s t) refl

appv0-subst1 : {n : Nat} (a A : Expr n) (B : Expr (suc n)) (t : Expr n)
  -> Eq (substExpr (subst1Sub a) (appv0 A B t)) (App A B t a)
appv0-subst1 a A B t = Eq-cong4 App (subst1-wk A a) (subst1-lift-liftWk a B) (subst1-wk t a) refl

appv0-lsub : {n : Nat} (z : LSub) (A : Expr n) (B : Expr (suc n)) (t : Expr n)
  -> Eq (lsubE z (appv0 A B t)) (appv0 (lsubE z A) (lsubE z B) (lsubE z t))
appv0-lsub z A B t = Eq-cong4 App (lsubE-ren z wkRen A) (lsubE-ren z (liftRen wkRen) B) (lsubE-ren z wkRen t) refl

------------------------------------------------------------------------
-- Level application to the fresh level variable
------------------------------------------------------------------------

-- the annotation of t↑ α
liftLw : {n : Nat} -> Expr n -> Expr n
liftLw A = lsubE (liftL lwkS) A

-- (t↑) α
lappv0 : {n : Nat} -> Expr n -> Expr n -> Expr n
lappv0 A t = LApp (liftLw A) (lshiftE t) (lvar zero)

-- weakening along a fresh level
shI : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType G A -> IsType (addL G) (lshiftE A)
shI {G = G} = lsub-IsType (lsk-shift G) (lok-shift G)
shH : {n : Nat} {G : Ctx n} {M A : Expr n} -> HasType G M A -> HasType (addL G) (lshiftE M) (lshiftE A)
shH {G = G} = lsub-HasType (lsk-shift G) (lok-shift G)
shM : {n : Nat} {G : Ctx n} {M N A : Expr n} -> ConvTm G M N A -> ConvTm (addL G) (lshiftE M) (lshiftE N) (lshiftE A)
shM {G = G} = lsub-ConvTm (lsk-shift G) (lok-shift G)

-- under the level binder
shI2 : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType (addL G) A -> IsType (addL (addL G)) (liftLw A)
shI2 {G = G} = lsub-IsType (lsk-addL (lsk-shift G)) (lok-addL G (addL G) (lok-shift G))
shH2 : {n : Nat} {G : Ctx n} {M A : Expr n} -> HasType (addL G) M A -> HasType (addL (addL G)) (liftLw M) (liftLw A)
shH2 {G = G} = lsub-HasType (lsk-addL (lsk-shift G)) (lok-addL G (addL G) (lok-shift G))

lappv0-ty : {n : Nat} {G : Ctx n} {A t : Expr n}
  -> IsType (addL G) A -> HasType G t (LPi A) -> HasType (addL G) (lappv0 A t) A
lappv0-ty {G = G} {A = A} {t = t} dA dt =
  Eq-transport (HasType (addL G) (lappv0 A t)) (lsub1-lift-var A) (ty-LApp (shI2 dA) (shH dt))

lappv0-cong : {n : Nat} {G : Ctx n} {A t t' : Expr n}
  -> IsType (addL G) A -> ConvTm G t t' (LPi A) -> ConvTm (addL G) (lappv0 A t) (lappv0 A t') A
lappv0-cong {G = G} {A = A} {t = t} {t' = t'} dA e =
  Eq-transport (ConvTm (addL G) (lappv0 A t) (lappv0 A t')) (lsub1-lift-var A)
    (conv-cong-LApp-fun (shI2 dA) (shM e))

-- (⟨α⟩u)↑ α = u : A
llam-beta-v0 : {n : Nat} {G : Ctx n} {A u : Expr n}
  -> IsType (addL G) A -> HasType (addL G) u A -> ConvTm (addL G) (lappv0 A (LLam A u)) u A
llam-beta-v0 {G = G} {A = A} {u = u} dA du =
  Eq-transport (ConvTm (addL G) (lappv0 A (LLam A u)) u) (lsub1-lift-var A)
    (Eq-transport (\ M -> ConvTm (addL G) (lappv0 A (LLam A u)) M (lsub1 (liftLw A) (lvar zero)))
      (lsub1-lift-var u)
      (conv-LApp-beta (shI2 dA) (shH2 du)))

lappv0-subst : {h g : Nat} (s : Sub h g) (A t : Expr g)
  -> Eq (substExpr (\ i -> lshiftE (s i)) (lappv0 A t))
        (lappv0 (substExpr (\ i -> lshiftE (s i)) A) (substExpr s t))
lappv0-subst s A t =
  Eq-cong2 (\ X Y -> LApp X Y (lvar zero)) (Eq-sym (subst-lshift2 s A)) (subst-lshift s t)

lappv0-lsub : {n : Nat} (z : LSub) (A t : Expr n)
  -> Eq (lsubE (liftL z) (lappv0 A t)) (lappv0 (lsubE (liftL z) A) (lsubE z t))
lappv0-lsub z A t =
  Eq-cong2 (\ X Y -> LApp X Y (lvar zero)) (lsubE-liftL2-shift z A) (lsubE-liftL-shift z t)

private
  lsub1-shiftE : {n : Nat} (l : LExpr) (t : Expr n) -> Eq (lsubE (lsub1S l) (lshiftE t)) t
  lsub1-shiftE l t = Eq-trans (lsubE-comp (lsub1S l) lwkS t) (Eq-trans (lsubE-ext _ _ (\ i -> refl) t) (lsubE-id t))

  lsub1-liftLw : {n : Nat} (l : LExpr) (A : Expr n) -> Eq (lsubE (liftL (lsub1S l)) (liftLw A)) A
  lsub1-liftLw l A =
    Eq-trans (lsubE-comp (liftL (lsub1S l)) (liftL lwkS) A)
      (Eq-trans (lsubE-ext _ _ pt A) (lsubE-id A))
    where
      pt : (i : Nat) -> Eq (lcomp (liftL (lsub1S l)) (liftL lwkS) i) (lidS i)
      pt zero    = refl
      pt (suc i) = refl

-- instantiating (t↑ α) at l gives t l
lappv0-inst : {n : Nat} (l : LExpr) (A t : Expr n) -> Eq (lsubE (lsub1S l) (lappv0 A t)) (LApp A t l)
lappv0-inst l A t = Eq-cong2 (\ X Y -> LApp X Y l) (lsub1-liftLw l A) (lsub1-shiftE l t)

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

data Co : Nat -> Set where
  idC  : {n : Nat} -> Co n
  piC  : {n : Nat} -> Expr n -> Expr (suc n) -> Expr (suc n) -> Co (suc n) -> Co n   -- A B L k
  lpiC : {n : Nat} -> Expr n -> Expr n -> Co n -> Co n                                -- A L k  (under α)
  grdC : {n : Nat} -> Constr -> Expr n -> Co n -> Co n                                -- ψ L k

coe : {n : Nat} -> Co n -> Expr n -> Expr n
coe idC           t = t
coe (piC A B L k) t = Lam A L (coe k (appv0 A B t))
coe (lpiC A L k)  t = LLam L (coe k (lappv0 A t))
coe (grdC c L k)  t = GLam c L (coe k t)

substCo : {h g : Nat} -> Sub h g -> Co g -> Co h
substCo s idC           = idC
substCo s (piC A B L k) = piC (substExpr s A) (substExpr (liftSub s) B) (substExpr (liftSub s) L) (substCo (liftSub s) k)
substCo s (lpiC A L k)  = lpiC (substExpr (\ i -> lshiftE (s i)) A) (substExpr (\ i -> lshiftE (s i)) L)
                               (substCo (\ i -> lshiftE (s i)) k)
substCo s (grdC c L k)  = grdC c (substExpr s L) (substCo s k)

coe-subst : {h g : Nat} (s : Sub h g) (k : Co g) (t : Expr g)
  -> Eq (substExpr s (coe k t)) (coe (substCo s k) (substExpr s t))
coe-subst s idC           t = refl
coe-subst s (piC A B L k) t =
  Eq-cong (Lam (substExpr s A) (substExpr (liftSub s) L))
    (Eq-trans (coe-subst (liftSub s) k (appv0 A B t))
              (Eq-cong (coe (substCo (liftSub s) k)) (appv0-subst s A B t)))
coe-subst s (lpiC A L k)  t =
  Eq-cong (LLam (substExpr (\ i -> lshiftE (s i)) L))
    (Eq-trans (coe-subst (\ i -> lshiftE (s i)) k (lappv0 A t))
              (Eq-cong (coe (substCo (\ i -> lshiftE (s i)) k)) (lappv0-subst s A t)))
coe-subst s (grdC c L k)  t = Eq-cong (GLam c (substExpr s L)) (coe-subst s k t)

lsubCo : {n : Nat} -> LSub -> Co n -> Co n
lsubCo z idC           = idC
lsubCo z (piC A B L k) = piC (lsubE z A) (lsubE z B) (lsubE z L) (lsubCo z k)
lsubCo z (lpiC A L k)  = lpiC (lsubE (liftL z) A) (lsubE (liftL z) L) (lsubCo (liftL z) k)
lsubCo z (grdC c L k)  = grdC (lsubC z c) (lsubE z L) (lsubCo z k)

coe-lsub : {n : Nat} (z : LSub) (k : Co n) (t : Expr n)
  -> Eq (lsubE z (coe k t)) (coe (lsubCo z k) (lsubE z t))
coe-lsub z idC           t = refl
coe-lsub z (piC A B L k) t =
  Eq-cong (Lam (lsubE z A) (lsubE z L))
    (Eq-trans (coe-lsub z k (appv0 A B t)) (Eq-cong (coe (lsubCo z k)) (appv0-lsub z A B t)))
coe-lsub z (lpiC A L k)  t =
  Eq-cong (LLam (lsubE (liftL z) L))
    (Eq-trans (coe-lsub (liftL z) k (lappv0 A t)) (Eq-cong (coe (lsubCo (liftL z) k)) (lappv0-lsub z A t)))
coe-lsub z (grdC c L k)  t = Eq-cong (GLam (lsubC z c) (lsubE z L)) (coe-lsub z k t)

------------------------------------------------------------------------
-- Joins
------------------------------------------------------------------------

data Join : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Co n -> Co n -> Set where
  jconv : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n}
    -> ConvTy G T0 L -> ConvTy G T1 L -> Join G T0 T1 L idC idC
  juniv : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} (k m p : LExpr) -> Valid (lctx G) p (lsup k m)
    -> ConvTy G T0 (U k) -> ConvTy G T1 (U m) -> Join G T0 T1 (U p) idC idC
  jpi : {n : Nat} {G : Ctx n} {T0 T1 A : Expr n} {B0 B1 L : Expr (suc n)} {k0 k1 : Co (suc n)}
    -> IsType G A -> IsType (extend G A) B0 -> IsType (extend G A) B1
    -> ConvTy G T0 (Pi A B0) -> ConvTy G T1 (Pi A B1)
    -> Join (extend G A) B0 B1 L k0 k1
    -> Join G T0 T1 (Pi A L) (piC A B0 L k0) (piC A B1 L k1)
  jlpi : {n : Nat} {G : Ctx n} {T0 T1 B0 B1 L : Expr n} {k0 k1 : Co n}
    -> WfCtx G -> IsType (addL G) B0 -> IsType (addL G) B1
    -> ConvTy G T0 (LPi B0) -> ConvTy G T1 (LPi B1)
    -> Join (addL G) B0 B1 L k0 k1
    -> Join G T0 T1 (LPi L) (lpiC B0 L k0) (lpiC B1 L k1)
  jgrd : {n : Nat} {G : Ctx n} {c : Constr} {T0 T1 B0 B1 L : Expr n} {k0 k1 : Co n}
    -> WfCtx G -> IsType (addC G c) B0 -> IsType (addC G c) B1
    -> ConvTy G T0 (Grd c B0) -> ConvTy G T1 (Grd c B1)
    -> Join (addC G c) B0 B1 L k0 k1
    -> Join G T0 T1 (Grd c L) (grdC c L k0) (grdC c L k1)

Join-sym : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> Join G T1 T0 L k1 k0
Join-sym (jconv c0 c1)                = jconv c1 c0
Join-sym (juniv k m p v c0 c1)        = juniv m k p (v-trans v v-comm) c1 c0
Join-sym (jpi dA dB0 dB1 cv0 cv1 j)   = jpi dA dB1 dB0 cv1 cv0 (Join-sym j)
Join-sym (jlpi wf dB0 dB1 cv0 cv1 j)  = jlpi wf dB1 dB0 cv1 cv0 (Join-sym j)
Join-sym (jgrd wf dB0 dB1 cv0 cv1 j)  = jgrd wf dB1 dB0 cv1 cv0 (Join-sym j)

retarget : {n : Nat} {G : Ctx n} {T0 T1 T0' T1' L : Expr n} {k0 k1 : Co n}
  -> ConvTy G T0' T0 -> ConvTy G T1' T1 -> Join G T0 T1 L k0 k1 -> Join G T0' T1' L k0 k1
retarget e0 e1 (jconv c0 c1)               = jconv (conv-Ty-trans e0 c0) (conv-Ty-trans e1 c1)
retarget e0 e1 (juniv k m p v c0 c1)       = juniv k m p v (conv-Ty-trans e0 c0) (conv-Ty-trans e1 c1)
retarget e0 e1 (jpi dA dB0 dB1 cv0 cv1 j)  = jpi dA dB0 dB1 (conv-Ty-trans e0 cv0) (conv-Ty-trans e1 cv1) j
retarget e0 e1 (jlpi wf dB0 dB1 cv0 cv1 j) = jlpi wf dB0 dB1 (conv-Ty-trans e0 cv0) (conv-Ty-trans e1 cv1) j
retarget e0 e1 (jgrd wf dB0 dB1 cv0 cv1 j) = jgrd wf dB0 dB1 (conv-Ty-trans e0 cv0) (conv-Ty-trans e1 cv1) j

join-L : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> IsType G L
join-L (jconv c0 c1)               = presup-r-ConvTy c0
join-L (juniv k m p v c0 c1)       = isType-U (isType-WfCtx (presup-l-ConvTy c0))
join-L (jpi dA dB0 dB1 cv0 cv1 j)  = is-Pi dA (join-L j)
join-L (jlpi wf dB0 dB1 cv0 cv1 j) = is-LPi wf (join-L j)
join-L (jgrd wf dB0 dB1 cv0 cv1 j) = is-Grd wf (join-L j)

join-T0 : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n} -> Join G T0 T1 L k0 k1 -> IsType G T0
join-T0 (jconv c0 c1)               = presup-l-ConvTy c0
join-T0 (juniv k m p v c0 c1)       = presup-l-ConvTy c0
join-T0 (jpi dA dB0 dB1 cv0 cv1 j)  = presup-l-ConvTy cv0
join-T0 (jlpi wf dB0 dB1 cv0 cv1 j) = presup-l-ConvTy cv0
join-T0 (jgrd wf dB0 dB1 cv0 cv1 j) = presup-l-ConvTy cv0

------------------------------------------------------------------------
-- Stability: term substitution, level substitution, relevelling
------------------------------------------------------------------------

Join-subst : {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} {T0 T1 L : Expr g} {k0 k1 : Co g}
  -> WtSub H G s -> WfCtx H -> Join G T0 T1 L k0 k1
  -> Join H (substExpr s T0) (substExpr s T1) (substExpr s L) (substCo s k0) (substCo s k1)
Join-subst ws wfH (jconv c0 c1) = jconv (subst-ConvTy ws wfH c0) (subst-ConvTy ws wfH c1)
Join-subst ws wfH (juniv k m p v c0 c1) =
  juniv k m p (valid-ent (wtE ws) v) (subst-ConvTy ws wfH c0) (subst-ConvTy ws wfH c1)
Join-subst ws wfH (jpi dA dB0 dB1 cv0 cv1 j) =
  let dA'  = subst-IsType ws wfH dA
      wfH' = wf-extend dA'
      ws'  = liftSub-WtSub ws wfH dA
  in jpi dA' (subst-IsType ws' wfH' dB0) (subst-IsType ws' wfH' dB1)
         (subst-ConvTy ws wfH cv0) (subst-ConvTy ws wfH cv1) (Join-subst ws' wfH' j)
Join-subst ws wfH (jlpi wf dB0 dB1 cv0 cv1 j) =
  let ws' = WtSub-addL ws ; wf' = wkL-WfCtx wfH
  in jlpi wfH (subst-IsType ws' wf' dB0) (subst-IsType ws' wf' dB1)
          (subst-ConvTy ws wfH cv0) (subst-ConvTy ws wfH cv1) (Join-subst ws' wf' j)
Join-subst ws wfH (jgrd {c = c} wf dB0 dB1 cv0 cv1 j) =
  let ws' = WtSub-addC c ws ; wf' = wkC-WfCtx c wfH
  in jgrd wfH (subst-IsType ws' wf' dB0) (subst-IsType ws' wf' dB1)
          (subst-ConvTy ws wfH cv0) (subst-ConvTy ws wfH cv1) (Join-subst ws' wf' j)

Join-lsub : {z : LSub} {n : Nat} {G H : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> LSk z G H -> LOK z G H -> Join G T0 T1 L k0 k1
  -> Join H (lsubE z T0) (lsubE z T1) (lsubE z L) (lsubCo z k0) (lsubCo z k1)
Join-lsub s ok (jconv c0 c1) = jconv (lsub-ConvTy s ok c0) (lsub-ConvTy s ok c1)
Join-lsub {z} s ok (juniv k m p v c0 c1) =
  juniv (lsubL z k) (lsubL z m) (lsubL z p) (valid-lsub z ok v) (lsub-ConvTy s ok c0) (lsub-ConvTy s ok c1)
Join-lsub s ok (jpi dA dB0 dB1 cv0 cv1 j) =
  let s' = lsk-extend s refl
  in jpi (lsub-IsType s ok dA) (lsub-IsType s' ok dB0) (lsub-IsType s' ok dB1)
         (lsub-ConvTy s ok cv0) (lsub-ConvTy s ok cv1) (Join-lsub s' ok j)
Join-lsub {G = G} {H = H} s ok (jlpi wf dB0 dB1 cv0 cv1 j) =
  let s' = lsk-addL s ; ok' = lok-addL G H ok
  in jlpi (lsub-WfCtx s ok wf) (lsub-IsType s' ok' dB0) (lsub-IsType s' ok' dB1)
          (lsub-ConvTy s ok cv0) (lsub-ConvTy s ok cv1) (Join-lsub s' ok' j)
Join-lsub {G = G} {H = H} s ok (jgrd {c = c} wf dB0 dB1 cv0 cv1 j) =
  let s' = lsk-addC c s ; ok' = lok-addC G H c ok
  in jgrd (lsub-WfCtx s ok wf) (lsub-IsType s' ok' dB0) (lsub-IsType s' ok' dB1)
          (lsub-ConvTy s ok cv0) (lsub-ConvTy s ok cv1) (Join-lsub s' ok' j)

Join-relev : {n : Nat} {G H : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> Skel G H -> CEnt H G -> Join G T0 T1 L k0 k1 -> Join H T0 T1 L k0 k1
Join-relev s e (jconv c0 c1) = jconv (relev-ConvTy s e c0) (relev-ConvTy s e c1)
Join-relev s e (juniv k m p v c0 c1) = juniv k m p (valid-ent e v) (relev-ConvTy s e c0) (relev-ConvTy s e c1)
Join-relev s e (jpi dA dB0 dB1 cv0 cv1 j) =
  jpi (relev-IsType s e dA) (relev-IsType (sk-extend s) e dB0) (relev-IsType (sk-extend s) e dB1)
      (relev-ConvTy s e cv0) (relev-ConvTy s e cv1) (Join-relev (sk-extend s) e j)
Join-relev {G = G} {H = H} s e (jlpi wf dB0 dB1 cv0 cv1 j) =
  let s' = skel-addL s ; e' = ent-addL G H e
  in jlpi (relev-WfCtx s e wf) (relev-IsType s' e' dB0) (relev-IsType s' e' dB1)
          (relev-ConvTy s e cv0) (relev-ConvTy s e cv1) (Join-relev s' e' j)
Join-relev {G = G} {H = H} s e (jgrd {c = c} wf dB0 dB1 cv0 cv1 j) =
  let s' = skel-addC c s ; e' = ent-addC G H c e
  in jgrd (relev-WfCtx s e wf) (relev-IsType s' e' dB0) (relev-IsType s' e' dB1)
          (relev-ConvTy s e cv0) (relev-ConvTy s e cv1) (Join-relev s' e' j)

------------------------------------------------------------------------
-- Coercions are well typed and congruent
------------------------------------------------------------------------

private
  U-join-le : {n : Nat} {G : Ctx n} {M : Expr n} (k m p : LExpr) -> Valid (lctx G) p (lsup k m) ->
    HasType G M (U k) -> HasType G M (U p)
  U-join-le k m p v d = U-resp (v-sym v) (ty-cum d (leL-supl k m))

  U-join-le-Tm : {n : Nat} {G : Ctx n} {M N : Expr n} (k m p : LExpr) -> Valid (lctx G) p (lsup k m) ->
    ConvTm G M N (U k) -> ConvTm G M N (U p)
  U-join-le-Tm k m p v d = U-resp-Tm (v-sym v) (conv-cum d (leL-supl k m))

coe-ty : {n : Nat} {G : Ctx n} {T0 T1 L t : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> HasType G t T0 -> HasType G (coe k0 t) L
coe-ty (jconv c0 c1) d = ty-conv d c0
coe-ty (juniv k m p v c0 c1) d = U-join-le k m p v (ty-conv d c0)
coe-ty (jpi dA dB0 dB1 cv0 cv1 j) d =
  ty-Lam dA (join-L j) (coe-ty j (appv0-ty dA dB0 (ty-conv d cv0)))
coe-ty (jlpi wf dB0 dB1 cv0 cv1 j) d =
  ty-LLam wf (join-L j) (coe-ty j (lappv0-ty dB0 (ty-conv d cv0)))
coe-ty (jgrd wf dB0 dB1 cv0 cv1 j) d =
  ty-GLam wf (join-L j) (coe-ty j (unguard-HasType dB0 (ty-conv d cv0)))

coe-cong : {n : Nat} {G : Ctx n} {T0 T1 L t t' : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> ConvTm G t t' T0 -> ConvTm G (coe k0 t) (coe k0 t') L
coe-cong (jconv c0 c1) e = conv-conv e c0
coe-cong (juniv k m p v c0 c1) e = U-join-le-Tm k m p v (conv-conv e c0)
coe-cong (jpi dA dB0 dB1 cv0 cv1 j) e =
  let ih = coe-cong j (appv0-cong dA dB0 (conv-conv e cv0))
  in conv-cong-Lam-body dA (join-L j) (presup-l-ConvTm ih) ih
coe-cong (jlpi wf dB0 dB1 cv0 cv1 j) e =
  let ih = coe-cong j (lappv0-cong dB0 (conv-conv e cv0))
  in conv-cong-LLam wf (join-L j) (presup-l-ConvTm ih) ih
coe-cong (jgrd wf dB0 dB1 cv0 cv1 j) e =
  let ih = coe-cong j (unguard-ConvTm dB0 (conv-conv e cv0))
  in conv-cong-GLam wf (join-L j) (presup-l-ConvTm ih) ih

------------------------------------------------------------------------
-- Coercions compute under the eliminations
------------------------------------------------------------------------

-- app(A, L, coe_{Π(A,B) ≤ Π(A,L)} t, a) = coe_{B[a] ≤ L[a]} (app(A,B,t,a)) : L[a]
coe-beta : {n : Nat} {G : Ctx n} {A t a : Expr n} {B L : Expr (suc n)} {k : Co (suc n)}
  -> IsType G A -> IsType (extend G A) L
  -> HasType (extend G A) (coe k (appv0 A B t)) L -> HasType G a A
  -> ConvTm G (App A L (coe (piC A B L k) t) a) (coe (substCo (subst1Sub a) k) (App A B t a)) (subst1 L a)
coe-beta {G = G} {A = A} {t = t} {a = a} {B = B} {L = L} {k = k} dA dL hb da =
  Eq-transport (\ M -> ConvTm G (App A L (coe (piC A B L k) t) a) M (subst1 L a))
    (Eq-trans (coe-subst (subst1Sub a) k (appv0 A B t))
              (Eq-cong (coe (substCo (subst1Sub a) k)) (appv0-subst1 a A B t)))
    (conv-beta dA dL hb da)

-- (coe_{[α]A ≤ [α]L} t) l = coe_{A[l] ≤ L[l]} (t l) : L[l]
coe-lbeta : {n : Nat} {G : Ctx n} {A L t : Expr n} {k : Co n} (l : LExpr)
  -> IsType (addL G) L -> HasType (addL G) (coe k (lappv0 A t)) L
  -> ConvTm G (LApp L (coe (lpiC A L k) t) l) (coe (lsubCo (lsub1S l) k) (LApp A t l)) (lsub1 L l)
coe-lbeta {G = G} {A = A} {L = L} {t = t} {k = k} l dL hb =
  Eq-transport (\ M -> ConvTm G (LApp L (coe (lpiC A L k) t) l) M (lsub1 L l))
    (Eq-trans (coe-lsub (lsub1S l) k (lappv0 A t))
              (Eq-cong (coe (lsubCo (lsub1S l) k)) (lappv0-inst l A t)))
    (conv-LApp-beta dL hb)
