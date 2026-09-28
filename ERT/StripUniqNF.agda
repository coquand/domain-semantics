{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.StripUniqNF
--
-- Lemma 4.18 (redundancy of the annotations of T_R) WITHOUT
-- normalisation: a structural induction on the term, using only
-- Π-injectivity, injectivity of universes and Π/U no-confusion.
--
-- Why the naive induction fails (Gap417): the stripped-equal functions
--   f0 = λ(U1,U1,v0) : Π(U1,U1)     f1 = λ(U1,U2,v0) : Π(U1,U2)
-- are NOT convertible (their types are different), yet app(f0,U0) and
-- app(f1,U0) are.  So the induction hypothesis must relate terms whose
-- types differ by cumulativity UNDER Π.  T_R has no such subtyping,
-- but it is definable: the coercion
--   coe_{Π(A,B) ≤ Π(A,L)} t = λ(A, L, coe_{B ≤ L} (app(A↑,B↑,t↑,v0)))
-- (η-expansion, with cumulativity at the leaves).
--
-- Join G T0 T1 L k0 k1: L is the "pointwise maximum" of T0 and T1
-- (they agree up to conversion except for universe levels, which may
-- differ also under Π), and k0, k1 describe the coercions into L.
--
-- Main lemma (main): if Γ ⊢ u0 : T0, Γ ⊢ u1 : T1 and strip u0 = strip u1,
-- then there is a Join G T0 T1 L k0 k1 with Γ ⊢ coe k0 u0 = coe k1 u1 : L.
--
-- When T0 = T1 the join is trivial and coercions are injective (η):
-- Join-diag.  Hence Lemma 4.18.
------------------------------------------------------------------------

module ERT.StripUniqNF where

open import ERT.Basic
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.RussellMetaCong using (subst1-cong-Ty)
open import ERT.RussellInversion
open import ERT.PiInjectivityR using (PiInj-R)
open import ERT.Model.Strip using (strip)
import ERT.Model.Core as C

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

max-comm : (a b : Nat) -> Eq (max a b) (max b a)
max-comm zero    zero    = refl
max-comm zero    (suc b) = refl
max-comm (suc a) zero    = refl
max-comm (suc a) (suc b) = Eq-cong suc (max-comm a b)

max-idem : (a : Nat) -> Eq (max a a) a
max-idem zero    = refl
max-idem (suc a) = Eq-cong suc (max-idem a)

max-lub : (a b c : Nat) -> Le a c -> Le b c -> Le (max a b) c
max-lub zero    b       c       _ h = h
max-lub (suc a) zero    c       h _ = h
max-lub (suc a) (suc b) zero    () _
max-lub (suc a) (suc b) (suc c) h h' = max-lub a b c h h'

Le-max-mono : (a b c d : Nat) -> Le a c -> Le b d -> Le (max a b) (max c d)
Le-max-mono a b c d h h' =
  max-lub a b (max c d) (Le-trans a c (max c d) h (Le-max-l c d))
                        (Le-trans b d (max c d) h' (Le-max-r c d))

------------------------------------------------------------------------
-- Application to the fresh variable, and its typing
------------------------------------------------------------------------

liftWk : {n : Nat} -> Expr (suc n) -> Expr (suc (suc n))
liftWk B = renExpr (liftRen wkRen) B

-- app(A↑, B↑, t↑, v0)
appv0 : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n -> Expr (suc n)
appv0 A B t = App (wkExpr A) (liftWk B) (wkExpr t) (Var fzero)

isType-liftWk : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> IsType (extend (extend G A) (wkExpr A)) (liftWk B)
isType-liftWk {G = G} {A = A} dA dB =
  ren-IsType (liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A})) (wf-extend (wk-IsType dA dA)) dB

hasType-liftWk : {n : Nat} {G : Ctx n} {A : Expr n} {b B : Expr (suc n)}
  -> IsType G A -> HasType (extend G A) b B
  -> HasType (extend (extend G A) (wkExpr A)) (liftWk b) (liftWk B)
hasType-liftWk {G = G} {A = A} dA db =
  ren-HasType (liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A})) (wf-extend (wk-IsType dA dA)) db

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

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

-- piC A B L k : from Π(A,B) to Π(A,L), with k from B to L
data Co : Nat -> Set where
  idC : {n : Nat} -> Co n
  piC : {n : Nat} -> Expr n -> Expr (suc n) -> Expr (suc n) -> Co (suc n) -> Co n

coe : {n : Nat} -> Co n -> Expr n -> Expr n
coe idC           t = t
coe (piC A B L k) t = Lam A L (coe k (appv0 A B t))

substCo : {h g : Nat} -> Sub h g -> Co g -> Co h
substCo s idC           = idC
substCo s (piC A B L k) = piC (substExpr s A) (substExpr (liftSub s) B) (substExpr (liftSub s) L) (substCo (liftSub s) k)

coe-subst : {h g : Nat} (s : Sub h g) (k : Co g) (t : Expr g)
  -> Eq (substExpr s (coe k t)) (coe (substCo s k) (substExpr s t))
coe-subst s idC           t = refl
coe-subst s (piC A B L k) t =
  Eq-cong (Lam (substExpr s A) (substExpr (liftSub s) L))
    (Eq-trans (coe-subst (liftSub s) k (appv0 A B t))
              (Eq-cong (coe (substCo (liftSub s) k)) (appv0-subst s A B t)))

------------------------------------------------------------------------
-- Joins
------------------------------------------------------------------------

data Join : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Co n -> Co n -> Set where
  jconv : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n}
    -> ConvTy G T0 L -> ConvTy G T1 L -> Join G T0 T1 L idC idC
  juniv : {n : Nat} {G : Ctx n} {T0 T1 : Expr n} (k m p : Nat) -> Eq p (max k m)
    -> ConvTy G T0 (U k) -> ConvTy G T1 (U m) -> Join G T0 T1 (U p) idC idC
  jpi : {n : Nat} {G : Ctx n} {T0 T1 A : Expr n} {B0 B1 L : Expr (suc n)} {k0 k1 : Co (suc n)}
    -> IsType G A -> IsType (extend G A) B0 -> IsType (extend G A) B1
    -> ConvTy G T0 (Pi A B0) -> ConvTy G T1 (Pi A B1)
    -> Join (extend G A) B0 B1 L k0 k1
    -> Join G T0 T1 (Pi A L) (piC A B0 L k0) (piC A B1 L k1)

Join-sym : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> Join G T1 T0 L k1 k0
Join-sym (jconv c0 c1)             = jconv c1 c0
Join-sym (juniv k m p ep c0 c1)    = juniv m k p (Eq-trans ep (max-comm k m)) c1 c0
Join-sym (jpi dA dB0 dB1 cv0 cv1 j) = jpi dA dB1 dB0 cv1 cv0 (Join-sym j)

retarget : {n : Nat} {G : Ctx n} {T0 T1 T0' T1' L : Expr n} {k0 k1 : Co n}
  -> ConvTy G T0' T0 -> ConvTy G T1' T1 -> Join G T0 T1 L k0 k1 -> Join G T0' T1' L k0 k1
retarget e0 e1 (jconv c0 c1)              = jconv (conv-Ty-trans e0 c0) (conv-Ty-trans e1 c1)
retarget e0 e1 (juniv k m p ep c0 c1)     = juniv k m p ep (conv-Ty-trans e0 c0) (conv-Ty-trans e1 c1)
retarget e0 e1 (jpi dA dB0 dB1 cv0 cv1 j) = jpi dA dB0 dB1 (conv-Ty-trans e0 cv0) (conv-Ty-trans e1 cv1) j

join-L : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> IsType G L
join-L (jconv c0 c1)              = presup-r-ConvTy c0
join-L (juniv k m p ep c0 c1)     = isType-U (isType-WfCtx (presup-l-ConvTy c0))
join-L (jpi dA dB0 dB1 cv0 cv1 j) = isType-Pi dA (join-L j)

Join-subst : {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} {T0 T1 L : Expr g} {k0 k1 : Co g}
  -> WtSub H G s -> WfCtx H -> Join G T0 T1 L k0 k1
  -> Join H (substExpr s T0) (substExpr s T1) (substExpr s L) (substCo s k0) (substCo s k1)
Join-subst ws wfH (jconv c0 c1)          = jconv (subst-ConvTy ws wfH c0) (subst-ConvTy ws wfH c1)
Join-subst ws wfH (juniv k m p ep c0 c1) = juniv k m p ep (subst-ConvTy ws wfH c0) (subst-ConvTy ws wfH c1)
Join-subst ws wfH (jpi dA dB0 dB1 cv0 cv1 j) =
  let dA'  = subst-IsType ws wfH dA
      wfH' = wf-extend dA'
      ws'  = liftSub-WtSub ws wfH dA
  in jpi dA' (subst-IsType ws' wfH' dB0) (subst-IsType ws' wfH' dB1)
         (subst-ConvTy ws wfH cv0) (subst-ConvTy ws wfH cv1) (Join-subst ws' wfH' j)

------------------------------------------------------------------------
-- Coercions are well typed, congruent, and compute under application
------------------------------------------------------------------------

coe-ty : {n : Nat} {G : Ctx n} {T0 T1 L t : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> HasType G t T0 -> HasType G (coe k0 t) L
coe-ty (jconv c0 c1) d = ty-conv d c0
coe-ty {G = G} {t = t} (juniv k m p ep c0 c1) d =
  Eq-transport (\ z -> HasType G t (U z)) (Eq-sym ep) (cum-le k (max k m) (Le-max-l k m) (ty-conv d c0))
coe-ty (jpi dA dB0 dB1 cv0 cv1 j) d =
  ty-Lam dA (join-L j) (coe-ty j (appv0-ty dA dB0 (ty-conv d cv0)))

coe-cong : {n : Nat} {G : Ctx n} {T0 T1 L t t' : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> ConvTm G t t' T0 -> ConvTm G (coe k0 t) (coe k0 t') L
coe-cong (jconv c0 c1) e = conv-conv e c0
coe-cong {G = G} {t = t} {t' = t'} (juniv k m p ep c0 c1) e =
  Eq-transport (\ z -> ConvTm G t t' (U z)) (Eq-sym ep) (cum-le-Tm k (max k m) (Le-max-l k m) (conv-conv e c0))
coe-cong (jpi dA dB0 dB1 cv0 cv1 j) e =
  let ih = coe-cong j (appv0-cong dA dB0 (conv-conv e cv0))
  in conv-cong-Lam-body dA (join-L j) (presup-l-ConvTm ih) ih

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

------------------------------------------------------------------------
-- On the diagonal the coercions are injective (η)
------------------------------------------------------------------------

Join-diag : {n : Nat} {G : Ctx n} {T0 T1 L t0 t1 : Expr n} {k0 k1 : Co n}
  -> Join G T0 T1 L k0 k1 -> ConvTy G T0 T1
  -> HasType G t0 T0 -> HasType G t1 T1
  -> ConvTm G (coe k0 t0) (coe k1 t1) L -> ConvTm G t0 t1 T0
Join-diag (jconv c0 c1) cT d0 d1 e = conv-conv e (conv-Ty-sym c0)
Join-diag {G = G} {t0 = t0} {t1 = t1} (juniv k m p ep c0 c1) cT d0 d1 e =
  let ekm = U-inj-R (conv-Ty-trans (conv-Ty-sym c0) (conv-Ty-trans cT c1))
      epk = Eq-trans ep (Eq-trans (Eq-cong (max k) (Eq-sym ekm)) (max-idem k))
  in conv-conv (Eq-transport (\ z -> ConvTm G t0 t1 (U z)) epk e) (conv-Ty-sym c0)
Join-diag (jpi dA dB0 dB1 cv0 cv1 j) cT d0 d1 e =
  let cB  = snd (PiInj-R (conv-Ty-trans (conv-Ty-sym cv0) (conv-Ty-trans cT cv1)))
      t0' = ty-conv d0 cv0
      t1' = ty-conv d1 cv1
      h0  = appv0-ty dA dB0 t0'
      h1  = appv0-ty dA dB1 t1'
      dL  = join-L j
      hb0 = coe-ty j h0
      hb1 = coe-ty (Join-sym j) h1
      eb  = conv-trans (conv-sym (lam-beta-v0 dA dL hb0))
              (conv-trans (appv0-cong dA dL e) (lam-beta-v0 dA dL hb1))
      ih  = Join-diag j cB h0 h1 eb
      s1  = conv-eta dA dB0 t0'
      s2  = conv-cong-Lam-body dA dB0 h0 ih
      s3  = conv-cong-Lam-Ty dA dB0 (conv-Ty-refl dA) cB (ty-conv h1 (conv-Ty-sym cB))
      s4  = conv-conv (conv-sym (conv-eta dA dB1 t1'))
              (conv-Ty-Pi dA dB1 (conv-Ty-refl dA) (conv-Ty-sym cB))
  in conv-conv (conv-trans s1 (conv-trans s2 (conv-trans s3 s4))) (conv-Ty-sym cv0)

------------------------------------------------------------------------
-- Results of the main lemma, and moving them up along SubTy
------------------------------------------------------------------------

record JRes {n : Nat} (G : Ctx n) (u0 u1 T0 T1 : Expr n) : Set where
  constructor mkJRes
  field
    L    : Expr n
    k0   : Co n
    k1   : Co n
    join : Join G T0 T1 L k0 k1
    eq   : ConvTm G (coe k0 u0) (coe k1 u1) L

swapRes : {n : Nat} {G : Ctx n} {u0 u1 T0 T1 : Expr n} -> JRes G u1 u0 T1 T0 -> JRes G u0 u1 T0 T1
swapRes (mkJRes L k0 k1 j e) = mkJRes L k1 k0 (Join-sym j) (conv-sym e)

-- a join one of whose sides is a universe is a universe join
joinU-l : {n : Nat} {G : Ctx n} {P0 P1 L : Expr n} {k0 k1 : Co n} {k : Nat} (x y : Expr n)
  -> Join G P0 P1 L k0 k1 -> ConvTy G P0 (U k) -> ConvTm G (coe k0 x) (coe k1 y) L
  -> Sigma Nat (\ p1 -> Pair (ConvTy G P1 (U p1)) (ConvTm G x y (U (max k p1))))
joinU-l {k = k} x y (jconv c0 c1) cP e =
  let cLU = conv-Ty-trans (conv-Ty-sym c0) cP
  in mkSigma k (mkSigma (conv-Ty-trans c1 cLU) (cum-le-Tm k (max k k) (Le-max-l k k) (conv-conv e cLU)))
joinU-l {G = G} {k = k} x y (juniv k' m' p ep c0 c1) cP e =
  let ek = U-inj-R (conv-Ty-trans (conv-Ty-sym c0) cP)
  in mkSigma m' (mkSigma c1 (Eq-transport (\ z -> ConvTm G x y (U z)) (Eq-trans ep (Eq-cong (\ z -> max z m') ek)) e))
joinU-l x y (jpi dA dB0 dB1 cv0 cv1 j) cP e = absurd (Pi-U-noconf (conv-Ty-trans (conv-Ty-sym cv0) cP))

joinU-both : {n : Nat} {G : Ctx n} {L : Expr n} {k0 k1 : Co n} {l0 l1 : Nat} (x y : Expr n)
  -> Join G (U l0) (U l1) L k0 k1 -> ConvTm G (coe k0 x) (coe k1 y) L -> ConvTm G x y (U (max l0 l1))
joinU-both {G = G} {l0 = l0} x y j e =
  let r  = joinU-l x y j (conv-Ty-refl (isType-U (typing-WfCtx (presup-l-ConvTm e)))) e
      el = U-inj-R (conv-Ty-sym (fst (snd r)))
  in Eq-transport (\ z -> ConvTm G x y (U (max l0 z))) el (snd (snd r))

aboveU : {n : Nat} {G : Ctx n} {P T : Expr n} {p : Nat}
  -> SubTy G P T -> ConvTy G P (U p) -> Sigma Nat (\ m -> Pair (Le p m) (ConvTy G T (U m)))
aboveU {p = p} (sub-conv c) cP = mkSigma p (mkSigma (Le-refl p) (conv-Ty-trans (conv-Ty-sym c) cP))
aboveU {p = p} (sub-cum k m le cP' cT) cP =
  let ek = U-inj-R (conv-Ty-trans (conv-Ty-sym cP) cP')
  in mkSigma m (mkSigma (Eq-transport (\ z -> Le z m) (Eq-sym ek) le) cT)

cumL : {n : Nat} {G : Ctx n} {P0 P1 L T0 T1 : Expr n} {k0 k1 : Co n} (x y : Expr n)
  -> Join G P0 P1 L k0 k1 -> (k m : Nat) -> Le k m -> ConvTy G P0 (U k) -> ConvTy G T0 (U m)
  -> SubTy G P1 T1 -> ConvTm G (coe k0 x) (coe k1 y) L -> JRes G x y T0 T1
cumL x y j k m le cP cT s1 e =
  let r  = joinU-l x y j cP e
      p1 = fst r
      a  = aboveU s1 (fst (snd r))
      m1 = fst a
  in mkJRes (U (max m m1)) idC idC (juniv m m1 (max m m1) refl cT (snd (snd a)))
       (cum-le-Tm (max k p1) (max m m1) (Le-max-mono k p1 m m1 le (fst (snd a))) (snd (snd r)))

Join-sub : {n : Nat} {G : Ctx n} {P0 P1 L T0 T1 t0 t1 : Expr n} {k0 k1 : Co n}
  -> Join G P0 P1 L k0 k1 -> SubTy G P0 T0 -> SubTy G P1 T1
  -> ConvTm G (coe k0 t0) (coe k1 t1) L -> JRes G t0 t1 T0 T1
Join-sub j (sub-conv c0) (sub-conv c1) e =
  mkJRes _ _ _ (retarget (conv-Ty-sym c0) (conv-Ty-sym c1) j) e
Join-sub {t0 = t0} {t1 = t1} j (sub-cum k m le cP cT) s1 e = cumL t0 t1 j k m le cP cT s1 e
Join-sub {t0 = t0} {t1 = t1} j (sub-conv c0) (sub-cum k m le cP cT) e =
  swapRes (cumL t1 t0 (Join-sym j) k m le cP cT (sub-conv c0) (conv-sym e))

------------------------------------------------------------------------
-- The application case
------------------------------------------------------------------------

appCase : {n : Nat} {G : Ctx n} {C0 C1 c0 c1 a0 a1 T0 T1 L : Expr n} {D0 D1 : Expr (suc n)} {k0 k1 : Co n}
  -> Join G (Pi C0 D0) (Pi C1 D1) L k0 k1 -> ConvTm G (coe k0 c0) (coe k1 c1) L
  -> JRes G a0 a1 C0 C1
  -> InvApp G C0 D0 c0 a0 T0 -> InvApp G C1 D1 c1 a1 T1
  -> JRes G (App C0 D0 c0 a0) (App C1 D1 c1 a1) T0 T1
appCase (jconv cv0 cv1) e ra i0 i1 =
  let dC0   = InvApp.dA i0 ; dD0 = InvApp.dB i0
      pinj  = PiInj-R (conv-Ty-trans cv0 (conv-Ty-sym cv1))
      cC    = fst pinj ; cB = snd pinj
      cf    = conv-conv e (conv-Ty-sym cv0)                              -- c0 = c1 : Π(C0,D0)
      ca    = Join-diag (JRes.join ra) cC (InvApp.da i0) (InvApp.da i1) (JRes.eq ra)
      da1'  = ty-conv (InvApp.da i1) (conv-Ty-sym cC)
      df1'  = presup-r-ConvTm cf
      cBa   = subst1-cong-Ty ca dC0 dD0
      step1 = conv-cong-App-fun dC0 dD0 cf (InvApp.da i0)
      step2 = conv-cong-App-arg dC0 dD0 df1' ca cBa
      step3 = conv-conv (conv-cong-App-Ty dC0 dD0 cC cB df1' da1') (conv-Ty-sym cBa)
      cBB   = conv-Ty-trans cBa (subst-ConvTy (subst1-WtSub dC0 da1') (isType-WfCtx dC0) cB)
      dP    = typing-IsType (presup-l-ConvTm step1)
  in Join-sub (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (InvApp.sub i0) (Sub-conv-left cBB (InvApp.sub i1))
       (conv-trans step1 (conv-trans step2 step3))
appCase (juniv k m p ep cv0 cv1) e ra i0 i1 = absurd (Pi-U-noconf cv0)
appCase (jpi dA dE0 dE1 cv0 cv1 j) e ra i0 i1 =
  let wfG  = isType-WfCtx dA
      pi0  = PiInj-R cv0                                                 -- C0 = A, D0 = E0
      pi1  = PiInj-R cv1                                                 -- C1 = A, D1 = E1
      dC0  = InvApp.dA i0 ; dC1 = InvApp.dA i1
      da0  = InvApp.da i0 ; da1 = InvApp.da i1
      cC   = conv-Ty-trans (fst pi0) (conv-Ty-sym (fst pi1))
      ca   = Join-diag (JRes.join ra) cC da0 da1 (JRes.eq ra)            -- a0 = a1 : C0
      a0A  = ty-conv da0 (fst pi0)
      a1A  = ty-conv da1 (fst pi1)
      caA  = conv-conv ca (fst pi0)
      c0A  = ty-conv (InvApp.dc i0) cv0
      c1A  = ty-conv (InvApp.dc i1) cv1
      dLB  = join-L j
      X    = conv-cong-App-fun dA dLB e a0A
      b0   = coe-beta dA dLB (coe-ty j (appv0-ty dA dE0 c0A)) a0A
      b1   = coe-beta dA dLB (coe-ty (Join-sym j) (appv0-ty dA dE1 c1A)) a0A
      j'   = Join-subst (subst1-WtSub dA a0A) wfG j
      cD0  = ctx-conv-ConvTy dC0 dA (fst pi0) (conv-Ty-sym (snd pi0))
      Y0   = conv-cong-App-Ty dA dE0 (conv-Ty-sym (fst pi0)) cD0 c0A a0A
      Z0   = coe-cong j' Y0
      cBa1 = subst1-cong-Ty caA dA dE1
      Y1a  = conv-cong-App-arg dA dE1 c1A caA cBa1
      cD1  = ctx-conv-ConvTy dC1 dA (fst pi1) (conv-Ty-sym (snd pi1))
      Y1b  = conv-cong-App-Ty dA dE1 (conv-Ty-sym (fst pi1)) cD1 c1A a1A
      Y1   = conv-trans Y1a (conv-conv Y1b (conv-Ty-sym cBa1))
      Z1   = coe-cong (Join-sym j') Y1
      eqf  = conv-trans (conv-sym Z0) (conv-trans (conv-sym b0) (conv-trans X (conv-trans b1 Z1)))
      cB0a = subst-ConvTy (subst1-WtSub dC0 da0) wfG (conv-Ty-sym (snd pi0))
      cB1a = subst-ConvTy (subst1-WtSub dC1 da1) wfG (conv-Ty-sym (snd pi1))
  in Join-sub j' (Sub-conv-left cB0a (InvApp.sub i0))
                 (Sub-conv-left (conv-Ty-trans cBa1 cB1a) (InvApp.sub i1)) eqf

------------------------------------------------------------------------
-- The main lemma, by structural induction on the term
------------------------------------------------------------------------

mutual

  main : {n : Nat} {G : Ctx n} (u0 u1 : Expr n) {T0 T1 : Expr n}
    -> Eq (strip u0) (strip u1) -> HasType G u0 T0 -> HasType G u1 T1 -> JRes G u0 u1 T0 T1
  -- variables
  main (Var i) (Var .i) refl d0 d1 =
    let r0 = inv-Var d0 ; r1 = inv-Var d1 ; wf = fst r0 ; dP = wfCtx-lookup wf i
    in Join-sub (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (snd r0) (snd r1) (conv-refl (ty-var wf))
  main (Var _) (U _) ()
  main (Var _) (Pi _ _) ()
  main (Var _) (Lam _ _ _) ()
  main (Var _) (App _ _ _ _) ()
  -- universes
  main (U l) (U .l) refl d0 d1 =
    let r0 = inv-U d0 ; r1 = inv-U d1 ; wf = fst r0 ; dP = isType-U {l = suc l} wf
    in Join-sub (jconv (conv-Ty-refl dP) (conv-Ty-refl dP)) (snd r0) (snd r1) (conv-refl (ty-U wf))
  main (U _) (Var _) ()
  main (U _) (Pi _ _) ()
  main (U _) (Lam _ _ _) ()
  main (U _) (App _ _ _ _) ()
  -- products
  main (Pi A0 B0) (Pi A1 B1) e d0 d1 =
    let inj  = C-Pi-inj e
        p0   = inv-Pi d0 ; p1 = inv-Pi d1
        l0   = InvPi.lvl p0 ; l1 = InvPi.lvl p1 ; m = max l0 l1
        dA0  = InvPi.dA p0 ; dA1 = InvPi.dA p1
        rA   = main A0 A1 (fst inj) dA0 dA1
        eA   = joinU-both A0 A1 (JRes.join rA) (JRes.eq rA)
        cA   = conv-Ty-from-U eA
        dB1' = ctx-conv-HasType (is-Ty-from-U dA1) (is-Ty-from-U dA0) (conv-Ty-sym cA) (InvPi.dB p1)
        rB   = main B0 B1 (snd inj) (InvPi.dB p0) dB1'
        eB   = joinU-both B0 B1 (JRes.join rB) (JRes.eq rB)
        ePi  = conv-cong-Pi (cum-le l0 m (Le-max-l l0 l1) dA0) (cum-le l0 m (Le-max-l l0 l1) (InvPi.dB p0)) eA eB
        wf   = typing-WfCtx dA0
    in Join-sub (juniv l0 l1 m refl (conv-Ty-refl (isType-U wf)) (conv-Ty-refl (isType-U wf)))
         (InvPi.sub p0) (InvPi.sub p1) ePi
  main (Pi _ _) (Var _) ()
  main (Pi _ _) (U _) ()
  main (Pi _ _) (Lam _ _ _) ()
  main (Pi _ _) (App _ _ _ _) ()
  -- abstractions
  main (Lam A0 B0 b0) (Lam A1 B1 b1) e d0 d1 =
    let inj  = C-Lam-inj e
        l0   = inv-Lam d0 ; l1 = inv-Lam d1
        dA0  = InvLam.dA l0 ; dB0 = InvLam.dB l0 ; db0 = InvLam.db l0
        dA1  = InvLam.dA l1 ; dB1 = InvLam.dB l1 ; db1 = InvLam.db l1
        cA   = tyEq A0 A1 (fst inj) dA0 dA1
        dB1' = ctx-conv-IsType dA1 dA0 (conv-Ty-sym cA) dB1
        db1' = ctx-conv-HasType dA1 dA0 (conv-Ty-sym cA) db1
        rb   = main b0 b1 (snd inj) db0 db1'
        j    = JRes.join rb
        dLB  = join-L j
        jP   = jpi dA0 dB0 dB1' (conv-Ty-refl (isType-Pi dA0 dB0))
                 (conv-Ty-Pi dA1 dB1 (conv-Ty-sym cA) (conv-Ty-refl dB1)) j
        E0   = coe-cong j (lam-beta-v0 dA0 dB0 db0)
        L0   = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm E0) E0
        M    = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm (JRes.eq rb)) (JRes.eq rb)
        R1   = coe-cong (Join-sym jP) (conv-cong-Lam-Ty dA1 dB1 (conv-Ty-sym cA) (conv-Ty-refl dB1) db1)
        E1   = coe-cong (Join-sym j) (lam-beta-v0 dA0 dB1' db1')
        R2   = conv-cong-Lam-body dA0 dLB (presup-l-ConvTm E1) E1
    in Join-sub jP (InvLam.sub l0) (InvLam.sub l1)
         (conv-trans L0 (conv-trans M (conv-sym (conv-trans R1 R2))))
  main (Lam _ _ _) (Var _) ()
  main (Lam _ _ _) (U _) ()
  main (Lam _ _ _) (Pi _ _) ()
  main (Lam _ _ _) (App _ _ _ _) ()
  -- applications
  main (App C0 D0 c0 a0) (App C1 D1 c1 a1) e d0 d1 =
    let inj = C-App-inj e
        i0  = inv-App d0 ; i1 = inv-App d1
        rc  = main c0 c1 (fst inj) (InvApp.dc i0) (InvApp.dc i1)
        ra  = main a0 a1 (snd inj) (InvApp.da i0) (InvApp.da i1)
    in appCase (JRes.join rc) (JRes.eq rc) ra i0 i1
  main (App _ _ _ _) (Var _) ()
  main (App _ _ _ _) (U _) ()
  main (App _ _ _ _) (Pi _ _) ()
  main (App _ _ _ _) (Lam _ _ _) ()

  tyEq : {n : Nat} {G : Ctx n} (A0 A1 : Expr n)
    -> Eq (strip A0) (strip A1) -> IsType G A0 -> IsType G A1 -> ConvTy G A0 A1
  tyEq A0 A1 e (is-Ty-from-U d0) (is-Ty-from-U d1) =
    let r = main A0 A1 e d0 d1
    in conv-Ty-from-U (joinU-both A0 A1 (JRes.join r) (JRes.eq r))

------------------------------------------------------------------------
-- Lemma 4.18, without normalisation
------------------------------------------------------------------------

type-uniq-NF : {n : Nat} {G : Ctx n} {A0 A1 : Expr n} ->
  IsType G A0 -> IsType G A1 -> Eq (strip A0) (strip A1) -> ConvTy G A0 A1
type-uniq-NF {A0 = A0} {A1 = A1} d0 d1 e = tyEq A0 A1 e d0 d1

term-uniq-conv-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> ConvTy G A0 A1 ->
  ConvTm G u0 u1 A0
term-uniq-conv-NF {u0 = u0} {u1 = u1} d0 d1 e cA =
  let r = main u0 u1 e d0 d1 in Join-diag (JRes.join r) cA d0 d1 (JRes.eq r)

term-uniq-NF : {n : Nat} {G : Ctx n} {u0 u1 A0 A1 : Expr n} ->
  HasType G u0 A0 -> HasType G u1 A1 -> Eq (strip u0) (strip u1) -> Eq (strip A0) (strip A1) ->
  Pair (ConvTy G A0 A1) (ConvTm G u0 u1 A0)
term-uniq-NF d0 d1 eu eA =
  let cA = type-uniq-NF (typing-IsType d0) (typing-IsType d1) eA
  in mkSigma cA (term-uniq-conv-NF d0 d1 eu cA)
