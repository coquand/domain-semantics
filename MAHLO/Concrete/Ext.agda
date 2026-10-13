{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Ext.agda
--
-- Assumption (A3) for the concrete model:
--   * ext: for x a variable fresh for v, v',
--       S (v x) (v' x)  ==>  S v v'
--     by induction on the reduction sequence of  v x  (no
--     standardisation): steps are inside v, or a head beta once v is a
--     lambda; then b[x/0] is a renaming of b with an inverse.
--   * ext-pair:  S (v.1) (v'.1),  S (v.2) (v'.2)  ==>  S v v'.
------------------------------------------------------------------------

module MAHLO.Concrete.Ext where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc ; cong2)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Confluence
open import MAHLO.Concrete.Conv
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.EtaLemmas
open import MAHLO.Concrete.Bnd
open import MAHLO.Concrete.Rel

private
  app-inj : {a b c d : Tm} -> Eq (tapp a b) (tapp c d) -> Eq a c
  app-inj refl = refl
  fst-inj : {a b : Tm} -> Eq (tfst a) (tfst b) -> Eq a b
  fst-inj refl = refl
  ne-lam : {b : Tm} -> Ne (tlam b) -> Empty
  ne-lam ()
  ne-pair : {a b : Tm} -> Ne (tpair a b) -> Empty
  ne-pair ()

retr-suc : Retr suc pred
retr-suc = retr (\ i -> refl)

------------------------------------------------------------------------
-- The normal form of  v x
------------------------------------------------------------------------

data AppCase (m : Num) (c w : Tm) : Set where
  lamC : (b : Tm) -> Eq c (tlam b) -> Eq w (ren (fr m) b) -> AppCase m c w
  neC  : Ne c -> Eq w (tapp c (tvar m)) -> AppCase m c w

record AppNf (m : Num) (v w : Tm) : Set where
  constructor appnf
  field
    c   : Tm
    red : Red v c
    vc  : Val c
    bc  : Bnd m c
    cs  : AppCase m c w

appNf : (m : Num) {v w : Tm} -> Bnd m v -> Red (tapp v (tvar m)) w -> Val w -> AppNf m v w
appNf m {v} bv r-refl (v-ne (ne-app nv vx)) = appnf v r-refl (v-ne nv) bv (neC nv refl)
appNf m {w = w} bv (r-step (s-beta {b}) r) vw =
  appnf (tlam b') (R-lam rb) (v-lam (val-ren (fr' m) vw)) (bnd-red (suc m) rb bv)
        (lamC b' refl (Eq-sym (ren-retract (retr-fr' m) w)))
  where
    b' = ren (fr' m) w
    r1 : Red (ren (fr m) b) w
    r1 = transport (\ z -> Red z w) (inst-fresh m b bv) r
    rb : Red b b'
    rb = transport (\ z -> Red z b') (ren-retract (retr-fr m) b) (Red-ren (fr' m) r1)
appNf m bv (r-step (s-app1 s) r) vw =
  let x = appNf m (bnd-step m s bv) r vw in
  appnf (AppNf.c x) (r-step s (AppNf.red x)) (AppNf.vc x) (AppNf.bc x) (AppNf.cs x)
appNf m bv (r-step (s-app2 ()) r) vw

-- the eta-normal forms of v, v' agree when those of v x, v' x do
private
  lam-ne : (m : Num) {b c' : Tm} -> Bnd m c' ->
           Eq (etanf (ren (fr m) b)) (etanf (tapp c' (tvar m))) ->
           Eq (etanf (tlam b)) (etanf c')
  lam-ne m {b} {c'} bc' e =
    Eq-trans (Eq-cong etaLam eb) (etaLam-shift (etanf c'))
    where
      e1 : Eq (ren (fr m) (etanf b)) (tapp (etanf c') (tvar m))
      e1 = Eq-trans (Eq-sym (etanf-ren (retr-fr m) b)) e
      e2 : Eq (ren (fr' m) (etanf c')) (shift (etanf c'))
      e2 = Eq-trans (Eq-sym (etanf-ren (retr-fr' m) c'))
             (Eq-trans (Eq-cong etanf (fr'-shift m c' bc')) (etanf-ren retr-suc c'))
      eb : Eq (etanf b) (tapp (shift (etanf c')) (tvar zero))
      eb = Eq-trans (Eq-sym (ren-retract (retr-fr m) (etanf b)))
             (Eq-trans (Eq-cong (ren (fr' m)) e1)
                (cong2 tapp e2 (Eq-cong tvar (fr'-fr m zero))))

  eqCase : (m : Num) {c c' w w' : Tm} -> Bnd m c -> Bnd m c' ->
           AppCase m c w -> AppCase m c' w' -> Eq (etanf w) (etanf w') ->
           Eq (etanf c) (etanf c')
  eqCase m bc bc' (lamC b refl refl) (lamC b' refl refl) e =
    Eq-cong etaLam (ren-inj (retr-fr m)
      (Eq-trans (Eq-sym (etanf-ren (retr-fr m) b)) (Eq-trans e (etanf-ren (retr-fr m) b'))))
  eqCase m {c' = c'} bc bc' (lamC b refl refl) (neC n' refl) e = lam-ne m {b} {c'} bc' e
  eqCase m {c} bc bc' (neC n refl) (lamC b' refl refl) e = Eq-sym (lam-ne m {b'} {c} bc (Eq-sym e))
  eqCase m bc bc' (neC n refl) (neC n' refl) e = app-inj e

-- (A3)
ext : (v v' : Tm) -> Sigma Tm (\ x -> NR x x * (SR (tapp v x) (tapp v' x) -> SR v v'))
ext v v' =
  tvar m , (nr (tvar m) (tvar m) (⇓-self (v-ne ne-var)) (⇓-self (v-ne ne-var)) ne-var ne-var refl ,
            h)
  where
    m = max (bound v) (bound v')
    bv = wkL (bound v) (bound v') v (bnd-bound v)
    bv' = wkR (bound v) (bound v') v' (bnd-bound v')
    h : SR (tapp v (tvar m)) (tapp v' (tvar m)) -> SR v v'
    h (sr w w' dw dw' e) =
      sr (AppNf.c A) (AppNf.c A') (AppNf.red A , AppNf.vc A) (AppNf.red A' , AppNf.vc A')
         (eqCase m (AppNf.bc A) (AppNf.bc A') (AppNf.cs A) (AppNf.cs A') e)
      where
        A = appNf m bv (fst dw) (snd dw)
        A' = appNf m bv' (fst dw') (snd dw')

------------------------------------------------------------------------
-- Pairs
------------------------------------------------------------------------

data FstCase (c w : Tm) : Set where
  pairF : (a b : Tm) -> Eq c (tpair a b) -> Red a w -> FstCase c w
  neF   : Ne c -> Eq w (tfst c) -> FstCase c w

data SndCase (c w : Tm) : Set where
  pairS : (a b : Tm) -> Eq c (tpair a b) -> Red b w -> SndCase c w
  neS   : Ne c -> Eq w (tsnd c) -> SndCase c w

record FstNf (v w : Tm) : Set where
  constructor fstnf
  field
    c   : Tm
    red : Red v c
    cs  : FstCase c w

record SndNf (v w : Tm) : Set where
  constructor sndnf
  field
    c   : Tm
    red : Red v c
    cs  : SndCase c w

fstNf : {v w : Tm} -> Red (tfst v) w -> Val w -> FstNf v w
fstNf {v} r-refl (v-ne (ne-fst nv)) = fstnf v r-refl (neF nv refl)
fstNf (r-step (s-fstp {a} {b}) r) vw = fstnf (tpair a b) r-refl (pairF a b refl r)
fstNf (r-step (s-fst s) r) vw =
  let x = fstNf r vw in fstnf (FstNf.c x) (r-step s (FstNf.red x)) (FstNf.cs x)

sndNf : {v w : Tm} -> Red (tsnd v) w -> Val w -> SndNf v w
sndNf {v} r-refl (v-ne (ne-snd nv)) = sndnf v r-refl (neS nv refl)
sndNf (r-step (s-sndp {a} {b}) r) vw = sndnf (tpair a b) r-refl (pairS a b refl r)
sndNf (r-step (s-snd s) r) vw =
  let x = sndNf r vw in sndnf (SndNf.c x) (r-step s (SndNf.red x)) (SndNf.cs x)

data PairNorm (v w1 w2 : Tm) : Set where
  pn-pair : Red v (tpair w1 w2) -> PairNorm v w1 w2
  pn-ne   : (c : Tm) -> v ⇓ c -> Ne c -> Eq w1 (tfst c) -> Eq w2 (tsnd c) -> PairNorm v w1 w2

private
  -- a neutral value is not a reduct of a pair
  pair-ne : {a b c : Tm} -> Red (tpair a b) c -> Ne c -> Empty
  pair-ne r n = h (Red2.ec (red-pair r)) n
    where h : {c a' b' : Tm} -> Eq c (tpair a' b') -> Ne c -> Empty
          h refl ()

  -- two reducts of v, one a neutral value: the other reduces to it
  meet-ne : {v c d : Tm} -> Red v c -> Red v d -> Ne d -> Red c d
  meet-ne p q n =
    let s = confluent p q in
    transport (Red _) (val-red (v-ne n) (snd (snd s))) (fst (snd s))

pairNorm : {v w1 w2 : Tm} -> FstNf v w1 -> SndNf v w2 -> Val w1 -> Val w2 -> PairNorm v w1 w2
pairNorm (fstnf c p (pairF a b refl ra)) (sndnf c' q (pairS a' b' refl rb)) v1 v2 =
  pn-pair (Red-trans p (Red-trans (R-pair (Red2.rA x) (Red2.rF x)) red3))
  where
    s = confluent p q
    x = red-pair (fst (snd s))
    y = red-pair (snd (snd s))
    a3 = Red2.A1 x
    b3 = Red2.F1 x
    eab : Eq (tpair a3 b3) (tpair (Red2.A1 y) (Red2.F1 y))
    eab = Eq-trans (Eq-sym (Red2.ec x)) (Red2.ec y)
    pinj : {u v u' v' : Tm} -> Eq (tpair u v) (tpair u' v') -> Eq u u' * Eq v v'
    pinj refl = refl , refl
    rb3 : Red b' b3
    rb3 = transport (Red b') (Eq-sym (snd (pinj eab))) (Red2.rF y)
    wa : a3 ⇓ _
    wa = ⇓-conv (cv-red (Red2.rA x)) (ra , v1)
    wb : b3 ⇓ _
    wb = ⇓-conv (cv-red rb3) (rb , v2)
    red3 : Red (tpair a3 b3) (tpair _ _)
    red3 = R-pair (fst wa) (fst wb)
pairNorm (fstnf c p (pairF a b refl ra)) (sndnf c' q (neS n e)) v1 v2 =
  Empty-elim (pair-ne (meet-ne p q n) n)
pairNorm (fstnf c p (neF n e)) (sndnf c' q (pairS a b refl rb)) v1 v2 =
  Empty-elim (pair-ne (meet-ne q p n) n)
pairNorm (fstnf c p (neF n e)) (sndnf c' q (neS n' e')) v1 v2 =
  pn-ne c (p , v-ne n) n e
    (Eq-trans e' (Eq-cong tsnd (Eq-sym (val-red (v-ne n') (meet-ne q p n)))))

-- the normal value of v, when v.1 and v.2 have normal values
private
  nfOf : {v w1 w2 : Tm} -> PairNorm v w1 w2 -> Val w1 -> Val w2 -> Tm
  nfOf {w1 = w1} {w2} (pn-pair r) v1 v2 = tpair w1 w2
  nfOf (pn-ne c d n e1 e2) v1 v2 = c

  nfOf-⇓ : {v w1 w2 : Tm} (p : PairNorm v w1 w2) (v1 : Val w1) (v2 : Val w2) -> v ⇓ nfOf p v1 v2
  nfOf-⇓ (pn-pair r) v1 v2 = r , v-pair v1 v2
  nfOf-⇓ (pn-ne c d n e1 e2) v1 v2 = d

  pn-eq : {v v' w1 w2 w1' w2' : Tm} (p : PairNorm v w1 w2) (p' : PairNorm v' w1' w2')
          (v1 : Val w1) (v2 : Val w2) (v1' : Val w1') (v2' : Val w2') ->
          Eq (etanf w1) (etanf w1') -> Eq (etanf w2) (etanf w2') ->
          Eq (etanf (nfOf p v1 v2)) (etanf (nfOf p' v1' v2'))
  pn-eq (pn-pair r) (pn-pair r') v1 v2 v1' v2' e1 e2 = cong2 etaPair e1 e2
  pn-eq (pn-pair r) (pn-ne c' d' n' refl refl) v1 v2 v1' v2' e1 e2 =
    Eq-trans (cong2 etaPair e1 e2) (etaPair-same (etanf c'))
  pn-eq (pn-ne c d n refl refl) (pn-pair r') v1 v2 v1' v2' e1 e2 =
    Eq-trans (Eq-sym (etaPair-same (etanf c))) (cong2 etaPair e1 e2)
  pn-eq (pn-ne c d n refl refl) (pn-ne c' d' n' refl refl) v1 v2 v1' v2' e1 e2 = fst-inj e1

-- (A3) for pairs
ext-pair : {v v' : Tm} -> SR (tfst v) (tfst v') -> SR (tsnd v) (tsnd v') -> SR v v'
ext-pair (sr w1 w1' d1 d1' e1) (sr w2 w2' d2 d2' e2) =
  sr (nfOf P (snd d1) (snd d2)) (nfOf P' (snd d1') (snd d2'))
     (nfOf-⇓ P (snd d1) (snd d2)) (nfOf-⇓ P' (snd d1') (snd d2'))
     (pn-eq P P' (snd d1) (snd d2) (snd d1') (snd d2') e1 e2)
  where
    P = pairNorm (fstNf (fst d1) (snd d1)) (sndNf (fst d2) (snd d2)) (snd d1) (snd d2)
    P' = pairNorm (fstNf (fst d1') (snd d1')) (sndNf (fst d2') (snd d2')) (snd d1') (snd d2')
