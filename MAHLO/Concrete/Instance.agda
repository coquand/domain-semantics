{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Instance.agda
--
-- The concrete beta-delta term model (plan Sec. 6.2) inhabits the
-- abstract interfaces of P1/P2:
--   concreteTM    : TermModel                  (A1)--(A4)
--   concreteModel : Model concreteTM           (denotation, delta by den)
-- So the soundness theorem of P2 depends only on the Fixpoint hypothesis.
------------------------------------------------------------------------

module MAHLO.Concrete.Instance where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax using (Num ; zero ; suc ; Fin ; fzero ; fsuc ; Expr ; cong2 ; cong4)
open import MAHLO.TermModel
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Confluence
open import MAHLO.Concrete.Conv
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.Rel
open import MAHLO.Concrete.Ext
open import MAHLO.Concrete.Den

------------------------------------------------------------------------
-- (A2), (A4) and the neutral disjointness facts
------------------------------------------------------------------------

private
  ne-appR : {u u' v v' : Tm} -> NR u u' -> SR v v' -> NR (tapp u v) (tapp u' v')
  ne-appR (nr a b da db na nb e) (sr c d dc dd e') =
    nr (tapp a c) (tapp b d)
       (R-app (fst da) (fst dc) , v-ne (ne-app na (snd dc)))
       (R-app (fst db) (fst dd) , v-ne (ne-app nb (snd dd)))
       (ne-app na (snd dc)) (ne-app nb (snd dd)) (cong2 tapp e e')

  ne-fstR : {u u' : Tm} -> NR u u' -> NR (tfst u) (tfst u')
  ne-fstR (nr a b da db na nb e) =
    nr (tfst a) (tfst b) (R-fst (fst da) , v-ne (ne-fst na)) (R-fst (fst db) , v-ne (ne-fst nb))
       (ne-fst na) (ne-fst nb) (Eq-cong tfst e)

  ne-sndR : {u u' : Tm} -> NR u u' -> NR (tsnd u) (tsnd u')
  ne-sndR (nr a b da db na nb e) =
    nr (tsnd a) (tsnd b) (R-snd (fst da) , v-ne (ne-snd na)) (R-snd (fst db) , v-ne (ne-snd nb))
       (ne-snd na) (ne-snd nb) (Eq-cong tsnd e)

  ne-recR : {C C' z z' s s' n n' : Tm} -> SR C C' -> SR z z' -> SR s s' -> NR n n' ->
            NR (trec C z s n) (trec C' z' s' n')
  ne-recR (sr c1 c1' d1 d1' e1) (sr c2 c2' d2 d2' e2) (sr c3 c3' d3 d3' e3)
          (nr a b da db na nb e) =
    nr (trec c1 c2 c3 a) (trec c1' c2' c3' b)
       (R-rec (fst d1) (fst d2) (fst d3) (fst da) , v-ne nn)
       (R-rec (fst d1') (fst d2') (fst d3') (fst db) , v-ne nn')
       nn nn' (cong4 trec e1 e2 e3 e)
    where
      nn = ne-rec (snd d1) (snd d2) (snd d3) na
      nn' = ne-rec (snd d1') (snd d2') (snd d3') nb

  S2 : {k : Tm -> Tm -> Tm} -> ({a b c d : Tm} -> Red a c -> Red b d -> Red (k a b) (k c d)) ->
       ({a b : Tm} -> Val a -> Val b -> Val (k a b)) ->
       ({a b c d : Tm} -> Eq (etanf a) (etanf c) -> Eq (etanf b) (etanf d) ->
          Eq (etanf (k a b)) (etanf (k c d))) ->
       {A A' F F' : Tm} -> SR A A' -> SR F F' -> SR (k A F) (k A' F')
  S2 rk vk ek (sr a a' da da' e) (sr f f' df df' e') =
    sr _ _ (rk (fst da) (fst df) , vk (snd da) (snd df))
           (rk (fst da') (fst df') , vk (snd da') (snd df')) (ek e e')

  -- a neutral value is never a reduct of a constructor-headed term
  noNe2 : {k : Tm -> Tm -> Tm} -> ({x a b : Tm} -> Eq x (k a b) -> Ne x -> Empty) ->
          ({a b c : Tm} -> Red (k a b) c -> Red2 k a b c) ->
          {A F b : Tm} -> NR (k A F) b -> Empty
  noNe2 h inv x = h (Red2.ec (inv (fst (NR.da x)))) (NR.na x)

  hPi : {x a b : Tm} -> Eq x (tpi a b) -> Ne x -> Empty
  hPi refl ()
  hSig : {x a b : Tm} -> Eq x (tsig a b) -> Ne x -> Empty
  hSig refl ()
  hU : {x a b : Tm} -> Eq x (tU a b) -> Ne x -> Empty
  hU refl ()

  ne-NatR : {b : Tm} -> NR tnat b -> Empty
  ne-NatR x = h (red-nat (fst (NR.da x))) (NR.na x)
    where h : {y : Tm} -> Eq y tnat -> Ne y -> Empty
          h refl ()

  ne-VR : {b : Tm} -> NR tV b -> Empty
  ne-VR x = h (red-V (fst (NR.da x))) (NR.na x)
    where h : {y : Tm} -> Eq y tV -> Ne y -> Empty
          h refl ()

------------------------------------------------------------------------
-- The term model
------------------------------------------------------------------------

concreteTM : TermModel
concreteTM = record
  { D = Tm ; app = tapp ; Pi = tpi ; Sig = tsig ; pr1 = tfst ; pr2 = tsnd ; Nat = tnat ; U = tU
  ; _~~_ = Conv ; ~~-refl = cv-refl ; ~~-sym = cv-sym ; ~~-trans = cv-trans
  ; app-cong = cv-app ; Pi-cong = cv-pi ; Sig-cong = cv-sig ; U-cong = cv-U
  ; pr1-cong = cv-fst ; pr2-cong = cv-snd
  ; N = NR ; S = SR ; NatR = NatR
  ; N-sym = NR-sym ; N-trans = NR-trans ; S-sym = SR-sym ; S-trans = SR-trans
  ; NatR-sym = NatR-sym ; NatR-trans = NatR-trans
  ; N-resp = NR-resp ; S-resp = SR-resp ; NatR-resp = NatR-resp
  ; N-S = NR-SR ; N-NatR = nat-ne ; NatR-S = NatR-SR
  ; ne-app = ne-appR ; ne-fst = ne-fstR ; ne-snd = ne-sndR
  ; ext = ext ; ext-pair = ext-pair
  ; Pi-inj = cv-pi-inj ; U-inj = cv-U-inj ; Sig-inj = cv-sig-inj
  ; Pi-Nat = cv-pi-nat ; Sig-Pi = cv-sig-pi ; Sig-Nat = cv-sig-nat ; Sig-U = cv-sig-U
  ; ne-Sig = noNe2 hSig red-sig
  ; Pi-U = cv-pi-U ; Nat-U = cv-nat-U
  ; ne-Pi = noNe2 hPi red-pi ; ne-Nat = ne-NatR ; ne-U = noNe2 hU red-U
  ; S-Pi = S2 R-pi v-pi (cong2 tpi) ; S-Sig = S2 R-sig v-sig (cong2 tsig)
  ; S-U = S2 R-U v-U (cong2 tU)
  ; S-Nat = sr tnat tnat (⇓-self v-nat) (⇓-self v-nat) refl }

------------------------------------------------------------------------
-- The denotation
------------------------------------------------------------------------

open import MAHLO.Model concreteTM

private
  cons-pw : {n : Num} (rho : Env n) (d : Tm) -> PW (cons' rho d) (cons rho d)
  cons-pw rho d fzero = refl
  cons-pw rho d (fsuc i) = refl

  eqcv : {a b : Tm} -> Eq a b -> Conv a b
  eqcv refl = cv-refl

concreteModel : Model
concreteModel = record
  { Vd = tV ; zeroD = tze ; sucD = tsc ; recD = trec ; pairD = tpair
  ; V-Pi = cv-V-pi ; V-Sig = cv-V-sig ; V-Nat = cv-V-nat ; V-U = cv-V-U
  ; ne-V = ne-VR
  ; S-V = sr tV tV (⇓-self v-V) (⇓-self v-V) refl
  ; NatR-zero = nat-ze cv-refl cv-refl
  ; NatR-suc = nat-sc cv-refl cv-refl
  ; NatR-ind = NatR-ind
  ; sucD-cong = cv-sc ; recD-cong = cv-rec ; pairD-cong = cv-pair
  ; rec-zero = cv-step s-rec0 ; rec-suc = cv-step s-recS
  ; ne-rec = ne-recR
  ; pr1-pair = cv-step s-fstp ; pr2-pair = cv-step s-sndp
  ; den = den
  ; den-subst = den-subst'
  ; den-Var = \ i -> cv-refl
  ; den-Lam = \ {n} {rho} A t d ->
      cv-trans (den-Lam' A t d) (eqcv (den-ext (cons-pw rho d) t))
  ; den-App = \ t u -> cv-refl
  ; den-Pi = \ A F -> cv-refl
  ; den-Sigma = \ A F -> cv-refl
  ; den-Pair = \ t u -> cv-refl
  ; den-Fst = \ t -> cv-refl
  ; den-Snd = \ t -> cv-refl
  ; den-Nat = cv-refl
  ; den-Zero = cv-refl
  ; den-Suc = \ t -> cv-refl
  ; den-Rec = \ C z s k -> cv-refl
  ; den-V = cv-refl
  ; den-Ucode = \ f g -> cv-refl
  ; den-Fhat = \ f g A F -> cv-refl
  ; den-Ghat = \ f g A F c -> cv-refl }
