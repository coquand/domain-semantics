{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/Complete.agda
--
-- (c) Completeness of the conversion algorithm, TYPED:
--   if G |- t : C, G |- t' : C and den t, den t' (identity environment)
--   have values with equal eta-normal forms (Concrete's S), then the
--   algorithm accepts t ~ t'.
--
-- Typing is needed: untyped eta identifies  \x. r x  and  (r.1, r.2)
-- (both contract to r), and the untyped algorithm does not; a lambda
-- and a pair at a common type are excluded by Pi /= Sigma.
--
-- Induction on the values, lexicographically on (lp, sz) of both sides
-- (lambda/pair nodes, size): eta steps lower lp, structural steps keep
-- lp and lower sz.  The algorithm's own soundness (algsound) supplies
-- the conversions needed to type the later premises.
------------------------------------------------------------------------

module MAHLOALG.Complete where

open import MAHLO.Basic renaming (Sigma to Sg) hiding (_+_)
open import MAHLO.Basic using (_+_ ; inl ; inr)
open import MAHLO.Syntax hiding (x0 ; x1)
open import MAHLO.Typing
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.EtaLemmas using (etanf-val ; etanf-ne)
open import MAHLO.Concrete.Den
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.CtxConv
open import MAHLOINJ.Syntax.Presup using (pCv ; pTE ; opGEq)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Final using (injHyp ; Pi-inj ; Sig-inj)
open import MAHLOINJ.Inversion.Inv injHyp
open import MAHLOINJ.Algo.NoConfV
open import MAHLOINJ.Algo.Alg
open import MAHLOINJ.Algo.Eval using (evalC ; evalV ; UEv ; tyRed)
open import MAHLOINJ.Algo.Syn using (appWk)
open import MAHLOINJ.Algo.Sound using (sNe ; NeRes ; upPi ; upSig ; upNat ; noLamTy ; noPairTy ; lamInj)
open import MAHLOINJ.Algo.All using (algsound ; algsound-ty)
open import MAHLOINJ.Adq.Syn using (stepEq)
import MAHLOALG.Measure as M
open M using (_<=_ ; z<= ; s<= ; <=-refl ; <=-trans ; <=-suc ; +-mono ; pred<= ; sz ; lp ; lp-ren ; sz-ren)
  renaming (_+_ to _⊕_)
open import MAHLOALG.Shape
open import MAHLOALG.Whnf
open import MAHLOALG.EtaDec
open import MAHLOALG.CompLem

------------------------------------------------------------------------
-- classes of shapes, and clashes
------------------------------------------------------------------------

data Unit : Set where
  unit : Unit

Flex : Cls -> Set
Flex cL = Unit
Flex cP = Unit
Flex cN = Empty
Flex cPi = Empty
Flex cSig = Empty
Flex cNat = Empty
Flex cZe = Empty
Flex cSc = Empty
Flex cV = Empty
Flex cU = Empty

ClsOK : Cls -> Cls -> Set
ClsOK K c = Eq c K + (Flex K * Eq c cN)

Distinct : Cls -> Cls -> Set
Distinct K K' = (Eq K K' -> Empty) * (((Flex K * Eq K' cN) -> Empty) * (((Flex K' * Eq K cN) -> Empty) * ((Flex K * Flex K') -> Empty)))

clash : {K K' c : Cls} -> ClsOK K c -> ClsOK K' c -> Distinct K K' -> Empty
clash (inl e1) (inl e2) d = fst d (Eq-trans (Eq-sym e1) e2)
clash (inl e1) (inr (f2 , e2)) d = fst (snd (snd d)) (f2 , Eq-trans (Eq-sym e1) e2)
clash (inr (f1 , e1)) (inl e2) d = fst (snd d) (f1 , Eq-trans (Eq-sym e2) e1)
clash (inr (f1 , e1)) (inr (f2 , e2)) d = snd (snd (snd d)) (f1 , f2)

shK : {n : Num} {w : Expr n} -> SynSh w -> Cls
shK (sh-ne _) = cN
shK sh-lam = cL
shK sh-pair = cP
shK sh-pi = cPi
shK sh-sig = cSig
shK sh-nat = cNat
shK sh-ze = cZe
shK sh-sc = cSc
shK sh-V = cV
shK sh-U = cU

private
  trCls : {K : Cls} {a b : Tm} -> Eq a b -> ClsOK K (cls (etanf b)) -> ClsOK K (cls (etanf a))
  trCls refl k = k

  constCls : {v t : Tm} (K : Cls) -> Eq v t -> Eq (cls (etanf t)) K -> ClsOK K (cls (etanf v))
  constCls K refl e = inl e

clsOK : {n : Num} {w : Expr n} {v : Tm} (sh : SynSh w) -> den w idE ⇓ v -> ClsOK (shK sh) (cls (etanf v))
clsOK (sh-ne n) d = inl (ne-cls (etanf-ne (valNe n d)))
clsOK (sh-lam {A} {b}) d = let L = valLam {A = A} {b = b} d in trCls (VLam.ev L) (go (clsLam (etanf-val (snd (VLam.dx L)))))
  where
    go : _ -> _
    go (inl e) = inl e
    go (inr e) = inr (unit , e)
clsOK (sh-pair {a} {b}) d = let P = valPair {a = a} {b = b} d in trCls (V2.ev P) (go (clsPair {b = etanf (V2.y P)} (etanf-val (snd (V2.dx P)))))
  where
    go : _ -> _
    go (inl e) = inl e
    go (inr e) = inr (unit , e)
clsOK (sh-pi {A} {F}) d = constCls cPi (V2.ev (valPi {A = A} {F = F} d)) refl
clsOK (sh-sig {A} {F}) d = constCls cSig (V2.ev (valSig {A = A} {F = F} d)) refl
clsOK sh-nat (r , vv) = constCls cNat (red-const nat-c r) refl
clsOK sh-ze (r , vv) = constCls cZe (red-const ze-c r) refl
clsOK (sh-sc {k}) d = constCls cSc (V1.ev (valSc {k = k} d)) refl
clsOK sh-V (r , vv) = constCls cV (red-const V-c r) refl
clsOK (sh-U {f} {g}) d = constCls cU (V2.ev (valU {f = f} {g = g} d)) refl

private
  trOK : {K : Cls} {a b : Tm} -> Eq (etanf a) (etanf b) -> ClsOK K (cls (etanf b)) -> ClsOK K (cls (etanf a))
  trOK e k = transport (\ X -> ClsOK _ (cls X)) (Eq-sym e) k

mismatch : {n : Num} {w w' : Expr n} {va vb : Tm} (sh : SynSh w) (sh' : SynSh w') ->
  den w idE ⇓ va -> den w' idE ⇓ vb -> Eq (etanf va) (etanf vb) -> Distinct (shK sh) (shK sh') -> Empty
mismatch {va = va} {vb = vb} sh sh' d d' e dist = clash (clsOK sh d) (trOK {a = va} {b = vb} e (clsOK sh' d')) dist

------------------------------------------------------------------------
-- auxiliaries
------------------------------------------------------------------------

private
  noZ : {a b : Num} -> (suc a ⊕ b) <= zero -> Empty
  noZ ()

  noS : {c : Num} -> suc c <= zero -> Empty
  noS ()

  noL : (va vb : Tm) (k : Num) -> Eq (lp va) (suc k) -> (lp va ⊕ lp vb) <= zero -> Empty
  noL va vb k e p = noS (M.eq-<= (Eq-sym (Eq-cong (\ x -> x ⊕ lp vb) e)) p)

  noR : (va vb : Tm) (k : Num) -> Eq (lp vb) (suc k) -> (lp va ⊕ lp vb) <= zero -> Empty
  noR va vb k e p = noS (M.eq-<= (Eq-sym (Eq-trans (Eq-cong (\ x -> lp va ⊕ x) e) (M.+-suc (lp va) k))) p)

  lpLam : {v x : Tm} -> Eq v (tlam x) -> Eq (lp v) (suc (lp x))
  lpLam refl = refl

  lpPair : {v x y : Tm} -> Eq v (tpair x y) -> Eq (lp v) (suc (lp x ⊕ lp y))
  lpPair refl = refl

  noSz : (va vb : Tm) -> (sz va ⊕ sz vb) <= zero -> Empty
  noSz va vb p = go (M.sz-pos va) p
    where
      go : Sg Num (\ k -> Eq (sz va) (suc k)) -> (sz va ⊕ sz vb) <= zero -> Empty
      go (k , e) q = noS (M.eq-<= (Eq-sym (Eq-cong (\ x -> x ⊕ sz vb) e)) q)

  noZ' : {a b : Num} -> (a ⊕ suc b) <= zero -> Empty
  noZ' {a} {b} p = noS (M.eq-<= (Eq-sym (M.+-suc a b)) p)

  +zero : (a : Num) -> Eq (a ⊕ zero) a
  +zero zero = refl
  +zero (suc a) = Eq-cong suc (+zero a)

  tpiI : {a b c d : Tm} -> Eq (tpi a b) (tpi c d) -> Eq a c * Eq b d
  tpiI refl = refl , refl
  tsigI : {a b c d : Tm} -> Eq (tsig a b) (tsig c d) -> Eq a c * Eq b d
  tsigI refl = refl , refl
  tUI : {a b c d : Tm} -> Eq (tU a b) (tU c d) -> Eq a c * Eq b d
  tUI refl = refl , refl
  tappI : {a b c d : Tm} -> Eq (tapp a b) (tapp c d) -> Eq a c * Eq b d
  tappI refl = refl , refl
  tscI : {a b : Tm} -> Eq (tsc a) (tsc b) -> Eq a b
  tscI refl = refl
  tfstI : {a b : Tm} -> Eq (tfst a) (tfst b) -> Eq a b
  tfstI refl = refl
  tsndI : {a b : Tm} -> Eq (tsnd a) (tsnd b) -> Eq a b
  tsndI refl = refl
  tvarI : {a b : Num} -> Eq (tvar a) (tvar b) -> Eq a b
  tvarI refl = refl
  trecI : {a b c d a' b' c' d' : Tm} -> Eq (trec a b c d) (trec a' b' c' d') -> Eq a a' * (Eq b b' * (Eq c c' * Eq d d'))
  trecI refl = refl , (refl , (refl , refl))

  -- lp / sz of an abstraction body is below that of the abstraction
  lpBody : {f fb : Tm} -> Eq f (tlam fb) -> lp fb <= lp f
  lpBody refl = <=-suc (<=-refl _)
  szBody : {f fb : Tm} -> Eq f (tlam fb) -> sz fb <= sz f
  szBody refl = <=-suc (<=-refl _)
  <=-suc' : {a b : Num} -> a <= b -> a <= suc b
  <=-suc' = <=-suc
  <=-suc'' : {a b : Num} -> suc a <= b -> a <= b
  <=-suc'' {a} p = <=-trans (<=-suc (<=-refl a)) p

  lpTr : {a b : Tm} -> Eq a b -> lp a <= lp b
  lpTr refl = <=-refl _
  szTr : {a b : Tm} -> Eq a b -> sz a <= sz b
  szTr refl = <=-refl _

  tr<= : {a b c : Num} -> Eq a b -> a <= c -> b <= c
  tr<= refl p = p

  -- the sum over two values, transported along their shapes
  sumL : (f : Tm -> Num) {va vb x y : Tm} -> Eq va x -> Eq vb y -> Eq (f va ⊕ f vb) (f x ⊕ f y)
  sumL f refl refl = refl

  eqE : {va vb x y : Tm} -> Eq va x -> Eq vb y -> Eq (etanf va) (etanf vb) -> Eq (etanf x) (etanf y)
  eqE refl refl e = e

  tlamI : {a b : Tm} -> Eq (tlam a) (tlam b) -> Eq a b
  tlamI refl = refl

  -- Pi / Sigma with a literal family
  record TyPiF {n : Num} (G : Ctx n) (A F : Expr n) : Set where
    constructor typif
    field
      B  : Expr (suc n)
      eF : Eq F (Lam A B)
      iA : IsType G A
      iB : IsType (extend G A) B

  tyPiF : {n : Num} {G : Ctx n} {A F : Expr n} -> IsType G (Pi A F) -> TyPiF G A F
  tyPiF (isty-el h) = typif B eF (elTy un hA) (elTy (renUniv wkRen un) hB)
    where open PiInv (invPi h)
  tyPiF (isty-Pi iA iB) = typif _ refl iA iB

  tySigF : {n : Num} {G : Ctx n} {A F : Expr n} -> IsType G (Sigma A F) -> TyPiF G A F
  tySigF (isty-el h) = typif B eF (elTy un hA) (elTy (renUniv wkRen un) hB)
    where open PiInv (invSigma h)
  tySigF (isty-Sigma iA iB) = typif _ refl iA iB

  -- the common type of two evaluated terms
  record Common {n : Num} (G : Ctx n) (w w' : Expr n) : Set where
    constructor common
    field
      T  : Expr n
      hw : HasType G w T
      hw' : HasType G w' T

  commonTy : {n : Num} {G : Ctx n} {t t' w w' C : Expr n} -> HasType G t C -> HasType G t' C -> HRs t w -> HRs t' w' -> Common G w w'
  commonTy ht ht' r r' = go (evalC ht r) (evalC ht' r')
    where
      viaV : {f g : Expr _} -> TyEq _ _ (Ucode f g) -> Common _ _ _
      viaV e = common V (snd (pCv (evalV (ty-sub (ty-conv ht e)) r))) (snd (pCv (evalV (ty-sub (ty-conv ht' e)) r')))
      go : _ -> _ -> Common _ _ _
      go (inl c) (inl c') = common _ (snd (pCv c)) (snd (pCv c'))
      go (inr (f , (g , e))) _ = viaV e
      go (inl c) (inr (f , (g , e))) = viaV e

------------------------------------------------------------------------
-- kinds of neutrals
------------------------------------------------------------------------

data NK : Set where
  kv ka kf ks kr ko : NK

ncls : Tm -> NK
ncls (tvar _) = kv
ncls (tapp _ _) = ka
ncls (tfst _) = kf
ncls (tsnd _) = ks
ncls (trec _ _ _ _) = kr
ncls (tlam _) = ko
ncls (tpi _ _) = ko
ncls (tsig _ _) = ko
ncls (tpair _ _) = ko
ncls tnat = ko
ncls tze = ko
ncls (tsc _) = ko
ncls tV = ko
ncls (tU _ _) = ko

snK : {n : Num} {w : Expr n} -> SNe w -> NK
snK sne-var = kv
snK (sne-app _) = ka
snK (sne-fst _) = kf
snK (sne-snd _) = ks
snK (sne-rec _) = kr

NKDiff : NK -> NK -> Set
NKDiff a b = Eq a b -> Empty

nkNE : {a b : NK} -> Eq a b -> NKDiff a b -> Empty
nkNE e d = d e

private
  nkTr : {a b : Tm} {k : NK} -> Eq a b -> Eq (ncls (etanf b)) k -> Eq (ncls (etanf a)) k
  nkTr refl e = e

neK : {n : Num} {w : Expr n} {v : Tm} (sn : SNe w) -> den w idE ⇓ v -> Eq (ncls (etanf v)) (snK sn)
neK sne-var d = nkTr (valVar d) refl
neK (sne-app {u} {v} n) d = nkTr (V2.ev (valApp {u = u} {a = v} n d)) refl
neK (sne-fst n) d = nkTr (V1.ev (valFst n d)) refl
neK (sne-snd n) d = nkTr (V1.ev (valSnd n d)) refl
neK (sne-rec n) (r , vv) = nkTr (RecRed.ev (red-rec (wneOf n) r)) refl

neMismatch : {n : Num} {w w' : Expr n} {va vb : Tm} (sn : SNe w) (sn' : SNe w') ->
  den w idE ⇓ va -> den w' idE ⇓ vb -> Eq (etanf va) (etanf vb) -> NKDiff (snK sn) (snK sn') -> Empty
neMismatch sn sn' d d' e = nkNE (Eq-trans (Eq-sym (neK sn d)) (Eq-trans (Eq-cong ncls e) (neK sn' d')))

-- small types are elements of V
elNe : {n : Num} {G : Ctx n} {w : Expr n} -> SNe w -> IsType G w -> HasType G w V
elNe sne-var (isty-el h) = h
elNe (sne-app n) (isty-el h) = h
elNe (sne-fst n) (isty-el h) = h
elNe (sne-snd n) (isty-el h) = h
elNe (sne-rec n) (isty-el h) = h

elNat : {n : Num} {G : Ctx n} -> IsType G Nat -> HasType G Nat V
elNat (isty-el h) = h
elZe : {n : Num} {G : Ctx n} -> IsType G Zero -> HasType G Zero V
elZe (isty-el h) = h
elSc : {n : Num} {G : Ctx n} {k : Expr n} -> IsType G (Suc k) -> HasType G (Suc k) V
elSc (isty-el h) = h
elU : {n : Num} {G : Ctx n} {f g : Expr n} -> IsType G (Ucode f g) -> HasType G (Ucode f g) V
elU (isty-el h) = h

------------------------------------------------------------------------
-- completeness
------------------------------------------------------------------------

mutual

  comp : (cb sb : Num) {n : Num} {G : Ctx n} {t t' C : Expr n} {va vb : Tm} ->
    HasType G t C -> HasType G t' C -> den t idE ⇓ va -> den t' idE ⇓ vb -> Eq (etanf va) (etanf vb) ->
    (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgEq t t'
  comp cb sb {t = t} {t'} ht ht' da db e bc bs =
    alg (WhnfRes.rs W) (WhnfRes.rs W')
      (compW cb sb (WhnfRes.sh W) (WhnfRes.sh W') (Common.hw K) (Common.hw' K) (WhnfRes.dv W) (WhnfRes.dv W') e bc bs)
    where
      W = whnfOf t da
      W' = whnfOf t' db
      K = commonTy ht ht' (WhnfRes.rs W) (WhnfRes.rs W')

  ----------------------------------------------------------------------
  -- abstractions
  ----------------------------------------------------------------------

  caseLL : (cb sb : Num) {n : Num} {G : Ctx n} {C A A' : Expr n} {b b' : Expr (suc n)} {va vb : Tm} ->
    HasType G (Lam A b) C -> HasType G (Lam A' b') C -> den (Lam A b) idE ⇓ va -> den (Lam A' b') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Lam A b) (Lam A' b')
  caseLL zero sb {A = A} {A'} {b} {b'} {va = va} {vb = vb} hw hw' dw dw' e bc bs =
    Empty-elim (noL va vb _ (lpLam (VLam.ev (valLam {A = A} {b = b} dw))) bc)
  caseLL (suc cb) sb {A = A} {A'} {b} {b'} hw hw' dw dw' e bc bs =
    w-lam (comp cb (sz x ⊕ sz y) (LamInv.ht I) hb'A (VLam.dx L) (VLam.dx L') ex
             (ar-LL (lp x) (lp y) cb (tr<= (sumL lp (VLam.ev L) (VLam.ev L')) bc)) (<=-refl _))
    where
      L = valLam {A = A} {b = b} dw ; L' = valLam {A = A'} {b = b'} dw'
      x = VLam.x L ; y = VLam.x L'
      I = invLam hw ; I' = invLam hw'
      pj = Pi-inj (tyeq-trans (tyeq-sym (LamInv.eq I)) (LamInv.eq I'))
      hb'A = ty-conv (ccTm (LamInv.hA I) (fst pj) (LamInv.ht I')) (tyeq-sym (snd pj))
      ex = E-lam (etanf-val (snd (VLam.dx L))) (etanf-val (snd (VLam.dx L'))) (eqE (VLam.ev L) (VLam.ev L') e)

  caseLN : (cb sb : Num) {n : Num} {G : Ctx n} {C A w' : Expr n} {b : Expr (suc n)} {va vb : Tm} -> SNe w' ->
    HasType G (Lam A b) C -> HasType G w' C -> den (Lam A b) idE ⇓ va -> den w' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Lam A b) w'
  caseLN zero sb {A = A} {b = b} {va = va} {vb = vb} n' hw hw' dw dw' e bc bs =
    Empty-elim (noL va vb _ (lpLam (VLam.ev (valLam {A = A} {b = b} dw))) bc)
  caseLN (suc cb) sb {A = A} {w'} {b} {vb = vb} n' hw hw' dw dw' e bc bs =
    w-lamL (comp cb _ (LamInv.ht I) hApp (VLam.dx L) dApp ex bnd (<=-refl _))
    where
      L = valLam {A = A} {b = b} dw
      x = VLam.x L
      nv = valNe n' dw'
      I = invLam hw
      htP = ty-conv hw' (LamInv.eq I)
      hApp = appWk (LamInv.hA I) (LamInv.hB I) htP
      dApp = valWkApp {w = w'} nv dw'
      ex = Eq-trans (E-lamNe (etanf-val (snd (VLam.dx L))) (etanf-ne nv) (eqE {vb = vb} (VLam.ev L) refl e))
                    (Eq-sym (etanf-shift-app vb))
      bnd = tr<= (Eq-sym (Eq-cong (\ k -> lp x ⊕ k) (Eq-trans (+zero _) (lp-ren suc vb))))
              (ar-LN (lp x) (lp vb) cb (tr<= (sumL lp {vb = vb} (VLam.ev L) refl) bc))

  caseNL : (cb sb : Num) {n : Num} {G : Ctx n} {C w A' : Expr n} {b' : Expr (suc n)} {va vb : Tm} -> SNe w ->
    HasType G w C -> HasType G (Lam A' b') C -> den w idE ⇓ va -> den (Lam A' b') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW w (Lam A' b')
  caseNL zero sb {A' = A'} {b' = b'} {va = va} {vb = vb} n hw hw' dw dw' e bc bs =
    Empty-elim (noR va vb _ (lpLam (VLam.ev (valLam {A = A'} {b = b'} dw'))) bc)
  caseNL (suc cb) sb {w = w} {A'} {b'} {va = va} n hw hw' dw dw' e bc bs =
    w-lamR (comp cb _ hApp (LamInv.ht I') dApp (VLam.dx L') ex bnd (<=-refl _))
    where
      L' = valLam {A = A'} {b = b'} dw'
      y = VLam.x L'
      nv = valNe n dw
      I' = invLam hw'
      htP = ty-conv hw (LamInv.eq I')
      hApp = appWk (LamInv.hA I') (LamInv.hB I') htP
      dApp = valWkApp {w = w} nv dw
      ex = Eq-sym (Eq-trans (E-lamNe (etanf-val (snd (VLam.dx L'))) (etanf-ne nv) (Eq-sym (eqE {va = va} refl (VLam.ev L') e)))
                    (Eq-sym (etanf-shift-app va)))
      bnd = tr<= (Eq-sym (Eq-cong (\ k -> k ⊕ lp y) (Eq-trans (+zero _) (lp-ren suc va))))
              (ar-NL (lp va) (lp y) cb (tr<= (sumL lp {va = va} refl (VLam.ev L')) bc))

  ----------------------------------------------------------------------
  -- pairs
  ----------------------------------------------------------------------

  casePP : (cb sb : Num) {n : Num} {G : Ctx n} {C t u t' u' : Expr n} {va vb : Tm} ->
    HasType G (Pair t u) C -> HasType G (Pair t' u') C -> den (Pair t u) idE ⇓ va -> den (Pair t' u') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Pair t u) (Pair t' u')
  casePP zero sb {t = t} {u} {t'} {u'} {va = va} {vb = vb} hw hw' dw dw' e bc bs =
    Empty-elim (noL va vb _ (lpPair (V2.ev (valPair {a = t} {b = u} dw))) bc)
  casePP (suc cb) sb {t = t} {u} {t'} {u'} hw hw' dw dw' e bc bs = w-pair R1 R2
    where
      P = valPair {a = t} {b = u} dw ; P' = valPair {a = t'} {b = u'} dw'
      x1 = V2.x P ; x2 = V2.y P ; y1 = V2.x P' ; y2 = V2.y P'
      Ee = E-pair (etanf-val (snd (V2.dx P))) (etanf-val (snd (V2.dx P'))) (eqE (V2.ev P) (V2.ev P') e)
      bc' = pred<= (tr<= (sumL lp (V2.ev P) (V2.ev P')) bc)
      I = invPair hw ; I' = invPair hw'
      wG = wfTm hw
      sj = Sig-inj (tyeq-trans (tyeq-sym (PairInv.eq I)) (PairInv.eq I'))
      ht'A = ty-conv (PairInv.ht I') (tyeq-sym (fst sj))
      hu'B = ty-conv (PairInv.hu I') (s1TE wG ht'A (tyeq-sym (snd sj)))
      R1 = comp cb (sz x1 ⊕ sz y1) (PairInv.ht I) ht'A (V2.dx P) (V2.dx P') (fst Ee)
             (ar-sub (<=+l (lp x1) (lp x2)) (<=-suc (<=+l (lp y1) (lp y2))) bc') (<=-refl _)
      ct = algsound (PairInv.ht I) ht'A R1
      tq = s1fTy wG (PairInv.hA I) (PairInv.ht I) ht'A ct (PairInv.hB I)
      R2 = comp cb (sz x2 ⊕ sz y2) (PairInv.hu I) (ty-conv hu'B (tyeq-sym tq)) (V2.dy P) (V2.dy P') (snd Ee)
             (ar-sub (<=+r (lp x1) (lp x2)) (<=-suc (<=+r (lp y1) (lp y2))) bc') (<=-refl _)

  casePN : (cb sb : Num) {n : Num} {G : Ctx n} {C t u w' : Expr n} {va vb : Tm} -> SNe w' ->
    HasType G (Pair t u) C -> HasType G w' C -> den (Pair t u) idE ⇓ va -> den w' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Pair t u) w'
  casePN zero sb {t = t} {u} {va = va} {vb = vb} n' hw hw' dw dw' e bc bs =
    Empty-elim (noL va vb _ (lpPair (V2.ev (valPair {a = t} {b = u} dw))) bc)
  casePN (suc cb) sb {t = t} {u} {w'} {vb = vb} n' hw hw' dw dw' e bc bs = w-pairL R1 R2
    where
      P = valPair {a = t} {b = u} dw
      x1 = V2.x P ; x2 = V2.y P
      nv = valNe n' dw'
      EN = E-pairNe (etanf-ne nv) (eqE {vb = vb} (V2.ev P) refl e)
      bc' = pred<= (tr<= (sumL lp {vb = vb} (V2.ev P) refl) bc)
      I = invPair hw
      wG = wfTm hw
      hP' = ty-conv hw' (PairInv.eq I)
      hF' = ty-Fst (PairInv.hA I) (PairInv.hB I) hP'
      R1 = comp cb _ (PairInv.ht I) hF' (V2.dx P) (valFstOf {w = w'} nv dw') (fst EN)
             (ar-sub (<=+l (lp x1) (lp x2)) (<=-refl (lp vb)) bc') (<=-refl _)
      ct = algsound (PairInv.ht I) hF' R1
      q = tyeq-sym (s1fTy wG (PairInv.hA I) (PairInv.ht I) hF' ct (PairInv.hB I))
      R2 = comp cb _ (PairInv.hu I) (ty-conv (ty-Snd (PairInv.hA I) (PairInv.hB I) hP') q) (V2.dy P) (valSndOf {w = w'} nv dw') (snd EN)
             (ar-sub (<=+r (lp x1) (lp x2)) (<=-refl (lp vb)) bc') (<=-refl _)

  caseNP : (cb sb : Num) {n : Num} {G : Ctx n} {C w t' u' : Expr n} {va vb : Tm} -> SNe w ->
    HasType G w C -> HasType G (Pair t' u') C -> den w idE ⇓ va -> den (Pair t' u') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW w (Pair t' u')
  caseNP zero sb {t' = t'} {u'} {va = va} {vb = vb} n hw hw' dw dw' e bc bs =
    Empty-elim (noR va vb _ (lpPair (V2.ev (valPair {a = t'} {b = u'} dw'))) bc)
  caseNP (suc cb) sb {w = w} {t'} {u'} {va = va} n hw hw' dw dw' e bc bs = w-pairR R1 R2
    where
      P' = valPair {a = t'} {b = u'} dw'
      y1 = V2.x P' ; y2 = V2.y P'
      nv = valNe n dw
      EN = E-pairNe (etanf-ne nv) (Eq-sym (eqE {va = va} refl (V2.ev P') e))
      bc' = ar-NL (lp va) (lp y1 ⊕ lp y2) cb (tr<= (sumL lp {va = va} refl (V2.ev P')) bc)
      I' = invPair hw'
      wG = wfTm hw
      hP = ty-conv hw (PairInv.eq I')
      hF = ty-Fst (PairInv.hA I') (PairInv.hB I') hP
      R1 = comp cb _ hF (PairInv.ht I') (valFstOf {w = w} nv dw) (V2.dx P') (Eq-sym (fst EN))
             (ar-sub (<=-refl (lp va)) (<=+l (lp y1) (lp y2)) bc') (<=-refl _)
      ct = algsound hF (PairInv.ht I') R1
      q = s1fTy wG (PairInv.hA I') hF (PairInv.ht I') ct (PairInv.hB I')
      R2 = comp cb _ (ty-Snd (PairInv.hA I') (PairInv.hB I') hP) (ty-conv (PairInv.hu I') (tyeq-sym q))
             (valSndOf {w = w} nv dw) (V2.dy P') (Eq-sym (snd EN))
             (ar-sub (<=-refl (lp va)) (<=+r (lp y1) (lp y2)) bc') (<=-refl _)

  ----------------------------------------------------------------------
  -- constructors
  ----------------------------------------------------------------------

  casePi : (cb sb : Num) {n : Num} {G : Ctx n} {C A F A' F' : Expr n} {va vb : Tm} ->
    HasType G (Pi A F) C -> HasType G (Pi A' F') C -> den (Pi A F) idE ⇓ va -> den (Pi A' F') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Pi A F) (Pi A' F')
  casePi cb zero {va = va} {vb = vb} hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  casePi cb (suc sb) {G = G} {A = A} {F} {A'} {F'} hw hw' dw dw' e bc bs =
    transport2 (\ X Y -> AlgW (Pi A X) (Pi A' Y)) (Eq-sym (PiInv.eF P)) (Eq-sym (PiInv.eF P')) (w-pi RA RB)
    where
      P = invPi hw ; P' = invPi hw'
      Vv = valPi {A = A} {F = F} dw ; Vv' = valPi {A = A'} {F = F'} dw'
      x = V2.x Vv ; f = V2.y Vv ; y = V2.x Vv' ; g = V2.y Vv'
      L = valLam {A = A} {b = PiInv.B P} (transport (\ X -> den X idE ⇓ f) (PiInv.eF P) (V2.dy Vv))
      L' = valLam {A = A'} {b = PiInv.B P'} (transport (\ X -> den X idE ⇓ g) (PiInv.eF P') (V2.dy Vv'))
      ee = tpiI (eqE (V2.ev Vv) (V2.ev Vv') e)
      eB = E-lam (etanf-val (snd (VLam.dx L))) (etanf-val (snd (VLam.dx L'))) (eqE (VLam.ev L) (VLam.ev L') (snd ee))
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      un = PiInv.un P
      hA = PiInv.hA P
      iA = elTy un hA
      quu = tyeq-trans (tyeq-sym (PiInv.eq P')) (PiInv.eq P)
      RA = comp cb sb hA (ty-conv (PiInv.hA P') quu) (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp f)) (<=+l (lp y) (lp g)) bcp)
             (ar-sub (<=+l (sz x) (sz f)) (<=-suc (<=+l (sz y) (sz g))) bsp)
      qA = cvTE un (algsound hA (ty-conv (PiInv.hA P') quu) RA)
      hB'A = ty-conv (ccTm iA qA (PiInv.hB P')) (wkTE iA quu)
      RB = comp cb sb (PiInv.hB P) hB'A (VLam.dx L) (VLam.dx L') eB
             (ar-sub (<=-trans (lpBody (VLam.ev L)) (<=+r (lp x) (lp f))) (<=-trans (lpBody (VLam.ev L')) (<=+r (lp y) (lp g))) bcp)
             (ar-sub (<=-trans (szBody (VLam.ev L)) (<=+r (sz x) (sz f)))
                     (<=-suc (<=-trans (szBody (VLam.ev L')) (<=+r (sz y) (sz g)))) bsp)

  caseSig : (cb sb : Num) {n : Num} {G : Ctx n} {C A F A' F' : Expr n} {va vb : Tm} ->
    HasType G (Sigma A F) C -> HasType G (Sigma A' F') C -> den (Sigma A F) idE ⇓ va -> den (Sigma A' F') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Sigma A F) (Sigma A' F')
  caseSig cb zero {va = va} {vb = vb} hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  caseSig cb (suc sb) {G = G} {A = A} {F} {A'} {F'} hw hw' dw dw' e bc bs =
    transport2 (\ X Y -> AlgW (Sigma A X) (Sigma A' Y)) (Eq-sym (PiInv.eF P)) (Eq-sym (PiInv.eF P')) (w-sigma RA RB)
    where
      P = invSigma hw ; P' = invSigma hw'
      Vv = valSig {A = A} {F = F} dw ; Vv' = valSig {A = A'} {F = F'} dw'
      x = V2.x Vv ; f = V2.y Vv ; y = V2.x Vv' ; g = V2.y Vv'
      L = valLam {A = A} {b = PiInv.B P} (transport (\ X -> den X idE ⇓ f) (PiInv.eF P) (V2.dy Vv))
      L' = valLam {A = A'} {b = PiInv.B P'} (transport (\ X -> den X idE ⇓ g) (PiInv.eF P') (V2.dy Vv'))
      ee = tsigI (eqE (V2.ev Vv) (V2.ev Vv') e)
      eB = E-lam (etanf-val (snd (VLam.dx L))) (etanf-val (snd (VLam.dx L'))) (eqE (VLam.ev L) (VLam.ev L') (snd ee))
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      un = PiInv.un P
      hA = PiInv.hA P
      iA = elTy un hA
      quu = tyeq-trans (tyeq-sym (PiInv.eq P')) (PiInv.eq P)
      RA = comp cb sb hA (ty-conv (PiInv.hA P') quu) (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp f)) (<=+l (lp y) (lp g)) bcp)
             (ar-sub (<=+l (sz x) (sz f)) (<=-suc (<=+l (sz y) (sz g))) bsp)
      qA = cvTE un (algsound hA (ty-conv (PiInv.hA P') quu) RA)
      hB'A = ty-conv (ccTm iA qA (PiInv.hB P')) (wkTE iA quu)
      RB = comp cb sb (PiInv.hB P) hB'A (VLam.dx L) (VLam.dx L') eB
             (ar-sub (<=-trans (lpBody (VLam.ev L)) (<=+r (lp x) (lp f))) (<=-trans (lpBody (VLam.ev L')) (<=+r (lp y) (lp g))) bcp)
             (ar-sub (<=-trans (szBody (VLam.ev L)) (<=+r (sz x) (sz f)))
                     (<=-suc (<=-trans (szBody (VLam.ev L')) (<=+r (sz y) (sz g)))) bsp)

  caseSc : (cb sb : Num) {n : Num} {G : Ctx n} {C k k' : Expr n} {va vb : Tm} ->
    HasType G (Suc k) C -> HasType G (Suc k') C -> den (Suc k) idE ⇓ va -> den (Suc k') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Suc k) (Suc k')
  caseSc cb zero {va = va} {vb = vb} hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  caseSc cb (suc sb) {k = k} {k'} hw hw' dw dw' e bc bs =
    w-suc (comp cb sb (fst (invSuc hw)) (fst (invSuc hw')) (V1.dx Vv) (V1.dx Vv') (tscI (eqE (V1.ev Vv) (V1.ev Vv') e))
             (tr<= (sumL lp (V1.ev Vv) (V1.ev Vv')) bc)
             (ar-sub (<=-refl _) (<=-suc (<=-refl _)) (pred<= (tr<= (sumL sz (V1.ev Vv) (V1.ev Vv')) bs))))
    where
      Vv = valSc {k = k} dw ; Vv' = valSc {k = k'} dw'

  caseU : (cb sb : Num) {n : Num} {G : Ctx n} {C f g f' g' : Expr n} {va vb : Tm} ->
    HasType G (Ucode f g) C -> HasType G (Ucode f' g') C -> den (Ucode f g) idE ⇓ va -> den (Ucode f' g') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Ucode f g) (Ucode f' g')
  caseU cb zero {va = va} {vb = vb} hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  caseU cb (suc sb) {f = f0} {g0} {f0'} {g0'} hw hw' dw dw' e bc bs = w-ucode Rf Rg
    where
      Vv = valU {f = f0} {g = g0} dw ; Vv' = valU {f = f0'} {g = g0'} dw'
      x = V2.x Vv ; xg = V2.y Vv ; y = V2.x Vv' ; yg = V2.y Vv'
      ee = tUI (eqE (V2.ev Vv) (V2.ev Vv') e)
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      hf = fst (invUcode hw) ; hg = fst (snd (invUcode hw))
      hf' = fst (invUcode hw') ; hg' = fst (snd (invUcode hw'))
      Rf = comp cb sb hf hf' (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp xg)) (<=+l (lp y) (lp yg)) bcp)
             (ar-sub (<=+l (sz x) (sz xg)) (<=-suc (<=+l (sz y) (sz yg))) bsp)
      cf = algsound hf hf' Rf
      Rg = comp cb sb hg (ty-conv hg' (tyeq-sym (opGEq (wfTm hf) hf hf' cf))) (V2.dy Vv) (V2.dy Vv') (snd ee)
             (ar-sub (<=+r (lp x) (lp xg)) (<=+r (lp y) (lp yg)) bcp)
             (ar-sub (<=+r (sz x) (sz xg)) (<=-suc (<=+r (sz y) (sz yg))) bsp)

  ----------------------------------------------------------------------
  -- neutrals
  ----------------------------------------------------------------------

  compNe : (cb sb : Num) {n : Num} {G : Ctx n} {w w' C C' : Expr n} {va vb : Tm} -> SNe w -> SNe w' ->
    HasType G w C -> HasType G w' C' -> den w idE ⇓ va -> den w' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgNe w w'
  compNe cb sb (sne-var {i = i}) (sne-var {i = j}) hw hw' dw dw' e bc bs =
    transport (\ X -> AlgNe (Var i) (Var X)) (f2n-inj (tvarI (eqE (valVar dw) (valVar dw') e))) ne-var
  compNe cb sb (sne-app nu) (sne-app nu') hw hw' dw dw' e bc bs = appNe cb sb nu nu' hw hw' dw dw' e bc bs
  compNe cb sb (sne-fst nu) (sne-fst nu') hw hw' dw dw' e bc bs = fstNe cb sb nu nu' hw hw' dw dw' e bc bs
  compNe cb sb (sne-snd nu) (sne-snd nu') hw hw' dw dw' e bc bs = sndNe cb sb nu nu' hw hw' dw dw' e bc bs
  compNe cb sb (sne-rec {C = F} {z} {s} {k} nk) (sne-rec {C = F'} {z'} {s'} {k'} nk') hw hw' dw dw' e bc bs =
    recNe cb sb nk nk' (RecInv.eF I) (RecInv.eF I') hw hw' dw dw' e bc bs
    where I = invRec hw ; I' = invRec hw'
  compNe cb sb n1@sne-var n2@(sne-app _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@sne-var n2@(sne-fst _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@sne-var n2@(sne-snd _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@sne-var n2@(sne-rec _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-app _) n2@sne-var hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-app _) n2@(sne-fst _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-app _) n2@(sne-snd _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-app _) n2@(sne-rec _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-fst _) n2@sne-var hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-fst _) n2@(sne-app _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-fst _) n2@(sne-snd _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-fst _) n2@(sne-rec _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-snd _) n2@sne-var hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-snd _) n2@(sne-app _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-snd _) n2@(sne-fst _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-snd _) n2@(sne-rec _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-rec _) n2@sne-var hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-rec _) n2@(sne-app _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-rec _) n2@(sne-fst _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))
  compNe cb sb n1@(sne-rec _) n2@(sne-snd _) hw hw' dw dw' e bc bs = Empty-elim (neMismatch n1 n2 dw dw' e (\ ()))

  appNe : (cb sb : Num) {n : Num} {G : Ctx n} {u u' a a' C C' : Expr n} {va vb : Tm} -> SNe u -> SNe u' ->
    HasType G (App u a) C -> HasType G (App u' a') C' -> den (App u a) idE ⇓ va -> den (App u' a') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgNe (App u a) (App u' a')
  appNe cb zero {va = va} {vb = vb} nu nu' hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  appNe cb (suc sb) {u = u} {u'} {a} {a'} nu nu' hw hw' dw dw' e bc bs = ne-app Rnn Ra
    where
      Vv = valApp {u = u} {a = a} nu dw ; Vv' = valApp {u = u'} {a = a'} nu' dw'
      x = V2.x Vv ; xa = V2.y Vv ; y = V2.x Vv' ; ya = V2.y Vv'
      ee = tappI (eqE (V2.ev Vv) (V2.ev Vv') e)
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      I = invApp hw ; I' = invApp hw'
      Rnn = compNe cb sb nu nu' (AppInv.ht I) (AppInv.ht I') (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp xa)) (<=+l (lp y) (lp ya)) bcp)
             (ar-sub (<=+l (sz x) (sz xa)) (<=-suc (<=+l (sz y) (sz ya))) bsp)
      NR = sNe Rnn (AppInv.ht I) (AppInv.ht I')
      e1 = upPi (NeRes.upL NR (AppInv.ht I))
      e1' = upPi (NeRes.upR NR (AppInv.ht I'))
      pj = Pi-inj (tyeq-trans e1' (tyeq-sym e1))
      Ra = comp cb sb (AppInv.ha I) (ty-conv (AppInv.ha I') (fst pj)) (V2.dy Vv) (V2.dy Vv') (snd ee)
             (ar-sub (<=+r (lp x) (lp xa)) (<=+r (lp y) (lp ya)) bcp)
             (ar-sub (<=+r (sz x) (sz xa)) (<=-suc (<=+r (sz y) (sz ya))) bsp)

  fstNe : (cb sb : Num) {n : Num} {G : Ctx n} {w w' C C' : Expr n} {va vb : Tm} -> SNe w -> SNe w' ->
    HasType G (Fst w) C -> HasType G (Fst w') C' -> den (Fst w) idE ⇓ va -> den (Fst w') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgNe (Fst w) (Fst w')
  fstNe cb zero {va = va} {vb = vb} nu nu' hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  fstNe cb (suc sb) {w = w} {w'} nu nu' hw hw' dw dw' e bc bs =
    ne-fst (compNe cb sb nu nu' (FstInv.ht (invFst hw)) (FstInv.ht (invFst hw')) (V1.dx Vv) (V1.dx Vv')
              (tfstI (eqE (V1.ev Vv) (V1.ev Vv') e)) (tr<= (sumL lp (V1.ev Vv) (V1.ev Vv')) bc)
              (ar-sub (<=-refl _) (<=-suc (<=-refl _)) (pred<= (tr<= (sumL sz (V1.ev Vv) (V1.ev Vv')) bs))))
    where Vv = valFst {u = w} nu dw ; Vv' = valFst {u = w'} nu' dw'

  sndNe : (cb sb : Num) {n : Num} {G : Ctx n} {w w' C C' : Expr n} {va vb : Tm} -> SNe w -> SNe w' ->
    HasType G (Snd w) C -> HasType G (Snd w') C' -> den (Snd w) idE ⇓ va -> den (Snd w') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgNe (Snd w) (Snd w')
  sndNe cb zero {va = va} {vb = vb} nu nu' hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  sndNe cb (suc sb) {w = w} {w'} nu nu' hw hw' dw dw' e bc bs =
    ne-snd (compNe cb sb nu nu' (SndInv.ht (invSnd hw)) (SndInv.ht (invSnd hw')) (V1.dx Vv) (V1.dx Vv')
              (tsndI (eqE (V1.ev Vv) (V1.ev Vv') e)) (tr<= (sumL lp (V1.ev Vv) (V1.ev Vv')) bc)
              (ar-sub (<=-refl _) (<=-suc (<=-refl _)) (pred<= (tr<= (sumL sz (V1.ev Vv) (V1.ev Vv')) bs))))
    where Vv = valSnd {u = w} nu dw ; Vv' = valSnd {u = w'} nu' dw'

  recNe : (cb sb : Num) {n : Num} {G : Ctx n} {F F' z z' s s' k k' C1 C1' : Expr n} {C0 C0' : Expr (suc n)} {va vb : Tm} ->
    SNe k -> SNe k' -> Eq F (Lam Nat C0) -> Eq F' (Lam Nat C0') ->
    HasType G (Rec F z s k) C1 -> HasType G (Rec F' z' s' k') C1' -> den (Rec F z s k) idE ⇓ va -> den (Rec F' z' s' k') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgNe (Rec F z s k) (Rec F' z' s' k')
  recNe cb zero {va = va} {vb = vb} nk nk' refl refl hw hw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  recNe cb (suc sb) {G = G} {z = z} {z'} {s} {s'} {k} {k'} {C0 = C0} {C0'} nk nk' refl refl hw hw' dw dw' e bc bs = ne-rec RC Rz Rs Rk
    where
      I = invRec hw ; I' = invRec hw'
      wG = wfTm hw
      lC = snd (lamInj (RecInv.eF I)) ; lC' = snd (lamInj (RecInv.eF I'))
      hC = transport (IsType (extend G Nat)) (Eq-sym lC) (RecInv.hC I)
      hC' = transport (IsType (extend G Nat)) (Eq-sym lC') (RecInv.hC I')
      hz = transport (\ X -> HasType G _ (subst1 X Zero)) (Eq-sym lC) (RecInv.hz I)
      hz' = transport (\ X -> HasType G _ (subst1 X Zero)) (Eq-sym lC') (RecInv.hz I')
      hs = transport (\ X -> HasType G _ (RecStep X)) (Eq-sym lC) (RecInv.hs I)
      hs' = transport (\ X -> HasType G _ (RecStep X)) (Eq-sym lC') (RecInv.hs I')
      Vv = valRec {N = Nat} {z = z} {s = s} {k = k} {C = C0} nk dw ; Vv' = valRec {N = Nat} {z = z'} {s = s'} {k = k'} {C = C0'} nk' dw'
      ee = trecI (eqE (VRec.ev Vv) (VRec.ev Vv') e)
      eC = E-lam (etanf-val (snd (VRec.dc Vv))) (etanf-val (snd (VRec.dc Vv'))) (fst ee)
      xc = VRec.xc Vv ; xz = VRec.xz Vv ; xs = VRec.xs Vv ; xk = VRec.xk Vv
      yc = VRec.xc Vv' ; yz = VRec.xz Vv' ; ys = VRec.xs Vv' ; yk = VRec.xk Vv'
      bcp = tr<= (sumL lp (VRec.ev Vv) (VRec.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (VRec.ev Vv) (VRec.ev Vv')) bs)
      -- the four parts of  lp/sz (trec c z s k) = c + (z + (s + k))
      p1 : (a b c d : Num) -> a <= (a ⊕ (b ⊕ (c ⊕ d)))
      p1 a b c d = <=+l a _
      p2 : (a b c d : Num) -> b <= (a ⊕ (b ⊕ (c ⊕ d)))
      p2 a b c d = <=-trans (<=+l b _) (<=+r a _)
      p3 : (a b c d : Num) -> c <= (a ⊕ (b ⊕ (c ⊕ d)))
      p3 a b c d = <=-trans (<=+l c d) (<=-trans (<=+r b _) (<=+r a _))
      p4 : (a b c d : Num) -> d <= (a ⊕ (b ⊕ (c ⊕ d)))
      p4 a b c d = <=-trans (<=+r c d) (<=-trans (<=+r b _) (<=+r a _))
      RC = compTy cb sb hC hC' (VRec.dc Vv) (VRec.dc Vv') eC
             (ar-sub (<=-suc' (p1 (lp xc) (lp xz) (lp xs) (lp xk))) (<=-suc' (p1 (lp yc) (lp yz) (lp ys) (lp yk))) bcp)
             (ar-sub (<=-suc'' (p1 (suc (sz xc)) (sz xz) (sz xs) (sz xk)))
                     (<=-suc (<=-suc'' (p1 (suc (sz yc)) (sz yz) (sz ys) (sz yk)))) bsp)
      qC = algsound-ty hC hC' RC
      Rz = comp cb sb hz (ty-conv hz' (s1TE wG (ty-Zero wG) (tyeq-sym qC))) (VRec.dz Vv) (VRec.dz Vv') (fst (snd ee))
             (ar-sub (p2 (suc (lp xc)) (lp xz) (lp xs) (lp xk)) (p2 (suc (lp yc)) (lp yz) (lp ys) (lp yk)) bcp)
             (ar-sub (p2 (suc (sz xc)) (sz xz) (sz xs) (sz xk)) (<=-suc (p2 (suc (sz yc)) (sz yz) (sz ys) (sz yk))) bsp)
      Rs = comp cb sb hs (ty-conv hs' (stepEq wG hC' hC (tyeq-sym qC))) (VRec.ds Vv) (VRec.ds Vv') (fst (snd (snd ee)))
             (ar-sub (p3 (suc (lp xc)) (lp xz) (lp xs) (lp xk)) (p3 (suc (lp yc)) (lp yz) (lp ys) (lp yk)) bcp)
             (ar-sub (p3 (suc (sz xc)) (sz xz) (sz xs) (sz xk)) (<=-suc (p3 (suc (sz yc)) (sz yz) (sz ys) (sz yk))) bsp)
      Rk = compNe cb sb nk nk' (RecInv.hk I) (RecInv.hk I') (VRec.dk Vv) (VRec.dk Vv') (snd (snd (snd ee)))
             (ar-sub (p4 (suc (lp xc)) (lp xz) (lp xs) (lp xk)) (p4 (suc (lp yc)) (lp yz) (lp ys) (lp yk)) bcp)
             (ar-sub (p4 (suc (sz xc)) (sz xz) (sz xs) (sz xk)) (<=-suc (p4 (suc (sz yc)) (sz yz) (sz ys) (sz yk))) bsp)

  ----------------------------------------------------------------------
  -- types
  ----------------------------------------------------------------------

  compTy : (cb sb : Num) {n : Num} {G : Ctx n} {A A' : Expr n} {va vb : Tm} ->
    IsType G A -> IsType G A' -> den A idE ⇓ va -> den A' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgEq A A'
  compTy cb sb (isty-el h) (isty-el h') d d' e bc bs = comp cb sb h h' d d' e bc bs
  compTy cb sb iA@(isty-el h) iA'@(isty-V w) d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs
  compTy cb sb iA@(isty-el h) iA'@(isty-Pi a b) d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs
  compTy cb sb iA@(isty-el h) iA'@(isty-Sigma a b) d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs
  compTy cb sb iA@(isty-V w) iA' d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs
  compTy cb sb iA@(isty-Pi a b) iA' d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs
  compTy cb sb iA@(isty-Sigma a b) iA' d d' e bc bs = compTyG cb sb iA iA' d d' e bc bs

  compTyG : (cb sb : Num) {n : Num} {G : Ctx n} {A A' : Expr n} {va vb : Tm} ->
    IsType G A -> IsType G A' -> den A idE ⇓ va -> den A' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgEq A A'
  compTyG cb sb {A = A} {A'} iA iA' d d' e bc bs =
    alg (WhnfRes.rs W) (WhnfRes.rs W')
      (compTyW cb sb (snd (pTE (tyRed iA (WhnfRes.rs W)))) (snd (pTE (tyRed iA' (WhnfRes.rs W'))))
         (WhnfRes.sh W) (WhnfRes.sh W') (WhnfRes.dv W) (WhnfRes.dv W') e bc bs)
    where
      W = whnfOf A d
      W' = whnfOf A' d'

  tyPiCase : (cb sb : Num) {n : Num} {G : Ctx n} {A F A' F' : Expr n} {va vb : Tm} ->
    IsType G (Pi A F) -> IsType G (Pi A' F') -> den (Pi A F) idE ⇓ va -> den (Pi A' F') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Pi A F) (Pi A' F')
  tyPiCase cb zero {va = va} {vb = vb} iw iw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  tyPiCase cb (suc sb) {A = A} {F} {A'} {F'} iw iw' dw dw' e bc bs =
    transport2 (\ X Y -> AlgW (Pi A X) (Pi A' Y)) (Eq-sym (TyPiF.eF P)) (Eq-sym (TyPiF.eF P')) (w-pi RA RB)
    where
      P = tyPiF iw ; P' = tyPiF iw'
      Vv = valPi {A = A} {F = F} dw ; Vv' = valPi {A = A'} {F = F'} dw'
      x = V2.x Vv ; f = V2.y Vv ; y = V2.x Vv' ; g = V2.y Vv'
      L = valLam {A = A} {b = TyPiF.B P} (transport (\ X -> den X idE ⇓ f) (TyPiF.eF P) (V2.dy Vv))
      L' = valLam {A = A'} {b = TyPiF.B P'} (transport (\ X -> den X idE ⇓ g) (TyPiF.eF P') (V2.dy Vv'))
      ee = tpiI (eqE (V2.ev Vv) (V2.ev Vv') e)
      eB = E-lam (etanf-val (snd (VLam.dx L))) (etanf-val (snd (VLam.dx L'))) (eqE (VLam.ev L) (VLam.ev L') (snd ee))
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      RA = compTy cb sb (TyPiF.iA P) (TyPiF.iA P') (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp f)) (<=+l (lp y) (lp g)) bcp)
             (ar-sub (<=+l (sz x) (sz f)) (<=-suc (<=+l (sz y) (sz g))) bsp)
      qA = algsound-ty (TyPiF.iA P) (TyPiF.iA P') RA
      iB'A = ccTy (TyPiF.iA P) qA (TyPiF.iB P')
      RB = compTy cb sb (TyPiF.iB P) iB'A (VLam.dx L) (VLam.dx L') eB
             (ar-sub (<=-trans (lpBody (VLam.ev L)) (<=+r (lp x) (lp f))) (<=-trans (lpBody (VLam.ev L')) (<=+r (lp y) (lp g))) bcp)
             (ar-sub (<=-trans (szBody (VLam.ev L)) (<=+r (sz x) (sz f)))
                     (<=-suc (<=-trans (szBody (VLam.ev L')) (<=+r (sz y) (sz g)))) bsp)

  tySigCase : (cb sb : Num) {n : Num} {G : Ctx n} {A F A' F' : Expr n} {va vb : Tm} ->
    IsType G (Sigma A F) -> IsType G (Sigma A' F') -> den (Sigma A F) idE ⇓ va -> den (Sigma A' F') idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW (Sigma A F) (Sigma A' F')
  tySigCase cb zero {va = va} {vb = vb} iw iw' dw dw' e bc bs = Empty-elim (noSz va vb bs)
  tySigCase cb (suc sb) {A = A} {F} {A'} {F'} iw iw' dw dw' e bc bs =
    transport2 (\ X Y -> AlgW (Sigma A X) (Sigma A' Y)) (Eq-sym (TyPiF.eF P)) (Eq-sym (TyPiF.eF P')) (w-sigma RA RB)
    where
      P = tySigF iw ; P' = tySigF iw'
      Vv = valSig {A = A} {F = F} dw ; Vv' = valSig {A = A'} {F = F'} dw'
      x = V2.x Vv ; f = V2.y Vv ; y = V2.x Vv' ; g = V2.y Vv'
      L = valLam {A = A} {b = TyPiF.B P} (transport (\ X -> den X idE ⇓ f) (TyPiF.eF P) (V2.dy Vv))
      L' = valLam {A = A'} {b = TyPiF.B P'} (transport (\ X -> den X idE ⇓ g) (TyPiF.eF P') (V2.dy Vv'))
      ee = tsigI (eqE (V2.ev Vv) (V2.ev Vv') e)
      eB = E-lam (etanf-val (snd (VLam.dx L))) (etanf-val (snd (VLam.dx L'))) (eqE (VLam.ev L) (VLam.ev L') (snd ee))
      bcp = tr<= (sumL lp (V2.ev Vv) (V2.ev Vv')) bc
      bsp = pred<= (tr<= (sumL sz (V2.ev Vv) (V2.ev Vv')) bs)
      RA = compTy cb sb (TyPiF.iA P) (TyPiF.iA P') (V2.dx Vv) (V2.dx Vv') (fst ee)
             (ar-sub (<=+l (lp x) (lp f)) (<=+l (lp y) (lp g)) bcp)
             (ar-sub (<=+l (sz x) (sz f)) (<=-suc (<=+l (sz y) (sz g))) bsp)
      qA = algsound-ty (TyPiF.iA P) (TyPiF.iA P') RA
      iB'A = ccTy (TyPiF.iA P) qA (TyPiF.iB P')
      RB = compTy cb sb (TyPiF.iB P) iB'A (VLam.dx L) (VLam.dx L') eB
             (ar-sub (<=-trans (lpBody (VLam.ev L)) (<=+r (lp x) (lp f))) (<=-trans (lpBody (VLam.ev L')) (<=+r (lp y) (lp g))) bcp)
             (ar-sub (<=-trans (szBody (VLam.ev L)) (<=+r (sz x) (sz f)))
                     (<=-suc (<=-trans (szBody (VLam.ev L')) (<=+r (sz y) (sz g)))) bsp)

  compW : (cb sb : Num) {n : Num} {G : Ctx n} {w w' C : Expr n} {va vb : Tm} -> SynSh w -> SynSh w' ->
    HasType G w C -> HasType G w' C -> den w idE ⇓ va -> den w' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW w w'
  compW cb sb sh-lam sh-lam hw hw' dw dw' e bc bs = caseLL cb sb hw hw' dw dw' e bc bs
  compW cb sb sh-lam (sh-ne n') hw hw' dw dw' e bc bs = caseLN cb sb n' hw hw' dw dw' e bc bs
  compW cb sb (sh-ne n) sh-lam hw hw' dw dw' e bc bs = caseNL cb sb n hw hw' dw dw' e bc bs
  compW cb sb sh-pair sh-pair hw hw' dw dw' e bc bs = casePP cb sb hw hw' dw dw' e bc bs
  compW cb sb sh-pair (sh-ne n') hw hw' dw dw' e bc bs = casePN cb sb n' hw hw' dw dw' e bc bs
  compW cb sb (sh-ne n) sh-pair hw hw' dw dw' e bc bs = caseNP cb sb n hw hw' dw dw' e bc bs
  compW cb sb sh-lam sh-pair hw hw' dw dw' e bc bs = Empty-elim (Pi-Sig (tyeq-trans (tyeq-sym (LamInv.eq (invLam hw))) (PairInv.eq (invPair hw'))))
  compW cb sb sh-pair sh-lam hw hw' dw dw' e bc bs = Empty-elim (Pi-Sig (tyeq-trans (tyeq-sym (LamInv.eq (invLam hw'))) (PairInv.eq (invPair hw))))
  compW cb sb sh-pi sh-pi hw hw' dw dw' e bc bs = casePi cb sb hw hw' dw dw' e bc bs
  compW cb sb sh-sig sh-sig hw hw' dw dw' e bc bs = caseSig cb sb hw hw' dw dw' e bc bs
  compW cb sb sh-nat sh-nat hw hw' dw dw' e bc bs = w-nat
  compW cb sb sh-ze sh-ze hw hw' dw dw' e bc bs = w-zero
  compW cb sb sh-V sh-V hw hw' dw dw' e bc bs = w-V
  compW cb sb sh-sc sh-sc hw hw' dw dw' e bc bs = caseSc cb sb hw hw' dw dw' e bc bs
  compW cb sb sh-U sh-U hw hw' dw dw' e bc bs = caseU cb sb hw hw' dw dw' e bc bs
  compW cb sb (sh-ne n) (sh-ne n') hw hw' dw dw' e bc bs = w-ne (compNe cb sb n n' hw hw' dw dw' e bc bs)
  compW cb sb sh1@(sh-ne _) sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@(sh-ne _) sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-lam sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-lam sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pair sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
  compW cb sb sh1@sh-pi sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-pi sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sig sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-nat sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-ze sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-sc sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-V sh2@sh-U hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@(sh-ne _) hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-lam hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-pair hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (_ , ()) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-pi hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-sig hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-nat hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-ze hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-sc hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compW cb sb sh1@sh-U sh2@sh-V hw hw' dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))

  compTyW : (cb sb : Num) {n : Num} {G : Ctx n} {w w' : Expr n} {va vb : Tm} -> IsType G w -> IsType G w' ->
    SynSh w -> SynSh w' -> den w idE ⇓ va -> den w' idE ⇓ vb ->
    Eq (etanf va) (etanf vb) -> (lp va ⊕ lp vb) <= cb -> (sz va ⊕ sz vb) <= sb -> AlgW w w'
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@(sh-ne N2) dw dw' e bc bs = compW cb sb sh1 sh2 (elNe N1 iw) (elNe N2 iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-nat dw dw' e bc bs = compW cb sb sh1 sh2 (elNe N1 iw) (elNat iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-ze dw dw' e bc bs = compW cb sb sh1 sh2 (elNe N1 iw) (elZe iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-sc dw dw' e bc bs = compW cb sb sh1 sh2 (elNe N1 iw) (elSc iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@(sh-ne N1) sh2@sh-U dw dw' e bc bs = compW cb sb sh1 sh2 (elNe N1 iw) (elU iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-lam sh2@(sh-ne N2) dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-pair dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-pi dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-sig dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-nat dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-ze dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-sc dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-V dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-lam sh2@sh-U dw dw' e bc bs = Empty-elim (noLamTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@(sh-ne N2) dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-pi dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-sig dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-nat dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-ze dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-sc dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-V dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pair sh2@sh-U dw dw' e bc bs = Empty-elim (noPairTy iw)
  compTyW cb sb iw iw' sh1@sh-pi sh2@(sh-ne N2) dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-pi dw dw' e bc bs = tyPiCase cb sb iw iw' dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-nat dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-ze dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-sc dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-pi sh2@sh-U dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@(sh-ne N2) dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-sig dw dw' e bc bs = tySigCase cb sb iw iw' dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-nat dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-ze dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-sc dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sig sh2@sh-U dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-nat sh2@(sh-ne N2) dw dw' e bc bs = compW cb sb sh1 sh2 (elNat iw) (elNe N2 iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-nat dw dw' e bc bs = compW cb sb sh1 sh2 (elNat iw) (elNat iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-ze dw dw' e bc bs = compW cb sb sh1 sh2 (elNat iw) (elZe iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-sc dw dw' e bc bs = compW cb sb sh1 sh2 (elNat iw) (elSc iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-nat sh2@sh-U dw dw' e bc bs = compW cb sb sh1 sh2 (elNat iw) (elU iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-ze sh2@(sh-ne N2) dw dw' e bc bs = compW cb sb sh1 sh2 (elZe iw) (elNe N2 iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-nat dw dw' e bc bs = compW cb sb sh1 sh2 (elZe iw) (elNat iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-ze dw dw' e bc bs = compW cb sb sh1 sh2 (elZe iw) (elZe iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-sc dw dw' e bc bs = compW cb sb sh1 sh2 (elZe iw) (elSc iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-ze sh2@sh-U dw dw' e bc bs = compW cb sb sh1 sh2 (elZe iw) (elU iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sc sh2@(sh-ne N2) dw dw' e bc bs = compW cb sb sh1 sh2 (elSc iw) (elNe N2 iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-nat dw dw' e bc bs = compW cb sb sh1 sh2 (elSc iw) (elNat iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-ze dw dw' e bc bs = compW cb sb sh1 sh2 (elSc iw) (elZe iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-sc dw dw' e bc bs = compW cb sb sh1 sh2 (elSc iw) (elSc iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-sc sh2@sh-U dw dw' e bc bs = compW cb sb sh1 sh2 (elSc iw) (elU iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-V sh2@(sh-ne N2) dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-nat dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-ze dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-sc dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-V dw dw' e bc bs = w-V
  compTyW cb sb iw iw' sh1@sh-V sh2@sh-U dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-U sh2@(sh-ne N2) dw dw' e bc bs = compW cb sb sh1 sh2 (elU iw) (elNe N2 iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-lam dw dw' e bc bs = Empty-elim (noLamTy iw')
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-pair dw dw' e bc bs = Empty-elim (noPairTy iw')
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-pi dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-sig dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-nat dw dw' e bc bs = compW cb sb sh1 sh2 (elU iw) (elNat iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-ze dw dw' e bc bs = compW cb sb sh1 sh2 (elU iw) (elZe iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-sc dw dw' e bc bs = compW cb sb sh1 sh2 (elU iw) (elSc iw') dw dw' e bc bs
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-V dw dw' e bc bs = Empty-elim (mismatch sh1 sh2 dw dw' e ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
  compTyW cb sb iw iw' sh1@sh-U sh2@sh-U dw dw' e bc bs = compW cb sb sh1 sh2 (elU iw) (elU iw') dw dw' e bc bs

------------------------------------------------------------------------
-- completeness
------------------------------------------------------------------------

open import MAHLO.Concrete.Rel using (SR ; sr)

complete : {n : Num} {G : Ctx n} {t t' C : Expr n} -> HasType G t C -> HasType G t' C ->
  SR (den t idE) (den t' idE) -> AlgEq t t'
complete ht ht' (sr va vb da db e) = comp (lp va ⊕ lp vb) (sz va ⊕ sz vb) ht ht' da db e (<=-refl _) (<=-refl _)

complete-ty : {n : Num} {G : Ctx n} {A A' : Expr n} -> IsType G A -> IsType G A' ->
  SR (den A idE) (den A' idE) -> AlgEq A A'
complete-ty iA iA' (sr va vb da db e) = compTy (lp va ⊕ lp vb) (sz va ⊕ sz vb) iA iA' da db e (<=-refl _) (<=-refl _)
