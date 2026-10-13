{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Algo/Sound.agda
--
-- Soundness of the conversion algorithm (plan Thm algsound):
--   if G |- t : C, G |- t' : C and the algorithm accepts t ~ t',
--   then G |- t = t' : C.
--
-- Corrected (constructive) proof.  Simultaneous induction on the run,
-- for all types:
--   sEq   R  at an arbitrary type C;
--   sEqV  R  at V;
--   sW, sNe, sTy, sTyW  on the sub-runs.
-- sEq evaluates both sides with evalC.  Each side either evaluates by
-- conversions at C, or a delta step occurs at the top of a term
-- fhat/ghat, whose typing gives  C = U(f,g)  (derivation data, no
-- decision on conversion needed).  In that case sEq calls sEqV on the
-- SAME run: at V every delta step is a conversion, and (R') brings the
-- result back to U(f,g).  sEqV only calls sW on the sub-run, so the
-- induction is lexicographic in (run, "at V" before "at C"): this is
-- the plan's "the subuniverse case is ordered before the other",
-- made structural.
--
-- Neutrals have a principal type up to subsumption (NeRes): every
-- typing of either side is UpTo the principal type.  This uses
-- V /= Pi, V /= Sigma, V /= Nat (Algo/NoConfV) besides InjHyp.
-- The rec motive is compared (under Nat); only lambda-annotations are
-- ignored.
------------------------------------------------------------------------

module MAHLOINJ.Algo.Sound where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf
open import MAHLOINJ.Syntax.CtxConv
open import MAHLOINJ.Syntax.Presup using (pCv ; pTE ; pTm ; opGEq)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Final using (injHyp ; Pi-inj ; Sig-inj ; U-Pi ; U-Sig ; U-Nat)
open import MAHLOINJ.Inversion.Inv injHyp
open import MAHLOINJ.Algo.NoConfV
open import MAHLOINJ.Algo.Alg
open import MAHLOINJ.Algo.Eval
open import MAHLOINJ.Algo.Syn
open import MAHLOINJ.Adq.Syn using (stepEq)

------------------------------------------------------------------------
-- auxiliaries
------------------------------------------------------------------------

-- change of the canonical side of UpTo
upX : {n : Num} {G : Ctx n} {C X X' : Expr n} -> UpTo G C X -> TyEq G X X' -> UpTo G C X'
upX (upEq e) q = upEq (tyeq-trans e q)
upX (upSub f g e1 e2) q = upSub f g e1 (tyeq-trans (tyeq-sym q) e2)

-- from UpTo at a principal type T to a conversion at C
upConvTm : {n : Num} {G : Ctx n} {u u' C T : Expr n} -> UpTo G C T -> ConvTm G u u' T -> ConvTm G u u' C
upConvTm (upEq e) c = conv-conv c (tyeq-sym e)
upConvTm (upSub f g e1 e2) c = conv-conv (conv-sub (conv-conv c e2)) (tyeq-sym e1)

-- a Pi / Sigma / Nat type is only UpTo itself
upPi : {n : Num} {G : Ctx n} {A T : Expr n} {B : Expr (suc n)} -> UpTo G (PiB A B) T -> TyEq G (PiB A B) T
upPi (upEq e) = e
upPi (upSub f g e1 e2) = Empty-elim (V-Pi (tyeq-sym e1))

upSig : {n : Num} {G : Ctx n} {A T : Expr n} {B : Expr (suc n)} -> UpTo G (SigmaB A B) T -> TyEq G (SigmaB A B) T
upSig (upEq e) = e
upSig (upSub f g e1 e2) = Empty-elim (V-Sig (tyeq-sym e1))

upNat : {n : Num} {G : Ctx n} {T : Expr n} -> UpTo G Nat T -> TyEq G Nat T
upNat (upEq e) = e
upNat (upSub f g e1 e2) = Empty-elim (V-Nat (tyeq-sym e1))

-- selectors on abstractions
lamDom : {n : Num} -> Expr n -> Expr n
lamDom (Lam A _) = A
lamDom (Var _) = Nat
lamDom (App _ _) = Nat
lamDom (Pi _ _) = Nat
lamDom (Sigma _ _) = Nat
lamDom (Pair _ _) = Nat
lamDom (Fst _) = Nat
lamDom (Snd _) = Nat
lamDom Nat = Nat
lamDom Zero = Nat
lamDom (Suc _) = Nat
lamDom (Rec _ _ _ _) = Nat
lamDom V = Nat
lamDom (Ucode _ _) = Nat
lamDom (Fhat _ _ _ _) = Nat
lamDom (Ghat _ _ _ _ _) = Nat

lamInj : {n : Num} {A A' : Expr n} {b b' : Expr (suc n)} -> Eq (Lam A b) (Lam A' b') -> Eq A A' * Eq b b'
lamInj e = Eq-cong lamDom e , Eq-cong lamb1 e

-- types that are not V, Pi or Sigma are elements of V
noLamTy : {n : Num} {G : Ctx n} {A : Expr n} {b : Expr (suc n)} -> IsType G (Lam A b) -> Empty
noLamTy (isty-el h) = V-Pi (LamInv.eq (invLam h))

noPairTy : {n : Num} {G : Ctx n} {t u : Expr n} -> IsType G (Pair t u) -> Empty
noPairTy (isty-el h) = V-Sig (PairInv.eq (invPair h))

neEl : {n : Num} {G : Ctx n} {u u' : Expr n} -> AlgNe u u' -> IsType G u -> HasType G u V
neEl ne-var (isty-el h) = h
neEl (ne-app N R) (isty-el h) = h
neEl (ne-fst N) (isty-el h) = h
neEl (ne-snd N) (isty-el h) = h
neEl (ne-rec RC Rz Rs N) (isty-el h) = h

neEl' : {n : Num} {G : Ctx n} {u u' : Expr n} -> AlgNe u u' -> IsType G u' -> HasType G u' V
neEl' ne-var (isty-el h) = h
neEl' (ne-app N R) (isty-el h) = h
neEl' (ne-fst N) (isty-el h) = h
neEl' (ne-snd N) (isty-el h) = h
neEl' (ne-rec RC Rz Rs N) (isty-el h) = h

-- a Pi / Sigma shaped type: its components
record TyPi {n : Num} (G : Ctx n) (A A0 : Expr n) (B : Expr (suc n)) : Set where
  constructor typi
  field
    eA : Eq A0 A
    iA : IsType G A
    iB : IsType (extend G A) B

tyPi : {n : Num} {G : Ctx n} {A A0 : Expr n} {B : Expr (suc n)} -> IsType G (Pi A (Lam A0 B)) -> TyPi G A A0 B
tyPi (isty-el h) = typi (fst li) (elTy un hA) (transport (\ X -> IsType _ X) (Eq-sym (snd li)) (elTy (renUniv wkRen un) hB))
  where
    open PiInv (invPi h)
    li = lamInj eF
tyPi (isty-Pi iA iB) = typi refl iA iB

tySig : {n : Num} {G : Ctx n} {A A0 : Expr n} {B : Expr (suc n)} -> IsType G (Sigma A (Lam A0 B)) -> TyPi G A A0 B
tySig (isty-el h) = typi (fst li) (elTy un hA) (transport (\ X -> IsType _ X) (Eq-sym (snd li)) (elTy (renUniv wkRen un) hB))
  where
    open PiInv (invSigma h)
    li = lamInj eF
tySig (isty-Sigma iA iB) = typi refl iA iB

-- the principal type of a pair of related neutrals
record NeRes {n : Num} (G : Ctx n) (u u' : Expr n) : Set where
  constructor neres
  field
    T   : Expr n
    cv  : ConvTm G u u' T
    upL : {C : Expr n} -> HasType G u C -> UpTo G C T
    upR : {C : Expr n} -> HasType G u' C -> UpTo G C T

------------------------------------------------------------------------
-- soundness
------------------------------------------------------------------------

mutual

  sEq : {n : Num} {G : Ctx n} {t t' C : Expr n} -> AlgEq t t' -> HasType G t C -> HasType G t' C -> ConvTm G t t' C
  sEq {G = G} {t} {t'} {C} (alg rt rt' W) ht ht' = go (evalC ht rt) (evalC ht' rt')
    where
      viaU : UEv G C -> ConvTm G t t' C
      viaU (f , (g , e)) =
        conv-conv (conv-R' (ty-conv ht e) (ty-conv ht' e) (sEqV rt rt' W (ty-sub (ty-conv ht e)) (ty-sub (ty-conv ht' e))))
          (tyeq-sym e)
      go : _ -> _ -> ConvTm G t t' C
      go (inl c) (inl c') = conv-trans c (conv-trans (sW W (snd (pCv c)) (snd (pCv c'))) (conv-sym c'))
      go (inr u) _ = viaU u
      go (inl c) (inr u) = viaU u

  sEqV : {n : Num} {G : Ctx n} {t t' w w' : Expr n} -> HRs t w -> HRs t' w' -> AlgW w w' ->
    HasType G t V -> HasType G t' V -> ConvTm G t t' V
  sEqV rt rt' W ht ht' =
    let c = evalV ht rt ; c' = evalV ht' rt'
    in conv-trans c (conv-trans (sW W (snd (pCv c)) (snd (pCv c'))) (conv-sym c'))

  sW : {n : Num} {G : Ctx n} {w w' C : Expr n} -> AlgW w w' -> HasType G w C -> HasType G w' C -> ConvTm G w w' C
  sW (w-lam R) hw hw' =
    conv-conv (lamConvB hA (LamInv.hA I') qA hB ht hb'A (sEq R ht hb'A)) (tyeq-sym eq)
    where
      open LamInv (invLam hw)
      I' = invLam hw'
      pj = Pi-inj (tyeq-trans (tyeq-sym eq) (LamInv.eq I'))
      qA = fst pj
      hb'A = ty-conv (ccTm hA qA (LamInv.ht I')) (tyeq-sym (snd pj))
  sW (w-lamL R) hw hw' =
    conv-conv (etaLam hA hB ht htP (sEq R ht (appWk hA hB htP))) (tyeq-sym eq)
    where
      open LamInv (invLam hw)
      htP = ty-conv hw' eq
  sW (w-lamR R) hw hw' =
    conv-conv (conv-sym (etaLam hA hB ht htP (conv-sym (sEq R (appWk hA hB htP) ht)))) (tyeq-sym eq)
    where
      open LamInv (invLam hw')
      htP = ty-conv hw eq
  sW {G = G} (w-pair {t} {u} {t'} {u'} Rt Ru) hw hw' =
    conv-conv (conv-pairext hA hB hP hP' cF cS) (tyeq-sym eq)
    where
      open PairInv (invPair hw)
      I' = invPair hw'
      wG = wfTm hw
      sj = Sig-inj (tyeq-trans (tyeq-sym eq) (PairInv.eq I'))
      hP = ty-conv hw eq
      hP' = ty-conv hw' eq
      ht'A = ty-conv (PairInv.ht I') (tyeq-sym (fst sj))
      hu'B = ty-conv (PairInv.hu I') (s1TE wG ht'A (tyeq-sym (snd sj)))
      ct = sEq Rt ht ht'A
      tq = s1fTy wG hA ht ht'A ct hB
      cu = sEq Ru hu (ty-conv hu'B (tyeq-sym tq))
      fb = conv-fst-beta hA hB ht hu
      fb' = conv-fst-beta hA hB ht'A hu'B
      cF = conv-trans fb (conv-trans ct (conv-sym fb'))
      sb = conv-snd-beta hA hB ht hu
      sb' = conv-conv (conv-snd-beta hA hB ht'A hu'B) (tyeq-sym tq)
      cS = conv-conv (conv-trans sb (conv-trans cu (conv-sym sb')))
             (tyeq-sym (s1fTy wG hA (ty-Fst hA hB hP) ht fb hB))
  sW {G = G} (w-pairL {t} {u} {t'} R1 R2) hw hw' =
    conv-conv (conv-pairext hA hB hP hP' cF cS) (tyeq-sym eq)
    where
      open PairInv (invPair hw)
      wG = wfTm hw
      hP = ty-conv hw eq
      hP' = ty-conv hw' eq
      hF' = ty-Fst hA hB hP'
      ct = sEq R1 ht hF'
      q = tyeq-sym (s1fTy wG hA ht hF' ct hB)
      cu = sEq R2 hu (ty-conv (ty-Snd hA hB hP') q)
      fb = conv-fst-beta hA hB ht hu
      cF = conv-trans fb ct
      cS = conv-conv (conv-trans (conv-snd-beta hA hB ht hu) cu)
             (tyeq-sym (s1fTy wG hA (ty-Fst hA hB hP) ht fb hB))
  sW {G = G} (w-pairR {t} {t'} {u'} R1 R2) hw hw' =
    conv-conv (conv-pairext hA hB hP hP' cF cS) (tyeq-sym eq)
    where
      open PairInv (invPair hw')
      wG = wfTm hw
      hP = ty-conv hw eq
      hP' = ty-conv hw' eq
      hF = ty-Fst hA hB hP
      ct = sEq R1 hF ht
      q = s1fTy wG hA hF ht ct hB
      cu = sEq R2 (ty-Snd hA hB hP) (ty-conv hu (tyeq-sym q))
      fb' = conv-fst-beta hA hB ht hu
      cF = conv-trans ct (conv-sym fb')
      cS = conv-trans cu (conv-sym (conv-conv (conv-snd-beta hA hB ht hu) (tyeq-sym q)))
  sW {G = G} (w-pi {A} {A'} {A0} {A0'} {B} {B'} RA RB) hw hw' =
    conv-conv (transport2 (\ X Y -> ConvTm G (Pi A (Lam X B)) (Pi A' (Lam Y B')) (PiInv.u P))
                 (Eq-sym (fst li)) (Eq-sym (fst li')) (conv-Pi un hA hB hB' cA cB))
      (tyeq-sym (PiInv.eq P))
    where
      P = invPi hw
      P' = invPi hw'
      li = lamInj (PiInv.eF P)
      li' = lamInj (PiInv.eF P')
      un = PiInv.un P
      hA = PiInv.hA P
      iA = elTy un hA
      quu = tyeq-trans (tyeq-sym (PiInv.eq P')) (PiInv.eq P)
      cA = sEq RA hA (ty-conv (PiInv.hA P') quu)
      qA = cvTE un cA
      hB = transport (\ X -> HasType (extend G A) X (wkExpr (PiInv.u P))) (Eq-sym (snd li)) (PiInv.hB P)
      hB' = ty-conv (ccTm iA qA (transport (\ X -> HasType (extend G A') X (wkExpr (PiInv.u P'))) (Eq-sym (snd li')) (PiInv.hB P')))
              (wkTE iA quu)
      cB = sEq RB hB hB'
  sW {G = G} (w-sigma {A} {A'} {A0} {A0'} {B} {B'} RA RB) hw hw' =
    conv-conv (transport2 (\ X Y -> ConvTm G (Sigma A (Lam X B)) (Sigma A' (Lam Y B')) (PiInv.u P))
                 (Eq-sym (fst li)) (Eq-sym (fst li')) (conv-Sigma un hA hB hB' cA cB))
      (tyeq-sym (PiInv.eq P))
    where
      P = invSigma hw
      P' = invSigma hw'
      li = lamInj (PiInv.eF P)
      li' = lamInj (PiInv.eF P')
      un = PiInv.un P
      hA = PiInv.hA P
      iA = elTy un hA
      quu = tyeq-trans (tyeq-sym (PiInv.eq P')) (PiInv.eq P)
      cA = sEq RA hA (ty-conv (PiInv.hA P') quu)
      qA = cvTE un cA
      hB = transport (\ X -> HasType (extend G A) X (wkExpr (PiInv.u P))) (Eq-sym (snd li)) (PiInv.hB P)
      hB' = ty-conv (ccTm iA qA (transport (\ X -> HasType (extend G A') X (wkExpr (PiInv.u P'))) (Eq-sym (snd li')) (PiInv.hB P')))
              (wkTE iA quu)
      cB = sEq RB hB hB'
  sW w-nat hw hw' = conv-refl hw
  sW w-zero hw hw' = conv-refl hw
  sW w-V hw hw' = conv-refl hw
  sW (w-suc R) hw hw' = conv-conv (conv-Suc (sEq R (fst (invSuc hw)) (fst (invSuc hw')))) (tyeq-sym (snd (invSuc hw)))
  sW (w-ucode Rf Rg) hw hw' =
    conv-conv (conv-Ucode hf hg cf (sEq Rg hg (ty-conv hg' (tyeq-sym (opGEq (wfTm hf) hf hf' cf))))) (tyeq-sym e)
    where
      hf = fst (invUcode hw) ; hg = fst (snd (invUcode hw)) ; e = snd (snd (invUcode hw))
      hf' = fst (invUcode hw') ; hg' = fst (snd (invUcode hw'))
      cf = sEq Rf hf hf'
  sW (w-ne N) hw hw' = upConvTm (NeRes.upL r hw) (NeRes.cv r)
    where r = sNe N hw hw'

  sNe : {n : Num} {G : Ctx n} {u u' C C' : Expr n} -> AlgNe u u' -> HasType G u C -> HasType G u' C' -> NeRes G u u'
  sNe {G = G} (ne-var {i}) hu hu' = neres (lookup G i) (conv-refl (ty-var (wfTm hu))) invVar invVar
  sNe {G = G} (ne-app {u} {u'} {v} {v'} N R) hu hu' =
    neres (subst1 B v) (conv-App hA hB cu cv) upL' upR'
    where
      open AppInv (invApp hu)
      I' = invApp hu'
      wG = wfTm hu
      r = sNe N ht (AppInv.ht I')
      e1 = upPi (NeRes.upL r ht)
      e1' = upPi (NeRes.upR r (AppInv.ht I'))
      pj = Pi-inj (tyeq-trans e1' (tyeq-sym e1))
      cv = sEq R ha (ty-conv (AppInv.ha I') (fst pj))
      cu = conv-conv (NeRes.cv r) (tyeq-sym e1)
      upL' : {C : Expr _} -> HasType G (App u v) C -> UpTo G C (subst1 B v)
      upL' h = upX (AppInv.up J) (s1TE wG (AppInv.ha J) (snd pjJ))
        where
          J = invApp h
          pjJ = Pi-inj (tyeq-trans (upPi (NeRes.upL r (AppInv.ht J))) (tyeq-sym e1))
      upR' : {C : Expr _} -> HasType G (App u' v') C -> UpTo G C (subst1 B v)
      upR' h = upX (AppInv.up J) (tyeq-trans (s1TE wG (AppInv.ha J) (snd pjJ))
                 (tyeq-sym (s1fTy wG hA ha (ty-conv (AppInv.ha J) (fst pjJ)) cvJ hB)))
        where
          J = invApp h
          pjJ = Pi-inj (tyeq-trans (upPi (NeRes.upR r (AppInv.ht J))) (tyeq-sym e1))
          cvJ = conv-trans cv (conv-refl (snd (pCv cv)))
  sNe {G = G} (ne-fst {u} {u'} N) hu hu' =
    neres A (conv-Fst hA hB (conv-conv (NeRes.cv r) (tyeq-sym e1))) upL' upR'
    where
      open FstInv (invFst hu)
      r = sNe N ht (FstInv.ht (invFst hu'))
      e1 = upSig (NeRes.upL r ht)
      upL' : {C : Expr _} -> HasType G (Fst u) C -> UpTo G C A
      upL' h = upX (FstInv.up J) (fst (Sig-inj (tyeq-trans (upSig (NeRes.upL r (FstInv.ht J))) (tyeq-sym e1))))
        where J = invFst h
      upR' : {C : Expr _} -> HasType G (Fst u') C -> UpTo G C A
      upR' h = upX (FstInv.up J) (fst (Sig-inj (tyeq-trans (upSig (NeRes.upR r (FstInv.ht J))) (tyeq-sym e1))))
        where J = invFst h
  sNe {G = G} (ne-snd {u} {u'} N) hu hu' =
    neres (subst1 B (Fst u)) (conv-Snd hA hB cu) upL' upR'
    where
      open SndInv (invSnd hu)
      wG = wfTm hu
      r = sNe N ht (SndInv.ht (invSnd hu'))
      e1 = upSig (NeRes.upL r ht)
      cu = conv-conv (NeRes.cv r) (tyeq-sym e1)
      upL' : {C : Expr _} -> HasType G (Snd u) C -> UpTo G C (subst1 B (Fst u))
      upL' h = upX (SndInv.up J) (s1TE wG (ty-Fst (SndInv.hA J) (SndInv.hB J) (SndInv.ht J)) (snd sj))
        where
          J = invSnd h
          sj = Sig-inj (tyeq-trans (upSig (NeRes.upL r (SndInv.ht J))) (tyeq-sym e1))
      upR' : {C : Expr _} -> HasType G (Snd u') C -> UpTo G C (subst1 B (Fst u))
      upR' h = upX (SndInv.up J)
                 (tyeq-trans (s1TE wG hFJ (snd sj))
                    (tyeq-sym (s1fTy wG hA (ty-Fst hA hB ht) (ty-conv hFJ (fst sj)) (conv-Fst hA hB cu) hB)))
        where
          J = invSnd h
          sj = Sig-inj (tyeq-trans (upSig (NeRes.upR r (SndInv.ht J))) (tyeq-sym e1))
          hFJ = ty-Fst (SndInv.hA J) (SndInv.hB J) (SndInv.ht J)
  sNe {G = G} (ne-rec {N} {N'} {z} {z'} {s} {s'} {k} {k'} {C} {C'} RC Rz Rs Nk) hu hu' =
    neres (subst1 C k)
      (transport2 (\ X Y -> ConvTm G (Rec (Lam X C) z s k) (Rec (Lam Y C') z' s' k') (subst1 C k))
         (Eq-sym (fst li)) (Eq-sym (fst li')) (conv-Rec hC1 hC1' qC cz cs ck))
      upL' upR'
    where
      I = invRec hu
      I' = invRec hu'
      wG = wfTm hu
      li = lamInj (RecInv.eF I)
      li' = lamInj (RecInv.eF I')
      hC1 = transport (IsType (extend G Nat)) (Eq-sym (snd li)) (RecInv.hC I)
      hC1' = transport (IsType (extend G Nat)) (Eq-sym (snd li')) (RecInv.hC I')
      hz1 = transport (\ X -> HasType G z (subst1 X Zero)) (Eq-sym (snd li)) (RecInv.hz I)
      hz1' = transport (\ X -> HasType G z' (subst1 X Zero)) (Eq-sym (snd li')) (RecInv.hz I')
      hs1 = transport (\ X -> HasType G s (RecStep X)) (Eq-sym (snd li)) (RecInv.hs I)
      hs1' = transport (\ X -> HasType G s' (RecStep X)) (Eq-sym (snd li')) (RecInv.hs I')
      hk = RecInv.hk I
      hk' = RecInv.hk I'
      r = sNe Nk hk hk'
      ck = conv-conv (NeRes.cv r) (tyeq-sym (upNat (NeRes.upL r hk)))
      qC = sTy RC hC1 hC1'
      cz = sEq Rz hz1 (ty-conv hz1' (s1TE wG (ty-Zero wG) (tyeq-sym qC)))
      cs = sEq Rs hs1 (ty-conv hs1' (stepEq wG hC1' hC1 (tyeq-sym qC)))
      upL' : {D : Expr _} -> HasType G (Rec (Lam N C) z s k) D -> UpTo G D (subst1 C k)
      upL' h = transport (\ X -> UpTo G _ (subst1 X k)) (Eq-sym (snd (lamInj (RecInv.eF J)))) (RecInv.up J)
        where J = invRec h
      upR' : {D : Expr _} -> HasType G (Rec (Lam N' C') z' s' k') D -> UpTo G D (subst1 C k)
      upR' h = upX (transport (\ X -> UpTo G _ (subst1 X k')) (Eq-sym (snd (lamInj (RecInv.eF J)))) (RecInv.up J))
                 (tyeq-trans (s1TE wG hk' (tyeq-sym qC)) (tyeq-sym (s1fTy wG (NatTy wG) hk hk' ck hC1)))
        where J = invRec h

  sTy : {n : Num} {G : Ctx n} {A A' : Expr n} -> AlgEq A A' -> IsType G A -> IsType G A' -> TyEq G A A'
  sTy (alg r r' W) iA iA' =
    tyeq-trans q (tyeq-trans (sTyW W (snd (pTE q)) (snd (pTE q'))) (tyeq-sym q'))
    where
      q = tyRed iA r
      q' = tyRed iA' r'

  sTyW : {n : Num} {G : Ctx n} {w w' : Expr n} -> AlgW w w' -> IsType G w -> IsType G w' -> TyEq G w w'
  sTyW (w-lam R) iw iw' = Empty-elim (noLamTy iw)
  sTyW (w-lamL R) iw iw' = Empty-elim (noLamTy iw)
  sTyW (w-lamR R) iw iw' = Empty-elim (noLamTy iw')
  sTyW (w-pair R1 R2) iw iw' = Empty-elim (noPairTy iw)
  sTyW (w-pairL R1 R2) iw iw' = Empty-elim (noPairTy iw)
  sTyW (w-pairR R1 R2) iw iw' = Empty-elim (noPairTy iw')
  sTyW {G = G} (w-pi {A} {A'} {A0} {A0'} {B} {B'} RA RB) iw iw' =
    transport2 (\ X Y -> TyEq G (Pi A (Lam X B)) (Pi A' (Lam Y B'))) (Eq-sym (TyPi.eA P)) (Eq-sym (TyPi.eA P'))
      (tyeq-Pi (TyPi.iA P) (TyPi.iB P) iB'A qA (sTy RB (TyPi.iB P) iB'A))
    where
      P = tyPi iw
      P' = tyPi iw'
      qA = sTy RA (TyPi.iA P) (TyPi.iA P')
      iB'A = ccTy (TyPi.iA P) qA (TyPi.iB P')
  sTyW {G = G} (w-sigma {A} {A'} {A0} {A0'} {B} {B'} RA RB) iw iw' =
    transport2 (\ X Y -> TyEq G (Sigma A (Lam X B)) (Sigma A' (Lam Y B'))) (Eq-sym (TyPi.eA P)) (Eq-sym (TyPi.eA P'))
      (tyeq-Sigma (TyPi.iA P) (TyPi.iB P) iB'A qA (sTy RB (TyPi.iB P) iB'A))
    where
      P = tySig iw
      P' = tySig iw'
      qA = sTy RA (TyPi.iA P) (TyPi.iA P')
      iB'A = ccTy (TyPi.iA P) qA (TyPi.iB P')
  sTyW w-nat iw iw' = tyeq-refl iw
  sTyW w-V iw iw' = tyeq-refl iw
  sTyW w-zero (isty-el h) (isty-el h') = tyeq-el (conv-refl h)
  sTyW (w-suc R) (isty-el h) (isty-el h') = tyeq-el (sW (w-suc R) h h')
  sTyW (w-ucode Rf Rg) (isty-el h) (isty-el h') = tyeq-el (sW (w-ucode Rf Rg) h h')
  sTyW (w-ne N) iw iw' = tyeq-el (sW (w-ne N) (neEl N iw) (neEl' N iw'))
