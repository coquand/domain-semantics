{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/UniqLemmas.agda
--
-- The per-former steps of uniqueness, as non-recursive combinators
-- taking the induction hypotheses (Coh of the immediate subterms) as
-- arguments; MAHLORT/Uniq does the recursion.  Relative to TInj.
--
-- Codes are handled uniformly by a KIND  k : V | U_{f,g}  of the
-- universe they live in.  The image in V,  KIm k t  (= t, resp. T^ t),
-- does not depend on f, g -- T^ is unannotated -- so codes of different
-- subuniverses are compared in V.
------------------------------------------------------------------------

open import MAHLORT.Hyp

module MAHLORT.UniqLemmas (I : TInj) where

open import MAHLO.Basic hiding (Sigma)
import MAHLO.Syntax as R
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.CtxConv
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Ops
open import MAHLORT.Syntax.Presup
open import MAHLORT.TNoConf
open import MAHLORT.Coh
open Extract I public
open TInj I

------------------------------------------------------------------------
-- Injectivity of the Russell constructors (on arbitrary expressions)
------------------------------------------------------------------------

r-var : {n : Num} {i j : Fin n} -> Eq (R.Var i) (R.Var j) -> Eq i j
r-var refl = refl

r-lam : {n : Num} {a c : R.Expr n} {b d : R.Expr (suc n)} -> Eq (R.Lam a b) (R.Lam c d) -> Eq a c * Eq b d
r-lam refl = refl , refl
r-app : {n : Num} {a b c d : R.Expr n} -> Eq (R.App a b) (R.App c d) -> Eq a c * Eq b d
r-app refl = refl , refl
r-pi : {n : Num} {a b c d : R.Expr n} -> Eq (R.Pi a b) (R.Pi c d) -> Eq a c * Eq b d
r-pi refl = refl , refl
r-sig : {n : Num} {a b c d : R.Expr n} -> Eq (R.Sigma a b) (R.Sigma c d) -> Eq a c * Eq b d
r-sig refl = refl , refl
r-pair : {n : Num} {a b c d : R.Expr n} -> Eq (R.Pair a b) (R.Pair c d) -> Eq a c * Eq b d
r-pair refl = refl , refl
r-ucode : {n : Num} {a b c d : R.Expr n} -> Eq (R.Ucode a b) (R.Ucode c d) -> Eq a c * Eq b d
r-ucode refl = refl , refl
r-fst : {n : Num} {a c : R.Expr n} -> Eq (R.Fst a) (R.Fst c) -> Eq a c
r-fst refl = refl
r-snd : {n : Num} {a c : R.Expr n} -> Eq (R.Snd a) (R.Snd c) -> Eq a c
r-snd refl = refl
r-suc : {n : Num} {a c : R.Expr n} -> Eq (R.Suc a) (R.Suc c) -> Eq a c
r-suc refl = refl
r-rec : {n : Num} {a b c d a' b' c' d' : R.Expr n} -> Eq (R.Rec a b c d) (R.Rec a' b' c' d') ->
        Eq a a' * (Eq b b' * (Eq c c' * Eq d d'))
r-rec refl = refl , (refl , (refl , refl))
r-fhat : {n : Num} {a b c d a' b' c' d' : R.Expr n} -> Eq (R.Fhat a b c d) (R.Fhat a' b' c' d') ->
         Eq a a' * (Eq b b' * (Eq c c' * Eq d d'))
r-fhat refl = refl , (refl , (refl , refl))
r-ghat : {n : Num} {a b c d e a' b' c' d' e' : R.Expr n} ->
         Eq (R.Ghat a b c d e) (R.Ghat a' b' c' d' e') ->
         Eq a a' * (Eq b b' * (Eq c c' * (Eq d d' * Eq e e')))
r-ghat refl = refl , (refl , (refl , (refl , refl)))

-- an annotated family  Pi a (Lam a b): the body
r-fam : {n : Num} {a c : R.Expr n} {b d : R.Expr (suc n)} ->
        Eq (R.Pi a (R.Lam a b)) (R.Pi c (R.Lam c d)) -> Eq a c * Eq b d
r-fam e = fst (r-pi e) , snd (r-lam (snd (r-pi e)))
r-famS : {n : Num} {a c : R.Expr n} {b d : R.Expr (suc n)} ->
         Eq (R.Sigma a (R.Lam a b)) (R.Sigma c (R.Lam c d)) -> Eq a c * Eq b d
r-famS e = fst (r-sig e) , snd (r-lam (snd (r-sig e)))

------------------------------------------------------------------------
-- Type heads (the erasures of the non-El types)
------------------------------------------------------------------------

data THead {n : Num} : R.Expr n -> Set where
  thV   : THead R.V
  thU   : {f g : R.Expr n} -> THead (R.Ucode f g)
  thPi  : {A F : R.Expr n} -> THead (R.Pi A F)
  thSig : {A F : R.Expr n} -> THead (R.Sigma A F)
  thNat : THead R.Nat

------------------------------------------------------------------------
-- beta at x0, and FunB under single substitution
------------------------------------------------------------------------

lamBetaX : {n : Num} {G : Ctx n} {D : Expr n} {B s : Expr (suc n)} ->
           IsType G D -> IsType (extend G D) B -> HasType (extend G D) s B ->
           ConvTm (extend G D) (FunB D B (Lam D s)) s B
lamBetaX {G = G} {D} {B} {s} hD hB hs =
  trCv refl (subst1-liftWk-cancel s) (subst1-liftWk-cancel B)
    (conv-beta hX (rTy (liftRen wkRen) rt (wf-extend hX) hB) (rTm (liftRen wkRen) rt (wf-extend hX) hs)
               (ty-var (wf-extend hD)))
  where
    hX = wkTy hD hD
    rt = liftRT {r = wkRen} {A = D} (wkRT {G = G} {D}) hX

private
  liftWk-subst1 : {n : Num} (a : Expr n) (B : Expr (suc n)) ->
    Eq (substExpr (liftSub (subst1Sub a)) (renExpr (liftRen wkRen) B)) B
  liftWk-subst1 a B =
    Eq-trans (subst-ren-gen (liftSub (subst1Sub a)) (liftRen wkRen) idSub e B) (substExpr-id B)
    where
      e : (i : Fin _) -> Eq (liftSub (subst1Sub a) (liftRen wkRen i)) (Var i)
      e fzero = refl
      e (fsuc i) = refl

  AP : {n : Num} -> Expr n -> Expr (suc n) -> Expr n -> Expr n -> Expr n
  AP D B c a = App D (Lam D B) c a

funB-subst1 : {n : Num} (D : Expr n) (B : Expr (suc n)) (c a : Expr n) ->
              Eq (subst1 (FunB D B c) a) (appB D B c a)
funB-subst1 D B c a =
  Eq-trans (Eq-cong (\ z -> App (subst1 (wkExpr D) a) (Lam (subst1 (wkExpr D) a) z) (subst1 (wkExpr c) a) a)
                    (liftWk-subst1 a B))
           (cong3 (\ x y z -> App x (Lam x B) y z) (subst1-wk D a) (subst1-wk c a) refl)

------------------------------------------------------------------------
-- Lam, App, Pair, Fst, Snd
------------------------------------------------------------------------

lamCoh : {n : Num} {G : Ctx n} {A0 A1 : Expr n} {B0 B1 s0 s1 : Expr (suc n)} ->
         IsType G A0 -> IsType (extend G A0) B0 -> HasType (extend G A0) s0 B0 ->
         IsType G A1 -> IsType (extend G A1) B1 -> HasType (extend G A1) s1 B1 ->
         (qA : TyEq G A0 A1) -> Coh (extend G A0) s0 B0 s1 B1 ->
         Coh G (Lam A0 s0) (PiB A0 B0) (Lam A1 s1) (PiB A1 B1)
lamCoh hA0 hB0 hs0 hA1 hB1 hs1 qA cs =
  pi _ _ _ hA0 hB0 hB1' (tyeq-refl (isty-Pi hA0 hB0))
     (tyeq-Pi hA1 hB1 hB1 (tyeq-sym qA) (tyeq-refl hB1))
     (ty-Lam hA0 hB0 hs0) (ty-Lam hA1 hB1 hs1)
     (cohConvR (cohConvL cs (conv-sym (lamBetaX hA0 hB0 hs0)) (tyeq-refl hB0)) (conv-sym beta1)
               (tyeq-refl hB1'))
  where
    hB1' = ccTy hA0 qA hB1
    hs1' = ccTm hA0 qA hs1
    beta1 = conv-trans (funCong hA0 hB1' (tyeq-refl hB1') (conv-sym (conv-Lam hA0 hB1' qA (conv-refl hs1'))))
                       (lamBetaX hA0 hB1' hs1')

appCoh : {n : Num} {G : Ctx n} {A0 A1 c0 c1 a0 a1 : Expr n} {B0 B1 : Expr (suc n)} ->
         IsType G A0 -> IsType (extend G A0) B0 -> HasType G c0 (PiB A0 B0) -> HasType G a0 A0 ->
         IsType G A1 -> IsType (extend G A1) B1 -> HasType G c1 (PiB A1 B1) -> HasType G a1 A1 ->
         Coh G c0 (PiB A0 B0) c1 (PiB A1 B1) -> Coh G a0 A0 a1 A1 ->
         Coh G (appB A0 B0 c0 a0) (subst1 B0 a0) (appB A1 B1 c1 a1) (subst1 B1 a1)
appCoh hA0 hB0 hc0 ha0 hA1 hB1 hc1 ha1 (same q c) ca =
  same (tyeq-trans (s1fTy w hA0 ha0 ha1' ca' hB0) (s1TE w ha1' qB)) (conv-App hA0 hB0 qA qB c ca')
  where
    w = wfTy hA0
    qA = fst (Pi-inj q)
    qB = snd (Pi-inj q)
    ca' = extract ca qA
    ha1' = ty-conv ha1 (tyeq-sym qA)
appCoh hA0 hB0 hc0 ha0 hA1 hB1 hc1 ha1 (univ u0 u1 p0 p1 c) ca =
  Empty-elim (upNoPi p0 (tyeq-refl (isty-Pi hA0 hB0)))
appCoh hA0 hB0 hc0 ha0 hA1 hB1 hc1 ha1 (sigma D0 D1 C0 C1 hD0 hC0 hD1 hC1 q0 q1 h0 h1 c c') ca =
  Empty-elim (tPi-Sig q0)
appCoh {G = G} {A0} {A1} {c0} {c1} {a0} {a1} {B0} {B1} hA0 hB0 hc0 ha0 hA1 hB1 hc1 ha1
       (pi D C0 C1 hD hC0 hC1 q0 q1 h0 h1 inner) ca =
  cohConvR (cohConvL sub left (s1TE w haD qC0B0)) right
           (tyeq-trans (s1fTy w hD haD ha1D cD hC1) (s1TE w ha1D qC1B1))
  where
    w = wfTy hA0
    qA0 = fst (Pi-inj q0)
    qA1 = fst (Pi-inj q1)
    qC0B0 = tyeq-sym (ccTE hD (tyeq-sym qA0) (snd (Pi-inj q0)))
    qC1B1 = tyeq-sym (ccTE hD (tyeq-sym qA1) (snd (Pi-inj q1)))
    ca' = extract ca (tyeq-trans qA0 (tyeq-sym qA1))
    haD = ty-conv ha0 qA0
    ha1D = ty-conv ha1 qA1
    cD = conv-conv ca' qA0
    sub = trCoh (funB-subst1 D C0 c0 a0) refl (funB-subst1 D C1 c1 a0) refl
            (cohSub (subst1Sub a0) (ws1 w haD) w inner)
    left = conv-App hD hC0 (tyeq-sym qA0) qC0B0 (conv-refl (ty-conv hc0 q0)) (conv-refl haD)
    right = conv-App hD hC1 (tyeq-sym qA1) qC1B1 (conv-refl (ty-conv hc1 q1)) cD

pairCoh : {n : Num} {G : Ctx n} {A0 A1 a0 a1 b0 b1 : Expr n} {B0 B1 : Expr (suc n)} ->
          IsType G A0 -> IsType (extend G A0) B0 -> HasType G a0 A0 -> HasType G b0 (subst1 B0 a0) ->
          IsType G A1 -> IsType (extend G A1) B1 -> HasType G a1 A1 -> HasType G b1 (subst1 B1 a1) ->
          Coh G a0 A0 a1 A1 -> Coh G b0 (subst1 B0 a0) b1 (subst1 B1 a1) ->
          Coh G (Pair A0 (Lam A0 B0) a0 b0) (SigmaB A0 B0) (Pair A1 (Lam A1 B1) a1 b1) (SigmaB A1 B1)
pairCoh hA0 hB0 ha0 hb0 hA1 hB1 ha1 hb1 ca cb =
  sigma _ _ _ _ hA0 hB0 hA1 hB1 (tyeq-refl (isty-Sigma hA0 hB0)) (tyeq-refl (isty-Sigma hA1 hB1))
    p0 p1
    (cohConvR (cohConvL ca (conv-sym fb0) (tyeq-refl hA0)) (conv-sym fb1) (tyeq-refl hA1))
    (cohConvR (cohConvL cb (conv-sym sb0) (s1fTy w hA0 ha0 (snd (pCv fb0')) fb0' hB0))
              (conv-sym sb1) (s1fTy w hA1 ha1 (snd (pCv fb1')) fb1' hB1))
  where
    w = wfTy hA0
    p0 = ty-Pair hA0 hB0 ha0 hb0
    p1 = ty-Pair hA1 hB1 ha1 hb1
    fb0 = conv-fst-beta hA0 hB0 ha0 hb0
    fb1 = conv-fst-beta hA1 hB1 ha1 hb1
    fb0' = conv-sym fb0
    fb1' = conv-sym fb1
    sb0 = conv-snd-beta hA0 hB0 ha0 hb0
    sb1 = conv-snd-beta hA1 hB1 ha1 hb1

fstCoh : {n : Num} {G : Ctx n} {A0 A1 s0 s1 : Expr n} {B0 B1 : Expr (suc n)} ->
         IsType G A0 -> IsType (extend G A0) B0 -> HasType G s0 (SigmaB A0 B0) ->
         IsType G A1 -> IsType (extend G A1) B1 -> HasType G s1 (SigmaB A1 B1) ->
         Coh G s0 (SigmaB A0 B0) s1 (SigmaB A1 B1) ->
         Coh G (Fst A0 (Lam A0 B0) s0) A0 (Fst A1 (Lam A1 B1) s1) A1
fstCoh hA0 hB0 hs0 hA1 hB1 hs1 (same q c) =
  same (fst (Sig-inj q)) (conv-Fst hA0 hB0 (fst (Sig-inj q)) (snd (Sig-inj q)) c)
fstCoh hA0 hB0 hs0 hA1 hB1 hs1 (univ u0 u1 p0 p1 c) =
  Empty-elim (upNoSig p0 (tyeq-refl (isty-Sigma hA0 hB0)))
fstCoh hA0 hB0 hs0 hA1 hB1 hs1 (pi D C0 C1 hD hC0 hC1 q0 q1 h0 h1 c) =
  Empty-elim (tPi-Sig (tyeq-sym q0))
fstCoh hA0 hB0 hs0 hA1 hB1 hs1 (sigma D0 D1 C0 C1 hD0 hC0 hD1 hC1 q0 q1 h0 h1 cF cS) =
  cohConvR (cohConvL cF (fstAnn hD0 hC0 q0 h0) (tyeq-sym (fst (Sig-inj q0))))
           (fstAnn hD1 hC1 q1 h1) (tyeq-sym (fst (Sig-inj q1)))
  where
    fstAnn : {n : Num} {G : Ctx n} {A D s : Expr n} {B C : Expr (suc n)} ->
             IsType G D -> IsType (extend G D) C -> TyEq G (SigmaB A B) (SigmaB D C) ->
             HasType G s (SigmaB A B) ->
             ConvTm G (Fst D (Lam D C) s) (Fst A (Lam A B) s) D
    fstAnn hD hC q h =
      conv-Fst hD hC (tyeq-sym (fst (Sig-inj q))) (tyeq-sym (ccTE hD (tyeq-sym (fst (Sig-inj q))) (snd (Sig-inj q))))
               (conv-refl (ty-conv h q))

sndCoh : {n : Num} {G : Ctx n} {A0 A1 s0 s1 : Expr n} {B0 B1 : Expr (suc n)} ->
         IsType G A0 -> IsType (extend G A0) B0 -> HasType G s0 (SigmaB A0 B0) ->
         IsType G A1 -> IsType (extend G A1) B1 -> HasType G s1 (SigmaB A1 B1) ->
         Coh G s0 (SigmaB A0 B0) s1 (SigmaB A1 B1) ->
         Coh G (Snd A0 (Lam A0 B0) s0) (subst1 B0 (Fst A0 (Lam A0 B0) s0))
               (Snd A1 (Lam A1 B1) s1) (subst1 B1 (Fst A1 (Lam A1 B1) s1))
sndCoh hA0 hB0 hs0 hA1 hB1 hs1 (same q c) =
  same (tyeq-trans (s1fTy w hA0 (fst (pCv cF)) (snd (pCv cF)) cF hB0) (s1TE w (snd (pCv cF)) qB))
       (conv-Snd hA0 hB0 qA qB c)
  where
    w = wfTy hA0
    qA = fst (Sig-inj q)
    qB = snd (Sig-inj q)
    cF = conv-Fst hA0 hB0 qA qB c
sndCoh hA0 hB0 hs0 hA1 hB1 hs1 (univ u0 u1 p0 p1 c) =
  Empty-elim (upNoSig p0 (tyeq-refl (isty-Sigma hA0 hB0)))
sndCoh hA0 hB0 hs0 hA1 hB1 hs1 (pi D C0 C1 hD hC0 hC1 q0 q1 h0 h1 c) =
  Empty-elim (tPi-Sig (tyeq-sym q0))
sndCoh hA0 hB0 hs0 hA1 hB1 hs1 (sigma D0 D1 C0 C1 hD0 hC0 hD1 hC1 q0 q1 h0 h1 cF cS) =
  cohConvR (cohConvL cS (sndAnn hD0 hC0 q0 h0) (sndTy hD0 hC0 q0 h0))
           (sndAnn hD1 hC1 q1 h1) (sndTy hD1 hC1 q1 h1)
  where
    module _ {n : Num} {G : Ctx n} {A D s : Expr n} {B C : Expr (suc n)}
             (hD : IsType G D) (hC : IsType (extend G D) C) (q : TyEq G (SigmaB A B) (SigmaB D C))
             (h : HasType G s (SigmaB A B)) where
      qAD = tyeq-sym (fst (Sig-inj q))
      qCB = tyeq-sym (ccTE hD (tyeq-sym (fst (Sig-inj q))) (snd (Sig-inj q)))
      hS = ty-conv h q
      sndAnn : ConvTm G (Snd D (Lam D C) s) (Snd A (Lam A B) s) (subst1 C (Fst D (Lam D C) s))
      sndAnn = conv-Snd hD hC qAD qCB (conv-refl hS)
      cFa : ConvTm G (Fst D (Lam D C) s) (Fst A (Lam A B) s) D
      cFa = conv-Fst hD hC qAD qCB (conv-refl hS)
      sndTy : TyEq G (subst1 C (Fst D (Lam D C) s)) (subst1 B (Fst A (Lam A B) s))
      sndTy = tyeq-trans (s1fTy (wfTy hD) hD (fst (pCv cFa)) (snd (pCv cFa)) cFa hC)
                         (s1TE (wfTy hD) (snd (pCv cFa)) qCB)

------------------------------------------------------------------------
-- Kinds: the universe a code lives in
------------------------------------------------------------------------

data Kind (n : Num) : Set where
  kV : Kind n
  kU : Expr n -> Expr n -> Kind n

KTy : {n : Num} -> Kind n -> Expr n
KTy kV = V
KTy (kU f g) = TyU f g

-- the image in V
KIm : {n : Num} -> Kind n -> Expr n -> Expr n
KIm kV t = t
KIm (kU f g) t = That t

-- decoding
KEl : {n : Num} -> Kind n -> Expr n -> Expr n
KEl kV a = ElV a
KEl (kU f g) a = ElU f g a

wkK : {n : Num} -> Kind n -> Kind (suc n)
wkK kV = kV
wkK (kU f g) = kU (wkExpr f) (wkExpr g)

module _ {n : Num} {G : Ctx n} where

  upK : {t A : Expr n} (k : Kind n) -> HasType G t A -> TyEq G A (KTy k) -> Up G t A (KIm k t)
  upK kV h q = upV q (ty-conv h q) refl
  upK (kU f g) h q = upU f g q (ty-conv h q) refl

  upK' : {t : Expr n} (k : Kind n) -> HasType G t (KTy k) -> Up G t (KTy k) (KIm k t)
  upK' k h = upK k h (tyeq-refl (pTm h))

  imTy : {t : Expr n} (k : Kind n) -> HasType G t (KTy k) -> HasType G (KIm k t) V
  imTy kV h = h
  imTy (kU f g) h = ty-That h

  elImEq : {a : Expr n} (k : Kind n) -> HasType G a (KTy k) -> TyEq G (KEl k a) (ElV (KIm k a))
  elImEq kV h = tyeq-refl (isty-ElV h)
  elImEq (kU f g) h = tyeq-ElU-That h

  isKEl : {a : Expr n} (k : Kind n) -> HasType G a (KTy k) -> IsType G (KEl k a)
  isKEl kV h = isty-ElV h
  isKEl (kU f g) h = isty-ElU h

  -- moving between the decodings of two coherent codes
  elKEq : {x0 x1 : Expr n} (k0 k1 : Kind n) -> HasType G x0 (KTy k0) -> HasType G x1 (KTy k1) ->
          ConvTm G (KIm k0 x0) (KIm k1 x1) V -> TyEq G (KEl k0 x0) (KEl k1 x1)
  elKEq k0 k1 h0 h1 c = tyeq-trans (elImEq k0 h0) (tyeq-trans (tyeq-ElV c) (tyeq-sym (elImEq k1 h1)))

  -- the family of a code, mapped to V
  famIm : {x : Expr n} {b : Expr (suc n)} (k : Kind n) -> HasType G x (KTy k) ->
          HasType (extend G (KEl k x)) b (KTy (wkK k)) ->
          HasType (extend G (ElV (KIm k x))) (KIm (wkK k) b) V
  famIm kV hx hb = hb
  famIm (kU f g) hx hb = famBody hx hb

------------------------------------------------------------------------
-- Pi / Sigma codes
------------------------------------------------------------------------

data Fm : Set where
  fPi  : Fm
  fSig : Fm

codeK : {n : Num} -> Fm -> Kind n -> Expr n -> Expr (suc n) -> Expr n
codeK fPi kV x b = PiV x (Lam (ElV x) b)
codeK fPi (kU f g) x b = PiU f g x (Lam (ElU f g x) b)
codeK fSig kV x b = SigV x (Lam (ElV x) b)
codeK fSig (kU f g) x b = SigU f g x (Lam (ElU f g x) b)

codeV : {n : Num} -> Fm -> Expr n -> Expr n -> Expr n
codeV fPi a F = PiV a F
codeV fSig a F = SigV a F

decT : {n : Num} -> Fm -> Expr n -> Expr (suc n) -> Expr n
decT fPi A B = PiB A B
decT fSig A B = SigmaB A B

module _ {n : Num} {G : Ctx n} where

  codeTy : {x : Expr n} {b : Expr (suc n)} (fm : Fm) (k : Kind n) -> HasType G x (KTy k) ->
           HasType (extend G (KEl k x)) b (KTy (wkK k)) -> HasType G (codeK fm k x b) (KTy k)
  codeTy fPi kV hx hb = ty-PiV hx hb
  codeTy fPi (kU f g) hx hb = ty-PiU hx hb
  codeTy fSig kV hx hb = ty-SigV hx hb
  codeTy fSig (kU f g) hx hb = ty-SigU hx hb

  codeEqn : {x : Expr n} {b : Expr (suc n)} (fm : Fm) (k : Kind n) -> HasType G x (KTy k) ->
            HasType (extend G (KEl k x)) b (KTy (wkK k)) ->
            ConvTm G (KIm k (codeK fm k x b)) (codeV fm (KIm k x) (Lam (ElV (KIm k x)) (KIm (wkK k) b))) V
  codeEqn fPi kV hx hb = conv-refl (ty-PiV hx hb)
  codeEqn fPi (kU f g) hx hb = conv-That-PiU hx hb
  codeEqn fSig kV hx hb = conv-refl (ty-SigV hx hb)
  codeEqn fSig (kU f g) hx hb = conv-That-SigU hx hb

  codeCong : {a a' : Expr n} {b b' : Expr (suc n)} (fm : Fm) ->
             HasType G a V -> HasType (extend G (ElV a)) b V -> HasType (extend G (ElV a)) b' V ->
             ConvTm G a a' V -> ConvTm (extend G (ElV a)) b b' V ->
             ConvTm G (codeV fm a (Lam (ElV a) b)) (codeV fm a' (Lam (ElV a') b')) V
  codeCong fPi = conv-PiV
  codeCong fSig = conv-SigV

  decEq : {a : Expr n} {b : Expr (suc n)} (fm : Fm) ->
          HasType G a V -> HasType (extend G (ElV a)) b V ->
          TyEq G (ElV (codeV fm a (Lam (ElV a) b))) (decT fm (ElV a) (ElV b))
  decEq fPi = tyeq-El-PiV
  decEq fSig = tyeq-El-SigV

  decCong : {A A' : Expr n} {B B' : Expr (suc n)} (fm : Fm) ->
            IsType G A -> IsType (extend G A) B -> IsType (extend G A) B' ->
            TyEq G A A' -> TyEq (extend G A) B B' -> TyEq G (decT fm A B) (decT fm A' B')
  decCong fPi = tyeq-Pi
  decCong fSig = tyeq-Sigma

  -- two coherent codes (b1 typed both in its own context and in that of b0)
  codeCoh : {x0 x1 : Expr n} {b0 b1 : Expr (suc n)} (fm : Fm) (k0 k1 : Kind n) ->
            HasType G x0 (KTy k0) -> HasType (extend G (KEl k0 x0)) b0 (KTy (wkK k0)) ->
            HasType G x1 (KTy k1) -> HasType (extend G (KEl k1 x1)) b1 (KTy (wkK k1)) ->
            HasType (extend G (KEl k0 x0)) b1 (KTy (wkK k1)) ->
            Coh G x0 (KTy k0) x1 (KTy k1) ->
            Coh (extend G (KEl k0 x0)) b0 (KTy (wkK k0)) b1 (KTy (wkK k1)) ->
            Coh G (codeK fm k0 x0 b0) (KTy k0) (codeK fm k1 x1 b1) (KTy k1)
  codeCoh fm k0 k1 hx0 hb0 hx1 hb1 hb1' cx cb =
    univ _ _ (upK' k0 (codeTy fm k0 hx0 hb0)) (upK' k1 (codeTy fm k1 hx1 hb1))
      (conv-trans (codeEqn fm k0 hx0 hb0)
        (conv-trans (codeCong fm (imTy k0 hx0) (fst (pCv cbi')) (snd (pCv cbi')) cxi cbi')
                    (conv-sym (codeEqn fm k1 hx1 hb1))))
    where
      cxi = cohUp cx (upK' k0 hx0) (upK' k1 hx1)
      cbi = cohUp cb (upK' (wkK k0) hb0) (upK' (wkK k1) hb1')
      cbi' = ccCv (isty-ElV (imTy k0 hx0)) (tyeq-sym (elImEq k0 hx0)) cbi

  -- the decoding of a code, against a Pi / Sigma type
  elCode : {x D : Expr n} {b B : Expr (suc n)} (fm : Fm) (k : Kind n) ->
           HasType G x (KTy k) -> HasType (extend G (KEl k x)) b (KTy (wkK k)) ->
           IsType G D -> IsType (extend G D) B ->
           TyEq G (ElV (KIm k x)) D -> TyEq (extend G (KEl k x)) (ElV (KIm (wkK k) b)) B ->
           TyEq G (ElV (KIm k (codeK fm k x b))) (decT fm D B)
  elCode fm k hx hb hD hB qd qb =
    tyeq-trans (tyeq-ElV (codeEqn fm k hx hb))
      (tyeq-trans (decEq fm (imTy k hx) hbi)
                  (decCong fm hEi (isty-ElV hbi) (ccTy hEi qd hB) qd
                           (ccTE hEi (tyeq-sym (elImEq k hx)) qb)))
    where
      hEi = isty-ElV (imTy k hx)
      hbi = famIm k hx hb

------------------------------------------------------------------------
-- N codes, U codes, f^, g^
------------------------------------------------------------------------

natK : {n : Num} -> Kind n -> Expr n
natK kV = NatV
natK (kU f g) = NatU f g

module _ {n : Num} {G : Ctx n} where

  natTy : (k : Kind n) -> IsType G (KTy k) -> HasType G (natK k) (KTy k)
  natTy kV hU = ty-NatV (wfTy hU)
  natTy (kU f g) hU = ty-NatU hU

  natEqn : (k : Kind n) -> IsType G (KTy k) -> ConvTm G (KIm k (natK k)) NatV V
  natEqn kV hU = conv-refl (ty-NatV (wfTy hU))
  natEqn (kU f g) hU = conv-That-NatU hU

  natCoh : (k0 k1 : Kind n) -> IsType G (KTy k0) -> IsType G (KTy k1) ->
           Coh G (natK k0) (KTy k0) (natK k1) (KTy k1)
  natCoh k0 k1 hU0 hU1 =
    univ _ _ (upK' k0 (natTy k0 hU0)) (upK' k1 (natTy k1 hU1))
      (conv-trans (natEqn k0 hU0) (conv-sym (natEqn k1 hU1)))

  elNat : (k : Kind n) -> IsType G (KTy k) -> TyEq G (ElV (KIm k (natK k))) Nat
  elNat k hU = tyeq-trans (tyeq-ElV (natEqn k hU)) (tyeq-El-NatV (wfTy hU))

  -- f, g of two coherent operator pairs are convertible
  opConv : {f0 f1 g0 g1 : Expr n} -> HasType G f0 OpF -> HasType G f1 OpF ->
           Coh G f0 OpF f1 OpF -> Coh G g0 (OpG f0) g1 (OpG f1) ->
           ConvTm G f0 f1 OpF * ConvTm G g0 g1 (OpG f0)
  opConv hf0 hf1 cohf cohg = cf , extract cohg (opGEq (wfTm hf0) hf0 hf1 cf)
    where cf = extract cohf (tyeq-refl (opFTy (wfTm hf0)))

  uvCoh : {f0 f1 g0 g1 : Expr n} -> HasType G f0 OpF -> HasType G g0 (OpG f0) -> HasType G f1 OpF ->
          Coh G f0 OpF f1 OpF -> Coh G g0 (OpG f0) g1 (OpG f1) -> Coh G (UV f0 g0) V (UV f1 g1) V
  uvCoh hf0 hg0 hf1 cohf cohg =
    same (tyeq-refl (isty-V (wfTm hf0))) (conv-UV hf0 hg0 (fst cs) (snd cs))
    where cs = opConv hf0 hf1 cohf cohg

  module _ {f0 f1 g0 g1 x0 x1 : Expr n} {b0 b1 : Expr (suc n)}
           (hf0 : HasType G f0 OpF) (hg0 : HasType G g0 (OpG f0))
           (hx0 : HasType G x0 (TyU f0 g0)) (hb0 : HasType (extend G (ElU f0 g0 x0)) b0 (wkExpr (TyU f0 g0)))
           (hf1 : HasType G f1 OpF) (hg1 : HasType G g1 (OpG f1))
           (hx1 : HasType G x1 (TyU f1 g1)) (hb1 : HasType (extend G (ElU f1 g1 x1)) b1 (wkExpr (TyU f1 g1)))
           (hb1' : HasType (extend G (ElU f0 g0 x0)) b1 (wkExpr (TyU f1 g1)))
           (cohf : Coh G f0 OpF f1 OpF)
           (cx : Coh G x0 (TyU f0 g0) x1 (TyU f1 g1))
           (cb : Coh (extend G (ElU f0 g0 x0)) b0 (wkExpr (TyU f0 g0)) b1 (wkExpr (TyU f1 g1))) where

    private
      k0 = kU f0 g0
      k1 = kU f1 g1
      cf = extract cohf (tyeq-refl (opFTy (wfTm hf0)))
      cxi = cohUp cx (upK' k0 hx0) (upK' k1 hx1)
      cbi = cohUp cb (upK' (wkK k0) hb0) (upK' (wkK k1) hb1')
      hE = isty-ElV (ty-That hx0)
      cbi' = ccCv hE (tyeq-sym (tyeq-ElU-That hx0)) cbi

    cFam : ConvTm G (Lam (ElV (That x0)) (That b0)) (Lam (ElV (That x1)) (That b1)) (Arr (ElV (That x0)) V)
    cFam = conv-Lam hE (isty-V (wf-extend hE)) (tyeq-ElV cxi) cbi'

    fhatChain : ConvTm G (That (Fhat f0 g0 x0 (Lam (ElU f0 g0 x0) b0)))
                         (That (Fhat f1 g1 x1 (Lam (ElU f1 g1 x1) b1))) V
    fhatChain =
      conv-trans (conv-That-Fhat hf0 hg0 hx0 hb0)
        (conv-trans (fAppCong hf0 (ty-That hx0) cf cxi cFam)
                    (conv-sym (conv-That-Fhat hf1 hg1 hx1 hb1)))

    fhatCoh : Coh G (Fhat f0 g0 x0 (Lam (ElU f0 g0 x0) b0)) (TyU f0 g0)
                    (Fhat f1 g1 x1 (Lam (ElU f1 g1 x1) b1)) (TyU f1 g1)
    fhatCoh = univ _ _ (upK' k0 (ty-Fhat hf0 hg0 hx0 hb0)) (upK' k1 (ty-Fhat hf1 hg1 hx1 hb1)) fhatChain

    ghatCoh : {c0 c1 : Expr n} ->
              HasType G c0 (ElU f0 g0 (Fhat f0 g0 x0 (Lam (ElU f0 g0 x0) b0))) ->
              HasType G c1 (ElU f1 g1 (Fhat f1 g1 x1 (Lam (ElU f1 g1 x1) b1))) ->
              Coh G g0 (OpG f0) g1 (OpG f1) ->
              Coh G c0 (ElU f0 g0 (Fhat f0 g0 x0 (Lam (ElU f0 g0 x0) b0)))
                    c1 (ElU f1 g1 (Fhat f1 g1 x1 (Lam (ElU f1 g1 x1) b1))) ->
              Coh G (Ghat f0 g0 x0 (Lam (ElU f0 g0 x0) b0) c0) (TyU f0 g0)
                    (Ghat f1 g1 x1 (Lam (ElU f1 g1 x1) b1) c1) (TyU f1 g1)
    ghatCoh hc0 hc1 cohg cohc =
      univ _ _ (upK' k0 (ty-Ghat hf0 hg0 hx0 hb0 hc0)) (upK' k1 (ty-Ghat hf1 hg1 hx1 hb1 hc1))
        (conv-trans (conv-That-Ghat hf0 hg0 hx0 hb0 hc0)
          (conv-trans (gAppCong hf0 hf1 hg0 (ty-That hx0) (fst (pCv cFam)) cf cg cxi cFam cc')
                      (conv-sym (conv-That-Ghat hf1 hg1 hx1 hb1 hc1))))
      where
        cg = extract cohg (opGEq (wfTm hf0) hf0 hf1 cf)
        hF0 = ty-Fhat hf0 hg0 hx0 hb0
        hF1 = ty-Fhat hf1 hg1 hx1 hb1
        qc = tyeq-trans (tyeq-ElU-That hF0) (tyeq-trans (tyeq-ElV fhatChain) (tyeq-sym (tyeq-ElU-That hF1)))
        cc' = conv-conv (extract cohc qc)
                (tyeq-trans (tyeq-ElU-That hF0) (tyeq-ElV (conv-That-Fhat hf0 hg0 hx0 hb0)))
