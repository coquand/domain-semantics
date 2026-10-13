{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Coh.agda
--
-- Coherence of two Tarski terms  t0 : A0,  t1 : A1  (in one context):
-- the form uniqueness takes when the Russell side is T_P-like (App,
-- Pair unannotated), ERT Lemma 4.10 merged with 4.18 (StripUniqNF).
--
--   same   A0 = A1  and  t0 = t1 : A0
--   univ   both types are universes (V, or a subuniverse U_{f,g}) and
--          the images in V agree:  ^t0 = ^t1 : V,  ^ = T^ on a U side
--   pi     A0 = Pi D B0,  A1 = Pi D B1,  and the applications to x0
--          are coherent (in G, D)
--   sigma  A0, A1 Sigma types, Fst's coherent and Snd's coherent
--
-- Same erasure does NOT give a common type, e.g.
--   \x:A. N^_U(f,g)  vs  \x:A. N^_V      (A -> U_{f,g}  vs  A -> V)
--   Pair(N^_U(f,g), 0)  vs  Pair(N^_V, 0)
-- have equal erasures and types that are neither equal nor universes.
--
-- Here: symmetry, closure under conversion and substitution, the T^
-- peeling steps, and (relative to TInj) same-type extraction.
------------------------------------------------------------------------

module MAHLORT.Coh where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Presup
open import MAHLORT.TNoConf
open import MAHLORT.Hyp

------------------------------------------------------------------------
-- The application of t to x0, in (G, D)  (= the funext body)
------------------------------------------------------------------------

funTy : {n : Num} {G : Ctx n} {D t : Expr n} {B : Expr (suc n)} ->
        IsType G D -> IsType (extend G D) B -> HasType G t (PiB D B) ->
        HasType (extend G D) (FunB D B t) B
funTy {G = G} {D} {t} {B} hD hB ht =
  trHT refl (subst1-liftWk-cancel B)
    (ty-App hX (rTy (liftRen wkRen) (liftRT {r = wkRen} {A = D} (wkRT {G = G} {D}) hX) (wf-extend hX) hB)
            (wkTm hD ht) (ty-var (wf-extend hD)))
  where hX = wkTy hD hD

-- FunB, with both the function and the codomain annotation changing
funCong : {n : Num} {G : Ctx n} {D t t' : Expr n} {B B' : Expr (suc n)} ->
          IsType G D -> IsType (extend G D) B -> TyEq (extend G D) B B' ->
          ConvTm G t t' (PiB D B) -> ConvTm (extend G D) (FunB D B t) (FunB D B' t') B
funCong {G = G} {D} {t} {t'} {B} hD hB qB c =
  trCv refl refl (subst1-liftWk-cancel B)
    (conv-App hX (rTy (liftRen wkRen) rt (wf-extend hX) hB) (tyeq-refl hX)
              (rTE (liftRen wkRen) rt (wf-extend hX) qB)
              (wkCv hD c) (conv-refl (ty-var (wf-extend hD))))
  where
    hX = wkTy hD hD
    rt = liftRT {r = wkRen} {A = D} (wkRT {G = G} {D}) hX

------------------------------------------------------------------------
-- Universes and the image in V
------------------------------------------------------------------------

data Up {n : Num} (G : Ctx n) (t A u : Expr n) : Set where
  upV : TyEq G A V -> HasType G t V -> Eq u t -> Up G t A u
  upU : (f g : Expr n) -> TyEq G A (TyU f g) -> HasType G t (TyU f g) -> Eq u (That t) -> Up G t A u

------------------------------------------------------------------------
-- Coherence
------------------------------------------------------------------------

data Coh : {n : Num} (G : Ctx n) (t0 A0 t1 A1 : Expr n) -> Set where
  same  : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} ->
          TyEq G A0 A1 -> ConvTm G t0 t1 A0 -> Coh G t0 A0 t1 A1
  univ  : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} (u0 u1 : Expr n) ->
          Up G t0 A0 u0 -> Up G t1 A1 u1 -> ConvTm G u0 u1 V -> Coh G t0 A0 t1 A1
  pi    : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} (D : Expr n) (B0 B1 : Expr (suc n)) ->
          IsType G D -> IsType (extend G D) B0 -> IsType (extend G D) B1 ->
          TyEq G A0 (PiB D B0) -> TyEq G A1 (PiB D B1) ->
          HasType G t0 A0 -> HasType G t1 A1 ->
          Coh (extend G D) (FunB D B0 t0) B0 (FunB D B1 t1) B1 ->
          Coh G t0 A0 t1 A1
  sigma : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} (D0 D1 : Expr n) (B0 B1 : Expr (suc n)) ->
          IsType G D0 -> IsType (extend G D0) B0 -> IsType G D1 -> IsType (extend G D1) B1 ->
          TyEq G A0 (SigmaB D0 B0) -> TyEq G A1 (SigmaB D1 B1) ->
          HasType G t0 A0 -> HasType G t1 A1 ->
          Coh G (Fst D0 (Lam D0 B0) t0) D0 (Fst D1 (Lam D1 B1) t1) D1 ->
          Coh G (Snd D0 (Lam D0 B0) t0) (subst1 B0 (Fst D0 (Lam D0 B0) t0))
                (Snd D1 (Lam D1 B1) t1) (subst1 B1 (Fst D1 (Lam D1 B1) t1)) ->
          Coh G t0 A0 t1 A1

trCoh : {n : Num} {G : Ctx n} {t0 t0' A0 A0' t1 t1' A1 A1' : Expr n} ->
        Eq t0 t0' -> Eq A0 A0' -> Eq t1 t1' -> Eq A1 A1' -> Coh G t0 A0 t1 A1 -> Coh G t0' A0' t1' A1'
trCoh refl refl refl refl c = c

------------------------------------------------------------------------
-- Typing of the two sides
------------------------------------------------------------------------

upTy : {n : Num} {G : Ctx n} {t A u : Expr n} -> Up G t A u -> HasType G t A
upTy (upV q h e) = ty-conv h (tyeq-sym q)
upTy (upU f g q h e) = ty-conv h (tyeq-sym q)

cohL : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} -> Coh G t0 A0 t1 A1 -> HasType G t0 A0
cohL (same q c) = fst (pCv c)
cohL (univ u0 u1 p0 p1 c) = upTy p0
cohL (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) = h0
cohL (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') = h0

cohR : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} -> Coh G t0 A0 t1 A1 -> HasType G t1 A1
cohR (same q c) = ty-conv (snd (pCv c)) q
cohR (univ u0 u1 p0 p1 c) = upTy p1
cohR (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) = h1
cohR (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') = h1

------------------------------------------------------------------------
-- Symmetry
------------------------------------------------------------------------

cohSym : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} -> Coh G t0 A0 t1 A1 -> Coh G t1 A1 t0 A0
cohSym (same q c) = same (tyeq-sym q) (conv-conv (conv-sym c) q)
cohSym (univ u0 u1 p0 p1 c) = univ u1 u0 p1 p0 (conv-sym c)
cohSym (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) = pi D B1 B0 hD hB1 hB0 q1 q0 h1 h0 (cohSym c)
cohSym (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') =
  sigma D1 D0 B1 B0 hD1 hB1 hD0 hB0 q1 q0 h1 h0 (cohSym c) (cohSym c')

------------------------------------------------------------------------
-- Closure under conversion (right side; left side by symmetry)
------------------------------------------------------------------------

cohConvR : {n : Num} {G : Ctx n} {t0 A0 t1 A1 t1' A1' : Expr n} ->
           Coh G t0 A0 t1 A1 -> ConvTm G t1 t1' A1 -> TyEq G A1 A1' -> Coh G t0 A0 t1' A1'
cohConvR (same q c) c1 q' = same (tyeq-trans q q') (conv-trans c (conv-conv c1 (tyeq-sym q)))
cohConvR (univ u0 u1 p0 (upV q h e) c) c1 q' =
  univ u0 _ p0 (upV (tyeq-trans (tyeq-sym q') q) (snd (pCv c1V)) refl) (conv-trans (trCv refl e refl c) c1V)
  where c1V = conv-conv c1 q
cohConvR (univ u0 u1 p0 (upU f g q h e) c) c1 q' =
  univ u0 _ p0 (upU f g (tyeq-trans (tyeq-sym q') q) (snd (pCv c1U)) refl)
       (conv-trans (trCv refl e refl c) (conv-That c1U))
  where c1U = conv-conv c1 q
cohConvR (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) c1 q' =
  pi D B0 B1 hD hB0 hB1 q0 (tyeq-trans (tyeq-sym q') q1) h0 (ty-conv (snd (pCv c1)) q')
     (cohConvR c (funCong hD hB1 (tyeq-refl hB1) (conv-conv c1 q1)) (tyeq-refl hB1))
cohConvR {G = G} (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') c1 q' =
  sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 (tyeq-trans (tyeq-sym q') q1) h0 (ty-conv (snd (pCv c1)) q')
    (cohConvR c cF (tyeq-refl hD1))
    (cohConvR c' (conv-Snd hD1 hB1 (tyeq-refl hD1) (tyeq-refl hB1) c1S)
                 (s1fTy (wfTy hD1) hD1 (fst (pCv cF)) (snd (pCv cF)) cF hB1))
  where
    c1S = conv-conv c1 q1
    cF = conv-Fst hD1 hB1 (tyeq-refl hD1) (tyeq-refl hB1) c1S

cohConvL : {n : Num} {G : Ctx n} {t0 A0 t1 A1 t0' A0' : Expr n} ->
           Coh G t0 A0 t1 A1 -> ConvTm G t0 t0' A0 -> TyEq G A0 A0' -> Coh G t0' A0' t1 A1
cohConvL c c0 q = cohSym (cohConvR (cohSym c) c0 q)

------------------------------------------------------------------------
-- Closure under substitution
------------------------------------------------------------------------

private
  sbUp : {h g : Num} {H : Ctx h} {G : Ctx g} (s : Sub h g) -> WtSub H G s -> WfCtx H ->
         {t A u : Expr g} -> Up G t A u -> Up H (substExpr s t) (substExpr s A) (substExpr s u)
  sbUp s ws w (upV q h e) = upV (sbTE s ws w q) (sbTm s ws w h) (Eq-cong (substExpr s) e)
  sbUp s ws w (upU f g q h e) =
    upU (substExpr s f) (substExpr s g) (sbTE s ws w q) (sbTm s ws w h) (Eq-cong (substExpr s) e)

cohSub : {h g : Num} {H : Ctx h} {G : Ctx g} (s : Sub h g) -> WtSub H G s -> WfCtx H ->
         {t0 A0 t1 A1 : Expr g} -> Coh G t0 A0 t1 A1 ->
         Coh H (substExpr s t0) (substExpr s A0) (substExpr s t1) (substExpr s A1)
cohSub s ws w (same q c) = same (sbTE s ws w q) (sbCv s ws w c)
cohSub s ws w (univ u0 u1 p0 p1 c) =
  univ (substExpr s u0) (substExpr s u1) (sbUp s ws w p0) (sbUp s ws w p1) (sbCv s ws w c)
cohSub s ws w {t0} {A0} {t1} {A1} (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) =
  pi (substExpr s D) (substExpr (liftSub s) B0) (substExpr (liftSub s) B1) hsD
     (sbTy (liftSub s) wsL wL hB0) (sbTy (liftSub s) wsL wL hB1)
     (sbTE s ws w q0) (sbTE s ws w q1) (sbTm s ws w h0) (sbTm s ws w h1)
     (trCoh (subst-FunB s D B0 t0) refl (subst-FunB s D B1 t1) refl (cohSub (liftSub s) wsL wL c))
  where
    hsD = sbTy s ws w hD
    wsL = liftWS ws hsD
    wL = wf-extend hsD
cohSub s ws w {t0} {A0} {t1} {A1} (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') =
  sigma (substExpr s D0) (substExpr s D1) (substExpr (liftSub s) B0) (substExpr (liftSub s) B1)
        hsD0 (sbTy (liftSub s) (liftWS ws hsD0) (wf-extend hsD0) hB0)
        hsD1 (sbTy (liftSub s) (liftWS ws hsD1) (wf-extend hsD1) hB1)
        (sbTE s ws w q0) (sbTE s ws w q1) (sbTm s ws w h0) (sbTm s ws w h1)
        (cohSub s ws w c)
        (trCoh refl (subst-subst1-comm s B0 (Fst D0 (Lam D0 B0) t0)) refl
               (subst-subst1-comm s B1 (Fst D1 (Lam D1 B1) t1)) (cohSub s ws w c'))
  where
    hsD0 = sbTy s ws w hD0
    hsD1 = sbTy s ws w hD1

------------------------------------------------------------------------
-- Peeling T^:  t0 = T^ x  with  x : U_{f,g}
------------------------------------------------------------------------

cohThatL : {n : Num} {G : Ctx n} {f g x A t1 A1 : Expr n} ->
           HasType G x (TyU f g) -> TyEq G A V -> Coh G x (TyU f g) t1 A1 -> Coh G (That x) A t1 A1
cohThatL {f = f} {g} hx qA (same q c) =
  univ _ _ (upV qA (ty-That hx) refl) (upU f g (tyeq-sym q) (snd (pCv c)) refl) (conv-That c)
cohThatL hx qA (univ u0 u1 (upV q h e) p1 c) = Empty-elim (tV-U (tyeq-sym q))
cohThatL hx qA (univ u0 u1 (upU f' g' q h e) p1 c) =
  univ _ u1 (upV qA (ty-That hx) refl) p1 (trCv e refl refl c)
cohThatL hx qA (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) = Empty-elim (tU-Pi q0)
cohThatL hx qA (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') = Empty-elim (tU-Sig q0)

cohThatR : {n : Num} {G : Ctx n} {f g x A t0 A0 : Expr n} ->
           HasType G x (TyU f g) -> TyEq G A V -> Coh G t0 A0 x (TyU f g) -> Coh G t0 A0 (That x) A
cohThatR hx qA c = cohSym (cohThatL hx qA (cohSym c))

------------------------------------------------------------------------
-- Two universes: the images in V agree
------------------------------------------------------------------------

upUniq : {n : Num} {G : Ctx n} {t A u u' : Expr n} -> Up G t A u -> Up G t A u' -> Eq u u'
upUniq (upV q h e) (upV q' h' e') = Eq-trans e (Eq-sym e')
upUniq (upV q h e) (upU f g q' h' e') = Empty-elim (tV-U (tyeq-trans (tyeq-sym q) q'))
upUniq (upU f g q h e) (upV q' h' e') = Empty-elim (tV-U (tyeq-trans (tyeq-sym q') q))
upUniq (upU f g q h e) (upU f' g' q' h' e') = Eq-trans e (Eq-sym e')

upNoPi : {n : Num} {G : Ctx n} {t A u D : Expr n} {B : Expr (suc n)} ->
         Up G t A u -> TyEq G A (PiB D B) -> Empty
upNoPi (upV q h e) q' = tV-Pi (tyeq-trans (tyeq-sym q) q')
upNoPi (upU f g q h e) q' = tU-Pi (tyeq-trans (tyeq-sym q) q')

upNoSig : {n : Num} {G : Ctx n} {t A u D : Expr n} {B : Expr (suc n)} ->
          Up G t A u -> TyEq G A (SigmaB D B) -> Empty
upNoSig (upV q h e) q' = tV-Sig (tyeq-trans (tyeq-sym q) q')
upNoSig (upU f g q h e) q' = tU-Sig (tyeq-trans (tyeq-sym q) q')

cohUp : {n : Num} {G : Ctx n} {t0 A0 t1 A1 u0 u1 : Expr n} ->
        Coh G t0 A0 t1 A1 -> Up G t0 A0 u0 -> Up G t1 A1 u1 -> ConvTm G u0 u1 V
cohUp (same q c) (upV q0 h0 e0) (upV q1 h1 e1) = trCv (Eq-sym e0) (Eq-sym e1) refl (conv-conv c q0)
cohUp (same q c) (upV q0 h0 e0) (upU f g q1 h1 e1) =
  Empty-elim (tV-U (tyeq-trans (tyeq-sym q0) (tyeq-trans q q1)))
cohUp (same q c) (upU f g q0 h0 e0) (upV q1 h1 e1) =
  Empty-elim (tV-U (tyeq-trans (tyeq-sym q1) (tyeq-trans (tyeq-sym q) q0)))
cohUp (same q c) (upU f g q0 h0 e0) (upU f' g' q1 h1 e1) =
  trCv (Eq-sym e0) (Eq-sym e1) refl (conv-That (conv-conv c q0))
cohUp (univ u0 u1 p0 p1 c) p0' p1' = trCv (upUniq p0 p0') (upUniq p1 p1') refl c
cohUp (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) p0' p1' = Empty-elim (upNoPi p0' q0)
cohUp (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') p0' p1' = Empty-elim (upNoSig p0' q0)

------------------------------------------------------------------------
-- Same-type extraction (relative to Pi/Sigma-injectivity)
------------------------------------------------------------------------

module Extract (I : TInj) where
  open TInj I

  extract : {n : Num} {G : Ctx n} {t0 A0 t1 A1 : Expr n} ->
            Coh G t0 A0 t1 A1 -> TyEq G A0 A1 -> ConvTm G t0 t1 A0
  extract (same q c) q' = c
  extract (univ u0 u1 (upV q0 h0 e0) (upV q1 h1 e1) c) q' =
    conv-conv (trCv e0 e1 refl c) (tyeq-sym q0)
  extract (univ u0 u1 (upV q0 h0 e0) (upU f g q1 h1 e1) c) q' =
    Empty-elim (tV-U (tyeq-trans (tyeq-sym q0) (tyeq-trans q' q1)))
  extract (univ u0 u1 (upU f g q0 h0 e0) (upV q1 h1 e1) c) q' =
    Empty-elim (tV-U (tyeq-trans (tyeq-sym q1) (tyeq-trans (tyeq-sym q') q0)))
  extract (univ u0 u1 (upU f g q0 h0 e0) (upU f' g' q1 h1 e1) c) q' =
    conv-conv (conv-reflect h0 (ty-conv h1 (tyeq-sym qU)) (trCv e0 e1 refl c)) (tyeq-sym q0)
    where qU = tyeq-trans (tyeq-sym q0) (tyeq-trans q' q1)
  extract (pi D B0 B1 hD hB0 hB1 q0 q1 h0 h1 c) q' =
    conv-conv
      (conv-funext hD hB0 (ty-conv h0 q0) (ty-conv h1 (tyeq-trans (tyeq-sym q') q0))
        (conv-trans (extract c qB)
          (conv-conv (funCong hD hB1 (tyeq-sym qB) (conv-refl (ty-conv h1 q1))) (tyeq-sym qB))))
      (tyeq-sym q0)
    where qB = snd (Pi-inj (tyeq-trans (tyeq-sym q0) (tyeq-trans q' q1)))
  extract {G = G} {t0} {A0} {t1} {A1} (sigma D0 D1 B0 B1 hD0 hB0 hD1 hB1 q0 q1 h0 h1 c c') q' =
    conv-conv (conv-pairext hD0 hB0 h0S h1S cFst cSnd) (tyeq-sym q0)
    where
      qS = Sig-inj (tyeq-trans (tyeq-sym q0) (tyeq-trans q' q1))
      qD = fst qS
      qB = snd qS
      w = wfTy hD0
      h0S = ty-conv h0 q0
      h1S = ty-conv h1 (tyeq-trans (tyeq-sym q') q0)
      F0 = Fst D0 (Lam D0 B0) t0
      -- Fst at the annotations of A0, against Fst at those of A1
      ann1 : ConvTm G (Fst D0 (Lam D0 B0) t1) (Fst D1 (Lam D1 B1) t1) D0
      ann1 = conv-Fst hD0 hB0 qD qB (conv-refl h1S)
      e01 : ConvTm G F0 (Fst D1 (Lam D1 B1) t1) D0
      e01 = extract c qD
      cFst : ConvTm G F0 (Fst D0 (Lam D0 B0) t1) D0
      cFst = conv-trans e01 (conv-sym ann1)
      hF0 = fst (pCv e01)
      hF1 = snd (pCv e01)
      -- B0[F0] = B1[F1]
      qSnd : TyEq G (subst1 B0 F0) (subst1 B1 (Fst D1 (Lam D1 B1) t1))
      qSnd = tyeq-trans (s1fTy w hD0 hF0 hF1 e01 hB0) (s1TE w hF1 qB)
      annS : ConvTm G (Snd D0 (Lam D0 B0) t1) (Snd D1 (Lam D1 B1) t1)
                      (subst1 B0 (Fst D0 (Lam D0 B0) t1))
      annS = conv-Snd hD0 hB0 qD qB (conv-refl h1S)
      qF : TyEq G (subst1 B0 F0) (subst1 B0 (Fst D0 (Lam D0 B0) t1))
      qF = s1fTy w hD0 hF0 (snd (pCv cFst)) cFst hB0
      cSnd : ConvTm G (Snd D0 (Lam D0 B0) t0) (Snd D0 (Lam D0 B0) t1) (subst1 B0 F0)
      cSnd = conv-trans (extract c' qSnd) (conv-conv (conv-sym annS) (tyeq-sym qF))
