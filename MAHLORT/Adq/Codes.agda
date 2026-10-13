{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Codes.agda
--
-- Case lemmas of the fundamental lemma for the Tarski universes:
-- the types U_{f,g}, the codes in V (Pi^_V, Sigma^_V, N^_V, U^) and in
-- U_{f,g} (Pi^_U, Sigma^_U, N^_U), the embedding T^ and reflection.
-- A code is related through its decoding, which reduces (El_V, T^) to
-- the type it codes; that type is related by formation (MAHLORT/Adq/
-- Form), and the decoding by head expansion.
------------------------------------------------------------------------

module MAHLORT.Adq.Codes where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLOINJ.Model.Comb using (AtomS)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Weaken using (wkTy)
open import MAHLORT.Syntax.CtxConv using (ccTm ; ccCv)
open import MAHLORT.Syntax.Wf using (wfTm ; NatTy)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Form
open import MAHLORT.Adq.El

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  private
    one : {n : Num} {X Y : Expr n} -> HR X Y -> AR X Y
    one r = ar-hrs (hrs-step r hrs-refl)
    two : {n : Num} {X Y Z : Expr n} -> HR X Y -> HR Y Z -> AR X Z
    two r r' = ar-hrs (hrs-step r (hrs-step r' hrs-refl))

  -- the types U_{f,g}
  tyUR : (E : Env H G s s' rho) {f0 g0 f1 g1 : Expr g} -> IsType G (TyU f0 g0) -> IsType G (TyU f1 g1) ->
    TyRelAt H s s' rho (TyU f0 g0) (TyU f1 g1)
  tyUR E iU iU' c ec cU =
    uTy (univR (univ-U _ _ refl) (sbTy s (CSub.w1 (Env.cs E)) (Env.wH E) iU))
        (univR (univ-U _ _ refl) (sbTy s' (CSub.w2 (Env.cs E)) (Env.wH E) iU')) kU c ec

  -- T^
  thatR : (E : Env H G s s' rho) {f0 g0 a a' : Expr g} -> IsType G (TyU f0 g0) ->
    TmRelAt H s s' rho a a' (TyU f0 g0) -> TmRelAt H s s' rho (That a) (That a') V
  thatR E {a = a} {a'} iU F = tmV E {M = That a} {M' = That a'} (elTyU E {M = a} {M' = a'} iU F)

  -- reflection
  reflR : (E : Env H G s s' rho) {f0 g0 a a' : Expr g} -> IsType G (TyU f0 g0) ->
    TmRelAt H s s' rho (That a) (That a') V -> TmRelAt H s s' rho a a' (TyU f0 g0)
  reflR E {a = a} {a'} iU F = tmU E {M = a} {M' = a'} iU (elTyV E {M = That a} {M' = That a'} F)

  -- N^_V and N^_U
  natVR : (E : Env H G s s' rho) -> TmRelAt H s s' rho NatV NatV V
  natVR E = tmV E {M = NatV} {M' = NatV} (\ c ec cU -> pExpT c (one hr-El-NatV) q (pExpT' c (one hr-El-NatV) q (natTy (NatTy wH) c ec)))
    where wH = Env.wH E ; q = tyeq-El-NatV wH

  natUR : (E : Env H G s s' rho) {f0 g0 : Expr g} -> IsType G (TyU f0 g0) -> TmRelAt H s s' rho (NatU f0 g0) (NatU f0 g0) (TyU f0 g0)
  natUR E {f0} {g0} iU =
    tmU E {M = NatU f0 g0} {M' = NatU f0 g0} iU (\ c ec cU -> pExpT c (two (hr-ElV hr-That-NatU) hr-El-NatV) (q s (CSub.w1 cs))
                             (pExpT' c (two (hr-ElV hr-That-NatU) hr-El-NatV) (q s' (CSub.w2 cs)) (natTy (NatTy wH) c ec)))
    where
      wH = Env.wH E ; cs = Env.cs E
      q : (r : Sub h g) -> WtSub H G r -> TyEq H (substExpr r (ElV (That (NatU f0 g0)))) Nat
      q r wr = sbTE r wr wH (tyeq-trans (tyeq-ElV (conv-That-NatU iU)) (tyeq-El-NatV (wfTm (conv-That-NatU' iU))))
        where
          conv-That-NatU' : IsType G (TyU f0 g0) -> HasType G NatV V
          conv-That-NatU' i = ty-NatV (wfTy' i)
            where
              wfTy' : IsType G (TyU f0 g0) -> WfCtx G
              wfTy' (isty-TyU hf hg) = wfTm hf

  -- U^_{f,g}
  uvR : (E : Env H G s s' rho) {f0 g0 f1 g1 : Expr g} ->
    HasType G f0 OpF -> HasType G g0 (OpG f0) -> HasType G f1 OpF -> HasType G g1 (OpG f1) ->
    TmRelAt H s s' rho (UV f0 g0) (UV f1 g1) V
  uvR E {f0} {g0} {f1} {g1} hf hg hf' hg' =
    tmV E {M = UV f0 g0} {M' = UV f1 g1} (\ c ec cU -> pExpT c (one hr-El-UV) (sbTE s (CSub.w1 cs) wH (tyeq-El-UV hf hg))
                          (pExpT' c (one hr-El-UV) (sbTE s' (CSub.w2 cs) wH (tyeq-El-UV hf' hg'))
                             (tyUR E (isty-TyU hf hg) (isty-TyU hf' hg') c ec cU)))
    where wH = Env.wH E ; cs = Env.cs E

  -- Pi^_V and Sigma^_V, two-sided
  module CodeV (E : Env H G s s' rho) {a a' : Expr g} {b b' : Expr (suc g)}
    (ha : HasType G a V) (ha' : HasType G a' V) (hb : HasType (extend G (ElV a)) b V) (hb' : HasType (extend G (ElV a)) b' V)
    (ca : ConvTm G a a' V) (cb : ConvTm (extend G (ElV a)) b b' V)
    (Fad : TmRelAt H s s' rho a a V) (Fa : TmRelAt H s s' rho a a' V)
    (Fb : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElV a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
          TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b' V) where

    private
      wH = Env.wH E ; cs = Env.cs E
      iA = isty-ElV ha ; iA' = isty-ElV ha'
      qA = tyeq-ElV ca
      hb'' : HasType (extend G (ElV a')) b' V
      hb'' = ccTm iA' (tyeq-sym qA) hb'
      module FX = FormX E {A = ElV a} {A' = ElV a'} {B = ElV b} {B' = ElV b'} iA (isty-ElV hb) iA' (isty-ElV hb'')
                    qA (tyeq-ElV cb) (elTyV E {M = a} {M' = a} Fad) (elTyV E {M = a} {M' = a'} Fa) (\ E' -> elTyV E' {M = b} {M' = b'} (Fb E'))

    piVR : TmRelAt H s s' rho (PiV a (Lam (ElV a) b)) (PiV a' (Lam (ElV a') b')) V
    piVR = tmV E {M = PiV a (Lam (ElV a) b)} {M' = PiV a' (Lam (ElV a') b')} (\ c ec cU -> pExpT c (one hr-El-PiV) (sbTE s (CSub.w1 cs) wH (tyeq-El-PiV ha hb))
                                 (pExpT' c (one hr-El-PiV) (sbTE s' (CSub.w2 cs) wH (tyeq-El-PiV ha' hb'')) (FX.piR c ec cU)))

    sigVR : TmRelAt H s s' rho (SigV a (Lam (ElV a) b)) (SigV a' (Lam (ElV a') b')) V
    sigVR = tmV E {M = SigV a (Lam (ElV a) b)} {M' = SigV a' (Lam (ElV a') b')} (\ c ec cU -> pExpT c (one hr-El-SigV) (sbTE s (CSub.w1 cs) wH (tyeq-El-SigV ha hb))
                                  (pExpT' c (one hr-El-SigV) (sbTE s' (CSub.w2 cs) wH (tyeq-El-SigV ha' hb'')) (FX.sigR c ec cU)))

    -- the decoded types, for the type equalities El_V(Pi^ a b) = Pi(El_V a, El_V b)
    piTyR : TyRelAt H s s' rho (PiB (ElV a) (ElV b)) (PiB (ElV a') (ElV b'))
    piTyR = FX.piR
    sigTyR : TyRelAt H s s' rho (SigmaB (ElV a) (ElV b)) (SigmaB (ElV a') (ElV b'))
    sigTyR = FX.sigR

  -- Pi^_U and Sigma^_U, two-sided (f, g fixed)
  module CodeU (E : Env H G s s' rho) {f0 g0 a a' : Expr g} {b b' : Expr (suc g)} (iU : IsType G (TyU f0 g0))
    (ha : HasType G a (TyU f0 g0)) (ha' : HasType G a' (TyU f0 g0))
    (hb : HasType (extend G (ElU f0 g0 a)) b (wkExpr (TyU f0 g0))) (hb' : HasType (extend G (ElU f0 g0 a)) b' (wkExpr (TyU f0 g0)))
    (ca : ConvTm G a a' (TyU f0 g0)) (cb : ConvTm (extend G (ElU f0 g0 a)) b b' (wkExpr (TyU f0 g0)))
    (Fad : TmRelAt H s s' rho a a (TyU f0 g0)) (Fa : TmRelAt H s s' rho a a' (TyU f0 g0))
    (Fb : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
          TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b' (wkExpr (TyU f0 g0))) where

    private
      wH = Env.wH E ; cs = Env.cs E
      X = ElU f0 g0 a
      Y = ElV (That a) ; Y' = ElV (That a')
      iY = isty-ElV (ty-That ha) ; iY' = isty-ElV (ty-That ha')
      qXY = tyeq-ElU-That ha
      qA : TyEq G Y Y'
      qA = tyeq-ElV (conv-That ca)
      hbY : HasType (extend G Y) b (wkExpr (TyU f0 g0))
      hbY = ccTm iY (tyeq-sym qXY) hb
      cbY : ConvTm (extend G Y) b b' (wkExpr (TyU f0 g0))
      cbY = ccCv iY (tyeq-sym qXY) cb
      hb'Y' : HasType (extend G Y') b' (wkExpr (TyU f0 g0))
      hb'Y' = ccTm iY' (tyeq-trans (tyeq-sym qA) (tyeq-sym qXY)) hb'
      hb'X' : HasType (extend G (ElU f0 g0 a')) b' (wkExpr (TyU f0 g0))
      hb'X' = ccTm (isty-ElU ha') (tyeq-ElU (conv-sym ca)) hb'
      iUw = wkTy (isty-ElU ha) iU
      module FX = FormX E {A = Y} {A' = Y'} {B = ElV (That b)} {B' = ElV (That b')} iY (isty-ElV (ty-That hbY))
                    iY' (isty-ElV (ty-That hb'Y')) qA (tyeq-ElV (conv-That cbY))
                    (elTyU E {M = a} {M' = a} iU Fad) (elTyU E {M = a} {M' = a'} iU Fa)
                    (\ E' -> elTyU (envElU ha E') {M = b} {M' = b'} iUw (Fb (envElU ha E')))
      qPi : (r : Sub h g) -> WtSub H G r -> {aa : Expr g} {bb : Expr (suc g)} -> HasType G aa (TyU f0 g0) ->
        HasType (extend G (ElU f0 g0 aa)) bb (wkExpr (TyU f0 g0)) -> HasType (extend G (ElV (That aa))) bb (wkExpr (TyU f0 g0)) ->
        TyEq H (substExpr r (ElV (That (PiU f0 g0 aa (Lam (ElU f0 g0 aa) bb))))) (substExpr r (PiB (ElV (That aa)) (ElV (That bb))))
      qPi r wr h1 h2 h3 = sbTE r wr wH (tyeq-trans (tyeq-ElV (conv-That-PiU h1 h2)) (tyeq-El-PiV (ty-That h1) (ty-That h3)))
      qSig : (r : Sub h g) -> WtSub H G r -> {aa : Expr g} {bb : Expr (suc g)} -> HasType G aa (TyU f0 g0) ->
        HasType (extend G (ElU f0 g0 aa)) bb (wkExpr (TyU f0 g0)) -> HasType (extend G (ElV (That aa))) bb (wkExpr (TyU f0 g0)) ->
        TyEq H (substExpr r (ElV (That (SigU f0 g0 aa (Lam (ElU f0 g0 aa) bb))))) (substExpr r (SigmaB (ElV (That aa)) (ElV (That bb))))
      qSig r wr h1 h2 h3 = sbTE r wr wH (tyeq-trans (tyeq-ElV (conv-That-SigU h1 h2)) (tyeq-El-SigV (ty-That h1) (ty-That h3)))

    piUR : TmRelAt H s s' rho (PiU f0 g0 a (Lam (ElU f0 g0 a) b)) (PiU f0 g0 a' (Lam (ElU f0 g0 a') b')) (TyU f0 g0)
    piUR = tmU E {M = PiU f0 g0 a (Lam (ElU f0 g0 a) b)} {M' = PiU f0 g0 a' (Lam (ElU f0 g0 a') b')} iU (\ c ec cU -> pExpT c (two (hr-ElV hr-That-PiU) hr-El-PiV) (qPi s (CSub.w1 cs) ha hb hbY)
                                    (pExpT' c (two (hr-ElV hr-That-PiU) hr-El-PiV) (qPi s' (CSub.w2 cs) ha' hb'X' hb'Y')
                                       (FX.piR c ec cU)))

    sigUR : TmRelAt H s s' rho (SigU f0 g0 a (Lam (ElU f0 g0 a) b)) (SigU f0 g0 a' (Lam (ElU f0 g0 a') b')) (TyU f0 g0)
    sigUR = tmU E {M = SigU f0 g0 a (Lam (ElU f0 g0 a) b)} {M' = SigU f0 g0 a' (Lam (ElU f0 g0 a') b')} iU (\ c ec cU -> pExpT c (two (hr-ElV hr-That-SigU) hr-El-SigV) (qSig s (CSub.w1 cs) ha hb hbY)
                                     (pExpT' c (two (hr-ElV hr-That-SigU) hr-El-SigV) (qSig s' (CSub.w2 cs) ha' hb'X' hb'Y')
                                        (FX.sigR c ec cU)))
