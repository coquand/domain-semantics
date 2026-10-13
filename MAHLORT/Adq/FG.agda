{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/FG.agda
--
-- The operators f, g in the fundamental lemma (Tarski): the chains
--   f a L  and  g a L c   (annotated applications, MAHLORT/Syntax/Ops),
-- and through them the codes f^, g^ of U_{f,g} and the equations
--   T^(f^(a, b)) = f (T^ a) (\x. T^ b),   T^(g^(a, b, c)) = g ...
-- (the Tarski counterpart of the Russell delta chains).
------------------------------------------------------------------------

module MAHLORT.Adq.FG where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Weaken using (wkTy ; wkTm ; wkCv)
open import MAHLORT.Syntax.CtxConv using (ccTm ; ccCv)
open import MAHLORT.Syntax.Wf using (wfTm)
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Syntax.Ops
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Form
open import MAHLORT.Adq.LamApp
open import MAHLORT.Adq.Delta using (vRel ; substTyPi)
open import MAHLORT.Adq.El
open import MAHLORT.Adq.Codes using (thatR)

private
  arrEq : {n : Num} {G : Ctx n} {a a' : Expr n} -> HasType G a V -> ConvTm G a a' V ->
          TyEq G (Arr (ElV a) V) (Arr (ElV a') V)
  arrEq ha ca = tyeq-Pi (isty-ElV ha) (isty-V w1) (isty-V w1) (tyeq-ElV ca) (tyeq-refl (isty-V w1))
    where w1 = wf-extend (isty-ElV ha)

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  private
    -- a G-conversion, at the two substitutions
    cvH : (E : Env H G s s' rho) {t t' A : Expr g} -> ConvTm G t t' A -> ConvTm H (substExpr s t) (substExpr s' t') (substExpr s A)
    cvH E c = conv-trans (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) c) (fst (fTm s s' (Env.cs E) (Env.wH E) (snd (pCv c))))

  -- f a L : V
  fAppR : (E : Env H G s s' rho) {f f' a a' L L' : Expr g} ->
    HasType G f OpF -> HasType G a V -> HasType G L (Arr (ElV a) V) ->
    ConvTm G a a' V -> ConvTm G L L' (Arr (ElV a) V) ->
    TyRelAt H s s' rho OpF OpF -> TmRelAt H s s' rho f f' OpF ->
    TmRelAt H s s' rho a a V -> TmRelAt H s s' rho a a' V -> TmRelAt H s s' rho L L' (Arr (ElV a) V) ->
    TmRelAt H s s' rho (fApp f a L) (fApp f' a' L') V
  fAppR E {f} {f'} {a} {a'} {L} {L'} hf ha hL ca cL DTf Ff Fad Fa FL =
    appR E {A = Arr (ElV a) V} {A' = Arr (ElV a') V} {B = wkExpr V} {B' = wkExpr V}
      {t = appB V Bf f a} {t' = appB V Bf f' a'} {a = L} {a' = L'}
      hA (isty-V (wf-extend hA)) (arrEq ha ca) (tyeq-refl (isty-V (wf-extend hA)))
      (ty-App (isty-V wG) (bodyF wG) hf ha) (cvH E cL) r1 FL (vRel E)
    where
      wG = Env.wG E
      Bf : Expr (suc g)
      Bf = Arr (Arr (ElV x0) V) V
      hA = arrV (isty-ElV ha)
      VT1 = substTyPi E {A = V} {B = Bf} {N = a} DTf ha Fad
      r1 = appR E {A = V} {A' = V} {B = Bf} {B' = Bf} {t = f} {t' = f'} {a = a} {a' = a'}
             (isty-V wG) (bodyF wG) (tyeq-refl (isty-V wG)) (tyeq-refl (bodyF wG)) hf (cvH E ca) Ff Fa VT1

  -- g a L c : V   (f fixed)
  gAppR : (E : Env H G s s' rho) {f gg gg' a a' L L' c c' : Expr g} ->
    HasType G f OpF -> HasType G gg (OpG f) -> HasType G a V -> HasType G L (Arr (ElV a) V) ->
    HasType G c (ElV (fApp f a L)) ->
    ConvTm G a a' V -> ConvTm G L L' (Arr (ElV a) V) -> ConvTm G c c' (ElV (fApp f a L)) ->
    TyRelAt H s s' rho (OpG f) (OpG f) -> TmRelAt H s s' rho gg gg' (OpG f) ->
    TmRelAt H s s' rho a a V -> TmRelAt H s s' rho a a' V ->
    TmRelAt H s s' rho L L (Arr (ElV a) V) -> TmRelAt H s s' rho L L' (Arr (ElV a) V) ->
    TmRelAt H s s' rho c c' (ElV (fApp f a L)) ->
    TmRelAt H s s' rho (gApp f gg a L c) (gApp f gg' a' L' c') V
  gAppR E {f} {gg} {gg'} {a} {a'} {L} {L'} {c} {c'} hf hg ha hL hc ca cL cc DTg Fg Fad Fa FLd FL Fc =
    appR E {A = ElV (fApp f a L)} {A' = ElV (fApp f a' L')} {B = wkExpr V} {B' = wkExpr V}
      {t = T2} {t' = T2'} {a = c} {a' = c'}
      iFA (isty-V (wf-extend iFA)) (tyeq-ElV (fAppCong hf ha (conv-refl hf) ca cL)) (tyeq-refl (isty-V (wf-extend iFA)))
      dt2 (cvH E cc) r2' Fc (vRel E)
    where
      wG = Env.wG E
      Bg : Expr (suc g)
      Bg = OpGB (wkExpr (wkExpr f))
      hA = arrV (isty-ElV ha)
      wA = wf-extend hA
      fa1 = fAppTy (wkTm hA hf) (wkTm hA ha) (ty-var wA)
      C2 C2' : Expr (suc g)
      C2 = Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V
      C2' = Arr (ElV (fApp (wkExpr f) (wkExpr a') x0)) V
      iC2 = arrV (isty-ElV fa1)
      w5 = wf-extend (isty-ElV fa1)
      qMid : TyEq (extend G (Arr (ElV a) V)) C2 C2'
      qMid = tyeq-Pi (isty-ElV fa1) (isty-V w5) (isty-V w5)
               (tyeq-ElV (fAppCong (wkTm hA hf) (wkTm hA ha) (conv-refl (wkTm hA hf)) (wkCv hA ca) (conv-refl (ty-var wA))))
               (tyeq-refl (isty-V w5))
      T1 = appB V Bg gg a ; T1' = appB V Bg gg' a'
      T2 = appB (Arr (ElV a) V) C2 T1 L ; T2' = appB (Arr (ElV a') V) C2' T1' L'
      dt1 : HasType G T1 (PiB (Arr (ElV a) V) C2)
      dt1 = trHT refl (gAE f a) (ty-App (isty-V wG) (opGBody wG hf) hg ha)
      dt2 : HasType G T2 (Arr (ElV (fApp f a L)) V)
      dt2 = trHT refl (gAFE f a L) (ty-App hA iC2 dt1 hL)
      iFA = isty-ElV (fAppTy hf ha hL)
      VT1 = substTyPi E {A = V} {B = Bg} {N = a} DTg ha Fad
      r1 = appR E {A = V} {A' = V} {B = Bg} {B' = Bg} {t = gg} {t' = gg'} {a = a} {a' = a'}
             (isty-V wG) (opGBody wG hf) (tyeq-refl (isty-V wG)) (tyeq-refl (opGBody wG hf)) hg (cvH E ca) Fg Fa VT1
      r1' = transport (\ X -> TmRelAt H s s' rho T1 T1' X) (gAE f a) r1
      VT1' = transport (\ X -> TyRelAt H s s' rho X X) (gAE f a) VT1
      VT2 = substTyPi E {A = Arr (ElV a) V} {B = C2} {N = L} VT1' hL FLd
      r2 = appR E {A = Arr (ElV a) V} {A' = Arr (ElV a') V} {B = C2} {B' = C2'} {t = T1} {t' = T1'} {a = L} {a' = L'}
             hA iC2 (arrEq ha ca) qMid dt1 (cvH E cL) r1' FL VT2
      r2' = transport (\ X -> TmRelAt H s s' rho T2 T2' X) (gAFE f a L) r2

------------------------------------------------------------------------
-- the codes f^, g^ and the equations of T^ on them
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- the family \x:T_V(T^ a). T^ b  of the code, two-sided
  module Fam (E : Env H G s s' rho) {f0 g0 a a' : Expr g} {b b' : Expr (suc g)} (iU : IsType G (TyU f0 g0))
    (ha : HasType G a (TyU f0 g0)) (ha' : HasType G a' (TyU f0 g0))
    (hb : HasType (extend G (ElU f0 g0 a)) b (wkExpr (TyU f0 g0))) (hb' : HasType (extend G (ElU f0 g0 a)) b' (wkExpr (TyU f0 g0)))
    (ca : ConvTm G a a' (TyU f0 g0)) (cb : ConvTm (extend G (ElU f0 g0 a)) b b' (wkExpr (TyU f0 g0)))
    (Fad : TmRelAt H s s' rho a a (TyU f0 g0))
    (Fbd : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
           TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b (wkExpr (TyU f0 g0)))
    (Fb : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
          TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b' (wkExpr (TyU f0 g0))) where

    X = ElU f0 g0 a
    Y = ElV (That a) ; Y' = ElV (That a')
    iY = isty-ElV (ty-That ha) ; iY' = isty-ElV (ty-That ha')
    qXY = tyeq-ElU-That ha
    qA : TyEq G Y Y'
    qA = tyeq-ElV (conv-That ca)
    hbY : HasType (extend G Y) b (wkExpr (TyU f0 g0))
    hbY = ccTm iY (tyeq-sym qXY) hb
    hb'Y : HasType (extend G Y) b' (wkExpr (TyU f0 g0))
    hb'Y = ccTm iY (tyeq-sym qXY) hb'
    hb'X' : HasType (extend G (ElU f0 g0 a')) b' (wkExpr (TyU f0 g0))
    hb'X' = ccTm (isty-ElU ha') (tyeq-ElU (conv-sym ca)) hb'
    cbY = ccCv iY (tyeq-sym qXY) cb
    iUw = wkTy (isty-ElU ha) iU
    iV1 = isty-V (wf-extend iY)
    L = Lam Y (That b) ; L' = Lam Y' (That b')
    hL : HasType G L (Arr Y V)
    hL = ty-Lam iY iV1 (ty-That hbY)
    cL : ConvTm G L L' (Arr Y V)
    cL = conv-Lam iY iV1 qA (conv-That cbY)
    FL : TmRelAt H s s' rho L L' (Arr Y V)
    FL = lamR E {A = Y} {A' = Y'} {B = wkExpr V} {t = That b} {t' = That b'} iY iV1 (ty-That hbY) iY' qA (ty-That hb'Y)
           (elTyU E {M = a} {M' = a} iU Fad) (\ E' -> vRel E')
           (\ E' -> thatR (envElU ha E') {a = b} {a' = b'} iUw (Fb (envElU ha E')))
    FLd : TmRelAt H s s' rho L L (Arr Y V)
    FLd = lamR E {A = Y} {A' = Y} {B = wkExpr V} {t = That b} {t' = That b} iY iV1 (ty-That hbY) iY (tyeq-refl iY) (ty-That hbY)
            (elTyU E {M = a} {M' = a} iU Fad) (\ E' -> vRel E')
            (\ E' -> thatR (envElU ha E') {a = b} {a' = b} iUw (Fbd (envElU ha E')))

  private
    one : {n : Num} {P Q : Expr n} -> HR P Q -> AR P Q
    one r = ar-hrs (hrs-step r hrs-refl)
    -- the head step of T^ g^ lands on gApp up to the annotations (which contain weakenings of f)
    oneG : {n : Num} {P Q Q' : Expr n} -> HR P Q -> Ann Q Q' -> AR P Q'
    oneG r p = ar-post (hrs-step r hrs-refl) p

  module FhatC (E : Env H G s s' rho) {f0 g0 a a' : Expr g} {b b' : Expr (suc g)} (iU : IsType G (TyU f0 g0))
    (hf : HasType G f0 OpF) (hg : HasType G g0 (OpG f0))
    (ha : HasType G a (TyU f0 g0)) (ha' : HasType G a' (TyU f0 g0))
    (hb : HasType (extend G (ElU f0 g0 a)) b (wkExpr (TyU f0 g0))) (hb' : HasType (extend G (ElU f0 g0 a)) b' (wkExpr (TyU f0 g0)))
    (ca : ConvTm G a a' (TyU f0 g0)) (cb : ConvTm (extend G (ElU f0 g0 a)) b b' (wkExpr (TyU f0 g0)))
    (DTf : TyRelAt H s s' rho OpF OpF) (Ff : TmRelAt H s s' rho f0 f0 OpF)
    (Fad : TmRelAt H s s' rho a a (TyU f0 g0)) (Fa : TmRelAt H s s' rho a a' (TyU f0 g0))
    (Fbd : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
           TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b (wkExpr (TyU f0 g0)))
    (Fb : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
          TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b' (wkExpr (TyU f0 g0))) where

    open Fam E iU ha ha' hb hb' ca cb Fad Fbd Fb public
    wH = Env.wH E ; cs = Env.cs E

    RF : TmRelAt H s s' rho (fApp f0 (That a) L) (fApp f0 (That a') L') V
    RF = fAppR E {f' = f0} hf (ty-That ha) hL (conv-That ca) cL DTf Ff (thatR E {a = a} {a' = a} iU Fad) (thatR E {a = a} {a' = a'} iU Fa) FL

    qF : (r : Sub h g) -> WtSub H G r -> {aa : Expr g} {bb : Expr (suc g)} -> HasType G aa (TyU f0 g0) ->
      HasType (extend G (ElU f0 g0 aa)) bb (wkExpr (TyU f0 g0)) ->
      TyEq H (substExpr r (ElV (That (Fhat f0 g0 aa (Lam (ElU f0 g0 aa) bb)))))
             (substExpr r (ElV (fApp f0 (That aa) (Lam (ElV (That aa)) (That bb)))))
    qF r wr h1 h2 = sbTE r wr wH (tyeq-ElV (conv-That-Fhat hf hg h1 h2))

    fhatR : TmRelAt H s s' rho (Fhat f0 g0 a (Lam X b)) (Fhat f0 g0 a' (Lam (ElU f0 g0 a') b')) (TyU f0 g0)
    fhatR = tmU E {M = Fhat f0 g0 a (Lam X b)} {M' = Fhat f0 g0 a' (Lam (ElU f0 g0 a') b')} iU
              (\ c ec cU -> pExpT c (one (hr-ElV hr-That-Fhat)) (qF s (CSub.w1 cs) ha hb)
                              (pExpT' c (one (hr-ElV hr-That-Fhat)) (qF s' (CSub.w2 cs) ha' hb'X')
                                 (elTyV E {M = fApp f0 (That a) L} {M' = fApp f0 (That a') L'} RF c ec cU)))

    -- T^ (f^ (a, b)) = f (T^ a) (\x. T^ b)
    fhatEqR : TmRelAt H s s' rho (That (Fhat f0 g0 a (Lam X b))) (fApp f0 (That a') L') V
    fhatEqR = tmV E {M = That (Fhat f0 g0 a (Lam X b))} {M' = fApp f0 (That a') L'}
                (\ c ec cU -> pExpT c (one (hr-ElV hr-That-Fhat)) (qF s (CSub.w1 cs) ha hb)
                                (elTyV E {M = fApp f0 (That a) L} {M' = fApp f0 (That a') L'} RF c ec cU))

  module GhatC (E : Env H G s s' rho) {f0 g0 a a' cc0 cc0' : Expr g} {b b' : Expr (suc g)} (iU : IsType G (TyU f0 g0))
    (hf : HasType G f0 OpF) (hg : HasType G g0 (OpG f0))
    (ha : HasType G a (TyU f0 g0)) (ha' : HasType G a' (TyU f0 g0))
    (hb : HasType (extend G (ElU f0 g0 a)) b (wkExpr (TyU f0 g0))) (hb' : HasType (extend G (ElU f0 g0 a)) b' (wkExpr (TyU f0 g0)))
    (hc : HasType G cc0 (ElU f0 g0 (Fhat f0 g0 a (Lam (ElU f0 g0 a) b))))
    (ca : ConvTm G a a' (TyU f0 g0)) (cb : ConvTm (extend G (ElU f0 g0 a)) b b' (wkExpr (TyU f0 g0)))
    (ccv : ConvTm G cc0 cc0' (ElU f0 g0 (Fhat f0 g0 a (Lam (ElU f0 g0 a) b))))
    (DTg : TyRelAt H s s' rho (OpG f0) (OpG f0)) (Fg : TmRelAt H s s' rho g0 g0 (OpG f0))
    (Fad : TmRelAt H s s' rho a a (TyU f0 g0)) (Fa : TmRelAt H s s' rho a a' (TyU f0 g0))
    (Fbd : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
           TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b (wkExpr (TyU f0 g0)))
    (Fb : {N1 N2 : Expr h} {w : FinEl} -> Env H (extend G (ElU f0 g0 a)) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
          TmRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) b b' (wkExpr (TyU f0 g0)))
    (Fc : TmRelAt H s s' rho cc0 cc0' (ElU f0 g0 (Fhat f0 g0 a (Lam (ElU f0 g0 a) b))))
    -- the type of c, as El_U and as El_V(f ...), under the left substitution
    (Rq : TyRelAt H s s rho (ElU f0 g0 (Fhat f0 g0 a (Lam (ElU f0 g0 a) b)))
                             (ElV (fApp f0 (That a) (Lam (ElV (That a)) (That b))))) where

    open Fam E iU ha ha' hb hb' ca cb Fad Fbd Fb public
    wH = Env.wH E ; cs = Env.cs E

    qc : TyEq G (ElU f0 g0 (Fhat f0 g0 a (Lam X b))) (ElV (fApp f0 (That a) L))
    qc = tyeq-trans (tyeq-ElU-That (ty-Fhat hf hg ha hb)) (tyeq-ElV (conv-That-Fhat hf hg ha hb))

    Fc' : TmRelAt H s s' rho cc0 cc0' (ElV (fApp f0 (That a) L))
    Fc' a0 u e aU eu ua = pConvM u a0 ua aU (Rq a0 e aU) (Fc a0 u e aU eu ua)

    RG : TmRelAt H s s' rho (gApp f0 g0 (That a) L cc0) (gApp f0 g0 (That a') L' cc0') V
    RG = gAppR E {gg' = g0} hf hg (ty-That ha) hL (ty-conv hc qc) (conv-That ca) cL (conv-conv ccv qc) DTg Fg
           (thatR E {a = a} {a' = a} iU Fad) (thatR E {a = a} {a' = a'} iU Fa) FLd FL Fc'

    qG : (r : Sub h g) -> WtSub H G r -> {aa cx : Expr g} {bb : Expr (suc g)} -> HasType G aa (TyU f0 g0) ->
      HasType (extend G (ElU f0 g0 aa)) bb (wkExpr (TyU f0 g0)) ->
      HasType G cx (ElU f0 g0 (Fhat f0 g0 aa (Lam (ElU f0 g0 aa) bb))) ->
      TyEq H (substExpr r (ElV (That (Ghat f0 g0 aa (Lam (ElU f0 g0 aa) bb) cx))))
             (substExpr r (ElV (gApp f0 g0 (That aa) (Lam (ElV (That aa)) (That bb)) cx)))
    qG r wr h1 h2 h3 = sbTE r wr wH (tyeq-ElV (conv-That-Ghat hf hg h1 h2 h3))

    hc'X' : HasType G cc0' (ElU f0 g0 (Fhat f0 g0 a' (Lam (ElU f0 g0 a') b')))
    hc'X' = ty-conv (snd (pCv ccv)) (tyeq-ElU (conv-Fhat hf hg ha hb hb' ca cb))

    ghatR : TmRelAt H s s' rho (Ghat f0 g0 a (Lam X b) cc0) (Ghat f0 g0 a' (Lam (ElU f0 g0 a') b') cc0') (TyU f0 g0)
    ghatR = tmU E {M = Ghat f0 g0 a (Lam X b) cc0} {M' = Ghat f0 g0 a' (Lam (ElU f0 g0 a') b') cc0'} iU
              (\ c ec cU -> pExpT c (oneG (hr-ElV hr-That-Ghat) (ann-ElV (ann-app (ann-app (ann-app ann-refl))))) (qG s (CSub.w1 cs) ha hb hc)
                              (pExpT' c (oneG (hr-ElV hr-That-Ghat) (ann-ElV (ann-app (ann-app (ann-app ann-refl))))) (qG s' (CSub.w2 cs) ha' hb'X' hc'X')
                                 (elTyV E {M = gApp f0 g0 (That a) L cc0} {M' = gApp f0 g0 (That a') L' cc0'} RG c ec cU)))

    -- T^ (g^ (a, b, c)) = g (T^ a) (\x. T^ b) c
    ghatEqR : TmRelAt H s s' rho (That (Ghat f0 g0 a (Lam X b) cc0)) (gApp f0 g0 (That a') L' cc0') V
    ghatEqR = tmV E {M = That (Ghat f0 g0 a (Lam X b) cc0)} {M' = gApp f0 g0 (That a') L' cc0'}
                (\ c ec cU -> pExpT c (oneG (hr-ElV hr-That-Ghat) (ann-ElV (ann-app (ann-app (ann-app ann-refl))))) (qG s (CSub.w1 cs) ha hb hc)
                                (elTyV E {M = gApp f0 g0 (That a) L cc0} {M' = gApp f0 g0 (That a') L' cc0'} RG c ec cU))
