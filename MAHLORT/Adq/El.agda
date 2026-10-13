{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/El.agda
--
-- Decoding in the fundamental lemma (Tarski):
--   * an element of V (resp. of U_{f,g}) is related iff its decoding
--     El_V M (resp. El_V (T^ M)) is related as a type;
--   * El_U f g a and El_V (T^ a) are one head step apart and have the
--     same erasure, so related substitutions over a context ending in
--     one of them are related over the context ending in the other.
------------------------------------------------------------------------

module MAHLORT.Adq.El where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (FinMem ; NotBot)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (AtomS ; bot-or)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Weaken using (wkTE)
open import MAHLORT.Syntax.Presup using (pTm)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Delta using (tmBot)

private
  hrElU : {n : Num} {f g a : Expr n} -> AR (ElU f g a) (ElV (That a))
  hrElU = ar-hrs (hrs-step hr-ElU hrs-refl)

------------------------------------------------------------------------
-- elements of V and of U_{f,g}, through their decodings
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- El_V of related elements of V
  elTyV : (E : Env H G s s' rho) {M M' : Expr g} -> TmRelAt H s s' rho M M' V -> TyRelAt H s s' rho (ElV M) (ElV M')
  elTyV E {M} {M'} F u eu uU =
    elTyR {H = H} {M = substExpr s M} {M' = substExpr s' M'} {T = V} u (F UCode u (mkSigma tt tt) tt eu uU)
      (univR (univ-V refl) (isty-V (Env.wH E)))

  -- El_V (T^ -) of related elements of U_{f,g}
  elTyU : (E : Env H G s s' rho) {f0 g0 M M' : Expr g} -> IsType G (TyU f0 g0) ->
    TmRelAt H s s' rho M M' (TyU f0 g0) -> TyRelAt H s s' rho (ElV (That M)) (ElV (That M'))
  elTyU E {f0} {g0} {M} {M'} iU F u eu uU =
    elTyR {H = H} {M = substExpr s M} {M' = substExpr s' M'} {T = substExpr s (TyU f0 g0)} u (F UCode u (mkSigma tt tt) tt eu uU)
      (univR (univ-U _ _ refl) (sbTy s (CSub.w1 (Env.cs E)) (Env.wH E) iU))

  -- related elements of V, from related decodings
  tmV : (E : Env H G s s' rho) {M M' : Expr g} -> TyRelAt H s s' rho (ElV M) (ElV M') -> TmRelAt H s s' rho M M' V
  tmV E {M} {M'} R a u ea aU eu ua = go a ea ua
    where
      go : (a : FinEl) -> AtomS UCode a -> FinMem u a -> RTm H (substExpr s M) (substExpr s' M') V u a
      go Bot e m = tmBot u
      go UCode e m = elM u (univR (univ-V refl) (isty-V (Env.wH E))) (R u eu m)
      go (D.FunEl _) (mkSigma _ ()) m
      go (D.PiCode _ _) (mkSigma _ ()) m
      go D.NatCode (mkSigma _ ()) m
      go D.ZeroEl (mkSigma _ ()) m
      go (D.SucEl _) (mkSigma _ ()) m
      go (D.PairEl _ _) (mkSigma _ ()) m
      go (D.SigmaCode _ _) (mkSigma _ ()) m

  -- related elements of U_{f,g}, from related decodings
  tmU : (E : Env H G s s' rho) {f0 g0 M M' : Expr g} -> IsType G (TyU f0 g0) ->
    TyRelAt H s s' rho (ElV (That M)) (ElV (That M')) -> TmRelAt H s s' rho M M' (TyU f0 g0)
  tmU E {f0} {g0} {M} {M'} iU R a u ea aU eu ua = go a ea ua
    where
      go : (a : FinEl) -> AtomS UCode a -> FinMem u a -> RTm H (substExpr s M) (substExpr s' M') (substExpr s (TyU f0 g0)) u a
      go Bot e m = tmBot u
      go UCode e m = elM u (univR (univ-U _ _ refl) (sbTy s (CSub.w1 (Env.cs E)) (Env.wH E) iU)) (R u eu m)
      go (D.FunEl _) (mkSigma _ ()) m
      go (D.PiCode _ _) (mkSigma _ ()) m
      go D.NatCode (mkSigma _ ()) m
      go D.ZeroEl (mkSigma _ ()) m
      go (D.SucEl _) (mkSigma _ ()) m
      go (D.PairEl _ _) (mkSigma _ ()) m
      go (D.SigmaCode _ _) (mkSigma _ ()) m

  -- El_U f g a, from El_V (T^ a)
  elUTy : (E : Env H G s s' rho) {f0 g0 a a' : Expr g} -> HasType G a (TyU f0 g0) -> HasType G a' (TyU f0 g0) ->
    TyRelAt H s s' rho (ElV (That a)) (ElV (That a')) -> TyRelAt H s s' rho (ElU f0 g0 a) (ElU f0 g0 a')
  elUTy E {f0} {g0} {a} {a'} ha ha' R c ec cU =
    pExpT c hrElU (sbTE s w1 wH (tyeq-ElU-That ha))
      (pExpT' c hrElU (sbTE s' w2 wH (tyeq-ElU-That ha')) (R c ec cU))
    where wH = Env.wH E ; w1 = CSub.w1 (Env.cs E) ; w2 = CSub.w2 (Env.cs E)

------------------------------------------------------------------------
-- retyping the last context entry:  El_V (T^ a)  to  El_U f g a
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {f0 g0 a : Expr g} (ha : HasType G a (TyU f0 g0))
         {s s' : Sub h (suc g)} {rho : EnvApprox (suc g)} where

  private
    X = ElU f0 g0 a
    Y = ElV (That a)
    iX = isty-ElU ha
    iY = isty-ElV (ty-That ha)
    qYX : TyEq G Y X
    qYX = tyeq-sym (tyeq-ElU-That ha)

  envElU : Env H (extend G Y) s s' rho -> Env H (extend G X) s s' rho
  envElU E = mkEnv (mkSR cs' ty' tm') (Env.fits E) wH (wf-extend iX)
    where
      wH = Env.wH E ; cs = Env.cs E ; sr = Env.sr E
      qW : TyEq (extend G Y) (wkExpr Y) (wkExpr X)
      qW = wkTE iY qYX
      ql : TyEq H (substExpr s (wkExpr Y)) (substExpr s (wkExpr X))
      ql = sbTE s (CSub.w1 cs) wH qW
      qr : TyEq H (substExpr s' (wkExpr Y)) (substExpr s' (wkExpr X))
      qr = sbTE s' (CSub.w2 cs) wH qW
      w1' : (i : Fin (suc g)) -> HasType H (s i) (substExpr s (lookup (extend G X) i))
      w1' fzero = ty-conv (CSub.w1 cs fzero) ql
      w1' (fsuc i) = CSub.w1 cs (fsuc i)
      w2' : (i : Fin (suc g)) -> HasType H (s' i) (substExpr s' (lookup (extend G X) i))
      w2' fzero = ty-conv (CSub.w2 cs fzero) qr
      w2' (fsuc i) = CSub.w2 cs (fsuc i)
      cv' : (i : Fin (suc g)) -> ConvTm H (s i) (s' i) (substExpr s (lookup (extend G X) i))
      cv' fzero = conv-conv (CSub.cv cs fzero) ql
      cv' (fsuc i) = CSub.cv cs (fsuc i)
      te' : (i : Fin (suc g)) -> TyEq H (substExpr s (lookup (extend G X) i)) (substExpr s' (lookup (extend G X) i))
      te' fzero = tyeq-trans (tyeq-sym ql) (tyeq-trans (CSub.te cs fzero) qr)
      te' (fsuc i) = CSub.te cs (fsuc i)
      cs' = csub w1' w2' cv' te'
      -- the type relation at the new entry: one head step on each side
      hX : AR (substExpr s (wkExpr X)) (substExpr s (wkExpr Y))
      hX = ar-hrs (hrs-step hr-ElU hrs-refl)
      hX' : AR (substExpr s' (wkExpr X)) (substExpr s' (wkExpr Y))
      hX' = ar-hrs (hrs-step hr-ElU hrs-refl)
      ty' : (i : Fin (suc g)) (c : FinEl) -> EvalRel (lookup (extend G X) i) rho c -> FinMem c UCode ->
            RTy H (substExpr s (lookup (extend G X) i)) (substExpr s' (lookup (extend G X) i)) c
      ty' fzero c e cU = pExpT c hX (tyeq-sym ql) (pExpT' c hX' (tyeq-sym qr) (SR.ty sr fzero c e cU))
      ty' (fsuc i) c e cU = SR.ty sr (fsuc i) c e cU
      tm' : (i : Fin (suc g)) (c : FinEl) -> EvalRel (lookup (extend G X) i) rho c -> FinMem c UCode ->
            FinMem (lookupEnv i rho) c ->
            RTm H (s i) (s' i) (substExpr s (lookup (extend G X) i)) (lookupEnv i rho) c
      tm' fzero c e cU m =
        pConvM (lookupEnv fzero rho) c m cU
          (pExpT' c hX (tyeq-sym ql) (diagL c cU (SR.ty sr fzero c e cU)))
          (SR.tm sr fzero c e cU m)
      tm' (fsuc i) c e cU m = SR.tm sr (fsuc i) c e cU m
