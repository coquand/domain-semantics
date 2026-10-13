{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Fund.agda
--
-- The fundamental lemma for the Tarski theory: every derivable
-- judgement is valid in the logical relation, for every pair of
-- related substitutions over an approximation of the context.  By
-- mutual structural induction on the derivations (the Tarski port of
-- MAHLOINJ/Adq/Fund); the type of a term judgement is related as well.
-- Every case lemma receives the induction hypotheses as functions; no
-- recursion on constructed derivations.
------------------------------------------------------------------------

module MAHLORT.Adq.Fund where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (LeCode ; FinMem ; NotBot)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-elim)
open import MAHLORT.Model
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Weaken using (wkTy)
open import MAHLORT.Syntax.Wf using (NatTy ; wfTm)
open import MAHLORT.Syntax.CtxConv using (ccTy ; ccTm)
open import MAHLORT.Syntax.Presup using (pCv ; pTm ; pTE)
open import MAHLORT.Syntax.Ops using (opGEq)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLORT.Adq.Env
open import MAHLORT.Adq.Form
open import MAHLORT.Adq.LamApp
open import MAHLORT.Adq.Sig
open import MAHLORT.Adq.Small
open import MAHLORT.Adq.Delta
open import MAHLORT.Adq.Cases
open import MAHLORT.Adq.El
open import MAHLORT.Adq.Codes
open import MAHLORT.Adq.FG

------------------------------------------------------------------------
-- helpers
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  inAB : {A B : Expr g} -> TyEq G A B -> Env H G s s' rho -> (a : FinEl) -> EvalRel A rho a -> EvalRel B rho a
  inAB q E a e = dfst (dsnd (dsnd (sTE q rho (Env.fits E)))) a e

  inBA : {A B : Expr g} -> TyEq G A B -> Env H G s s' rho -> (a : FinEl) -> EvalRel B rho a -> EvalRel A rho a
  inBA q E a e = dsnd (dsnd (dsnd (sTE q rho (Env.fits E)))) a e

  cinAB : {M N A : Expr g} -> ConvTm G M N A -> Env H G s s' rho -> (u : FinEl) -> EvalRel M rho u -> EvalRel N rho u
  cinAB c E u e = dfst (dsnd (dsnd (sCv c rho (Env.fits E)))) u e

  cinBA : {M N A : Expr g} -> ConvTm G M N A -> Env H G s s' rho -> (u : FinEl) -> EvalRel N rho u -> EvalRel M rho u
  cinBA c E u e = dsnd (dsnd (dsnd (sCv c rho (Env.fits E)))) u e

  -- a G-conversion at the two substitutions
  cvH : Env H G s s' rho -> {t t' A : Expr g} -> ConvTm G t t' A -> ConvTm H (substExpr s t) (substExpr s' t') (substExpr s A)
  cvH E c = conv-trans (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) c) (fst (fTm s s' (Env.cs E) (Env.wH E) (snd (pCv c))))

private
  one : {n : Num} {P Q : Expr n} -> HR P Q -> AR P Q
  one r = ar-hrs (hrs-step r hrs-refl)
  two : {n : Num} {P Q R : Expr n} -> HR P Q -> HR Q R -> AR P R
  two r r' = ar-hrs (hrs-step r (hrs-step r' hrs-refl))

  -- the type of the third argument of g^, as El_U and as El_V(f ...)
  qcG : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
    HasType G f OpF -> HasType G g (OpG f) -> HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
    TyEq G (ElU f g (Fhat f g a (Lam (ElU f g a) b))) (ElV (fApp f (That a) (Lam (ElV (That a)) (That b))))
  qcG hf hg ha hb = tyeq-trans (tyeq-ElU-That (ty-Fhat hf hg ha hb)) (tyeq-ElV (conv-That-Fhat hf hg ha hb))

------------------------------------------------------------------------
-- the fundamental lemma
------------------------------------------------------------------------

mutual

  AT : {h g : Num} {H : Ctx h} {G : Ctx g} {A : Expr g} -> IsType G A -> TyIH H G A A
  AT (isty-V w) E = vRel E
  AT (isty-ElV {a = a} ha) E = elTyV E {M = a} {M' = a} (AM ha E)
  AT (isty-TyU hf hg) E = tyUR E (isty-TyU hf hg) (isty-TyU hf hg)
  AT (isty-ElU {a = a} ha) E = elUTy E ha ha (elTyU E {M = a} {M' = a} (pTm ha) (AM ha E))
  AT (isty-Pi iA iB) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  AT (isty-Sigma iA iB) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  AT (isty-Nat w) E = natRel E

  AE : {h g : Num} {H : Ctx h} {G : Ctx g} {A B : Expr g} -> TyEq G A B -> TyIH H G A B
  AE (tyeq-refl iA) = AT iA
  AE {H = H} (tyeq-sym {A = X} {B = Y} d) {s} {s'} E a ea aU =
    pSymT {G = H} {T = substExpr s' X} {T' = substExpr s Y} a aU (AE d (envSym E) a (inBA d E a ea) aU)
  AE {H = H} (tyeq-trans {A = X} {B = Y} {C = Z} d1 d2) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s X} {T2 = substExpr s' Y} {T3 = substExpr s' Z} a aU
      (AE d1 E a ea aU) (AE d2 (envR E) a (inAB d1 E a ea) aU)
  AE (tyeq-ElV {a = a} {a' = a'} c) E = elTyV E {M = a} {M' = a'} (AC c E)
  AE (tyeq-ElU {a = a} {a' = a'} c) E =
    elUTy E (fst (pCv c)) (snd (pCv c)) (elTyU E {M = a} {M' = a'} (pTm (fst (pCv c))) (AC c E))
  AE (tyeq-TyU hf hg cf cg) E =
    tyUR E (isty-TyU hf hg) (isty-TyU (snd (pCv cf)) (ty-conv (snd (pCv cg)) (opGEq (wfTm hf) hf (snd (pCv cf)) cf)))
  AE (tyeq-Pi iA iB iB' dA dB) E =
    FormX.piR E iA iB (snd (pTE dA)) (ccTy (snd (pTE dA)) (tyeq-sym dA) iB') dA dB (AT iA E) (AE dA E) (\ E' -> AE dB E')
  AE (tyeq-Sigma iA iB iB' dA dB) E =
    FormX.sigR E iA iB (snd (pTE dA)) (ccTy (snd (pTE dA)) (tyeq-sym dA) iB') dA dB (AT iA E) (AE dA E) (\ E' -> AE dB E')
  AE {H = H} (tyeq-El-PiV ha hb) {s} {s'} E c ec cU =
    pExpT c (one hr-El-PiV) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-El-PiV ha hb))
      (CodeV.piTyR E ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E') c ec cU)
  AE {H = H} (tyeq-El-SigV ha hb) {s} {s'} E c ec cU =
    pExpT c (one hr-El-SigV) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-El-SigV ha hb))
      (CodeV.sigTyR E ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E') c ec cU)
  AE (tyeq-El-NatV w) {s} E c ec cU =
    pExpT c (one hr-El-NatV) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-El-NatV w)) (natRel E c ec cU)
  AE (tyeq-El-UV hf hg) {s} E c ec cU =
    pExpT c (one hr-El-UV) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-El-UV hf hg))
      (tyUR E (isty-TyU hf hg) (isty-TyU hf hg) c ec cU)
  AE (tyeq-ElU-That {a = a} ha) {s} E c ec cU =
    pExpT c (one hr-ElU) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-ElU-That ha))
      (elTyU E {M = a} {M' = a} (pTm ha) (AM ha E) c ec cU)

  AM : {h g : Num} {H : Ctx h} {G : Ctx g} {M A : Expr g} -> HasType G M A -> TmIH H G M M A
  AM (ty-var {i = i} w) = varR i
  AM {H = H} (ty-conv {t = t} {A = X} {B = Y} d q) {s} {s'} E a u ea aU eu ua =
    pConvM {G = H} {M = substExpr s t} {M' = substExpr s' t} {T = substExpr s X} {T' = substExpr s Y} u a ua aU
      (AE q (envL E) a (inBA q E a ea) aU) (AM d E a u (inBA q E a ea) aU eu ua)
  AM (ty-Lam iA iB dt) E = lamR E iA iB dt iA (tyeq-refl iA) dt (AT iA E) (\ E' -> AT iB E') (\ E' -> AM dt E')
  AM (ty-App {A = A} {c = t} {a = a} {B = B} iA iB dt da) {s} {s'} E =
    appR E {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} {a = a} {a' = a} iA iB (tyeq-refl iA) (tyeq-refl iB) dt
      (fst (fTm s s' (Env.cs E) (Env.wH E) da)) (AM dt E) (AM da E)
      (substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E))
  AM (ty-Pair iA iB da db) = pairR iA iB (tyeq-refl iA) (tyeq-refl iB) (conv-refl da) (conv-refl db) (AT iA) (AT iB) (TM db) (AM da) (AM db)
  AM (ty-Fst {A = A} {t = t} {B = B} iA iB dt) =
    fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) dt (AT iA) (AM dt)
  AM (ty-Snd {A = A} {t = t} {B = B} iA iB dt) =
    sndR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) dt
      (\ E -> substTy E {A = A} {B = B} {N = Fst A (Lam A B) t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB dt)
                 (fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) dt (AT iA) (AM dt) E))
      (AM dt)
  AM (ty-Zero w) = zeroR
  AM (ty-Suc d) = sucR d d (conv-refl d) (AM d)
  AM (ty-Rec iC dz ds dk) =
    recX iC iC (tyeq-refl iC) (conv-refl dz) (conv-refl ds) (conv-refl dk) (AT iC) (AM dz) (AM ds) (AM dk)
  AM (ty-PiV ha hb) E = CodeV.piVR E ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E')
  AM (ty-SigV ha hb) E = CodeV.sigVR E ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E')
  AM (ty-NatV w) E = natVR E
  AM (ty-UV hf hg) E = uvR E hf hg hf hg
  AM (ty-PiU ha hb) E =
    CodeU.piUR E (pTm ha) ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E')
  AM (ty-SigU ha hb) E =
    CodeU.sigUR E (pTm ha) ha ha hb hb (conv-refl ha) (conv-refl hb) (AM ha E) (AM ha E) (\ E' -> AM hb E')
  AM (ty-NatU iU) E = natUR E iU
  AM (ty-Fhat hf hg ha hb) E =
    FhatC.fhatR E (pTm ha) hf hg ha ha hb hb (conv-refl ha) (conv-refl hb) (TM hf E) (AM hf E) (AM ha E) (AM ha E)
      (\ E' -> AM hb E') (\ E' -> AM hb E')
  AM (ty-Ghat hf hg ha hb hc) E =
    GhatC.ghatR E (pTm ha) hf hg ha ha hb hb hc (conv-refl ha) (conv-refl hb) (conv-refl hc) (TM hg E) (AM hg E)
      (AM ha E) (AM ha E) (\ E' -> AM hb E') (\ E' -> AM hb E') (AM hc E) (rqG hf hg ha hb E)
  AM (ty-That {a = a} ha) E = thatR E {a = a} {a' = a} (pTm ha) (AM ha E)

  -- the type of c in g^(a, b, c), under the left substitution
  rqG : {h g : Num} {H : Ctx h} {G : Ctx g} {f g0 a : Expr g} {b : Expr (suc g)} ->
    (hf : HasType G f OpF) (hg : HasType G g0 (OpG f)) (ha : HasType G a (TyU f g0))
    (hb : HasType (extend G (ElU f g0 a)) b (wkExpr (TyU f g0))) ->
    {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho ->
    TyRelAt H s s rho (ElU f g0 (Fhat f g0 a (Lam (ElU f g0 a) b))) (ElV (fApp f (That a) (Lam (ElV (That a)) (That b))))
  rqG {f = f} {a = a} {b = b} hf hg ha hb {s} E c ec cU =
    pExpT c (two hr-ElU (hr-ElV hr-That-Fhat)) (sbTE s (CSub.w1 (Env.cs EL)) (Env.wH EL) (qcG hf hg ha hb))
      (diagL c cU (elTyV EL {M = fApp f (That a) (Lam (ElV (That a)) (That b))} {M' = fApp f (That a) (Lam (ElV (That a)) (That b))}
                    (FhatC.RF EL (pTm ha) hf hg ha ha hb hb (conv-refl ha) (conv-refl hb) (TM hf EL) (AM hf EL) (AM ha EL) (AM ha EL)
                       (\ E' -> AM hb E') (\ E' -> AM hb E')) c ec cU))
    where EL = envL E

  TM : {h g : Num} {H : Ctx h} {G : Ctx g} {M A : Expr g} -> HasType G M A -> TyIH H G A A
  TM (ty-var {i = i} w) E = SR.ty (Env.sr E) i
  TM {H = H} (ty-conv {A = X} {B = Y} d q) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s Y} {T2 = substExpr s X} {T3 = substExpr s' Y} a aU
      (pSymT {G = H} {T = substExpr s X} {T' = substExpr s Y} a aU (AE q (envL E) a (inBA q E a ea) aU))
      (AE q E a (inBA q E a ea) aU)
  TM (ty-Lam iA iB dt) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  TM (ty-App {A = A} {a = a} {B = B} iA iB dt da) E = substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E)
  TM (ty-Pair iA iB da db) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  TM (ty-Fst iA iB dt) = AT iA
  TM (ty-Snd {A = A} {t = t} {B = B} iA iB dt) E =
    substTy E {A = A} {B = B} {N = Fst A (Lam A B) t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB dt)
      (fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) dt (AT iA) (AM dt) E)
  TM (ty-Zero w) = natRel
  TM (ty-Suc d) = natRel
  TM (ty-Rec {k = k} {C = C} iC dz ds dk) E = substTy E {A = Nat} {B = C} {N = k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') dk (AM dk E)
  TM (ty-PiV ha hb) = vRel
  TM (ty-SigV ha hb) = vRel
  TM (ty-NatV w) = vRel
  TM (ty-UV hf hg) = vRel
  TM (ty-PiU ha hb) E = tyUR E (pTm ha) (pTm ha)
  TM (ty-SigU ha hb) E = tyUR E (pTm ha) (pTm ha)
  TM (ty-NatU iU) E = tyUR E iU iU
  TM (ty-Fhat hf hg ha hb) E = tyUR E (pTm ha) (pTm ha)
  TM (ty-Ghat hf hg ha hb hc) E = tyUR E (pTm ha) (pTm ha)
  TM (ty-That ha) = vRel

  AC : {h g : Num} {H : Ctx h} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> TmIH H G M N A
  AC (conv-refl d) = AM d
  AC {H = H} (conv-sym {t = t} {u = w} {A = X} d) {s} {s'} E a u ea aU eu ua =
    pConvM {G = H} {M = substExpr s w} {M' = substExpr s' t} {T = substExpr s' X} {T' = substExpr s X} u a ua aU vt
      (pSymM {G = H} {M = substExpr s' t} {M' = substExpr s w} {T = substExpr s' X} u a ua aU
         (diagL {G = H} {T = substExpr s' X} {T' = substExpr s X} a aU vt)
         (AC d (envSym E) a u ea aU (cinBA d E u eu) ua))
    where vt = TC d (envSym E) a ea aU
  AC {H = H} (conv-trans {t = t} {u = w} {w = v} {A = X} d1 d2) {s} {s'} E a x ea aU ex xa =
    pTransM {G = H} {M1 = substExpr s t} {M2 = substExpr s' w} {M3 = substExpr s' v} {T = substExpr s X} x a xa aU
      (diagL {G = H} {T = substExpr s X} {T' = substExpr s' X} a aU vt) (AC d1 E a x ea aU ex xa)
      (pConvM {G = H} {M = substExpr s' w} {M' = substExpr s' v} {T = substExpr s' X} {T' = substExpr s X} x a xa aU
         (pSymT {G = H} {T = substExpr s X} {T' = substExpr s' X} a aU vt)
         (AC d2 (envR E) a x ea aU (cinAB d1 E x ex) xa))
    where vt = TC d1 E a ea aU
  AC {H = H} (conv-conv {t = t} {u = w} {A = X} {B = Y} d q) {s} {s'} E a x ea aU ex xa =
    pConvM {G = H} {M = substExpr s t} {M' = substExpr s' w} {T = substExpr s X} {T' = substExpr s Y} x a xa aU
      (AE q (envL E) a (inBA q E a ea) aU) (AC d E a x (inBA q E a ea) aU ex xa)
  AC (conv-beta iA iB dt da) = betaCv iA iB dt da (AT iA) (AT iB) (AM dt) (AM da)
  AC (conv-funext {A = A} {t = t} {t' = t'} {B = B} iA iB dt dt' d) =
    funextR {A = A} {B = B} {t = t} {t' = t'} iA iB dt dt' (AT iA) (AT iB) (AC d)
  AC {H = H} (conv-fst-beta {A = A} {a = t} {b = w} {B = B} iA iB dt du) {s} {s'} E a x ea aU ex xa = go (bot-or x)
    where
      go : Or (Eq x Bot) (NotBot x) ->
        RTm H (substExpr s (Fst A (Lam A B) (Pair A (Lam A B) t w))) (substExpr s' t) (substExpr s A) x a
      go (left refl) = tt
      go (right nb) =
        pExpM x a xa aU (one hr-fst-pair) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-fst-beta iA iB dt du))
          (diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} a aU (AT iA E a ea aU))
          (AM dt E a x ea aU (dfst (dsnd (guard-elim x nb ex))) xa)
  AC {H = H} (conv-snd-beta {A = A} {a = t} {b = w} {B = B} iA iB dt du) {s} {s'} E c y ec cU ey yc = go (bot-or y)
    where
      go : Or (Eq y Bot) (NotBot y) ->
        RTm H (substExpr s (Snd A (Lam A B) (Pair A (Lam A B) t w))) (substExpr s' w) (substExpr s (subst1 B t)) y c
      go (left refl) = tt
      go (right nb) =
        pExpM y c yc cU (one hr-snd-pair) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-snd-beta iA iB dt du))
          (diagL {G = H} {T = substExpr s (subst1 B t)} {T' = substExpr s' (subst1 B t)} c cU
             (substTy E {A = A} {B = B} {N = t} iA (AT iA E) (\ E' -> AT iB E') dt (AM dt E) c ec cU))
          (AM du E c y ec cU (dsnd (dsnd (guard-elim y nb ey))) yc)
  AC (conv-pairext {A = A} {t = t} {B = B} iA iB dt dt' d1 d2) =
    pairextR iA iB dt dt' d1 (AT iA)
      (\ E -> substTy E {A = A} {B = B} {N = Fst A (Lam A B) t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB dt)
                (fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) dt (AT iA) (AM dt) E))
      (AC d1) (AC d2)
  AC {H = H} (conv-rec-zero {z = z} {s = st} {C = C} iC dz ds) {s} {s'} {rho} E c u ec cU eu uc = go (bot-or u)
    where
      Lhs = Rec (Lam Nat (substExpr (liftSub s) C)) (substExpr s z) (substExpr s st) Zero
      go : Or (Eq u Bot) (NotBot u) -> RTm H Lhs (substExpr s' z) (substExpr s (subst1 C Zero)) u c
      go (left refl) = tt
      go (right nb) = pickZ (dfst bd) (dfst (dsnd bd)) (dsnd (dsnd bd))
        where
          bd = guard-elim u nb eu
          pickZ : (w : FinEl) -> EvalRel Zero rho w -> MAHLOINJ.Model.Comb.RecB (EvalRel z rho) (EvalRel st rho) u w ->
            RTm H Lhs (substExpr s' z) (substExpr s (subst1 C Zero)) u c
          pickZ D.ZeroEl ew rb =
            pExpM u c uc cU (one hr-rec-zero) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-rec-zero iC dz ds))
              (diagL {G = H} {T = substExpr s (subst1 C Zero)} {T' = substExpr s' (subst1 C Zero)} c cU (TM dz E c ec cU))
              (AM dz E c u ec cU rb uc)
  AC (conv-rec-suc iC dz ds dk) = recSucCv iC dz ds dk (AT iC) (AM dz) (AM ds) (TM ds) (AM dk)
  AC (conv-Lam iA iB eAA' ct) E =
    lamR E iA iB (fst (pCv ct)) (snd (pTE eAA')) eAA' (snd (pCv ct)) (AT iA E) (\ E' -> AT iB E') (\ E' -> AC ct E')
  AC (conv-App {A = A} {A' = A'} {c = t} {c' = t'} {a = a} {a' = a'} {B = B} {B' = B'} iA iB eA eB cc ca) E =
    appR E {A = A} {A' = A'} {B = B} {B' = B'} {t = t} {t' = t'} {a = a} {a' = a'} iA iB eA eB (fst (pCv cc)) (cvH E ca)
      (AC cc E) (AC ca E)
      (substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') (fst (pCv ca)) (diagC {M = a} {M' = a'} {T = A} (AC ca) (AT iA) E))
  AC (conv-Pair iA iB eA eB ca cb) = pairR iA iB eA eB ca cb (AT iA) (AT iB) (TC cb) (AC ca) (AC cb)
  AC (conv-Fst {A = A} {A' = A'} {t = t} {t' = t'} {B = B} {B' = B'} iA iB eA eB d) =
    fstR {A = A} {A' = A'} {B = B} {B' = B'} {t = t} {t' = t'} iA iB eA eB (fst (pCv d)) (AT iA) (AC d)
  AC (conv-Snd {A = A} {A' = A'} {t = t} {t' = t'} {B = B} {B' = B'} iA iB eA eB d) =
    sndR {A = A} {A' = A'} {B = B} {B' = B'} {t = t} {t' = t'} iA iB eA eB (fst (pCv d))
      (\ E -> substTy E {A = A} {B = B} {N = Fst A (Lam A B) t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB (fst (pCv d)))
                (fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) (fst (pCv d)) (AT iA)
                   (diagC {M = t} {M' = t'} {T = SigmaB A B} (AC d) (\ E2 -> Form.sigR E2 iA iB (AT iA E2) (\ E' -> AT iB E'))) E))
      (AC d)
  AC (conv-Suc d) = sucR (fst (pCv d)) (snd (pCv d)) d (AC d)
  AC (conv-Rec iC iC' qC cz cs ck) = recX iC iC' qC cz cs ck (AT iC) (AC cz) (AC cs) (AC ck)
  AC (conv-PiV ha hb hb' ca cb) E =
    CodeV.piVR E ha (snd (pCv ca)) hb hb' ca cb (AM ha E) (AC ca E) (\ E' -> AC cb E')
  AC (conv-SigV ha hb hb' ca cb) E =
    CodeV.sigVR E ha (snd (pCv ca)) hb hb' ca cb (AM ha E) (AC ca E) (\ E' -> AC cb E')
  AC (conv-UV hf hg cf cg) E =
    uvR E hf hg (snd (pCv cf)) (ty-conv (snd (pCv cg)) (opGEq (wfTm hf) hf (snd (pCv cf)) cf))
  AC (conv-PiU ha hb hb' ca cb) E =
    CodeU.piUR E (pTm ha) ha (snd (pCv ca)) hb hb' ca cb (AM ha E) (AC ca E) (\ E' -> AC cb E')
  AC (conv-SigU ha hb hb' ca cb) E =
    CodeU.sigUR E (pTm ha) ha (snd (pCv ca)) hb hb' ca cb (AM ha E) (AC ca E) (\ E' -> AC cb E')
  AC (conv-Fhat hf hg ha hb hb' ca cb) E =
    FhatC.fhatR E (pTm ha) hf hg ha (snd (pCv ca)) hb hb' ca cb (TM hf E) (AM hf E) (AM ha E) (AC ca E)
      (\ E' -> AM hb E') (\ E' -> AC cb E')
  AC (conv-Ghat hf hg ha hb hb' ca cb cc) E =
    GhatC.ghatR E (pTm ha) hf hg ha (snd (pCv ca)) hb hb' (fst (pCv cc)) ca cb cc (TM hg E) (AM hg E)
      (AM ha E) (AC ca E) (\ E' -> AM hb E') (\ E' -> AC cb E') (AC cc E) (rqG hf hg ha hb E)
  AC (conv-That {a = a} {a' = a'} ca) E = thatR E {a = a} {a' = a'} (pTm (fst (pCv ca))) (AC ca E)
  AC (conv-That-PiU {f = f0} {g = g0} {a = a} {b = b} ha hb) {s} E =
    tmV E {M = That (PiU f0 g0 a (Lam (ElU f0 g0 a) b))} {M' = PiV (That a) (Lam (ElV (That a)) (That b))}
      (\ c ec cU -> pExpT c (one (hr-ElV hr-That-PiU)) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-ElV (conv-That-PiU ha hb)))
                      (elTyV E {M = PiV (That a) (Lam (ElV (That a)) (That b))} {M' = PiV (That a) (Lam (ElV (That a)) (That b))}
                         (CodeV.piVR E (ty-That ha) (ty-That ha) hTb hTb (conv-refl (ty-That ha)) (conv-refl hTb)
                            (thatR E {a = a} {a' = a} (pTm ha) (AM ha E)) (thatR E {a = a} {a' = a} (pTm ha) (AM ha E))
                            (\ E' -> thatR (envElU ha E') {a = b} {a' = b} (wkTy (isty-ElU ha) (pTm ha)) (AM hb (envElU ha E'))))
                         c ec cU))
    where hTb = ty-That (ccTm (isty-ElV (ty-That ha)) (tyeq-sym (tyeq-ElU-That ha)) hb)
  AC (conv-That-SigU {f = f0} {g = g0} {a = a} {b = b} ha hb) {s} E =
    tmV E {M = That (SigU f0 g0 a (Lam (ElU f0 g0 a) b))} {M' = SigV (That a) (Lam (ElV (That a)) (That b))}
      (\ c ec cU -> pExpT c (one (hr-ElV hr-That-SigU)) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-ElV (conv-That-SigU ha hb)))
                      (elTyV E {M = SigV (That a) (Lam (ElV (That a)) (That b))} {M' = SigV (That a) (Lam (ElV (That a)) (That b))}
                         (CodeV.sigVR E (ty-That ha) (ty-That ha) hTb hTb (conv-refl (ty-That ha)) (conv-refl hTb)
                            (thatR E {a = a} {a' = a} (pTm ha) (AM ha E)) (thatR E {a = a} {a' = a} (pTm ha) (AM ha E))
                            (\ E' -> thatR (envElU ha E') {a = b} {a' = b} (wkTy (isty-ElU ha) (pTm ha)) (AM hb (envElU ha E'))))
                         c ec cU))
    where hTb = ty-That (ccTm (isty-ElV (ty-That ha)) (tyeq-sym (tyeq-ElU-That ha)) hb)
  AC (conv-That-NatU {f = f0} {g = g0} iU) {s} E =
    tmV E {M = That (NatU f0 g0)} {M' = NatV}
      (\ c ec cU -> pExpT c (one (hr-ElV hr-That-NatU)) (sbTE s (CSub.w1 (Env.cs E)) (Env.wH E) (tyeq-ElV (conv-That-NatU iU)))
                      (elTyV E {M = NatV} {M' = NatV} (natVR E) c ec cU))
  AC (conv-That-Fhat hf hg ha hb) E =
    FhatC.fhatEqR E (pTm ha) hf hg ha ha hb hb (conv-refl ha) (conv-refl hb) (TM hf E) (AM hf E) (AM ha E) (AM ha E)
      (\ E' -> AM hb E') (\ E' -> AM hb E')
  AC (conv-That-Ghat hf hg ha hb hc) E =
    GhatC.ghatEqR E (pTm ha) hf hg ha ha hb hb hc (conv-refl ha) (conv-refl hb) (conv-refl hc) (TM hg E) (AM hg E)
      (AM ha E) (AM ha E) (\ E' -> AM hb E') (\ E' -> AM hb E') (AM hc E) (rqG hf hg ha hb E)
  AC (conv-reflect {a = a} {b = b} ha hb c) E = reflR E {a = a} {a' = b} (pTm ha) (AC c E)

  TC : {h g : Num} {H : Ctx h} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> TyIH H G A A
  TC (conv-refl d) = TM d
  TC (conv-sym d) = TC d
  TC (conv-trans d1 d2) = TC d1
  TC {H = H} (conv-conv {A = X} {B = Y} d q) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s Y} {T2 = substExpr s X} {T3 = substExpr s' Y} a aU
      (pSymT {G = H} {T = substExpr s X} {T' = substExpr s Y} a aU (AE q (envL E) a (inBA q E a ea) aU))
      (AE q E a (inBA q E a ea) aU)
  TC (conv-beta {A = A} {a = a} {B = B} iA iB dt da) E = substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E)
  TC (conv-funext iA iB dt dt' d) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-fst-beta iA iB dt du) = AT iA
  TC (conv-snd-beta {A = A} {a = t} {B = B} iA iB dt du) E = substTy E {A = A} {B = B} {N = t} iA (AT iA E) (\ E' -> AT iB E') dt (AM dt E)
  TC (conv-pairext iA iB dt dt' d1 d2) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-rec-zero iC dz ds) = TM dz
  TC (conv-rec-suc {k = k} {C = C} iC dz ds dk) E =
    substTy E {A = Nat} {B = C} {N = Suc k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') (ty-Suc dk) (sucR dk dk (conv-refl dk) (AM dk) E)
  TC (conv-Lam iA iB eAA' ct) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-App {A = A} {a = a} {a' = a'} {B = B} iA iB eA eB cc ca) E =
    substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') (fst (pCv ca)) (diagC {M = a} {M' = a'} {T = A} (AC ca) (AT iA) E)
  TC (conv-Pair iA iB eA eB ca cb) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-Fst iA iB eA eB d) = AT iA
  TC (conv-Snd {A = A} {t = t} {t' = t'} {B = B} iA iB eA eB d) E =
    substTy E {A = A} {B = B} {N = Fst A (Lam A B) t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB (fst (pCv d)))
      (fstR {A = A} {A' = A} {B = B} {B' = B} {t = t} {t' = t} iA iB (tyeq-refl iA) (tyeq-refl iB) (fst (pCv d)) (AT iA)
         (diagC {M = t} {M' = t'} {T = SigmaB A B} (AC d) (\ E2 -> Form.sigR E2 iA iB (AT iA E2) (\ E' -> AT iB E'))) E)
  TC (conv-Suc d) = natRel
  TC (conv-Rec {k = k} {k' = k'} {C = C} iC iC' qC cz cs ck) E =
    substTy E {A = Nat} {B = C} {N = k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') (fst (pCv ck))
      (diagC {M = k} {M' = k'} {T = Nat} (AC ck) natRel E)
  TC (conv-PiV ha hb hb' ca cb) = vRel
  TC (conv-SigV ha hb hb' ca cb) = vRel
  TC (conv-UV hf hg cf cg) = vRel
  TC (conv-PiU ha hb hb' ca cb) E = tyUR E (pTm ha) (pTm ha)
  TC (conv-SigU ha hb hb' ca cb) E = tyUR E (pTm ha) (pTm ha)
  TC (conv-Fhat hf hg ha hb hb' ca cb) E = tyUR E (pTm ha) (pTm ha)
  TC (conv-Ghat hf hg ha hb hb' ca cb cc) E = tyUR E (pTm ha) (pTm ha)
  TC (conv-That ca) = vRel
  TC (conv-That-PiU ha hb) = vRel
  TC (conv-That-SigU ha hb) = vRel
  TC (conv-That-NatU iU) = vRel
  TC (conv-That-Fhat hf hg ha hb) = vRel
  TC (conv-That-Ghat hf hg ha hb hc) = vRel
  TC (conv-reflect ha hb c) E = tyUR E (pTm ha) (pTm ha)
