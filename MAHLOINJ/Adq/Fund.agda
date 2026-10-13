{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Fund.agda
--
-- The fundamental lemma: every derivable judgement is valid in the
-- logical relation, for every pair of related substitutions over an
-- approximation of the context.  By mutual structural induction on the
-- derivations; the type of a term judgement is related as well
-- (bundled two-substitution validity).
------------------------------------------------------------------------

module MAHLOINJ.Adq.Fund where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (LeCode ; FinMem ; NotBot)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-elim)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.Soundness using (sTE ; sCv)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf using (NatTy)
open import MAHLOINJ.Syntax.CtxConv using (ccTy)
open import MAHLOINJ.Syntax.Presup using (pCv ; pTm ; pTE ; lamV)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Env
open import MAHLOINJ.Adq.Form
open import MAHLOINJ.Adq.LamApp
open import MAHLOINJ.Adq.Sig
open import MAHLOINJ.Adq.Small
open import MAHLOINJ.Adq.Delta
open import MAHLOINJ.Adq.DeltaCases
open import MAHLOINJ.Adq.Cases

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

  -- the universe u(f,g) under s and s'
  uRL : {ff gg : Expr g} -> Env H G s s' rho -> IsType G (Ucode ff gg) -> UnivR H (substExpr s (Ucode ff gg))
  uRL E iu = univR (univ-U _ _ refl) (sbTy s (CSub.w1 (Env.cs E)) (Env.wH E) iu)

  uRR : {ff gg : Expr g} -> Env H G s s' rho -> IsType G (Ucode ff gg) -> UnivR H (substExpr s' (Ucode ff gg))
  uRR E iu = univR (univ-U _ _ refl) (sbTy s' (CSub.w2 (Env.cs E)) (Env.wH E) iu)

------------------------------------------------------------------------
-- the fundamental lemma
------------------------------------------------------------------------

mutual

  AT : {h g : Num} {H : Ctx h} {G : Ctx g} {A : Expr g} -> IsType G A -> TyIH H G A A
  AT (isty-V w) E = vRel E
  AT (isty-el d) E a ea aU = elTyR a (AM d E UCode a uUC tt ea aU)
  AT (isty-Pi iA iB) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  AT (isty-Sigma iA iB) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')

  AE : {h g : Num} {H : Ctx h} {G : Ctx g} {A B : Expr g} -> TyEq G A B -> TyIH H G A B
  AE (tyeq-refl iA) = AT iA
  AE {H = H} (tyeq-sym {A = X} {B = Y} d) {s} {s'} E a ea aU =
    pSymT {G = H} {T = substExpr s' X} {T' = substExpr s Y} a aU (AE d (envSym E) a (inBA d E a ea) aU)
  AE {H = H} (tyeq-trans {A = X} {B = Y} {C = Z} d1 d2) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s X} {T2 = substExpr s' Y} {T3 = substExpr s' Z} a aU
      (AE d1 E a ea aU) (AE d2 (envR E) a (inAB d1 E a ea) aU)
  AE (tyeq-el d) E a ea aU = elTyR a (AC d E UCode a uUC tt ea aU)
  AE (tyeq-Pi iA iB iB' dA dB) E =
    FormX.piR E iA iB (snd (pTE dA)) (ccTy (snd (pTE dA)) (tyeq-sym dA) iB') dA dB (AT iA E) (AE dA E) (\ E' -> AE dB E')
  AE (tyeq-Sigma iA iB iB' dA dB) E =
    FormX.sigR E iA iB (snd (pTE dA)) (ccTy (snd (pTE dA)) (tyeq-sym dA) iB') dA dB (AT iA E) (AE dA E) (\ E' -> AE dB E')

  AM : {h g : Num} {H : Ctx h} {G : Ctx g} {M A : Expr g} -> HasType G M A -> TmIH H G M M A
  AM (ty-var {i = i} w) = varR i
  AM {H = H} (ty-conv {t = t} {A = X} {B = Y} d q) {s} {s'} E a u ea aU eu ua =
    pConvM {G = H} {M = substExpr s t} {M' = substExpr s' t} {T = substExpr s X} {T' = substExpr s Y} u a ua aU
      (AE q (envL E) a (inBA q E a ea) aU) (AM d E a u (inBA q E a ea) aU eu ua)
  AM (ty-sub d) E a u ea aU eu ua = reUnivAt (univV E) a u ea (AM d E a u ea aU eu ua)
  AM (ty-Pi (univ-V refl) dA dB) E Bot c ea aU ec ca = tmBot c
  AM (ty-Pi (univ-V refl) dA dB) E UCode c ea aU ec ca =
    elM c (univV E) (Form.piR E (isty-el dA) (isty-el dB) (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU))
                       (\ E' c' ec' cU' -> elTyR c' (AM dB E' UCode c' uUC tt ec' cU')) c ec ca)
  AM (ty-Pi (univ-U f g refl) dA dB) E Bot c ea aU ec ca = tmBot c
  AM (ty-Pi (univ-U f g refl) dA dB) E UCode c ea aU ec ca =
    elM c (uRL E (pTm dA)) (Form.piR E (isty-el (ty-sub dA)) (isty-el (ty-sub dB))
                              (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU))
                              (\ E' c' ec' cU' -> elTyR c' (AM dB E' UCode c' uUC tt ec' cU')) c ec ca)
  AM (ty-Sigma (univ-V refl) dA dB) E Bot c ea aU ec ca = tmBot c
  AM (ty-Sigma (univ-V refl) dA dB) E UCode c ea aU ec ca =
    elM c (univV E) (Form.sigR E (isty-el dA) (isty-el dB) (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU))
                       (\ E' c' ec' cU' -> elTyR c' (AM dB E' UCode c' uUC tt ec' cU')) c ec ca)
  AM (ty-Sigma (univ-U f g refl) dA dB) E Bot c ea aU ec ca = tmBot c
  AM (ty-Sigma (univ-U f g refl) dA dB) E UCode c ea aU ec ca =
    elM c (uRL E (pTm dA)) (Form.sigR E (isty-el (ty-sub dA)) (isty-el (ty-sub dB))
                              (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU))
                              (\ E' c' ec' cU' -> elTyR c' (AM dB E' UCode c' uUC tt ec' cU')) c ec ca)
  AM (ty-Nat-V w) E Bot u ea aU eu ua = tmBot u
  AM (ty-Nat-V w) E UCode u ea aU eu ua = elM u (univV E) (natTy (NatTy (Env.wH E)) u eu)
  AM (ty-Nat-U d) E Bot u ea aU eu ua = tmBot u
  AM (ty-Nat-U d) E UCode u ea aU eu ua = elM u (uRL E (isty-el d)) (natTy (NatTy (Env.wH E)) u eu)
  AM (ty-Ucode df dg) E Bot u ea aU eu ua = tmBot u
  AM (ty-Ucode df dg) E UCode u ea aU eu ua =
    elM u (univV E) (uTy (uRL E (isty-el (ty-Ucode df dg))) (uRR E (isty-el (ty-Ucode df dg))) u eu)
  AM (ty-Fhat df dg dA dB) E Bot u ea aU eu ua = tmBot u
  AM {H = H} (ty-Fhat {f = ff} {g = gg} {A = A} {B = B} df dg dA dB) {s} {s'} E UCode u ea aU eu ua =
    elM u (uRL E (isty-el (ty-Ucode df dg)))
      (pExpT {G = H} {T = substExpr s (Fhat ff gg A (Lam A B))} {T1 = substExpr s (App (App ff A) (Lam A B))}
         {T' = substExpr s' (Fhat ff gg A (Lam A B))} u (hrs-step hr-fhat hrs-refl) (qFhat (CSub.w1 (Env.cs E)) (Env.wH E) df dg dA dB)
        (pExpT' {G = H} {T = substExpr s (App (App ff A) (Lam A B))} {T' = substExpr s' (Fhat ff gg A (Lam A B))}
           {T1' = substExpr s' (App (App ff A) (Lam A B))} u (hrs-step hr-fhat hrs-refl) (qFhat (CSub.w2 (Env.cs E)) (Env.wH E) df dg dA dB)
           (elTyR u (fhatD df dA dB (TM df) (AM df) (AM dA) (AM dB) E UCode u uUC tt eu ua))))
  AM (ty-Ghat df dg dA dB dc) E Bot u ea aU eu ua = tmBot u
  AM {H = H} {G = G} (ty-Ghat {f = ff} {g = gg} {A = A} {c = c} {B = B} df dg dA dB dc) {s} {s'} E UCode u ea aU eu ua =
    elM u (uRL E (isty-el (ty-Ucode df dg)))
      (pExpT {G = H} {T = substExpr s (Ghat ff gg A (Lam A B) c)} {T1 = substExpr s (App (App (App gg A) (Lam A B)) c)}
         {T' = substExpr s' (Ghat ff gg A (Lam A B) c)} u (hrs-step hr-ghat hrs-refl) (qG s (CSub.w1 (Env.cs E)))
        (pExpT' {G = H} {T = substExpr s (App (App (App gg A) (Lam A B)) c)} {T' = substExpr s' (Ghat ff gg A (Lam A B) c)}
           {T1' = substExpr s' (App (App (App gg A) (Lam A B)) c)} u (hrs-step hr-ghat hrs-refl) (qG s' (CSub.w2 (Env.cs E)))
           (elTyR u (ghatD df dg dA dB dc (TM df) (AM df) (TM dg) (AM dg) (AM dA) (AM dB) (AM dc) E UCode u uUC tt eu ua))))
    where
      qG : (r : Sub _ _) -> WtSub H G r ->
        TyEq H (substExpr r (Ghat ff gg A (Lam A B) c)) (substExpr r (App (App (App gg A) (Lam A B)) c))
      qG r wr = tyeq-el (sbCv r wr (Env.wH E) (conv-delta-g df dg dA dB dc))
  AM (ty-Lam iA iB dt) E = lamR E iA iB dt (AT iA E) (\ E' -> AT iB E') (\ E' -> AM dt E')
  AM (ty-App {A = A} {t = t} {a = a} {B = B} iA iB dt da) {s} {s'} E =
    appR E {A = A} {B = B} {t = t} {t' = t} {a = a} {a' = a} dt (fst (fTm s s' (Env.cs E) (Env.wH E) da)) (AM dt E) (AM da E)
      (substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E))
  AM (ty-Pair iA iB dt du) = pairR iA iB dt du (AT iA) (AT iB) (AM dt) (AM du)
  AM (ty-Fst {A = A} {t = t} {B = B} iA iB dt) = fstR {A = A} {B = B} {t = t} {t' = t} dt (AT iA) (AM dt)
  AM (ty-Snd {A = A} {t = t} {B = B} iA iB dt) =
    sndR {A = A} {B = B} {t = t} {t' = t} iB dt
      (\ E -> substTy E {A = A} {B = B} {N = Fst t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB dt)
                 (fstR {A = A} {B = B} {t = t} {t' = t} dt (AT iA) (AM dt) E)) (AM dt)
  AM (ty-Zero w) = zeroR
  AM (ty-Suc d) = sucR d d (conv-refl d) (AM d)
  AM (ty-Rec iC dz ds dk) =
    recX iC iC (tyeq-refl iC) (conv-refl dz) (conv-refl ds) (conv-refl dk) (AT iC) (AM dz) (AM ds) (AM dk)

  TM : {h g : Num} {H : Ctx h} {G : Ctx g} {M A : Expr g} -> HasType G M A -> TyIH H G A A
  TM (ty-var {i = i} w) E = SR.ty (Env.sr E) i
  TM {H = H} (ty-conv {A = X} {B = Y} d q) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s Y} {T2 = substExpr s X} {T3 = substExpr s' Y} a aU
      (pSymT {G = H} {T = substExpr s X} {T' = substExpr s Y} a aU (AE q (envL E) a (inBA q E a ea) aU))
      (AE q E a (inBA q E a ea) aU)
  TM (ty-sub d) = vRel
  TM (ty-Pi (univ-V refl) dA dB) = vRel
  TM (ty-Pi (univ-U f g refl) dA dB) E a ea aU = uTy (uRL E (pTm dA)) (uRR E (pTm dA)) a ea
  TM (ty-Sigma (univ-V refl) dA dB) = vRel
  TM (ty-Sigma (univ-U f g refl) dA dB) E a ea aU = uTy (uRL E (pTm dA)) (uRR E (pTm dA)) a ea
  TM (ty-Nat-V w) = vRel
  TM (ty-Nat-U d) E a ea aU = uTy (uRL E (isty-el d)) (uRR E (isty-el d)) a ea
  TM (ty-Ucode df dg) = vRel
  TM (ty-Fhat df dg dA dB) E a ea aU = uTy (uRL E (isty-el (ty-Ucode df dg))) (uRR E (isty-el (ty-Ucode df dg))) a ea
  TM (ty-Ghat df dg dA dB dc) E a ea aU = uTy (uRL E (isty-el (ty-Ucode df dg))) (uRR E (isty-el (ty-Ucode df dg))) a ea
  TM (ty-Lam iA iB dt) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  TM (ty-App {A = A} {a = a} {B = B} iA iB dt da) E = substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E)
  TM (ty-Pair iA iB dt du) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  TM (ty-Fst iA iB dt) = AT iA
  TM (ty-Snd {A = A} {t = t} {B = B} iA iB dt) E =
    substTy E {A = A} {B = B} {N = Fst t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB dt)
      (fstR {A = A} {B = B} {t = t} {t' = t} dt (AT iA) (AM dt) E)
  TM (ty-Zero w) = natRel
  TM (ty-Suc d) = natRel
  TM (ty-Rec {k = k} {C = C} iC dz ds dk) E = substTy E {A = Nat} {B = C} {N = k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') dk (AM dk E)

  AC : {h g : Num} {H : Ctx h} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> TmIH H G M N A
  AC (conv-refl d) = AM d
  AC {H = H} (conv-sym {t = t} {u = w} {A = X} d) {s} {s'} E a u ea aU eu ua =
    pConvM {G = H} {M = substExpr s w} {M' = substExpr s' t} {T = substExpr s' X} {T' = substExpr s X} u a ua aU vt
      (pSymM {G = H} {M = substExpr s' t} {M' = substExpr s w} {T = substExpr s' X} u a ua aU
         (diagL {G = H} {T = substExpr s' X} {T' = substExpr s X} a aU vt)
         (AC d (envSym E) a u ea aU (cinBA d E u eu) ua))
    where vt = TC d (envSym E) a ea aU
  AC {H = H} (conv-trans {t = t} {u = w} {v = v} {A = X} d1 d2) {s} {s'} E a x ea aU ex xa =
    pTransM {G = H} {M1 = substExpr s t} {M2 = substExpr s' w} {M3 = substExpr s' v} {T = substExpr s X} x a xa aU
      (diagL {G = H} {T = substExpr s X} {T' = substExpr s' X} a aU vt) (AC d1 E a x ea aU ex xa)
      (pConvM {G = H} {M = substExpr s' w} {M' = substExpr s' v} {T = substExpr s' X} {T' = substExpr s X} x a xa aU
         (pSymT {G = H} {T = substExpr s X} {T' = substExpr s' X} a aU vt)
         (AC d2 (envR E) a x ea aU (cinAB d1 E x ex) xa))
    where vt = TC d1 E a ea aU
  AC {H = H} (conv-conv {t = t} {u = w} {A = X} {B = Y} d q) {s} {s'} E a x ea aU ex xa =
    pConvM {G = H} {M = substExpr s t} {M' = substExpr s' w} {T = substExpr s X} {T' = substExpr s Y} x a xa aU
      (AE q (envL E) a (inBA q E a ea) aU) (AC d E a x (inBA q E a ea) aU ex xa)
  AC (conv-sub d) E a x ea aU ex xa = reUnivAt (univV E) a x ea (AC d E a x ea aU ex xa)
  AC (conv-R' dA dB d) E a x ea aU ex xa = reUnivAt (uRL E (pTm dA)) a x ea (AC d E a x ea aU ex xa)
  AC (conv-delta-f df dg dA dB) E Bot u ea aU eu ua = tmBot u
  AC {H = H} (conv-delta-f {f = ff} {g = gg} {A = A} {B = B} df dg dA dB) {s} {s'} E UCode u ea aU eu ua =
    elM u (univV E)
      (pExpT {G = H} {T = substExpr s (Fhat ff gg A (Lam A B))} {T1 = substExpr s (App (App ff A) (Lam A B))}
         {T' = substExpr s' (App (App ff A) (Lam A B))} u (hrs-step hr-fhat hrs-refl) (qFhat (CSub.w1 (Env.cs E)) (Env.wH E) df dg dA dB)
         (elTyR u (fhatD df dA dB (TM df) (AM df) (AM dA) (AM dB) E UCode u uUC tt eu ua)))
  AC (conv-delta-g df dg dA dB dc) E Bot u ea aU eu ua = tmBot u
  AC {H = H} (conv-delta-g {f = ff} {g = gg} {A = A} {c = c} {B = B} df dg dA dB dc) {s} {s'} E UCode u ea aU eu ua =
    elM u (univV E)
      (pExpT {G = H} {T = substExpr s (Ghat ff gg A (Lam A B) c)} {T1 = substExpr s (App (App (App gg A) (Lam A B)) c)}
         {T' = substExpr s' (App (App (App gg A) (Lam A B)) c)} u (hrs-step hr-ghat hrs-refl)
         (tyeq-el (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-delta-g df dg dA dB dc)))
         (elTyR u (ghatD df dg dA dB dc (TM df) (AM df) (TM dg) (AM dg) (AM dA) (AM dB) (AM dc) E UCode u uUC tt eu ua)))
  AC (conv-beta iA iB dt da) = betaCv iA iB dt da (AT iA) (AT iB) (AM dt) (AM da)
  AC (conv-funext {A = A} {t = t} {t' = t'} {B = B} iA iB dt dt' d) = funextR {A = A} {B = B} {t = t} {t' = t'} iA iB (AT iA) (AC d)
  AC {H = H} (conv-fst-beta {A = A} {t = t} {u = w} {B = B} iA iB dt du) {s} {s'} E a x ea aU ex xa = go (bot-or x)
    where
      go : Or (Eq x Bot) (NotBot x) -> RTm H (Fst (Pair (substExpr s t) (substExpr s w))) (substExpr s' t) (substExpr s A) x a
      go (left refl) = tt
      go (right nb) =
        pExpM {G = H} {M = Fst (Pair (substExpr s t) (substExpr s w))} {M1 = substExpr s t} {M' = substExpr s' t} {T = substExpr s A}
          x a xa aU (hrs-step hr-fst-pair hrs-refl) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-fst-beta iA iB dt du))
          (diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} a aU (AT iA E a ea aU))
          (AM dt E a x ea aU (dfst (dsnd (guard-elim x nb ex))) xa)
  AC {H = H} (conv-snd-beta {A = A} {t = t} {u = w} {B = B} iA iB dt du) {s} {s'} E c y ec cU ey yc = go (bot-or y)
    where
      go : Or (Eq y Bot) (NotBot y) ->
        RTm H (Snd (Pair (substExpr s t) (substExpr s w))) (substExpr s' w) (substExpr s (subst1 B t)) y c
      go (left refl) = tt
      go (right nb) =
        pExpM {G = H} {M = Snd (Pair (substExpr s t) (substExpr s w))} {M1 = substExpr s w} {M' = substExpr s' w}
          {T = substExpr s (subst1 B t)}
          y c yc cU (hrs-step hr-snd-pair hrs-refl) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-snd-beta iA iB dt du))
          (diagL {G = H} {T = substExpr s (subst1 B t)} {T' = substExpr s' (subst1 B t)} c cU
             (substTy E {A = A} {B = B} {N = t} iA (AT iA E) (\ E' -> AT iB E') dt (AM dt E) c ec cU))
          (AM du E c y ec cU (dsnd (dsnd (guard-elim y nb ey))) yc)
  AC (conv-pairext iA iB dt dt' d1 d2) = pairextR iA iB dt dt' d1 (AC d1) (AC d2)
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
          pickZ ZeroEl ew rb =
            pExpM {G = H} {M = Lhs} {M1 = substExpr s z} {M' = substExpr s' z} {T = substExpr s (subst1 C Zero)}
              u c uc cU (hrs-step hr-rec-zero hrs-refl) (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-rec-zero iC dz ds))
              (diagL {G = H} {T = substExpr s (subst1 C Zero)} {T' = substExpr s' (subst1 C Zero)} c cU (TM dz E c ec cU))
              (AM dz E c u ec cU rb uc)
  AC (conv-rec-suc iC dz ds dk) = recSucCv iC dz ds dk (AT iC) (AM dz) (AM ds) (TM ds) (AM dk)
  AC (conv-App {A = A} {t = t} {t' = t'} {a = a} {a' = a'} {B = B} iA iB d1 d2) {s} {s'} E =
    appR E {A = A} {B = B} {t = t} {t' = t'} {a = a} {a' = a'} (fst (pCv d1))
      (conv-trans (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) d2) (fst (fTm s s' (Env.cs E) (Env.wH E) (snd (pCv d2)))))
      (AC d1 E) (AC d2 E)
      (substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') (fst (pCv d2)) (diagC {M = a} {M' = a'} {T = A} (AC d2) (AT iA) E))
  AC (conv-Fst {A = A} {t = t} {t' = t'} {B = B} iA iB d) = fstR {A = A} {B = B} {t = t} {t' = t'} (fst (pCv d)) (AT iA) (AC d)
  AC (conv-Snd {A = A} {t = t} {t' = t'} {B = B} iA iB d) =
    sndR {A = A} {B = B} {t = t} {t' = t'} iB (fst (pCv d))
      (\ E -> substTy E {A = A} {B = B} {N = Fst t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB (fst (pCv d)))
                (fstR {A = A} {B = B} {t = t} {t' = t} (fst (pCv d)) (AT iA)
                   (diagC {M = t} {M' = t'} {T = SigmaB A B} (AC d) (\ E2 -> Form.sigR E2 iA iB (AT iA E2) (\ E' -> AT iB E'))) E))
      (AC d)
  AC (conv-Pi (univ-V refl) dA dB dB' cA cB) E Bot c ea aU ec ca = tmBot c
  AC (conv-Pi (univ-V refl) dA dB dB' cA cB) E UCode c ea aU ec ca =
    elM c (univV E)
      (FormX.piR E (isty-el dA) (isty-el dB) (isty-el (snd (pCv cA)))
         (ccTy (isty-el (snd (pCv cA))) (tyeq-sym (tyeq-el cA)) (isty-el dB')) (tyeq-el cA) (tyeq-el cB)
         (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU)) (\ a ea aU -> elTyR a (AC cA E UCode a uUC tt ea aU))
         (\ E' c' ec' cU' -> elTyR c' (AC cB E' UCode c' uUC tt ec' cU')) c ec ca)
  AC (conv-Pi (univ-U f g refl) dA dB dB' cA cB) E Bot c ea aU ec ca = tmBot c
  AC (conv-Pi (univ-U f g refl) dA dB dB' cA cB) E UCode c ea aU ec ca =
    elM c (uRL E (pTm dA))
      (FormX.piR E (isty-el (ty-sub dA)) (isty-el (ty-sub dB)) (isty-el (ty-sub (snd (pCv cA))))
         (ccTy (isty-el (ty-sub (snd (pCv cA)))) (tyeq-sym (tyeq-el (conv-sub cA))) (isty-el (ty-sub dB')))
         (tyeq-el (conv-sub cA)) (tyeq-el (conv-sub cB))
         (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU)) (\ a ea aU -> elTyR a (AC cA E UCode a uUC tt ea aU))
         (\ E' c' ec' cU' -> elTyR c' (AC cB E' UCode c' uUC tt ec' cU')) c ec ca)
  AC (conv-Sigma (univ-V refl) dA dB dB' cA cB) E Bot c ea aU ec ca = tmBot c
  AC (conv-Sigma (univ-V refl) dA dB dB' cA cB) E UCode c ea aU ec ca =
    elM c (univV E)
      (FormX.sigR E (isty-el dA) (isty-el dB) (isty-el (snd (pCv cA)))
         (ccTy (isty-el (snd (pCv cA))) (tyeq-sym (tyeq-el cA)) (isty-el dB')) (tyeq-el cA) (tyeq-el cB)
         (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU)) (\ a ea aU -> elTyR a (AC cA E UCode a uUC tt ea aU))
         (\ E' c' ec' cU' -> elTyR c' (AC cB E' UCode c' uUC tt ec' cU')) c ec ca)
  AC (conv-Sigma (univ-U f g refl) dA dB dB' cA cB) E Bot c ea aU ec ca = tmBot c
  AC (conv-Sigma (univ-U f g refl) dA dB dB' cA cB) E UCode c ea aU ec ca =
    elM c (uRL E (pTm dA))
      (FormX.sigR E (isty-el (ty-sub dA)) (isty-el (ty-sub dB)) (isty-el (ty-sub (snd (pCv cA))))
         (ccTy (isty-el (ty-sub (snd (pCv cA)))) (tyeq-sym (tyeq-el (conv-sub cA))) (isty-el (ty-sub dB')))
         (tyeq-el (conv-sub cA)) (tyeq-el (conv-sub cB))
         (\ a ea aU -> elTyR a (AM dA E UCode a uUC tt ea aU)) (\ a ea aU -> elTyR a (AC cA E UCode a uUC tt ea aU))
         (\ E' c' ec' cU' -> elTyR c' (AC cB E' UCode c' uUC tt ec' cU')) c ec ca)
  AC (conv-Suc d) = sucR (fst (pCv d)) (snd (pCv d)) d (AC d)
  AC (conv-Rec iC iC' qC cz cs ck) = recX iC iC' qC cz cs ck (AT iC) (AC cz) (AC cs) (AC ck)
  AC (conv-Ucode df dg cf cg) E Bot u ea aU eu ua = tmBot u
  AC (conv-Ucode df dg cf cg) E UCode u ea aU eu ua =
    elM u (univV E) (uTy (uRL E (isty-el (ty-Ucode df dg))) (uRR E (isty-el (snd (pCv (conv-Ucode df dg cf cg))))) u eu)
  AC (conv-Fhat cf cg hA hB hB' cA cB) E Bot u ea aU eu ua = tmBot u
  AC {H = H} (conv-Fhat {f = ff} {f' = ff'} {g = gg} {g' = gg'} {A = A} {A' = A'} {B = B} {B' = B'} cf cg hA hB hB' cA cB)
     {s} {s'} E UCode u ea aU eu ua =
    elM u (uRL E (pTm hA))
      (pExpT {G = H} {T = substExpr s (Fhat ff gg A (Lam A B))} {T1 = substExpr s (App (App ff A) (Lam A B))}
         {T' = substExpr s' (Fhat ff' gg' A' (Lam A' B'))} u (hrs-step hr-fhat hrs-refl)
         (qFhat (CSub.w1 (Env.cs E)) (Env.wH E) (fst (pCv cf)) (fst (pCv cg)) hA hB)
        (pExpT' {G = H} {T = substExpr s (App (App ff A) (Lam A B))} {T' = substExpr s' (Fhat ff' gg' A' (Lam A' B'))}
           {T1' = substExpr s' (App (App ff' A') (Lam A' B'))} u (hrs-step hr-fhat hrs-refl)
           (qFhat (CSub.w2 (Env.cs E)) (Env.wH E) (FhatPrime.pf P) (FhatPrime.pg P) (FhatPrime.pA P) (FhatPrime.pB P))
           (elTyR u (fhatX cf hA hB hB' cA cB (TC cf) (AC cf) (AM hA) (AC cA) (AC cB) E UCode u uUC tt eu ua))))
    where P = fhatPrime {B = B} cf cg hA hB' cA
  AC (conv-Ghat cf cg hA hB hB' cA cB cc) E Bot u ea aU eu ua = tmBot u
  AC {H = H} (conv-Ghat {f = ff} {f' = ff'} {g = gg} {g' = gg'} {A = A} {A' = A'} {c = c} {c' = c'} {B = B} {B' = B'}
       cf cg hA hB hB' cA cB cc) {s} {s'} E UCode u ea aU eu ua =
    elM u (uRL E (pTm hA))
      (pExpT {G = H} {T = substExpr s (Ghat ff gg A (Lam A B) c)} {T1 = substExpr s (App (App (App gg A) (Lam A B)) c)}
         {T' = substExpr s' (Ghat ff' gg' A' (Lam A' B') c')} u (hrs-step hr-ghat hrs-refl)
         (tyeq-el (sbCv s (CSub.w1 (Env.cs E)) (Env.wH E) (conv-delta-g (fst (pCv cf)) (fst (pCv cg)) hA hB (fst (pCv cc)))))
        (pExpT' {G = H} {T = substExpr s (App (App (App gg A) (Lam A B)) c)} {T' = substExpr s' (Ghat ff' gg' A' (Lam A' B') c')}
           {T1' = substExpr s' (App (App (App gg' A') (Lam A' B')) c')} u (hrs-step hr-ghat hrs-refl)
           (tyeq-el (sbCv s' (CSub.w2 (Env.cs E)) (Env.wH E)
              (conv-delta-g (FhatPrime.pf P) (FhatPrime.pg P) (FhatPrime.pA P) (FhatPrime.pB P) c2)))
           (elTyR u (ghatX cf cg hA hB hB' cA cB cc (TC cf) (AC cf) (TC cg) (AC cg) (AM hA) (AC cA) (AM hB) (AC cB) (AC cc)
                       E UCode u uUC tt eu ua))))
    where
      P = fhatPrime {B = B} cf cg hA hB' cA
      c2 = ty-conv (snd (pCv cc)) (tyeq-el (conv-sub (conv-Fhat cf cg hA hB hB' cA cB)))

  TC : {h g : Num} {H : Ctx h} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> TyIH H G A A
  TC (conv-refl d) = TM d
  TC (conv-sym d) = TC d
  TC (conv-trans d1 d2) = TC d1
  TC {H = H} (conv-conv {A = X} {B = Y} d q) {s} {s'} E a ea aU =
    pTransT {G = H} {T1 = substExpr s Y} {T2 = substExpr s X} {T3 = substExpr s' Y} a aU
      (pSymT {G = H} {T = substExpr s X} {T' = substExpr s Y} a aU (AE q (envL E) a (inBA q E a ea) aU))
      (AE q E a (inBA q E a ea) aU)
  TC (conv-sub d) = vRel
  TC (conv-R' dA dB d) E a ea aU = uTy (uRL E (pTm dA)) (uRR E (pTm dA)) a ea
  TC (conv-delta-f df dg dA dB) = vRel
  TC (conv-delta-g df dg dA dB dc) = vRel
  TC (conv-beta {A = A} {a = a} {B = B} iA iB dt da) E = substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') da (AM da E)
  TC (conv-funext iA iB dt dt' d) E = Form.piR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-fst-beta iA iB dt du) = AT iA
  TC (conv-snd-beta {A = A} {t = t} {B = B} iA iB dt du) E = substTy E {A = A} {B = B} {N = t} iA (AT iA E) (\ E' -> AT iB E') dt (AM dt E)
  TC (conv-pairext iA iB dt dt' d1 d2) E = Form.sigR E iA iB (AT iA E) (\ E' -> AT iB E')
  TC (conv-rec-zero iC dz ds) = TM dz
  TC (conv-rec-suc {k = k} {C = C} iC dz ds dk) E =
    substTy E {A = Nat} {B = C} {N = Suc k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') (ty-Suc dk) (sucR dk dk (conv-refl dk) (AM dk) E)
  TC (conv-App {A = A} {a = a} {a' = a'} {B = B} iA iB d1 d2) E =
    substTy E {A = A} {B = B} {N = a} iA (AT iA E) (\ E' -> AT iB E') (fst (pCv d2)) (diagC {M = a} {M' = a'} {T = A} (AC d2) (AT iA) E)
  TC (conv-Fst iA iB d) = AT iA
  TC (conv-Snd {A = A} {t = t} {t' = t'} {B = B} iA iB d) E =
    substTy E {A = A} {B = B} {N = Fst t} iA (AT iA E) (\ E' -> AT iB E') (ty-Fst iA iB (fst (pCv d)))
      (fstR {A = A} {B = B} {t = t} {t' = t} (fst (pCv d)) (AT iA)
         (diagC {M = t} {M' = t'} {T = SigmaB A B} (AC d) (\ E2 -> Form.sigR E2 iA iB (AT iA E2) (\ E' -> AT iB E'))) E)
  TC (conv-Pi (univ-V refl) dA dB dB' cA cB) = vRel
  TC (conv-Pi (univ-U f g refl) dA dB dB' cA cB) E a ea aU = uTy (uRL E (pTm dA)) (uRR E (pTm dA)) a ea
  TC (conv-Sigma (univ-V refl) dA dB dB' cA cB) = vRel
  TC (conv-Sigma (univ-U f g refl) dA dB dB' cA cB) E a ea aU = uTy (uRL E (pTm dA)) (uRR E (pTm dA)) a ea
  TC (conv-Suc d) = natRel
  TC (conv-Rec {k = k} {k' = k'} {C = C} iC iC' qC cz cs ck) E =
    substTy E {A = Nat} {B = C} {N = k} (NatTy (Env.wG E)) (natRel E) (\ E' -> AT iC E') (fst (pCv ck))
      (diagC {M = k} {M' = k'} {T = Nat} (AC ck) natRel E)
  TC (conv-Ucode df dg cf cg) = vRel
  TC (conv-Fhat cf cg hA hB hB' cA cB) E a ea aU = uTy (uRL E (pTm hA)) (uRR E (pTm hA)) a ea
  TC (conv-Ghat cf cg hA hB hB' cA cB cc) E a ea aU = uTy (uRL E (pTm hA)) (uRR E (pTm hA)) a ea
