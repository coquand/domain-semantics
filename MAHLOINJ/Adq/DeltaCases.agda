{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/DeltaCases.agda
--
-- The delta chains of the fundamental lemma, assembled from the
-- induction hypotheses (diagonal and two-sided).
------------------------------------------------------------------------

module MAHLOINJ.Adq.DeltaCases where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (FinEl ; UCode ; tt)
open import MAHLOINJ.Domain.Kernel using (FinMem)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Weaken using (wkTE)
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf using (wfTm)
open import MAHLOINJ.Syntax.CtxConv using (ccTm)
open import MAHLOINJ.Syntax.Presup using (pCv ; lamV ; opGEq)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Env
open import MAHLOINJ.Adq.LamApp using (lamR)
open import MAHLOINJ.Adq.Delta
open import MAHLOINJ.Adq.Syn using (lamConv)

module _ {g : Num} {G : Ctx g} where

  -- the components of the right-hand side of conv-Fhat are well typed
  record FhatPrime (ff' gg' A' : Expr g) (B' : Expr (suc g)) : Set where
    constructor mkFP
    field
      pf : HasType G ff' OpF
      pg : HasType G gg' (OpG ff')
      pA : HasType G A' (Ucode ff' gg')
      pB : HasType (extend G A') B' (wkExpr (Ucode ff' gg'))

  fhatPrime : {ff ff' gg gg' A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G ff ff' OpF -> ConvTm G gg gg' (OpG ff) -> HasType G A (Ucode ff gg) -> HasType (extend G A) B' (wkExpr (Ucode ff gg)) ->
    ConvTm G A A' (Ucode ff gg) -> FhatPrime ff' gg' A' B'
  fhatPrime cf cg hA hB' cA =
    mkFP f2 (ty-conv g2 (opGEq w f1 f2 cf)) (ty-conv A2 eU) (ty-conv (ccTm hA'ty qA'A hB') (wkTE hA'ty eU))
    where
      f1 = fst (pCv cf) ; f2 = snd (pCv cf)
      g1 = fst (pCv cg) ; g2 = snd (pCv cg)
      w = wfTm f1
      eU = tyeq-el (conv-Ucode f1 g1 cf cg)
      A2 = snd (pCv cA)
      hA'ty = isty-el (ty-sub A2)
      qA'A = tyeq-sym (tyeq-el (conv-sub cA))


univV : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> UnivR H V
univV E = univR (univ-V refl) (isty-V (Env.wH E))

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  -- f A (\x:A.B), diagonal
  fhatD : {ff gg A : Expr g} {B : Expr (suc g)} ->
    HasType G ff OpF -> HasType G A (Ucode ff gg) -> HasType (extend G A) B (wkExpr (Ucode ff gg)) ->
    TyIH H G OpF OpF -> TmIH H G ff ff OpF -> TmIH H G A A (Ucode ff gg) -> TmIH H (extend G A) B B (wkExpr (Ucode ff gg)) ->
    TmIH H G (App (App ff A) (Lam A B)) (App (App ff A) (Lam A B)) V
  fhatD {ff} {gg} {A} {B} df dA dB TS Ff FA FB {s} {s'} {rho} E =
    fhatC E {ff = ff} {ff' = ff} {A = A} {A' = A} {L = Lam A B} {L' = Lam A B} df (ty-sub dA) (lamV dA dB) cA cL (TS E) (Ff E) AV AV lamF
    where
      wH = Env.wH E ; cs = Env.cs E
      cA = conv-sub (fst (fTm s s' cs wH dA))
      cL = fst (fTm s s' cs wH (lamV dA dB))
      AV = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FA E a u ea aU eu ua)
      iAt = isty-el (ty-sub dA)
      lamF = lamR E iAt (isty-V (wf-extend iAt)) (ty-sub dB)
               (\ a ea aU -> elTyR a (FA E UCode a uUC tt ea aU)) (\ E' -> vRel E')
               (\ E' a u ea aU eu ua -> reUnivAt (univV E') a u ea (FB E' a u ea aU eu ua))

  -- the left delta-f conversion, substituted
  qFhat : {s : Sub h g} {ff gg A : Expr g} {B : Expr (suc g)} -> WtSub H G s -> WfCtx H ->
    HasType G ff OpF -> HasType G gg (OpG ff) -> HasType G A (Ucode ff gg) -> HasType (extend G A) B (wkExpr (Ucode ff gg)) ->
    TyEq H (substExpr s (Fhat ff gg A (Lam A B))) (substExpr s (App (App ff A) (Lam A B)))
  qFhat {s} ws wH df dg dA dB = tyeq-el (sbCv s ws wH (conv-delta-f df dg dA dB))

  -- g A (\x:A.B) c, diagonal
  ghatD : {ff gg A c : Expr g} {B : Expr (suc g)} ->
    HasType G ff OpF -> HasType G gg (OpG ff) -> HasType G A (Ucode ff gg) -> HasType (extend G A) B (wkExpr (Ucode ff gg)) ->
    HasType G c (Fhat ff gg A (Lam A B)) ->
    TyIH H G OpF OpF -> TmIH H G ff ff OpF -> TyIH H G (OpG ff) (OpG ff) -> TmIH H G gg gg (OpG ff) ->
    TmIH H G A A (Ucode ff gg) -> TmIH H (extend G A) B B (wkExpr (Ucode ff gg)) ->
    TmIH H G c c (Fhat ff gg A (Lam A B)) ->
    TmIH H G (App (App (App gg A) (Lam A B)) c) (App (App (App gg A) (Lam A B)) c) V
  ghatD {ff} {gg} {A} {c} {B} df dg dA dB dc TF Ff TG Fg FA FB Fc {s} {s'} {rho} E =
    ghatC E {ff = ff} {gg = gg} {gg' = gg} {A = A} {A' = A} {L = Lam A B} {L' = Lam A B} {c = c} {c' = c}
      df dg (ty-sub dA) (lamV dA dB) cA cL cC (TG E) (Fg E) AV AV lamF lamF FC
    where
      wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      cA = conv-sub (fst (fTm s s' cs wH dA))
      cL = fst (fTm s s' cs wH (lamV dA dB))
      qF = qFhat w1 wH df dg dA dB
      cC = conv-conv (fst (fTm s s' cs wH dc)) qF
      AV = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FA E a u ea aU eu ua)
      iAt = isty-el (ty-sub dA)
      lamF = lamR E iAt (isty-V (wf-extend iAt)) (ty-sub dB)
               (\ a ea aU -> elTyR a (FA E UCode a uUC tt ea aU)) (\ E' -> vRel E')
               (\ E' a u ea aU eu ua -> reUnivAt (univV E') a u ea (FB E' a u ea aU eu ua))
      FH = fhatD df dA dB TF Ff FA FB E
      FC : TmRelAt H s s' rho c c (App (App ff A) (Lam A B))
      FC a u ea aU eu ua =
        pConvM {G = H} {M = substExpr s c} {M' = substExpr s' c} {T = substExpr s (Fhat ff gg A (Lam A B))}
          {T' = substExpr s (App (App ff A) (Lam A B))} u a ua aU
          (pExpT {G = H} {T = substExpr s (Fhat ff gg A (Lam A B))} {T1 = substExpr s (App (App ff A) (Lam A B))}
             {T' = substExpr s (App (App ff A) (Lam A B))} a (hrs-step hr-fhat hrs-refl) qF
             (diagL {G = H} {T = substExpr s (App (App ff A) (Lam A B))} {T' = substExpr s' (App (App ff A) (Lam A B))} a aU
                (elTyR a (FH UCode a uUC tt ea aU))))
          (Fc E a u ea aU eu ua)

  -- f A (\x:A.B) ~ f' A' (\x:A'.B')
  fhatX : {ff ff' gg A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G ff ff' OpF -> HasType G A (Ucode ff gg) -> HasType (extend G A) B (wkExpr (Ucode ff gg)) ->
    HasType (extend G A) B' (wkExpr (Ucode ff gg)) -> ConvTm G A A' (Ucode ff gg) ->
    ConvTm (extend G A) B B' (wkExpr (Ucode ff gg)) ->
    TyIH H G OpF OpF -> TmIH H G ff ff' OpF -> TmIH H G A A (Ucode ff gg) -> TmIH H G A A' (Ucode ff gg) ->
    TmIH H (extend G A) B B' (wkExpr (Ucode ff gg)) ->
    TmIH H G (App (App ff A) (Lam A B)) (App (App ff' A') (Lam A' B')) V
  fhatX {ff} {ff'} {gg} {A} {A'} {B} {B'} cf hA hB hB' cA cB TS Ff FA FAx FBx {s} {s'} {rho} E =
    fhatC E {ff = ff} {ff' = ff'} {A = A} {A' = A'} {L = Lam A B} {L' = Lam A' B'}
      (fst (pCv cf)) (ty-sub hA) (lamV hA hB) cAH cLH (TS E) (Ff E) AVd AVx lamX
    where
      wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      cAH = conv-sub (conv-trans (sbCv s w1 wH cA) (fst (fTm s s' cs wH (snd (pCv cA)))))
      iAt = isty-el (ty-sub hA)
      iA't = isty-el (ty-sub (snd (pCv cA)))
      qA = tyeq-el (conv-sub cA)
      lc = lamConv iAt iA't qA (ty-sub hB) (ty-sub hB') (conv-sub cB)
      cLH = conv-trans (sbCv s w1 wH lc) (fst (fTm s s' cs wH (snd (pCv lc))))
      AVd = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FA E a u ea aU eu ua)
      AVx = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FAx E a u ea aU eu ua)
      lamX = lamRX E iAt iA't qA (isty-V (wf-extend iAt)) (ty-sub hB) (ccTm iA't (tyeq-sym qA) (ty-sub hB'))
               (\ a ea aU -> elTyR a (FA E UCode a uUC tt ea aU)) (\ E' -> vRel E')
               (\ E' a u ea aU eu ua -> reUnivAt (univV E') a u ea (FBx E' a u ea aU eu ua))

  -- g A (\x:A.B) c ~ g' A' (\x:A'.B') c'
  ghatX : {ff ff' gg gg' A A' c c' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G ff ff' OpF -> ConvTm G gg gg' (OpG ff) -> HasType G A (Ucode ff gg) ->
    HasType (extend G A) B (wkExpr (Ucode ff gg)) -> HasType (extend G A) B' (wkExpr (Ucode ff gg)) ->
    ConvTm G A A' (Ucode ff gg) -> ConvTm (extend G A) B B' (wkExpr (Ucode ff gg)) ->
    ConvTm G c c' (Fhat ff gg A (Lam A B)) ->
    TyIH H G OpF OpF -> TmIH H G ff ff' OpF -> TyIH H G (OpG ff) (OpG ff) -> TmIH H G gg gg' (OpG ff) ->
    TmIH H G A A (Ucode ff gg) -> TmIH H G A A' (Ucode ff gg) ->
    TmIH H (extend G A) B B (wkExpr (Ucode ff gg)) -> TmIH H (extend G A) B B' (wkExpr (Ucode ff gg)) ->
    TmIH H G c c' (Fhat ff gg A (Lam A B)) ->
    TmIH H G (App (App (App gg A) (Lam A B)) c) (App (App (App gg' A') (Lam A' B')) c') V
  ghatX {ff} {ff'} {gg} {gg'} {A} {A'} {c} {c'} {B} {B'} cf cg hA hB hB' cA cB cc TF Ff TG Fg FA FAx FB FBx Fcx {s} {s'} {rho} E =
    ghatC E {ff = ff} {gg = gg} {gg' = gg'} {A = A} {A' = A'} {L = Lam A B} {L' = Lam A' B'} {c = c} {c' = c'}
      f1 g1 (ty-sub hA) (lamV hA hB) cAH cLH cCH (TG E) (Fg E) AVd AVx lamD lamX FC
    where
      wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      f1 = fst (pCv cf) ; g1 = fst (pCv cg)
      cAH = conv-sub (conv-trans (sbCv s w1 wH cA) (fst (fTm s s' cs wH (snd (pCv cA)))))
      iAt = isty-el (ty-sub hA)
      iA't = isty-el (ty-sub (snd (pCv cA)))
      qA = tyeq-el (conv-sub cA)
      lc = lamConv iAt iA't qA (ty-sub hB) (ty-sub hB') (conv-sub cB)
      cLH = conv-trans (sbCv s w1 wH lc) (fst (fTm s s' cs wH (snd (pCv lc))))
      qF = qFhat w1 wH f1 g1 hA hB
      cCH = conv-conv (conv-trans (sbCv s w1 wH cc) (fst (fTm s s' cs wH (snd (pCv cc))))) qF
      AVd = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FA E a u ea aU eu ua)
      AVx = \ a u ea aU eu ua -> reUnivAt (univV E) a u ea (FAx E a u ea aU eu ua)
      VA = \ a ea aU -> elTyR a (FA E UCode a uUC tt ea aU)
      lamD = lamR E iAt (isty-V (wf-extend iAt)) (ty-sub hB) VA (\ E' -> vRel E')
               (\ E' a u ea aU eu ua -> reUnivAt (univV E') a u ea (FB E' a u ea aU eu ua))
      lamX = lamRX E iAt iA't qA (isty-V (wf-extend iAt)) (ty-sub hB) (ccTm iA't (tyeq-sym qA) (ty-sub hB')) VA (\ E' -> vRel E')
               (\ E' a u ea aU eu ua -> reUnivAt (univV E') a u ea (FBx E' a u ea aU eu ua))
      FH = fhatD f1 hA hB TF (diagC {M = ff} {M' = ff'} {T = OpF} Ff TF) FA FB E
      FC : TmRelAt H s s' rho c c' (App (App ff A) (Lam A B))
      FC a u ea aU eu ua =
        pConvM {G = H} {M = substExpr s c} {M' = substExpr s' c'} {T = substExpr s (Fhat ff gg A (Lam A B))}
          {T' = substExpr s (App (App ff A) (Lam A B))} u a ua aU
          (pExpT {G = H} {T = substExpr s (Fhat ff gg A (Lam A B))} {T1 = substExpr s (App (App ff A) (Lam A B))}
             {T' = substExpr s (App (App ff A) (Lam A B))} a (hrs-step hr-fhat hrs-refl) qF
             (diagL {G = H} {T = substExpr s (App (App ff A) (Lam A B))} {T' = substExpr s' (App (App ff A) (Lam A B))} a aU
                (elTyR a (FH UCode a uUC tt ea aU))))
          (Fcx E a u ea aU eu ua)
