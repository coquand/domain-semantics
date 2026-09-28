{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Eta
--
-- η:  c = λ(A,B, app(A↑,B↑,c↑,v0)) : Π(A,B).
--
-- The η-expansion L of c has the same value as c; an application of L
-- β-reduces (on the nose, syntactically) to the application of c with
-- annotations (A,B).  So L is valid through c's own Π-record, and c, L
-- are related pointwise by c's appE clause (with two annotations).
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Eta (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import BCDE4.Basic using (Fin ; fzero ; fsuc ; wkRen ; liftRen ; Eq-cong)
open import BCDE4.Dom.Kernel using (EvalFun ; FinMem)
open import BCDE4.Model.Eval D using (EnvApprox ; EvalRel ; CoherentEnv)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTm ;
  liftSub-WtSub ; isType-Pi ; subst1-wk)
open import BCDE4.RussellMetaCong using (subst1-cong-Ty)
open import BCDE4.RussellReduction using (HeadRed ; headred-refl ; headred-step ; headred-beta ;
  mkRed ; Red-unique-Pi)

open import BCDE4.Levels using (LCtx ; LSub ; lidS)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- Reading a function's record at the literal product it is typed with
------------------------------------------------------------------------

private
  fixV : {n : Nat} {H : Ctx n} {M A A0 : Expr n} {B B0 : Expr (suc n)} {b : FinEl} {f g : FinFun} ->
    Eq A A0 -> Eq B B0 -> PiAppVal2 H M A0 B0 b f g -> PiAppVal2 H M A B b f g
  fixV refl refl p = p

  fixE : {n : Nat} {H : Ctx n} {M A A0 : Expr n} {B B0 : Expr (suc n)} {b : FinEl} {f g : FinFun} ->
    Eq A A0 -> Eq B B0 -> PiAppEq2 H M A0 B0 b f g -> PiAppEq2 H M A B b f g
  fixE refl refl p = p

  uniq : {n : Nat} {H : Ctx n} {A A0 : Expr n} {B B0 : Expr (suc n)} ->
    Red3 H (Pi A B) (Pi A0 B0) -> Pair (Eq A A0) (Eq B B0)
  uniq {H = H} r = Red-unique-Pi {G = H} (mkRed headred-refl) (mkRed (Red3.hr r))

  appV-at : {n : Nat} {H : Ctx n} {M A : Expr n} {B : Expr (suc n)} {g : FinFun} {b : FinEl} {f : FinFun} ->
    RValPi H M (Pi A B) g b f -> PiAppVal2 H M A B b f g
  appV-at {g = g} {b = b} {f = f} r = let e = uniq (RValPi.red r) in fixV {b = b} {f = f} {g = g} (fst e) (snd e) (RValPi.appV r)

  appE-at : {n : Nat} {H : Ctx n} {M A : Expr n} {B : Expr (suc n)} {g : FinFun} {b : FinEl} {f : FinFun} ->
    RValPi H M (Pi A B) g b f -> PiAppEq2 H M A B b f g
  appE-at {g = g} {b = b} {f = f} r = let e = uniq (RValPi.red r) in fixE {b = b} {f = f} {g = g} (fst e) (snd e) (RValPi.appE r)

------------------------------------------------------------------------
-- The η-expanded body, substituted, applied: the syntactic identity
--   (app(A↑,B↑,c↑,v0))[σ↑][N]  =  app(A[σ],B[σ↑],c[σ],N)
------------------------------------------------------------------------

etaBody : {g : Nat} -> Expr g -> Expr (suc g) -> Expr g -> Expr (suc g)
etaBody A B c = App (wkExpr A) (renExpr (liftRen wkRen) B) (wkExpr c) (Var fzero)

private
  W1 : {h g : Nat} (sigma : Sub h g) (X : Expr g) (N : Expr h) ->
    Eq (subst1 (substExpr (liftSub sigma) (wkExpr X)) N) (substExpr sigma X)
  W1 sigma X N =
    Eq-trans (Eq-cong (\ Y -> subst1 Y N) (subst-wk-comm sigma X)) (subst1-wk (substExpr sigma X) N)

  W2pt : {h g : Nat} (sigma : Sub h g) (N : Expr h) (i : Fin (suc g)) ->
    Eq (substExpr (liftSub (subst1Sub N)) (liftSub (liftSub sigma) (liftRen wkRen i))) (liftSub sigma i)
  W2pt sigma N fzero    = refl
  W2pt sigma N (fsuc j) =
    Eq-trans (subst-wk-comm (subst1Sub N) (wkExpr (sigma j)))
             (Eq-cong wkExpr (subst1-wk (sigma j) N))

  W2 : {h g : Nat} (sigma : Sub h g) (B : Expr (suc g)) (N : Expr h) ->
    Eq (substExpr (liftSub (subst1Sub N)) (substExpr (liftSub (liftSub sigma)) (renExpr (liftRen wkRen) B)))
       (substExpr (liftSub sigma) B)
  W2 sigma B N =
    Eq-trans (subst-subst (liftSub (subst1Sub N)) (liftSub (liftSub sigma)) (renExpr (liftRen wkRen) B))
      (Eq-trans (subst-ren (\ i -> substExpr (liftSub (subst1Sub N)) (liftSub (liftSub sigma) i)) (liftRen wkRen) B)
         (substExpr-ext _ (liftSub sigma) (W2pt sigma N) B))

eta-red : {h g : Nat} (sigma : Sub h g) (A : Expr g) (B : Expr (suc g)) (c : Expr g) (N : Expr h) ->
  Eq (subst1 (substExpr (liftSub sigma) (etaBody A B c)) N)
     (App (substExpr sigma A) (substExpr (liftSub sigma) B) (substExpr sigma c) N)
eta-red sigma A B c N =
  Eq-cong3' (W1 sigma A N) (W2 sigma B N) (W1 sigma c N)
  where
    Eq-cong3' : {X X' Z Z' : Expr _} {Y Y' : Expr (suc _)} ->
      Eq X X' -> Eq Y Y' -> Eq Z Z' -> Eq (App X Y Z N) (App X' Y' Z' N)
    Eq-cong3' refl refl refl = refl

------------------------------------------------------------------------
-- The η combinator
------------------------------------------------------------------------

private
  eta-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c : Expr g} ->
    IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) ->
    Adq G c (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (g0 : FinFun) -> EvalRel (strip c) rho (FunEl g0) ->
    (b : FinEl) -> (f0 : FinFun) -> EvalRel (strip (Pi A B)) rho (PiCode b f0) ->
    FinMem (FunEl g0) (PiCode b f0) ->
    EqVal2 H (substExpr sigma c) (substExpr sigma (Lam A B (etaBody A B c)))
             (substExpr sigma (Pi A B)) (FunEl g0) (PiCode b f0)
  eta-core {H = H} {A = A} {B = B} {c = c} d1 d2 dc IH-c sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
    mk-EqValPi vtPi rvc rL rE
    where
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sc  = substExpr sigma c
      L   = substExpr sigma (Lam A B (etaBody A B c))
      wsL = liftSub-WtSub wtsub wfH d1
      htA = subst-IsType wtsub wfH d1
      htB = subst-IsType wsL (wf-extend htA) d2
      htc = subst-HasType wtsub wfH dc
      deta : ConvTm H sc L (Pi sA sB)
      deta = subst-ConvTm wtsub wfH (conv-eta d1 d2 dc)
      valc = IH-c sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
      rvc  = un-ValPi valc
      vtPi = valPi-ty valc
      avc  = appV-at rvc
      aec  = appE-at rvc
      rfl  = Ann-refl htA htB

      hrL : {A1 : Expr _} {B1 : Expr (suc _)} (N : Expr _) ->
        HeadRed (App A1 B1 L N) (App sA sB sc N)
      hrL {A1} {B1} N = S.Eq-transport (\ X -> HeadRed (App A1 B1 L N) X) (eta-red sigma A B c N)
                (headred-step headred-beta headred-refl)

      cvL : {A1 : Expr _} {B1 : Expr (suc _)} -> Ann H sA sB A1 B1 ->
        {N : Expr _} -> HasType H N sA ->
        ConvTm H (App A1 B1 L N) (App sA sB sc N) (subst1 sB N)
      cvL an htN =
        conv-trans (ann-App-fun htA an (conv-sym deta) htN)
                   (conv-sym (conv-cong-App-Ty htA htB (conv-Ty-sym (Ann.annA an)) (conv-Ty-sym (Ann.annB an)) htc htN))

      rL : RValPi H L (Pi sA sB) g0 b f0
      rL = record
        { domA0 = sA ; codB0 = sB
        ; red   = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
        ; cohG  = RValPi.cohG rvc ; fmG = RValPi.fmG rvc
        ; appV  = \ u v sel an N htN valN ->
            Val2-beta-expand v (EvalFun f0 u) (hrL N) (cvL an htN) (avc u v sel rfl N htN valN)
        ; appE  = \ u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN ->
            EqVal2-headred-expand v (EvalFun f0 u) (hrL N1) (hrL N2) (cvL an1 htN1)
              (conv-conv (cvL an2 htN2) (subst1-cong-Ty (conv-sym cvN) htA htB))
              (aec u v sel rfl rfl N1 N2 htN1 htN2 cvN eqN) }

      rE : REqValPi H sc L (Pi sA sB) g0 b f0
      rE = record
        { domA0 = sA ; codB0 = sB
        ; red   = mkRed3 headred-refl (conv-Ty-refl (isType-Pi htA htB))
        ; cohG  = RValPi.cohG rvc ; fmG = RValPi.fmG rvc
        ; appEV = \ u v sel an1 an2 P htP valP ->
            EqVal2-headred-expand v (EvalFun f0 u) headred-refl (hrL P)
              (conv-refl (ann-App-ty htA an1 htc htP)) (cvL an2 htP)
              (aec u v sel an1 rfl P P htP htP (conv-refl htP) (Val2-to-EqVal2 u b valP)) }

AdqE1-eta : {g : Nat} {G : Ctx g} {A : Expr g} {B : Expr (suc g)} {c : Expr g} ->
  IsType G A -> IsType (extend G A) B -> HasType G c (Pi A B) ->
  Adq G c (Pi A B) ->
  AdqE1 G c (Lam A B (etaBody A B c)) (Pi A B)
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH u            hu Bot          evA fm = tt
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH u            hu (UCode _)    () fm
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH u            hu (FunEl _)    () fm
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH Bot          hu (PiCode b f0) evA fm = tt
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH (UCode _)    hu (PiCode b f0) evA fm = tt
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH (PiCode _ _) hu (PiCode b f0) evA fm = tt
AdqE1-eta d1 d2 dc IH-c sigma rho crho vs fits wt wfH (FunEl g0)   hu (PiCode b f0) evA fm =
  eta-core d1 d2 dc IH-c sigma rho crho vs fits wt wfH g0 hu b f0 evA fm
