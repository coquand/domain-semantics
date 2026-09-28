{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Level
--
-- The adequacy combinators for universe-level products [α]A:
--
--   AdqTy-LPi, AdqConvTy-LPi, AdqETy-LPi    (formation, both forms,
--                                            and conv-Ty-LPi);
--   Adq-LLam, AdqConv-LLam, AdqE1-LLam      (abstraction, and its
--                                            congruences conv-cong-LLam / -Ty).
--
-- The application / β / η combinators are in BCDE4.Adeq.LevelApp.
--
-- A selected edge (u, v) of a level function is either ⊥ or lives at a
-- canonical token LevEl k ≤ u; for an admissible level l (u ≤ LevEl
-- (codeL H l)) the token is the code of l, and the body evaluates at
-- lsub1 _ l (lpi-app-cases).  The IH families at lsub1 A l, lsub1 u l
-- are then used at the SAME substitution and environment.
--
-- Non-recursive: all IHs are parameters.  No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Level (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; refl ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0 ;
              LevTy ; LevEl ; LPiCode)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; CoherentFunTail ; FinMem ; EvalFun ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  finMem-LpiU-allU ; finMem-LpiU-cft ;
  finMem-Lfunel-fun ; finMem-Lfunel-coh ; finMem-Lfunel-wf)
open import BCDE4.Model.Eval D using (EnvApprox ; EvalRel ; CoherentEnv ; EvalRel-down ; lcodeT)
open import BCDE4.Model.SoundnessLevel D using (lpi-app-cases ; LPi-app-type)
open import BCDE4.Model.SoundnessLemmas D using (Fits)
open import BCDE4.Model.Selection using (Selection ; Coherent-Selection ;
  FinMem-Selection-UCode ; FinMem-Selection-codomain)
open import BCDE4.Model.Strip using (strip ; stripCtx ; strip-lsubE)
import BCDE4.Model.Core as C
open import BCDE4.RussellSyntax using (Expr ; U ; LPi ; LLam ; LApp ; lsub1 ; lshiftE ; Sub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; subst-IsType ; subst-HasType ; subst-ConvTy ; subst-ConvTm ;
  WtSub-addL ; wkL-WfCtx ; isType-LPi ; subst-lsub1 ; presup-r-ConvTy ; typing-ConvTm)
open import BCDE4.RussellMetaCong using (subst-cong-IsType ; ConvTmSub-addL ; csL)
open import BCDE4.RussellReduction using (HeadRed ; headred-refl ; headred-step ; headred-lbeta)

open import BCDE4.Levels using (LCtx ; LSub ; LExpr ; lidS ; lsubL ; lsub1S ; lsubL-id ;
  Valid ; ValidC ; ceq ; lsubC ; lsubC-id ; v-sym)
open import BCDE4.Adeq.Guard D using (wt-addC ; vs-addC)
open import BCDE4.Model.RussellSound D using (fits-addC)
open import BCDE4.RussellLeq using (lsub1-cong)
open import BCDE4.Model.Selection using (Coherent-Selection-val)
open import BCDE4.Dom.Kernel using (EvalFun-in-UCode)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

-- the substitution under a level binder
lsh : {h g : Nat} -> Sub h g -> Sub h g
lsh sigma i = lshiftE (sigma i)

EqVal2-tr3 : {n : Nat} {G : Ctx n} {M M' N N' T T' : Expr n} {u a : FinEl} ->
  Eq M M' -> Eq N N' -> Eq T T' -> EqVal2 G M N T u a -> EqVal2 G M' N' T' u a
EqVal2-tr3 refl refl refl e = e

Val2-tr2 : {n : Nat} {G : Ctx n} {M M' T T' : Expr n} {u a : FinEl} ->
  Eq M M' -> Eq T T' -> Val2 G M T u a -> Val2 G M' T' u a
Val2-tr2 refl refl v = v

-- the code of l, as the evaluation of a level application computes it
eqc : {h : Nat} (H : Ctx h) (l : LExpr) -> Eq (lcodeT (lctx H) (lsubL lidS l)) (codeL H l)
eqc H l = S.Eq-cong (lcodeT (lctx H)) (lsubL-id l)

-- admissibility, in the form of the evaluation
lelE : {h : Nat} (H : Ctx h) (l : LExpr) {u : FinEl} ->
  LeCode u (LevEl (codeL H l)) -> LeCode u (LevEl (lcodeT (lctx H) (lsubL lidS l)))
lelE H l {u} lel = S.Eq-transport (\ k -> LeCode u (LevEl k)) (S.Eq-sym (eqc H l)) lel

-- instantiation, through strip
evInst : {h g : Nat} {H : Ctx h} (X : Expr g) (l : LExpr) (rho : EnvApprox (lctx H) lidS g) (v : FinEl) ->
  EvalRel (C.lsub1 (strip X) l) rho v -> EvalRel (strip (lsub1 X l)) rho v
evInst X l rho v ev = S.Eq-transport (\ Y -> EvalRel Y rho v) (S.Eq-sym (strip-lsubE (lsub1S l) X)) ev

-- the body of a level product at a selected edge, at an admissible level
edgeEv : {h g : Nat} {H : Ctx h} (X : Expr g) (rho : EnvApprox (lctx H) lidS g) (f : FinFun) ->
  CoherentFunTail f -> EvalRel (strip (LPi X)) rho (LPiCode f) ->
  (u v : FinEl) -> Selection f u v -> (l : LExpr) -> LeCode u (LevEl (codeL H l)) ->
  EvalRel (strip (lsub1 X l)) rho v
edgeEv {H = H} X rho f cf hu u v sel l lel =
  evInst {H = H} X l rho v
    (lpi-app-cases (strip X) l rho u v (Coherent-Selection sel cf) (lelE H l {u} lel) (snd hu u v sel))

EqValTy2-snd' : {h : Nat} {H : Ctx h} {M N : Expr h} (a : FinEl) ->
  EqValTy2 H M N a -> ValTy2 H N a
EqValTy2-snd' Bot          e = tt
EqValTy2-snd' (UCode _)    e = snd e
EqValTy2-snd' (FunEl _)    e = tt
EqValTy2-snd' (PiCode _ _) e = fst (snd e)
EqValTy2-snd' LevTy        e = tt
EqValTy2-snd' (LevEl _)    e = tt
EqValTy2-snd' (LPiCode _)  e = fst (snd e)

------------------------------------------------------------------------
-- The level-variation hypotheses: a statement in Γ,(l = l'), used in a
-- target where l = l' is valid.
------------------------------------------------------------------------

LvTy : {g : Nat} -> Ctx g -> Expr g -> Set
LvTy G A = (l l' : LExpr) -> AdqETy (addC G (ceq l l')) (lsub1 A l) (lsub1 A l')

LvTm : {g : Nat} -> Ctx g -> Expr g -> Expr g -> Set
LvTm G u A = (l l' : LExpr) -> AdqE1 (addC G (ceq l l')) (lsub1 u l) (lsub1 u l') (lsub1 A l)

private
  vC : {h : Nat} {H : Ctx h} {l l' : LExpr} -> Valid (lctx H) l l' -> ValidC (lctx H) (lsubC lidS (ceq l l'))
  vC {H = H} {l} {l'} e = S.Eq-transport (ValidC (lctx H)) (S.Eq-sym (lsubC-id (ceq l l'))) e

useLvTy : {h g : Nat} {H : Ctx h} {G : Ctx g} {A B : Expr g} (l l' : LExpr) ->
  AdqETy (addC G (ceq l l')) A B ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H -> Valid (lctx H) l l' ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem a U0 ->
  EqValTy2 H (substExpr sigma A) (substExpr sigma B) a
useLvTy {H = H} {G = G} l l' IH sigma rho crho vs fits wt wfH e a ev aU =
  IH sigma rho crho (vs-addC {G = G} (ceq l l') vs) (fits-addC {G = G} (ceq l l') fits (vC {H = H} e))
     (wt-addC (ceq l l') wt e) wfH a ev aU

useLvE1 : {h g : Nat} {H : Ctx h} {G : Ctx g} {M N A : Expr g} (l l' : LExpr) ->
  AdqE1 (addC G (ceq l l')) M N A ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H -> Valid (lctx H) l l' ->
  (u : FinEl) -> EvalRel (strip M) rho u ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a
useLvE1 {H = H} {G = G} l l' IH sigma rho crho vs fits wt wfH e u hu a ev fm =
  IH sigma rho crho (vs-addC {G = G} (ceq l l') vs) (fits-addC {G = G} (ceq l l') fits (vC {H = H} e))
     (wt-addC (ceq l l') wt e) wfH u hu a ev fm

------------------------------------------------------------------------
-- Formation
------------------------------------------------------------------------

ty-LPi-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
  IsType (addL G) A -> ((l : LExpr) -> AdqTy G (lsub1 A l)) -> LvTy G A ->
  (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem (LPiCode f) U0 ->
  ValTy2 H (LPi (substExpr (lsh sigma) A)) (LPiCode f)
ty-LPi-core {H = H} {A = A} d1 IH IHlv sigma rho crho vs fits wt wfH f hu fm =
  mk-ValTyLPi (record
    { domA = sA
    ; red = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA))
    ; cohF = cf ; fmAllU = allU ; htA = htA
    ; edgeV = \ u v sel l lel ->
        ValTy2-transport (subst-lsub1 sigma A l)
          (IH l sigma rho crho vs fits wt wfH v (edgeEv {H = H} A rho f cf hu u v sel l lel)
             (FinMem-Selection-UCode LevTy sel allU cf))
    ; edgeLE = \ u v sel l l' e lel ->
        EqValTy2-transport (subst-lsub1 sigma A l) (subst-lsub1 sigma A l')
          (useLvTy {A = lsub1 A l} {B = lsub1 A l'} l l' (IHlv l l') sigma rho crho vs fits wt wfH e v
             (edgeEv {H = H} A rho f cf hu u v sel l lel)
             (FinMem-Selection-UCode LevTy sel allU cf)) })
  where
    sA   = substExpr (lsh sigma) A
    htA  = subst-IsType (WtSub-addL wt) (wkL-WfCtx wfH) d1
    allU = finMem-LpiU-allU f fm
    cf   = finMem-LpiU-cft f fm

AdqTy-LPi : {g : Nat} {G : Ctx g} {A : Expr g} ->
  WfCtx G -> IsType (addL G) A -> ((l : LExpr) -> AdqTy G (lsub1 A l)) -> LvTy G A -> AdqTy G (LPi A)
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH Bot          hu fm = tt
AdqTy-LPi {A = A} d0 d1 IH IHlv sigma rho crho vs fits wt wfH (LPiCode f) hu fm =
  ty-LPi-core {A = A} d1 IH IHlv sigma rho crho vs fits wt wfH f hu fm
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH (UCode _)    () fm
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH LevTy        () fm
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH (LevEl _)    () fm
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH (FunEl _)    () fm
AdqTy-LPi d0 d1 IH IHlv sigma rho crho vs fits wt wfH (PiCode _ _) () fm

------------------------------------------------------------------------
-- Two substitutions
------------------------------------------------------------------------

private
  conv-LPi-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g} ->
    IsType (addL G) A -> ((l : LExpr) -> AdqConvTy G (lsub1 A l)) -> LvTy G A ->
    (sigma sigma' : Sub h g) (rho : EnvApprox (lctx H) lidS g) -> CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
    (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem (LPiCode f) U0 ->
    EqValTy2 H (LPi (substExpr (lsh sigma) A)) (LPi (substExpr (lsh sigma') A)) (LPiCode f)
  conv-LPi-core {H = H} {G = G} {A = A} d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH f hu fm =
    mk-EqValTyLPi (ty-LPi-core {A = A} d1 IH1 IHlv sigma rho crho vs fits wt wfH f hu fm)
                  (ty-LPi-core {A = A} d1 IH1 IHlv sigma' rho crho vs' fits wt' wfH f hu fm)
      (record
        { domA = sA ; domA' = sA'
        ; redM = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA))
        ; redN = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA'))
        ; cohF = cf ; fmAllU = allU
        ; convA = subst-cong-IsType (ConvTmSub-addL wcs) wfL d1
        ; edgeET = \ u v sel l lel ->
            EqValTy2-transport (subst-lsub1 sigma A l) (subst-lsub1 sigma' A l)
              (IH l sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH v
                 (edgeEv {H = H} A rho f cf hu u v sel l lel)
                 (FinMem-Selection-UCode LevTy sel allU cf)) })
    where
      IH1 : (l : LExpr) -> AdqTy G (lsub1 A l)
      IH1 l = AdqConvTy-to-AdqTy {G = G} {A = lsub1 A l} (IH l)
      sA   = substExpr (lsh sigma) A
      sA'  = substExpr (lsh sigma') A
      wfL  = wkL-WfCtx wfH
      htA  = subst-IsType (WtSub-addL wt) wfL d1
      htA' = subst-IsType (WtSub-addL wt') wfL d1
      allU = finMem-LpiU-allU f fm
      cf   = finMem-LpiU-cft f fm

AdqConvTy-LPi : {g : Nat} {G : Ctx g} {A : Expr g} ->
  WfCtx G -> IsType (addL G) A -> ((l : LExpr) -> AdqConvTy G (lsub1 A l)) -> LvTy G A -> AdqConvTy G (LPi A)
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH Bot          hu fm = tt
AdqConvTy-LPi {A = A} d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (LPiCode f) hu fm =
  conv-LPi-core {A = A} d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH f hu fm
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (UCode _)    () fm
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH LevTy        () fm
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (LevEl _)    () fm
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (FunEl _)    () fm
AdqConvTy-LPi d0 d1 IH IHlv sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH (PiCode _ _) () fm

------------------------------------------------------------------------
-- Conversion of level products (conv-Ty-LPi)
------------------------------------------------------------------------

private
  eq-LPi-core : {h g : Nat} {H : Ctx h} {G : Ctx g} {A B : Expr g} ->
    IsType (addL G) A -> ConvTy (addL G) A B ->
    ((l : LExpr) -> AdqETy G (lsub1 A l) (lsub1 B l)) -> LvTy G A ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem (LPiCode f) U0 ->
    EqValTy2 H (LPi (substExpr (lsh sigma) A)) (LPi (substExpr (lsh sigma) B)) (LPiCode f)
  eq-LPi-core {H = H} {G = G} {A = A} {B = B} d1 cAB IH IHlv sigma rho crho vs fits wt wfH f hu fm =
    mk-EqValTyLPi vtA vtB
      (record
        { domA = sA ; domA' = sB
        ; redM = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA))
        ; redN = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htB))
        ; cohF = cf ; fmAllU = allU
        ; convA = scAB
        ; edgeET = eET })
    where
      IH1 : (l : LExpr) -> AdqTy G (lsub1 A l)
      IH1 l = AdqETy-to-AdqTy {G = G} {A = lsub1 A l} {B = lsub1 B l} (IH l)
      sA   = substExpr (lsh sigma) A
      sB   = substExpr (lsh sigma) B
      wfL  = wkL-WfCtx wfH
      htA  = subst-IsType (WtSub-addL wt) wfL d1
      scAB = subst-ConvTy (WtSub-addL wt) wfL cAB
      htB  = presup-r-ConvTy scAB
      allU = finMem-LpiU-allU f fm
      cf   = finMem-LpiU-cft f fm

      eET : LEdgeEqTy2 H sA sB f
      eET u v sel l lel =
        EqValTy2-transport (subst-lsub1 sigma A l) (subst-lsub1 sigma B l)
          (IH l sigma rho crho vs fits wt wfH v (edgeEv {H = H} A rho f cf hu u v sel l lel)
             (FinMem-Selection-UCode LevTy sel allU cf))

      vtA : ValTy2 H (LPi sA) (LPiCode f)
      vtA = ty-LPi-core {A = A} d1 IH1 IHlv sigma rho crho vs fits wt wfH f hu fm

      -- sB l ~ sA l ~ sA l' ~ sB l'
      eLE : (u v : FinEl) -> Selection f u v -> (l l' : LExpr) -> Valid (lctx H) l l' ->
        LeCode u (LevEl (codeL H l)) -> EqValTy2 H (lsub1 sB l) (lsub1 sB l') v
      eLE u v sel l l' e lel =
        let cv   = Coherent-Selection-val sel cf
            lel' = LeL-transport H {u = u} e lel
            aLE  = RValTyLPi.edgeLE (un-ValTyLPi vtA) u v sel l l' e lel
        in EqValTy2-trans v cv (EqValTy2-sym v cv (eET u v sel l lel))
             (EqValTy2-trans v cv aLE (eET u v sel l' lel'))

      vtB : ValTy2 H (LPi sB) (LPiCode f)
      vtB = mk-ValTyLPi (record
        { domA = sB
        ; red = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htB))
        ; cohF = cf ; fmAllU = allU ; htA = htB
        ; edgeV = \ u v sel l lel -> EqValTy2-snd' v (eET u v sel l lel)
        ; edgeLE = eLE })

AdqETy-LPi : {g : Nat} {G : Ctx g} {A B : Expr g} ->
  WfCtx G -> IsType (addL G) A -> ConvTy (addL G) A B ->
  ((l : LExpr) -> AdqETy G (lsub1 A l) (lsub1 B l)) -> LvTy G A -> AdqETy G (LPi A) (LPi B)
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH Bot          hu fm = tt
AdqETy-LPi {A = A} {B = B} d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH (LPiCode f) hu fm =
  eq-LPi-core {A = A} {B = B} d1 cAB IH IHlv sigma rho crho vs fits wt wfH f hu fm
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH (UCode _)    () fm
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH LevTy        () fm
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH (LevEl _)    () fm
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH (FunEl _)    () fm
AdqETy-LPi d0 d1 cAB IH IHlv sigma rho crho vs fits wt wfH (PiCode _ _) () fm

------------------------------------------------------------------------
-- Level abstraction: one core for the three statements.  The second
-- body u2 is any term of the substituted domain type whose instances
-- are related to those of the first (IHb).
------------------------------------------------------------------------

private
  lamCore' : {h g : Nat} {H : Ctx h} {G : Ctx g} {A u : Expr g} (u2 : Expr h) ->
    IsType (addL G) A -> HasType (addL G) u A -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    LvTy G A -> LvTm G u A ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    {A2 : Expr h} -> ConvTy (addL H) (substExpr (lsh sigma) A) A2 ->
    HasType (addL H) u2 (substExpr (lsh sigma) A) ->
    ((l : LExpr) (v : FinEl) -> EvalRel (strip (lsub1 u l)) rho v ->
      (a : FinEl) -> EvalRel (strip (lsub1 A l)) rho a -> FinMem v a ->
      EqVal2 H (lsub1 (substExpr (lsh sigma) u) l) (lsub1 u2 l) (lsub1 (substExpr (lsh sigma) A) l) v a) ->
    (g0 : FinFun) -> EvalRel (strip (LLam A u)) rho (FunEl g0) ->
    (f : FinFun) -> EvalRel (strip (LPi A)) rho (LPiCode f) -> FinMem (FunEl g0) (LPiCode f) ->
    EqVal2 H (LLam (substExpr (lsh sigma) A) (substExpr (lsh sigma) u)) (LLam A2 u2) (LPi (substExpr (lsh sigma) A))
      (FunEl g0) (LPiCode f)
  lamCore' {H = H} {A = A} {u = u} u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH {A2} c2 ht2 IHb g0 hu f evA fm =
    mk-EqValLPi vtA rM rN rE
    where
      sA   = substExpr (lsh sigma) A
      su   = substExpr (lsh sigma) u
      wtL  = WtSub-addL wt
      wfL  = wkL-WfCtx wfH
      htA  = subst-IsType wtL wfL d1
      htu  = subst-HasType wtL wfL d2
      piU  = finMem-Lfunel-wf g0 f fm
      allU = finMem-LpiU-allU f piU
      cf   = finMem-LpiU-cft f piU
      cg   = finMem-Lfunel-coh g0 f fm
      fmg  = finMem-Lfunel-fun g0 f fm
      ctg  = cft-from-cf g0 cg
      vtA  = ty-LPi-core {A = A} d1 IHA IHlvA sigma rho crho vs fits wt wfH f evA piU
      redA = mkRed3 headred-refl (conv-Ty-refl (isType-LPi wfH htA))

      cR   = conv-Ty-refl htA

      hrB : (l : LExpr) {X Y Z : Expr _} -> HeadRed (LApp Y (LLam Z X) l) (lsub1 X l)
      hrB l = headred-step headred-lbeta headred-refl

      appEV : (u' v' : FinEl) -> Selection g0 u' v' -> {A1 A1' : Expr _} -> LAnn H sA A1 -> LAnn H sA A1' ->
        (l : LExpr) -> LeCode u' (LevEl (codeL H l)) ->
        EqVal2 H (LApp A1 (LLam sA su) l) (LApp A1' (LLam A2 u2) l) (lsub1 sA l) v' (EvalFun f u')
      evUat : (u' v' : FinEl) -> Selection g0 u' v' -> (l : LExpr) -> LeCode u' (LevEl (codeL H l)) ->
        EvalRel (strip (lsub1 u l)) rho v'
      evUat u' v' sel l lel =
        evInst {H = H} u l rho v'
          (lpi-app-cases (strip u) l rho u' v' (Coherent-Selection sel ctg) (lelE H l {u'} lel) (snd hu u' v' sel))

      evTat : (u' v' : FinEl) -> Selection g0 u' v' -> (l : LExpr) -> LeCode u' (LevEl (codeL H l)) ->
        EvalRel (strip (lsub1 A l)) rho (EvalFun f u')
      evTat u' v' sel l lel =
        let cu' = Coherent-Selection sel ctg
            c   = lcodeT (lctx H) (lsubL lidS l)
            cef = Coherent-EvalFun f u' cf cu'
        in evInst {H = H} A l rho (EvalFun f u')
             (EvalRel-down (C.lsub1 (strip A) l) rho (EvalFun f (LevEl c)) (EvalFun f u') crho cef
                (LPi-app-type (strip A) l rho f evA)
                (EvalFun-mon-arg f u' (LevEl c) (lelE H l {u'} lel) cf cu' tt))

      fmvAt : (u' v' : FinEl) -> Selection g0 u' v' -> FinMem v' (EvalFun f u')
      fmvAt u' v' sel = FinMem-Selection-codomain LevTy f sel fmg ctg cf allU

      appEV u' v' sel an1 an2 l lel =
        EqVal2-headred-expand v' (EvalFun f u') (hrB l) (hrB l)
          (lann-LApp-beta htA an1 cR htu) (lann-LApp-beta htA an2 c2 ht2)
          (IHb l v' (evUat u' v' sel l lel) (EvalFun f u') (evTat u' v' sel l lel) (fmvAt u' v' sel))

      -- level variation of the first abstraction: from the IH on u
      appLEM : (u' v' : FinEl) -> Selection g0 u' v' -> {A1 A1' : Expr _} -> LAnn H sA A1 -> LAnn H sA A1' ->
        (l l' : LExpr) -> Valid (lctx H) l l' ->
        LeCode u' (LevEl (codeL H l)) ->
        EqVal2 H (LApp A1 (LLam sA su) l) (LApp A1' (LLam sA su) l') (lsub1 sA l) v' (EvalFun f u')
      appLEM u' v' sel an1 an2 l l' e lel =
        EqVal2-headred-expand v' (EvalFun f u') (hrB l) (hrB l')
          (lann-LApp-beta htA an1 cR htu) (conv-conv (lann-LApp-beta htA an2 cR htu) (lsub1-cong htA (v-sym e)))
          (EqVal2-tr3 (subst-lsub1 sigma u l) (subst-lsub1 sigma u l') (subst-lsub1 sigma A l)
             (useLvE1 {M = lsub1 u l} {N = lsub1 u l'} {A = lsub1 A l} l l' (IHlvU l l') sigma rho crho vs fits wt wfH e v' (evUat u' v' sel l lel)
                (EvalFun f u') (evTat u' v' sel l lel) (fmvAt u' v' sel)))

      -- and of the second: through the first, u2 l ~ su l ~ su l' ~ u2 l'
      appLEN : (u' v' : FinEl) -> Selection g0 u' v' -> {A1 A1' : Expr _} -> LAnn H sA A1 -> LAnn H sA A1' ->
        (l l' : LExpr) -> Valid (lctx H) l l' ->
        LeCode u' (LevEl (codeL H l)) ->
        EqVal2 H (LApp A1 (LLam A2 u2) l) (LApp A1' (LLam A2 u2) l') (lsub1 sA l) v' (EvalFun f u')
      appLEN u' v' sel an1 an2 l l' e lel =
        let cu'  = Coherent-Selection sel ctg
            cv'  = Coherent-Selection-val sel ctg
            cef  = Coherent-EvalFun f u' cf cu'
            lel' = LeL-transport H {u = u'} e lel
            tyE  = EqValTy2-transport (subst-lsub1 sigma A l') (subst-lsub1 sigma A l)
                     (useLvTy {A = lsub1 A l'} {B = lsub1 A l} l' l (IHlvA l' l) sigma rho crho vs fits wt wfH (v-sym e) (EvalFun f u')
                        (evTat u' v' sel l' lel') (EvalFun-in-UCode f u' LevTy cf cu' allU))
            e1   = EqVal2-sym v' (EvalFun f u') cv' cef (appEV u' v' sel an1 an1 l lel)
            e3   = EqVal2-EqValTy2-fwd v' (EvalFun f u') cef tyE (appEV u' v' sel an2 an2 l' lel')
        in EqVal2-trans v' (EvalFun f u') cv' cef e1
             (EqVal2-trans v' (EvalFun f u') cv' cef (appLEM u' v' sel an1 an2 l l' e lel) e3)

      rM : RValLPi H (LLam sA su) (LPi sA) g0 f
      rM = record { domA0 = sA ; red = redA ; cohG = cg ; fmG = fmg
                  ; appV = \ u' v' sel an l lel ->
                      Val2-from-EqVal2-first v' (EvalFun f u') (appEV u' v' sel an an l lel)
                  ; appLE = appLEM }

      rN : RValLPi H (LLam A2 u2) (LPi sA) g0 f
      rN = record { domA0 = sA ; red = redA ; cohG = cg ; fmG = fmg
                  ; appV = \ u' v' sel an l lel ->
                      Val2-from-EqVal2-second v' (EvalFun f u') (appEV u' v' sel an an l lel)
                  ; appLE = appLEN }

      rE : REqValLPi H (LLam sA su) (LLam A2 u2) (LPi sA) g0 f
      rE = record { domA0 = sA ; red = redA ; cohG = cg ; fmG = fmg ; appEV = appEV }

  lamCore : {h g : Nat} {H : Ctx h} {G : Ctx g} {A u : Expr g} (u2 : Expr h) ->
    IsType (addL G) A -> HasType (addL G) u A -> ((l : LExpr) -> AdqTy G (lsub1 A l)) ->
    LvTy G A -> LvTm G u A ->
    (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
    WtSub H G sigma -> WfCtx H ->
    {A2 : Expr h} -> ConvTy (addL H) (substExpr (lsh sigma) A) A2 ->
    HasType (addL H) u2 (substExpr (lsh sigma) A) ->
    ((l : LExpr) (v : FinEl) -> EvalRel (strip (lsub1 u l)) rho v ->
      (a : FinEl) -> EvalRel (strip (lsub1 A l)) rho a -> FinMem v a ->
      EqVal2 H (lsub1 (substExpr (lsh sigma) u) l) (lsub1 u2 l) (lsub1 (substExpr (lsh sigma) A) l) v a) ->
    (x : FinEl) -> EvalRel (strip (LLam A u)) rho x ->
    (a : FinEl) -> EvalRel (strip (LPi A)) rho a -> FinMem x a ->
    EqVal2 H (LLam (substExpr (lsh sigma) A) (substExpr (lsh sigma) u)) (LLam A2 u2) (LPi (substExpr (lsh sigma) A)) x a
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu Bot          evA fm = tt
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb Bot          hu (LPiCode f) evA fm = tt
  lamCore {A = A} {u = u} u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb (FunEl g0) hu (LPiCode f) evA fm =
    lamCore' {A = A} {u = u} u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb g0 hu f evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb (UCode _)    () (LPiCode f) evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb LevTy        () (LPiCode f) evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb (LevEl _)    () (LPiCode f) evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb (PiCode _ _) () (LPiCode f) evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb (LPiCode _)  () (LPiCode f) evA fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu (UCode _)    () fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu LevTy        () fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu (LevEl _)    () fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu (FunEl _)    () fm
  lamCore u2 d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH c2 ht2 IHb x            hu (PiCode _ _) () fm

------------------------------------------------------------------------
-- The three abstraction statements
------------------------------------------------------------------------

Adq-LLam : {g : Nat} {G : Ctx g} {A u : Expr g} ->
  WfCtx G -> IsType (addL G) A -> HasType (addL G) u A ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) -> ((l : LExpr) -> Adq G (lsub1 u l) (lsub1 A l)) ->
  LvTy G A -> LvTm G u A ->
  Adq G (LLam A u) (LPi A)
Adq-LLam {A = A} {u = u} d0 d1 d2 IHA IHu IHlvA IHlvU sigma rho crho vs fits wt wfH x hu a evA fm =
  Val2-from-EqVal2-first x a
    (lamCore {A = A} {u = u} (substExpr (lsh sigma) u) d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH
       (conv-Ty-refl (subst-IsType (WtSub-addL wt) (wkL-WfCtx wfH) d1))
       (subst-HasType (WtSub-addL wt) (wkL-WfCtx wfH) d2)
       (\ l v ev b evb fmb -> Val2-to-EqVal2 v b
          (Val2-tr2 (subst-lsub1 sigma u l) (subst-lsub1 sigma A l)
             (IHu l sigma rho crho vs fits wt wfH v ev b evb fmb)))
       x hu a evA fm)

AdqConv-LLam : {g : Nat} {G : Ctx g} {A u : Expr g} ->
  WfCtx G -> IsType (addL G) A -> HasType (addL G) u A ->
  ((l : LExpr) -> AdqConvTy G (lsub1 A l)) -> ((l : LExpr) -> AdqConv G (lsub1 u l) (lsub1 A l)) ->
  LvTy G A -> LvTm G u A ->
  AdqConv G (LLam A u) (LPi A)
AdqConv-LLam {G = G} {A = A} {u = u} d0 d1 d2 IHA IHu IHlvA IHlvU
    sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH x hu a evA fm =
  lamCore {A = A} {u = u} (substExpr (lsh sigma') u) d1 d2
    (\ l -> AdqConvTy-to-AdqTy {G = G} {A = lsub1 A l} (IHA l)) IHlvA IHlvU
    sigma rho crho vs fits wt wfH
    (subst-cong-IsType (ConvTmSub-addL wcs) wfL d1)
    (ty-conv (subst-HasType (WtSub-addL wt') wfL d2)
             (conv-Ty-sym (subst-cong-IsType (ConvTmSub-addL wcs) wfL d1)))
    (\ l v ev b evb fmb ->
       EqVal2-tr3 (subst-lsub1 sigma u l) (subst-lsub1 sigma' u l) (subst-lsub1 sigma A l)
         (IHu l sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH v ev b evb fmb))
    x hu a evA fm
  where wfL = wkL-WfCtx wfH

-- (the annotation may change along: <α>u = <α>u' at [α]A for A = A')
AdqE1-LLam : {g : Nat} {G : Ctx g} {A A' u u' : Expr g} ->
  WfCtx G -> IsType (addL G) A -> ConvTy (addL G) A A' -> HasType (addL G) u A -> ConvTm (addL G) u u' A ->
  ((l : LExpr) -> AdqTy G (lsub1 A l)) -> ((l : LExpr) -> AdqE1 G (lsub1 u l) (lsub1 u' l) (lsub1 A l)) ->
  LvTy G A -> LvTm G u A ->
  AdqE1 G (LLam A u) (LLam A' u') (LPi A)
AdqE1-LLam {A = A} {u = u} {u' = u'} d0 d1 cAA' d2 c12 IHA IHe IHlvA IHlvU sigma rho crho vs fits wt wfH x hu a evA fm =
  lamCore {A = A} {u = u} (substExpr (lsh sigma) u') d1 d2 IHA IHlvA IHlvU sigma rho crho vs fits wt wfH
    (subst-ConvTy (WtSub-addL wt) (wkL-WfCtx wfH) cAA')
    (snd (typing-ConvTm (subst-ConvTm (WtSub-addL wt) (wkL-WfCtx wfH) c12)))
    (\ l v ev b evb fmb ->
       EqVal2-tr3 (subst-lsub1 sigma u l) (subst-lsub1 sigma u' l) (subst-lsub1 sigma A l)
         (IHe l sigma rho crho vs fits wt wfH v ev b evb fmb))
    x hu a evA fm
