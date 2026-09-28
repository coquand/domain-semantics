{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Stmt
--
-- The adequacy statements for T_R (the shapes of the induction
-- hypotheses of the fundamental theorem), and the converters between
-- the term-at-a-universe form and the type form.
--
--   Adq     G M A    HasType G M A,   one substitution:  Val2
--   AdqConv G M A    HasType G M A,   two substitutions: EqVal2
--   AdqE1   G M N A  ConvTm G M N A,  one substitution:  EqVal2
--   AdqTy     G A    IsType G A,      one substitution:  ValTy2
--   AdqConvTy G A    IsType G A,      two substitutions: EqValTy2
--   AdqETy    G A B  ConvTy G A B,    one substitution:  EqValTy2
--
-- Terms are evaluated through `strip` (BCDE4.Model.Strip).
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Stmt (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; mkSigma ; fst ; snd ; Pair ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; U0 ; EqL ; EqL-refl ; EqL-sym ;
              LevTy ; LevEl ; LPiCode)
open import BCDE4.Dom.Kernel using (FinMem)
open import BCDE4.Dom.Membership using (finMem-U-lvl)
open import BCDE4.Model.Eval D using (EnvApprox ; EvalRel ; CoherentEnv ; lcodeT)
open import BCDE4.Model.SoundnessLemmas D using (Fits ; Typed)
open import BCDE4.Model.RussellSound D using (sound-Tm ; sound-CTy ; sound-CTm)
open import BCDE4.Model.Strip using (strip ; stripCtx)
open import BCDE4.RussellSyntax using (Expr ; U ; Sub ; substExpr)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (WtSub ; isType-U)
open import BCDE4.RussellReduction using (headred-refl)

open import BCDE4.Levels using (LCtx ; LSub ; lidS ; LExpr ; lsubL ; lsubL-id ; LDec)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

Adq : {g : Nat} (G : Ctx g) (M A : Expr g) -> Set
Adq {g} G M A =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (strip M) rho u ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
  Val2 H (substExpr sigma M) (substExpr sigma A) u a

AdqConv : {g : Nat} (G : Ctx g) (M A : Expr g) -> Set
AdqConv {g} G M A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (u : FinEl) -> EvalRel (strip M) rho u ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a

AdqE1 : {g : Nat} (G : Ctx g) (M N A : Expr g) -> Set
AdqE1 {g} G M N A =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (u : FinEl) -> EvalRel (strip M) rho u ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
  EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

AdqTy : {g : Nat} (G : Ctx g) (A : Expr g) -> Set
AdqTy {g} G A =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem a U0 ->
  ValTy2 H (substExpr sigma A) a

AdqConvTy : {g : Nat} (G : Ctx g) (A : Expr g) -> Set
AdqConvTy {g} G A =
  {h : Nat} {H : Ctx h} (sigma sigma' : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
  ValidConvSub2 H G sigma sigma' rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WtSub H G sigma' -> WtConvSub H G sigma sigma' -> WfCtx H ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem a U0 ->
  EqValTy2 H (substExpr sigma A) (substExpr sigma' A) a

AdqETy : {g : Nat} (G : Ctx g) (A B : Expr g) -> Set
AdqETy {g} G A B =
  {h : Nat} {H : Ctx h} (sigma : Sub h g) (rho : EnvApprox (lctx H) lidS g) ->
  CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits (stripCtx G) rho ->
  WtSub H G sigma -> WfCtx H ->
  (a : FinEl) -> EvalRel (strip A) rho a -> FinMem a U0 ->
  EqValTy2 H (substExpr sigma A) (substExpr sigma B) a

------------------------------------------------------------------------
-- Universes
------------------------------------------------------------------------

-- the code of U_l in the target, as the evaluation computes it
cU : {h : Nat} (H : Ctx h) (l : LExpr) -> Nat
cU H l = lcodeT (lctx H) (lsubL lidS l)

evU : {n : Nat} (rho : EnvApprox TL θ n) (l : LExpr) ->
  EvalRel (strip {n} (U l)) rho (UCode (lcodeT TL (lsubL θ l)))
evU {TL = TL} {θ = θ} rho l = mkSigma tt (EqL-refl (lcodeT TL (lsubL θ l)))

-- U_l is a universe of its own code
valTyU : {h : Nat} {H : Ctx h} (l : LExpr) {k : Nat} -> WfCtx H -> EqL (cU H l) k -> ValTy2 H (U l) (UCode k)
valTyU {H = H} l {k} wfH e =
  mkRValU l (mkRed3 headred-refl (conv-Ty-refl (isType-U wfH)))
    (S.Eq-transport (\ x -> EqL (LDec.lcode (D (lctx H)) x) k) (lsubL-id l) e)

------------------------------------------------------------------------
-- Term at a universe  <->  type  (in the model a value of a universe is
-- the same as a value of a type: the universe's code plays no role)
------------------------------------------------------------------------

Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M A : Expr n} {l : Nat}
  (u : FinEl) -> FinMem u U0 -> Val2 G M A u (UCode l) -> ValTy2 G M u
Val2-U-to-ValTy2 Bot          _ _ = tt
Val2-U-to-ValTy2 (UCode _)    _ v = snd v
Val2-U-to-ValTy2 (PiCode _ _) _ v = snd v
Val2-U-to-ValTy2 (FunEl _)    () _
Val2-U-to-ValTy2 LevTy        _ _ = tt
Val2-U-to-ValTy2 (LevEl _)    () _
Val2-U-to-ValTy2 (LPiCode _)  _ v = snd v

EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N A : Expr n} {l : Nat}
  (u : FinEl) -> FinMem u U0 -> EqVal2 G M N A u (UCode l) -> EqValTy2 G M N u
EqVal2-U-to-EqValTy2 Bot          _ _  = tt
EqVal2-U-to-EqValTy2 (UCode _)    _ ev = snd (snd (snd ev))
EqVal2-U-to-EqValTy2 (PiCode _ _) _ ev = snd (snd (snd ev))
EqVal2-U-to-EqValTy2 (FunEl _)    () _
EqVal2-U-to-EqValTy2 LevTy        _ _  = tt
EqVal2-U-to-EqValTy2 (LevEl _)    () _
EqVal2-U-to-EqValTy2 (LPiCode _)  _ ev = snd (snd (snd ev))

EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N A : Expr n} {l : Nat}
  (u : FinEl) -> FinMem u U0 -> EqVal2 G M N A u (UCode l) -> ValTy2 G M u
EqVal2-U-to-ValTy2-fst Bot          _ _  = tt
EqVal2-U-to-ValTy2-fst (UCode _)    _ ev = fst (snd ev)
EqVal2-U-to-ValTy2-fst (PiCode _ _) _ ev = fst (snd ev)
EqVal2-U-to-ValTy2-fst (FunEl _)    () _
EqVal2-U-to-ValTy2-fst LevTy        _ _  = tt
EqVal2-U-to-ValTy2-fst (LevEl _)    () _
EqVal2-U-to-ValTy2-fst (LPiCode _)  _ ev = fst (snd ev)

EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N A : Expr n} {l : Nat}
  (u : FinEl) -> FinMem u U0 -> EqVal2 G M N A u (UCode l) -> ValTy2 G N u
EqVal2-U-to-ValTy2-snd Bot          _ _  = tt
EqVal2-U-to-ValTy2-snd (UCode _)    _ ev = fst (snd (snd ev))
EqVal2-U-to-ValTy2-snd (PiCode _ _) _ ev = fst (snd (snd ev))
EqVal2-U-to-ValTy2-snd (FunEl _)    () _
EqVal2-U-to-ValTy2-snd LevTy        _ _  = tt
EqVal2-U-to-ValTy2-snd (LevEl _)    () _
EqVal2-U-to-ValTy2-snd (LPiCode _)  _ ev = fst (snd (snd ev))

-- The converse directions, at U_l with the code of l.
ValTy2-to-Val2-U : {n : Nat} {G : Ctx n} {M : Expr n} (l : LExpr) {k : Nat} -> WfCtx G -> EqL (cU G l) k ->
  (u : FinEl) -> ValTy2 G M u -> Val2 G M (U l) u (UCode k)
ValTy2-to-Val2-U l wfG e Bot          vt = tt
ValTy2-to-Val2-U l wfG e (UCode _)    vt = mkSigma (valTyU l wfG e) vt
ValTy2-to-Val2-U l wfG e (PiCode _ _) vt = mkSigma (valTyU l wfG e) vt
ValTy2-to-Val2-U l wfG e (FunEl _)    vt = tt
ValTy2-to-Val2-U l wfG e LevTy        vt = tt
ValTy2-to-Val2-U l wfG e (LevEl _)    vt = tt
ValTy2-to-Val2-U l wfG e (LPiCode _)  vt = mkSigma (valTyU l wfG e) vt

EqValTy2-to-EqVal2-U : {n : Nat} {G : Ctx n} {M N : Expr n} (l : LExpr) {k : Nat} -> WfCtx G -> EqL (cU G l) k ->
  (u : FinEl) -> EqValTy2 G M N u -> EqVal2 G M N (U l) u (UCode k)
EqValTy2-to-EqVal2-U l wfG e Bot          ev = tt
EqValTy2-to-EqVal2-U l wfG e (UCode _)    ev =
  mkSigma (valTyU l wfG e) (mkSigma (fst ev) (mkSigma (snd ev) ev))
EqValTy2-to-EqVal2-U l wfG e (PiCode _ _) ev =
  mkSigma (valTyU l wfG e) (mkSigma (fst ev) (mkSigma (fst (snd ev)) ev))
EqValTy2-to-EqVal2-U l wfG e (FunEl _)    ev = tt
EqValTy2-to-EqVal2-U l wfG e LevTy        ev = tt
EqValTy2-to-EqVal2-U l wfG e (LevEl _)    ev = tt
EqValTy2-to-EqVal2-U l wfG e (LPiCode _)  ev =
  mkSigma (valTyU l wfG e) (mkSigma (fst ev) (mkSigma (fst (snd ev)) ev))

------------------------------------------------------------------------
-- From the universe forms of the statements to the type forms
------------------------------------------------------------------------

Adq-U-to-AdqTy : {g : Nat} {G : Ctx g} {A : Expr g} {l : LExpr} ->
  Adq G A (U l) -> AdqTy G A
Adq-U-to-AdqTy {l = l} IH {H = H} sigma rho crho vs fits wt wfH a evA aU =
  Val2-U-to-ValTy2 a aU (IH sigma rho crho vs fits wt wfH a evA _ (evU rho l) (finMem-U-lvl a 0 (cU H l) aU))

AdqConv-U-to-AdqConvTy : {g : Nat} {G : Ctx g} {A : Expr g} {l : LExpr} ->
  AdqConv G A (U l) -> AdqConvTy G A
AdqConv-U-to-AdqConvTy {l = l} IH {H = H} sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a evA aU =
  EqVal2-U-to-EqValTy2 a aU
    (IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a evA _ (evU rho l) (finMem-U-lvl a 0 (cU H l) aU))

AdqE1-U-to-AdqETy : {g : Nat} {G : Ctx g} {A B : Expr g} {l : LExpr} ->
  AdqE1 G A B (U l) -> AdqETy G A B
AdqE1-U-to-AdqETy {l = l} IH {H = H} sigma rho crho vs fits wt wfH a evA aU =
  EqVal2-U-to-EqValTy2 a aU (IH sigma rho crho vs fits wt wfH a evA _ (evU rho l) (finMem-U-lvl a 0 (cU H l) aU))

-- Diagonal: the one-substitution statement from the two-substitution one.
AdqConvTy-to-AdqTy : {g : Nat} {G : Ctx g} {A : Expr g} -> AdqConvTy G A -> AdqTy G A
AdqConvTy-to-AdqTy {G = G} IH sigma rho crho vs fits wt wfH a evA aU =
  EqValTy2-fst a
    (IH sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs) fits
       wt wt (WtConvSub-refl {G = G} wt) wfH a evA aU)
  where
    EqValTy2-fst : {h : Nat} {H : Ctx h} {M N : Expr h} (a : FinEl) -> EqValTy2 H M N a -> ValTy2 H M a
    EqValTy2-fst Bot          e = tt
    EqValTy2-fst (UCode _)    e = fst e
    EqValTy2-fst (FunEl _)    e = tt
    EqValTy2-fst (PiCode _ _) e = fst e
    EqValTy2-fst LevTy        e = tt
    EqValTy2-fst (LevEl _)    e = tt
    EqValTy2-fst (LPiCode _)  e = fst e

Conv-to-diag : {g : Nat} {G : Ctx g} {M A : Expr g} -> AdqConv G M A -> Adq G M A
Conv-to-diag {G = G} IH sigma rho crho vs fits wt wfH u hu a evA fm =
  Val2-from-EqVal2-first u a
    (IH sigma sigma rho crho vs vs (ValidConvSub2-refl {G = G} vs) fits
       wt wt (WtConvSub-refl {G = G} wt) wfH u hu a evA fm)

------------------------------------------------------------------------
-- From the type forms of the statements to the universe forms: in the
-- model a type is valid as a term of every universe (the universe's own
-- code is only constrained through its level, the one of U_l).
------------------------------------------------------------------------

AdqTy-to-Adq-U : {g : Nat} {G : Ctx g} {T : Expr g} {l : LExpr} -> AdqTy G T -> Adq G T (U l)
AdqTy-to-Adq-U IH sigma rho crho vs fits wt wfH u hu Bot          evA fm = tt
AdqTy-to-Adq-U IH sigma rho crho vs fits wt wfH u hu (FunEl _)    () fm
AdqTy-to-Adq-U IH sigma rho crho vs fits wt wfH u hu (PiCode _ _) () fm
AdqTy-to-Adq-U {l = l} IH {H = H} sigma rho crho vs fits wt wfH u hu (UCode k) evA fm =
  ValTy2-to-Val2-U l wfH (EqL-sym k (cU H l) (snd evA)) u
    (IH sigma rho crho vs fits wt wfH u hu (finMem-U-lvl u k 0 fm))

AdqConvTy-to-AdqConv-U : {g : Nat} {G : Ctx g} {T : Expr g} {l : LExpr} -> AdqConvTy G T -> AdqConv G T (U l)
AdqConvTy-to-AdqConv-U IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu Bot          evA fm = tt
AdqConvTy-to-AdqConv-U IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu (FunEl _)    () fm
AdqConvTy-to-AdqConv-U IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu (PiCode _ _) () fm
AdqConvTy-to-AdqConv-U {l = l} IH {H = H} sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu (UCode k) evA fm =
  EqValTy2-to-EqVal2-U l wfH (EqL-sym k (cU H l) (snd evA)) u
    (IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu (finMem-U-lvl u k 0 fm))

AdqETy-to-AdqE1-U : {g : Nat} {G : Ctx g} {T T' : Expr g} {l : LExpr} -> AdqETy G T T' -> AdqE1 G T T' (U l)
AdqETy-to-AdqE1-U IH sigma rho crho vs fits wt wfH u hu Bot          evA fm = tt
AdqETy-to-AdqE1-U IH sigma rho crho vs fits wt wfH u hu (FunEl _)    () fm
AdqETy-to-AdqE1-U IH sigma rho crho vs fits wt wfH u hu (PiCode _ _) () fm
AdqETy-to-AdqE1-U {l = l} IH {H = H} sigma rho crho vs fits wt wfH u hu (UCode k) evA fm =
  EqValTy2-to-EqVal2-U l wfH (EqL-sym k (cU H l) (snd evA)) u
    (IH sigma rho crho vs fits wt wfH u hu (finMem-U-lvl u k 0 fm))

------------------------------------------------------------------------
-- Soundness of the model, in the form used by the adequacy proof:
-- evaluation transfers along conversions, and typed terms have a
-- typed value (BCDE4.Model.RussellSound).
------------------------------------------------------------------------

evFwd-Tm : {n : Nat} {G : Ctx n} {M N A : Expr n} -> ConvTm G M N A ->
  (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho ->
  (u : FinEl) -> EvalRel (strip M) rho u -> EvalRel (strip N) rho u
evFwd-Tm d rho fits = fst (snd (snd (sound-CTm d rho fits)))

evBwd-Tm : {n : Nat} {G : Ctx n} {M N A : Expr n} -> ConvTm G M N A ->
  (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho ->
  (u : FinEl) -> EvalRel (strip N) rho u -> EvalRel (strip M) rho u
evBwd-Tm d rho fits = snd (snd (snd (sound-CTm d rho fits)))

evFwd-Ty : {n : Nat} {G : Ctx n} {A B : Expr n} -> ConvTy G A B ->
  (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho ->
  (u : FinEl) -> EvalRel (strip A) rho u -> EvalRel (strip B) rho u
evFwd-Ty d rho fits = fst (snd (snd (sound-CTy d rho fits)))

evBwd-Ty : {n : Nat} {G : Ctx n} {A B : Expr n} -> ConvTy G A B ->
  (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho ->
  (u : FinEl) -> EvalRel (strip B) rho u -> EvalRel (strip A) rho u
evBwd-Ty d rho fits = snd (snd (snd (sound-CTy d rho fits)))

-- theorem1: a value of a typed term lies below a value that is a member
-- of a value of its type.
typedVal : {n : Nat} {G : Ctx n} {M A : Expr n} -> HasType G M A ->
  (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho ->
  (u : FinEl) -> EvalRel (strip M) rho u -> Typed (strip M) (strip A) rho u
typedVal d rho fits = sound-Tm d rho fits

------------------------------------------------------------------------
-- Annotations equal to the record's own
------------------------------------------------------------------------

Ann-refl : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
  IsType G A -> IsType (extend G A) B -> Ann G A B A B
Ann-refl dA dB = mkAnn (conv-Ty-refl dA) (conv-Ty-refl dB)

------------------------------------------------------------------------
-- The left end of a type conversion is a valid type.
------------------------------------------------------------------------

EqValTy2-fst : {h : Nat} {H : Ctx h} {M N : Expr h} (a : FinEl) -> EqValTy2 H M N a -> ValTy2 H M a
EqValTy2-fst Bot          e = tt
EqValTy2-fst (UCode _)    e = fst e
EqValTy2-fst (FunEl _)    e = tt
EqValTy2-fst (PiCode _ _) e = fst e
EqValTy2-fst LevTy        e = tt
EqValTy2-fst (LevEl _)    e = tt
EqValTy2-fst (LPiCode _)  e = fst e

AdqETy-to-AdqTy : {g : Nat} {G : Ctx g} {A B : Expr g} -> AdqETy G A B -> AdqTy G A
AdqETy-to-AdqTy IH sigma rho crho vs fits wt wfH a evA aU =
  EqValTy2-fst a (IH sigma rho crho vs fits wt wfH a evA aU)
