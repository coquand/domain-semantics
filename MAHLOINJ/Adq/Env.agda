{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Env.agda
--
-- Environments of the fundamental lemma (related substitutions over an
-- approximation of the context), the relations "at every code", and
-- the generic helpers (universes, Nat, substitution instances).
------------------------------------------------------------------------

module MAHLOINJ.Adq.Env where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel using (LeCode ; FinMem ; Coherent ; NotBot ; LeCode-trans)
open import MAHLOINJ.Model.Selection using (Or ; left ; right)
open import MAHLOINJ.Model.Comb using (AtomS ; bot-or)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalFwd using (EvalRel-subst1-forward)
open import MAHLOINJ.Model.SemLam using (InvTypP ; TypedP)
open import MAHLOINJ.Model.SoundBase using (Fits ; Fits-coh ; Fits-ext)
open import MAHLOINJ.Model.Soundness using (sTm)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Presup using (pCv ; pTm ; pTE)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base

------------------------------------------------------------------------
-- environments
------------------------------------------------------------------------

record Env {h g : Num} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) (rho : EnvApprox g) : Set where
  constructor mkEnv
  field
    sr   : SR H G s s' rho
    fits : Fits G rho
    wH   : WfCtx H
    wG   : WfCtx G

  cs : CSub H G s s'
  cs = SR.cs sr

  crho : CoherentEnv rho
  crho = Fits-coh G rho fits

-- relations at every code
TyRelAt : {h g : Num} (H : Ctx h) (s s' : Sub h g) (rho : EnvApprox g) (A B : Expr g) -> Set
TyRelAt H s s' rho A B = (a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> RTy H (substExpr s A) (substExpr s' B) a

TmRelAt : {h g : Num} (H : Ctx h) (s s' : Sub h g) (rho : EnvApprox g) (M N A : Expr g) -> Set
TmRelAt H s s' rho M N A = (a u : FinEl) -> EvalRel A rho a -> FinMem a UCode -> EvalRel M rho u -> FinMem u a ->
  RTm H (substExpr s M) (substExpr s' N) (substExpr s A) u a

envL : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> Env H G s s rho
envL E = mkEnv (leftSR (Env.wH E) (Env.wG E) (Env.sr E)) (Env.fits E) (Env.wH E) (Env.wG E)

envSym : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> Env H G s' s rho
envSym E = mkEnv (symSR (Env.sr E)) (Env.fits E) (Env.wH E) (Env.wG E)

envR : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> Env H G s' s' rho
envR E = envL (envSym E)

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  -- extension by related terms at a point w of the domain
  envExt : (E : Env H G s s' rho) {A : Expr g} -> IsType G A ->
    TyRelAt H s s' rho A A ->
    {N N' : Expr h} -> ConvTm H N N' (substExpr s A) ->
    (w b : FinEl) -> EvalRel A rho b -> FinMem w b ->
    ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> FinMem w a -> RTm H N N' (substExpr s A) w a) ->
    Env H (extend G A) (consSub s N) (consSub s' N') (extendEnv rho w)
  envExt E {A} iA VA {N} {N'} cv w b eb wb RN =
    mkEnv (extSR (Env.sr E) qA VA (fst (pCv cv)) (ty-conv (snd (pCv cv)) qA) cv w RN)
          (Fits-ext G A rho w b (Env.fits E) wb eb) (Env.wH E) (wf-extend iA)
    where
      qA = fTy s s' (Env.cs E) (Env.wH E) iA

------------------------------------------------------------------------
-- substitution instances  B[N]  of a related family
------------------------------------------------------------------------

module _ {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} where

  substTy : (E : Env H G s s' rho) {A : Expr g} {B : Expr (suc g)} {N : Expr g} ->
    IsType G A -> TyRelAt H s s' rho A A ->
    ({N1 N2 : Expr h} {w : FinEl} -> Env H (extend G A) (consSub s N1) (consSub s' N2) (extendEnv rho w) ->
       TyRelAt H (consSub s N1) (consSub s' N2) (extendEnv rho w) B B) ->
    HasType G N A -> TmRelAt H s s' rho N N A ->
    TyRelAt H s s' rho (subst1 B N) (subst1 B N)
  substTy E {A} {B} {N} iA VA atB dN FN c ec cU =
    let fw = EvalRel-subst1-forward B N rho c (Env.crho E) ec
        x = dfst fw ; ex = dfst (dsnd fw) ; cx = dsnd (dsnd fw)
        t = sTm dN rho (Env.fits E) x ex
        y = dfst t ; a' = dfst (dsnd t) ; lxy = dfst (dsnd (dsnd t)) ; ey = dfst (dsnd (dsnd (dsnd t)))
        ya = dfst (dsnd (dsnd (dsnd (dsnd t)))) ; ea = dsnd (dsnd (dsnd (dsnd (dsnd t))))
        cohx = EvalRel-coh N rho (Env.crho E) x ex
        cohy = EvalRel-coh N rho (Env.crho E) y ey
        cy = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho y)
               (mkSigma (EnvLe-refl rho (Env.crho E)) (mkSigma cohx (mkSigma cohy lxy))) c cx
        cN = fst (fTm s s' (Env.cs E) (Env.wH E) dN)
        E' = envExt E iA VA cN y a' ea ya (\ a0 ea0 aU0 ya0 -> FN a0 y ea0 aU0 ey ya0)
    in transport2 (\ X Y -> RTy H X Y c) (substCons s B N) (substCons s' B N) (atB E' c cy cU)

------------------------------------------------------------------------
-- universes and Nat
------------------------------------------------------------------------

univR : {n : Num} {H : Ctx n} {u : Expr n} -> Univ u -> IsType H u -> UnivR H u
univR {u = u} un iu = u , (hrs-refl , (un , tyeq-refl iu))

uTy : {n : Num} {H : Ctx n} {T T' : Expr n} -> UnivR H T -> UnivR H T' -> (a : FinEl) -> AtomS UCode a -> RTy H T T' a
uTy q q' Bot e = tt
uTy q q' UCode e = q , q'
uTy q q' (FunEl _) (mkSigma _ ())
uTy q q' (PiCode _ _) (mkSigma _ ())
uTy q q' NatCode (mkSigma _ ())
uTy q q' ZeroEl (mkSigma _ ())
uTy q q' (SucEl _) (mkSigma _ ())
uTy q q' (PairEl _ _) (mkSigma _ ())
uTy q q' (SigmaCode _ _) (mkSigma _ ())

natTy : {n : Num} {H : Ctx n} -> IsType H Nat -> (a : FinEl) -> AtomS NatCode a -> RTy H Nat Nat a
natTy iN Bot e = tt
natTy iN NatCode e = (hrs-refl , tyeq-refl iN) , (hrs-refl , tyeq-refl iN)
natTy iN UCode (mkSigma _ ())
natTy iN (FunEl _) (mkSigma _ ())
natTy iN (PiCode _ _) (mkSigma _ ())
natTy iN ZeroEl (mkSigma _ ())
natTy iN (SucEl _) (mkSigma _ ())
natTy iN (PairEl _ _) (mkSigma _ ())
natTy iN (SigmaCode _ _) (mkSigma _ ())

reUniv : {n : Num} {H : Ctx n} {M M' T T' : Expr n} -> UnivR H T' -> (u : FinEl) ->
  RTm H M M' T u UCode -> RTm H M M' T' u UCode
reUniv {H = H} {M} {M'} {T} {T'} q u r = go (bot-or u)
  where
    go : Or (Eq u Bot) (NotBot u) -> RTm H M M' T' u UCode
    go (left refl) = tt
    go (right nb) = elM u q (snd (elV u nb r))

-- the type relation carried by an element of a universe
elTyR : {n : Num} {H : Ctx n} {M M' T : Expr n} (u : FinEl) -> RTm H M M' T u UCode -> RTy H M M' u
elTyR {H = H} {M} {M'} {T} u r = go (bot-or u)
  where
    go : Or (Eq u Bot) (NotBot u) -> RTy H M M' u
    go (left refl) = tt
    go (right nb) = snd (elV u nb r)

------------------------------------------------------------------------
-- induction hypotheses: relations under every environment
------------------------------------------------------------------------

TyIH : {h g : Num} (H : Ctx h) (G : Ctx g) (A B : Expr g) -> Set
TyIH {h} {g} H G A B = {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> TyRelAt H s s' rho A B

TmIH : {h g : Num} (H : Ctx h) (G : Ctx g) (M N A : Expr g) -> Set
TmIH {h} {g} H G M N A = {s s' : Sub h g} {rho : EnvApprox g} -> Env H G s s' rho -> TmRelAt H s s' rho M N A
