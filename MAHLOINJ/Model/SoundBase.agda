{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SoundBase.agda
--
-- Environments fitting a context, and syntax-level wrappers around the
-- generic semantic typing lemmas (application, Pi/Sigma formation,
-- lambda, Fhat/Ghat chains, rec).
------------------------------------------------------------------------

module MAHLOINJ.Model.SoundBase where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst
open import MAHLOINJ.Model.EvalFwd
open import MAHLOINJ.Model.SemLam
open import MAHLOINJ.Model.SemCode
open import MAHLOINJ.Model.SemConv
open import MAHLOINJ.Model.SemSig
open import MAHLOINJ.Model.SemRec
open import MAHLO.Syntax
  using ( Num ; Fin ; fzero ; fsuc ; Expr
        ; Var ; Lam ; App ; Pi ; Fst ; Snd ; Nat ; Zero ; Suc ; Rec
        ; V ; Ucode ; Fhat ; Ghat
        ; wkExpr ; subst1 ; substExpr ; sucSub ; subst1Sub ; liftSub
        ; PiB ; SigmaB ; Arr ; x0 ; x1 ; OpF ; OpG ; RecStep )
  renaming (zero to nzero ; suc to nsuc ; Sigma to SigmaE ; Pair to PairE)
open import MAHLO.Typing using (Ctx ; empty ; extend ; lookup ; Univ ; univ-V ; univ-U)

------------------------------------------------------------------------
-- Fits
------------------------------------------------------------------------

Fits : {n : Num} -> Ctx n -> EnvApprox n -> Set
Fits empty emptyEnv = Top
Fits (extend G A) (extendEnv rho u) =
  Pair (Fits G rho) (Sigma FinEl (\ a -> Pair (FinMem u a) (EvalRel A rho a)))

Fits-coh : {n : Num} (G : Ctx n) (rho : EnvApprox n) -> Fits G rho -> CoherentEnv rho
Fits-coh empty emptyEnv f = tt
Fits-coh (extend G A) (extendEnv rho u) f =
  mkSigma (Fits-coh G rho (fst f)) (FinMem-coh-u u (fst (snd f)) (fst (snd (snd f))))

Fits-ext : {n : Num} (G : Ctx n) (A : Expr n) (rho : EnvApprox n) (x a : FinEl) ->
  Fits G rho -> FinMem x a -> EvalRel A rho a -> Fits (extend G A) (extendEnv rho x)
Fits-ext G A rho x a f m e = mkSigma f (mkSigma a (mkSigma m e))

Fits-var : {n : Num} (G : Ctx n) (rho : EnvApprox n) -> Fits G rho -> (i : Fin n) ->
  Sigma FinEl (\ a -> Pair (FinMem (lookupEnv i rho) a) (EvalRel (lookup G i) rho a))
Fits-var (extend G A) (extendEnv rho v) f fzero =
  mkSigma (fst (snd f)) (mkSigma (fst (snd (snd f))) (EvalRel-wk A rho v _ (snd (snd (snd f)))))
Fits-var (extend G A) (extendEnv rho v) f (fsuc i) =
  let r = Fits-var G rho (fst f) i
  in mkSigma (fst r) (mkSigma (fst (snd r)) (EvalRel-wk (lookup G i) rho v _ (snd (snd r))))

------------------------------------------------------------------------
-- generic body families
------------------------------------------------------------------------

Body : {n : Num} -> Expr (nsuc n) -> EnvApprox n -> FinEl -> Pred
Body B rho x = EvalRel B (extendEnv rho x)

bodyOK : {n : Num} (B : Expr (nsuc n)) (rho : EnvApprox n) -> CoherentEnv rho -> BodyOK (Body B rho)
bodyOK B rho c = record
  { ideal = \ x cx -> EvalRel-ideal B (extendEnv rho x) (mkSigma c cx)
  ; mon = \ x x' v cx cx' le e ->
      EvalRel-mon-env B (extendEnv rho x) (extendEnv rho x') (mkSigma (EnvLe-refl rho c) (mkSigma cx (mkSigma cx' le))) v e }

iR : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho -> Ideal (EvalRel M rho)
iR = EvalRel-ideal

-- universes all denote UCode
univ-in : {n : Num} {u : Expr n} -> Univ u -> (rho : EnvApprox n) -> (v : FinEl) -> AtomS UCode v -> EvalRel u rho v
univ-in (univ-V refl) rho v e = e
univ-in (univ-U f g refl) rho v e = e

univ-out : {n : Num} {u : Expr n} -> Univ u -> (rho : EnvApprox n) -> (v : FinEl) -> EvalRel u rho v -> AtomS UCode v
univ-out (univ-V refl) rho v e = e
univ-out (univ-U f g refl) rho v e = e

univ-wk-out : {n : Num} {u : Expr n} -> Univ u -> (rho : EnvApprox n) (x : FinEl) -> (v : FinEl) ->
  EvalRel (wkExpr u) (extendEnv rho x) v -> AtomS UCode v
univ-wk-out (univ-V refl) rho x v e = e
univ-wk-out (univ-U f g refl) rho x v e = e

------------------------------------------------------------------------
-- syntax-level typing lemmas
------------------------------------------------------------------------

InvConvP : Pred -> Pred -> Pred -> Set
InvConvP P Q T = Pair (InvTypP P T) (Pair (InvTypP Q T) (Pair (Incl P Q) (Incl Q P)))

app-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (M N : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel M rho) (EvalRel (PiB A B) rho) ->
  InvTypP (EvalRel (App M N) rho) (EvalRel (subst1 B N) rho)
app-T A B M N rho c inv =
  AppTyping.App-typed (EvalRel M rho) (EvalRel N rho) (EvalRel A rho) (Body B rho) (EvalRel (subst1 B N) rho)
    (iR M rho c) (iR N rho c) (bodyOK B rho c) inv
    (\ w v ew eb -> EvalRel-subst1-backward B N rho w v c ew eb)
    (EvalRel-Bot (subst1 B N) rho c)

lam-T : {n : Num} (A : Expr n) (B t : Expr (nsuc n)) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body t rho x) (Body B rho x)) ->
  InvTypP (EvalRel (Lam A t) rho) (EvalRel (PiB A B) rho)
lam-T A B t rho c ih =
  LamTyping.Typing.Lam-typed (EvalRel A rho) (iR A rho c) (Body t rho) (Body B rho)
    (bodyOK t rho c) (bodyOK B rho c) ih

pi-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel A rho) (AtomS UCode) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body B rho x) (AtomS UCode)) ->
  InvTypP (EvalRel (PiB A B) rho) (AtomS UCode)
pi-T A B rho c invA ih = CodeTyping.Pi-typed (EvalRel A rho) (iR A rho c) (Body B rho) (bodyOK B rho c) invA ih

sig-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel A rho) (AtomS UCode) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body B rho x) (AtomS UCode)) ->
  InvTypP (EvalRel (SigmaB A B) rho) (AtomS UCode)
sig-T A B rho c invA ih = CodeTyping.Sig-typed (EvalRel A rho) (iR A rho c) (Body B rho) (bodyOK B rho c) invA ih

-- fhat / ghat : iterated application of a typed operator
fhat-T : {n : Num} (f g A F : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel f rho) (EvalRel OpF rho) ->
  InvTypP (EvalRel (Fhat f g A F) rho) (EvalRel V rho)
fhat-T f g A F rho c invf =
  app-T (substExpr (subst1Sub A) (Arr x0 V)) V (App f A) F rho c (app-T V (Arr (Arr x0 V) V) f A rho c invf)

ghat-T : {n : Num} (f g A F c' : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel g rho) (EvalRel (OpG f) rho) ->
  InvTypP (EvalRel (Ghat f g A F c') rho) (EvalRel V rho)
ghat-T f g A F c' rho c invg =
  app-T (substExpr (subst1Sub F) (substExpr (liftSub (subst1Sub A)) (App (App (wkExpr (wkExpr f)) x1) x0))) V
    (App (App g A) F) c' rho c
    (app-T (substExpr (subst1Sub A) (Arr x0 V))
           (substExpr (liftSub (subst1Sub A)) (Arr (App (App (wkExpr (wkExpr f)) x1) x0) V))
           (App g A) F rho c
      (app-T V (PiB (Arr x0 V) (Arr (App (App (wkExpr (wkExpr f)) x1) x0) V)) g A rho c invg))

rec-T : {n : Num} (C : Expr (nsuc n)) (z s k : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel z rho) (EvalRel (subst1 C Zero) rho) ->
  InvTypP (EvalRel s rho) (EvalRel (RecStep C) rho) ->
  InvTypP (EvalRel (Rec (Lam Nat C) z s k) rho) (EvalRel (subst1 C k) rho)
rec-T C z s k rho c invZ invS =
  RecTyping.Rec-typed (EvalRel z rho) (EvalRel s rho) (EvalRel k rho) (EvalRel (subst1 C Zero) rho)
    (EvalRel (subst1 C k) rho) (Body C rho) (Body C rho) D
    (iR z rho c) (iR s rho c) (iR k rho c) (bodyOK C rho c)
    (bodyOK (Arr C C') rho c) (\ x cx -> bodyOK (wkExpr C') (extendEnv rho x) (mkSigma c cx))
    invZ fromZ invS fromD
    (\ w g ek eg -> EvalRel-subst1-backward C k rho w g c ek eg) (EvalRel-Bot (subst1 C k) rho c)
  where
    C' = substExpr sucSub C
    D : FinEl -> FinEl -> Pred
    D x = Body (wkExpr C') (extendEnv rho x)
    fromZ : (g : FinEl) -> EvalRel (subst1 C Zero) rho g -> Body C rho ZeroEl g
    fromZ g e =
      let fw = EvalRel-subst1-forward C Zero rho g c e
          v = fst fw ; ev = fst (snd fw)
      in EvalRel-mon-env C (extendEnv rho v) (extendEnv rho ZeroEl)
           (mkSigma (EnvLe-refl rho c) (mkSigma (fst ev) (mkSigma tt (snd ev)))) g (snd (snd fw))
    msr : (x : FinEl) -> Coherent x -> MaxSubRel sucSub (extendEnv rho x) (extendEnv rho (SucEl x))
    msr x cx fzero u e =
      LeCode-trans u (SucEl (fst (snd e))) (SucEl x) (fst e) (fst (fst (snd (snd e)))) cx
        (snd (snd (snd e))) (snd (fst (snd (snd e))))
    msr x cx (fsuc i) u e = snd e
    fromD : (x y v : FinEl) -> Coherent x -> D x y v -> Body C rho (SucEl x) v
    fromD x y v cx e =
      EvalRel-subst-fwd-max sucSub C (extendEnv rho x) (extendEnv rho (SucEl x)) (mkSigma c cx) (msr x cx) v
        (EvalRel-unwk C' (extendEnv rho x) y v e)

pair-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (t u : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel t rho) (EvalRel A rho) -> InvTypP (EvalRel u rho) (EvalRel (subst1 B t) rho) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body B rho x) (AtomS UCode)) ->
  InvTypP (EvalRel (PairE t u) rho) (EvalRel (SigmaB A B) rho)
pair-T A B t u rho c invT invU ihB =
  PairTyping.Pair-typed (EvalRel A rho) (EvalRel t rho) (EvalRel u rho) (EvalRel (subst1 B t) rho) (Body B rho)
    (iR A rho c) (iR t rho c) (iR u rho c) (bodyOK B rho c) invT invU
    (\ b e -> EvalRel-subst1-forward B t rho b c e) ihB

fst-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (t : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel t rho) (EvalRel (SigmaB A B) rho) -> InvTypP (EvalRel (Fst t) rho) (EvalRel A rho)
fst-T A B t rho c invT =
  ProjTyping.Fst-typed (EvalRel A rho) (EvalRel t rho) (Body B rho) (iR A rho c) (iR t rho c) (bodyOK B rho c) invT

snd-T : {n : Num} (A : Expr n) (B : Expr (nsuc n)) (t : Expr n) (rho : EnvApprox n) (c : CoherentEnv rho) ->
  InvTypP (EvalRel t rho) (EvalRel (SigmaB A B) rho) -> InvTypP (EvalRel (Snd t) rho) (EvalRel (subst1 B (Fst t)) rho)
snd-T A B t rho c invT =
  ProjTyping.SndT.Snd-typed (EvalRel A rho) (EvalRel t rho) (Body B rho) (iR A rho c) (iR t rho c) (bodyOK B rho c) invT
    (EvalRel (subst1 B (Fst t)) rho) (\ a1 b ef eb -> EvalRel-subst1-backward B (Fst t) rho a1 b c ef eb)
    (EvalRel-Bot (subst1 B (Fst t)) rho c)

-- inclusion of Pi/Sigma/Lam semantics from inclusions of the parts
lam-incl : {n : Num} (A A' : Expr n) (B B' : Expr (nsuc n)) (rho : EnvApprox n) ->
  Incl (EvalRel A rho) (EvalRel A' rho) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> Incl (Body B rho x) (Body B' rho x)) ->
  Incl (EvalRel (Lam A B) rho) (EvalRel (Lam A' B') rho)
lam-incl A A' B B' rho ha hb = LamS-map2 _ _ _ _ ha (\ x a v m ea e -> hb x a m ea v e)

pi-incl : {n : Num} (A A' : Expr n) (B B' : Expr (nsuc n)) (rho : EnvApprox n) ->
  Incl (EvalRel A rho) (EvalRel A' rho) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> Incl (Body B rho x) (Body B' rho x)) ->
  Incl (EvalRel (PiB A B) rho) (EvalRel (PiB A' B') rho)
pi-incl A A' B B' rho ha hb = PiS-map _ _ _ _ ha (lam-incl A A' B B' rho ha hb)

sig-incl : {n : Num} (A A' : Expr n) (B B' : Expr (nsuc n)) (rho : EnvApprox n) ->
  Incl (EvalRel A rho) (EvalRel A' rho) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a -> Incl (Body B rho x) (Body B' rho x)) ->
  Incl (EvalRel (SigmaB A B) rho) (EvalRel (SigmaB A' B') rho)
sig-incl A A' B B' rho ha hb = SigS-map _ _ _ _ ha (lam-incl A A' B B' rho ha hb)

conv-from : (P Q T : Pred) -> InvTypP P T -> Incl P Q -> Incl Q P -> InvConvP P Q T
conv-from P Q T inv pq qp = mkSigma inv (mkSigma (InvTyp-transfer P Q T pq qp inv) (mkSigma pq qp))
