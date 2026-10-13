{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/EvalSubst.agda
--
-- Semantic renaming and substitution for EvalRel:
--   EvalRel-ren / -ren-inv, EvalRel-wk / -unwk,
--   EvalRel-subst (backward, SubRel),
--   EvalRel-subst-fwd-max (forward under a bounding environment).
------------------------------------------------------------------------

module MAHLOINJ.Model.EvalSubst where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.Eval
open import MAHLO.Syntax
  using ( Num ; Fin ; fzero ; fsuc ; Expr
        ; Var ; Lam ; App ; Pi ; Fst ; Snd ; Nat ; Zero ; Suc ; Rec
        ; V ; Ucode ; Fhat ; Ghat
        ; Ren ; liftRen ; renExpr ; wkRen ; wkExpr
        ; Sub ; liftSub ; substExpr ; subst1Sub ; subst1 )
  renaming (zero to nzero ; suc to nsuc ; Sigma to SigmaE ; Pair to PairE)

------------------------------------------------------------------------
-- Generic transfer: a pointwise inclusion between the semantics of two
-- expressions built with the same head, from inclusions of the parts.
-- (Used for renaming in both directions and for both substitution
-- directions; the binder case is handled through liftings.)
------------------------------------------------------------------------

-- Renaming
RenAgree : {n m : Num} -> Ren n m -> EnvApprox n -> EnvApprox m -> Set
RenAgree {n} r rho rho' = (i : Fin n) -> Eq (lookupEnv (r i) rho') (lookupEnv i rho)

liftRen-agree : {n m : Num} (r : Ren n m) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (x : FinEl) -> RenAgree (liftRen r) (extendEnv rho x) (extendEnv rho' x)
liftRen-agree r rho rho' eq x fzero    = refl
liftRen-agree r rho rho' eq x (fsuc i) = eq i

EvalRel-ren : {n m : Num} (r : Ren n m) (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (u : FinEl) -> EvalRel M rho u -> EvalRel (renExpr r M) rho' u
EvalRel-ren-inv : {n m : Num} (r : Ren n m) (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (u : FinEl) -> EvalRel (renExpr r M) rho' u -> EvalRel M rho u

EvalRel-ren r (Var i) rho rho' eq u e = Eq-transport (\ z -> AtomS z u) (Eq-sym (eq i)) e
EvalRel-ren r (Lam A t) rho rho' eq =
  LamS-map _ _ _ _ (EvalRel-ren r A rho rho' eq)
    (\ x v cx e -> EvalRel-ren (liftRen r) t (extendEnv rho x) (extendEnv rho' x)
                     (liftRen-agree r rho rho' eq x) v e)
EvalRel-ren r (App t a) rho rho' eq = AppS-map _ _ _ _ (EvalRel-ren r t rho rho' eq) (EvalRel-ren r a rho rho' eq)
EvalRel-ren r (Pi A F) rho rho' eq = PiS-map _ _ _ _ (EvalRel-ren r A rho rho' eq) (EvalRel-ren r F rho rho' eq)
EvalRel-ren r (SigmaE A F) rho rho' eq = SigS-map _ _ _ _ (EvalRel-ren r A rho rho' eq) (EvalRel-ren r F rho rho' eq)
EvalRel-ren r (PairE t u) rho rho' eq = PairS-map _ _ _ _ (EvalRel-ren r t rho rho' eq) (EvalRel-ren r u rho rho' eq)
EvalRel-ren r (Fst t) rho rho' eq = FstS-map _ _ (EvalRel-ren r t rho rho' eq)
EvalRel-ren r (Snd t) rho rho' eq = SndS-map _ _ (EvalRel-ren r t rho rho' eq)
EvalRel-ren r Nat rho rho' eq u e = e
EvalRel-ren r Zero rho rho' eq u e = e
EvalRel-ren r (Suc t) rho rho' eq = SucS-map _ _ (EvalRel-ren r t rho rho' eq)
EvalRel-ren r (Rec C z s k) rho rho' eq =
  RecS-map _ _ _ _ _ _ (EvalRel-ren r z rho rho' eq) (EvalRel-ren r s rho rho' eq) (EvalRel-ren r k rho rho' eq)
EvalRel-ren r V rho rho' eq u e = e
EvalRel-ren r (Ucode f g) rho rho' eq u e = e
EvalRel-ren r (Fhat f g A F) rho rho' eq =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-ren r f rho rho' eq) (EvalRel-ren r A rho rho' eq))
    (EvalRel-ren r F rho rho' eq)
EvalRel-ren r (Ghat f g A F c) rho rho' eq =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-ren r g rho rho' eq)
    (EvalRel-ren r A rho rho' eq)) (EvalRel-ren r F rho rho' eq)) (EvalRel-ren r c rho rho' eq)

EvalRel-ren-inv r (Var i) rho rho' eq u e = Eq-transport (\ z -> AtomS z u) (eq i) e
EvalRel-ren-inv r (Lam A t) rho rho' eq =
  LamS-map _ _ _ _ (EvalRel-ren-inv r A rho rho' eq)
    (\ x v cx e -> EvalRel-ren-inv (liftRen r) t (extendEnv rho x) (extendEnv rho' x)
                     (liftRen-agree r rho rho' eq x) v e)
EvalRel-ren-inv r (App t a) rho rho' eq = AppS-map _ _ _ _ (EvalRel-ren-inv r t rho rho' eq) (EvalRel-ren-inv r a rho rho' eq)
EvalRel-ren-inv r (Pi A F) rho rho' eq = PiS-map _ _ _ _ (EvalRel-ren-inv r A rho rho' eq) (EvalRel-ren-inv r F rho rho' eq)
EvalRel-ren-inv r (SigmaE A F) rho rho' eq = SigS-map _ _ _ _ (EvalRel-ren-inv r A rho rho' eq) (EvalRel-ren-inv r F rho rho' eq)
EvalRel-ren-inv r (PairE t u) rho rho' eq = PairS-map _ _ _ _ (EvalRel-ren-inv r t rho rho' eq) (EvalRel-ren-inv r u rho rho' eq)
EvalRel-ren-inv r (Fst t) rho rho' eq = FstS-map _ _ (EvalRel-ren-inv r t rho rho' eq)
EvalRel-ren-inv r (Snd t) rho rho' eq = SndS-map _ _ (EvalRel-ren-inv r t rho rho' eq)
EvalRel-ren-inv r Nat rho rho' eq u e = e
EvalRel-ren-inv r Zero rho rho' eq u e = e
EvalRel-ren-inv r (Suc t) rho rho' eq = SucS-map _ _ (EvalRel-ren-inv r t rho rho' eq)
EvalRel-ren-inv r (Rec C z s k) rho rho' eq =
  RecS-map _ _ _ _ _ _ (EvalRel-ren-inv r z rho rho' eq) (EvalRel-ren-inv r s rho rho' eq) (EvalRel-ren-inv r k rho rho' eq)
EvalRel-ren-inv r V rho rho' eq u e = e
EvalRel-ren-inv r (Ucode f g) rho rho' eq u e = e
EvalRel-ren-inv r (Fhat f g A F) rho rho' eq =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-ren-inv r f rho rho' eq) (EvalRel-ren-inv r A rho rho' eq))
    (EvalRel-ren-inv r F rho rho' eq)
EvalRel-ren-inv r (Ghat f g A F c) rho rho' eq =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-ren-inv r g rho rho' eq)
    (EvalRel-ren-inv r A rho rho' eq)) (EvalRel-ren-inv r F rho rho' eq)) (EvalRel-ren-inv r c rho rho' eq)

EvalRel-wk : {n : Num} (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  EvalRel M rho u -> EvalRel (wkExpr M) (extendEnv rho v) u
EvalRel-wk M rho v u e = EvalRel-ren wkRen M rho (extendEnv rho v) (\ i -> refl) u e

EvalRel-unwk : {n : Num} (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  EvalRel (wkExpr M) (extendEnv rho v) u -> EvalRel M rho u
EvalRel-unwk M rho v u e = EvalRel-ren-inv wkRen M rho (extendEnv rho v) (\ i -> refl) u e

------------------------------------------------------------------------
-- Substitution, backward:  rho' i <= [sigma i]rho  ==>  [M]rho' <= [sigma M]rho
------------------------------------------------------------------------

SubRel : {h g : Num} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
SubRel {h} {g} sigma rho rho' = (i : Fin g) -> EvalRel (sigma i) rho (lookupEnv i rho')

SubRel-lift : {h g : Num} (sigma : Sub h g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  SubRel sigma rho rho' -> (x : FinEl) -> Coherent x ->
  SubRel (liftSub sigma) (extendEnv rho x) (extendEnv rho' x)
SubRel-lift sigma rho rho' sr x cx fzero    = mkSigma cx (LeCode-refl x cx)
SubRel-lift sigma rho rho' sr x cx (fsuc i) = EvalRel-wk (sigma i) rho x _ (sr i)

EvalRel-subst : {h g : Num} (sigma : Sub h g) (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho -> SubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel M rho' u -> EvalRel (substExpr sigma M) rho u
EvalRel-subst sigma (Var i) rho rho' c sr u e =
  EvalRel-down (sigma i) rho c (lookupEnv i rho') u (sr i) (fst e) (snd e)
EvalRel-subst sigma (Lam A t) rho rho' c sr =
  LamS-map _ _ _ _ (EvalRel-subst sigma A rho rho' c sr)
    (\ x v cx e -> EvalRel-subst (liftSub sigma) t (extendEnv rho x) (extendEnv rho' x)
                     (mkSigma c cx) (SubRel-lift sigma rho rho' sr x cx) v e)
EvalRel-subst sigma (App t a) rho rho' c sr =
  AppS-map _ _ _ _ (EvalRel-subst sigma t rho rho' c sr) (EvalRel-subst sigma a rho rho' c sr)
EvalRel-subst sigma (Pi A F) rho rho' c sr =
  PiS-map _ _ _ _ (EvalRel-subst sigma A rho rho' c sr) (EvalRel-subst sigma F rho rho' c sr)
EvalRel-subst sigma (SigmaE A F) rho rho' c sr =
  SigS-map _ _ _ _ (EvalRel-subst sigma A rho rho' c sr) (EvalRel-subst sigma F rho rho' c sr)
EvalRel-subst sigma (PairE t u) rho rho' c sr =
  PairS-map _ _ _ _ (EvalRel-subst sigma t rho rho' c sr) (EvalRel-subst sigma u rho rho' c sr)
EvalRel-subst sigma (Fst t) rho rho' c sr = FstS-map _ _ (EvalRel-subst sigma t rho rho' c sr)
EvalRel-subst sigma (Snd t) rho rho' c sr = SndS-map _ _ (EvalRel-subst sigma t rho rho' c sr)
EvalRel-subst sigma Nat rho rho' c sr u e = e
EvalRel-subst sigma Zero rho rho' c sr u e = e
EvalRel-subst sigma (Suc t) rho rho' c sr = SucS-map _ _ (EvalRel-subst sigma t rho rho' c sr)
EvalRel-subst sigma (Rec C z s k) rho rho' c sr =
  RecS-map _ _ _ _ _ _ (EvalRel-subst sigma z rho rho' c sr) (EvalRel-subst sigma s rho rho' c sr)
    (EvalRel-subst sigma k rho rho' c sr)
EvalRel-subst sigma V rho rho' c sr u e = e
EvalRel-subst sigma (Ucode f g) rho rho' c sr u e = e
EvalRel-subst sigma (Fhat f g A F) rho rho' c sr =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-subst sigma f rho rho' c sr) (EvalRel-subst sigma A rho rho' c sr))
    (EvalRel-subst sigma F rho rho' c sr)
EvalRel-subst sigma (Ghat f g A F c') rho rho' c sr =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-subst sigma g rho rho' c sr)
    (EvalRel-subst sigma A rho rho' c sr)) (EvalRel-subst sigma F rho rho' c sr))
    (EvalRel-subst sigma c' rho rho' c sr)

SubRel-subst1 : {n : Num} (M : Expr n) (rho : EnvApprox n) (v : FinEl) ->
  CoherentEnv rho -> EvalRel M rho v -> SubRel (subst1Sub M) rho (extendEnv rho v)
SubRel-subst1 M rho v c e fzero    = e
SubRel-subst1 M rho v c e (fsuc i) =
  mkSigma (lookupEnv-coh i rho c) (LeCode-refl (lookupEnv i rho) (lookupEnv-coh i rho c))

EvalRel-subst1-backward : {n : Num} (B : Expr (nsuc n)) (M : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  CoherentEnv rho -> EvalRel M rho v -> EvalRel B (extendEnv rho v) u -> EvalRel (subst1 B M) rho u
EvalRel-subst1-backward B M rho v u c eM eB =
  EvalRel-subst (subst1Sub M) B rho (extendEnv rho v) c (SubRel-subst1 M rho v c eM) u eB

------------------------------------------------------------------------
-- Substitution, forward under a bound:  [sigma i]rho <= rho' i
------------------------------------------------------------------------

MaxSubRel : {h g : Num} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
MaxSubRel {h} {g} sigma rho rho' =
  (i : Fin g) (u : FinEl) -> EvalRel (sigma i) rho u -> LeCode u (lookupEnv i rho')

MaxSubRel-lift : {h g : Num} (sigma : Sub h g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  MaxSubRel sigma rho rho' -> (x : FinEl) ->
  MaxSubRel (liftSub sigma) (extendEnv rho x) (extendEnv rho' x)
MaxSubRel-lift sigma rho rho' m x fzero    u e = snd e
MaxSubRel-lift sigma rho rho' m x (fsuc i) u e = m i u (EvalRel-unwk (sigma i) rho x u e)

EvalRel-subst-fwd-max : {h g : Num} (sigma : Sub h g) (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho -> MaxSubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel (substExpr sigma M) rho u -> EvalRel M rho' u
EvalRel-subst-fwd-max sigma (Var i) rho rho' c m u e =
  mkSigma (EvalRel-coh (sigma i) rho c u e) (m i u e)
EvalRel-subst-fwd-max sigma (Lam A t) rho rho' c m =
  LamS-map _ _ _ _ (EvalRel-subst-fwd-max sigma A rho rho' c m)
    (\ x v cx e -> EvalRel-subst-fwd-max (liftSub sigma) t (extendEnv rho x) (extendEnv rho' x)
                     (mkSigma c cx) (MaxSubRel-lift sigma rho rho' m x) v e)
EvalRel-subst-fwd-max sigma (App t a) rho rho' c m =
  AppS-map _ _ _ _ (EvalRel-subst-fwd-max sigma t rho rho' c m) (EvalRel-subst-fwd-max sigma a rho rho' c m)
EvalRel-subst-fwd-max sigma (Pi A F) rho rho' c m =
  PiS-map _ _ _ _ (EvalRel-subst-fwd-max sigma A rho rho' c m) (EvalRel-subst-fwd-max sigma F rho rho' c m)
EvalRel-subst-fwd-max sigma (SigmaE A F) rho rho' c m =
  SigS-map _ _ _ _ (EvalRel-subst-fwd-max sigma A rho rho' c m) (EvalRel-subst-fwd-max sigma F rho rho' c m)
EvalRel-subst-fwd-max sigma (PairE t u) rho rho' c m =
  PairS-map _ _ _ _ (EvalRel-subst-fwd-max sigma t rho rho' c m) (EvalRel-subst-fwd-max sigma u rho rho' c m)
EvalRel-subst-fwd-max sigma (Fst t) rho rho' c m = FstS-map _ _ (EvalRel-subst-fwd-max sigma t rho rho' c m)
EvalRel-subst-fwd-max sigma (Snd t) rho rho' c m = SndS-map _ _ (EvalRel-subst-fwd-max sigma t rho rho' c m)
EvalRel-subst-fwd-max sigma Nat rho rho' c m u e = e
EvalRel-subst-fwd-max sigma Zero rho rho' c m u e = e
EvalRel-subst-fwd-max sigma (Suc t) rho rho' c m = SucS-map _ _ (EvalRel-subst-fwd-max sigma t rho rho' c m)
EvalRel-subst-fwd-max sigma (Rec C z s k) rho rho' c m =
  RecS-map _ _ _ _ _ _ (EvalRel-subst-fwd-max sigma z rho rho' c m) (EvalRel-subst-fwd-max sigma s rho rho' c m)
    (EvalRel-subst-fwd-max sigma k rho rho' c m)
EvalRel-subst-fwd-max sigma V rho rho' c m u e = e
EvalRel-subst-fwd-max sigma (Ucode f g) rho rho' c m u e = e
EvalRel-subst-fwd-max sigma (Fhat f g A F) rho rho' c m =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-subst-fwd-max sigma f rho rho' c m)
    (EvalRel-subst-fwd-max sigma A rho rho' c m)) (EvalRel-subst-fwd-max sigma F rho rho' c m)
EvalRel-subst-fwd-max sigma (Ghat f g A F c') rho rho' c m =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-subst-fwd-max sigma g rho rho' c m)
    (EvalRel-subst-fwd-max sigma A rho rho' c m)) (EvalRel-subst-fwd-max sigma F rho rho' c m))
    (EvalRel-subst-fwd-max sigma c' rho rho' c m)

MaxSubRel-subst1 : {n : Num} (a : Expr n) (rho : EnvApprox n) (v : FinEl) ->
  ((u : FinEl) -> EvalRel a rho u -> LeCode u v) ->
  MaxSubRel (subst1Sub a) rho (extendEnv rho v)
MaxSubRel-subst1 a rho v bound fzero    u e = bound u e
MaxSubRel-subst1 a rho v bound (fsuc i) u e = snd e

EvalRel-subst1-fwd-bounded : {n : Num} (M : Expr (nsuc n)) (a : Expr n) (rho : EnvApprox n) (v u : FinEl) ->
  CoherentEnv rho -> ((u' : FinEl) -> EvalRel a rho u' -> LeCode u' v) ->
  EvalRel (subst1 M a) rho u -> EvalRel M (extendEnv rho v) u
EvalRel-subst1-fwd-bounded M a rho v u c bound e =
  EvalRel-subst-fwd-max (subst1Sub a) M rho (extendEnv rho v) c (MaxSubRel-subst1 a rho v bound) u e
