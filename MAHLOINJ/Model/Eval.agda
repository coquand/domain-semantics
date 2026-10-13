{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/Eval.agda
--
-- Relational semantics of the (frozen) MAHLO syntax in the finite-
-- element domain, assembled from the combinators of Model/Comb:
--   EvalRel M rho u  :  "u is a finite approximant of [M]rho".
--
-- Universes are ERASED: V and U(f,g) both denote the code UCode;
-- fhat(f,g,A,F) and ghat(f,g,A,F,c) denote f A F and g A F c
-- (definitionally the same predicate as the corresponding App terms).
------------------------------------------------------------------------

module MAHLOINJ.Model.Eval where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Comb
open import MAHLO.Syntax
  using ( Num ; Fin ; fzero ; fsuc ; Expr
        ; Var ; Lam ; App ; Pi ; Fst ; Snd ; Nat ; Zero ; Suc ; Rec
        ; V ; Ucode ; Fhat ; Ghat )
  renaming (zero to nzero ; suc to nsuc ; Sigma to SigmaE ; Pair to PairE)

------------------------------------------------------------------------
-- Finite environments
------------------------------------------------------------------------

data EnvApprox : Num -> Set where
  emptyEnv  : EnvApprox nzero
  extendEnv : {n : Num} -> EnvApprox n -> FinEl -> EnvApprox (nsuc n)

lookupEnv : {n : Num} -> Fin n -> EnvApprox n -> FinEl
lookupEnv fzero    (extendEnv rho v) = v
lookupEnv (fsuc i) (extendEnv rho v) = lookupEnv i rho

CoherentEnv : {n : Num} -> EnvApprox n -> Set
CoherentEnv emptyEnv          = Top
CoherentEnv (extendEnv rho u) = Pair (CoherentEnv rho) (Coherent u)

lookupEnv-coh : {n : Num} (i : Fin n) (rho : EnvApprox n) ->
  CoherentEnv rho -> Coherent (lookupEnv i rho)
lookupEnv-coh fzero    (extendEnv rho u) crho = snd crho
lookupEnv-coh (fsuc i) (extendEnv rho u) crho = lookupEnv-coh i rho (fst crho)

EnvLe : {n : Num} -> EnvApprox n -> EnvApprox n -> Set
EnvLe emptyEnv emptyEnv = Top
EnvLe (extendEnv rho u) (extendEnv rho' u') =
  Pair (EnvLe rho rho') (Pair (Coherent u) (Pair (Coherent u') (LeCode u u')))

lookupEnv-mon : {n : Num} (i : Fin n) (rho rho' : EnvApprox n) -> EnvLe rho rho' ->
  Pair (Coherent (lookupEnv i rho))
    (Pair (Coherent (lookupEnv i rho')) (LeCode (lookupEnv i rho) (lookupEnv i rho')))
lookupEnv-mon fzero    (extendEnv rho u) (extendEnv rho' u') le = snd le
lookupEnv-mon (fsuc i) (extendEnv rho u) (extendEnv rho' u') le = lookupEnv-mon i rho rho' (fst le)

EnvLe-refl : {n : Num} (rho : EnvApprox n) -> CoherentEnv rho -> EnvLe rho rho
EnvLe-refl emptyEnv          c = tt
EnvLe-refl (extendEnv rho u) c =
  mkSigma (EnvLe-refl rho (fst c)) (mkSigma (snd c) (mkSigma (snd c) (LeCode-refl u (snd c))))

EnvLe-extend : {n : Num} (rho rho' : EnvApprox n) (x : FinEl) ->
  EnvLe rho rho' -> Coherent x -> EnvLe (extendEnv rho x) (extendEnv rho' x)
EnvLe-extend rho rho' x le cx = mkSigma le (mkSigma cx (mkSigma cx (LeCode-refl x cx)))

EnvLe-coh-r : {n : Num} (rho rho' : EnvApprox n) -> EnvLe rho rho' -> CoherentEnv rho'
EnvLe-coh-r emptyEnv emptyEnv le = tt
EnvLe-coh-r (extendEnv rho u) (extendEnv rho' u') le =
  mkSigma (EnvLe-coh-r rho rho' (fst le)) (fst (snd (snd le)))

------------------------------------------------------------------------
-- The relational semantics
------------------------------------------------------------------------

EvalRel : {n : Num} -> Expr n -> EnvApprox n -> Pred
EvalRel (Var i)          rho = AtomS (lookupEnv i rho)
EvalRel (Lam A t)        rho = LamS (EvalRel A rho) (\ x -> EvalRel t (extendEnv rho x))
EvalRel (App t a)        rho = AppS (EvalRel t rho) (EvalRel a rho)
EvalRel (Pi A F)         rho = PiS (EvalRel A rho) (EvalRel F rho)
EvalRel (SigmaE A F)     rho = SigS (EvalRel A rho) (EvalRel F rho)
EvalRel (PairE t u)      rho = PairS (EvalRel t rho) (EvalRel u rho)
EvalRel (Fst t)          rho = FstS (EvalRel t rho)
EvalRel (Snd t)          rho = SndS (EvalRel t rho)
EvalRel Nat              rho = AtomS NatCode
EvalRel Zero             rho = AtomS ZeroEl
EvalRel (Suc t)          rho = SucS (EvalRel t rho)
EvalRel (Rec C z s k)    rho = RecS (EvalRel z rho) (EvalRel s rho) (EvalRel k rho)
EvalRel V                rho = AtomS UCode
EvalRel (Ucode f g)      rho = AtomS UCode
EvalRel (Fhat f g A F)   rho = AppS (AppS (EvalRel f rho) (EvalRel A rho)) (EvalRel F rho)
EvalRel (Ghat f g A F c) rho =
  AppS (AppS (AppS (EvalRel g rho) (EvalRel A rho)) (EvalRel F rho)) (EvalRel c rho)

------------------------------------------------------------------------
-- Monotonicity in the environment
------------------------------------------------------------------------

EvalRel-mon-env : {n : Num} (M : Expr n) (rho rho' : EnvApprox n) ->
  EnvLe rho rho' -> (u : FinEl) -> EvalRel M rho u -> EvalRel M rho' u
EvalRel-mon-env (Var i) rho rho' le u e =
  let m = lookupEnv-mon i rho rho' le
  in mkSigma (fst e) (LeCode-trans u (lookupEnv i rho) (lookupEnv i rho')
                        (fst e) (fst m) (fst (snd m)) (snd e) (snd (snd m)))
EvalRel-mon-env (Lam A t) rho rho' le =
  LamS-map (EvalRel A rho) (EvalRel A rho') (\ x -> EvalRel t (extendEnv rho x))
    (\ x -> EvalRel t (extendEnv rho' x)) (EvalRel-mon-env A rho rho' le)
    (\ x v cx e -> EvalRel-mon-env t (extendEnv rho x) (extendEnv rho' x)
                     (EnvLe-extend rho rho' x le cx) v e)
EvalRel-mon-env (App t a) rho rho' le =
  AppS-map _ _ _ _ (EvalRel-mon-env t rho rho' le) (EvalRel-mon-env a rho rho' le)
EvalRel-mon-env (Pi A F) rho rho' le =
  PiS-map _ _ _ _ (EvalRel-mon-env A rho rho' le) (EvalRel-mon-env F rho rho' le)
EvalRel-mon-env (SigmaE A F) rho rho' le =
  SigS-map _ _ _ _ (EvalRel-mon-env A rho rho' le) (EvalRel-mon-env F rho rho' le)
EvalRel-mon-env (PairE t u) rho rho' le =
  PairS-map _ _ _ _ (EvalRel-mon-env t rho rho' le) (EvalRel-mon-env u rho rho' le)
EvalRel-mon-env (Fst t) rho rho' le = FstS-map _ _ (EvalRel-mon-env t rho rho' le)
EvalRel-mon-env (Snd t) rho rho' le = SndS-map _ _ (EvalRel-mon-env t rho rho' le)
EvalRel-mon-env Nat rho rho' le u e = e
EvalRel-mon-env Zero rho rho' le u e = e
EvalRel-mon-env (Suc t) rho rho' le = SucS-map _ _ (EvalRel-mon-env t rho rho' le)
EvalRel-mon-env (Rec C z s k) rho rho' le =
  RecS-map _ _ _ _ _ _ (EvalRel-mon-env z rho rho' le) (EvalRel-mon-env s rho rho' le)
    (EvalRel-mon-env k rho rho' le)
EvalRel-mon-env V rho rho' le u e = e
EvalRel-mon-env (Ucode f g) rho rho' le u e = e
EvalRel-mon-env (Fhat f g A F) rho rho' le =
  AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-mon-env f rho rho' le) (EvalRel-mon-env A rho rho' le))
    (EvalRel-mon-env F rho rho' le)
EvalRel-mon-env (Ghat f g A F c) rho rho' le =
  AppS-map _ _ _ _
    (AppS-map _ _ _ _ (AppS-map _ _ _ _ (EvalRel-mon-env g rho rho' le) (EvalRel-mon-env A rho rho' le))
       (EvalRel-mon-env F rho rho' le))
    (EvalRel-mon-env c rho rho' le)

------------------------------------------------------------------------
-- Every EvalRel M rho (rho coherent) is an ideal
------------------------------------------------------------------------

EvalRel-ideal : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho -> Ideal (EvalRel M rho)
EvalRel-ideal (Var i) rho c = AtomS-ideal (lookupEnv i rho) (lookupEnv-coh i rho c)
EvalRel-ideal (Lam A t) rho c =
  LamProps.ideal-Lam (EvalRel A rho) (\ x -> EvalRel t (extendEnv rho x))
    (EvalRel-ideal A rho c)
    (record { ideal = \ x cx -> EvalRel-ideal t (extendEnv rho x) (mkSigma c cx)
            ; mon = \ x x' v cx cx' le e ->
                EvalRel-mon-env t (extendEnv rho x) (extendEnv rho x')
                  (mkSigma (EnvLe-refl rho c) (mkSigma cx (mkSigma cx' le))) v e })
EvalRel-ideal (App t a) rho c = AppS-ideal _ _ (EvalRel-ideal t rho c) (EvalRel-ideal a rho c)
EvalRel-ideal (Pi A F) rho c = CodeProps.ideal-Pi _ _ (EvalRel-ideal A rho c) (EvalRel-ideal F rho c)
EvalRel-ideal (SigmaE A F) rho c = CodeProps.ideal-Sig _ _ (EvalRel-ideal A rho c) (EvalRel-ideal F rho c)
EvalRel-ideal (PairE t u) rho c = PairS-ideal _ _ (EvalRel-ideal t rho c) (EvalRel-ideal u rho c)
EvalRel-ideal (Fst t) rho c = FstS-ideal _ (EvalRel-ideal t rho c)
EvalRel-ideal (Snd t) rho c = SndS-ideal _ (EvalRel-ideal t rho c)
EvalRel-ideal Nat rho c = AtomS-ideal NatCode tt
EvalRel-ideal Zero rho c = AtomS-ideal ZeroEl tt
EvalRel-ideal (Suc t) rho c = SucS-ideal _ (EvalRel-ideal t rho c)
EvalRel-ideal (Rec C z s k) rho c =
  RecProps.ideal-Rec _ _ (EvalRel-ideal z rho c) (EvalRel-ideal s rho c) _ (EvalRel-ideal k rho c)
EvalRel-ideal V rho c = AtomS-ideal UCode tt
EvalRel-ideal (Ucode f g) rho c = AtomS-ideal UCode tt
EvalRel-ideal (Fhat f g A F) rho c =
  AppS-ideal _ _ (AppS-ideal _ _ (EvalRel-ideal f rho c) (EvalRel-ideal A rho c)) (EvalRel-ideal F rho c)
EvalRel-ideal (Ghat f g A F c') rho c =
  AppS-ideal _ _
    (AppS-ideal _ _ (AppS-ideal _ _ (EvalRel-ideal g rho c) (EvalRel-ideal A rho c)) (EvalRel-ideal F rho c))
    (EvalRel-ideal c' rho c)

------------------------------------------------------------------------
-- Named projections (the NAT-style API)
------------------------------------------------------------------------

EvalRel-coh : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  (u : FinEl) -> EvalRel M rho u -> Coherent u
EvalRel-coh M rho c = Ideal.coh (EvalRel-ideal M rho c)

EvalRel-Bot : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho -> EvalRel M rho Bot
EvalRel-Bot M rho c = Ideal.bot (EvalRel-ideal M rho c)

EvalRel-down : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  (u u' : FinEl) -> EvalRel M rho u -> Coherent u' -> LeCode u' u -> EvalRel M rho u'
EvalRel-down M rho c = Ideal.down (EvalRel-ideal M rho c)

EvalRel-Comp : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> Comp u v
EvalRel-Comp M rho c = Ideal.comp (EvalRel-ideal M rho c)

EvalRel-Sup : {n : Num} (M : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)
EvalRel-Sup M rho c = Ideal.sup (EvalRel-ideal M rho c)
