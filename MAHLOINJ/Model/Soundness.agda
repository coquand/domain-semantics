{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/Soundness.agda
--
-- Soundness of the (frozen) Mahlo typing in the erased finite-element
-- model:  for every environment fitting the context,
--   IsType G A     ->  every approximant of A is below an element of U
--   HasType G t A  ->  every approximant of t is below an element of a
--                      type below A                        (InvTyp)
--   TyEq / ConvTm  ->  both sides typed, and equal denotations (InvConv)
------------------------------------------------------------------------

module MAHLOINJ.Model.Soundness where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst
open import MAHLOINJ.Model.EvalFwd
open import MAHLOINJ.Model.SemLam
open import MAHLOINJ.Model.SemConv
open import MAHLOINJ.Model.SemSig
open import MAHLOINJ.Model.SemRec
open import MAHLOINJ.Model.SoundBase
open import MAHLO.Syntax
  using ( Num ; Fin ; fzero ; fsuc ; Expr
        ; Var ; Lam ; App ; Pi ; Fst ; Snd ; Nat ; Zero ; Suc ; Rec
        ; V ; Ucode ; Fhat ; Ghat
        ; wkExpr ; subst1 ; substExpr ; sucSub ; subst1Sub ; liftSub
        ; PiB ; SigmaB ; Arr ; x0 ; x1 ; OpF ; OpG ; RecStep )
  renaming (zero to nzero ; suc to nsuc ; Sigma to SigmaE ; Pair to PairE)
open import MAHLO.Typing

------------------------------------------------------------------------

UT : Pred
UT = AtomS UCode

sTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A ->
  (rho : EnvApprox n) -> Fits G rho -> InvTypP (EvalRel A rho) UT
sTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A ->
  (rho : EnvApprox n) -> Fits G rho -> InvTypP (EvalRel t rho) (EvalRel A rho)
sTE : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B ->
  (rho : EnvApprox n) -> Fits G rho -> InvConvP (EvalRel A rho) (EvalRel B rho) UT
sCv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
  (rho : EnvApprox n) -> Fits G rho -> InvConvP (EvalRel t rho) (EvalRel u rho) (EvalRel A rho)

-- bodies in an extended context
bodyTy : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (nsuc n)} -> IsType (extend G A) B ->
  (rho : EnvApprox n) -> Fits G rho ->
  (x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body B rho x) UT
bodyTy {G = G} {A} dB rho f x a m e = sTy dB (extendEnv rho x) (Fits-ext G A rho x a f m e)

bodyTm : {n : Num} {G : Ctx n} {A : Expr n} {t B : Expr (nsuc n)} -> HasType (extend G A) t B ->
  (rho : EnvApprox n) -> Fits G rho ->
  (x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body t rho x) (Body B rho x)
bodyTm {G = G} {A} dt rho f x a m e = sTm dt (extendEnv rho x) (Fits-ext G A rho x a f m e)

-- a term in a universe, as a type
sTmU : {n : Num} {G : Ctx n} {t u : Expr n} -> Univ u -> HasType G t u ->
  (rho : EnvApprox n) -> Fits G rho -> InvTypP (EvalRel t rho) UT
sTmU un d rho f = InvTypP-map _ _ _ _ (\ u e -> e) (\ u e -> e) (univ-out un rho) (sTm d rho f)

bodyTmU : {n : Num} {G : Ctx n} {A u : Expr n} {B : Expr (nsuc n)} -> Univ u -> HasType (extend G A) B (wkExpr u) ->
  (rho : EnvApprox n) -> Fits G rho ->
  (x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvTypP (Body B rho x) UT
bodyTmU {G = G} {A} un dB rho f x a m e =
  InvTypP-map _ _ _ _ (\ u e -> e) (\ u e -> e) (univ-wk-out un rho x)
    (sTm dB (extendEnv rho x) (Fits-ext G A rho x a f m e))

------------------------------------------------------------------------
-- IsType
------------------------------------------------------------------------

sTy (isty-V w) rho f = Atom-typed UCode UCode tt tt UT (mkSigma tt tt)
sTy (isty-el d) rho f = sTm d rho f
sTy (isty-Pi {A = A} {B} dA dB) rho f =
  pi-T A B rho (Fits-coh _ rho f) (sTy dA rho f) (bodyTy dB rho f)
sTy (isty-Sigma {A = A} {B} dA dB) rho f =
  sig-T A B rho (Fits-coh _ rho f) (sTy dA rho f) (bodyTy dB rho f)

------------------------------------------------------------------------
-- HasType
------------------------------------------------------------------------

sTm {G = G} (ty-var {i = i} w) rho f u e =
  let r = Fits-var G rho f i
  in mkSigma (lookupEnv i rho) (mkSigma (fst r) (mkSigma (snd e)
       (mkSigma (mkSigma (FinMem-coh-u (lookupEnv i rho) (fst r) (fst (snd r)))
                   (LeCode-refl (lookupEnv i rho) (FinMem-coh-u (lookupEnv i rho) (fst r) (fst (snd r)))))
         (mkSigma (fst (snd r)) (snd (snd r))))))
sTm (ty-conv d e) rho f = InvTypP-map _ _ _ _ (\ u x -> x) (\ u x -> x) (fst (snd (snd (sTE e rho f)))) (sTm d rho f)
sTm (ty-sub d) rho f = sTm d rho f
sTm (ty-Pi {u = u} {A} {B} un dA dB) rho f =
  InvTypP-map _ _ _ _ (\ v x -> x) (\ v x -> x) (univ-in un rho)
    (pi-T A B rho (Fits-coh _ rho f) (sTmU un dA rho f) (bodyTmU un dB rho f))
sTm (ty-Sigma {u = u} {A} {B} un dA dB) rho f =
  InvTypP-map _ _ _ _ (\ v x -> x) (\ v x -> x) (univ-in un rho)
    (sig-T A B rho (Fits-coh _ rho f) (sTmU un dA rho f) (bodyTmU un dB rho f))
sTm (ty-Nat-V w) rho f = Atom-typed NatCode UCode tt tt _ (mkSigma tt tt)
sTm (ty-Nat-U d) rho f = Atom-typed NatCode UCode tt tt _ (mkSigma tt tt)
sTm (ty-Ucode df dg) rho f = Atom-typed UCode UCode tt tt _ (mkSigma tt tt)
sTm (ty-Fhat {f = fe} {g} {A} {B} df dg dA dB) rho f =
  fhat-T fe g A (Lam A B) rho (Fits-coh _ rho f) (sTm df rho f)
sTm (ty-Ghat {f = fe} {g} {A} {c} {B} df dg dA dB dc) rho f =
  ghat-T fe g A (Lam A B) c rho (Fits-coh _ rho f) (sTm dg rho f)
sTm (ty-Lam {A = A} {B} {t} dA dB dt) rho f =
  lam-T A B t rho (Fits-coh _ rho f) (bodyTm dt rho f)
sTm (ty-App {A = A} {t} {a} {B} dA dB dt da) rho f =
  app-T A B t a rho (Fits-coh _ rho f) (sTm dt rho f)
sTm (ty-Pair {A = A} {t} {u} {B} dA dB dt du) rho f =
  pair-T A B t u rho (Fits-coh _ rho f) (sTm dt rho f) (sTm du rho f) (bodyTy dB rho f)
sTm (ty-Fst {A = A} {t} {B} dA dB dt) rho f = fst-T A B t rho (Fits-coh _ rho f) (sTm dt rho f)
sTm (ty-Snd {A = A} {t} {B} dA dB dt) rho f = snd-T A B t rho (Fits-coh _ rho f) (sTm dt rho f)
sTm (ty-Zero w) rho f = Atom-typed ZeroEl NatCode tt tt _ (mkSigma tt tt)
sTm (ty-Suc {t = t} d) rho f = Suc-typed (EvalRel t rho) (iR t rho (Fits-coh _ rho f)) (sTm d rho f)
sTm (ty-Rec {z = z} {s} {k} {C} dC dz ds dk) rho f =
  rec-T C z s k rho (Fits-coh _ rho f) (sTm dz rho f) (sTm ds rho f)

------------------------------------------------------------------------
-- TyEq
------------------------------------------------------------------------

sTE (tyeq-refl d) rho f = conv-from _ _ _ (sTy d rho f) (\ u x -> x) (\ u x -> x)
sTE (tyeq-sym e) rho f =
  let r = sTE e rho f in mkSigma (fst (snd r)) (mkSigma (fst r) (mkSigma (snd (snd (snd r))) (fst (snd (snd r)))))
sTE (tyeq-trans e1 e2) rho f =
  let r1 = sTE e1 rho f ; r2 = sTE e2 rho f
  in mkSigma (fst r1) (mkSigma (fst (snd r2))
       (mkSigma (\ u x -> fst (snd (snd r2)) u (fst (snd (snd r1)) u x))
                (\ u x -> snd (snd (snd r1)) u (snd (snd (snd r2)) u x))))
sTE (tyeq-el d) rho f = sCv d rho f
sTE {G = G} (tyeq-Pi {A = A} {A'} {B} {B'} dA dB dB' eA eB) rho f =
  let c = Fits-coh G rho f
      rA = sTE eA rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvConvP (Body B rho x) (Body B' rho x) UT
      ihB x a m e = sTE eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _ (pi-T A B rho c (sTy dA rho f) (bodyTy dB rho f))
       (pi-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e)))))
       (pi-incl A' A B' B rho (snd (snd (snd rA)))
          (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e))))))
sTE {G = G} (tyeq-Sigma {A = A} {A'} {B} {B'} dA dB dB' eA eB) rho f =
  let c = Fits-coh G rho f
      rA = sTE eA rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a -> InvConvP (Body B rho x) (Body B' rho x) UT
      ihB x a m e = sTE eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _ (sig-T A B rho c (sTy dA rho f) (bodyTy dB rho f))
       (sig-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e)))))
       (sig-incl A' A B' B rho (snd (snd (snd rA)))
          (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e))))))

------------------------------------------------------------------------
-- ConvTm
------------------------------------------------------------------------

sCv (conv-refl d) rho f = conv-from _ _ _ (sTm d rho f) (\ u x -> x) (\ u x -> x)
sCv (conv-sym e) rho f =
  let r = sCv e rho f in mkSigma (fst (snd r)) (mkSigma (fst r) (mkSigma (snd (snd (snd r))) (fst (snd (snd r)))))
sCv (conv-trans e1 e2) rho f =
  let r1 = sCv e1 rho f ; r2 = sCv e2 rho f
  in mkSigma (fst r1) (mkSigma (fst (snd r2))
       (mkSigma (\ u x -> fst (snd (snd r2)) u (fst (snd (snd r1)) u x))
                (\ u x -> snd (snd (snd r1)) u (snd (snd (snd r2)) u x))))
sCv (conv-conv e t) rho f =
  let r = sCv e rho f ; incl = fst (snd (snd (sTE t rho f)))
  in mkSigma (InvTypP-map _ _ _ _ (\ u x -> x) (\ u x -> x) incl (fst r))
       (mkSigma (InvTypP-map _ _ _ _ (\ u x -> x) (\ u x -> x) incl (fst (snd r))) (snd (snd r)))
sCv (conv-sub e) rho f = sCv e rho f
sCv (conv-R' dA dB e) rho f = sCv e rho f
sCv (conv-delta-f {f = fe} {g} {A} {B} df dg dA dB) rho f =
  conv-from _ _ _ (fhat-T fe g A (Lam A B) rho (Fits-coh _ rho f) (sTm df rho f)) (\ u x -> x) (\ u x -> x)
sCv (conv-delta-g {f = fe} {g} {A} {c} {B} df dg dA dB dc) rho f =
  conv-from _ _ _ (ghat-T fe g A (Lam A B) c rho (Fits-coh _ rho f) (sTm dg rho f)) (\ u x -> x) (\ u x -> x)
sCv {G = G} (conv-beta {A = A} {a} {B} {t} dA dB dt da) rho f =
  let c = Fits-coh G rho f
      okt = bodyOK t rho c
  in conv-from _ _ _ (app-T A B (Lam A t) a rho c (lam-T A B t rho c (bodyTm dt rho f)))
       (Beta.app-to-sub (EvalRel A rho) (EvalRel a rho) (EvalRel (subst1 t a) rho) (Body t rho)
          (iR A rho c) (iR a rho c) (iR (subst1 t a) rho c) okt
          (\ z u ez eb -> EvalRel-subst1-backward t a rho z u c ez eb)
          (\ u e -> EvalRel-subst1-forward t a rho u c e) (sTm da rho f))
       (Beta.sub-to-app (EvalRel A rho) (EvalRel a rho) (EvalRel (subst1 t a) rho) (Body t rho)
          (iR A rho c) (iR a rho c) (iR (subst1 t a) rho c) okt
          (\ z u ez eb -> EvalRel-subst1-backward t a rho z u c ez eb)
          (\ u e -> EvalRel-subst1-forward t a rho u c e) (sTm da rho f))
sCv {G = G} (conv-funext {A = A} {t} {t'} {B} dA dB dt dt' e) rho f =
  let c = Fits-coh G rho f
      pt : (M N : Expr _) ->
           ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
              Incl (EvalRel (App (wkExpr M) x0) (extendEnv rho x)) (EvalRel (App (wkExpr N) x0) (extendEnv rho x))) ->
           (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
           Incl (AppS (EvalRel M rho) (AtomS x)) (AppS (EvalRel N rho) (AtomS x))
      pt M N h x a m ea v ev =
        AppS-map _ _ _ _ (EvalRel-unwk N rho x) (\ w y -> y) v
          (h x a m ea v (AppS-map _ _ _ _ (EvalRel-wk M rho x) (\ w y -> y) v ev))
      ih : (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
           InvConvP (EvalRel (App (wkExpr t) x0) (extendEnv rho x)) (EvalRel (App (wkExpr t') x0) (extendEnv rho x))
                    (Body B rho x)
      ih x a m ea = sCv e (extendEnv rho x) (Fits-ext G A rho x a f m ea)
  in mkSigma (sTm dt rho f) (mkSigma (sTm dt' rho f)
       (mkSigma (Funext.incl (EvalRel A rho) (EvalRel t rho) (EvalRel t' rho) (Body B rho) (iR t rho c) (iR t' rho c)
                   (sTm dt rho f) (pt t t' (\ x a m ea -> fst (snd (snd (ih x a m ea))))))
                (Funext.incl (EvalRel A rho) (EvalRel t' rho) (EvalRel t rho) (Body B rho) (iR t' rho c) (iR t rho c)
                   (sTm dt' rho f) (pt t' t (\ x a m ea -> snd (snd (snd (ih x a m ea))))))))
sCv {G = G} (conv-fst-beta {A = A} {t} {u} {B} dA dB dt du) rho f =
  let c = Fits-coh G rho f
  in mkSigma (InvTyp-transfer _ _ _ (PairEq.fst-beta-2 _ _ (iR t rho c) (iR u rho c))
                (PairEq.fst-beta-1 _ _ (iR t rho c) (iR u rho c)) (sTm dt rho f))
       (mkSigma (sTm dt rho f) (mkSigma (PairEq.fst-beta-1 _ _ (iR t rho c) (iR u rho c))
                                        (PairEq.fst-beta-2 _ _ (iR t rho c) (iR u rho c))))
sCv {G = G} (conv-snd-beta {A = A} {t} {u} {B} dA dB dt du) rho f =
  let c = Fits-coh G rho f
  in mkSigma (InvTyp-transfer _ _ _ (PairEq.snd-beta-2 _ _ (iR t rho c) (iR u rho c))
                (PairEq.snd-beta-1 _ _ (iR t rho c) (iR u rho c)) (sTm du rho f))
       (mkSigma (sTm du rho f) (mkSigma (PairEq.snd-beta-1 _ _ (iR t rho c) (iR u rho c))
                                        (PairEq.snd-beta-2 _ _ (iR t rho c) (iR u rho c))))
sCv {G = G} (conv-pairext {A = A} {t} {t'} {B} dA dB dt dt' e1 e2) rho f =
  let c = Fits-coh G rho f
      r1 = sCv e1 rho f ; r2 = sCv e2 rho f
  in mkSigma (sTm dt rho f) (mkSigma (sTm dt' rho f)
       (mkSigma (PairExt.incl _ _ (EvalRel t rho) (EvalRel t' rho) (iR t rho c) (iR t' rho c) (sTm dt rho f)
                   (fst (snd (snd r1))) (fst (snd (snd r2))))
                (PairExt.incl _ _ (EvalRel t' rho) (EvalRel t rho) (iR t' rho c) (iR t rho c) (sTm dt' rho f)
                   (snd (snd (snd r1))) (snd (snd (snd r2))))))
sCv {G = G} (conv-rec-zero {z = z} {s} {C} dC dz ds) rho f =
  let c = Fits-coh G rho f
      i1 = RecIota.zero-1 _ _ _ (iR z rho c) (iR s rho c) (iR Zero rho c)
      i2 = RecIota.zero-2 _ _ _ (iR z rho c) (iR s rho c) (iR Zero rho c)
  in mkSigma (InvTyp-transfer _ _ _ i2 i1 (sTm dz rho f)) (mkSigma (sTm dz rho f) (mkSigma i1 i2))
sCv {G = G} (conv-rec-suc {z = z} {s} {k} {C} dC dz ds dk) rho f =
  let c = Fits-coh G rho f
      i1 = RecIota.suc-1 _ _ _ (iR z rho c) (iR s rho c) (iR k rho c)
      i2 = RecIota.suc-2 _ _ _ (iR z rho c) (iR s rho c) (iR k rho c)
  in conv-from _ _ _ (rec-T C z s (Suc k) rho c (sTm dz rho f) (sTm ds rho f)) i1 i2
sCv {G = G} (conv-App {A = A} {t} {t'} {a} {a'} {B} dA dB et ea) rho f =
  let c = Fits-coh G rho f ; rt = sCv et rho f ; ra = sCv ea rho f
  in conv-from _ _ _ (app-T A B t a rho c (fst rt))
       (AppS-map _ _ _ _ (fst (snd (snd rt))) (fst (snd (snd ra))))
       (AppS-map _ _ _ _ (snd (snd (snd rt))) (snd (snd (snd ra))))
sCv {G = G} (conv-Fst {A = A} {t} {t'} {B} dA dB et) rho f =
  let c = Fits-coh G rho f ; rt = sCv et rho f
  in conv-from _ _ _ (fst-T A B t rho c (fst rt))
       (FstS-map _ _ (fst (snd (snd rt)))) (FstS-map _ _ (snd (snd (snd rt))))
sCv {G = G} (conv-Snd {A = A} {t} {t'} {B} dA dB et) rho f =
  let c = Fits-coh G rho f ; rt = sCv et rho f
  in conv-from _ _ _ (snd-T A B t rho c (fst rt))
       (SndS-map _ _ (fst (snd (snd rt)))) (SndS-map _ _ (snd (snd (snd rt))))
sCv {G = G} (conv-Pi {u = u} {A} {A'} {B} {B'} un dA dB dB' eA eB) rho f =
  let c = Fits-coh G rho f
      rA = sCv eA rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
            InvConvP (Body B rho x) (Body B' rho x) (EvalRel (wkExpr u) (extendEnv rho x))
      ihB x a m e = sCv eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _
       (InvTypP-map _ _ _ _ (\ v x -> x) (\ v x -> x) (univ-in un rho)
          (pi-T A B rho c (sTmU un dA rho f) (bodyTmU un dB rho f)))
       (pi-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e)))))
       (pi-incl A' A B' B rho (snd (snd (snd rA)))
          (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e))))))
sCv {G = G} (conv-Sigma {u = u} {A} {A'} {B} {B'} un dA dB dB' eA eB) rho f =
  let c = Fits-coh G rho f
      rA = sCv eA rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
            InvConvP (Body B rho x) (Body B' rho x) (EvalRel (wkExpr u) (extendEnv rho x))
      ihB x a m e = sCv eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _
       (InvTypP-map _ _ _ _ (\ v x -> x) (\ v x -> x) (univ-in un rho)
          (sig-T A B rho c (sTmU un dA rho f) (bodyTmU un dB rho f)))
       (sig-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e)))))
       (sig-incl A' A B' B rho (snd (snd (snd rA)))
          (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e))))))
sCv {G = G} (conv-Suc {t = t} {t'} et) rho f =
  let c = Fits-coh G rho f ; rt = sCv et rho f
  in conv-from _ _ _ (Suc-typed (EvalRel t rho) (iR t rho c) (fst rt))
       (SucS-map _ _ (fst (snd (snd rt)))) (SucS-map _ _ (snd (snd (snd rt))))
sCv {G = G} (conv-Rec {z = z} {z'} {s} {s'} {k} {k'} {C} {C'} dC dC' eC ez es ek) rho f =
  let c = Fits-coh G rho f ; rz = sCv ez rho f ; rs = sCv es rho f ; rk = sCv ek rho f
  in conv-from _ _ _ (rec-T C z s k rho c (fst rz) (fst rs))
       (RecS-map _ _ _ _ _ _ (fst (snd (snd rz))) (fst (snd (snd rs))) (fst (snd (snd rk))))
       (RecS-map _ _ _ _ _ _ (snd (snd (snd rz))) (snd (snd (snd rs))) (snd (snd (snd rk))))
sCv (conv-Ucode df dg ef eg) rho f =
  conv-from _ _ _ (Atom-typed UCode UCode tt tt _ (mkSigma tt tt)) (\ u x -> x) (\ u x -> x)
sCv {G = G} (conv-Fhat {f = fe} {f'} {g} {g'} {A} {A'} {B} {B'} ef eg dA dB dB' eA eB) rho f =
  let c = Fits-coh G rho f ; rf = sCv ef rho f ; rA = sCv eA rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
            InvConvP (Body B rho x) (Body B' rho x) (EvalRel (wkExpr (Ucode fe g)) (extendEnv rho x))
      ihB x a m e = sCv eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _ (fhat-T fe g A (Lam A B) rho c (fst rf))
       (AppS-map _ _ _ _ (AppS-map _ _ _ _ (fst (snd (snd rf))) (fst (snd (snd rA))))
          (lam-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e))))))
       (AppS-map _ _ _ _ (AppS-map _ _ _ _ (snd (snd (snd rf))) (snd (snd (snd rA))))
          (lam-incl A' A B' B rho (snd (snd (snd rA)))
             (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e)))))))
sCv {G = G} (conv-Ghat {f = fe} {f'} {g} {g'} {A} {A'} {c'} {c''} {B} {B'} ef eg dA dB dB' eA eB ec) rho f =
  let c = Fits-coh G rho f ; rg = sCv eg rho f ; rA = sCv eA rho f ; rc = sCv ec rho f
      ihB : (x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
            InvConvP (Body B rho x) (Body B' rho x) (EvalRel (wkExpr (Ucode fe g)) (extendEnv rho x))
      ihB x a m e = sCv eB (extendEnv rho x) (Fits-ext G A rho x a f m e)
  in conv-from _ _ _ (ghat-T fe g A (Lam A B) c' rho c (fst rg))
       (AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (fst (snd (snd rg))) (fst (snd (snd rA))))
          (lam-incl A A' B B' rho (fst (snd (snd rA))) (\ x a m e -> fst (snd (snd (ihB x a m e))))))
          (fst (snd (snd rc))))
       (AppS-map _ _ _ _ (AppS-map _ _ _ _ (AppS-map _ _ _ _ (snd (snd (snd rg))) (snd (snd (snd rA))))
          (lam-incl A' A B' B rho (snd (snd (snd rA)))
             (\ x a m e -> snd (snd (snd (ihB x a m (snd (snd (snd rA)) a e)))))))
          (snd (snd (snd rc))))
