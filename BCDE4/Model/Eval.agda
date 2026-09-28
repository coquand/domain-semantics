{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.Eval
--
-- The relational semantics of the core syntax in finite elements.
--
-- Environments are indexed by the ambient level theory T (in which the
-- guards [ψ]A are evaluated) and by a LEVEL ENVIRONMENT θ : LSub (the
-- values of the level variables of the evaluated term, as level
-- expressions of T).  Level codes are taken with the parameter D.
--
-- Level functions are STRICT: in a level product / level abstraction a
-- non-⊥ value sits only above a level token LevEl k, and is then the
-- value of the body at the level ldec k (LBody).
--
-- 0 postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)

module BCDE4.Model.Eval (D : LDecAll) where

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun)
open import BCDE4.Dom.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMem ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ; NotBot-Sup-Comp ;
  EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ; Coherent-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMem-Sup-element ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append)
open import BCDE4.Model.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ; sel-skip-all ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import BCDE4.Model.Core
open import BCDE4.Levels using (LCtx ; Constr ; ValidC ; LSub ; LExpr ; LDec ;
  lconsS ; lsubC ; lsubL)
open import BCDE4.Model.Guard
open import BCDE4.Basic using (Either ; inl ; inr)

------------------------------------------------------------------------
-- Level codes
------------------------------------------------------------------------

lcodeT : LCtx -> LExpr -> Nat
lcodeT T = LDec.lcode (D T)

ldecT : LCtx -> Nat -> LExpr
ldecT T = LDec.ldec (D T)

private variable
  T : LCtx
  θ θ' : LSub

------------------------------------------------------------------------
-- Part 1: Finite environments
------------------------------------------------------------------------

data EnvApprox (T : LCtx) (θ : LSub) : Nat -> Set where
  emptyEnv  : EnvApprox T θ zero
  extendEnv : {n : Nat} -> EnvApprox T θ n -> FinEl -> EnvApprox T θ (suc n)

lookupEnv : {n : Nat} -> Fin n -> EnvApprox T θ n -> FinEl
lookupEnv fzero    (extendEnv rho v) = v
lookupEnv (fsuc i) (extendEnv rho v) = lookupEnv i rho

-- the same term values, another level environment
reidx : {n : Nat} -> EnvApprox T θ n -> EnvApprox T θ' n
reidx emptyEnv          = emptyEnv
reidx (extendEnv rho x) = extendEnv (reidx rho) x

-- entering a level binder: level 0 := l
extL : {n : Nat} -> EnvApprox T θ n -> (l : LExpr) -> EnvApprox T (lconsS l θ) n
extL rho l = reidx rho

lookupEnv-reidx : {n : Nat} (i : Fin n) (rho : EnvApprox T θ n) ->
  Eq (lookupEnv i (reidx {θ' = θ'} rho)) (lookupEnv i rho)
lookupEnv-reidx fzero    (extendEnv rho x) = refl
lookupEnv-reidx (fsuc i) (extendEnv rho x) = lookupEnv-reidx i rho

------------------------------------------------------------------------
-- Part 2: EvalRel
------------------------------------------------------------------------

mutual
  EvalRel : {n : Nat} -> Expr n -> EnvApprox T θ n -> FinEl -> Set

  -- Variables
  EvalRel (Var i) rho b = Pair (Coherent b) (LeCode b (lookupEnv i rho))

  -- Universe
  EvalRel {T = T} {θ = θ} (U l) rho b = Pair (Coherent b) (LeCode b (UCode (lcodeT T (lsubL θ l))))

  -- Application
  EvalRel (App M N) rho b =
    NBody b (Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                                      (EvalRel M rho (FunEl (cons (mkSigma v b) nil)))))

  -- Lambda
  EvalRel (Lam A M) rho Bot = Top
  EvalRel (Lam A M) rho (FunEl g) =
    Sigma FinEl (\ a ->
      Pair (CoherentFun g)
        (Pair (FinMem a U0)
          (Pair (EvalRel A rho a)
            ((u v : FinEl) ->
              Selection g u v ->
              Sigma FinEl (\ x ->
                Pair (LeCode x u)
                     (Pair (FinMem x a)
                           (EvalRel M (extendEnv rho x) v)))))))
  EvalRel (Lam A M) rho (UCode lu)   = Empty
  EvalRel (Lam A M) rho LevTy        = Empty
  EvalRel (Lam A M) rho (LevEl _)    = Empty
  EvalRel (Lam A M) rho (PiCode a f) = Empty
  EvalRel (Lam A M) rho (LPiCode f)  = Empty

  -- Pi
  EvalRel (Pi A B) rho Bot = Top
  EvalRel (Pi A B) rho (PiCode a f) =
    Pair (Coherent (PiCode a f))
      (Pair (EvalRel A rho a)
        (Sigma FinEl (\ a' ->
          Pair (EvalRel A rho a')
            ((u v : FinEl) ->
              Selection f u v ->
              Sigma FinEl (\ x ->
                Pair (LeCode x u)
                     (Pair (FinMem x a')
                           (EvalRel B (extendEnv rho x) v)))))))
  EvalRel (Pi A B) rho (UCode lu)  = Empty
  EvalRel (Pi A B) rho LevTy       = Empty
  EvalRel (Pi A B) rho (LevEl _)   = Empty
  EvalRel (Pi A B) rho (FunEl g)   = Empty
  EvalRel (Pi A B) rho (LPiCode f) = Empty

  -- Guard [ψ]A: ⊥, or A when ψ (instantiated by θ) holds in T
  EvalRel {T = T} {θ = θ} (Grd c A) rho b = Guard (ValidC T (lsubC θ c)) (EvalRel A rho) b

  -- ⟨ψ⟩t: the same
  EvalRel {T = T} {θ = θ} (GLam c t) rho b = Guard (ValidC T (lsubC θ c)) (EvalRel t rho) b

  -- ∅ is interpreted by ⊥ (the one-point type)
  EvalRel Emp rho b = Pair (Coherent b) (LeCode b Bot)

  -- level product [α]A
  EvalRel (LPi A) rho Bot = Top
  EvalRel (LPi A) rho (LPiCode f) =
    Pair (Coherent (LPiCode f)) ((u v : FinEl) -> Selection f u v -> LBody A rho u v)
  EvalRel (LPi A) rho (UCode lu)   = Empty
  EvalRel (LPi A) rho LevTy        = Empty
  EvalRel (LPi A) rho (LevEl _)    = Empty
  EvalRel (LPi A) rho (FunEl g)    = Empty
  EvalRel (LPi A) rho (PiCode a f) = Empty

  -- level abstraction ⟨α⟩u
  EvalRel (LLam M) rho Bot = Top
  EvalRel (LLam M) rho (FunEl g) =
    Pair (CoherentFun g) ((u v : FinEl) -> Selection g u v -> LBody M rho u v)
  EvalRel (LLam M) rho (UCode lu)   = Empty
  EvalRel (LLam M) rho LevTy        = Empty
  EvalRel (LLam M) rho (LevEl _)    = Empty
  EvalRel (LLam M) rho (PiCode a f) = Empty
  EvalRel (LLam M) rho (LPiCode f)  = Empty

  -- level application t l
  EvalRel {T = T} {θ = θ} (LApp t l) rho b =
    NBody b (EvalRel t rho (FunEl (cons (mkSigma (LevEl (lcodeT T (lsubL θ l))) b) nil)))

  -- the body of a strict level function at key u, value v
  LBody : {n : Nat} -> Expr n -> EnvApprox T θ n -> FinEl -> FinEl -> Set
  LBody {T = T} X rho u v =
    Either (LeCode v Bot)
           (Sigma Nat (\ k -> Pair (Eq (lcodeT T (ldecT T k)) k) (Pair (LeCode (LevEl k) u) (EvalRel X (extL rho (ldecT T k)) v))))

------------------------------------------------------------------------
-- The bodies of the application clauses
------------------------------------------------------------------------

AppX : {n : Nat} -> Expr n -> Expr n -> EnvApprox T θ n -> FinEl -> Set
AppX M N rho b = Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                                           (EvalRel M rho (FunEl (cons (mkSigma v b) nil))))

LAppX : {n : Nat} -> Expr n -> LExpr -> EnvApprox T θ n -> FinEl -> Set
LAppX {T = T} {θ = θ} t l rho b =
  EvalRel t rho (FunEl (cons (mkSigma (LevEl (lcodeT T (lsubL θ l))) b) nil))

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

absurd : {A : Set} -> Empty -> A
absurd ()

Coherent-val-LeBot-absurd : (v : FinEl) -> Pair (Coherent v) (NotBot v) -> LeCode v Bot -> Empty
Coherent-val-LeBot-absurd v cnb le = helper v (leBot-eq v le) (snd cnb)
  where
    helper : (v : FinEl) -> Eq v Bot -> NotBot v -> Empty
    helper .Bot refl ()

CoherentFun-LeBot-absurd : (g : FinFun) -> CoherentFun g -> LeFunCode g nil -> Empty
CoherentFun-LeBot-absurd nil cf lf = cf
CoherentFun-LeBot-absurd (cons p ps) cf lf =
  Coherent-val-LeBot-absurd (snd p) (mkSigma (CFTcons.val-coh cf) (CFTcons.val-nbot cf)) (fst lf)

-- a level token below u: u is that token
levLe-eq : (k : Nat) (u : FinEl) -> LeCode (LevEl k) u -> Eq u (LevEl k)
levLe-eq k Bot          ()
levLe-eq k (UCode _)    ()
levLe-eq k LevTy        ()
levLe-eq k (LevEl m)    e = Eq-sym (Eq-cong LevEl (EqL-Eq k m e))
  where
    Eq-cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
    Eq-cong f refl = refl
levLe-eq k (FunEl _)    ()
levLe-eq k (PiCode _ _) ()
levLe-eq k (LPiCode _)  ()

-- two level tokens below a coherent u are the same
levLe-same : (k m : Nat) (u : FinEl) -> Coherent u -> LeCode (LevEl k) u -> LeCode (LevEl m) u -> Eq k m
levLe-same k m u cu lk lm = EqL-Eq k m (LeCode-Comp (LevEl k) (LevEl m) u cu lk lm)

-- level tokens below compatible keys are the same
levComp-same : (k m : Nat) (u w : FinEl) -> LeCode (LevEl k) u -> LeCode (LevEl m) w -> Comp u w -> Eq m k
levComp-same k m u w lk lm c =
  let s1 = Comp-down (LevEl k) u w lk c
      s2 = Comp-down (LevEl m) w (LevEl k) lm (Comp-sym (LevEl k) w s1)
  in EqL-Eq m k s2

-- CompFun from the edges
CompFun-edges : (g1 g2 : FinFun) ->
  ((s : Edge) -> EdgeIn s g1 -> (t : Edge) -> EdgeIn t g2 -> CompStepStep s t) ->
  CompFun g1 g2
CompFun-edges nil g2 h = tt
CompFun-edges (cons s g1) g2 h =
  mkSigma (step g2 (\ t ein -> h s here t ein)) (CompFun-edges g1 g2 (\ s' e -> h s' (there e)))
  where
    step : (g : FinFun) -> ((t : Edge) -> EdgeIn t g -> CompStepStep s t) -> CompStepFun s g
    step nil h' = tt
    step (cons t g) h' = mkSigma (h' t here) (step g (\ t' e -> h' t' (there e)))

------------------------------------------------------------------------
-- Part 3: Coherence extraction
------------------------------------------------------------------------

EvalRel-coh : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (u : FinEl) ->
  EvalRel M rho u -> Coherent u

EvalRel-coh (Var i) rho u ev = fst ev
EvalRel-coh (U l) rho u ev = fst ev
EvalRel-coh (App M N) rho u ev =
  nbody-coh {X = AppX M N rho} (\ b nb e -> Coherent-singleton-val (fst e) b
                           (EvalRel-coh M rho (FunEl (cons (mkSigma (fst e) b) nil)) (snd (snd e)))) u ev
EvalRel-coh (Lam A M) rho Bot ev = tt
EvalRel-coh (Lam A M) rho (FunEl g) ev = fst (snd ev)
EvalRel-coh (Lam A M) rho (UCode lu) ()
EvalRel-coh (Lam A M) rho LevTy ()
EvalRel-coh (Lam A M) rho (LevEl _) ()
EvalRel-coh (Lam A M) rho (PiCode a f) ()
EvalRel-coh (Lam A M) rho (LPiCode f) ()
EvalRel-coh (Pi A B) rho Bot ev = tt
EvalRel-coh (Pi A B) rho (PiCode a f) ev = fst ev
EvalRel-coh (Pi A B) rho (UCode lu) ()
EvalRel-coh (Pi A B) rho LevTy ()
EvalRel-coh (Pi A B) rho (LevEl _) ()
EvalRel-coh (Pi A B) rho (FunEl g) ()
EvalRel-coh (Pi A B) rho (LPiCode f) ()
EvalRel-coh (Grd c A) rho u ev = guard-coh (EvalRel-coh A rho) u ev
EvalRel-coh (GLam c t) rho u ev = guard-coh (EvalRel-coh t rho) u ev
EvalRel-coh Emp rho u ev = fst ev
EvalRel-coh (LPi A) rho Bot ev = tt
EvalRel-coh (LPi A) rho (LPiCode f) ev = fst ev
EvalRel-coh (LPi A) rho (UCode lu) ()
EvalRel-coh (LPi A) rho LevTy ()
EvalRel-coh (LPi A) rho (LevEl _) ()
EvalRel-coh (LPi A) rho (FunEl g) ()
EvalRel-coh (LPi A) rho (PiCode a f) ()
EvalRel-coh (LLam M) rho Bot ev = tt
EvalRel-coh (LLam M) rho (FunEl g) ev = fst ev
EvalRel-coh (LLam M) rho (UCode lu) ()
EvalRel-coh (LLam M) rho LevTy ()
EvalRel-coh (LLam M) rho (LevEl _) ()
EvalRel-coh (LLam M) rho (PiCode a f) ()
EvalRel-coh (LLam M) rho (LPiCode f) ()
EvalRel-coh {T = T} {θ = θ} (LApp t l) rho u ev =
  nbody-coh {X = LAppX t l rho} (\ b nb e -> Coherent-singleton-val (LevEl (lcodeT T (lsubL θ l))) b
                           (EvalRel-coh t rho _ e)) u ev

------------------------------------------------------------------------
-- Environment infrastructure
------------------------------------------------------------------------

CoherentEnv : {n : Nat} -> EnvApprox T θ n -> Set
CoherentEnv emptyEnv = Top
CoherentEnv (extendEnv rho u) = Pair (CoherentEnv rho) (Coherent u)

CoherentEnv-reidx : {n : Nat} (rho : EnvApprox T θ n) -> CoherentEnv rho ->
  CoherentEnv (reidx {θ' = θ'} rho)
CoherentEnv-reidx emptyEnv c = tt
CoherentEnv-reidx (extendEnv rho u) c = mkSigma (CoherentEnv-reidx rho (fst c)) (snd c)

lookupEnv-coh : {n : Nat} (i : Fin n) (rho : EnvApprox T θ n) ->
  CoherentEnv rho -> Coherent (lookupEnv i rho)
lookupEnv-coh fzero    (extendEnv rho u) crho = snd crho
lookupEnv-coh (fsuc i) (extendEnv rho u) crho = lookupEnv-coh i rho (fst crho)

EnvLe : {n : Nat} -> EnvApprox T θ n -> EnvApprox T θ n -> Set
EnvLe emptyEnv emptyEnv = Top
EnvLe (extendEnv rho u) (extendEnv rho' u') =
  Pair (EnvLe rho rho')
       (Pair (Coherent u) (Pair (Coherent u') (LeCode u u')))

EnvLe-reidx : {n : Nat} (rho rho' : EnvApprox T θ n) -> EnvLe rho rho' ->
  EnvLe (reidx {θ' = θ'} rho) (reidx {θ' = θ'} rho')
EnvLe-reidx emptyEnv emptyEnv le = tt
EnvLe-reidx (extendEnv rho u) (extendEnv rho' u') le =
  mkSigma (EnvLe-reidx rho rho' (fst le)) (snd le)

lookupEnv-coh-left : {n : Nat} (i : Fin n) (rho rho' : EnvApprox T θ n) ->
  EnvLe rho rho' -> Coherent (lookupEnv i rho)
lookupEnv-coh-left fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  fst (snd envle)
lookupEnv-coh-left (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-coh-left i rho rho' (fst envle)

lookupEnv-coh-right : {n : Nat} (i : Fin n) (rho rho' : EnvApprox T θ n) ->
  EnvLe rho rho' -> Coherent (lookupEnv i rho')
lookupEnv-coh-right fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  fst (snd (snd envle))
lookupEnv-coh-right (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-coh-right i rho rho' (fst envle)

lookupEnv-mon : {n : Nat} (i : Fin n) (rho rho' : EnvApprox T θ n) ->
  EnvLe rho rho' -> LeCode (lookupEnv i rho) (lookupEnv i rho')
lookupEnv-mon fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  snd (snd (snd envle))
lookupEnv-mon (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-mon i rho rho' (fst envle)

EnvLe-extend : {n : Nat} (rho rho' : EnvApprox T θ n) (x : FinEl) ->
  EnvLe rho rho' -> Coherent x ->
  EnvLe (extendEnv rho x) (extendEnv rho' x)
EnvLe-extend rho rho' x envle cx =
  mkSigma envle (mkSigma cx (mkSigma cx (LeCode-refl x cx)))

EnvLe-refl : {n : Nat} (rho : EnvApprox T θ n) -> CoherentEnv rho -> EnvLe rho rho
EnvLe-refl emptyEnv crho = tt
EnvLe-refl (extendEnv rho u) crho =
  mkSigma (EnvLe-refl rho (fst crho))
          (mkSigma (snd crho) (mkSigma (snd crho) (LeCode-refl u (snd crho))))

EnvLe-extend-left : {n : Nat} (rho : EnvApprox T θ n) (x y : FinEl) ->
  CoherentEnv rho -> Comp x y -> Coherent x -> Coherent y ->
  EnvLe (extendEnv rho x) (extendEnv rho (Sup x y))
EnvLe-extend-left rho x y crho comp cx cy =
  mkSigma (EnvLe-refl rho crho)
          (mkSigma cx (mkSigma (Coherent-Sup x y comp cx cy)
                               (LeCode-Sup-left x y comp cx cy)))

EnvLe-extend-right : {n : Nat} (rho : EnvApprox T θ n) (x y : FinEl) ->
  CoherentEnv rho -> Comp x y -> Coherent x -> Coherent y ->
  EnvLe (extendEnv rho y) (extendEnv rho (Sup x y))
EnvLe-extend-right rho x y crho comp cx cy =
  mkSigma (EnvLe-refl rho crho)
          (mkSigma cy (mkSigma (Coherent-Sup x y comp cx cy)
                               (LeCode-Sup-right x y comp cx cy)))

------------------------------------------------------------------------
-- EvalRel-Bot
------------------------------------------------------------------------

EvalRel-Bot : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) ->
  EvalRel M rho Bot
EvalRel-Bot (Var i) rho = mkSigma tt tt
EvalRel-Bot (U l) rho = mkSigma tt tt
EvalRel-Bot (App M N) rho = tt
EvalRel-Bot (Lam A M) rho = tt
EvalRel-Bot (Pi A B) rho = tt
EvalRel-Bot (Grd c A) rho = tt
EvalRel-Bot (GLam c t) rho = tt
EvalRel-Bot Emp rho = mkSigma tt tt
EvalRel-Bot (LPi A) rho = tt
EvalRel-Bot (LLam M) rho = tt
EvalRel-Bot (LApp t l) rho = tt

------------------------------------------------------------------------
-- Level bodies: edgewise form
------------------------------------------------------------------------

LEdges : {n : Nat} -> Expr n -> EnvApprox T θ n -> FinFun -> Set
LEdges X rho g = (p : Edge) -> EdgeIn p g -> LBody X rho (fst p) (snd p)

LEdges-cons : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) (p : Edge) (ps : FinFun) ->
  LBody X rho (fst p) (snd p) -> LEdges X rho ps -> LEdges X rho (cons p ps)
LEdges-cons X rho p ps hd tl .p here = hd
LEdges-cons X rho p ps hd tl q (there ein) = tl q ein

LBody-edgewise : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) (g : FinFun) ->
  ((u v : FinEl) -> Selection g u v -> LBody X rho u v) -> LEdges X rho g
LBody-edgewise X rho g body p ein =
  Eq-transport (\ z -> LBody X rho (fst p) z) (Sup-Bot-r (snd p))
    (Eq-transport (\ z -> LBody X rho z (Sup (snd p) Bot)) (Sup-Bot-r (fst p))
      (body _ _ (singleton-selection p g ein)))

LPi-edgewise : {n : Nat} (A : Expr n) (rho : EnvApprox T θ n) (f : FinFun) ->
  EvalRel (LPi A) rho (LPiCode f) -> LEdges A rho f
LPi-edgewise A rho f ev = LBody-edgewise A rho f (snd ev)

LLam-edgewise : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (g : FinFun) ->
  EvalRel (LLam M) rho (FunEl g) -> LEdges M rho g
LLam-edgewise M rho g ev = LBody-edgewise M rho g (snd ev)

-- a non-⊥ value on a level edge sits at one level k, and its key is LevEl k
LBody-nb : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) (u v : FinEl) ->
  Coherent v -> NotBot v -> LBody X rho u v ->
  Sigma Nat (\ k -> Pair (Eq (lcodeT T (ldecT T k)) k) (Pair (LeCode (LevEl k) u) (EvalRel X (extL rho (ldecT T k)) v)))
LBody-nb X rho u v cv nb (inl le) = absurd (Coherent-val-LeBot-absurd v (mkSigma cv nb) le)
LBody-nb X rho u v cv nb (inr r)  = r

-- mapping the body of a level edge
lbody-map : {n m : Nat} (X : Expr n) (Y : Expr m) (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' m)
  (u v : FinEl) ->
  ((k : Nat) -> EvalRel X (extL rho (ldecT T k)) v -> EvalRel Y (extL rho' (ldecT T k)) v) ->
  LBody X rho u v -> LBody Y rho' u v
lbody-map X Y rho rho' u v h (inl le) = inl le
lbody-map X Y rho rho' u v h (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) = inr (mkSigma k (mkSigma ck (mkSigma lk (h k e))))

------------------------------------------------------------------------
-- EvalRel-mon-env
------------------------------------------------------------------------

EvalRel-mon-env : {n : Nat} (M : Expr n) (rho rho' : EnvApprox T θ n) (u : FinEl) ->
  EvalRel M rho u -> EnvLe rho rho' -> EvalRel M rho' u

LBody-mon-env : {n : Nat} (X : Expr n) (rho rho' : EnvApprox T θ n) (u v : FinEl) ->
  LBody X rho u v -> EnvLe rho rho' -> LBody X rho' u v
LBody-mon-env X rho rho' u v (inl le) envle = inl le
LBody-mon-env {T = T} X rho rho' u v (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) envle =
  inr (mkSigma k (mkSigma ck (mkSigma lk
    (EvalRel-mon-env X (extL rho (ldecT T k)) (extL rho' (ldecT T k)) v e (EnvLe-reidx rho rho' envle)))))

EvalRel-mon-env (Var i) rho rho' u ev envle =
  mkSigma (fst ev) (LeCode-trans u (lookupEnv i rho) (lookupEnv i rho')
    (fst ev) (lookupEnv-coh-left i rho rho' envle)
    (lookupEnv-coh-right i rho rho' envle) (snd ev) (lookupEnv-mon i rho rho' envle))
EvalRel-mon-env (U l) rho rho' u ev envle = ev
EvalRel-mon-env (App M N) rho rho' u ev envle =
  nbody-map {X = AppX M N rho u} {Y = AppX M N rho' u} u (\ e -> mkSigma (fst e) (mkSigma (EvalRel-mon-env N rho rho' (fst e) (fst (snd e)) envle)
                                               (EvalRel-mon-env M rho rho' _ (snd (snd e)) envle))) ev
EvalRel-mon-env (Lam A M) rho rho' Bot ev envle = tt
EvalRel-mon-env (Lam A M) rho rho' (FunEl g) ev envle =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma a (mkSigma cg (mkSigma aU
       (mkSigma (EvalRel-mon-env A rho rho' a evA envle)
         (\ u v sel ->
            let w      = body u v sel
                x      = fst w
                le-x-u = fst (snd w)
                mem    = fst (snd (snd w))
                evM    = snd (snd (snd w))
                cx     = FinMem-coh-u x a mem
                envle' = EnvLe-extend rho rho' x envle cx
            in mkSigma x (mkSigma le-x-u (mkSigma mem
                 (EvalRel-mon-env M (extendEnv rho x) (extendEnv rho' x)
                    v evM envle')))))))
EvalRel-mon-env (Lam A M) rho rho' (UCode lu) () envle
EvalRel-mon-env (Lam A M) rho rho' LevTy () envle
EvalRel-mon-env (Lam A M) rho rho' (LevEl _) () envle
EvalRel-mon-env (Lam A M) rho rho' (PiCode a f) () envle
EvalRel-mon-env (Lam A M) rho rho' (LPiCode f) () envle
EvalRel-mon-env (Pi A B) rho rho' Bot ev envle = tt
EvalRel-mon-env (Pi A B) rho rho' (PiCode a f) ev envle =
  let caf  = fst ev
      evA  = fst (snd ev)
      a'   = fst (snd (snd ev))
      evA' = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma caf (mkSigma (EvalRel-mon-env A rho rho' a evA envle)
       (mkSigma a' (mkSigma (EvalRel-mon-env A rho rho' a' evA' envle)
       (\ u v sel ->
          let w      = body u v sel
              x      = fst w
              le-x-u = fst (snd w)
              mem    = fst (snd (snd w))
              evB    = snd (snd (snd w))
              cx     = FinMem-coh-u x a' mem
              envle' = EnvLe-extend rho rho' x envle cx
          in mkSigma x (mkSigma le-x-u (mkSigma mem
               (EvalRel-mon-env B (extendEnv rho x) (extendEnv rho' x)
                  v evB envle')))))))
EvalRel-mon-env (Pi A B) rho rho' (UCode lu) () envle
EvalRel-mon-env (Pi A B) rho rho' LevTy () envle
EvalRel-mon-env (Pi A B) rho rho' (LevEl _) () envle
EvalRel-mon-env (Pi A B) rho rho' (FunEl g) () envle
EvalRel-mon-env (Pi A B) rho rho' (LPiCode f) () envle
EvalRel-mon-env (Grd c A) rho rho' u ev envle =
  guard-map (\ v -> v) (\ b e -> EvalRel-mon-env A rho rho' b e envle) u ev
EvalRel-mon-env (GLam c t) rho rho' u ev envle =
  guard-map (\ v -> v) (\ b e -> EvalRel-mon-env t rho rho' b e envle) u ev
EvalRel-mon-env Emp rho rho' u ev envle = ev
EvalRel-mon-env (LPi A) rho rho' Bot ev envle = tt
EvalRel-mon-env (LPi A) rho rho' (LPiCode f) ev envle =
  mkSigma (fst ev) (\ u v sel -> LBody-mon-env A rho rho' u v (snd ev u v sel) envle)
EvalRel-mon-env (LPi A) rho rho' (UCode lu) () envle
EvalRel-mon-env (LPi A) rho rho' LevTy () envle
EvalRel-mon-env (LPi A) rho rho' (LevEl _) () envle
EvalRel-mon-env (LPi A) rho rho' (FunEl g) () envle
EvalRel-mon-env (LPi A) rho rho' (PiCode a f) () envle
EvalRel-mon-env (LLam M) rho rho' Bot ev envle = tt
EvalRel-mon-env (LLam M) rho rho' (FunEl g) ev envle =
  mkSigma (fst ev) (\ u v sel -> LBody-mon-env M rho rho' u v (snd ev u v sel) envle)
EvalRel-mon-env (LLam M) rho rho' (UCode lu) () envle
EvalRel-mon-env (LLam M) rho rho' LevTy () envle
EvalRel-mon-env (LLam M) rho rho' (LevEl _) () envle
EvalRel-mon-env (LLam M) rho rho' (PiCode a f) () envle
EvalRel-mon-env (LLam M) rho rho' (LPiCode f) () envle
EvalRel-mon-env (LApp t l) rho rho' u ev envle =
  nbody-map {X = LAppX t l rho u} {Y = LAppX t l rho' u} u (\ e -> EvalRel-mon-env t rho rho' _ e envle) ev

------------------------------------------------------------------------
-- App-decompose
------------------------------------------------------------------------

App-decompose : {n : Nat} (M N : Expr n) (rho : EnvApprox T θ n)
  (u : FinEl) -> NotBot u ->
  EvalRel (App M N) rho u ->
  S.Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v u) nil))))
App-decompose M N rho u nb ev = nbody-out u nb ev

App-compose : {n : Nat} (M N : Expr n) (rho : EnvApprox T θ n)
  (u : FinEl) -> NotBot u ->
  S.Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v u) nil)))) ->
  EvalRel (App M N) rho u
App-compose M N rho u nb ev = nbody-in u nb ev

------------------------------------------------------------------------
-- Edgewise lemmas
------------------------------------------------------------------------

Lam-edgewise : {n : Nat} (A : Expr n) (M : Expr (suc n))
  (rho : EnvApprox T θ n) (g : FinFun) ->
  EvalRel (Lam A M) rho (FunEl g) ->
  S.Sigma FinEl (\ a ->
    Pair (CoherentFun g)
      (Pair (FinMem a U0)
        (Pair (EvalRel A rho a)
          ((p : Edge) -> EdgeIn p g ->
            S.Sigma FinEl (\ x ->
              Pair (LeCode x (fst p))
                   (Pair (FinMem x a)
                         (EvalRel M (extendEnv rho x) (snd p))))))))
Lam-edgewise A M rho g ev =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA
       (\ p ein ->
          let sel = singleton-selection p g ein
              w   = body (Sup (fst p) Bot) (Sup (snd p) Bot) sel
              x   = fst w
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p)) (fst (snd w))
              mem = fst (snd (snd w))
              evM = Eq-transport (EvalRel M (extendEnv rho x)) (Sup-Bot-r (snd p)) (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evM))))))

Pi-edgewise : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox T θ n) (a : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode a f) ->
  Pair (Coherent (PiCode a f))
    (Pair (EvalRel A rho a)
      (S.Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((p : Edge) -> EdgeIn p f ->
            S.Sigma FinEl (\ x ->
              Pair (LeCode x (fst p))
                   (Pair (FinMem x a')
                         (EvalRel B (extendEnv rho x) (snd p))))))))
Pi-edgewise A B rho a f ev =
  let caf  = fst ev
      evA  = fst (snd ev)
      a'   = fst (snd (snd ev))
      evA' = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA'
       (\ p ein ->
          let sel = singleton-selection p f ein
              w   = body (Sup (fst p) Bot) (Sup (snd p) Bot) sel
              x   = fst w
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p)) (fst (snd w))
              mem = fst (snd (snd w))
              evB = Eq-transport (EvalRel B (extendEnv rho x)) (Sup-Bot-r (snd p)) (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evB))))))

------------------------------------------------------------------------
-- Helpers for EvalRel-Comp
------------------------------------------------------------------------

App-Comp-helper : {n : Nat} (M N : Expr n) (rho : EnvApprox T θ n) ->
  (IH-M : (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> Comp u v) ->
  (IH-N : (u v : FinEl) -> EvalRel N rho u -> EvalRel N rho v -> Comp u v) ->
  (u1 u2 : FinEl) ->
  (v1 : FinEl) -> EvalRel N rho v1 ->
  EvalRel M rho (FunEl (cons (mkSigma v1 u1) nil)) ->
  (v2 : FinEl) -> EvalRel N rho v2 ->
  EvalRel M rho (FunEl (cons (mkSigma v2 u2) nil)) ->
  Comp u1 u2
App-Comp-helper M N rho ihm ihn u1 u2 v1 evN1 evM1 v2 evN2 evM2 =
  let comp-fg = ihm (FunEl (cons (mkSigma v1 u1) nil))
                    (FunEl (cons (mkSigma v2 u2) nil)) evM1 evM2
      step = fst (fst comp-fg)
      comp-v = ihn v1 v2 evN1 evN2
  in step comp-v

Comp-via-body : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox T θ n)
  (x1 x2 : FinEl) (v1 v2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) v1 ->
  EvalRel M (extendEnv rho x2) v2 ->
  ((rho' : EnvApprox T θ (suc n)) -> CoherentEnv rho' ->
    EvalRel M rho' v1 -> EvalRel M rho' v2 -> Comp v1 v2) ->
  Comp v1 v2
Comp-via-body M rho x1 x2 v1 v2 crho comp cx1 cx2 ev1 ev2 ih =
  let envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1' = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 ev1 envle1
      ev2' = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 ev2 envle2
      crho' = mkSigma crho (Coherent-Sup x1 x2 comp cx1 cx2)
  in ih (extendEnv rho (Sup x1 x2)) crho' ev1' ev2'

Lam-CompStepFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox T θ n)
  (a1 a2 : FinEl)
  (s : Edge) (g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g2 ->
  S.Sigma FinEl (\ xs ->
    Pair (LeCode xs (fst s)) (Pair (FinMem xs a1) (EvalRel M (extendEnv rho xs) (snd s)))) ->
  ((t : Edge) -> EdgeIn t g2 ->
    S.Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t)) (Pair (FinMem xt a2) (EvalRel M (extendEnv rho xt) (snd t))))) ->
  ((rho' : EnvApprox T θ (suc n)) -> CoherentEnv rho' ->
    (u v : FinEl) -> EvalRel M rho' u -> EvalRel M rho' v -> Comp u v) ->
  CompStepFun s g2
Lam-CompStepFun M rho a1 a2 s nil crho cg2 ws wf ih = tt
Lam-CompStepFun M rho a1 a2 s (cons t rest) crho cg2 ws wf ih =
  let xs    = fst ws
      le-xs = fst (snd ws)
      mem-s = fst (snd (snd ws))
      ev-s  = snd (snd (snd ws))
      wt    = wf t here
      xt    = fst wt
      le-xt = fst (snd wt)
      mem-t = fst (snd (snd wt))
      ev-t  = snd (snd (snd wt))
      step : CompStepStep s t
      step comp-keys =
        let cxs    = FinMem-coh-u xs a1 mem-s
            cxt    = FinMem-coh-u xt a2 mem-t
            step-a = Comp-down xs (fst s) (fst t) le-xs comp-keys
            step-b = Comp-down xt (fst t) xs le-xt (Comp-sym xs (fst t) step-a)
            comp-x = Comp-sym xt xs step-b
        in Comp-via-body M rho xs xt (snd s) (snd t) crho comp-x cxs cxt ev-s ev-t
             (\ rho' crho' ev1 ev2 -> ih rho' crho' (snd s) (snd t) ev1 ev2)
      tail = Lam-CompStepFun M rho a1 a2 s rest crho (CFTcons.tail-coh cg2)
               ws (\ t' ein -> wf t' (there ein)) ih
  in mkSigma step tail

Lam-CompFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox T θ n)
  (a1 a2 : FinEl)
  (g1 g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g1 -> CoherentFunTail g2 ->
  ((s : Edge) -> EdgeIn s g1 ->
    S.Sigma FinEl (\ xs ->
      Pair (LeCode xs (fst s)) (Pair (FinMem xs a1) (EvalRel M (extendEnv rho xs) (snd s))))) ->
  ((t : Edge) -> EdgeIn t g2 ->
    S.Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t)) (Pair (FinMem xt a2) (EvalRel M (extendEnv rho xt) (snd t))))) ->
  ((rho' : EnvApprox T θ (suc n)) -> CoherentEnv rho' ->
    (u v : FinEl) -> EvalRel M rho' u -> EvalRel M rho' v -> Comp u v) ->
  CompFun g1 g2
Lam-CompFun M rho a1 a2 nil g2 crho cg1 cg2 wf1 wf2 ih = tt
Lam-CompFun M rho a1 a2 (cons s rest) g2 crho cg1 cg2 wf1 wf2 ih =
  mkSigma (Lam-CompStepFun M rho a1 a2 s g2 crho cg2
             (wf1 s here) wf2 ih)
          (Lam-CompFun M rho a1 a2 rest g2 crho (CFTcons.tail-coh cg1) cg2
             (\ s' ein -> wf1 s' (there ein)) wf2 ih)

-- two level edges with compatible keys have compatible values
LBody-comp : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) ->
  (ih : (k : Nat) (x y : FinEl) -> EvalRel X (extL rho (ldecT T k)) x ->
          EvalRel X (extL rho (ldecT T k)) y -> Comp x y) ->
  (u1 v1 u2 v2 : FinEl) -> Comp u1 u2 -> LBody X rho u1 v1 -> LBody X rho u2 v2 -> Comp v1 v2
LBody-comp X rho ih u1 v1 u2 v2 c (inl le1) b2 =
  Eq-transport (\ z -> Comp z v2) (Eq-sym (leBot-eq v1 le1)) (comp-Bot-l v2)
LBody-comp X rho ih u1 v1 u2 v2 c (inr b1) (inl le2) =
  Eq-transport (\ z -> Comp v1 z) (Eq-sym (leBot-eq v2 le2)) (comp-Bot-r v1)
LBody-comp {T = T} X rho ih u1 v1 u2 v2 c (inr (mkSigma k1 (mkSigma ck1 (mkSigma l1 e1)))) (inr (mkSigma k2 (mkSigma ck2 (mkSigma l2 e2)))) =
  let eq  = levComp-same k1 k2 u1 u2 l1 l2 c
      e2' = Eq-transport (\ k -> EvalRel X (extL rho (ldecT T k)) v2) eq e2
  in ih k1 v1 v2 e1 e2'

LCompFun : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) (g1 g2 : FinFun) ->
  (ih : (k : Nat) (x y : FinEl) -> EvalRel X (extL rho (ldecT T k)) x ->
          EvalRel X (extL rho (ldecT T k)) y -> Comp x y) ->
  LEdges X rho g1 -> LEdges X rho g2 -> CompFun g1 g2
LCompFun X rho g1 g2 ih e1 e2 =
  CompFun-edges g1 g2 (\ s ins t int ck ->
    LBody-comp X rho ih (fst s) (snd s) (fst t) (snd t) ck (e1 s ins) (e2 t int))

LeFunCode-Sup-pair :
  (v1 u1 v2 u2 : FinEl) ->
  Comp v1 v2 -> Comp u1 u2 ->
  CoherentFun (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)) ->
  Coherent (Sup v1 v2) ->
  LeFunCode (cons (mkSigma (Sup v1 v2) (Sup u1 u2)) nil)
            (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil))
LeFunCode-Sup-pair v1 u1 v2 u2 comp-v comp-u cf c-supv =
  let sel-inner = sel-take (comp-Bot-r v2) (comp-Bot-r u2) (sel-skip-all nil)
      comp-v1-sv2 = Eq-transport (Comp v1) (Eq-sym (Sup-Bot-r v2)) comp-v
      comp-u1-su2 = Eq-transport (Comp u1) (Eq-sym (Sup-Bot-r u2)) comp-u
      sel-both = sel-take comp-v1-sv2 comp-u1-su2 sel-inner
      eq-key = Eq-transport (\ z -> Eq (Sup v1 (Sup v2 Bot)) (Sup v1 z)) (Sup-Bot-r v2) refl
      eq-val = Eq-transport (\ z -> Eq (Sup u1 (Sup u2 Bot)) (Sup u1 z)) (Sup-Bot-r u2) refl
      g2 = cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)
      ctf = cft-from-cf g2 cf
      lf-refl = LeFunCode-refl g2 ctf
      c-key = Eq-transport Coherent (Eq-sym eq-key) c-supv
      le-raw = Selection-le-EvalFun g2 sel-both lf-refl cf cf c-key
      le-trans = Eq-transport (\ z -> LeCode z (EvalFun g2 (Sup v1 (Sup v2 Bot)))) eq-val le-raw
      le-result = Eq-transport (\ z -> LeCode (Sup u1 u2) (EvalFun g2 z)) eq-key le-trans
  in mkSigma le-result tt

------------------------------------------------------------------------
-- EvalRel-Comp
------------------------------------------------------------------------

EvalRel-Comp : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) ->
  CoherentEnv rho -> (u v : FinEl) ->
  EvalRel M rho u -> EvalRel M rho v -> Comp u v
EvalRel-Comp (Grd c A) rho crho u v ev1 ev2 = guard-Comp (EvalRel-Comp A rho crho) u v ev1 ev2
EvalRel-Comp (GLam c t) rho crho u v ev1 ev2 = guard-Comp (EvalRel-Comp t rho crho) u v ev1 ev2
EvalRel-Comp Emp rho crho u v ev1 ev2 = LeCode-Comp u v Bot tt (snd ev1) (snd ev2)
EvalRel-Comp (Var i) rho crho u v ev1 ev2 =
  LeCode-Comp u v (lookupEnv i rho) (lookupEnv-coh i rho crho) (snd ev1) (snd ev2)
EvalRel-Comp {T = T} {θ = θ} (U l) rho crho u v ev1 ev2 = LeCode-Comp u v (UCode (lcodeT T (lsubL θ l))) tt (snd ev1) (snd ev2)
EvalRel-Comp (App M N) rho crho u v ev1 ev2 =
  nbody-Comp {X = AppX M N rho} (\ u v nu nv e1 e2 ->
    App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
      u v (fst e1) (fst (snd e1)) (snd (snd e1)) (fst e2) (fst (snd e2)) (snd (snd e2))) u v ev1 ev2
EvalRel-Comp {T = T} {θ = θ} (LApp t l) rho crho u v ev1 ev2 =
  nbody-Comp {X = LAppX t l rho} (\ u v nu nv e1 e2 ->
    fst (fst (EvalRel-Comp t rho crho _ _ e1 e2)) (EqL-refl (lcodeT T (lsubL θ l)))) u v ev1 ev2
-- Lam
EvalRel-Comp (Lam A M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Lam A M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (Lam A M) rho crho (UCode lu) v () ev2
EvalRel-Comp (Lam A M) rho crho LevTy v () ev2
EvalRel-Comp (Lam A M) rho crho (LevEl _) v () ev2
EvalRel-Comp (Lam A M) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (Lam A M) rho crho (LPiCode f1) v () ev2
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (UCode lu) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) LevTy ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (LevEl _) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (LPiCode f2) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (FunEl g2) ev1 ev2 =
  let ew1 = Lam-edgewise A M rho g1 ev1
      ew2 = Lam-edgewise A M rho g2 ev2
  in Lam-CompFun M rho (fst ew1) (fst ew2) g1 g2 crho
       (cft-from-cf g1 (fst (snd ew1))) (cft-from-cf g2 (fst (snd ew2)))
       (snd (snd (snd (snd ew1)))) (snd (snd (snd (snd ew2))))
       (\ rho' crho' u v eu ev -> EvalRel-Comp M rho' crho' u v eu ev)
-- Pi
EvalRel-Comp (Pi A B) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) Bot ev1 ev2 = comp-Bot-r (PiCode a1 f1)
EvalRel-Comp (Pi A B) rho crho (UCode lu) v () ev2
EvalRel-Comp (Pi A B) rho crho LevTy v () ev2
EvalRel-Comp (Pi A B) rho crho (LevEl _) v () ev2
EvalRel-Comp (Pi A B) rho crho (FunEl g1) v () ev2
EvalRel-Comp (Pi A B) rho crho (LPiCode g1) v () ev2
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (UCode lu) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) LevTy ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (LevEl _) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (FunEl g2) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (LPiCode g2) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  let pew1 = Pi-edgewise A B rho a1 f1 ev1
      pew2 = Pi-edgewise A B rho a2 f2 ev2
      comp-a = EvalRel-Comp A rho crho a1 a2 (fst (snd ev1)) (fst (snd ev2))
      comp-f = Lam-CompFun B rho (fst (snd (snd pew1))) (fst (snd (snd pew2))) f1 f2 crho
                 (snd (fst ev1)) (snd (fst ev2))
                 (snd (snd (snd (snd pew1)))) (snd (snd (snd (snd pew2))))
                 (\ rho' crho' u v eu ev -> EvalRel-Comp B rho' crho' u v eu ev)
  in mkSigma comp-a comp-f
-- LPi
EvalRel-Comp (LPi A) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (LPi A) rho crho (LPiCode f1) Bot ev1 ev2 = comp-Bot-r (LPiCode f1)
EvalRel-Comp (LPi A) rho crho (UCode lu) v () ev2
EvalRel-Comp (LPi A) rho crho LevTy v () ev2
EvalRel-Comp (LPi A) rho crho (LevEl _) v () ev2
EvalRel-Comp (LPi A) rho crho (FunEl g1) v () ev2
EvalRel-Comp (LPi A) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (LPi A) rho crho (LPiCode f1) (UCode lu) ev1 ()
EvalRel-Comp (LPi A) rho crho (LPiCode f1) LevTy ev1 ()
EvalRel-Comp (LPi A) rho crho (LPiCode f1) (LevEl _) ev1 ()
EvalRel-Comp (LPi A) rho crho (LPiCode f1) (FunEl g2) ev1 ()
EvalRel-Comp (LPi A) rho crho (LPiCode f1) (PiCode a2 f2) ev1 ()
EvalRel-Comp {T = T} (LPi A) rho crho (LPiCode f1) (LPiCode f2) ev1 ev2 =
  LCompFun A rho f1 f2
    (\ k x y e1 e2 -> EvalRel-Comp A (extL rho (ldecT T k)) (CoherentEnv-reidx rho crho) x y e1 e2)
    (LPi-edgewise A rho f1 ev1) (LPi-edgewise A rho f2 ev2)
-- LLam
EvalRel-Comp (LLam M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (LLam M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (LLam M) rho crho (UCode lu) v () ev2
EvalRel-Comp (LLam M) rho crho LevTy v () ev2
EvalRel-Comp (LLam M) rho crho (LevEl _) v () ev2
EvalRel-Comp (LLam M) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (LLam M) rho crho (LPiCode f1) v () ev2
EvalRel-Comp (LLam M) rho crho (FunEl g1) (UCode lu) ev1 ()
EvalRel-Comp (LLam M) rho crho (FunEl g1) LevTy ev1 ()
EvalRel-Comp (LLam M) rho crho (FunEl g1) (LevEl _) ev1 ()
EvalRel-Comp (LLam M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (LLam M) rho crho (FunEl g1) (LPiCode f2) ev1 ()
EvalRel-Comp {T = T} (LLam M) rho crho (FunEl g1) (FunEl g2) ev1 ev2 =
  LCompFun M rho g1 g2
    (\ k x y e1 e2 -> EvalRel-Comp M (extL rho (ldecT T k)) (CoherentEnv-reidx rho crho) x y e1 e2)
    (LLam-edgewise M rho g1 ev1) (LLam-edgewise M rho g2 ev2)

------------------------------------------------------------------------
-- EvalRel-down: downward closure of the evaluation relation.
------------------------------------------------------------------------

EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n)
  (u u' : FinEl) -> CoherentEnv rho -> Coherent u' ->
  EvalRel M rho u -> LeCode u' u -> EvalRel M rho u'

-- a singleton graph can be lowered in its value
single-down : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (key w w' : FinEl) ->
  CoherentEnv rho -> Coherent w' -> NotBot w' -> LeCode w' w ->
  EvalRel M rho (FunEl (cons (mkSigma key w) nil)) ->
  EvalRel M rho (FunEl (cons (mkSigma key w') nil))
single-down M rho key w w' crho cw' nbw' le evM =
  let sg   = FunEl (cons (mkSigma key w) nil)
      c-vu = EvalRel-coh M rho sg evM
      cv   = Coherent-singleton-key key w c-vu
      cu   = Coherent-singleton-val key w c-vu
      le-refl = fst (LeCode-refl sg c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma key w) nil) key c-vu cv
      le-u'-ef = LeCode-trans w' w (EvalFun (cons (mkSigma key w) nil) key)
                   cw' cu c-ef le le-refl
      c-vu' = mkCFT cv cw' nbw' tt tt
  in EvalRel-down M rho sg (FunEl (cons (mkSigma key w') nil)) crho c-vu' evM (mkSigma le-u'-ef tt)

-- the key-lowering / value-lowering of a level body
LBody-down : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) ->
  (dn : (k : Nat) (x x' : FinEl) -> Coherent x' -> EvalRel X (extL rho (ldecT T k)) x ->
          LeCode x' x -> EvalRel X (extL rho (ldecT T k)) x') ->
  (u0 v0 u v : FinEl) -> Coherent u0 -> Coherent u -> Coherent v ->
  LeCode u0 u -> LeCode v v0 -> LBody X rho u0 v0 -> LBody X rho u v
LBody-down X rho dn u0 v0 u v cu0 cu cv le-u le-v (inl l0) =
  inl (Eq-transport (LeCode v) (leBot-eq v0 l0) le-v)
LBody-down X rho dn u0 v0 u v cu0 cu cv le-u le-v (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) =
  inr (mkSigma k (mkSigma ck (mkSigma (LeCode-trans (LevEl k) u0 u tt cu0 cu lk le-u) (dn k v0 v cv e le-v))))

-- a selection-wise level body, lowered along f' <= f
LBody-sel-down : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) ->
  (dn : (k : Nat) (x x' : FinEl) -> Coherent x' -> EvalRel X (extL rho (ldecT T k)) x ->
          LeCode x' x -> EvalRel X (extL rho (ldecT T k)) x') ->
  (f f' : FinFun) -> CoherentFunTail f -> CoherentFunTail f' -> LeFunCode f' f ->
  ((u v : FinEl) -> Selection f u v -> LBody X rho u v) ->
  (u v : FinEl) -> Selection f' u v -> LBody X rho u v
LBody-sel-down X rho dn f f' cf cf' le body u v sel =
  let cu  = Coherent-Selection sel cf'
      cv  = Coherent-Selection-val sel cf'
      le-v-ef' = Selection-le-EvalFun f' sel (LeFunCode-refl f' cf') cf' cf' cu
      le-ef'-ef = EvalFun-mon f' f u cf' cf cu le
      le-v-efu = LeCode-trans v (EvalFun f' u) (EvalFun f u)
                   cv (Coherent-EvalFun f' u cf' cu) (Coherent-EvalFun f u cf cu) le-v-ef' le-ef'-ef
      sb     = selectionBelow f u cf cu
      u0     = fst sb
      v0     = fst (snd sb)
      sel-f  = fst (snd (snd sb))
      le-u0  = fst (snd (snd (snd sb)))
      eq-v0  = snd (snd (snd (snd sb)))
      le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-efu
  in LBody-down X rho dn u0 v0 u v (Coherent-Selection sel-f cf) cu cv le-u0 le-v-v0 (body u0 v0 sel-f)

EvalRel-down (Grd c A) rho u u' crho cu' ev le =
  guard-down (\ x x' cx' e l -> EvalRel-down A rho x x' crho cx' e l) u u' cu' ev le
EvalRel-down (GLam c t) rho u u' crho cu' ev le =
  guard-down (\ x x' cx' e l -> EvalRel-down t rho x x' crho cx' e l) u u' cu' ev le
EvalRel-down Emp rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u Bot cu' (fst ev) tt le (snd ev))
EvalRel-down (Var i) rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u (lookupEnv i rho)
    cu' (fst ev) (lookupEnv-coh i rho crho) le (snd ev))
EvalRel-down {T = T} {θ = θ} (U l) rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u (UCode (lcodeT T (lsubL θ l))) cu' (fst ev) tt le (snd ev))
EvalRel-down (App M N) rho u u' crho cu' ev le =
  nbody-down {X = AppX M N rho} u u' (\ nw nw' e ->
    mkSigma (fst e) (mkSigma (fst (snd e)) (single-down M rho (fst e) u u' crho cu' nw' le (snd (snd e)))))
    ev le
EvalRel-down {T = T} {θ = θ} (LApp t l) rho u u' crho cu' ev le =
  nbody-down {X = LAppX t l rho} u u' (\ nw nw' e -> single-down t rho _ u u' crho cu' nw' le e) ev le
-- Lam
EvalRel-down (Lam A M) rho u Bot crho cu' ev le = tt
EvalRel-down (Lam A M) rho Bot (UCode _) crho cu' ev ()
EvalRel-down (Lam A M) rho Bot LevTy crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (LevEl _) crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (FunEl _) crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (PiCode _ _) crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (LPiCode _) crho cu' ev ()
EvalRel-down (Lam A M) rho (UCode _) u' crho cu' () le
EvalRel-down (Lam A M) rho LevTy u' crho cu' () le
EvalRel-down (Lam A M) rho (LevEl _) u' crho cu' () le
EvalRel-down (Lam A M) rho (PiCode _ _) u' crho cu' () le
EvalRel-down (Lam A M) rho (LPiCode _) u' crho cu' () le
EvalRel-down (Lam A M) rho (FunEl g) (UCode _) crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) LevTy crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (LevEl _) crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (PiCode _ _) crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (LPiCode _) crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (FunEl g') crho cu' ev le =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
      cg'  = cu'
      ctg' = cft-from-cf g' cg'
      ctg  = cft-from-cf g cg
  in mkSigma a (mkSigma cg' (mkSigma aU (mkSigma evA
       (\ u v sel ->
          let cu  = Coherent-Selection sel ctg'
              cv  = Coherent-Selection-val sel ctg'
              lf-g' = LeCode-refl (FunEl g') cg'
              le-v-efg' = Selection-le-EvalFun g' sel lf-g' ctg' ctg' cu
              le-efg'-efg = EvalFun-mon g' g u ctg' ctg cu le
              c-efg'u = Coherent-EvalFun g' u ctg' cu
              c-efgu  = Coherent-EvalFun g u ctg cu
              le-v-efgu = LeCode-trans v (EvalFun g' u) (EvalFun g u)
                            cv c-efg'u c-efgu le-v-efg' le-efg'-efg
              sb     = selectionBelow g u ctg cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-g  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              w      = body u0 v0 sel-g
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x  = fst (snd (snd w))
              evM-v0 = snd (snd (snd w))
              cx     = FinMem-coh-u x a mem-x
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-g ctg) cu le-x-u0 le-u0
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-efgu
              cx-env = mkSigma crho cx
              evM-v  = EvalRel-down M (extendEnv rho x) v0 v cx-env cv evM-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x evM-v))))))
-- Pi
EvalRel-down (Pi A B) rho u Bot crho cu' ev le = tt
EvalRel-down (Pi A B) rho Bot (UCode _) crho cu' ev ()
EvalRel-down (Pi A B) rho Bot LevTy crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (LevEl _) crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (FunEl _) crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (PiCode _ _) crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (LPiCode _) crho cu' ev ()
EvalRel-down (Pi A B) rho (UCode _) u' crho cu' () le
EvalRel-down (Pi A B) rho LevTy u' crho cu' () le
EvalRel-down (Pi A B) rho (LevEl _) u' crho cu' () le
EvalRel-down (Pi A B) rho (FunEl _) u' crho cu' () le
EvalRel-down (Pi A B) rho (LPiCode _) u' crho cu' () le
EvalRel-down (Pi A B) rho (PiCode a f) (UCode _) crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) LevTy crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (LevEl _) crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (FunEl _) crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (LPiCode _) crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (PiCode a' f') crho cu' ev le =
  let caf  = fst ev
      evA  = fst (snd ev)
      a0   = fst (snd (snd ev))
      evA0 = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
      le-a = fst le
      le-f = snd le
      ca'  = fst cu'
      cf'  = snd cu'
      cf-orig = snd caf
  in mkSigma cu' (mkSigma
       (EvalRel-down A rho a a' crho ca' evA le-a)
       (mkSigma a0 (mkSigma evA0
       (\ u v sel ->
          let cu  = Coherent-Selection sel cf'
              cv  = Coherent-Selection-val sel cf'
              lf-f' = LeFunCode-refl f' cf'
              le-v-eff' = Selection-le-EvalFun f' sel lf-f' cf' cf' cu
              le-eff'-eff = EvalFun-mon f' f u cf' cf-orig cu le-f
              c-eff'u = Coherent-EvalFun f' u cf' cu
              c-effu  = Coherent-EvalFun f u cf-orig cu
              le-v-effu = LeCode-trans v (EvalFun f' u) (EvalFun f u)
                            cv c-eff'u c-effu le-v-eff' le-eff'-eff
              sb     = selectionBelow f u cf-orig cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              w      = body u0 v0 sel-f
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x-a0 = fst (snd (snd w))
              evB-v0 = snd (snd (snd w))
              cx     = FinMem-coh-u x a0 mem-x-a0
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-f cf-orig) cu le-x-u0 le-u0
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-effu
              cx-env = mkSigma crho cx
              evB-x-v = EvalRel-down B (extendEnv rho x) v0 v cx-env cv evB-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x-a0 evB-x-v))))))
-- LPi
EvalRel-down (LPi A) rho u Bot crho cu' ev le = tt
EvalRel-down (LPi A) rho Bot (UCode _) crho cu' ev ()
EvalRel-down (LPi A) rho Bot LevTy crho cu' ev ()
EvalRel-down (LPi A) rho Bot (LevEl _) crho cu' ev ()
EvalRel-down (LPi A) rho Bot (FunEl _) crho cu' ev ()
EvalRel-down (LPi A) rho Bot (PiCode _ _) crho cu' ev ()
EvalRel-down (LPi A) rho Bot (LPiCode _) crho cu' ev ()
EvalRel-down (LPi A) rho (UCode _) u' crho cu' () le
EvalRel-down (LPi A) rho LevTy u' crho cu' () le
EvalRel-down (LPi A) rho (LevEl _) u' crho cu' () le
EvalRel-down (LPi A) rho (FunEl _) u' crho cu' () le
EvalRel-down (LPi A) rho (PiCode _ _) u' crho cu' () le
EvalRel-down (LPi A) rho (LPiCode f) (UCode _) crho cu' ev ()
EvalRel-down (LPi A) rho (LPiCode f) LevTy crho cu' ev ()
EvalRel-down (LPi A) rho (LPiCode f) (LevEl _) crho cu' ev ()
EvalRel-down (LPi A) rho (LPiCode f) (FunEl _) crho cu' ev ()
EvalRel-down (LPi A) rho (LPiCode f) (PiCode _ _) crho cu' ev ()
EvalRel-down {T = T} (LPi A) rho (LPiCode f) (LPiCode f') crho cu' ev le =
  mkSigma cu' (LBody-sel-down A rho
    (\ k x x' cx' e l -> EvalRel-down A (extL rho (ldecT T k)) x x' (CoherentEnv-reidx rho crho) cx' e l)
    f f' (fst ev) cu' le (snd ev))
-- LLam
EvalRel-down (LLam M) rho u Bot crho cu' ev le = tt
EvalRel-down (LLam M) rho Bot (UCode _) crho cu' ev ()
EvalRel-down (LLam M) rho Bot LevTy crho cu' ev ()
EvalRel-down (LLam M) rho Bot (LevEl _) crho cu' ev ()
EvalRel-down (LLam M) rho Bot (FunEl _) crho cu' ev ()
EvalRel-down (LLam M) rho Bot (PiCode _ _) crho cu' ev ()
EvalRel-down (LLam M) rho Bot (LPiCode _) crho cu' ev ()
EvalRel-down (LLam M) rho (UCode _) u' crho cu' () le
EvalRel-down (LLam M) rho LevTy u' crho cu' () le
EvalRel-down (LLam M) rho (LevEl _) u' crho cu' () le
EvalRel-down (LLam M) rho (PiCode _ _) u' crho cu' () le
EvalRel-down (LLam M) rho (LPiCode _) u' crho cu' () le
EvalRel-down (LLam M) rho (FunEl g) (UCode _) crho cu' ev ()
EvalRel-down (LLam M) rho (FunEl g) LevTy crho cu' ev ()
EvalRel-down (LLam M) rho (FunEl g) (LevEl _) crho cu' ev ()
EvalRel-down (LLam M) rho (FunEl g) (PiCode _ _) crho cu' ev ()
EvalRel-down (LLam M) rho (FunEl g) (LPiCode _) crho cu' ev ()
EvalRel-down {T = T} (LLam M) rho (FunEl g) (FunEl g') crho cu' ev le =
  mkSigma cu' (LBody-sel-down M rho
    (\ k x x' cx' e l -> EvalRel-down M (extL rho (ldecT T k)) x x' (CoherentEnv-reidx rho crho) cx' e l)
    g g' (cft-from-cf g (fst ev)) (cft-from-cf g' cu') le (snd ev))

------------------------------------------------------------------------
-- EvalRel-Sup: supremum closure of the evaluation relation.
------------------------------------------------------------------------

EvalRel-Sup : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n)
  (u v : FinEl) -> CoherentEnv rho -> Coherent u -> Coherent v ->
  Comp u v ->
  EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)

-- joining two singleton graphs of M
single-join : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) -> CoherentEnv rho ->
  (v1 v2 u w : FinEl) -> Comp v1 v2 -> Comp u w -> NotBot u ->
  EvalRel M rho (FunEl (cons (mkSigma v1 u) nil)) ->
  EvalRel M rho (FunEl (cons (mkSigma v2 w) nil)) ->
  EvalRel M rho (FunEl (cons (mkSigma (Sup v1 v2) (Sup u w)) nil))
single-join M rho crho v1 v2 u w comp-v comp nu evM1 evM2 =
  let s1   = FunEl (cons (mkSigma v1 u) nil)
      s2   = FunEl (cons (mkSigma v2 w) nil)
      cM1  = EvalRel-coh M rho s1 evM1
      cM2  = EvalRel-coh M rho s2 evM2
      cv1  = Coherent-singleton-key v1 u cM1
      cv2  = Coherent-singleton-key v2 w cM2
      cu   = Coherent-singleton-val v1 u cM1
      cw   = Coherent-singleton-val v2 w cM2
      comp-M = EvalRel-Comp M rho crho s1 s2 evM1 evM2
      evM-2 = EvalRel-Sup M rho s1 s2 crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup s1 s2 comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup u w comp cu cw
      le-down = LeFunCode-Sup-pair v1 u v2 w comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val (NotBot-Sup-Comp u w nu comp) tt tt
  in EvalRel-down M rho
       (FunEl (cons (mkSigma v1 u) (cons (mkSigma v2 w) nil)))
       (FunEl (cons (mkSigma (Sup v1 v2) (Sup u w)) nil))
       crho c-singleton evM-2 le-down

-- the join of two level bodies
LBody-join : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) ->
  (ihc : (k : Nat) (x y : FinEl) -> EvalRel X (extL rho (ldecT T k)) x ->
          EvalRel X (extL rho (ldecT T k)) y -> Comp x y) ->
  (ihs : (k : Nat) (x y : FinEl) -> Coherent x -> Coherent y -> Comp x y ->
          EvalRel X (extL rho (ldecT T k)) x -> EvalRel X (extL rho (ldecT T k)) y ->
          EvalRel X (extL rho (ldecT T k)) (Sup x y)) ->
  (dn : (k : Nat) (x x' : FinEl) -> Coherent x' -> EvalRel X (extL rho (ldecT T k)) x ->
          LeCode x' x -> EvalRel X (extL rho (ldecT T k)) x') ->
  (u1 v1 u2 v2 u v : FinEl) -> Coherent u1 -> Coherent u2 -> Coherent u -> Coherent v ->
  Coherent v1 -> Coherent v2 ->
  LeCode u1 u -> LeCode u2 u -> LeCode v (Sup v1 v2) ->
  LBody X rho u1 v1 -> LBody X rho u2 v2 -> LBody X rho u v
LBody-join X rho ihc ihs dn u1 v1 u2 v2 u v cu1 cu2 cu cv cv1 cv2 l1 l2 lv (inl b1) (inl b2) =
  inl (bb v1 v2 (leBot-eq v1 b1) (leBot-eq v2 b2) lv)
  where
    bb : (a b : FinEl) -> Eq a Bot -> Eq b Bot -> LeCode v (Sup a b) -> LeCode v Bot
    bb .Bot .Bot refl refl l = l
LBody-join X rho ihc ihs dn u1 v1 u2 v2 u v cu1 cu2 cu cv cv1 cv2 l1 l2 lv (inl b1) (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) =
  inr (mkSigma k (mkSigma ck (mkSigma (LeCode-trans (LevEl k) u2 u tt cu2 cu lk l2)
    (dn k v2 v cv e (bl v1 (leBot-eq v1 b1) lv)))))
  where
    bl : (a : FinEl) -> Eq a Bot -> LeCode v (Sup a v2) -> LeCode v v2
    bl .Bot refl l = l
LBody-join X rho ihc ihs dn u1 v1 u2 v2 u v cu1 cu2 cu cv cv1 cv2 l1 l2 lv (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) (inl b2) =
  inr (mkSigma k (mkSigma ck (mkSigma (LeCode-trans (LevEl k) u1 u tt cu1 cu lk l1)
    (dn k v1 v cv e (br v2 (leBot-eq v2 b2) lv)))))
  where
    br : (b : FinEl) -> Eq b Bot -> LeCode v (Sup v1 b) -> LeCode v v1
    br .Bot refl l = Eq-transport (LeCode v) (Sup-Bot-r v1) l
LBody-join {T = T} X rho ihc ihs dn u1 v1 u2 v2 u v cu1 cu2 cu cv cv1 cv2 l1 l2 lv
  (inr (mkSigma k1 (mkSigma ck1 (mkSigma lk1 e1)))) (inr (mkSigma k2 (mkSigma ck2 (mkSigma lk2 e2)))) =
  let lk1u = LeCode-trans (LevEl k1) u1 u tt cu1 cu lk1 l1
      lk2u = LeCode-trans (LevEl k2) u2 u tt cu2 cu lk2 l2
      eq   = levLe-same k2 k1 u cu lk2u lk1u
      e2'  = Eq-transport (\ k -> EvalRel X (extL rho (ldecT T k)) v2) eq e2
      c12  = ihc k1 v1 v2 e1 e2'
      es   = ihs k1 v1 v2 cv1 cv2 c12 e1 e2'
  in inr (mkSigma k1 (mkSigma ck1 (mkSigma lk1u (dn k1 (Sup v1 v2) v cv es lv))))

-- the selection-wise body of a join of two level graphs
LBody-sel-join : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) ->
  (ihc : (k : Nat) (x y : FinEl) -> EvalRel X (extL rho (ldecT T k)) x ->
          EvalRel X (extL rho (ldecT T k)) y -> Comp x y) ->
  (ihs : (k : Nat) (x y : FinEl) -> Coherent x -> Coherent y -> Comp x y ->
          EvalRel X (extL rho (ldecT T k)) x -> EvalRel X (extL rho (ldecT T k)) y ->
          EvalRel X (extL rho (ldecT T k)) (Sup x y)) ->
  (dn : (k : Nat) (x x' : FinEl) -> Coherent x' -> EvalRel X (extL rho (ldecT T k)) x ->
          LeCode x' x -> EvalRel X (extL rho (ldecT T k)) x') ->
  (f1 f2 : FinFun) -> CoherentFunTail f1 -> CoherentFunTail f2 -> CompFun f1 f2 ->
  ((u v : FinEl) -> Selection f1 u v -> LBody X rho u v) ->
  ((u v : FinEl) -> Selection f2 u v -> LBody X rho u v) ->
  (u v : FinEl) -> Selection (append f1 f2) u v -> LBody X rho u v
LBody-sel-join X rho ihc ihs dn f1 f2 cf1 cf2 comp-f body1 body2 u v sel =
  let c-fab  = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
      cu-sel = Coherent-Selection sel c-fab
      cv-sel = Coherent-Selection-val sel c-fab
      sb1    = selectionBelow f1 u cf1 cu-sel
      u1     = fst sb1
      v1     = fst (snd sb1)
      sel1   = fst (snd (snd sb1))
      le-u1  = fst (snd (snd (snd sb1)))
      eq-v1  = snd (snd (snd (snd sb1)))
      sb2    = selectionBelow f2 u cf2 cu-sel
      u2     = fst sb2
      v2     = fst (snd sb2)
      sel2   = fst (snd (snd sb2))
      le-u2  = fst (snd (snd (snd sb2)))
      eq-v2  = snd (snd (snd (snd sb2)))
      lf-fab = LeFunCode-refl (append f1 f2) c-fab
      le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-fab c-fab c-fab cu-sel
      eq-ef  = EvalFun-append-eq f1 f2 u comp-f cf1 cu-sel
      le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
      eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun f2 u)) (Sup v1 v2))
                 (Eq-sym eq-v1)
                 (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                   (Eq-sym eq-v2) refl)
      le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
  in LBody-join X rho ihc ihs dn u1 v1 u2 v2 u v
       (Coherent-Selection sel1 cf1) (Coherent-Selection sel2 cf2) cu-sel cv-sel
       (Coherent-Selection-val sel1 cf1) (Coherent-Selection-val sel2 cf2)
       le-u1 le-u2 le-v-supv (body1 u1 v1 sel1) (body2 u2 v2 sel2)

EvalRel-Sup (Grd c A) rho u v crho cu cv comp eu ev =
  guard-Sup u v (EvalRel-Sup A rho u v crho cu cv comp) eu ev
EvalRel-Sup (GLam c t) rho u v crho cu cv comp eu ev =
  guard-Sup u v (EvalRel-Sup t rho u v crho cu cv comp) eu ev
EvalRel-Sup Emp rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v Bot (snd eu) (snd ev))
EvalRel-Sup (Var i) rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv)
          (LeCode-Sup-lub u v (lookupEnv i rho) (snd eu) (snd ev))
EvalRel-Sup {T = T} {θ = θ} (U l) rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v (UCode (lcodeT T (lsubL θ l))) (snd eu) (snd ev))
EvalRel-Sup (App M N) rho u v crho cu cv comp eu ev =
  nbody-Sup {X = AppX M N rho} (\ u w nu nw c e1 e2 ->
    let v1   = fst e1
        evN1 = fst (snd e1)
        v2   = fst e2
        evN2 = fst (snd e2)
        cv1  = EvalRel-coh N rho v1 evN1
        cv2  = EvalRel-coh N rho v2 evN2
        comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
    in mkSigma (Sup v1 v2)
         (mkSigma (EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2)
                  (single-join M rho crho v1 v2 u w comp-v c nu (snd (snd e1)) (snd (snd e2)))))
    NotBot-Sup-Comp u v comp eu ev
EvalRel-Sup {T = T} {θ = θ} (LApp t l) rho u v crho cu cv comp eu ev =
  nbody-Sup {X = LAppX t l rho} (\ u w nu nw c e1 e2 ->
    single-join t rho crho (LevEl (lcodeT T (lsubL θ l))) (LevEl (lcodeT T (lsubL θ l))) u w
      (EqL-refl (lcodeT T (lsubL θ l))) c nu e1 e2)
    NotBot-Sup-Comp u v comp eu ev
-- Lam
EvalRel-Sup (Lam A M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Lam A M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Lam A M) rho (UCode lu) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho LevTy v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (LevEl _) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (LPiCode f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (FunEl g1) (UCode lu) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) LevTy crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (LevEl _) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (LPiCode f2) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  let a1    = fst eu
      cg1   = fst (snd eu)
      a1U   = fst (snd (snd eu))
      evA1  = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      a2    = fst ev
      cg2   = fst (snd ev)
      a2U   = fst (snd (snd ev))
      evA2  = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      ca1   = EvalRel-coh A rho a1 evA1
      ca2   = EvalRel-coh A rho a2 evA2
      comp-a = EvalRel-Comp A rho crho a1 a2 evA1 evA2
      evA-sup = EvalRel-Sup A rho a1 a2 crho ca1 ca2 comp-a evA1 evA2
      c-sup-a = Coherent-Sup a1 a2 comp-a ca1 ca2
      supU = FinMem-Sup-element a1 a2 U0 comp-a tt a1U a2U
      c-gab = CoherentFun-append g1 g2 cg1 cg2 comp
      ct-gab = cft-from-cf (append g1 g2) c-gab
  in mkSigma (Sup a1 a2) (mkSigma c-gab (mkSigma supU (mkSigma evA-sup
       (\ u v sel ->
          let cu-sel = Coherent-Selection sel ct-gab
              cv-sel = Coherent-Selection-val sel ct-gab
              sb1    = selectionBelow g1 u (cft-from-cf g1 cg1) cu-sel
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow g2 u (cft-from-cf g2 cg2) cu-sel
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evM-x1 = snd (snd (snd w1))
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evM-x2 = snd (snd (snd w2))
              cx1    = FinMem-coh-u x1 a1 mem-x1
              cx2    = FinMem-coh-u x2 a2 mem-x2
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 (cft-from-cf g1 cg1)) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 (cft-from-cf g2 cg2)) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              le-a1-sup = LeCode-Sup-left a1 a2 comp-a ca1 ca2
              le-a2-sup = LeCode-Sup-right a1 a2 comp-a ca1 ca2
              mem-x1-sup = finMem-upward x1 a1 (Sup a1 a2) le-a1-sup ca1 c-sup-a mem-x1 supU
              mem-x2-sup = finMem-upward x2 a2 (Sup a1 a2) le-a2-sup ca2 c-sup-a mem-x2 supU
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1 a2) comp-x c-sup-a mem-x1-sup mem-x2-sup
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evM-sup1 = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evM-x1 envle1
              evM-sup2 = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evM-x2 envle2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evM-sup1 evM-sup2
              cv1    = EvalRel-coh M (extendEnv rho x1) v1 evM-x1
              cv2    = EvalRel-coh M (extendEnv rho x2) v2 evM-x2
              evM-supv = EvalRel-Sup M (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evM-sup1 evM-sup2
              lf-gab = LeFunCode-refl (append g1 g2) ct-gab
              le-v-ef = Selection-le-EvalFun (append g1 g2) sel lf-gab ct-gab ct-gab cu-sel
              ctg1   = cft-from-cf g1 cg1
              eq-ef  = EvalFun-append-eq g1 g2 u comp ctg1 cu-sel
              le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
              eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun g2 u)) (Sup v1 v2))
                         (Eq-sym eq-v1)
                         (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                           (Eq-sym eq-v2) refl)
              le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
              evM-v  = EvalRel-down M (extendEnv rho (Sup x1 x2)) (Sup v1 v2) v crho-sup cv-sel evM-supv le-v-supv
          in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evM-v))))))
-- Pi
EvalRel-Sup (Pi A B) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Pi A B) rho (UCode lu) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho LevTy v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (LevEl _) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (LPiCode g1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (UCode lu) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) LevTy crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (LevEl _) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (FunEl g2) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (LPiCode g2) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  let cu1   = fst eu
      evA1  = fst (snd eu)
      a1'   = fst (snd (snd eu))
      evA1' = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      cu2   = fst ev
      evA2  = fst (snd ev)
      a2'   = fst (snd (snd ev))
      evA2' = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      ca1   = EvalRel-coh A rho a1 evA1
      ca2   = EvalRel-coh A rho a2 evA2
      ca1'  = EvalRel-coh A rho a1' evA1'
      ca2'  = EvalRel-coh A rho a2' evA2'
      comp-a = fst comp
      comp-f = snd comp
      comp-a' = EvalRel-Comp A rho crho a1' a2' evA1' evA2'
      evA-sup = EvalRel-Sup A rho a1 a2 crho ca1 ca2 comp-a evA1 evA2
      evA'-sup = EvalRel-Sup A rho a1' a2' crho ca1' ca2' comp-a' evA1' evA2'
      c-sup-a' = Coherent-Sup a1' a2' comp-a' ca1' ca2'
      c-result = Coherent-Sup (PiCode a1 f1) (PiCode a2 f2) comp cu cv
      cf1   = snd cu1
      cf2   = snd cu2
      c-fab = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
  in mkSigma c-result (mkSigma evA-sup
       (mkSigma (Sup a1' a2') (mkSigma evA'-sup
       (\ u v sel ->
          let cu-sel = Coherent-Selection sel c-fab
              cv-sel = Coherent-Selection-val sel c-fab
              sb1    = selectionBelow f1 u cf1 cu-sel
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u cf2 cu-sel
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evB-x1 = snd (snd (snd w1))
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evB-x2 = snd (snd (snd w2))
              cx1    = FinMem-coh-u x1 a1' mem-x1
              cx2    = FinMem-coh-u x2 a2' mem-x2
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 cf1) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 cf2) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              le-a1'-sup = LeCode-Sup-left a1' a2' comp-a' ca1' ca2'
              le-a2'-sup = LeCode-Sup-right a1' a2' comp-a' ca1' ca2'
              supU-a' = FinMem-a-in-U x1 a1' mem-x1
              supU-a'' = FinMem-a-in-U x2 a2' mem-x2
              supU-result = FinMem-Sup-element a1' a2' U0 comp-a' tt supU-a' supU-a''
              mem-x1-sup = finMem-upward x1 a1' (Sup a1' a2') le-a1'-sup ca1' c-sup-a' mem-x1 supU-result
              mem-x2-sup = finMem-upward x2 a2' (Sup a1' a2') le-a2'-sup ca2' c-sup-a' mem-x2 supU-result
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1' a2') comp-x c-sup-a' mem-x1-sup mem-x2-sup
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evB-sup1 = EvalRel-mon-env B (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evB-x1 envle1
              evB-sup2 = EvalRel-mon-env B (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evB-x2 envle2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp B (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evB-sup1 evB-sup2
              cv1    = EvalRel-coh B (extendEnv rho x1) v1 evB-x1
              cv2    = EvalRel-coh B (extendEnv rho x2) v2 evB-x2
              evB-supv = EvalRel-Sup B (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evB-sup1 evB-sup2
              lf-fab = LeFunCode-refl (append f1 f2) c-fab
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-fab c-fab c-fab cu-sel
              eq-ef  = EvalFun-append-eq f1 f2 u comp-f cf1 cu-sel
              le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
              eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun f2 u)) (Sup v1 v2))
                         (Eq-sym eq-v1)
                         (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                           (Eq-sym eq-v2) refl)
              le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
              evB-v  = EvalRel-down B (extendEnv rho (Sup x1 x2)) (Sup v1 v2) v crho-sup cv-sel evB-supv le-v-supv
          in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evB-v))))))
-- LPi
EvalRel-Sup (LPi A) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (LPi A) rho (LPiCode f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (LPi A) rho (UCode lu) v crho cu cv comp () ev
EvalRel-Sup (LPi A) rho LevTy v crho cu cv comp () ev
EvalRel-Sup (LPi A) rho (LevEl _) v crho cu cv comp () ev
EvalRel-Sup (LPi A) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (LPi A) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (LPi A) rho (LPiCode f1) (UCode lu) crho cu cv comp eu ()
EvalRel-Sup (LPi A) rho (LPiCode f1) LevTy crho cu cv comp eu ()
EvalRel-Sup (LPi A) rho (LPiCode f1) (LevEl _) crho cu cv comp eu ()
EvalRel-Sup (LPi A) rho (LPiCode f1) (FunEl g2) crho cu cv comp eu ()
EvalRel-Sup (LPi A) rho (LPiCode f1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup {T = T} (LPi A) rho (LPiCode f1) (LPiCode f2) crho cu cv comp eu ev =
  mkSigma (Coherent-Sup (LPiCode f1) (LPiCode f2) comp cu cv)
       (LBody-sel-join A rho
         (\ k x y e1 e2 -> EvalRel-Comp A (extL rho (ldecT T k)) (CoherentEnv-reidx rho crho) x y e1 e2)
         (\ k x y cx cy c e1 e2 -> EvalRel-Sup A (extL rho (ldecT T k)) x y (CoherentEnv-reidx rho crho) cx cy c e1 e2)
         (\ k x x' cx' e l -> EvalRel-down A (extL rho (ldecT T k)) x x' (CoherentEnv-reidx rho crho) cx' e l)
         f1 f2 cu cv comp (snd eu) (snd ev))
-- LLam
EvalRel-Sup (LLam M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (LLam M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (LLam M) rho (UCode lu) v crho cu cv comp () ev
EvalRel-Sup (LLam M) rho LevTy v crho cu cv comp () ev
EvalRel-Sup (LLam M) rho (LevEl _) v crho cu cv comp () ev
EvalRel-Sup (LLam M) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (LLam M) rho (LPiCode f1) v crho cu cv comp () ev
EvalRel-Sup (LLam M) rho (FunEl g1) (UCode lu) crho cu cv comp eu ()
EvalRel-Sup (LLam M) rho (FunEl g1) LevTy crho cu cv comp eu ()
EvalRel-Sup (LLam M) rho (FunEl g1) (LevEl _) crho cu cv comp eu ()
EvalRel-Sup (LLam M) rho (FunEl g1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (LLam M) rho (FunEl g1) (LPiCode f2) crho cu cv comp eu ()
EvalRel-Sup {T = T} (LLam M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  mkSigma (CoherentFun-append g1 g2 cu cv comp)
       (LBody-sel-join M rho
         (\ k x y e1 e2 -> EvalRel-Comp M (extL rho (ldecT T k)) (CoherentEnv-reidx rho crho) x y e1 e2)
         (\ k x y cx cy c e1 e2 -> EvalRel-Sup M (extL rho (ldecT T k)) x y (CoherentEnv-reidx rho crho) cx cy c e1 e2)
         (\ k x x' cx' e l -> EvalRel-down M (extL rho (ldecT T k)) x x' (CoherentEnv-reidx rho crho) cx' e l)
         g1 g2 (cft-from-cf g1 cu) (cft-from-cf g2 cv) comp (snd eu) (snd ev))

------------------------------------------------------------------------
-- Level bodies from edges
------------------------------------------------------------------------

LBody-from-edges : {n : Nat} (X : Expr n) (rho : EnvApprox T θ n) -> CoherentEnv rho ->
  (g : FinFun) -> CoherentFunTail g -> LEdges X rho g ->
  (u v : FinEl) -> Selection g u v -> LBody X rho u v
LBody-from-edges X rho crho .nil cg e .Bot .Bot sel-nil = inl tt
LBody-from-edges X rho crho (cons p g) cg e u v (sel-skip sel) =
  LBody-from-edges X rho crho g (CFTcons.tail-coh cg) (\ q ein -> e q (there ein)) u v sel
LBody-from-edges {T = T} X rho crho (cons p g) cg e .(Sup (fst p) u0) .(Sup (snd p) v0)
  (sel-take {.p} {u0} {v0} ck cv sel) =
  let rec  = LBody-from-edges X rho crho g (CFTcons.tail-coh cg) (\ q ein -> e q (there ein)) u0 v0 sel
      cp   = CFTcons.key-coh cg
      cvp  = CFTcons.val-coh cg
      cu0  = Coherent-Selection sel (CFTcons.tail-coh cg)
      cv0  = Coherent-Selection-val sel (CFTcons.tail-coh cg)
      cS   = Coherent-Sup (fst p) u0 ck cp cu0
      cSv  = Coherent-Sup (snd p) v0 cv cvp cv0
  in LBody-join X rho
       (\ k x y e1 e2 -> EvalRel-Comp X (extL rho (ldecT T k)) (CoherentEnv-reidx rho crho) x y e1 e2)
       (\ k x y cx cy c e1 e2 -> EvalRel-Sup X (extL rho (ldecT T k)) x y (CoherentEnv-reidx rho crho) cx cy c e1 e2)
       (\ k x x' cx' e1 l -> EvalRel-down X (extL rho (ldecT T k)) x x' (CoherentEnv-reidx rho crho) cx' e1 l)
       (fst p) (snd p) u0 v0 (Sup (fst p) u0) (Sup (snd p) v0) cp cu0 cS cSv cvp cv0
       (LeCode-Sup-left (fst p) u0 ck cp cu0) (LeCode-Sup-right (fst p) u0 ck cp cu0)
       (LeCode-refl (Sup (snd p) v0) cSv)
       (e p here) rec

------------------------------------------------------------------------
-- EvalRel-Comp-ext / EvalRel-ideal-Comp
------------------------------------------------------------------------

EvalRel-Comp-ext : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox T θ n)
  (x1 x2 y1 y2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) y1 ->
  EvalRel M (extendEnv rho x2) y2 ->
  Comp y1 y2
EvalRel-Comp-ext M rho x1 x2 y1 y2 crho comp cx1 cx2 ev1 ev2 =
  let envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1'   = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2))
                 y1 ev1 envle1
      ev2'   = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2))
                 y2 ev2 envle2
      c-sup  = Coherent-Sup x1 x2 comp cx1 cx2
      crho'  = mkSigma crho c-sup
  in EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho' y1 y2 ev1' ev2'

EvalRel-ideal-Comp : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox T θ n)
  (x1 x2 y1 y2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) y1 ->
  EvalRel M (extendEnv rho x2) y2 ->
  EvalRel M (extendEnv rho (Sup x1 x2)) (Sup y1 y2)
EvalRel-ideal-Comp M rho x1 x2 y1 y2 crho comp cx1 cx2 ev1 ev2 =
  let envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1'   = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2))
                 y1 ev1 envle1
      ev2'   = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2))
                 y2 ev2 envle2
      c-sup  = Coherent-Sup x1 x2 comp cx1 cx2
      crho'  = mkSigma crho c-sup
      cy1    = EvalRel-coh M (extendEnv rho (Sup x1 x2)) y1 ev1'
      cy2    = EvalRel-coh M (extendEnv rho (Sup x1 x2)) y2 ev2'
      comp-y = EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho' y1 y2 ev1' ev2'
  in EvalRel-Sup M (extendEnv rho (Sup x1 x2)) y1 y2 crho' cy1 cy2 comp-y ev1' ev2'
