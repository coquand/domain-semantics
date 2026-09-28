{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.EvalLevel
--
-- Evaluation and the level environment:
--
--   * reidx / SameEnv  : the same term values under another level
--                         environment;
--   * EvalRel-lsub2    : EvalRel (lsubE z1 M) rho -> EvalRel (lsubE z2 M) rho'
--                         when θ∘z1 and θ'∘z2 are pointwise T-equal;
--   * corollaries      : level substitution (both directions), invariance
--                         under pointwise T-equal level environments,
--                         instantiation lsub1, the shift lshiftE.
--
-- 0 postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)

module BCDE4.Model.EvalLevel (D : LDecAll) where

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent)
open import BCDE4.Model.Core
open import BCDE4.Levels using (LCtx ; LSub ; LExpr ; Valid ; ValidC ; LDec ; Constr ; ceq ;
  lvar ; lsup ; lnext ;
  v-refl ; v-sym ; v-trans ; v-sup ; v-next ;
  lsubL ; lsubC ; lconsS ; lidS ; lwkS ; lshift ; liftL ; lsub1S ; lcomp ;
  lsubL-comp ; lsubC-comp ; lsubL-id)
open import BCDE4.Model.Guard
open import BCDE4.Basic using (Either ; inl ; inr)
open import BCDE4.Model.Eval D

private variable
  T : LCtx
  θ θ' : LSub

------------------------------------------------------------------------
-- Same term values
------------------------------------------------------------------------

SameEnv : {n : Nat} -> EnvApprox T θ n -> EnvApprox T θ' n -> Set
SameEnv emptyEnv emptyEnv = Top
SameEnv (extendEnv r x) (extendEnv r' x') = Pair (SameEnv r r') (Eq x x')

SameEnv-refl : {n : Nat} (rho : EnvApprox T θ n) -> SameEnv rho rho
SameEnv-refl emptyEnv = tt
SameEnv-refl (extendEnv rho x) = mkSigma (SameEnv-refl rho) refl

SameEnv-sym : {n : Nat} (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> SameEnv rho' rho
SameEnv-sym emptyEnv emptyEnv s = tt
SameEnv-sym (extendEnv r x) (extendEnv r' x') s = mkSigma (SameEnv-sym r r' (fst s)) (Eq-sym (snd s))

SameEnv-reidx : {n : Nat} (rho : EnvApprox T θ n) -> SameEnv rho (reidx {θ' = θ'} rho)
SameEnv-reidx emptyEnv = tt
SameEnv-reidx (extendEnv rho x) = mkSigma (SameEnv-reidx rho) refl

SameEnv-reidx2 : {n : Nat} {θ1 θ2 : LSub} (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> SameEnv (reidx {θ' = θ1} rho) (reidx {θ' = θ2} rho')
SameEnv-reidx2 emptyEnv emptyEnv s = tt
SameEnv-reidx2 (extendEnv r x) (extendEnv r' x') s = mkSigma (SameEnv-reidx2 r r' (fst s)) (snd s)

SameEnv-rr : {n : Nat} {θ1 θ2 : LSub} (rho : EnvApprox T θ n) ->
  SameEnv rho (reidx {θ' = θ2} (reidx {θ' = θ1} rho))
SameEnv-rr emptyEnv = tt
SameEnv-rr (extendEnv rho x) = mkSigma (SameEnv-rr rho) refl

SameEnv-lookup : {n : Nat} (i : Fin n) (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> Eq (lookupEnv i rho) (lookupEnv i rho')
SameEnv-lookup fzero    (extendEnv r x) (extendEnv r' x') s = snd s
SameEnv-lookup (fsuc i) (extendEnv r x) (extendEnv r' x') s = SameEnv-lookup i r r' (fst s)

SameEnv-coh : {n : Nat} (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> CoherentEnv rho -> CoherentEnv rho'
SameEnv-coh emptyEnv emptyEnv s c = tt
SameEnv-coh (extendEnv r x) (extendEnv r' x') s c =
  mkSigma (SameEnv-coh r r' (fst s) (fst c)) (Eq-transport Coherent (snd s) (snd c))

------------------------------------------------------------------------
-- Pointwise T-equal level substitutions
------------------------------------------------------------------------

PwValid : LCtx -> LSub -> LSub -> Set
PwValid T z z' = (i : Nat) -> Valid T (z i) (z' i)

valid-lsubL-pw : {z z' : LSub} -> PwValid T z z' -> (l : LExpr) -> Valid T (lsubL z l) (lsubL z' l)
valid-lsubL-pw pw (lvar i)   = pw i
valid-lsubL-pw pw (lsup l m) = v-sup (valid-lsubL-pw pw l) (valid-lsubL-pw pw m)
valid-lsubL-pw pw (lnext l)  = v-next (valid-lsubL-pw pw l)

validC-pw : {z z' : LSub} -> PwValid T z z' -> (c : Constr) ->
  ValidC T (lsubC z c) -> ValidC T (lsubC z' c)
validC-pw pw (ceq l m) d = v-trans (v-sym (valid-lsubL-pw pw l)) (v-trans d (valid-lsubL-pw pw m))

-- the composed substitution θ ∘ z
compL : LSub -> LSub -> LSub
compL θ z i = lsubL θ (z i)

-- entering a level binder
pw-lift : {z1 z2 : LSub} (m : LExpr) -> PwValid T (compL θ z1) (compL θ' z2) ->
  PwValid T (compL (lconsS m θ) (liftL z1)) (compL (lconsS m θ') (liftL z2))
pw-lift m pw zero    = v-refl
pw-lift {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} m pw (suc j) =
  Eq-transport (\ a -> Valid _ a (lsubL (lconsS m θ') (lshift (z2 j))))
    (Eq-sym (lsubL-comp (lconsS m θ) lwkS (z1 j)))
    (Eq-transport (\ b -> Valid _ (lsubL θ (z1 j)) b)
      (Eq-sym (lsubL-comp (lconsS m θ') lwkS (z2 j))) (pw j))

private
  lcode-pw : {z1 z2 : LSub} -> PwValid T (compL θ z1) (compL θ' z2) -> (l : LExpr) ->
    Eq (lcodeT T (lsubL θ (lsubL z1 l))) (lcodeT T (lsubL θ' (lsubL z2 l)))
  lcode-pw {T = T} {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} pw l =
    LDec.lcode-sound (D T)
      (Eq-transport (\ a -> Valid T a (lsubL θ' (lsubL z2 l))) (Eq-sym (lsubL-comp θ z1 l))
        (Eq-transport (\ b -> Valid T (lsubL (compL θ z1) l) b) (Eq-sym (lsubL-comp θ' z2 l))
          (valid-lsubL-pw pw l)))

  guardV-pw : {z1 z2 : LSub} -> PwValid T (compL θ z1) (compL θ' z2) -> (c : Constr) ->
    ValidC T (lsubC θ (lsubC z1 c)) -> ValidC T (lsubC θ' (lsubC z2 c))
  guardV-pw {T = T} {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} pw c d =
    Eq-transport (ValidC T) (Eq-sym (lsubC-comp θ' z2 c))
      (validC-pw pw c (Eq-transport (ValidC T) (lsubC-comp θ z1 c) d))

------------------------------------------------------------------------
-- The main lemma
------------------------------------------------------------------------

EvalRel-lsub2 : {n : Nat} (z1 z2 : LSub) (M : Expr n)
  (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> PwValid T (compL θ z1) (compL θ' z2) ->
  (b : FinEl) -> EvalRel (lsubE z1 M) rho b -> EvalRel (lsubE z2 M) rho' b

LBody-lsub2 : {n : Nat} (z1 z2 : LSub) (X : Expr n)
  (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> PwValid T (compL θ z1) (compL θ' z2) ->
  (u v : FinEl) -> LBody (lsubE (liftL z1) X) rho u v -> LBody (lsubE (liftL z2) X) rho' u v
LBody-lsub2 z1 z2 X rho rho' s pw u v (inl le) = inl le
LBody-lsub2 {T = T} z1 z2 X rho rho' s pw u v (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) =
  inr (mkSigma k (mkSigma ck (mkSigma lk
    (EvalRel-lsub2 (liftL z1) (liftL z2) X (extL rho (ldecT T k)) (extL rho' (ldecT T k))
       (SameEnv-reidx2 rho rho' s) (pw-lift (ldecT T k) pw) v e))))

EvalRel-lsub2 z1 z2 (Var i) rho rho' s pw b ev =
  mkSigma (fst ev) (Eq-transport (LeCode b) (SameEnv-lookup i rho rho' s) (snd ev))
EvalRel-lsub2 {T = T} {θ = θ} {θ' = θ'} z1 z2 (U l) rho rho' s pw b ev =
  mkSigma (fst ev) (Eq-transport (\ c -> LeCode b (UCode c)) (lcode-pw {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} pw l) (snd ev))
EvalRel-lsub2 z1 z2 Emp rho rho' s pw b ev = ev
EvalRel-lsub2 z1 z2 (App M N) rho rho' s pw b ev =
  nbody-map b (\ e -> mkSigma (fst e) (mkSigma (EvalRel-lsub2 z1 z2 N rho rho' s pw (fst e) (fst (snd e)))
                                               (EvalRel-lsub2 z1 z2 M rho rho' s pw _ (snd (snd e))))) ev
EvalRel-lsub2 {T = T} {θ = θ} {θ' = θ'} z1 z2 (LApp t l) rho rho' s pw b ev =
  nbody-map b (\ e ->
    Eq-transport (\ c -> EvalRel (lsubE z2 t) rho' (FunEl (cons (mkSigma (LevEl c) b) nil)))
      (lcode-pw pw l)
      (EvalRel-lsub2 z1 z2 t rho rho' s pw _ e)) ev
EvalRel-lsub2 {θ = θ} {θ' = θ'} z1 z2 (Grd c A) rho rho' s pw b ev =
  guard-map (guardV-pw {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} pw c)
    (\ b' e -> EvalRel-lsub2 z1 z2 A rho rho' s pw b' e) b ev
EvalRel-lsub2 {θ = θ} {θ' = θ'} z1 z2 (GLam c t) rho rho' s pw b ev =
  guard-map (guardV-pw {θ = θ} {θ' = θ'} {z1 = z1} {z2 = z2} pw c)
    (\ b' e -> EvalRel-lsub2 z1 z2 t rho rho' s pw b' e) b ev
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw Bot ev = tt
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw (FunEl g) ev =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (mkSigma (fst (snd (snd ev)))
    (mkSigma (EvalRel-lsub2 z1 z2 A rho rho' s pw _ (fst (snd (snd (snd ev)))))
      (\ u v sel ->
        let w = snd (snd (snd (snd ev))) u v sel
        in mkSigma (fst w) (mkSigma (fst (snd w)) (mkSigma (fst (snd (snd w)))
             (EvalRel-lsub2 z1 z2 M (extendEnv rho (fst w)) (extendEnv rho' (fst w))
                (mkSigma s refl) pw v (snd (snd (snd w))))))))))
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw (UCode _) ()
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw LevTy ()
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw (LevEl _) ()
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw (PiCode _ _) ()
EvalRel-lsub2 z1 z2 (Lam A M) rho rho' s pw (LPiCode _) ()
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw Bot ev = tt
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw (PiCode a f) ev =
  mkSigma (fst ev) (mkSigma (EvalRel-lsub2 z1 z2 A rho rho' s pw a (fst (snd ev)))
    (mkSigma (fst (snd (snd ev))) (mkSigma (EvalRel-lsub2 z1 z2 A rho rho' s pw _ (fst (snd (snd (snd ev)))))
      (\ u v sel ->
        let w = snd (snd (snd (snd ev))) u v sel
        in mkSigma (fst w) (mkSigma (fst (snd w)) (mkSigma (fst (snd (snd w)))
             (EvalRel-lsub2 z1 z2 B (extendEnv rho (fst w)) (extendEnv rho' (fst w))
                (mkSigma s refl) pw v (snd (snd (snd w))))))))))
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw (UCode _) ()
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw LevTy ()
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw (LevEl _) ()
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw (FunEl _) ()
EvalRel-lsub2 z1 z2 (Pi A B) rho rho' s pw (LPiCode _) ()
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw Bot ev = tt
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw (LPiCode f) ev =
  mkSigma (fst ev) (\ u v sel -> LBody-lsub2 z1 z2 A rho rho' s pw u v (snd ev u v sel))
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw (UCode _) ()
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw LevTy ()
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw (LevEl _) ()
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw (FunEl _) ()
EvalRel-lsub2 z1 z2 (LPi A) rho rho' s pw (PiCode _ _) ()
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw Bot ev = tt
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw (FunEl g) ev =
  mkSigma (fst ev) (\ u v sel -> LBody-lsub2 z1 z2 M rho rho' s pw u v (snd ev u v sel))
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw (UCode _) ()
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw LevTy ()
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw (LevEl _) ()
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw (PiCode _ _) ()
EvalRel-lsub2 z1 z2 (LLam M) rho rho' s pw (LPiCode _) ()

------------------------------------------------------------------------
-- Corollaries
------------------------------------------------------------------------

-- invariance under pointwise T-equal level environments (same values)
EvalRel-inv : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> PwValid T θ θ' ->
  (b : FinEl) -> EvalRel M rho b -> EvalRel M rho' b
EvalRel-inv M rho rho' s pw b ev =
  Eq-transport (\ X -> EvalRel X rho' b) (lsubE-id M)
    (EvalRel-lsub2 lidS lidS M rho rho' s pw b
      (Eq-transport (\ X -> EvalRel X rho b) (Eq-sym (lsubE-id M)) ev))

-- level substitution, forward and backward
EvalRel-lsub-fwd : {n : Nat} (z : LSub) (M : Expr n) (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> PwValid T (compL θ z) θ' ->
  (b : FinEl) -> EvalRel (lsubE z M) rho b -> EvalRel M rho' b
EvalRel-lsub-fwd z M rho rho' s pw b ev =
  Eq-transport (\ X -> EvalRel X rho' b) (lsubE-id M) (EvalRel-lsub2 z lidS M rho rho' s pw b ev)

EvalRel-lsub-bwd : {n : Nat} (z : LSub) (M : Expr n) (rho : EnvApprox T θ n) (rho' : EnvApprox T θ' n) ->
  SameEnv rho rho' -> PwValid T (compL θ z) θ' ->
  (b : FinEl) -> EvalRel M rho' b -> EvalRel (lsubE z M) rho b
EvalRel-lsub-bwd z M rho rho' s pw b ev =
  EvalRel-lsub2 lidS z M rho' rho (SameEnv-sym rho rho' s) (\ i -> v-sym (pw i)) b
    (Eq-transport (\ X -> EvalRel X rho' b) (Eq-sym (lsubE-id M)) ev)

-- the reidx forms
EvalRel-reidx : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) -> PwValid T θ θ' ->
  (b : FinEl) -> EvalRel M rho b -> EvalRel M (reidx {θ' = θ'} rho) b
EvalRel-reidx M rho pw b = EvalRel-inv M rho (reidx rho) (SameEnv-reidx rho) pw b

EvalRel-unreidx : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) -> PwValid T θ θ' ->
  (b : FinEl) -> EvalRel M (reidx {θ' = θ'} rho) b -> EvalRel M rho b
EvalRel-unreidx M rho pw b =
  EvalRel-inv M (reidx rho) rho (SameEnv-sym rho (reidx rho) (SameEnv-reidx rho)) (\ i -> v-sym (pw i)) b

EvalRel-lsub-reidx : {n : Nat} (z : LSub) (M : Expr n) (rho : EnvApprox T θ n) (b : FinEl) ->
  EvalRel (lsubE z M) rho b -> EvalRel M (reidx {θ' = compL θ z} rho) b
EvalRel-lsub-reidx z M rho b = EvalRel-lsub-fwd z M rho (reidx rho) (SameEnv-reidx rho) (\ i -> v-refl) b

EvalRel-lsub-unreidx : {n : Nat} (z : LSub) (M : Expr n) (rho : EnvApprox T θ n) (b : FinEl) ->
  EvalRel M (reidx {θ' = compL θ z} rho) b -> EvalRel (lsubE z M) rho b
EvalRel-lsub-unreidx z M rho b = EvalRel-lsub-bwd z M rho (reidx rho) (SameEnv-reidx rho) (\ i -> v-refl) b

-- changing the level entered by a binder along a T-equation
pw-cons : (l l' : LExpr) -> Valid T l l' -> PwValid T (lconsS l θ) (lconsS l' θ)
pw-cons l l' d zero    = d
pw-cons l l' d (suc i) = v-refl

EvalRel-extL-valid : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (l l' : LExpr) -> Valid T l l' ->
  (b : FinEl) -> EvalRel M (extL rho l) b -> EvalRel M (extL rho l') b
EvalRel-extL-valid {θ = θ} M rho l l' d b =
  EvalRel-inv M (extL rho l) (extL rho l') (SameEnv-reidx2 rho rho (SameEnv-refl rho))
    (pw-cons {θ = θ} l l' d) b

-- instantiation lsub1:  (lsub1 A l) at rho  =  A at (rho, level 0 := θ l)
pw-lsub1 : (l : LExpr) -> PwValid T (compL θ (lsub1S l)) (lconsS (lsubL θ l) θ)
pw-lsub1 l zero    = v-refl
pw-lsub1 l (suc i) = v-refl

EvalRel-lsub1-fwd : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox T θ n) (b : FinEl) ->
  EvalRel (lsub1 A l) rho b -> EvalRel A (extL rho (lsubL θ l)) b
EvalRel-lsub1-fwd {θ = θ} A l rho b =
  EvalRel-lsub-fwd (lsub1S l) A rho (extL rho (lsubL θ l)) (SameEnv-reidx rho) (pw-lsub1 {θ = θ} l) b

EvalRel-lsub1-bwd : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox T θ n) (b : FinEl) ->
  EvalRel A (extL rho (lsubL θ l)) b -> EvalRel (lsub1 A l) rho b
EvalRel-lsub1-bwd {θ = θ} A l rho b =
  EvalRel-lsub-bwd (lsub1S l) A rho (extL rho (lsubL θ l)) (SameEnv-reidx rho) (pw-lsub1 {θ = θ} l) b

-- the special form for the identity level environment
pw-lsub1-id : (l : LExpr) -> PwValid T (compL lidS (lsub1S l)) (lconsS l lidS)
pw-lsub1-id {T = T} l zero    = Eq-transport (\ a -> Valid T a l) (Eq-sym (lsubL-id l)) v-refl
pw-lsub1-id l (suc i) = v-refl

EvalRel-lsub1-id-fwd : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox T lidS n) (b : FinEl) ->
  EvalRel (lsub1 A l) rho b -> EvalRel A (extL rho l) b
EvalRel-lsub1-id-fwd A l rho b =
  EvalRel-lsub-fwd (lsub1S l) A rho (extL rho l) (SameEnv-reidx rho) (pw-lsub1-id l) b

EvalRel-lsub1-id-bwd : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox T lidS n) (b : FinEl) ->
  EvalRel A (extL rho l) b -> EvalRel (lsub1 A l) rho b
EvalRel-lsub1-id-bwd A l rho b =
  EvalRel-lsub-bwd (lsub1S l) A rho (extL rho l) (SameEnv-reidx rho) (pw-lsub1-id l) b

-- the shift:  (lshiftE M) at (rho, level 0 := l)  =  M at rho
pw-shift : (l : LExpr) -> PwValid T (compL (lconsS l θ) lwkS) θ
pw-shift l i = v-refl

EvalRel-lshift-fwd : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (l : LExpr) (b : FinEl) ->
  EvalRel (lshiftE M) (extL rho l) b -> EvalRel M rho b
EvalRel-lshift-fwd {θ = θ} M rho l b =
  EvalRel-lsub-fwd lwkS M (extL rho l) rho (SameEnv-sym rho (extL rho l) (SameEnv-reidx rho))
    (pw-shift {θ = θ} l) b

EvalRel-lshift-bwd : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (l : LExpr) (b : FinEl) ->
  EvalRel M rho b -> EvalRel (lshiftE M) (extL rho l) b
EvalRel-lshift-bwd {θ = θ} M rho l b =
  EvalRel-lsub-bwd lwkS M (extL rho l) rho (SameEnv-sym rho (extL rho l) (SameEnv-reidx rho))
    (pw-shift {θ = θ} l) b

-- the level ldec (lcode l) evaluates like l
EvalRel-ldec-fwd : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (l : LExpr) (b : FinEl) ->
  EvalRel M (extL rho (ldecT T (lcodeT T l))) b -> EvalRel M (extL rho l) b
EvalRel-ldec-fwd {T = T} M rho l b =
  EvalRel-extL-valid M rho (ldecT T (lcodeT T l)) l (LDec.ldec-code (D T) l) b

EvalRel-ldec-bwd : {n : Nat} (M : Expr n) (rho : EnvApprox T θ n) (l : LExpr) (b : FinEl) ->
  EvalRel M (extL rho l) b -> EvalRel M (extL rho (ldecT T (lcodeT T l))) b
EvalRel-ldec-bwd {T = T} M rho l b =
  EvalRel-extL-valid M rho l (ldecT T (lcodeT T l)) (v-sym (LDec.ldec-code (D T) l)) b
