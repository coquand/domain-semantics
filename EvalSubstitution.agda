{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- EvalSubstitution.agda
--
-- General substitution/evaluation compatibility for the relational
-- semantics on finite approximants.
--
-- Architecture (McBride / PLFA style):
--   1. EvalRel-ren / EvalRel-ren-inv — renaming preserves evaluation
--   2. EvalRel-wk / EvalRel-unwk     — weakening as corollary
--   3. SubRel                         — semantic substitution relation
--   4. EvalRel-subst                  — general substitution (backward)
--   5. SubRel-subst1                  — SubRel for [M/0]
--   6. EvalRel-subst1-backward        — unary substitution (backward)
--   7. MaxSubRel / MaxSubRel-lift     — maximal substitution relation
--   8. EvalRel-subst-forward-max      — general forward substitution
--   9. EvalRel-subst1-forward-bounded — unary forward with explicit bound
--
-- NO postulates.
------------------------------------------------------------------------

module EvalSubstitution where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; isPos)
open import PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf ;
  Comp ; Comp-down ; Comp-sym ;
  Sup ; Sup-Bot-l ; Sup-Bot-r ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-Sup-lub ; FinMem-Sup-element ;
  FinMem ; FinMem-coh-u ; FinMem-coh-a ; FinMem-a-in-U ;
  EvalFun ; EvalFun-step ; leFinEl ; leFinEl-sound ;
  Coherent-EvalFun ; Comp-value-EvalFun ;
  coherentWith-to-compStepFun)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EnvLe-extend-left ; EnvLe-extend-right ;
  EvalRel-Bot ; EvalRel-Comp ; EvalRel-Sup ;
  EvalRel-ideal-Comp ;
  Lam-edgewise ; Pi-edgewise)
open S using (List ; nil ; cons)
open import Selection using (Edge ; EdgeIn ; here ; there ; Selection ;
  sel-nil ; sel-skip ; sel-take)
open import RawSyntax

------------------------------------------------------------------------
-- Part 1: Renaming preserves evaluation
------------------------------------------------------------------------

-- Renaming agreement: environments agree pointwise on a renaming.
RenAgree : {n m : Nat} -> Ren n m -> EnvApprox n -> EnvApprox m -> Set
RenAgree {n} r rho rho' = (i : Fin n) -> Eq (lookupEnv (r i) rho') (lookupEnv i rho)

-- Lifting preserves agreement on extended environments.
liftRen-agree : {n m : Nat} (r : Ren n m)
  (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (x : FinEl) ->
  RenAgree (liftRen r) (extendEnv rho x) (extendEnv rho' x)
liftRen-agree r rho rho' eq x fzero    = refl
liftRen-agree r rho rho' eq x (fsuc i) = eq i

-- EvalRel-ren: if environments agree on r, then EvalRel M rho u
-- implies EvalRel (renExpr r M) rho' u.
--
-- Structural induction on M.

EvalRel-ren : {n m : Nat} (r : Ren n m)
  (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (u : FinEl) ->
  EvalRel M rho u -> EvalRel (renExpr r M) rho' u

-- Var: transport via equation
EvalRel-ren r (Var i) rho rho' eq u (mkSigma cu le) =
  mkSigma cu (Eq-transport (\ z -> LeCode u z) (Eq-sym (eq i)) le)

-- U: identity
EvalRel-ren r U rho rho' eq u ev = ev

-- App Bot: trivial
EvalRel-ren r (App M N) rho rho' eq Bot ev = tt

-- App non-Bot: one-edge form
EvalRel-ren r (App M N) rho rho' eq UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))

-- Lam Bot: trivial
EvalRel-ren r (Lam A M) rho rho' eq Bot ev = tt

-- Lam (FunEl g)
EvalRel-ren r (Lam A M) rho rho' eq (FunEl g)
  (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
  mkSigma a (mkSigma cg (mkSigma aU
    (mkSigma (EvalRel-ren r A rho rho' eq a evA)
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evM  = snd (snd (snd w))
            eq'  = liftRen-agree r rho rho' eq x
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-ren (liftRen r) M (extendEnv rho x)
               (extendEnv rho' x) eq' v evM)))))))

-- Lam UCode: absurd
EvalRel-ren r (Lam A M) rho rho' eq UCode ()

-- Lam (PiCode a f): absurd
EvalRel-ren r (Lam A M) rho rho' eq (PiCode a f) ()

-- Pi Bot: trivial
EvalRel-ren r (Pi A B) rho rho' eq Bot ev = tt

-- Pi (PiCode a f): new structure with existential a'
EvalRel-ren r (Pi A B) rho rho' eq (PiCode a f)
  (mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA' body)))) =
  mkSigma caf (mkSigma (EvalRel-ren r A rho rho' eq a evA)
    (mkSigma a' (mkSigma (EvalRel-ren r A rho rho' eq a' evA')
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evB  = snd (snd (snd w))
            eq'  = liftRen-agree r rho rho' eq x
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-ren (liftRen r) B (extendEnv rho x)
               (extendEnv rho' x) eq' v evB)))))))

-- Pi UCode: absurd
EvalRel-ren r (Pi A B) rho rho' eq UCode ()

-- Pi (FunEl g): absurd
EvalRel-ren r (Pi A B) rho rho' eq (FunEl g) ()

------------------------------------------------------------------------
-- Part 1b: Inverse renaming — undo renaming on evaluation
------------------------------------------------------------------------

EvalRel-ren-inv : {n m : Nat} (r : Ren n m)
  (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' ->
  (u : FinEl) -> EvalRel (renExpr r M) rho' u -> EvalRel M rho u

EvalRel-ren-inv r (Var i) rho rho' eq u (mkSigma cu le) =
  mkSigma cu (Eq-transport (LeCode u) (eq i) le)

EvalRel-ren-inv r U rho rho' eq u ev = ev

EvalRel-ren-inv r (App M N) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (App M N) rho rho' eq UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))

EvalRel-ren-inv r (Lam A M) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (Lam A M) rho rho' eq (FunEl g)
  (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
  mkSigma a (mkSigma cg (mkSigma aU
    (mkSigma (EvalRel-ren-inv r A rho rho' eq a evA)
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evM  = snd (snd (snd w))
            eq'  = liftRen-agree r rho rho' eq x
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-ren-inv (liftRen r) M (extendEnv rho x)
               (extendEnv rho' x) eq' v evM)))))))
EvalRel-ren-inv r (Lam A M) rho rho' eq UCode ()
EvalRel-ren-inv r (Lam A M) rho rho' eq (PiCode a f) ()

EvalRel-ren-inv r (Pi A B) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (Pi A B) rho rho' eq (PiCode a f)
  (mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA' body)))) =
  mkSigma caf (mkSigma (EvalRel-ren-inv r A rho rho' eq a evA)
    (mkSigma a' (mkSigma (EvalRel-ren-inv r A rho rho' eq a' evA')
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evB  = snd (snd (snd w))
            eq'  = liftRen-agree r rho rho' eq x
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-ren-inv (liftRen r) B (extendEnv rho x)
               (extendEnv rho' x) eq' v evB)))))))
EvalRel-ren-inv r (Pi A B) rho rho' eq UCode ()
EvalRel-ren-inv r (Pi A B) rho rho' eq (FunEl g) ()

------------------------------------------------------------------------
-- Part 2: Weakening as corollary of renaming
------------------------------------------------------------------------

EvalRel-wk : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (v u : FinEl) -> EvalRel M rho u -> EvalRel (wkExpr M) (extendEnv rho v) u
EvalRel-wk M rho v u ev =
  EvalRel-ren wkRen M rho (extendEnv rho v) (\ i -> refl) u ev

EvalRel-unwk : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (v u : FinEl) -> EvalRel (wkExpr M) (extendEnv rho v) u -> EvalRel M rho u
EvalRel-unwk M rho v u ev =
  EvalRel-ren-inv wkRen M rho (extendEnv rho v) (\ i -> refl) u ev

------------------------------------------------------------------------
-- Part 3: Semantic substitution relation
------------------------------------------------------------------------

-- SubRel sigma rho rho' means: for each variable i in the source
-- context, sigma i evaluates in rho to (at least) the value that
-- variable i has in rho'.
SubRel : {h g : Nat} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
SubRel {h} {g} sigma rho rho' =
  (i : Fin g) -> EvalRel (sigma i) rho (lookupEnv i rho')

-- Lifting preserves SubRel on extended environments.
SubRel-lift : {h g : Nat} (sigma : Sub h g)
  (rho : EnvApprox h) (rho' : EnvApprox g) ->
  SubRel sigma rho rho' -> (x : FinEl) -> Coherent x ->
  SubRel (liftSub sigma) (extendEnv rho x) (extendEnv rho' x)
SubRel-lift sigma rho rho' sr x cx fzero =
  mkSigma cx (LeCode-refl x cx)
SubRel-lift sigma rho rho' sr x cx (fsuc i) =
  EvalRel-wk (sigma i) rho x (lookupEnv i rho') (sr i)

------------------------------------------------------------------------
-- Part 4: General substitution theorem (backward direction)
--
-- If SubRel sigma rho rho' and EvalRel M rho' u,
-- then EvalRel (substExpr sigma M) rho u.
--
-- Structural induction on M.  Uses EvalRel-down in the Var case
-- and EvalRel-wk (via SubRel-lift) in the binder cases.
------------------------------------------------------------------------

EvalRel-subst : {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho ->
  SubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel M rho' u -> EvalRel (substExpr sigma M) rho u

-- Var
EvalRel-subst sigma (Var i) rho rho' crho sr u (mkSigma cu le) =
  EvalRel-down (sigma i) rho (lookupEnv i rho') u crho cu (sr i) le

-- U: identity
EvalRel-subst sigma U rho rho' crho sr u ev = ev

-- App Bot: trivial
EvalRel-subst sigma (App M N) rho rho' crho sr Bot ev = tt

-- App non-Bot: one-edge form
EvalRel-subst sigma (App M N) rho rho' crho sr UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))

-- Lam Bot: trivial
EvalRel-subst sigma (Lam A M) rho rho' crho sr Bot ev = tt

-- Lam (FunEl g)
EvalRel-subst sigma (Lam A M) rho rho' crho sr (FunEl g)
  (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
  mkSigma a (mkSigma cg (mkSigma aU
    (mkSigma (EvalRel-subst sigma A rho rho' crho sr a evA)
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evM  = snd (snd (snd w))
            cx   = FinMem-coh-u x a mem
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-subst (liftSub sigma) M (extendEnv rho x) (extendEnv rho' x)
               (mkSigma crho cx)
               (SubRel-lift sigma rho rho' sr x cx)
               v evM)))))))

-- Lam UCode: absurd
EvalRel-subst sigma (Lam A M) rho rho' crho sr UCode ()

-- Lam (PiCode a f): absurd
EvalRel-subst sigma (Lam A M) rho rho' crho sr (PiCode a f) ()

-- Pi Bot: trivial
EvalRel-subst sigma (Pi A B) rho rho' crho sr Bot ev = tt

-- Pi (PiCode a f): new structure with existential a'
EvalRel-subst sigma (Pi A B) rho rho' crho sr (PiCode a f)
  (mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA' body)))) =
  mkSigma caf (mkSigma (EvalRel-subst sigma A rho rho' crho sr a evA)
    (mkSigma a' (mkSigma (EvalRel-subst sigma A rho rho' crho sr a' evA')
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evB  = snd (snd (snd w))
            cx   = FinMem-coh-u x a' mem
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-subst (liftSub sigma) B (extendEnv rho x) (extendEnv rho' x)
               (mkSigma crho cx)
               (SubRel-lift sigma rho rho' sr x cx)
               v evB)))))))

-- Pi UCode: absurd
EvalRel-subst sigma (Pi A B) rho rho' crho sr UCode ()

-- Pi (FunEl g): absurd
EvalRel-subst sigma (Pi A B) rho rho' crho sr (FunEl g) ()

------------------------------------------------------------------------
-- Part 5: SubRel for unary substitution
------------------------------------------------------------------------

-- SubRel-subst1: construct SubRel for the substitution [M/0].
SubRel-subst1 : {n : Nat} (M : Expr n)
  (rho : EnvApprox n) (v : FinEl) ->
  CoherentEnv rho ->
  EvalRel M rho v ->
  SubRel (subst1Sub M) rho (extendEnv rho v)
SubRel-subst1 M rho v crho evM fzero = evM
SubRel-subst1 M rho v crho evM (fsuc i) =
  mkSigma (lookupEnv-coh i rho crho)
          (LeCode-refl (lookupEnv i rho) (lookupEnv-coh i rho crho))

------------------------------------------------------------------------
-- Part 6: Unary substitution corollary (backward)
------------------------------------------------------------------------

EvalRel-subst1-backward :
  {n : Nat} ->
  (B : Expr (suc n)) ->
  (M : Expr n) ->
  (rho : EnvApprox n) ->
  (v u : FinEl) ->
  CoherentEnv rho ->
  EvalRel M rho v ->
  EvalRel B (extendEnv rho v) u ->
  EvalRel (subst1 B M) rho u
EvalRel-subst1-backward B M rho v u crho evM evB =
  EvalRel-subst (subst1Sub M) B rho (extendEnv rho v) crho
    (SubRel-subst1 M rho v crho evM) u evB

------------------------------------------------------------------------
-- Part 7: Maximal substitution relation
------------------------------------------------------------------------

-- MaxSubRel sigma rho rho' means: for each variable i, ALL evaluation
-- results of (sigma i) in rho are bounded by lookupEnv i rho'.
MaxSubRel : {h g : Nat} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
MaxSubRel {h} {g} sigma rho rho' =
  (i : Fin g) (u : FinEl) -> EvalRel (sigma i) rho u ->
  LeCode u (lookupEnv i rho')

-- Lifting MaxSubRel through binders
MaxSubRel-lift : {h g : Nat} (sigma : Sub h g)
  (rho : EnvApprox h) (rho' : EnvApprox g) ->
  MaxSubRel sigma rho rho' -> (x : FinEl) ->
  MaxSubRel (liftSub sigma) (extendEnv rho x) (extendEnv rho' x)
MaxSubRel-lift sigma rho rho' msr x fzero u ev = snd ev
MaxSubRel-lift sigma rho rho' msr x (fsuc i) u ev =
  msr i u (EvalRel-unwk (sigma i) rho x u ev)

------------------------------------------------------------------------
-- Part 8: General forward substitution (MaxSubRel version)
------------------------------------------------------------------------

EvalRel-subst-forward-max : {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho -> CoherentEnv rho' ->
  MaxSubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel (substExpr sigma M) rho u ->
  EvalRel M rho' u

-- Var i
EvalRel-subst-forward-max sigma (Var i) rho rho' crho crho' msr u ev =
  mkSigma (EvalRel-coh (sigma i) rho u ev) (msr i u ev)

-- U
EvalRel-subst-forward-max sigma U rho rho' crho crho' msr u ev = ev

-- App Bot
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr Bot ev = tt

-- App non-Bot: one-edge form
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))

-- Lam Bot
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr Bot ev = tt

-- Lam (FunEl g)
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr (FunEl g)
  (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
  mkSigma a (mkSigma cg (mkSigma aU
    (mkSigma (EvalRel-subst-forward-max sigma A rho rho' crho crho' msr a evA)
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evM  = snd (snd (snd w))
            cx   = FinMem-coh-u x a mem
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-subst-forward-max (liftSub sigma) M
               (extendEnv rho x) (extendEnv rho' x)
               (mkSigma crho cx) (mkSigma crho' cx)
               (MaxSubRel-lift sigma rho rho' msr x) v evM)))))))

-- Lam UCode: absurd
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr UCode ()

-- Lam (PiCode a f): absurd
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr (PiCode a f) ()

-- Pi Bot
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr Bot ev = tt

-- Pi (PiCode a f): new structure with existential a'
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr (PiCode a f)
  (mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA' body)))) =
  mkSigma caf (mkSigma (EvalRel-subst-forward-max sigma A rho rho' crho crho' msr a evA)
    (mkSigma a' (mkSigma (EvalRel-subst-forward-max sigma A rho rho' crho crho' msr a' evA')
      (\ u v sel ->
        let w    = body u v sel
            x    = fst w
            le   = fst (snd w)
            mem  = fst (snd (snd w))
            evB  = snd (snd (snd w))
            cx   = FinMem-coh-u x a' mem
        in mkSigma x (mkSigma le (mkSigma mem
             (EvalRel-subst-forward-max (liftSub sigma) B
               (extendEnv rho x) (extendEnv rho' x)
               (mkSigma crho cx) (mkSigma crho' cx)
               (MaxSubRel-lift sigma rho rho' msr x) v evB)))))))

-- Pi UCode: absurd
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr UCode ()

-- Pi (FunEl g): absurd
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr (FunEl g) ()

------------------------------------------------------------------------
-- Part 9: Forward substitution for subst1
------------------------------------------------------------------------

-- MaxSubRel for subst1Sub given a value v that upper-bounds all
-- evaluation results of a in rho.
MaxSubRel-subst1 : {n : Nat} (a : Expr n)
  (rho : EnvApprox n) (v : FinEl) ->
  ((u : FinEl) -> EvalRel a rho u -> LeCode u v) ->
  MaxSubRel (subst1Sub a) rho (extendEnv rho v)
MaxSubRel-subst1 a rho v bound fzero u ev = bound u ev
MaxSubRel-subst1 a rho v bound (fsuc i) u ev = snd ev

-- EvalRel-subst1-forward with explicit bound.
EvalRel-subst1-forward-bounded :
  {n : Nat} ->
  (M : Expr (suc n)) ->
  (a : Expr n) ->
  (rho : EnvApprox n) ->
  (v u : FinEl) ->
  CoherentEnv rho ->
  Coherent v ->
  EvalRel a rho v ->
  ((u' : FinEl) -> EvalRel a rho u' -> LeCode u' v) ->
  EvalRel (subst1 M a) rho u ->
  EvalRel M (extendEnv rho v) u
EvalRel-subst1-forward-bounded M a rho v u crho cv evAv bound ev =
  EvalRel-subst-forward-max (subst1Sub a) M rho (extendEnv rho v)
    crho (mkSigma crho cv)
    (MaxSubRel-subst1 a rho v bound) u ev

------------------------------------------------------------------------
-- Part 10: Forward substitution for subst1 with existential witness
--
-- EvalRel-subst1-forward: from EvalRel (subst1 M N) rho u, produce
-- a value v with EvalRel N rho v and EvalRel M (extendEnv rho v) u.
--
-- Proof: structural induction on M.
-- At each Var fzero leaf, v is the value from the proof.
-- At App nodes, Sup the v-witnesses from the two subterms.
-- At binder nodes (Lam/Pi), generalize to liftSub.
--
-- We define the general version EvalRel-subst-forward-wit first,
-- then specialize to subst1.
------------------------------------------------------------------------

-- Environment infrastructure for the forward substitution.

-- All-Bot environment
botEnv : {n : Nat} -> EnvApprox n
botEnv {zero}  = emptyEnv
botEnv {suc n} = extendEnv (botEnv {n}) Bot

-- Pointwise Sup of two environments
supEnv : {n : Nat} -> EnvApprox n -> EnvApprox n -> EnvApprox n
supEnv emptyEnv emptyEnv = emptyEnv
supEnv (extendEnv rho1 u1) (extendEnv rho2 u2) =
  extendEnv (supEnv rho1 rho2) (Sup u1 u2)

-- botEnv is coherent
botEnv-Coherent : {n : Nat} -> CoherentEnv (botEnv {n})
botEnv-Coherent {zero}  = tt
botEnv-Coherent {suc n} = mkSigma (botEnv-Coherent {n}) tt

-- lookupEnv in botEnv is Bot
lookupEnv-botEnv : {n : Nat} (i : Fin n) -> Eq (lookupEnv i (botEnv {n})) Bot
lookupEnv-botEnv fzero    = refl
lookupEnv-botEnv (fsuc i) = lookupEnv-botEnv i

-- Comp-Bot: anything is compatible with Bot
Comp-Bot-right : (u : FinEl) -> Comp u Bot
Comp-Bot-right Bot          = tt
Comp-Bot-right UCode        = tt
Comp-Bot-right (FunEl g)    = tt
Comp-Bot-right (PiCode a f) = tt

-- SubRel for sigma into botEnv: EvalRel (sigma i) rho Bot
SubRel-botEnv : {h n : Nat} (sigma : Sub h n) (rho : EnvApprox h) ->
  SubRel sigma rho (botEnv {n})
SubRel-botEnv sigma rho i =
  Eq-transport (EvalRel (sigma i) rho) (Eq-sym (lookupEnv-botEnv i))
    (EvalRel-Bot (sigma i) rho)

-- CompEnv: pointwise compatibility of two environments
CompEnv : {n : Nat} -> EnvApprox n -> EnvApprox n -> Set
CompEnv emptyEnv emptyEnv = Top
CompEnv (extendEnv rho1 u1) (extendEnv rho2 u2) =
  Pair (CompEnv rho1 rho2) (Comp u1 u2)

-- CoherentEnv of supEnv from CompEnv
CoherentEnv-supEnv : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  CoherentEnv (supEnv rho1 rho2)
CoherentEnv-supEnv emptyEnv emptyEnv c1 c2 comp = tt
CoherentEnv-supEnv (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (CoherentEnv-supEnv rho1 rho2 (fst c1) (fst c2) (fst comp))
          (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))

-- EnvLe from rho1 to supEnv rho1 rho2
EnvLe-supEnv-left : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  EnvLe rho1 (supEnv rho1 rho2)
EnvLe-supEnv-left emptyEnv emptyEnv c1 c2 comp = tt
EnvLe-supEnv-left (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (EnvLe-supEnv-left rho1 rho2 (fst c1) (fst c2) (fst comp))
    (mkSigma (snd c1) (mkSigma (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))
      (LeCode-Sup-left u1 u2 (snd comp) (snd c1) (snd c2))))

-- EnvLe from rho2 to supEnv rho1 rho2
EnvLe-supEnv-right : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  EnvLe rho2 (supEnv rho1 rho2)
EnvLe-supEnv-right emptyEnv emptyEnv c1 c2 comp = tt
EnvLe-supEnv-right (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (EnvLe-supEnv-right rho1 rho2 (fst c1) (fst c2) (fst comp))
    (mkSigma (snd c2) (mkSigma (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))
      (LeCode-Sup-right u1 u2 (snd comp) (snd c1) (snd c2))))

-- SubRel-supEnv: if SubRel sigma rho rho1 and SubRel sigma rho rho2,
-- and sigma-values are pairwise compatible, then SubRel sigma rho (supEnv rho1 rho2)
SubRel-supEnv : {h n : Nat} (sigma : Sub h n)
  (rho : EnvApprox h) (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho ->
  CoherentEnv rho1 -> CoherentEnv rho2 ->
  CompEnv rho1 rho2 ->
  SubRel sigma rho rho1 -> SubRel sigma rho rho2 ->
  SubRel sigma rho (supEnv rho1 rho2)
SubRel-supEnv {n = zero} sigma rho emptyEnv emptyEnv crho c1 c2 comp sr1 sr2 i
  with i
... | ()
SubRel-supEnv {n = suc n} sigma rho
  (extendEnv rho1 u1) (extendEnv rho2 u2)
  crho c1 c2 comp sr1 sr2 fzero =
  EvalRel-Sup (sigma fzero) rho u1 u2 crho (snd c1) (snd c2) (snd comp) (sr1 fzero) (sr2 fzero)
SubRel-supEnv {n = suc n} sigma rho
  (extendEnv rho1 u1) (extendEnv rho2 u2)
  crho c1 c2 comp sr1 sr2 (fsuc i) =
  SubRel-supEnv (\ j -> sigma (fsuc j)) rho rho1 rho2 crho
    (fst c1) (fst c2) (fst comp)
    (\ j -> sr1 (fsuc j)) (\ j -> sr2 (fsuc j)) i

-- CompEnv for botEnv and any coherent env
CompEnv-botEnv-right : {n : Nat} (rho : EnvApprox n) -> CoherentEnv rho ->
  CompEnv (botEnv {n}) rho
CompEnv-botEnv-right emptyEnv crho = tt
CompEnv-botEnv-right (extendEnv rho u) crho =
  mkSigma (CompEnv-botEnv-right rho (fst crho)) tt

-- CompEnv-SubRel: if sr1 and sr2 are SubRels for the same sigma,rho,
-- then the target environments are CompEnv (via EvalRel-Comp + SubRel)
CompEnv-from-SubRel : {h n : Nat} (sigma : Sub h n)
  (rho : EnvApprox h) (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho ->
  SubRel sigma rho rho1 -> SubRel sigma rho rho2 ->
  CompEnv rho1 rho2
CompEnv-from-SubRel {n = zero} sigma rho emptyEnv emptyEnv crho sr1 sr2 = tt
CompEnv-from-SubRel {n = suc n} sigma rho
  (extendEnv rho1 u1) (extendEnv rho2 u2) crho sr1 sr2 =
  mkSigma (CompEnv-from-SubRel (\ j -> sigma (fsuc j)) rho rho1 rho2 crho
            (\ j -> sr1 (fsuc j)) (\ j -> sr2 (fsuc j)))
          (EvalRel-Comp (sigma fzero) rho crho u1 u2 (sr1 fzero) (sr2 fzero))

-- supEnv with botEnv is identity (up to Eq)
lookupEnv-supEnv-botEnv-left : {n : Nat} (rho : EnvApprox n) (i : Fin n) ->
  Eq (lookupEnv i (supEnv (botEnv {n}) rho)) (lookupEnv i rho)
lookupEnv-supEnv-botEnv-left (extendEnv rho u) fzero = Sup-Bot-l u
lookupEnv-supEnv-botEnv-left (extendEnv rho u) (fsuc i) =
  lookupEnv-supEnv-botEnv-left rho i

------------------------------------------------------------------------
-- Part 10: General forward substitution with witness environment
--
-- Uses edgewise characterizations (Lam-edgewise, Pi-edgewise) for
-- binder cases: fold over finite edge lists to collect witness envs.
------------------------------------------------------------------------

-- Type alias for the result of the forward substitution
FwdResult : {h g : Nat} -> Sub h g -> EnvApprox h -> Expr g -> FinEl -> Set
FwdResult {h} {g} sigma rho M u =
  Sigma (EnvApprox g) (\ rho' ->
    Pair (CoherentEnv rho')
    (Pair (SubRel sigma rho rho')
          (EvalRel M rho' u)))

-- Helper: extract FinMem a0 UCode from first edge of non-nil function
extractFinMemU : {g : Nat} {B : Expr (suc g)} {rho' : EnvApprox g}
  (a0 : FinEl) (f0 : FinFun) -> CoherentFun f0 ->
  ((p : Edge) -> EdgeIn p f0 ->
    Sigma FinEl (\ z -> Pair (LeCode z (fst p))
      (Pair (FinMem z a0) (EvalRel B (extendEnv rho' z) (snd p))))) ->
  FinMem a0 UCode
extractFinMemU a0 nil cf _ with cf
... | ()
extractFinMemU a0 (cons p0 ps) cf bodyMap =
  FinMem-a-in-U (fst (bodyMap p0 here)) a0 (fst (snd (snd (bodyMap p0 here))))

-- Forward declaration for mutual recursion with foldEdgeFwd
EvalRel-subst-forward-wit :
  {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (u : FinEl) ->
  CoherentEnv rho ->
  EvalRel (substExpr sigma M) rho u ->
  FwdResult sigma rho M u

-- Helper: combine two FwdResults via supEnv
combineFwd : {h g : Nat} (sigma : Sub h g)
  (rho : EnvApprox h) ->
  CoherentEnv rho ->
  (rho1 rho2 : EnvApprox g) ->
  CoherentEnv rho1 -> CoherentEnv rho2 ->
  SubRel sigma rho rho1 -> SubRel sigma rho rho2 ->
  Sigma (EnvApprox g) (\ rho' ->
    Pair (CoherentEnv rho')
    (Pair (SubRel sigma rho rho')
    (Pair (EnvLe rho1 rho') (EnvLe rho2 rho'))))
combineFwd sigma rho crho rho1 rho2 c1 c2 sr1 sr2 =
  let comp = CompEnv-from-SubRel sigma rho rho1 rho2 crho sr1 sr2
  in mkSigma (supEnv rho1 rho2)
       (mkSigma (CoherentEnv-supEnv rho1 rho2 c1 c2 comp)
         (mkSigma (SubRel-supEnv sigma rho rho1 rho2 crho c1 c2 comp sr1 sr2)
           (mkSigma (EnvLe-supEnv-left rho1 rho2 c1 c2 comp)
                    (EnvLe-supEnv-right rho1 rho2 c1 c2 comp))))

-- EnvLe is transitive
EnvLe-trans : {n : Nat} (rho1 rho2 rho3 : EnvApprox n) ->
  EnvLe rho1 rho2 -> EnvLe rho2 rho3 -> EnvLe rho1 rho3
EnvLe-trans emptyEnv emptyEnv emptyEnv le12 le23 = tt
EnvLe-trans (extendEnv r1 u1) (extendEnv r2 u2) (extendEnv r3 u3)
  le12 le23 =
  mkSigma (EnvLe-trans r1 r2 r3 (fst le12) (fst le23))
    (mkSigma (fst (snd le12))
      (mkSigma (fst (snd (snd le23)))
        (LeCode-trans u1 u2 u3
          (fst (snd le12)) (fst (snd le23))
          (fst (snd (snd le23)))
          (snd (snd (snd le12)))
          (snd (snd (snd le23))))))

-- Environment destructors
tailEnv : {n : Nat} -> EnvApprox (suc n) -> EnvApprox n
tailEnv (extendEnv r _) = r

headEnv : {n : Nat} -> EnvApprox (suc n) -> FinEl
headEnv (extendEnv _ v) = v

tailCoherent : {n : Nat} (rho : EnvApprox (suc n)) -> CoherentEnv rho -> CoherentEnv (tailEnv rho)
tailCoherent (extendEnv r _) crho = fst crho

headCoherent : {n : Nat} (rho : EnvApprox (suc n)) -> CoherentEnv rho -> Coherent (headEnv rho)
headCoherent (extendEnv _ v) crho = snd crho

-- Decompose SubRel for liftSub into SubRel for sigma on the tail
decompSrTail : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h) (z : FinEl) ->
  (rho' : EnvApprox (suc g)) ->
  SubRel (liftSub sigma) (extendEnv rho z) rho' ->
  SubRel sigma rho (tailEnv rho')
decompSrTail sigma rho z (extendEnv r v) sr i =
  EvalRel-unwk (sigma i) rho z (lookupEnv i r) (sr (fsuc i))

-- Extract head ordering from SubRel for liftSub
decompSrHead : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h) (z : FinEl) ->
  (rho' : EnvApprox (suc g)) ->
  SubRel (liftSub sigma) (extendEnv rho z) rho' ->
  LeCode (headEnv rho') z
decompSrHead sigma rho z (extendEnv r v) sr = snd (sr fzero)

-- EnvLe from rho' to (extendEnv tailRho headVal) by pattern matching
decompEnvLe : {g : Nat} (rho' : EnvApprox (suc g)) (target : EnvApprox g) (z : FinEl) ->
  EnvLe (tailEnv rho') target -> Coherent (headEnv rho') -> Coherent z -> LeCode (headEnv rho') z ->
  EnvLe rho' (extendEnv target z)
decompEnvLe (extendEnv r v) target z leTail cv cz le =
  mkSigma leTail (mkSigma cv (mkSigma cz le))

-- Helper: fold over edge list to collect witness environments from body
-- evaluations. For each edge p in g, we call the IH on the body and
-- accumulate the witness environment via supEnv.
foldEdgeFwd : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h)
  (M : Expr (suc g))
  (accRho : EnvApprox g) ->
  CoherentEnv rho -> CoherentEnv accRho -> SubRel sigma rho accRho ->
  (a : FinEl) ->
  -- per-edge body evaluations (from edgewise)
  (edges : FinFun) ->
  (body : (p : Edge) -> EdgeIn p edges ->
    Sigma FinEl (\ z -> Pair (LeCode z (fst p))
      (Pair (FinMem z a)
            (EvalRel (substExpr (liftSub sigma) M) (extendEnv rho z) (snd p))))) ->
  -- Result: accumulated environment + per-edge body evaluations in it
  Sigma (EnvApprox g) (\ rho' ->
    Pair (CoherentEnv rho')
    (Pair (SubRel sigma rho rho')
    (Pair (EnvLe accRho rho')
      ((p : Edge) -> EdgeIn p edges ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst p))
          (Pair (FinMem z a)
                (EvalRel M (extendEnv rho' z) (snd p))))))))
foldEdgeFwd sigma rho M accRho crho cAcc srAcc a nil body =
  mkSigma accRho (mkSigma cAcc (mkSigma srAcc
    (mkSigma (EnvLe-refl accRho cAcc)
      (\ p ()))))
foldEdgeFwd sigma rho M accRho crho cAcc srAcc a (cons p ps) body =
  let -- Process edge p (at position 'here')
      wp   = body p here
      zp   = fst wp
      lep  = fst (snd wp)
      memp = fst (snd (snd wp))
      evBp = snd (snd (snd wp))
      czp  = FinMem-coh-u zp a memp
      -- IH on M for this edge
      ihp  = EvalRel-subst-forward-wit (liftSub sigma) M
               (extendEnv rho zp) (snd p) (mkSigma crho czp) evBp
      rhoBp    = fst ihp
      crhoBp   = fst (snd ihp)
      srBp     = fst (snd (snd ihp))
      evMp     = snd (snd (snd ihp))
      -- Extract tail of rhoBp (the sigma-variable part)
      tailBp   = tailEnv rhoBp
      cTailBp  = tailCoherent rhoBp crhoBp
      -- SubRel sigma rho tailBp (from liftSub SubRel at fsuc indices)
      srTailBp = decompSrTail sigma rho zp rhoBp srBp
      -- Combine accRho with tailBp
      comb   = combineFwd sigma rho crho accRho tailBp cAcc cTailBp srAcc srTailBp
      midRho = fst comb
      cMid   = fst (snd comb)
      srMid  = fst (snd (snd comb))
      leAcc  = fst (snd (snd (snd comb)))
      leTail = snd (snd (snd (snd comb)))
      -- Lift evMp from rhoBp to (extendEnv midRho zp)
      envleBp : EnvLe rhoBp (extendEnv midRho zp)
      envleBp = decompEnvLe rhoBp midRho zp leTail
                  (headCoherent rhoBp crhoBp) czp (decompSrHead sigma rho zp rhoBp srBp)
      evMp' = EvalRel-mon-env M rhoBp (extendEnv midRho zp) (snd p) evMp envleBp
      -- Recurse on remaining edges
      rec = foldEdgeFwd sigma rho M midRho crho cMid srMid a ps
              (\ q ein -> body q (there ein))
      rho'  = fst rec
      crho' = fst (snd rec)
      srho' = fst (snd (snd rec))
      leMid = fst (snd (snd (snd rec)))
      bodyRec = snd (snd (snd (snd rec)))
      -- Lift evMp' from (extendEnv midRho zp) to (extendEnv rho' zp)
      envleMid : EnvLe (extendEnv midRho zp) (extendEnv rho' zp)
      envleMid = mkSigma leMid (mkSigma czp (mkSigma czp (LeCode-refl zp czp)))
      evMp'' = EvalRel-mon-env M (extendEnv midRho zp) (extendEnv rho' zp)
                 (snd p) evMp' envleMid
  in mkSigma rho' (mkSigma crho' (mkSigma srho'
       (mkSigma (EnvLe-trans accRho midRho rho' leAcc leMid)
         (\ q ein -> edgeCase q ein
           (mkSigma zp (mkSigma lep (mkSigma memp evMp'')))
           bodyRec))))
  where
    edgeCase : {g0 : Nat} {M0 : Expr (suc g0)} {a0 : FinEl} {r : EnvApprox g0}
      {p0 : Edge} {ps0 : FinFun} ->
      (q : Edge) -> EdgeIn q (cons p0 ps0) ->
      Sigma FinEl (\ z -> Pair (LeCode z (fst p0))
        (Pair (FinMem z a0) (EvalRel M0 (extendEnv r z) (snd p0)))) ->
      ((q' : Edge) -> EdgeIn q' ps0 ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst q'))
          (Pair (FinMem z a0) (EvalRel M0 (extendEnv r z) (snd q'))))) ->
      Sigma FinEl (\ z -> Pair (LeCode z (fst q))
        (Pair (FinMem z a0) (EvalRel M0 (extendEnv r z) (snd q))))
    edgeCase ._ here result _ = result
    edgeCase q (there ein) _ rest = rest q ein

------------------------------------------------------------------------
-- Main forward substitution (cases)
------------------------------------------------------------------------

-- Var i
EvalRel-subst-forward-wit sigma (Var i) rho u crho ev =
  let cu = EvalRel-coh (sigma i) rho u ev
      -- Build env with u at position i, Bot elsewhere
      -- Use botEnv as base, then supEnv with a singleton
      -- Actually simpler: use botEnv and SubRel-botEnv, then
      -- show EvalRel (Var i) botEnv u = Pair cu (LeCode u Bot) -- NO
      -- Instead: we need lookupEnv i rho' >= u.
      -- Build rho' from scratch using EvalRel-down on each sigma j.
      -- Simplest: rho' with lookupEnv i = u, rest = Bot.
      -- Agda trick: use the Var evaluation directly.
  in mkSigma (singletonEnv i u) (mkSigma (singletonEnv-Coherent i u cu)
       (mkSigma (singletonEnv-SubRel sigma rho i u ev)
         (mkSigma cu (singletonEnv-lookup i u cu))))
  where
    -- singletonEnv: environment with u at position i, Bot elsewhere
    singletonEnv : {n : Nat} -> Fin n -> FinEl -> EnvApprox n
    singletonEnv fzero u    = extendEnv botEnv u
    singletonEnv (fsuc i) u = extendEnv (singletonEnv i u) Bot

    singletonEnv-Coherent : {n : Nat} (i : Fin n) (u : FinEl) ->
      Coherent u -> CoherentEnv (singletonEnv i u)
    singletonEnv-Coherent fzero u cu    = mkSigma botEnv-Coherent cu
    singletonEnv-Coherent (fsuc i) u cu = mkSigma (singletonEnv-Coherent i u cu) tt

    singletonEnv-lookup : {n : Nat} (i : Fin n) (u : FinEl) ->
      Coherent u -> LeCode u (lookupEnv i (singletonEnv i u))
    singletonEnv-lookup fzero u cu    = LeCode-refl u cu
    singletonEnv-lookup (fsuc i) u cu = singletonEnv-lookup i u cu

    singletonEnv-SubRel : {h n : Nat} (sigma : Sub h n)
      (rho : EnvApprox h) (i : Fin n) (u : FinEl) ->
      EvalRel (sigma i) rho u ->
      SubRel sigma rho (singletonEnv i u)
    singletonEnv-SubRel sigma rho fzero u ev fzero = ev
    singletonEnv-SubRel sigma rho fzero u ev (fsuc j) =
      Eq-transport (EvalRel (sigma (fsuc j)) rho)
        (Eq-sym (lookupEnv-botEnv j)) (EvalRel-Bot (sigma (fsuc j)) rho)
    singletonEnv-SubRel sigma rho (fsuc i) u ev fzero =
      EvalRel-Bot (sigma fzero) rho
    singletonEnv-SubRel sigma rho (fsuc i) u ev (fsuc j) =
      singletonEnv-SubRel (\ k -> sigma (fsuc k)) rho i u ev j

-- U: botEnv works
EvalRel-subst-forward-wit sigma U rho u crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) ev))

-- App Bot
EvalRel-subst-forward-wit sigma (App M N) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- App non-Bot: combine witness envs from M and N via supEnv
EvalRel-subst-forward-wit sigma (App M N) rho UCode crho
  (mkSigma v (mkSigma evN evM)) =
  let rN = EvalRel-subst-forward-wit sigma N rho v crho evN
      rM = EvalRel-subst-forward-wit sigma M rho _ crho evM
      rhoN = fst rN ; crhoN = fst (snd rN) ; srN = fst (snd (snd rN))
      evN' = snd (snd (snd rN))
      rhoM = fst rM ; crhoM = fst (snd rM) ; srM = fst (snd (snd rM))
      evM' = snd (snd (snd rM))
      comb = combineFwd sigma rho crho rhoM rhoN crhoM crhoN srM srN
      rho' = fst comb ; crho' = fst (snd comb)
      sr'  = fst (snd (snd comb))
      leM  = fst (snd (snd (snd comb)))
      leN  = snd (snd (snd (snd comb)))
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma v (mkSigma (EvalRel-mon-env N rhoN rho' v evN' leN)
                           (EvalRel-mon-env M rhoM rho' _ evM' leM)))))

EvalRel-subst-forward-wit sigma (App M N) rho (FunEl g') crho
  (mkSigma v (mkSigma evN evM)) =
  let rN = EvalRel-subst-forward-wit sigma N rho v crho evN
      rM = EvalRel-subst-forward-wit sigma M rho _ crho evM
      rhoN = fst rN ; crhoN = fst (snd rN) ; srN = fst (snd (snd rN))
      evN' = snd (snd (snd rN))
      rhoM = fst rM ; crhoM = fst (snd rM) ; srM = fst (snd (snd rM))
      evM' = snd (snd (snd rM))
      comb = combineFwd sigma rho crho rhoM rhoN crhoM crhoN srM srN
      rho' = fst comb ; crho' = fst (snd comb)
      sr'  = fst (snd (snd comb))
      leM  = fst (snd (snd (snd comb)))
      leN  = snd (snd (snd (snd comb)))
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma v (mkSigma (EvalRel-mon-env N rhoN rho' v evN' leN)
                           (EvalRel-mon-env M rhoM rho' _ evM' leM)))))

EvalRel-subst-forward-wit sigma (App M N) rho (PiCode a' f') crho
  (mkSigma v (mkSigma evN evM)) =
  let rN = EvalRel-subst-forward-wit sigma N rho v crho evN
      rM = EvalRel-subst-forward-wit sigma M rho _ crho evM
      rhoN = fst rN ; crhoN = fst (snd rN) ; srN = fst (snd (snd rN))
      evN' = snd (snd (snd rN))
      rhoM = fst rM ; crhoM = fst (snd rM) ; srM = fst (snd (snd rM))
      evM' = snd (snd (snd rM))
      comb = combineFwd sigma rho crho rhoM rhoN crhoM crhoN srM srN
      rho' = fst comb ; crho' = fst (snd comb)
      sr'  = fst (snd (snd comb))
      leM  = fst (snd (snd (snd comb)))
      leN  = snd (snd (snd (snd comb)))
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma v (mkSigma (EvalRel-mon-env N rhoN rho' v evN' leN)
                           (EvalRel-mon-env M rhoM rho' _ evM' leM)))))

-- Lam Bot
EvalRel-subst-forward-wit sigma (Lam A M) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Lam (FunEl g): use Lam-edgewise + fold over edges
EvalRel-subst-forward-wit sigma (Lam A M) rho (FunEl g) crho ev =
  let ew = Lam-edgewise (substExpr sigma A) (substExpr (liftSub sigma) M) rho g ev
      a     = fst ew
      cg    = fst (snd ew)
      aU    = fst (snd (snd ew))
      evA   = fst (snd (snd (snd ew)))
      edges = snd (snd (snd (snd ew)))
      -- IH on A
      rA    = EvalRel-subst-forward-wit sigma A rho a crho evA
      rhoA  = fst rA ; crhoA = fst (snd rA)
      srA   = fst (snd (snd rA)) ; evA' = snd (snd (snd rA))
      -- Fold over all edges in g to collect body environments
      fold  = foldEdgeFwd sigma rho M rhoA crho crhoA srA a g edges
      rho'  = fst fold
      crho' = fst (snd fold)
      sr'   = fst (snd (snd fold))
      leA   = fst (snd (snd (snd fold)))
      bodyAll = snd (snd (snd (snd fold)))
      -- Lift evA' from rhoA to rho'
      evA'' = EvalRel-mon-env A rhoA rho' a evA' leA
      -- Build the selection body from edgewise results
      selBody : (x v : FinEl) -> Selection g x v ->
        Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a) (EvalRel M (extendEnv rho' z) v)))
      selBody = sel-body-from-edges rho' crho' a aU g (cft-from-cf g cg) bodyAll
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA'' selBody))))))
  where
    -- Helper: extract Coherent for selection keys from CoherentFunTail
    sel-key-Coherent :
      (g0 : FinFun) -> CoherentFunTail g0 ->
      (x v : FinEl) -> Selection g0 x v -> Coherent x
    sel-key-Coherent .nil cft .Bot .Bot sel-nil = tt
    sel-key-Coherent .(cons _ _) cft x v (sel-skip {p} sel) =
      sel-key-Coherent _ (CFTcons.tail-coh cft) x v sel
    sel-key-Coherent .(cons p _) cft .(Sup (fst p) x0) .(Sup (snd p) v0)
      (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      Coherent-Sup (fst p) x0 comp-k
        (CFTcons.key-coh cft)
        (sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel)
    -- Rebuild selection body from per-edge evaluations
    sel-body-from-edges :
      (rho' : EnvApprox _) -> CoherentEnv rho' ->
      (a : FinEl) -> FinMem a UCode ->
      (g0 : FinFun) -> CoherentFunTail g0 ->
      ((p : Edge) -> EdgeIn p g0 ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst p))
          (Pair (FinMem z a) (EvalRel M (extendEnv rho' z) (snd p))))) ->
      (x v : FinEl) -> Selection g0 x v ->
      Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a)
        (EvalRel M (extendEnv rho' z) v)))
    sel-body-from-edges rho' crho' a aU0 .nil cft bodyMap .Bot .Bot sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma aU0 (EvalRel-Bot M (extendEnv rho' Bot))))
    sel-body-from-edges rho' crho' a aU0 .(cons _ _) cft bodyMap x v (sel-skip {p} sel) =
      sel-body-from-edges rho' crho' a aU0 _ (CFTcons.tail-coh cft)
        (\ q ein -> bodyMap q (there ein)) x v sel
    sel-body-from-edges rho' crho' a aU0 .(cons p _) cft bodyMap .(Sup (fst p) x0)
      .(Sup (snd p) v0) (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      let -- Edge p witness
          wp   = bodyMap p here
          zp   = fst wp
          lezp = fst (snd wp)
          memp = fst (snd (snd wp))
          evMp = snd (snd (snd wp))
          czp  = FinMem-coh-u zp a memp
          -- Coherence of fst p from CoherentFunTail
          cfp  = CFTcons.key-coh cft
          -- Recursive result for the rest
          rec   = sel-body-from-edges rho' crho' a aU0 _ (CFTcons.tail-coh cft)
                    (\ q ein -> bodyMap q (there ein)) x0 v0 sel
          zr    = fst rec
          lezr  = fst (snd rec)
          memr  = fst (snd (snd rec))
          evMr  = snd (snd (snd rec))
          czr   = FinMem-coh-u zr a memr
          -- Coherent x0 from recursive Selection
          cx0   = sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel
          -- Derive Comp zp zr from Comp (fst p) x0 via Comp-down
          comp-zp-x0 = Comp-down zp (fst p) x0 lezp comp-k
          comp-zp-zr = Comp-sym zr zp
                         (Comp-down zr x0 zp lezr (Comp-sym zp x0 comp-zp-x0))
          -- EvalRel M (extendEnv rho' (Sup zp zr)) (Sup (snd p) v0)
          evMsup = EvalRel-ideal-Comp M rho' zp zr (snd p) v0
                     crho' comp-zp-zr czp czr evMp evMr
          -- FinMem (Sup zp zr) a
          ca     = FinMem-coh-a zp a memp
          memsup = FinMem-Sup-element zp zr a comp-zp-zr ca memp memr
          -- LeCode (Sup zp zr) (Sup (fst p) x0)
          cSup   = Coherent-Sup (fst p) x0 comp-k cfp cx0
          lesup  = LeCode-Sup-lub zp zr (Sup (fst p) x0)
                     (LeCode-trans zp (fst p) (Sup (fst p) x0)
                       czp cfp cSup lezp
                       (LeCode-Sup-left (fst p) x0 comp-k cfp cx0))
                     (LeCode-trans zr x0 (Sup (fst p) x0)
                       czr cx0 cSup lezr
                       (LeCode-Sup-right (fst p) x0 comp-k cfp cx0))
      in mkSigma (Sup zp zr) (mkSigma lesup (mkSigma memsup evMsup))

-- Lam UCode: absurd
EvalRel-subst-forward-wit sigma (Lam A M) rho UCode crho ()

-- Lam (PiCode a f): absurd
EvalRel-subst-forward-wit sigma (Lam A M) rho (PiCode a f) crho ()

-- Pi Bot
EvalRel-subst-forward-wit sigma (Pi A B) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Pi (PiCode a f): use Pi-edgewise + fold over edges
EvalRel-subst-forward-wit sigma (Pi A B) rho (PiCode a f) crho ev =
  let pew = Pi-edgewise (substExpr sigma A) (substExpr (liftSub sigma) B) rho a f ev
      caf   = fst pew
      evA   = fst (snd pew)
      a'    = fst (snd (snd pew))
      evA'e = fst (snd (snd (snd pew)))
      edges = snd (snd (snd (snd pew)))
      -- IH on A for both a and a'
      rAa   = EvalRel-subst-forward-wit sigma A rho a crho evA
      rhoAa = fst rAa ; crhoAa = fst (snd rAa)
      srAa  = fst (snd (snd rAa)) ; evAa = snd (snd (snd rAa))
      rAa'  = EvalRel-subst-forward-wit sigma A rho a' crho evA'e
      rhoAa' = fst rAa' ; crhoAa' = fst (snd rAa')
      srAa'  = fst (snd (snd rAa')) ; evAa'0 = snd (snd (snd rAa'))
      -- Combine rhoAa and rhoAa'
      combA = combineFwd sigma rho crho rhoAa rhoAa' crhoAa crhoAa' srAa srAa'
      rhoAc = fst combA ; crhoAc = fst (snd combA)
      srAc  = fst (snd (snd combA))
      leAa  = fst (snd (snd (snd combA)))
      leAa' = snd (snd (snd (snd combA)))
      -- Fold over all edges in f to collect body environments
      cf    = snd caf
      fold  = foldEdgeFwd sigma rho B rhoAc crho crhoAc srAc a' f edges
      rho'  = fst fold
      crho' = fst (snd fold)
      sr'   = fst (snd (snd fold))
      leAc  = fst (snd (snd (snd fold)))
      bodyAll = snd (snd (snd (snd fold)))
      -- Lift evAa and evAa'0 to rho'
      leAa-rho' = EnvLe-trans rhoAa rhoAc rho' leAa leAc
      leAa'-rho' = EnvLe-trans rhoAa' rhoAc rho' leAa' leAc
      evAa-rho'  = EvalRel-mon-env A rhoAa rho' a evAa leAa-rho'
      evAa'-rho' = EvalRel-mon-env A rhoAa' rho' a' evAa'0 leAa'-rho'
      -- Extract FinMem a' UCode from first edge (f is non-nil since CoherentFun f)
      a'U   = extractFinMemU a' f cf bodyAll
      -- Build the selection body
      selBody : (x v : FinEl) -> Selection f x v ->
        Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a') (EvalRel B (extendEnv rho' z) v)))
      selBody = pi-sel-body rho' crho' a' a'U f (cft-from-cf f cf) bodyAll
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma caf (mkSigma evAa-rho'
         (mkSigma a' (mkSigma evAa'-rho' selBody))))))
  where
    -- Helper: extract Coherent for selection keys from CoherentFunTail
    pi-sel-key-Coherent :
      (g0 : FinFun) -> CoherentFunTail g0 ->
      (x v : FinEl) -> Selection g0 x v -> Coherent x
    pi-sel-key-Coherent .nil cft .Bot .Bot sel-nil = tt
    pi-sel-key-Coherent .(cons _ _) cft x v (sel-skip {p} sel) =
      pi-sel-key-Coherent _ (CFTcons.tail-coh cft) x v sel
    pi-sel-key-Coherent .(cons p _) cft .(Sup (fst p) x0) .(Sup (snd p) v0)
      (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      Coherent-Sup (fst p) x0 comp-k
        (CFTcons.key-coh cft)
        (pi-sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel)
    -- Rebuild selection body for Pi case
    pi-sel-body :
      (rho' : EnvApprox _) -> CoherentEnv rho' ->
      (a' : FinEl) -> FinMem a' UCode ->
      (g0 : FinFun) -> CoherentFunTail g0 ->
      ((p : Edge) -> EdgeIn p g0 ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst p))
          (Pair (FinMem z a') (EvalRel B (extendEnv rho' z) (snd p))))) ->
      (x v : FinEl) -> Selection g0 x v ->
      Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a')
        (EvalRel B (extendEnv rho' z) v)))
    pi-sel-body rho' crho' a' a'U0 .nil cft bodyMap .Bot .Bot sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma a'U0 (EvalRel-Bot B (extendEnv rho' Bot))))
    pi-sel-body rho' crho' a' a'U0 .(cons _ _) cft bodyMap x v (sel-skip {p} sel) =
      pi-sel-body rho' crho' a' a'U0 _ (CFTcons.tail-coh cft)
        (\ q ein -> bodyMap q (there ein)) x v sel
    pi-sel-body rho' crho' a' a'U0 .(cons p _) cft bodyMap .(Sup (fst p) x0)
      .(Sup (snd p) v0) (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      let wp   = bodyMap p here
          zp   = fst wp
          lezp = fst (snd wp)
          memp = fst (snd (snd wp))
          evBp = snd (snd (snd wp))
          czp  = FinMem-coh-u zp a' memp
          cfp  = CFTcons.key-coh cft
          rec   = pi-sel-body rho' crho' a' a'U0 _ (CFTcons.tail-coh cft)
                    (\ q ein -> bodyMap q (there ein)) x0 v0 sel
          zr    = fst rec
          lezr  = fst (snd rec)
          memr  = fst (snd (snd rec))
          evBr  = snd (snd (snd rec))
          czr   = FinMem-coh-u zr a' memr
          cx0   = pi-sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel
          comp-zp-x0 = Comp-down zp (fst p) x0 lezp comp-k
          comp-zp-zr = Comp-sym zr zp
                         (Comp-down zr x0 zp lezr (Comp-sym zp x0 comp-zp-x0))
          evBsup = EvalRel-ideal-Comp B rho' zp zr (snd p) v0
                     crho' comp-zp-zr czp czr evBp evBr
          ca'    = FinMem-coh-a zp a' memp
          memsup = FinMem-Sup-element zp zr a' comp-zp-zr ca' memp memr
          cSup   = Coherent-Sup (fst p) x0 comp-k cfp cx0
          lesup  = LeCode-Sup-lub zp zr (Sup (fst p) x0)
                     (LeCode-trans zp (fst p) (Sup (fst p) x0)
                       czp cfp cSup lezp
                       (LeCode-Sup-left (fst p) x0 comp-k cfp cx0))
                     (LeCode-trans zr x0 (Sup (fst p) x0)
                       czr cx0 cSup lezr
                       (LeCode-Sup-right (fst p) x0 comp-k cfp cx0))
      in mkSigma (Sup zp zr) (mkSigma lesup (mkSigma memsup evBsup))

-- Pi UCode: absurd
EvalRel-subst-forward-wit sigma (Pi A B) rho UCode crho ()

-- Pi (FunEl g): absurd
EvalRel-subst-forward-wit sigma (Pi A B) rho (FunEl g) crho ()

------------------------------------------------------------------------
-- Part 11: EnvLe from pointwise conditions
------------------------------------------------------------------------

envLe-from-pointwise : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  ((i : Fin n) -> Pair (Coherent (lookupEnv i rho1))
    (Pair (Coherent (lookupEnv i rho2))
          (LeCode (lookupEnv i rho1) (lookupEnv i rho2)))) ->
  EnvLe rho1 rho2
envLe-from-pointwise emptyEnv emptyEnv f = tt
envLe-from-pointwise (extendEnv rho1 u1) (extendEnv rho2 u2) f =
  mkSigma (envLe-from-pointwise rho1 rho2 (\ i -> f (fsuc i)))
    (mkSigma (fst (f fzero))
      (mkSigma (fst (snd (f fzero)))
               (snd (snd (f fzero)))))

------------------------------------------------------------------------
-- Part 12: Forward substitution for subst1 (existential witness)
------------------------------------------------------------------------

EvalRel-subst1-forward :
  {n : Nat} ->
  (M : Expr (suc n)) ->
  (N : Expr n) ->
  (rho : EnvApprox n) ->
  (u : FinEl) ->
  CoherentEnv rho ->
  EvalRel (subst1 M N) rho u ->
  Sigma FinEl (\ v ->
    Pair (EvalRel N rho v)
         (EvalRel M (extendEnv rho v) u))
EvalRel-subst1-forward M N rho u crho ev =
  let r    = EvalRel-subst-forward-wit (subst1Sub N) M rho u crho ev
      rho' = fst r
      crho' = fst (snd r)
      sr    = fst (snd (snd r))
      evM   = snd (snd (snd r))
      v     = lookupEnv fzero rho'
      cv    = lookupEnv-coh fzero rho' crho'
      evN   = sr fzero
      -- Build EnvLe rho' (extendEnv rho v)
      -- At fzero: v <= v (refl)
      -- At fsuc i: sr (fsuc i) : EvalRel (Var i) rho (lookupEnv (fsuc i) rho')
      --   gives Coherent (lookupEnv (fsuc i) rho') and LeCode ... <= lookupEnv i rho
      envle = envLe-from-pointwise rho' (extendEnv rho v)
        (\ { fzero -> mkSigma cv (mkSigma cv (LeCode-refl v cv))
           ; (fsuc i) -> mkSigma (fst (sr (fsuc i)))
                           (mkSigma (lookupEnv-coh i rho crho)
                                    (snd (sr (fsuc i))))
           })
      evM'  = EvalRel-mon-env M rho' (extendEnv rho v) u evM envle
  in mkSigma v (mkSigma evN evM')

------------------------------------------------------------------------
-- Part 11: EvalRel-Pi-app-type
--
-- If EvalRel (Pi A B) rho (PiCode b f) and EvalRel a rho v,
-- then EvalRel (subst1 B a) rho (EvalFun f v).
--
-- Proof: Pi-edgewise gives per-edge EvalRel B witnesses. By list
-- induction on f, combine firing-edge witnesses via EvalRel-Sup to
-- build EvalRel B (extendEnv rho v) (EvalFun f v), then apply
-- EvalRel-subst1-backward.
------------------------------------------------------------------------

-- Helper: by list induction on f, build EvalRel B (extendEnv rho v) (EvalFun f v)
-- from per-edge witnesses.
mutual
 EvalRel-body-EvalFun :
  {n : Nat} (B : Expr (suc n)) (rho : EnvApprox n) (v : FinEl)
  (a' : FinEl) (f : FinFun) ->
  CoherentEnv rho -> Coherent v -> CoherentFunTail f ->
  ((p : Edge) -> EdgeIn p f ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a')
                 (EvalRel B (extendEnv rho x) (snd p))))) ->
  EvalRel B (extendEnv rho v) (EvalFun f v)
 EvalRel-body-EvalFun B rho v a' nil crho cv cft wf = EvalRel-Bot B (extendEnv rho v)
 EvalRel-body-EvalFun B rho v a' (cons q rest) crho cv cft wf =
  EvalRel-body-EvalFun-step (leFinEl (fst q) v) B rho v a' q rest
    crho cv cft refl wf

 EvalRel-body-EvalFun-step :
  (k : Nat) ->
  {n : Nat} (B : Expr (suc n)) (rho : EnvApprox n) (v : FinEl)
  (a' : FinEl) (q : Edge) (rest : FinFun) ->
  CoherentEnv rho -> Coherent v -> CoherentFunTail (cons q rest) ->
  Eq k (leFinEl (fst q) v) ->
  ((p : Edge) -> EdgeIn p (cons q rest) ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a')
                 (EvalRel B (extendEnv rho x) (snd p))))) ->
  EvalRel B (extendEnv rho v) (EvalFun-step k (snd q) rest v)
 -- Non-firing edge: skip to rest
 EvalRel-body-EvalFun-step zero B rho v a' q rest crho cv cft eq wf =
  EvalRel-body-EvalFun B rho v a' rest crho cv (CFTcons.tail-coh cft)
    (\ p ein -> wf p (there ein))
 -- Firing edge: Sup (snd q) (EvalFun rest v)
 EvalRel-body-EvalFun-step (suc _) B rho v a' q rest crho cv cft eq wf =
  let -- IH for rest
      ih = EvalRel-body-EvalFun B rho v a' rest crho cv
             (CFTcons.tail-coh cft)
             (\ p ein -> wf p (there ein))
      -- Edge witness for q
      w      = wf q here
      x      = fst w
      le-x-u = fst (snd w)
      mem    = fst (snd (snd w))
      evB-x  = snd (snd (snd w))
      -- x <= fst q <= v
      cx  = FinMem-coh-u x a' mem
      cqu = CFTcons.key-coh cft
      le-qu-v = leFinEl-sound (fst q) v (Eq-transport isPos eq tt)
      le-x-v  = LeCode-trans x (fst q) v cx cqu cv le-x-u le-qu-v
      -- Transport EvalRel B from (rho, x) to (rho, v)
      envle = mkSigma (EnvLe-refl rho crho)
                (mkSigma cx (mkSigma cv le-x-v))
      evB-v = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho v)
                (snd q) evB-x envle
      -- Combine via EvalRel-Sup
      crho-v = mkSigma crho cv
      cohv = EvalRel-coh B (extendEnv rho v) (snd q) evB-v
      coh-rest = Coherent-EvalFun rest v (CFTcons.tail-coh cft) cv
      comp-vr = Comp-value-EvalFun q rest v le-qu-v cv
                  (CFTcons.val-coh cft)
                  (CFTcons.compat cft)
                  (coherentWith-to-compStepFun q rest (CFTcons.compat cft))
  in EvalRel-Sup B (extendEnv rho v) (snd q) (EvalFun rest v)
       crho-v cohv coh-rest comp-vr evB-v ih

-- Main theorem
EvalRel-Pi-app-type :
  {n : Nat} (A : Expr n) (B : Expr (suc n)) (a : Expr n)
  (rho : EnvApprox n) (b : FinEl) (f : FinFun) (v : FinEl) ->
  CoherentEnv rho ->
  EvalRel (Pi A B) rho (PiCode b f) ->
  EvalRel a rho v ->
  EvalRel (subst1 B a) rho (EvalFun f v)
EvalRel-Pi-app-type A B a rho b f v crho evPi eva =
  let -- Pi-edgewise decomposition
      pew  = Pi-edgewise A B rho b f evPi
      caf  = fst pew
      a'   = fst (snd (snd pew))
      wf   = snd (snd (snd (snd pew)))
      -- Coherence
      cf   = snd caf
      cft  = cft-from-cf f cf
      cv   = EvalRel-coh a rho v eva
      -- Build EvalRel B (extendEnv rho v) (EvalFun f v)
      evB  = EvalRel-body-EvalFun B rho v a' f crho cv cft wf
  in EvalRel-subst1-backward B a rho v (EvalFun f v) crho eva evB

-- EvalRel-Pi-body: from Pi evaluation, derive EvalRel B (extendEnv rho v) (EvalFun f v)
-- This is the intermediate step of EvalRel-Pi-app-type, before applying subst1-backward.
EvalRel-Pi-body :
  {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (b : FinEl) (f : FinFun) (v : FinEl) ->
  CoherentEnv rho -> Coherent v ->
  EvalRel (Pi A B) rho (PiCode b f) ->
  EvalRel B (extendEnv rho v) (EvalFun f v)
EvalRel-Pi-body A B rho b f v crho cv evPi =
  let pew  = Pi-edgewise A B rho b f evPi
      caf  = fst pew
      a'   = fst (snd (snd pew))
      wf   = snd (snd (snd (snd pew)))
      cf   = snd caf
      cft  = cft-from-cf f cf
  in EvalRel-body-EvalFun B rho v a' f crho cv cft wf
