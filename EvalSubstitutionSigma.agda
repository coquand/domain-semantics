{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- EvalSubstitutionSigma.agda
--
-- Parallel version of EvalSubstitution.agda extended with Sigma types.
--
-- Architecture:
--   1. EvalRel-ren / EvalRel-ren-inv — renaming preserves evaluation
--   2. EvalRel-wk / EvalRel-unwk     — weakening as corollary
--   3. SubRel                         — semantic substitution relation
--   4. EvalRel-subst                  — general substitution (backward)
--   5. SubRel-subst1                  — SubRel for [M/0]
--   6. EvalRel-subst1-backward        — unary substitution (backward)
--   7. MaxSubRel / MaxSubRel-lift     — maximal substitution relation
--   8. EvalRel-subst-forward-max      — general forward substitution
--   9. EvalRel-subst1-forward-bounded — unary forward with explicit bound
--  10. EvalRel-subst-forward-wit      — forward with witness environment
--  11. EvalRel-subst1-forward         — unary forward (existential witness)
--  12. EvalRel-Pi-app-type / EvalRel-Pi-body
--
-- NO postulates.
------------------------------------------------------------------------

module EvalSubstitutionSigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ; isPos)
open import PaperSemanticsSigma using (LeCode ; LeCode-refl ; LeCode-trans ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  Comp ; Comp-down ; Comp-sym ;
  Sup ; Sup-Bot-l ; Sup-Bot-r ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-Sup-lub ; FinMem-Sup-element ;
  FinMem ; FinMem-coh-u ; FinMem-coh-a ; FinMem-a-in-U ;
  EvalFun ; EvalFun-step ; leFinEl ; leFinEl-sound ;
  Coherent-EvalFun ; Comp-value-EvalFun ;
  coherentWith-to-compStepFun ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMemAllU ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ;
  LeCode-Bot ; LeCode-Comp ;
  EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append ;
  Or ; inl ; inr ;
  fstEl ; sndEl ;
  NotBot-Sup-Comp ; Or-NotBot-Sup)
open import RawSemanticsSigma using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EnvLe-extend-left ; EnvLe-extend-right ;
  EnvLe-extend ;
  EvalRel-Bot ; EvalRel-Comp ; EvalRel-Sup ;
  EvalRel-ideal-Comp ;
  Lam-edgewise ; Pi-edgewise ; Sigma-edgewise ;
  App-decompose ;
  lookupEnv-coh-left ; lookupEnv-coh-right ; lookupEnv-mon)
open S using (List ; nil ; cons)
open import SelectionSigma using (Edge ; EdgeIn ; here ; there ; Selection ;
  sel-nil ; sel-skip ; sel-take ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import RawSyntaxSigma hiding (Sigma)

------------------------------------------------------------------------
-- Part 1: Renaming preserves evaluation
------------------------------------------------------------------------

RenAgree : {n m : Nat} -> Ren n m -> EnvApprox n -> EnvApprox m -> Set
RenAgree {n} r rho rho' = (i : Fin n) -> Eq (lookupEnv (r i) rho') (lookupEnv i rho)

liftRen-agree : {n m : Nat} (r : Ren n m)
  (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (x : FinEl) ->
  RenAgree (liftRen r) (extendEnv rho x) (extendEnv rho' x)
liftRen-agree r rho rho' eq x fzero    = refl
liftRen-agree r rho rho' eq x (fsuc i) = eq i

EvalRel-ren : {n m : Nat} (r : Ren n m)
  (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' -> (u : FinEl) ->
  EvalRel M rho u -> EvalRel (renExpr r M) rho' u

-- Var
EvalRel-ren r (Var i) rho rho' eq u (mkSigma cu le) =
  mkSigma cu (Eq-transport (\ z -> LeCode u z) (Eq-sym (eq i)) le)

-- U
EvalRel-ren r U rho rho' eq u ev = ev

-- Prop
EvalRel-ren r Prop rho rho' eq u ev = ev

-- App Bot
EvalRel-ren r (App M N) rho rho' eq Bot ev = tt

-- App non-Bot
EvalRel-ren r (App M N) rho rho' eq UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq PropCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (SigmaCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))
EvalRel-ren r (App M N) rho rho' eq (PairCode u' v')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren r N rho rho' eq v evN)
                      (EvalRel-ren r M rho rho' eq _ evM))

-- Lam Bot
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

-- Lam absurd
EvalRel-ren r (Lam A M) rho rho' eq UCode ()
EvalRel-ren r (Lam A M) rho rho' eq PropCode ()
EvalRel-ren r (Lam A M) rho rho' eq (PiCode a f) ()
EvalRel-ren r (Lam A M) rho rho' eq (SigmaCode a f) ()
EvalRel-ren r (Lam A M) rho rho' eq (PairCode u v) ()

-- Pi Bot
EvalRel-ren r (Pi A B) rho rho' eq Bot ev = tt

-- Pi (PiCode a f)
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

-- Pi absurd
EvalRel-ren r (Pi A B) rho rho' eq UCode ()
EvalRel-ren r (Pi A B) rho rho' eq PropCode ()
EvalRel-ren r (Pi A B) rho rho' eq (FunEl g) ()
EvalRel-ren r (Pi A B) rho rho' eq (SigmaCode a f) ()
EvalRel-ren r (Pi A B) rho rho' eq (PairCode u v) ()

-- Sigma Bot
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq Bot ev = tt

-- Sigma (SigmaCode a f)
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq (SigmaCode a f)
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

-- Sigma absurd
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq UCode ()
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq PropCode ()
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq (FunEl g) ()
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq (PiCode a f) ()
EvalRel-ren r (RawSyntaxSigma.Sigma A B) rho rho' eq (PairCode u v) ()

-- MkPair Bot
EvalRel-ren r (MkPair M N) rho rho' eq Bot ev = tt

-- MkPair (PairCode u v)
EvalRel-ren r (MkPair M N) rho rho' eq (PairCode u v)
  (mkSigma cuv (mkSigma evM evN)) =
  mkSigma cuv (mkSigma (EvalRel-ren r M rho rho' eq u evM)
                        (EvalRel-ren r N rho rho' eq v evN))

-- MkPair absurd
EvalRel-ren r (MkPair M N) rho rho' eq UCode ()
EvalRel-ren r (MkPair M N) rho rho' eq PropCode ()
EvalRel-ren r (MkPair M N) rho rho' eq (FunEl g) ()
EvalRel-ren r (MkPair M N) rho rho' eq (PiCode a f) ()
EvalRel-ren r (MkPair M N) rho rho' eq (SigmaCode a f) ()

-- Fst Bot
EvalRel-ren r (Fst M) rho rho' eq Bot ev = tt

-- Fst non-Bot
EvalRel-ren r (Fst M) rho rho' eq UCode (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode UCode v) evM)
EvalRel-ren r (Fst M) rho rho' eq PropCode (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode PropCode v) evM)
EvalRel-ren r (Fst M) rho rho' eq (FunEl g) (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode (FunEl g) v) evM)
EvalRel-ren r (Fst M) rho rho' eq (PiCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode (PiCode a f) v) evM)
EvalRel-ren r (Fst M) rho rho' eq (SigmaCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode (SigmaCode a f) v) evM)
EvalRel-ren r (Fst M) rho rho' eq (PairCode u' v') (mkSigma v evM) =
  mkSigma v (EvalRel-ren r M rho rho' eq (PairCode (PairCode u' v') v) evM)

-- Snd Bot
EvalRel-ren r (Snd M) rho rho' eq Bot ev = tt

-- Snd non-Bot
EvalRel-ren r (Snd M) rho rho' eq UCode (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u UCode) evM)
EvalRel-ren r (Snd M) rho rho' eq PropCode (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u PropCode) evM)
EvalRel-ren r (Snd M) rho rho' eq (FunEl g) (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u (FunEl g)) evM)
EvalRel-ren r (Snd M) rho rho' eq (PiCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u (PiCode a f)) evM)
EvalRel-ren r (Snd M) rho rho' eq (SigmaCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u (SigmaCode a f)) evM)
EvalRel-ren r (Snd M) rho rho' eq (PairCode u' v') (mkSigma u evM) =
  mkSigma u (EvalRel-ren r M rho rho' eq (PairCode u (PairCode u' v')) evM)

------------------------------------------------------------------------
-- Part 1b: Inverse renaming
------------------------------------------------------------------------

EvalRel-ren-inv : {n m : Nat} (r : Ren n m)
  (M : Expr n) (rho : EnvApprox n) (rho' : EnvApprox m) ->
  RenAgree r rho rho' ->
  (u : FinEl) -> EvalRel (renExpr r M) rho' u -> EvalRel M rho u

EvalRel-ren-inv r (Var i) rho rho' eq u (mkSigma cu le) =
  mkSigma cu (Eq-transport (LeCode u) (eq i) le)

EvalRel-ren-inv r U rho rho' eq u ev = ev

EvalRel-ren-inv r Prop rho rho' eq u ev = ev

EvalRel-ren-inv r (App M N) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (App M N) rho rho' eq UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq PropCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (SigmaCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-ren-inv r N rho rho' eq v evN)
                      (EvalRel-ren-inv r M rho rho' eq _ evM))
EvalRel-ren-inv r (App M N) rho rho' eq (PairCode u' v')
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
EvalRel-ren-inv r (Lam A M) rho rho' eq PropCode ()
EvalRel-ren-inv r (Lam A M) rho rho' eq (PiCode a f) ()
EvalRel-ren-inv r (Lam A M) rho rho' eq (SigmaCode a f) ()
EvalRel-ren-inv r (Lam A M) rho rho' eq (PairCode u v) ()

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
EvalRel-ren-inv r (Pi A B) rho rho' eq PropCode ()
EvalRel-ren-inv r (Pi A B) rho rho' eq (FunEl g) ()
EvalRel-ren-inv r (Pi A B) rho rho' eq (SigmaCode a f) ()
EvalRel-ren-inv r (Pi A B) rho rho' eq (PairCode u v) ()

-- Sigma
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq (SigmaCode a f)
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
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq UCode ()
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq PropCode ()
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq (FunEl g) ()
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq (PiCode a f) ()
EvalRel-ren-inv r (RawSyntaxSigma.Sigma A B) rho rho' eq (PairCode u v) ()

-- MkPair
EvalRel-ren-inv r (MkPair M N) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (MkPair M N) rho rho' eq (PairCode u v)
  (mkSigma cuv (mkSigma evM evN)) =
  mkSigma cuv (mkSigma (EvalRel-ren-inv r M rho rho' eq u evM)
                        (EvalRel-ren-inv r N rho rho' eq v evN))
EvalRel-ren-inv r (MkPair M N) rho rho' eq UCode ()
EvalRel-ren-inv r (MkPair M N) rho rho' eq PropCode ()
EvalRel-ren-inv r (MkPair M N) rho rho' eq (FunEl g) ()
EvalRel-ren-inv r (MkPair M N) rho rho' eq (PiCode a f) ()
EvalRel-ren-inv r (MkPair M N) rho rho' eq (SigmaCode a f) ()

-- Fst
EvalRel-ren-inv r (Fst M) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (Fst M) rho rho' eq UCode (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode UCode v) evM)
EvalRel-ren-inv r (Fst M) rho rho' eq PropCode (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode PropCode v) evM)
EvalRel-ren-inv r (Fst M) rho rho' eq (FunEl g) (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode (FunEl g) v) evM)
EvalRel-ren-inv r (Fst M) rho rho' eq (PiCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode (PiCode a f) v) evM)
EvalRel-ren-inv r (Fst M) rho rho' eq (SigmaCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode (SigmaCode a f) v) evM)
EvalRel-ren-inv r (Fst M) rho rho' eq (PairCode u' v') (mkSigma v evM) =
  mkSigma v (EvalRel-ren-inv r M rho rho' eq (PairCode (PairCode u' v') v) evM)

-- Snd
EvalRel-ren-inv r (Snd M) rho rho' eq Bot ev = tt
EvalRel-ren-inv r (Snd M) rho rho' eq UCode (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u UCode) evM)
EvalRel-ren-inv r (Snd M) rho rho' eq PropCode (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u PropCode) evM)
EvalRel-ren-inv r (Snd M) rho rho' eq (FunEl g) (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u (FunEl g)) evM)
EvalRel-ren-inv r (Snd M) rho rho' eq (PiCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u (PiCode a f)) evM)
EvalRel-ren-inv r (Snd M) rho rho' eq (SigmaCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u (SigmaCode a f)) evM)
EvalRel-ren-inv r (Snd M) rho rho' eq (PairCode u' v') (mkSigma u evM) =
  mkSigma u (EvalRel-ren-inv r M rho rho' eq (PairCode u (PairCode u' v')) evM)

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

SubRel : {h g : Nat} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
SubRel {h} {g} sigma rho rho' =
  (i : Fin g) -> EvalRel (sigma i) rho (lookupEnv i rho')

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
------------------------------------------------------------------------

EvalRel-subst : {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho ->
  SubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel M rho' u -> EvalRel (substExpr sigma M) rho u

-- Var
EvalRel-subst sigma (Var i) rho rho' crho sr u (mkSigma cu le) =
  EvalRel-down (sigma i) rho (lookupEnv i rho') u crho cu (sr i) le

-- U
EvalRel-subst sigma U rho rho' crho sr u ev = ev

-- Prop
EvalRel-subst sigma Prop rho rho' crho sr u ev = ev

-- App Bot
EvalRel-subst sigma (App M N) rho rho' crho sr Bot ev = tt

-- App non-Bot
EvalRel-subst sigma (App M N) rho rho' crho sr UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr PropCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (SigmaCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))
EvalRel-subst sigma (App M N) rho rho' crho sr (PairCode u' v')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst sigma N rho rho' crho sr v evN)
                      (EvalRel-subst sigma M rho rho' crho sr _ evM))

-- Lam Bot
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

-- Lam absurd
EvalRel-subst sigma (Lam A M) rho rho' crho sr UCode ()
EvalRel-subst sigma (Lam A M) rho rho' crho sr PropCode ()
EvalRel-subst sigma (Lam A M) rho rho' crho sr (PiCode a f) ()
EvalRel-subst sigma (Lam A M) rho rho' crho sr (SigmaCode a f) ()
EvalRel-subst sigma (Lam A M) rho rho' crho sr (PairCode u v) ()

-- Pi Bot
EvalRel-subst sigma (Pi A B) rho rho' crho sr Bot ev = tt

-- Pi (PiCode a f)
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

-- Pi absurd
EvalRel-subst sigma (Pi A B) rho rho' crho sr UCode ()
EvalRel-subst sigma (Pi A B) rho rho' crho sr PropCode ()
EvalRel-subst sigma (Pi A B) rho rho' crho sr (FunEl g) ()
EvalRel-subst sigma (Pi A B) rho rho' crho sr (SigmaCode a f) ()
EvalRel-subst sigma (Pi A B) rho rho' crho sr (PairCode u v) ()

-- Sigma Bot
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr Bot ev = tt

-- Sigma (SigmaCode a f)
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr (SigmaCode a f)
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

-- Sigma absurd
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr UCode ()
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr PropCode ()
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr (FunEl g) ()
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr (PiCode a f) ()
EvalRel-subst sigma (RawSyntaxSigma.Sigma A B) rho rho' crho sr (PairCode u v) ()

-- MkPair Bot
EvalRel-subst sigma (MkPair M N) rho rho' crho sr Bot ev = tt

-- MkPair (PairCode u v)
EvalRel-subst sigma (MkPair M N) rho rho' crho sr (PairCode u v)
  (mkSigma cuv (mkSigma evM evN)) =
  mkSigma cuv (mkSigma (EvalRel-subst sigma M rho rho' crho sr u evM)
                        (EvalRel-subst sigma N rho rho' crho sr v evN))

-- MkPair absurd
EvalRel-subst sigma (MkPair M N) rho rho' crho sr UCode ()
EvalRel-subst sigma (MkPair M N) rho rho' crho sr PropCode ()
EvalRel-subst sigma (MkPair M N) rho rho' crho sr (FunEl g) ()
EvalRel-subst sigma (MkPair M N) rho rho' crho sr (PiCode a f) ()
EvalRel-subst sigma (MkPair M N) rho rho' crho sr (SigmaCode a f) ()

-- Fst Bot
EvalRel-subst sigma (Fst M) rho rho' crho sr Bot ev = tt

-- Fst non-Bot
EvalRel-subst sigma (Fst M) rho rho' crho sr UCode (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode UCode v) evM)
EvalRel-subst sigma (Fst M) rho rho' crho sr PropCode (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode PropCode v) evM)
EvalRel-subst sigma (Fst M) rho rho' crho sr (FunEl g) (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode (FunEl g) v) evM)
EvalRel-subst sigma (Fst M) rho rho' crho sr (PiCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode (PiCode a f) v) evM)
EvalRel-subst sigma (Fst M) rho rho' crho sr (SigmaCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode (SigmaCode a f) v) evM)
EvalRel-subst sigma (Fst M) rho rho' crho sr (PairCode u' v') (mkSigma v evM) =
  mkSigma v (EvalRel-subst sigma M rho rho' crho sr (PairCode (PairCode u' v') v) evM)

-- Snd Bot
EvalRel-subst sigma (Snd M) rho rho' crho sr Bot ev = tt

-- Snd non-Bot
EvalRel-subst sigma (Snd M) rho rho' crho sr UCode (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u UCode) evM)
EvalRel-subst sigma (Snd M) rho rho' crho sr PropCode (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u PropCode) evM)
EvalRel-subst sigma (Snd M) rho rho' crho sr (FunEl g) (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u (FunEl g)) evM)
EvalRel-subst sigma (Snd M) rho rho' crho sr (PiCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u (PiCode a f)) evM)
EvalRel-subst sigma (Snd M) rho rho' crho sr (SigmaCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u (SigmaCode a f)) evM)
EvalRel-subst sigma (Snd M) rho rho' crho sr (PairCode u' v') (mkSigma u evM) =
  mkSigma u (EvalRel-subst sigma M rho rho' crho sr (PairCode u (PairCode u' v')) evM)

------------------------------------------------------------------------
-- Part 5: SubRel for unary substitution
------------------------------------------------------------------------

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

MaxSubRel : {h g : Nat} -> Sub h g -> EnvApprox h -> EnvApprox g -> Set
MaxSubRel {h} {g} sigma rho rho' =
  (i : Fin g) (u : FinEl) -> EvalRel (sigma i) rho u ->
  LeCode u (lookupEnv i rho')

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

-- Prop
EvalRel-subst-forward-max sigma Prop rho rho' crho crho' msr u ev = ev

-- App Bot
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr Bot ev = tt

-- App non-Bot
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr UCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (FunEl g')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr PropCode
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (PiCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (SigmaCode a' f')
  (mkSigma v (mkSigma evN evM)) =
  mkSigma v (mkSigma (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN)
                      (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr _ evM))
EvalRel-subst-forward-max sigma (App M N) rho rho' crho crho' msr (PairCode u' v')
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

-- Lam absurd
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr UCode ()
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr PropCode ()
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr (PiCode a f) ()
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr (SigmaCode a f) ()
EvalRel-subst-forward-max sigma (Lam A M) rho rho' crho crho' msr (PairCode u v) ()

-- Pi Bot
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr Bot ev = tt

-- Pi (PiCode a f)
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

-- Pi absurd
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr UCode ()
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr PropCode ()
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr (FunEl g) ()
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr (SigmaCode a f) ()
EvalRel-subst-forward-max sigma (Pi A B) rho rho' crho crho' msr (PairCode u v) ()

-- Sigma Bot
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr Bot ev = tt

-- Sigma (SigmaCode a f)
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr (SigmaCode a f)
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

-- Sigma absurd
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr UCode ()
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr PropCode ()
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr (FunEl g) ()
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr (PiCode a f) ()
EvalRel-subst-forward-max sigma (RawSyntaxSigma.Sigma A B) rho rho' crho crho' msr (PairCode u v) ()

-- MkPair Bot
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr Bot ev = tt

-- MkPair (PairCode u v)
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr (PairCode u v)
  (mkSigma cuv (mkSigma evM evN)) =
  mkSigma cuv (mkSigma (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr u evM)
                        (EvalRel-subst-forward-max sigma N rho rho' crho crho' msr v evN))

-- MkPair absurd
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr UCode ()
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr PropCode ()
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr (FunEl g) ()
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr (PiCode a f) ()
EvalRel-subst-forward-max sigma (MkPair M N) rho rho' crho crho' msr (SigmaCode a f) ()

-- Fst Bot
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr Bot ev = tt

-- Fst non-Bot
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr UCode (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode UCode v) evM)
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr PropCode (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode PropCode v) evM)
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr (FunEl g) (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode (FunEl g) v) evM)
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr (PiCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode (PiCode a f) v) evM)
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr (SigmaCode a f) (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode (SigmaCode a f) v) evM)
EvalRel-subst-forward-max sigma (Fst M) rho rho' crho crho' msr (PairCode u' v') (mkSigma v evM) =
  mkSigma v (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode (PairCode u' v') v) evM)

-- Snd Bot
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr Bot ev = tt

-- Snd non-Bot
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr UCode (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u UCode) evM)
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr PropCode (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u PropCode) evM)
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr (FunEl g) (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u (FunEl g)) evM)
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr (PiCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u (PiCode a f)) evM)
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr (SigmaCode a f) (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u (SigmaCode a f)) evM)
EvalRel-subst-forward-max sigma (Snd M) rho rho' crho crho' msr (PairCode u' v') (mkSigma u evM) =
  mkSigma u (EvalRel-subst-forward-max sigma M rho rho' crho crho' msr (PairCode u (PairCode u' v')) evM)

------------------------------------------------------------------------
-- Part 9: Forward substitution for subst1
------------------------------------------------------------------------

MaxSubRel-subst1 : {n : Nat} (a : Expr n)
  (rho : EnvApprox n) (v : FinEl) ->
  ((u : FinEl) -> EvalRel a rho u -> LeCode u v) ->
  MaxSubRel (subst1Sub a) rho (extendEnv rho v)
MaxSubRel-subst1 a rho v bound fzero u ev = bound u ev
MaxSubRel-subst1 a rho v bound (fsuc i) u ev = snd ev

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
-- Part 10: Forward substitution with witness environment
------------------------------------------------------------------------

botEnv : {n : Nat} -> EnvApprox n
botEnv {zero}  = emptyEnv
botEnv {suc n} = extendEnv (botEnv {n}) Bot

supEnv : {n : Nat} -> EnvApprox n -> EnvApprox n -> EnvApprox n
supEnv emptyEnv emptyEnv = emptyEnv
supEnv (extendEnv rho1 u1) (extendEnv rho2 u2) =
  extendEnv (supEnv rho1 rho2) (Sup u1 u2)

botEnv-Coherent : {n : Nat} -> CoherentEnv (botEnv {n})
botEnv-Coherent {zero}  = tt
botEnv-Coherent {suc n} = mkSigma (botEnv-Coherent {n}) tt

lookupEnv-botEnv : {n : Nat} (i : Fin n) -> Eq (lookupEnv i (botEnv {n})) Bot
lookupEnv-botEnv fzero    = refl
lookupEnv-botEnv (fsuc i) = lookupEnv-botEnv i

Comp-Bot-right : (u : FinEl) -> Comp u Bot
Comp-Bot-right Bot             = tt
Comp-Bot-right UCode           = tt
Comp-Bot-right PropCode        = tt
Comp-Bot-right (FunEl g)       = tt
Comp-Bot-right (PiCode a f)    = tt
Comp-Bot-right (SigmaCode a f) = tt
Comp-Bot-right (PairCode u v)  = tt

SubRel-botEnv : {h n : Nat} (sigma : Sub h n) (rho : EnvApprox h) ->
  SubRel sigma rho (botEnv {n})
SubRel-botEnv sigma rho i =
  Eq-transport (EvalRel (sigma i) rho) (Eq-sym (lookupEnv-botEnv i))
    (EvalRel-Bot (sigma i) rho)

CompEnv : {n : Nat} -> EnvApprox n -> EnvApprox n -> Set
CompEnv emptyEnv emptyEnv = Top
CompEnv (extendEnv rho1 u1) (extendEnv rho2 u2) =
  Pair (CompEnv rho1 rho2) (Comp u1 u2)

CoherentEnv-supEnv : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  CoherentEnv (supEnv rho1 rho2)
CoherentEnv-supEnv emptyEnv emptyEnv c1 c2 comp = tt
CoherentEnv-supEnv (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (CoherentEnv-supEnv rho1 rho2 (fst c1) (fst c2) (fst comp))
          (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))

EnvLe-supEnv-left : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  EnvLe rho1 (supEnv rho1 rho2)
EnvLe-supEnv-left emptyEnv emptyEnv c1 c2 comp = tt
EnvLe-supEnv-left (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (EnvLe-supEnv-left rho1 rho2 (fst c1) (fst c2) (fst comp))
    (mkSigma (snd c1) (mkSigma (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))
      (LeCode-Sup-left u1 u2 (snd comp) (snd c1) (snd c2))))

EnvLe-supEnv-right : {n : Nat} (rho1 rho2 : EnvApprox n) ->
  CoherentEnv rho1 -> CoherentEnv rho2 -> CompEnv rho1 rho2 ->
  EnvLe rho2 (supEnv rho1 rho2)
EnvLe-supEnv-right emptyEnv emptyEnv c1 c2 comp = tt
EnvLe-supEnv-right (extendEnv rho1 u1) (extendEnv rho2 u2) c1 c2 comp =
  mkSigma (EnvLe-supEnv-right rho1 rho2 (fst c1) (fst c2) (fst comp))
    (mkSigma (snd c2) (mkSigma (Coherent-Sup u1 u2 (snd comp) (snd c1) (snd c2))
      (LeCode-Sup-right u1 u2 (snd comp) (snd c1) (snd c2))))

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

CompEnv-botEnv-right : {n : Nat} (rho : EnvApprox n) -> CoherentEnv rho ->
  CompEnv (botEnv {n}) rho
CompEnv-botEnv-right emptyEnv crho = tt
CompEnv-botEnv-right (extendEnv rho u) crho =
  mkSigma (CompEnv-botEnv-right rho (fst crho)) tt

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

lookupEnv-supEnv-botEnv-left : {n : Nat} (rho : EnvApprox n) (i : Fin n) ->
  Eq (lookupEnv i (supEnv (botEnv {n}) rho)) (lookupEnv i rho)
lookupEnv-supEnv-botEnv-left (extendEnv rho u) fzero = Sup-Bot-l u
lookupEnv-supEnv-botEnv-left (extendEnv rho u) (fsuc i) =
  lookupEnv-supEnv-botEnv-left rho i

-- Type alias for forward result
FwdResult : {h g : Nat} -> Sub h g -> EnvApprox h -> Expr g -> FinEl -> Set
FwdResult {h} {g} sigma rho M u =
  Sigma (EnvApprox g) (\ rho' ->
    Pair (CoherentEnv rho')
    (Pair (SubRel sigma rho rho')
          (EvalRel M rho' u)))

extractFinMemU-cft :
  {P : FinEl -> FinEl -> Set} {Q : FinEl -> FinEl -> Set}
  (a0 : FinEl) (f0 : FinFun) -> CoherentFunTail f0 ->
  ((p : Edge) -> EdgeIn p f0 ->
    Sigma FinEl (\ z -> Pair (LeCode z (fst p))
      (Pair (FinMem z a0) (P z (snd p))))) ->
  ((u v : FinEl) -> Selection f0 u v ->
    Sigma FinEl (\ x -> Pair (LeCode x u)
      (Pair (FinMem x a0) (Q x v)))) ->
  FinMem a0 UCode
extractFinMemU-cft a0 nil cft edgeMap rawBody =
  let w = rawBody Bot Bot sel-nil
      x = fst w
  in FinMem-a-in-U x a0 (fst (snd (snd w)))
extractFinMemU-cft a0 (cons p0 ps) cft edgeMap rawBody =
  FinMem-a-in-U (fst (edgeMap p0 here)) a0 (fst (snd (snd (edgeMap p0 here))))

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

tailEnv : {n : Nat} -> EnvApprox (suc n) -> EnvApprox n
tailEnv (extendEnv r _) = r

headEnv : {n : Nat} -> EnvApprox (suc n) -> FinEl
headEnv (extendEnv _ v) = v

tailCoherent : {n : Nat} (rho : EnvApprox (suc n)) -> CoherentEnv rho -> CoherentEnv (tailEnv rho)
tailCoherent (extendEnv r _) crho = fst crho

headCoherent : {n : Nat} (rho : EnvApprox (suc n)) -> CoherentEnv rho -> Coherent (headEnv rho)
headCoherent (extendEnv _ v) crho = snd crho

decompSrTail : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h) (z : FinEl) ->
  (rho' : EnvApprox (suc g)) ->
  SubRel (liftSub sigma) (extendEnv rho z) rho' ->
  SubRel sigma rho (tailEnv rho')
decompSrTail sigma rho z (extendEnv r v) sr i =
  EvalRel-unwk (sigma i) rho z (lookupEnv i r) (sr (fsuc i))

decompSrHead : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h) (z : FinEl) ->
  (rho' : EnvApprox (suc g)) ->
  SubRel (liftSub sigma) (extendEnv rho z) rho' ->
  LeCode (headEnv rho') z
decompSrHead sigma rho z (extendEnv r v) sr = snd (sr fzero)

decompEnvLe : {g : Nat} (rho' : EnvApprox (suc g)) (target : EnvApprox g) (z : FinEl) ->
  EnvLe (tailEnv rho') target -> Coherent (headEnv rho') -> Coherent z -> LeCode (headEnv rho') z ->
  EnvLe rho' (extendEnv target z)
decompEnvLe (extendEnv r v) target z leTail cv cz le =
  mkSigma leTail (mkSigma cv (mkSigma cz le))

foldEdgeFwd : {h g : Nat} (sigma : Sub h g) (rho : EnvApprox h)
  (M : Expr (suc g))
  (accRho : EnvApprox g) ->
  CoherentEnv rho -> CoherentEnv accRho -> SubRel sigma rho accRho ->
  (a : FinEl) ->
  (edges : FinFun) ->
  (body : (p : Edge) -> EdgeIn p edges ->
    Sigma FinEl (\ z -> Pair (LeCode z (fst p))
      (Pair (FinMem z a)
            (EvalRel (substExpr (liftSub sigma) M) (extendEnv rho z) (snd p))))) ->
  Sigma (EnvApprox g) (\ rho' ->
    Pair (CoherentEnv rho')
    (Pair (SubRel sigma rho rho')
    (Pair (EnvLe accRho rho')
      ((p : Edge) -> EdgeIn p edges ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst p))
          (Pair (FinMem z a)
                (EvalRel M (extendEnv rho' z) (snd p))))))))

-- Forward declaration for mutual recursion with foldEdgeFwd
EvalRel-subst-forward-wit :
  {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (u : FinEl) ->
  CoherentEnv rho ->
  EvalRel (substExpr sigma M) rho u ->
  FwdResult sigma rho M u

foldEdgeFwd sigma rho M accRho crho cAcc srAcc a nil body =
  mkSigma accRho (mkSigma cAcc (mkSigma srAcc
    (mkSigma (EnvLe-refl accRho cAcc)
      (\ p ()))))
foldEdgeFwd sigma rho M accRho crho cAcc srAcc a (cons p ps) body =
  let wp   = body p here
      zp   = fst wp
      lep  = fst (snd wp)
      memp = fst (snd (snd wp))
      evBp = snd (snd (snd wp))
      czp  = FinMem-coh-u zp a memp
      ihp  = EvalRel-subst-forward-wit (liftSub sigma) M
               (extendEnv rho zp) (snd p) (mkSigma crho czp) evBp
      rhoBp    = fst ihp
      crhoBp   = fst (snd ihp)
      srBp     = fst (snd (snd ihp))
      evMp     = snd (snd (snd ihp))
      tailBp   = tailEnv rhoBp
      cTailBp  = tailCoherent rhoBp crhoBp
      srTailBp = decompSrTail sigma rho zp rhoBp srBp
      comb   = combineFwd sigma rho crho accRho tailBp cAcc cTailBp srAcc srTailBp
      midRho = fst comb
      cMid   = fst (snd comb)
      srMid  = fst (snd (snd comb))
      leAcc  = fst (snd (snd (snd comb)))
      leTail = snd (snd (snd (snd comb)))
      envleBp : EnvLe rhoBp (extendEnv midRho zp)
      envleBp = decompEnvLe rhoBp midRho zp leTail
                  (headCoherent rhoBp crhoBp) czp (decompSrHead sigma rho zp rhoBp srBp)
      evMp' = EvalRel-mon-env M rhoBp (extendEnv midRho zp) (snd p) evMp envleBp
      rec = foldEdgeFwd sigma rho M midRho crho cMid srMid a ps
              (\ q ein -> body q (there ein))
      rho'  = fst rec
      crho' = fst (snd rec)
      srho' = fst (snd (snd rec))
      leMid = fst (snd (snd (snd rec)))
      bodyRec = snd (snd (snd (snd rec)))
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
  in mkSigma (singletonEnv i u) (mkSigma (singletonEnv-Coherent i u cu)
       (mkSigma (singletonEnv-SubRel sigma rho i u ev)
         (mkSigma cu (singletonEnv-lookup i u cu))))
  where
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

-- U
EvalRel-subst-forward-wit sigma U rho u crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) ev))

-- Prop
EvalRel-subst-forward-wit sigma Prop rho u crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) ev))

-- App Bot
EvalRel-subst-forward-wit sigma (App M N) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- App non-Bot: combine witness envs
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

EvalRel-subst-forward-wit sigma (App M N) rho PropCode crho
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

EvalRel-subst-forward-wit sigma (App M N) rho (SigmaCode a' f') crho
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

EvalRel-subst-forward-wit sigma (App M N) rho (PairCode u' v') crho
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

-- Lam (FunEl g)
EvalRel-subst-forward-wit sigma (Lam A M) rho (FunEl g) crho ev =
  let ew = Lam-edgewise (substExpr sigma A) (substExpr (liftSub sigma) M) rho g ev
      a     = fst ew
      cg    = fst (snd ew)
      aU    = fst (snd (snd ew))
      evA   = fst (snd (snd (snd ew)))
      edges = snd (snd (snd (snd ew)))
      rA    = EvalRel-subst-forward-wit sigma A rho a crho evA
      rhoA  = fst rA ; crhoA = fst (snd rA)
      srA   = fst (snd (snd rA)) ; evA' = snd (snd (snd rA))
      fold  = foldEdgeFwd sigma rho M rhoA crho crhoA srA a g edges
      rho'  = fst fold
      crho' = fst (snd fold)
      sr'   = fst (snd (snd fold))
      leA   = fst (snd (snd (snd fold)))
      bodyAll = snd (snd (snd (snd fold)))
      evA'' = EvalRel-mon-env A rhoA rho' a evA' leA
      selBody : (x v : FinEl) -> Selection g x v ->
        Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a) (EvalRel M (extendEnv rho' z) v)))
      selBody = sel-body-from-edges rho' crho' a aU g (cft-from-cf g cg) bodyAll
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA'' selBody))))))
  where
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
      let wp   = bodyMap p here
          zp   = fst wp
          lezp = fst (snd wp)
          memp = fst (snd (snd wp))
          evMp = snd (snd (snd wp))
          czp  = FinMem-coh-u zp a memp
          cfp  = CFTcons.key-coh cft
          rec   = sel-body-from-edges rho' crho' a aU0 _ (CFTcons.tail-coh cft)
                    (\ q ein -> bodyMap q (there ein)) x0 v0 sel
          zr    = fst rec
          lezr  = fst (snd rec)
          memr  = fst (snd (snd rec))
          evMr  = snd (snd (snd rec))
          czr   = FinMem-coh-u zr a memr
          cx0   = sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel
          comp-zp-x0 = Comp-down zp (fst p) x0 lezp comp-k
          comp-zp-zr = Comp-sym zr zp
                         (Comp-down zr x0 zp lezr (Comp-sym zp x0 comp-zp-x0))
          evMsup = EvalRel-ideal-Comp M rho' zp zr (snd p) v0
                     crho' comp-zp-zr czp czr evMp evMr
          ca     = FinMem-coh-a zp a memp
          memsup = FinMem-Sup-element zp zr a comp-zp-zr ca memp memr
          cSup   = Coherent-Sup (fst p) x0 comp-k cfp cx0
          lesup  = LeCode-Sup-lub zp zr (Sup (fst p) x0)
                     (LeCode-trans zp (fst p) (Sup (fst p) x0)
                       czp cfp cSup lezp
                       (LeCode-Sup-left (fst p) x0 comp-k cfp cx0))
                     (LeCode-trans zr x0 (Sup (fst p) x0)
                       czr cx0 cSup lezr
                       (LeCode-Sup-right (fst p) x0 comp-k cfp cx0))
      in mkSigma (Sup zp zr) (mkSigma lesup (mkSigma memsup evMsup))

-- Lam absurd
EvalRel-subst-forward-wit sigma (Lam A M) rho UCode crho ()
EvalRel-subst-forward-wit sigma (Lam A M) rho PropCode crho ()
EvalRel-subst-forward-wit sigma (Lam A M) rho (PiCode a f) crho ()
EvalRel-subst-forward-wit sigma (Lam A M) rho (SigmaCode a f) crho ()
EvalRel-subst-forward-wit sigma (Lam A M) rho (PairCode u v) crho ()

-- Pi Bot
EvalRel-subst-forward-wit sigma (Pi A B) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Pi (PiCode a f)
EvalRel-subst-forward-wit sigma (Pi A B) rho (PiCode a f) crho ev =
  let pew = Pi-edgewise (substExpr sigma A) (substExpr (liftSub sigma) B) rho a f ev
      caf   = fst pew
      evA   = fst (snd pew)
      a'    = fst (snd (snd pew))
      evA'e = fst (snd (snd (snd pew)))
      edges = snd (snd (snd (snd pew)))
      rAa   = EvalRel-subst-forward-wit sigma A rho a crho evA
      rhoAa = fst rAa ; crhoAa = fst (snd rAa)
      srAa  = fst (snd (snd rAa)) ; evAa = snd (snd (snd rAa))
      rAa'  = EvalRel-subst-forward-wit sigma A rho a' crho evA'e
      rhoAa' = fst rAa' ; crhoAa' = fst (snd rAa')
      srAa'  = fst (snd (snd rAa')) ; evAa'0 = snd (snd (snd rAa'))
      combA = combineFwd sigma rho crho rhoAa rhoAa' crhoAa crhoAa' srAa srAa'
      rhoAc = fst combA ; crhoAc = fst (snd combA)
      srAc  = fst (snd (snd combA))
      leAa  = fst (snd (snd (snd combA)))
      leAa' = snd (snd (snd (snd combA)))
      cf    = snd caf
      fold  = foldEdgeFwd sigma rho B rhoAc crho crhoAc srAc a' f edges
      rho'  = fst fold
      crho' = fst (snd fold)
      sr'   = fst (snd (snd fold))
      leAc  = fst (snd (snd (snd fold)))
      bodyAll = snd (snd (snd (snd fold)))
      leAa-rho' = EnvLe-trans rhoAa rhoAc rho' leAa leAc
      leAa'-rho' = EnvLe-trans rhoAa' rhoAc rho' leAa' leAc
      evAa-rho'  = EvalRel-mon-env A rhoAa rho' a evAa leAa-rho'
      evAa'-rho' = EvalRel-mon-env A rhoAa' rho' a' evAa'0 leAa'-rho'
      rawBody = snd (snd (snd (snd ev)))
      a'U   = extractFinMemU-cft a' f cf bodyAll rawBody
      selBody : (x v : FinEl) -> Selection f x v ->
        Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a') (EvalRel B (extendEnv rho' z) v)))
      selBody = pi-sel-body rho' crho' a' a'U f cf bodyAll
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma caf (mkSigma evAa-rho'
         (mkSigma a' (mkSigma evAa'-rho' selBody))))))
  where
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

-- Pi absurd
EvalRel-subst-forward-wit sigma (Pi A B) rho UCode crho ()
EvalRel-subst-forward-wit sigma (Pi A B) rho PropCode crho ()
EvalRel-subst-forward-wit sigma (Pi A B) rho (FunEl g) crho ()
EvalRel-subst-forward-wit sigma (Pi A B) rho (SigmaCode a f) crho ()
EvalRel-subst-forward-wit sigma (Pi A B) rho (PairCode u v) crho ()

-- Sigma Bot
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Sigma (SigmaCode a f): mirrors Pi (PiCode a f)
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) crho ev =
  let sew = Sigma-edgewise (substExpr sigma A) (substExpr (liftSub sigma) B) rho a f ev
      caf   = fst sew
      evA   = fst (snd sew)
      a'    = fst (snd (snd sew))
      evA'e = fst (snd (snd (snd sew)))
      edges = snd (snd (snd (snd sew)))
      rAa   = EvalRel-subst-forward-wit sigma A rho a crho evA
      rhoAa = fst rAa ; crhoAa = fst (snd rAa)
      srAa  = fst (snd (snd rAa)) ; evAa = snd (snd (snd rAa))
      rAa'  = EvalRel-subst-forward-wit sigma A rho a' crho evA'e
      rhoAa' = fst rAa' ; crhoAa' = fst (snd rAa')
      srAa'  = fst (snd (snd rAa')) ; evAa'0 = snd (snd (snd rAa'))
      combA = combineFwd sigma rho crho rhoAa rhoAa' crhoAa crhoAa' srAa srAa'
      rhoAc = fst combA ; crhoAc = fst (snd combA)
      srAc  = fst (snd (snd combA))
      leAa  = fst (snd (snd (snd combA)))
      leAa' = snd (snd (snd (snd combA)))
      cf    = snd caf
      fold  = foldEdgeFwd sigma rho B rhoAc crho crhoAc srAc a' f edges
      rho'  = fst fold
      crho' = fst (snd fold)
      sr'   = fst (snd (snd fold))
      leAc  = fst (snd (snd (snd fold)))
      bodyAll = snd (snd (snd (snd fold)))
      leAa-rho' = EnvLe-trans rhoAa rhoAc rho' leAa leAc
      leAa'-rho' = EnvLe-trans rhoAa' rhoAc rho' leAa' leAc
      evAa-rho'  = EvalRel-mon-env A rhoAa rho' a evAa leAa-rho'
      evAa'-rho' = EvalRel-mon-env A rhoAa' rho' a' evAa'0 leAa'-rho'
      rawBody = snd (snd (snd (snd ev)))
      a'U   = extractFinMemU-cft a' f cf bodyAll rawBody
      selBody : (x v : FinEl) -> Selection f x v ->
        Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a') (EvalRel B (extendEnv rho' z) v)))
      selBody = sigma-sel-body rho' crho' a' a'U f cf bodyAll
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma caf (mkSigma evAa-rho'
         (mkSigma a' (mkSigma evAa'-rho' selBody))))))
  where
    sigma-sel-key-Coherent :
      (g0 : FinFun) -> CoherentFunTail g0 ->
      (x v : FinEl) -> Selection g0 x v -> Coherent x
    sigma-sel-key-Coherent .nil cft .Bot .Bot sel-nil = tt
    sigma-sel-key-Coherent .(cons _ _) cft x v (sel-skip {p} sel) =
      sigma-sel-key-Coherent _ (CFTcons.tail-coh cft) x v sel
    sigma-sel-key-Coherent .(cons p _) cft .(Sup (fst p) x0) .(Sup (snd p) v0)
      (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      Coherent-Sup (fst p) x0 comp-k
        (CFTcons.key-coh cft)
        (sigma-sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel)
    sigma-sel-body :
      (rho' : EnvApprox _) -> CoherentEnv rho' ->
      (a' : FinEl) -> FinMem a' UCode ->
      (g0 : FinFun) -> CoherentFunTail g0 ->
      ((p : Edge) -> EdgeIn p g0 ->
        Sigma FinEl (\ z -> Pair (LeCode z (fst p))
          (Pair (FinMem z a') (EvalRel B (extendEnv rho' z) (snd p))))) ->
      (x v : FinEl) -> Selection g0 x v ->
      Sigma FinEl (\ z -> Pair (LeCode z x) (Pair (FinMem z a')
        (EvalRel B (extendEnv rho' z) v)))
    sigma-sel-body rho' crho' a' a'U0 .nil cft bodyMap .Bot .Bot sel-nil =
      mkSigma Bot (mkSigma tt (mkSigma a'U0 (EvalRel-Bot B (extendEnv rho' Bot))))
    sigma-sel-body rho' crho' a' a'U0 .(cons _ _) cft bodyMap x v (sel-skip {p} sel) =
      sigma-sel-body rho' crho' a' a'U0 _ (CFTcons.tail-coh cft)
        (\ q ein -> bodyMap q (there ein)) x v sel
    sigma-sel-body rho' crho' a' a'U0 .(cons p _) cft bodyMap .(Sup (fst p) x0)
      .(Sup (snd p) v0) (sel-take {p} {x0} {v0} comp-k comp-v sel) =
      let wp   = bodyMap p here
          zp   = fst wp
          lezp = fst (snd wp)
          memp = fst (snd (snd wp))
          evBp = snd (snd (snd wp))
          czp  = FinMem-coh-u zp a' memp
          cfp  = CFTcons.key-coh cft
          rec   = sigma-sel-body rho' crho' a' a'U0 _ (CFTcons.tail-coh cft)
                    (\ q ein -> bodyMap q (there ein)) x0 v0 sel
          zr    = fst rec
          lezr  = fst (snd rec)
          memr  = fst (snd (snd rec))
          evBr  = snd (snd (snd rec))
          czr   = FinMem-coh-u zr a' memr
          cx0   = sigma-sel-key-Coherent _ (CFTcons.tail-coh cft) x0 v0 sel
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

-- Sigma absurd
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho UCode crho ()
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho PropCode crho ()
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho (FunEl g) crho ()
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho (PiCode a f) crho ()
EvalRel-subst-forward-wit sigma (RawSyntaxSigma.Sigma A B) rho (PairCode u v) crho ()

-- MkPair Bot
EvalRel-subst-forward-wit sigma (MkPair M N) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- MkPair (PairCode u v): combine witness envs from M and N
EvalRel-subst-forward-wit sigma (MkPair M N) rho (PairCode u v) crho
  (mkSigma cuv (mkSigma evM evN)) =
  let rM = EvalRel-subst-forward-wit sigma M rho u crho evM
      rN = EvalRel-subst-forward-wit sigma N rho v crho evN
      rhoM = fst rM ; crhoM = fst (snd rM) ; srM = fst (snd (snd rM))
      evM' = snd (snd (snd rM))
      rhoN = fst rN ; crhoN = fst (snd rN) ; srN = fst (snd (snd rN))
      evN' = snd (snd (snd rN))
      comb = combineFwd sigma rho crho rhoM rhoN crhoM crhoN srM srN
      rho' = fst comb ; crho' = fst (snd comb)
      sr'  = fst (snd (snd comb))
      leM  = fst (snd (snd (snd comb)))
      leN  = snd (snd (snd (snd comb)))
  in mkSigma rho' (mkSigma crho' (mkSigma sr'
       (mkSigma cuv (mkSigma (EvalRel-mon-env M rhoM rho' u evM' leM)
                              (EvalRel-mon-env N rhoN rho' v evN' leN)))))

-- MkPair absurd
EvalRel-subst-forward-wit sigma (MkPair M N) rho UCode crho ()
EvalRel-subst-forward-wit sigma (MkPair M N) rho PropCode crho ()
EvalRel-subst-forward-wit sigma (MkPair M N) rho (FunEl g) crho ()
EvalRel-subst-forward-wit sigma (MkPair M N) rho (PiCode a f) crho ()
EvalRel-subst-forward-wit sigma (MkPair M N) rho (SigmaCode a f) crho ()

-- Fst Bot
EvalRel-subst-forward-wit sigma (Fst M) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Fst non-Bot: delegate to M with PairCode
EvalRel-subst-forward-wit sigma (Fst M) rho UCode crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode UCode v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))
EvalRel-subst-forward-wit sigma (Fst M) rho PropCode crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode PropCode v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))
EvalRel-subst-forward-wit sigma (Fst M) rho (FunEl g) crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode (FunEl g) v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))
EvalRel-subst-forward-wit sigma (Fst M) rho (PiCode a f) crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode (PiCode a f) v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))
EvalRel-subst-forward-wit sigma (Fst M) rho (SigmaCode a f) crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode (SigmaCode a f) v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))
EvalRel-subst-forward-wit sigma (Fst M) rho (PairCode u' v') crho (mkSigma v evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode (PairCode u' v') v) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma v evM')))

-- Snd Bot
EvalRel-subst-forward-wit sigma (Snd M) rho Bot crho ev =
  mkSigma botEnv (mkSigma botEnv-Coherent
    (mkSigma (SubRel-botEnv sigma rho) tt))

-- Snd non-Bot
EvalRel-subst-forward-wit sigma (Snd M) rho UCode crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u UCode) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))
EvalRel-subst-forward-wit sigma (Snd M) rho PropCode crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u PropCode) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))
EvalRel-subst-forward-wit sigma (Snd M) rho (FunEl g) crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u (FunEl g)) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))
EvalRel-subst-forward-wit sigma (Snd M) rho (PiCode a f) crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u (PiCode a f)) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))
EvalRel-subst-forward-wit sigma (Snd M) rho (SigmaCode a f) crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u (SigmaCode a f)) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))
EvalRel-subst-forward-wit sigma (Snd M) rho (PairCode u' v') crho (mkSigma u evM) =
  let r = EvalRel-subst-forward-wit sigma M rho (PairCode u (PairCode u' v')) crho evM
      rho' = fst r ; crho' = fst (snd r)
      sr' = fst (snd (snd r)) ; evM' = snd (snd (snd r))
  in mkSigma rho' (mkSigma crho' (mkSigma sr' (mkSigma u evM')))

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
      envle = envLe-from-pointwise rho' (extendEnv rho v)
        (\ { fzero -> mkSigma cv (mkSigma cv (LeCode-refl v cv))
           ; (fsuc i) -> mkSigma (fst (sr (fsuc i)))
                           (mkSigma (lookupEnv-coh i rho crho)
                                    (snd (sr (fsuc i))))
           })
      evM'  = EvalRel-mon-env M rho' (extendEnv rho v) u evM envle
  in mkSigma v (mkSigma evN evM')

------------------------------------------------------------------------
-- Part 13: EvalRel-Pi-app-type and EvalRel-Pi-body
------------------------------------------------------------------------

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
 EvalRel-body-EvalFun-step zero B rho v a' q rest crho cv cft eq wf =
  EvalRel-body-EvalFun B rho v a' rest crho cv (CFTcons.tail-coh cft)
    (\ p ein -> wf p (there ein))
 EvalRel-body-EvalFun-step (suc _) B rho v a' q rest crho cv cft eq wf =
  let ih = EvalRel-body-EvalFun B rho v a' rest crho cv
             (CFTcons.tail-coh cft)
             (\ p ein -> wf p (there ein))
      w      = wf q here
      x      = fst w
      le-x-u = fst (snd w)
      mem    = fst (snd (snd w))
      evB-x  = snd (snd (snd w))
      cx  = FinMem-coh-u x a' mem
      cqu = CFTcons.key-coh cft
      le-qu-v = leFinEl-sound (fst q) v (Eq-transport isPos eq tt)
      le-x-v  = LeCode-trans x (fst q) v cx cqu cv le-x-u le-qu-v
      envle = mkSigma (EnvLe-refl rho crho)
                (mkSigma cx (mkSigma cv le-x-v))
      evB-v = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho v)
                (snd q) evB-x envle
      crho-v = mkSigma crho cv
      cohv = EvalRel-coh B (extendEnv rho v) (snd q) evB-v
      coh-rest = Coherent-EvalFun rest v (CFTcons.tail-coh cft) cv
      comp-vr = Comp-value-EvalFun q rest v le-qu-v cv
                  (CFTcons.val-coh cft)
                  (CFTcons.compat cft)
                  (coherentWith-to-compStepFun q rest (CFTcons.compat cft))
  in EvalRel-Sup B (extendEnv rho v) (snd q) (EvalFun rest v)
       crho-v cohv coh-rest comp-vr evB-v ih

EvalRel-Pi-app-type :
  {n : Nat} (A : Expr n) (B : Expr (suc n)) (a : Expr n)
  (rho : EnvApprox n) (b : FinEl) (f : FinFun) (v : FinEl) ->
  CoherentEnv rho ->
  EvalRel (Pi A B) rho (PiCode b f) ->
  EvalRel a rho v ->
  EvalRel (subst1 B a) rho (EvalFun f v)
EvalRel-Pi-app-type A B a rho b f v crho evPi eva =
  let pew  = Pi-edgewise A B rho b f evPi
      caf  = fst pew
      a'   = fst (snd (snd pew))
      wf   = snd (snd (snd (snd pew)))
      cf   = snd caf
      cv   = EvalRel-coh a rho v eva
      evB  = EvalRel-body-EvalFun B rho v a' f crho cv cf wf
  in EvalRel-subst1-backward B a rho v (EvalFun f v) crho eva evB

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
  in EvalRel-body-EvalFun B rho v a' f crho cv cf wf
