{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- TypingSemantics.agda
--
-- Conversion soundness and typing soundness (Theorem 1) for the
-- finite relational semantics.
--
-- Central invariants:
--   InvTyp  G M A rho   — every u ≤ ⟦M⟧ρ has a typed enlargement
--   InvConv G M N A rho — InvTyp for both sides + bidir evaluation
------------------------------------------------------------------------

module TypingSemantics where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              nil ; cons)
open import PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; LeCode-Comp ; FinMem ; FinMem-coh-u ; FinMem-a-in-U ;
  FinMemFun ; FinMemAllU ; CoherentFun ; Coherent ; applyEl ;
  LeFunCode ; LeFunCode-refl ; EvalFun ; EvalFun-step ; EvalFun-mon-arg ;
  EvalFun-in-UCode ; Coherent-EvalFun ;
  LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  Sup ; Sup-Bot-r ;
  Comp ; comp-Bot-l ; comp-Bot-r ; Comp-refl ; Comp-sym ;
  Coherent-Sup ; CoherentFun-append ; CompFun ;
  finMem-upward ; coh-from-aU ;
  leFinEl ; leFinEl-complete ;
  FinMem-Sup-element ; comp-EvalFun ;
  EvalFun-append-eq)
open import Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  singleton-selection ; sel-nil ; sel-skip ; sel-take ;
  Coherent-Selection ; Coherent-Selection-val ;
  Selection-le-EvalFun ; FinMemAllU-Selection ; selectionBelow)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe ;
  EvalRel-Comp ; EvalRel-Sup ;
  Lam-edgewise ; EvalRel-Comp-ext ; EvalRel-ideal-Comp)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; Ren ; liftRen ; renExpr ; wkRen ; wkExpr ; subst1)
open import TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import EvalSubstitution using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-subst1-backward ; EvalRel-subst1-forward-bounded)

------------------------------------------------------------------------
-- Part 1: Fits — well-typed finite environments
------------------------------------------------------------------------

Fits : {n : Nat} -> Ctx n -> EnvApprox n -> Set
Fits empty emptyEnv = Top
Fits (extend G A) (extendEnv rho u) =
  Pair (Fits G rho)
       (Pair (Coherent u)
         (Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
           Pair (LeCode u u') (Pair (FinMem u' a') (EvalRel A rho a'))))))

Fits-tail : {n : Nat} {G : Ctx n} {A : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Fits (extend G A) (extendEnv rho u) -> Fits G rho
Fits-tail (mkSigma fits_G _) = fits_G

Fits-top : {n : Nat} {G : Ctx n} {A : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Fits (extend G A) (extendEnv rho u) ->
  Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
    Pair (LeCode u u') (Pair (FinMem u' a') (EvalRel A rho a'))))
Fits-top (mkSigma _ (mkSigma _ rest)) = rest

Fits-CoherentEnv : {n : Nat} {G : Ctx n} (rho : EnvApprox n) ->
  Fits G rho -> CoherentEnv rho
Fits-CoherentEnv {zero} {empty} emptyEnv fits = tt
Fits-CoherentEnv {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G (mkSigma cv _)) =
  mkSigma (Fits-CoherentEnv rho fits_G) cv

Fits-var : {n : Nat} {G : Ctx n} (rho : EnvApprox n) ->
  Fits G rho -> (i : Fin n) ->
  Pair (Coherent (lookupEnv i rho))
    (Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
      Pair (LeCode (lookupEnv i rho) u')
           (Pair (FinMem u' a') (EvalRel (lookup G i) rho a')))))
Fits-var {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G (mkSigma cv fitv)) fzero =
  let u' = fst fitv ; a' = fst (snd fitv)
      le = fst (snd (snd fitv))
      fm = fst (snd (snd (snd fitv)))
      evA = snd (snd (snd (snd fitv)))
  in mkSigma cv (mkSigma u' (mkSigma a' (mkSigma le (mkSigma fm
       (EvalRel-wk A rho v a' evA)))))
Fits-var {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G (mkSigma cv fitv)) (fsuc i) =
  let ih = Fits-var rho fits_G i
      ci = fst ih
      u' = fst (snd ih) ; a' = fst (snd (snd ih))
      le = fst (snd (snd (snd ih)))
      fm = fst (snd (snd (snd (snd ih))))
      evLk = snd (snd (snd (snd (snd ih))))
  in mkSigma ci (mkSigma u' (mkSigma a' (mkSigma le (mkSigma fm
       (EvalRel-wk (lookup G i) rho v a' evLk)))))

------------------------------------------------------------------------
-- Part 2: Named invariants
------------------------------------------------------------------------

-- Typed A rho u : there exist u ≤ x and a with FinMem x a and ⟦A⟧ρ = a
Typed : {n : Nat} -> Expr n -> EnvApprox n -> FinEl -> Set
Typed {n} A rho u =
  Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
    Pair (LeCode u u') (Pair (FinMem u' a') (EvalRel A rho a'))))

-- InvTyp G M A rho : for all u ≤ ⟦M⟧ρ, Typed A rho u
InvTyp : {n : Nat} -> Ctx n -> Expr n -> Expr n -> EnvApprox n -> Set
InvTyp G M A rho =
  (u : FinEl) -> EvalRel M rho u -> Typed A rho u

-- InvConv G M N A rho : typing for both + bidirectional evaluation
InvConv : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  EnvApprox n -> Set
InvConv G M N A rho =
  Pair (InvTyp G M A rho)
  (Pair (InvTyp G N A rho)
  (Pair ((u : FinEl) -> EvalRel M rho u -> EvalRel N rho u)
        ((u : FinEl) -> EvalRel N rho u -> EvalRel M rho u)))

------------------------------------------------------------------------
-- Part 2b: Key intermediate lemmas (used by theorem1 / convSound')
------------------------------------------------------------------------

-- Lambda case: if the body satisfies InvTyp in every extended
-- environment, then Lam A M satisfies InvTyp at Pi A B.
InvTyp-Lam : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr (suc n)) ->
  ((rho : EnvApprox n) (x a : FinEl) ->
    Fits G rho -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) M B (extendEnv rho x)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G (Lam A M) (Pi A B) rho
InvTyp-Lam A B M ih rho fits = {!!}

-- Application case: if M has type Pi A B and N has type A,
-- then App M N has type subst1 B N.
InvTyp-App : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) (rho : EnvApprox n) ->
  Fits G rho ->
  InvTyp G M (Pi A B) rho ->
  InvTyp G N A rho ->
  InvTyp G (App M N) (subst1 B N) rho
InvTyp-App A B M N rho fits invM invN = {!!}

-- Beta conversion: App (Lam A M) N is convertible with subst1 M N.
InvConv-beta : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr (suc n)) (N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G (App (Lam A M) N) (subst1 M N) (subst1 B N) rho
InvConv-beta A B M N rho fits = {!!}

------------------------------------------------------------------------
-- Part 3: Mutual declarations
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Theorem 1: HasType G M A  →  InvTyp G M A rho
  theorem1 : {n : Nat} {G : Ctx n} {M A : Expr n} ->
    HasType G M A ->
    (rho : EnvApprox n) -> Fits G rho ->
    InvTyp G M A rho

  -- Conversion soundness: ConvTm G M N A  →  InvConv G M N A rho
  convSound' : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A ->
    (rho : EnvApprox n) -> Fits G rho ->
    InvConv G M N A rho

  -- Projections (used in theorem1 for ty-conv)
  convSound : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A ->
    (rho : EnvApprox n) -> Fits G rho ->
    (u : FinEl) -> EvalRel M rho u -> EvalRel N rho u
  convSound d rho fits = fst (snd (snd (convSound' d rho fits)))

  convSound-inv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A ->
    (rho : EnvApprox n) -> Fits G rho ->
    (u : FinEl) -> EvalRel N rho u -> EvalRel M rho u
  convSound-inv d rho fits = snd (snd (snd (convSound' d rho fits)))

  ----------------------------------------------------------------------
  -- Part 4: Helpers for conversion cases
  ----------------------------------------------------------------------

  -- Pi congruence on evaluation (already proved)
  convSound-Pi-fwd : {n : Nat} {G : Ctx n}
    (A A' : Expr n) (B B' : Expr (suc n))
    (rho : EnvApprox n) -> Fits G rho -> (u : FinEl) ->
    ((w : FinEl) -> EvalRel A rho w -> EvalRel A' rho w) ->
    ((v : FinEl) -> Coherent v ->
      (w : FinEl) -> EvalRel B (extendEnv rho v) w ->
                     EvalRel B' (extendEnv rho v) w) ->
    EvalRel (Pi A B) rho u -> EvalRel (Pi A' B') rho u
  convSound-Pi-fwd A A' B B' rho fits Bot eqA eqB ev = tt
  convSound-Pi-fwd A A' B B' rho fits (PiCode b f) eqA eqB
    (mkSigma coh (mkSigma evA body)) =
    mkSigma coh (mkSigma (eqA b evA)
      (\ u v sel ->
        let w   = body u v sel
            x   = fst w
            le  = fst (snd w)
            mem = fst (snd (snd w))
            evB = snd (snd (snd w))
            cx  = FinMem-coh-u x b mem
        in mkSigma x (mkSigma le (mkSigma mem (eqB x cx v evB)))))
  convSound-Pi-fwd A A' B B' rho fits UCode eqA eqB ()
  convSound-Pi-fwd A A' B B' rho fits (FunEl g) eqA eqB ()

  -- App congruence — function slot (already proved)
  convSound-App-fun-fwd : {n : Nat}
    (f f' a : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel f rho w -> EvalRel f' rho w) ->
    EvalRel (App f a) rho u -> EvalRel (App f' a) rho u
  convSound-App-fun-fwd f f' a rho Bot eqF ev = tt
  convSound-App-fun-fwd f f' a rho UCode eqF
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma (eqF (FunEl g) evf) (mkSigma eva (mkSigma sel le))))))
  convSound-App-fun-fwd f f' a rho (FunEl g') eqF
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma (eqF (FunEl g) evf) (mkSigma eva (mkSigma sel le))))))
  convSound-App-fun-fwd f f' a rho (PiCode a'' f'') eqF
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma (eqF (FunEl g) evf) (mkSigma eva (mkSigma sel le))))))

  -- App congruence — argument slot (already proved)
  convSound-App-arg-fwd : {n : Nat}
    (f a a' : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel a rho w -> EvalRel a' rho w) ->
    EvalRel (App f a) rho u -> EvalRel (App f a') rho u
  convSound-App-arg-fwd f a a' rho Bot eqA ev = tt
  convSound-App-arg-fwd f a a' rho UCode eqA
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma (eqA x eva) (mkSigma sel le))))))
  convSound-App-arg-fwd f a a' rho (FunEl g') eqA
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma (eqA x eva) (mkSigma sel le))))))
  convSound-App-arg-fwd f a a' rho (PiCode a'' f'') eqA
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le))))))) =
    mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma (eqA x eva) (mkSigma sel le))))))

  -- Beta forward (already proved)
  convSound-beta-fwd : {n : Nat} {G : Ctx n}
    (A : Expr n) (M : Expr (suc n)) (a : Expr n)
    (rho : EnvApprox n) -> Fits G rho -> (u : FinEl) ->
    EvalRel (App (Lam A M) a) rho u -> EvalRel (subst1 M a) rho u
  convSound-beta-fwd A M a rho fits Bot ev = EvalRel-Bot (subst1 M a) rho
  convSound-beta-fwd A M a rho fits UCode
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evLam (mkSigma eva (mkSigma sel le))))))) =
    let crho = Fits-CoherentEnv rho fits
        a_code = fst evLam
        body   = snd (snd (snd (snd evLam)))
        w    = body x v sel
        x'   = fst w
        le'  = fst (snd w)
        mem  = fst (snd (snd w))
        evM  = snd (snd (snd w))
        cx'  = FinMem-coh-u x' a_code mem
        eva' = EvalRel-down a rho x x' crho cx' eva le'
        ev-subst = EvalRel-subst1-backward M a rho x' v crho eva' evM
    in EvalRel-down (subst1 M a) rho v UCode crho cu ev-subst le
  convSound-beta-fwd A M a rho fits (FunEl g')
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evLam (mkSigma eva (mkSigma sel le))))))) =
    let crho = Fits-CoherentEnv rho fits
        a_code = fst evLam
        body   = snd (snd (snd (snd evLam)))
        w    = body x v sel
        x'   = fst w
        le'  = fst (snd w)
        mem  = fst (snd (snd w))
        evM  = snd (snd (snd w))
        cx'  = FinMem-coh-u x' a_code mem
        eva' = EvalRel-down a rho x x' crho cx' eva le'
        ev-subst = EvalRel-subst1-backward M a rho x' v crho eva' evM
    in EvalRel-down (subst1 M a) rho v (FunEl g') crho cu ev-subst le
  convSound-beta-fwd A M a rho fits (PiCode a'' f'')
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evLam (mkSigma eva (mkSigma sel le))))))) =
    let crho = Fits-CoherentEnv rho fits
        a_code = fst evLam
        body   = snd (snd (snd (snd evLam)))
        w    = body x v sel
        x'   = fst w
        le'  = fst (snd w)
        mem  = fst (snd (snd w))
        evM  = snd (snd (snd w))
        cx'  = FinMem-coh-u x' a_code mem
        eva' = EvalRel-down a rho x x' crho cx' eva le'
        ev-subst = EvalRel-subst1-backward M a rho x' v crho eva' evM
    in EvalRel-down (subst1 M a) rho v (PiCode a'' f'') crho cu ev-subst le

  -- InvTyp for any Pi expression at type U (direct, no IH needed)
  invTyp-Pi : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
    (rho : EnvApprox n) ->
    InvTyp G (Pi A B) U rho
  invTyp-Pi A B rho Bot ev =
    mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt tt)))
  invTyp-Pi A B rho UCode ()
  invTyp-Pi A B rho (FunEl g) ()
  invTyp-Pi A B rho (PiCode b f)
    (mkSigma coh (mkSigma evA body)) =
    mkSigma (PiCode b f) (mkSigma UCode
      (mkSigma (LeCode-refl (PiCode b f) coh) (mkSigma coh tt)))

  ----------------------------------------------------------------------
  -- Part 5: convSound' — case analysis
  ----------------------------------------------------------------------

  -- conv-refl: Γ ⊢ M = M : A
  -- InvTyp from theorem1; forward/backward = identity
  convSound' (conv-refl dM) rho fits =
    let inv = theorem1 dM rho fits
    in mkSigma inv (mkSigma inv
         (mkSigma (\ u ev -> ev) (\ u ev -> ev)))

  -- conv-sym: Γ ⊢ N = M : A  from  Γ ⊢ M = N : A
  -- Swap components of IH
  convSound' (conv-sym d) rho fits =
    let ih = convSound' d rho fits
    in mkSigma (fst (snd ih)) (mkSigma (fst ih)
         (mkSigma (snd (snd (snd ih))) (fst (snd (snd ih)))))

  -- conv-trans: Γ ⊢ M = P : A  from  Γ ⊢ M = N : A, Γ ⊢ N = P : A
  -- Compose forward/backward; keep InvTyp for M from d1, for P from d2
  convSound' (conv-trans d1 d2) rho fits =
    let ih1 = convSound' d1 rho fits
        ih2 = convSound' d2 rho fits
        fwd1 = fst (snd (snd ih1))
        fwd2 = fst (snd (snd ih2))
        bwd1 = snd (snd (snd ih1))
        bwd2 = snd (snd (snd ih2))
    in mkSigma (fst ih1) (mkSigma (fst (snd ih2))
         (mkSigma (\ u ev -> fwd2 u (fwd1 u ev))
                  (\ u ev -> bwd1 u (bwd2 u ev))))

  -- conv-conv: Γ ⊢ M = N : B  from  Γ ⊢ M = N : A, Γ ⊢ A = B : U
  -- Transport InvTyp through type conversion; keep forward/backward
  convSound' (conv-conv d dAB) rho fits =
    let ih = convSound' d rho fits
        invM = fst ih
        invN = fst (snd ih)
        fwd = fst (snd (snd ih))
        bwd = snd (snd (snd ih))
        fwdAB = \ a' ev -> convSound dAB rho fits a' ev
        invM' = \ u ev ->
          let r = invM u ev
              u' = fst r ; a' = fst (snd r)
              le = fst (snd (snd r))
              fm = fst (snd (snd (snd r)))
              evA = snd (snd (snd (snd r)))
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma fm (fwdAB a' evA))))
        invN' = \ u ev ->
          let r = invN u ev
              u' = fst r ; a' = fst (snd r)
              le = fst (snd (snd r))
              fm = fst (snd (snd (snd r)))
              evA = snd (snd (snd (snd r)))
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma fm (fwdAB a' evA))))
    in mkSigma invM' (mkSigma invN' (mkSigma fwd bwd))

  -- conv-beta: Γ ⊢ (λA.M) a = M[a] : B[a]
  -- Forward: proved (convSound-beta-fwd)
  -- Backward: needs forward substitution (requires pCode / max-eval)
  -- InvTyp LHS: from theorem1 on ty-App
  -- InvTyp RHS: from InvTyp LHS composed with backward
  convSound' (conv-beta {A = A} {B = B} {M = M} {a = a} dA dB dM da)
    rho fits =
    let invLHS = theorem1 (ty-App dA (ty-Lam dA dB dM) da) rho fits
        fwd = \ u ev -> convSound-beta-fwd A M a rho fits u ev
        bwd : (u : FinEl) -> EvalRel (subst1 M a) rho u ->
                              EvalRel (App (Lam A M) a) rho u
        bwd = _  -- needs forward substitution
        invRHS = \ u ev -> invLHS u (bwd u ev)
    in mkSigma invLHS (mkSigma invRHS (mkSigma fwd bwd))

  -- conv-Pi: Γ ⊢ Π A B = Π A' B' : U
  -- Forward/backward: from convSound-Pi-fwd
  -- InvTyp: Pi always evaluates to Bot or PiCode, both trivially in U
  convSound' (conv-Pi {A = A} {A' = A'} {B = B} {B' = B'} d1 d2)
    rho fits =
    let fwd = \ u ev -> convSound-Pi-fwd A A' B B' rho fits u
                (\ w -> convSound d1 rho fits w)
                (\ v cv w -> convSound d2 (extendEnv rho v) _ w)
                ev
        bwd = \ u ev -> convSound-Pi-fwd A' A B' B rho fits u
                (\ w -> convSound-inv d1 rho fits w)
                (\ v cv w -> convSound-inv d2 (extendEnv rho v) _ w)
                ev
    in mkSigma (invTyp-Pi A B rho)
       (mkSigma (invTyp-Pi A' B' rho)
       (mkSigma fwd bwd))

  -- conv-funext: Γ ⊢ f = g : Π A B
  -- InvTyp: from theorem1 on df, dg
  -- Forward/backward: needs funext argument (application in extended env)
  convSound' (conv-funext {A = A} {B = B} {f = f} {g = g} dA d df dg)
    rho fits =
    let invF = theorem1 df rho fits
        invG = theorem1 dg rho fits
        fwd : (u : FinEl) -> EvalRel f rho u -> EvalRel g rho u
        fwd = _  -- needs funext construction
        bwd : (u : FinEl) -> EvalRel g rho u -> EvalRel f rho u
        bwd = _  -- needs funext construction
    in mkSigma invF (mkSigma invG (mkSigma fwd bwd))

  -- conv-App-fun: Γ ⊢ f a = f' a : B[a]
  -- Forward/backward: from convSound-App-fun-fwd
  -- InvTyp LHS: from theorem1 on ty-App applied to f
  -- InvTyp RHS: from InvTyp LHS composed with backward
  convSound' (conv-App-fun {A = A} {B = B} {f = f} {f' = f'} {a = a}
    dA dff' da) rho fits =
    let ih = convSound' dff' rho fits
        fwdF = fst (snd (snd ih))
        bwdF = snd (snd (snd ih))
        fwd = \ u ev -> convSound-App-fun-fwd f f' a rho u fwdF ev
        bwd = \ u ev -> convSound-App-fun-fwd f' f a rho u bwdF ev
        -- InvTyp: need HasType for f and f' to call theorem1 on ty-App.
        -- Extract from the conversion derivation dff'.
        invLHS : InvTyp _ (App f a) (subst1 B a) rho
        invLHS = _  -- theorem1 (ty-App dA df da) where df : HasType G f (Pi A B)
        invRHS : InvTyp _ (App f' a) (subst1 B a) rho
        invRHS = _  -- theorem1 (ty-App dA df' da) where df' : HasType G f' (Pi A B)
    in mkSigma invLHS (mkSigma invRHS (mkSigma fwd bwd))

  -- conv-App-arg: Γ ⊢ f a = f a' : B[a]
  -- Forward/backward: from convSound-App-arg-fwd
  -- InvTyp: similar to conv-App-fun
  convSound' (conv-App-arg {A = A} {B = B} {f = f} {a = a} {a' = a'}
    dA df daa') rho fits =
    let ih = convSound' daa' rho fits
        fwdA = fst (snd (snd ih))
        bwdA = snd (snd (snd ih))
        fwd = \ u ev -> convSound-App-arg-fwd f a a' rho u fwdA ev
        bwd = \ u ev -> convSound-App-arg-fwd f a' a rho u bwdA ev
        -- InvTyp: need HasType for a and a' to call theorem1 on ty-App.
        invLHS : InvTyp _ (App f a) (subst1 B a) rho
        invLHS = _  -- theorem1 (ty-App dA df da) where da : HasType G a A
        invRHS : InvTyp _ (App f a') (subst1 B a) rho
        invRHS = _  -- theorem1 (ty-App dA df da') composed with bwd
    in mkSigma invLHS (mkSigma invRHS (mkSigma fwd bwd))

  ----------------------------------------------------------------------
  -- Part 6: theorem1 — case analysis
  ----------------------------------------------------------------------

  -- ty-var: variable lookup (proved)
  theorem1 (ty-var {i = i} wf) rho fits u (mkSigma cu le) =
    let fv  = Fits-var rho fits i
        ci  = fst fv
        u'  = fst (snd fv) ; a' = fst (snd (snd fv))
        le0 = fst (snd (snd (snd fv)))
        fm  = fst (snd (snd (snd (snd fv))))
        evA = snd (snd (snd (snd (snd fv))))
        cu' = FinMem-coh-u u' a' fm
    in mkSigma u' (mkSigma a'
         (mkSigma (LeCode-trans u (lookupEnv i rho) u' cu ci cu' le le0)
           (mkSigma fm evA)))

  -- ty-U: universe (proved)
  theorem1 (ty-U wf) rho fits u ev =
    mkSigma UCode (mkSigma UCode (mkSigma ev (mkSigma tt tt)))

  -- ty-conv: type conversion (proved)
  theorem1 (ty-conv d1 d2) rho fits u ev =
    let ih  = theorem1 d1 rho fits u ev
        u'  = fst ih ; a' = fst (snd ih)
        le  = fst (snd (snd ih))
        fm  = fst (snd (snd (snd ih)))
        evA = snd (snd (snd (snd ih)))
    in mkSigma u' (mkSigma a'
         (mkSigma le (mkSigma fm (convSound d2 rho fits a' evA))))

  -- ty-Pi: Pi type, result type is U (proved)
  theorem1 (ty-Pi d1 d2) rho fits Bot ev =
    mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt tt)))
  theorem1 (ty-Pi d1 d2) rho fits UCode ()
  theorem1 (ty-Pi d1 d2) rho fits (FunEl g) ()
  theorem1 (ty-Pi d1 d2) rho fits (PiCode b f)
    (mkSigma coh (mkSigma evA body)) =
    mkSigma (PiCode b f) (mkSigma UCode
      (mkSigma (LeCode-refl (PiCode b f) coh) (mkSigma coh tt)))

  -- ty-Lam: lambda abstraction
  -- Bot case (proved)
  theorem1 (ty-Lam d1 d2 d3) rho fits Bot ev =
    mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt tt)))
  theorem1 (ty-Lam d1 d2 d3) rho fits UCode ()
  theorem1 (ty-Lam d1 d2 d3) rho fits (PiCode b f) ()
  -- FunEl case: needs Lam-edgewise + EvalRel-Comp-ext + pCode
  theorem1 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) rho fits (FunEl g)
    (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
    _

  -- ty-App: application
  -- Bot case (proved)
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3)
    rho fits Bot ev =
    mkSigma Bot (mkSigma Bot
      (mkSigma tt (mkSigma tt (EvalRel-Bot (subst1 B a) rho))))
  -- Non-Bot cases: need Pi inversion + codomain typing
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3)
    rho fits UCode
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le-u))))))) =
    _
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3)
    rho fits (FunEl g')
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le-u))))))) =
    _
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3)
    rho fits (PiCode a'' f'')
    (mkSigma cu (mkSigma g (mkSigma x (mkSigma v
      (mkSigma evf (mkSigma eva (mkSigma sel le-u))))))) =
    _

