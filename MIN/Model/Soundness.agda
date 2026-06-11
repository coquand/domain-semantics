{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- TypingSemanticsSigma.agda
--
-- Conversion soundness and typing soundness (Theorem 1) for the
-- finite relational semantics, extended with Sigma types.
--
-- Parallel version of TypingSemantics.agda.
--
-- Central invariants (from LemmaForTSSigma):
--   InvTyp  G M A rho   — every u ≤ ⟦M⟧ρ has a typed enlargement
--   InvConv G M N A rho — InvTyp for both sides + bidir evaluation
--
-- 0 postulates.
------------------------------------------------------------------------

module MIN.Model.Soundness where

import MIN.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              nil ; cons)
open import MIN.Domain.Kernel using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; LeFunCode ;
  FinMem ; FinMemFun ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf ; NotBot ;
  EvalFun ; EvalFun-mon ; Coherent-EvalFun ;
  finMem-upward ;
  absurdEl ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; comp-Bot-r ; comp-Bot-l ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  FinMemAllU)
open import MIN.Model.Selection using (Selection)
open import MIN.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EvalRel-Comp ; EvalRel-Sup)
open import MIN.Syntax.Raw using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1)
open import MIN.Syntax.Typing using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)

-- All hard lemmas come from LemmaForTSSigma (0 postulates).
import MIN.Model.SoundnessLemmas as LTS
open LTS using (Fits ; Typed ; InvTyp ; InvConv ;
  Fits-CoherentEnv ; Fits-var)
open import MIN.Model.EvalSubstitution using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-subst1-backward ; EvalRel-subst1-forward-bounded ;
  EvalRel-subst1-forward)

------------------------------------------------------------------------
-- Helpers for proof-irrelevance
------------------------------------------------------------------------

-- If FinMem u' Bot, then u' = Bot
FinMem-Bot-elim : (u' : FinEl) -> FinMem u' Bot -> Eq u' Bot
FinMem-Bot-elim Bot          mem = refl
FinMem-Bot-elim UCode        ()
FinMem-Bot-elim (FunEl g)    ()
FinMem-Bot-elim (PiCode a f) ()

-- If LeCode u u' and u' = Bot, then u = Bot
LeCode-Bot-eq : (u u' : FinEl) -> LeCode u u' -> Eq u' Bot -> Eq u Bot
LeCode-Bot-eq Bot u' le eq = refl
LeCode-Bot-eq UCode Bot ()
LeCode-Bot-eq UCode UCode le ()
LeCode-Bot-eq UCode (FunEl h) le ()
LeCode-Bot-eq UCode (PiCode b g) le ()
LeCode-Bot-eq (FunEl g) Bot ()
LeCode-Bot-eq (FunEl g) UCode le ()
LeCode-Bot-eq (FunEl g) (FunEl h) le ()
LeCode-Bot-eq (FunEl g) (PiCode b h) le ()
LeCode-Bot-eq (PiCode a f) Bot ()
LeCode-Bot-eq (PiCode a f) UCode le ()
LeCode-Bot-eq (PiCode a f) (FunEl h) le ()
LeCode-Bot-eq (PiCode a f) (PiCode b g) le ()

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

  -- Projections
  convSound : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A ->
    (rho : EnvApprox n) -> Fits G rho ->
    (u : FinEl) -> EvalRel M rho u -> EvalRel N rho u
  convSound d rho fits =
    let mkSigma _ (mkSigma _ (mkSigma fwd _)) = convSound' d rho fits
    in fwd

  convSound-inv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A ->
    (rho : EnvApprox n) -> Fits G rho ->
    (u : FinEl) -> EvalRel N rho u -> EvalRel M rho u
  convSound-inv d rho fits =
    let mkSigma _ (mkSigma _ (mkSigma _ bwd)) = convSound' d rho fits
    in bwd

  --------------------------------------------------------------------
  -- Helper: Pi congruence on evaluation
  --------------------------------------------------------------------

  convSound-Pi-fwd : {n : Nat}
    (A A' : Expr n) (B B' : Expr (suc n))
    (rho : EnvApprox n) -> (u : FinEl) ->
    ((w : FinEl) -> EvalRel A rho w -> EvalRel A' rho w) ->
    ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
      (w : FinEl) -> EvalRel B (extendEnv rho x) w ->
                     EvalRel B' (extendEnv rho x) w) ->
    EvalRel (Pi A B) rho u -> EvalRel (Pi A' B') rho u
  convSound-Pi-fwd A A' B B' rho Bot eqA eqB ev = tt
  convSound-Pi-fwd A A' B B' rho (PiCode b f) eqA eqB
    (mkSigma coh (mkSigma evA-b (mkSigma a' (mkSigma evA' body)))) =
    mkSigma coh (mkSigma (eqA b evA-b)
      (mkSigma a' (mkSigma (eqA a' evA')
        (\ u v sel ->
          let mkSigma x (mkSigma le (mkSigma mem evB)) = body u v sel
          in mkSigma x (mkSigma le (mkSigma mem (eqB x a' mem evA' v evB)))))))
  convSound-Pi-fwd A A' B B' rho UCode eqA eqB ()
  convSound-Pi-fwd A A' B B' rho (FunEl g) eqA eqB ()

  --------------------------------------------------------------------
  -- convSound' — case analysis
  --------------------------------------------------------------------

  -- conv-refl
  convSound' (conv-refl dM) rho fits =
    let inv = theorem1 dM rho fits
    in mkSigma inv (mkSigma inv
         (mkSigma (\ u ev -> ev) (\ u ev -> ev)))

  -- conv-sym
  convSound' (conv-sym d) rho fits =
    let mkSigma invM (mkSigma invN (mkSigma fwd bwd)) = convSound' d rho fits
    in mkSigma invN (mkSigma invM (mkSigma bwd fwd))

  -- conv-trans
  convSound' (conv-trans d1 d2) rho fits =
    let mkSigma invM (mkSigma _    (mkSigma fwd1 bwd1)) = convSound' d1 rho fits
        mkSigma _    (mkSigma invP (mkSigma fwd2 bwd2)) = convSound' d2 rho fits
    in mkSigma invM (mkSigma invP
         (mkSigma (\ u ev -> fwd2 u (fwd1 u ev))
                  (\ u ev -> bwd1 u (bwd2 u ev))))

  -- conv-conv: transport InvTyp through type conversion
  convSound' (conv-conv d dAB _) rho fits =
    let mkSigma invM (mkSigma invN (mkSigma fwd bwd)) = convSound' d rho fits
        fwdAB = \ a' ev -> convSound dAB rho fits a' ev
        invM' = \ u ev ->
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) = invM u ev
          in mkSigma u' (mkSigma a'
               (mkSigma le (mkSigma evM (mkSigma fm (fwdAB a' evA)))))
        invN' = \ u ev ->
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evN (mkSigma fm evA)))) = invN u ev
          in mkSigma u' (mkSigma a'
               (mkSigma le (mkSigma evN (mkSigma fm (fwdAB a' evA)))))
    in mkSigma invM' (mkSigma invN' (mkSigma fwd bwd))

  -- conv-beta: from LTS.InvConv-beta
  convSound' (conv-beta {A = A} {B = B} {M = M} {a = a} dA dB dM da)
    rho fits =
    LTS.InvConv-beta A B M a rho fits
      (theorem1 da rho fits)
      (\ rho' x a0 fits' fm evA ->
        theorem1 dM (extendEnv rho' x)
          (mkSigma fits' (mkSigma a0 (mkSigma fm evA))))

  -- conv-Pi: forward/backward from convSound-Pi-fwd,
  -- InvTyp from LTS.InvTyp-Pi
  convSound' (conv-Pi {A = A} {A' = A'} {B = B} {B' = B'} _ _ _ d1 d2)
    rho fits =
    let mkSigma invA (mkSigma invA' (mkSigma fwdA bwdA)) = convSound' d1 rho fits
        fwd = \ u ev -> convSound-Pi-fwd A A' B B' rho u
                fwdA
                (\ x a0 fm evA w ->
                  convSound d2 (extendEnv rho x)
                    (mkSigma fits (mkSigma a0 (mkSigma fm evA))) w)
                ev
        bwd = \ u ev -> convSound-Pi-fwd A' A B' B rho u
                bwdA
                (\ x a0 fm evA' w ->
                  convSound-inv d2 (extendEnv rho x)
                    (mkSigma fits (mkSigma a0 (mkSigma fm
                      (bwdA a0 evA')))) w)
                ev
        invPiLHS = LTS.InvTyp-Pi A B rho fits invA
          (\ x a0 fm evA ->
            let mkSigma invB _ = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm evA)))
            in invB)
        invPiRHS = LTS.InvTyp-Pi A' B' rho fits invA'
          (\ x a0 fm evA' ->
            let mkSigma _ (mkSigma invB' _) = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm
                    (bwdA a0 evA'))))
            in invB')
    in mkSigma invPiLHS (mkSigma invPiRHS (mkSigma fwd bwd))

  -- conv-funext: from LTS.InvConv-funext
  convSound' (conv-funext {A = A} {B = B} {f = f} {g = g} dA d df dg)
    rho fits =
    LTS.InvConv-funext A B f g rho fits
      (theorem1 df rho fits)
      (theorem1 dg rho fits)
      (\ x a fm evA ->
        convSound' d (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))

  -- conv-App-fun: from LTS.InvConv-App-fun
  convSound' (conv-App-fun {A = A} {B = B} {f = f} {f' = f'} {a = a}
    dA _ dff' da) rho fits =
    LTS.InvConv-App-fun A B f f' a rho fits
      (convSound' dff' rho fits)
      (theorem1 da rho fits)

  -- conv-App-arg: from LTS.InvConv-App-arg
  convSound' (conv-App-arg {A = A} {B = B} {f = f} {a = a} {a' = a'}
    dA _ df daa') rho fits =
    LTS.InvConv-App-arg A B f a a' rho fits
      (theorem1 df rho fits)
      (convSound' daa' rho fits)

  --------------------------------------------------------------------
  -- theorem1 — case analysis
  --------------------------------------------------------------------

  -- ty-var
  theorem1 (ty-var {i = i} wf) rho fits u (mkSigma cu le) =
    let mkSigma a' (mkSigma fm evA) = Fits-var rho fits i
        li  = lookupEnv i rho
        cli = FinMem-coh-u li a' fm
    in mkSigma li (mkSigma a'
         (mkSigma le (mkSigma (mkSigma cli (LeCode-refl li cli))
           (mkSigma fm evA))))

  -- ty-U
  theorem1 (ty-U wf) rho fits u ev =
    mkSigma UCode (mkSigma UCode
      (mkSigma (snd ev)
        (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-conv
  theorem1 (ty-conv d1 d2 _) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) =
          theorem1 d1 rho fits u ev
    in mkSigma u' (mkSigma a'
         (mkSigma le (mkSigma evM
           (mkSigma fm (convSound d2 rho fits a' evA)))))

  -- ty-Pi
  theorem1 (ty-Pi {A = A} {B = B} d1 d2) rho fits u ev =
    LTS.InvTyp-Pi A B rho fits
      (theorem1 d1 rho fits)
      (\ x a fm evA ->
        theorem1 d2 (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))
      u ev

  -- ty-Lam
  theorem1 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) rho fits u ev =
    LTS.InvTyp-Lam A B M
      (\ rho' x a fits' fm evA ->
        theorem1 d3 (extendEnv rho' x)
          (mkSigma fits' (mkSigma a (mkSigma fm evA))))
      rho fits u ev

  -- ty-App
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 _ d2 d3)
    rho fits u ev =
    LTS.InvTyp-App A B f a rho fits
      (theorem1 d2 rho fits)
      (theorem1 d3 rho fits)
      u ev
