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

module NAT.Model.Soundness where

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ;
              nil ; cons)
open import NAT.Domain.Kernel using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; LeFunCode ;
  FinMem ; FinMemFun ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf ; NotBot ;
  EvalFun ; EvalFun-mon ; Coherent-EvalFun ;
  finMem-upward ; sucNat-from ;
  absurdEl ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; comp-Bot-r ; comp-Bot-l ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  FinMemAllU)
open import NAT.Model.Selection using (Selection)
open import NAT.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EvalRel-Comp ; EvalRel-Sup ; Approx ; Approx-mon ; Coherent-val-LeBot-absurd)
open import NAT.Syntax.Raw using (Expr ; Var ; U ; Pi ; Lam ; App ; Y ;
  NatT ; Zero ; Suc ; Case ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  subst-ren ; substExpr-ext ; subst1Sub ; wkRen ; Eq-trans)
open import NAT.Syntax.Reduction using (substExpr-id)
open import NAT.Syntax.Typing using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  ty-NatT ; ty-Zero ; ty-Suc ; ty-Case ; ty-Case-dep ; ty-Y ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Y ; conv-Y-cong ;
  conv-case-zero ; conv-case-suc ; conv-Suc ; conv-Case ;
  conv-case-zero-dep ; conv-case-suc-dep ; conv-Case-dep)

-- All hard lemmas come from LemmaForTSSigma (0 postulates).
import NAT.Model.SoundnessLemmas as LTS
open LTS using (Fits ; Typed ; InvTyp ; InvConv ;
  Fits-CoherentEnv ; Fits-var)
open import NAT.Model.EvalSubstitution using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
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
FinMem-Bot-elim NatCode      ()
FinMem-Bot-elim ZeroEl       ()
FinMem-Bot-elim (SucEl u)    ()

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
-- u' a Nat-value code: Eq u' Bot is impossible
LeCode-Bot-eq UCode NatCode le ()
LeCode-Bot-eq UCode ZeroEl le ()
LeCode-Bot-eq UCode (SucEl b) le ()
LeCode-Bot-eq (FunEl g) NatCode le ()
LeCode-Bot-eq (FunEl g) ZeroEl le ()
LeCode-Bot-eq (FunEl g) (SucEl b) le ()
LeCode-Bot-eq (PiCode a f) NatCode le ()
LeCode-Bot-eq (PiCode a f) ZeroEl le ()
LeCode-Bot-eq (PiCode a f) (SucEl b) le ()
-- u a Nat-value code: u'=Bot kills le, else Eq u' Bot impossible
LeCode-Bot-eq NatCode Bot ()
LeCode-Bot-eq NatCode UCode le ()
LeCode-Bot-eq NatCode (FunEl h) le ()
LeCode-Bot-eq NatCode (PiCode b g) le ()
LeCode-Bot-eq NatCode NatCode le ()
LeCode-Bot-eq NatCode ZeroEl le ()
LeCode-Bot-eq NatCode (SucEl b) le ()
LeCode-Bot-eq ZeroEl Bot ()
LeCode-Bot-eq ZeroEl UCode le ()
LeCode-Bot-eq ZeroEl (FunEl h) le ()
LeCode-Bot-eq ZeroEl (PiCode b g) le ()
LeCode-Bot-eq ZeroEl NatCode le ()
LeCode-Bot-eq ZeroEl ZeroEl le ()
LeCode-Bot-eq ZeroEl (SucEl b) le ()
LeCode-Bot-eq (SucEl a) Bot ()
LeCode-Bot-eq (SucEl a) UCode le ()
LeCode-Bot-eq (SucEl a) (FunEl h) le ()
LeCode-Bot-eq (SucEl a) (PiCode b g) le ()
LeCode-Bot-eq (SucEl a) NatCode le ()
LeCode-Bot-eq (SucEl a) ZeroEl le ()
LeCode-Bot-eq (SucEl a) (SucEl b) le ()

-- wk/subst1 cancellation: subst1 (wk A) N = A   (verified Fact 3)
wk-subst1-cancel : {n : Nat} (A N : Expr n) -> Eq (subst1 (wkExpr A) N) A
wk-subst1-cancel A N =
  Eq-trans (subst-ren (subst1Sub N) wkRen A)
    (Eq-trans (substExpr-ext (\ i -> subst1Sub N (wkRen i)) (\ i -> Var i) (\ i -> refl) A)
              (substExpr-id A))

-- EvalRel-level soundness of the Y unfolding  Y g = g (Y g).
Y-unfold-fwd : {n : Nat} (g : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  EvalRel (Y g) rho u -> EvalRel (App g (Y g)) rho u
Y-unfold-fwd g rho u ev = go (fst ev) u (snd ev)
  where
    go : (k : Nat) (w : FinEl) ->
      Approx (\ p z -> EvalRel g rho (FunEl (cons (mkSigma p z) nil))) k w ->
      EvalRel (App g (Y g)) rho w
    go k Bot ap = tt
    go zero UCode ap =
      absurdEl (Coherent-val-LeBot-absurd UCode (mkSigma tt tt) (snd ap))
    go zero (FunEl g') ap =
      absurdEl (Coherent-val-LeBot-absurd (FunEl g') (mkSigma (fst ap) tt) (snd ap))
    go zero (PiCode a' f') ap =
      absurdEl (Coherent-val-LeBot-absurd (PiCode a' f') (mkSigma (fst ap) tt) (snd ap))
    go zero NatCode ap =
      absurdEl (Coherent-val-LeBot-absurd NatCode (mkSigma tt tt) (snd ap))
    go zero ZeroEl ap =
      absurdEl (Coherent-val-LeBot-absurd ZeroEl (mkSigma tt tt) (snd ap))
    go zero (SucEl w') ap =
      absurdEl (Coherent-val-LeBot-absurd (SucEl w') (mkSigma (fst ap) tt) (snd ap))
    go (suc j) UCode ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))
    go (suc j) (FunEl g') ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))
    go (suc j) (PiCode a' f') ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))
    go (suc j) NatCode ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))
    go (suc j) ZeroEl ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))
    go (suc j) (SucEl w') ap =
      mkSigma (fst ap) (mkSigma (mkSigma j (fst (snd ap))) (snd (snd ap)))

Y-unfold-bwd : {n : Nat} (g : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  EvalRel (App g (Y g)) rho u -> EvalRel (Y g) rho u
Y-unfold-bwd g rho Bot ev = mkSigma zero (mkSigma tt (LeCode-Bot Bot))
Y-unfold-bwd g rho UCode ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))
Y-unfold-bwd g rho (FunEl g') ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))
Y-unfold-bwd g rho (PiCode a' f') ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))
Y-unfold-bwd g rho NatCode ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))
Y-unfold-bwd g rho ZeroEl ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))
Y-unfold-bwd g rho (SucEl w') ev =
  mkSigma (suc (fst (fst (snd ev)))) (mkSigma (fst ev)
    (mkSigma (snd (fst (snd ev))) (snd (snd ev))))

-- InvTyp for  Y g : A  built from InvTyp for  g : Π(x:A)A  (no aU needed;
-- this is exactly the theorem1 (ty-Y …) body, factored so the conv-Y-cong
-- soundness can reuse it on both g and g').
mkY-InvTyp : {n : Nat} {G : Ctx n} (A g : Expr n) (rho : EnvApprox n) ->
  Fits G rho -> InvTyp G g (Pi A (wkExpr A)) rho -> InvTyp G (Y g) A rho
mkY-InvTyp {G = G} A g rho fits invg u ev =
  let invApp  = LTS.InvTyp-App A (wkExpr A) g (Y g) rho fits invg
      tApp    = invApp u (Y-unfold-fwd g rho u ev)
      u'      = S.fst tApp
      a'      = S.fst (S.snd tApp)
      le      = S.fst (S.snd (S.snd tApp))
      evAppU' = S.fst (S.snd (S.snd (S.snd tApp)))
      fm      = S.fst (S.snd (S.snd (S.snd (S.snd tApp))))
      evTa'   = S.snd (S.snd (S.snd (S.snd (S.snd tApp))))
      evYU'   = Y-unfold-bwd g rho u' evAppU'
      evAa'   = S.Eq-transport (\ T -> EvalRel T rho a') (wk-subst1-cancel A (Y g)) evTa'
  in S.mkSigma u' (S.mkSigma a' (S.mkSigma le (S.mkSigma evYU' (S.mkSigma fm evAa'))))

-- EvalRel-level Y congruence: a pointwise step implication  g ⊑ g'  lifts
-- through the Kleene approximant union (Approx-mon, index-preserving).
Y-cong-eval : {n : Nat} (g g' : Expr n) (rho : EnvApprox n) ->
  ((w : FinEl) -> EvalRel g rho w -> EvalRel g' rho w) ->
  (u : FinEl) -> EvalRel (Y g) rho u -> EvalRel (Y g') rho u
Y-cong-eval g g' rho gle u ev =
  S.mkSigma (S.fst ev)
    (Approx-mon (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
                (\ p w -> EvalRel g' rho (FunEl (cons (mkSigma p w) nil)))
                (\ p w sw -> gle (FunEl (cons (mkSigma p w) nil)) sw)
                (S.fst ev) u (S.snd ev))

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

  -- conv-Y :  Y g = g (Y g)  at A
  convSound' (conv-Y {G = G} {A = A} {g = g} aU dg) rho fits =
    let invM = theorem1 (ty-Y aU dg) rho fits
        invN-raw = LTS.InvTyp-App A (wkExpr A) g (Y g) rho fits (theorem1 dg rho fits)
        invN = Eq-transport (\ T -> InvTyp G (App g (Y g)) T rho)
                 (wk-subst1-cancel A (Y g)) invN-raw
    in mkSigma invM (mkSigma invN
         (mkSigma (\ w ev -> Y-unfold-fwd g rho w ev)
                  (\ w ev -> Y-unfold-bwd g rho w ev)))

  -- conv-Y-cong :  Y g = Y g'  at A   (from  g = g' : Π(x:A)A)
  convSound' (conv-Y-cong {A = A} {g = g} {g' = g'} aU dcvg) rho fits =
    let mkSigma invg (mkSigma invg' (mkSigma fwdg bwdg)) = convSound' dcvg rho fits
    in mkSigma (mkY-InvTyp A g rho fits invg)
         (mkSigma (mkY-InvTyp A g' rho fits invg')
           (mkSigma (\ w ev -> Y-cong-eval g g' rho fwdg w ev)
                    (\ w ev -> Y-cong-eval g' g rho bwdg w ev)))

  -- conv-case-zero: from LTS.InvConv-case-zero
  convSound' (conv-case-zero {C = C} {a = a} {b = b} dC da db) rho fits =
    LTS.InvConv-case-zero C a b rho fits
      (theorem1 dC rho fits) (theorem1 da rho fits) (theorem1 db rho fits)

  -- conv-case-suc: from LTS.InvConv-case-suc
  convSound' (conv-case-suc {C = C} {m = m} {a = a} {b = b} dC dm da db) rho fits =
    LTS.InvConv-case-suc C m a b rho fits
      (theorem1 dC rho fits) (theorem1 dm rho fits)
      (theorem1 da rho fits) (theorem1 db rho fits)

  -- conv-Suc: congruence via LTS.EvalRel-Suc-map / LTS.InvTyp-Suc
  convSound' {G = G} (conv-Suc {m = m} {m' = m'} d) rho fits =
    let mkSigma invm (mkSigma invm' (mkSigma fwd bwd)) = convSound' d rho fits
    in mkSigma (LTS.InvTyp-Suc {G = G} m rho invm)
         (mkSigma (LTS.InvTyp-Suc {G = G} m' rho invm')
           (mkSigma (LTS.EvalRel-Suc-map m m' rho fwd)
                    (LTS.EvalRel-Suc-map m' m rho bwd)))

  -- conv-Case: congruence via LTS.InvConv-Case
  convSound' (conv-Case {C = C} {M = M} {M' = M'} {a = a} {a' = a'}
    {b = b} {b' = b'} dC dMM' daa' dbb') rho fits =
    LTS.InvConv-Case C M M' a a' b b' rho fits
      (theorem1 dC rho fits)
      (convSound' dMM' rho fits) (convSound' daa' rho fits) (convSound' dbb' rho fits)

  -- conv-case-zero-dep: from LTS.InvConv-case-zero-dep
  convSound' (conv-case-zero-dep {C = C} {a = a} {b = b} dC da db) rho fits =
    LTS.InvConv-case-zero-dep C a b rho fits
      (theorem1 da rho fits) (theorem1 db rho fits)

  -- conv-case-suc-dep: from LTS.InvConv-case-suc-dep
  convSound' (conv-case-suc-dep {C = C} {m = m} {a = a} {b = b} dC dm da db) rho fits =
    LTS.InvConv-case-suc-dep C m a b rho fits
      (theorem1 dm rho fits) (theorem1 da rho fits) (theorem1 db rho fits)

  -- conv-Case-dep: congruence via LTS.InvConv-Case-dep
  convSound' (conv-Case-dep {C = C} {M = M} {M' = M'} {a = a} {a' = a'}
    {b = b} {b' = b'} dC dMM' daa' dbb') rho fits =
    LTS.InvConv-Case-dep C M M' a a' b b' rho fits
      (convSound' dMM' rho fits) (convSound' daa' rho fits) (convSound' dbb' rho fits)

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
      u ev

  -- ty-Y :  Y g : A   (Y g = g (Y g);  membership comes from g : A -> A,
  -- transported through the unfolding;  no Kleene induction needed).
  theorem1 (ty-Y {A = A} {g = g} aU dg) rho fits u ev =
    let invApp  = LTS.InvTyp-App A (wkExpr A) g (Y g) rho fits (theorem1 dg rho fits)
        tApp    = invApp u (Y-unfold-fwd g rho u ev)
        u'      = fst tApp
        a'      = fst (snd tApp)
        le      = fst (snd (snd tApp))
        evAppU' = fst (snd (snd (snd tApp)))
        fm      = fst (snd (snd (snd (snd tApp))))
        evTa'   = snd (snd (snd (snd (snd tApp))))
        evYU'   = Y-unfold-bwd g rho u' evAppU'
        evAa'   = Eq-transport (\ T -> EvalRel T rho a') (wk-subst1-cancel A (Y g)) evTa'
    in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evYU' (mkSigma fm evAa'))))

  -- ty-NatT
  theorem1 (ty-NatT wf) rho fits u ev =
    mkSigma NatCode (mkSigma UCode
      (mkSigma (snd ev) (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-Zero
  theorem1 (ty-Zero wf) rho fits u ev =
    mkSigma ZeroEl (mkSigma NatCode
      (mkSigma (snd ev) (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-Suc
  theorem1 {G = G} (ty-Suc {m = m} d) rho fits u ev =
    LTS.InvTyp-Suc {G = G} m rho (theorem1 d rho fits) u ev

  -- ty-Case
  theorem1 (ty-Case {C = C} {M = M} {a = a} {b = b} dC dM da db) rho fits u ev =
    LTS.InvTyp-Case C M a b rho fits
      (theorem1 dC rho fits) (theorem1 dM rho fits)
      (theorem1 da rho fits) (theorem1 db rho fits)
      u ev

  -- ty-Case-dep
  theorem1 (ty-Case-dep {C = C} {M = M} {a = a} {b = b} dC dM da db) rho fits u ev =
    LTS.InvTyp-Case-dep C M a b rho fits
      (theorem1 dM rho fits) (theorem1 da rho fits) (theorem1 db rho fits)
      u ev
