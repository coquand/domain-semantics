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

module CAST.TypingSemantics where

import CAST.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun ;
              nil ; cons)
open import CAST.PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
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
open import CAST.Selection using (Selection)
open import CAST.RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EvalRel-Comp ; EvalRel-Sup)
open import CAST.RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; Id ; cast ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1)
open import CAST.RawSyntax using () renaming (refl to refl-tm)  -- Expr `refl`, vs Eq.refl
open import CAST.TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  ty-Id ; ty-refl ; ty-sym ; ty-pi1 ; ty-pi2 ; ty-cast ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Id ; conv-cast-refl ; conv-Id-irr ; conv-cast-cong ;
  conv-pi1 ; conv-pi2 ; conv-cast-Pi)

-- All hard lemmas come from LemmaForTSSigma (0 postulates).
import CAST.LemmaForTS as LTS
open LTS using (Fits ; Typed ; InvTyp ; InvConv ;
  Fits-CoherentEnv ; Fits-var ; InvTyp-Id)
open import CAST.CastAgreement using (InvConv-cast-Pi)
open import CAST.EvalSubstitution using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
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
FinMem-Bot-elim (IdCode a b) ()

-- The only member of an Id-code is Bot (proof irrelevance).
FinMem-IdCode-elim : (u' a b : FinEl) -> FinMem u' (IdCode a b) -> Eq u' Bot
FinMem-IdCode-elim Bot          a b mem = refl
FinMem-IdCode-elim UCode        a b ()
FinMem-IdCode-elim (FunEl g)    a b ()
FinMem-IdCode-elim (PiCode c f) a b ()
FinMem-IdCode-elim (IdCode c d) a b ()

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
LeCode-Bot-eq (IdCode a f) Bot ()
LeCode-Bot-eq (IdCode a f) UCode le ()
LeCode-Bot-eq (IdCode a f) (FunEl h) le ()
LeCode-Bot-eq (IdCode a f) (PiCode b g) le ()
LeCode-Bot-eq (IdCode a f) (IdCode b g) le ()

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
  -- Helper: Id congruence on evaluation (no function part)
  --------------------------------------------------------------------

  convSound-Id-fwd : {n : Nat}
    (A A' B B' : Expr n)
    (rho : EnvApprox n) -> (u : FinEl) ->
    ((w : FinEl) -> EvalRel A rho w -> EvalRel A' rho w) ->
    ((w : FinEl) -> EvalRel B rho w -> EvalRel B' rho w) ->
    EvalRel (Id A B) rho u -> EvalRel (Id A' B') rho u
  convSound-Id-fwd A A' B B' rho Bot eqA eqB ev = tt
  convSound-Id-fwd A A' B B' rho (IdCode a b) eqA eqB
    (mkSigma coh (mkSigma evA-a evB-b)) =
    mkSigma coh (mkSigma (eqA a evA-a) (eqB b evB-b))
  convSound-Id-fwd A A' B B' rho UCode eqA eqB ()
  convSound-Id-fwd A A' B B' rho (FunEl g) eqA eqB ()
  convSound-Id-fwd A A' B B' rho (PiCode a f) eqA eqB ()

  --------------------------------------------------------------------
  -- Helper: a value of an Id-typed term is forced to Bot
  --------------------------------------------------------------------

  -- (G dropped from the signature: InvTyp/Typed do not mention it, so it is
  -- not inferable; we take the unfolded predicate instead.)
  Id-val-Bot : {n : Nat} {A B : Expr n} {rho : EnvApprox n}
    (p : Expr n) ->
    ((u : FinEl) -> EvalRel p rho u -> Typed p (Id A B) rho u) ->
    (u : FinEl) -> EvalRel p rho u -> Eq u Bot
  Id-val-Bot {A = A} {B = B} {rho = rho} p invP u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evp' (mkSigma fm evId)))) = invP u ev
    in LeCode-Bot-eq u u' le (aux u' a' fm evId)
    where
      aux : (u' a' : FinEl) -> FinMem u' a' ->
        EvalRel (Id A B) rho a' -> Eq u' Bot
      aux u' Bot            fm evId = FinMem-Bot-elim u' fm
      aux u' (IdCode a0 b0) fm evId = FinMem-IdCode-elim u' a0 b0 fm
      aux u' UCode          fm ()
      aux u' (FunEl g)      fm ()
      aux u' (PiCode a0 f0) fm ()

  --------------------------------------------------------------------
  -- cast-InvTyp:  InvTyp for  cast A B p M  at type B.
  --
  -- `cast` is GUARDED (downward-restriction semantics, RawSemantics):
  --   EvalRel (cast A B p M) rho u
  --     = Coherent u × Σ v. (LeCode u v × EvalRel M rho v
  --                          × Σ b. (EvalRel B rho b × FinMem v b))
  -- i.e. u sits below an M-value v that is a member of an approximant b of B.
  -- So the B-typing is already carried by the value: the typed enlargement is
  -- just (u' := v, btype := b) — adequacy holds by construction, with NO
  -- ⟦A⟧=⟦B⟧ assumption and without using the typing premises p, M:A, …
  --------------------------------------------------------------------

  cast-InvTyp : {n : Nat} {G : Ctx n} (A B p M : Expr n) ->
    (rho : EnvApprox n) -> Fits G rho ->
    InvTyp G (cast A B p M) B rho
  cast-InvTyp A B p M rho fits u
    (mkSigma cu (mkSigma v (mkSigma le-uv (mkSigma evM-v (mkSigma b (mkSigma evB-b fm-v-b)))))) =
    let cv = EvalRel-coh M rho v evM-v
    in mkSigma v (mkSigma b
         (mkSigma le-uv
           (mkSigma (mkSigma cv (mkSigma v (mkSigma (LeCode-refl v cv)
                      (mkSigma evM-v (mkSigma b (mkSigma evB-b fm-v-b))))))
             (mkSigma fm-v-b evB-b))))

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

  -- conv-Id: congruence Id A B ≡ Id A' B' : U  (mirror conv-Pi, no body)
  convSound' (conv-Id {A = A} {B = B} {A' = A'} {B' = B'}
    _ _ _ _ dAA' dBB') rho fits =
    let mkSigma invA (mkSigma invA' (mkSigma fwdA bwdA)) = convSound' dAA' rho fits
        mkSigma invB (mkSigma invB' (mkSigma fwdB bwdB)) = convSound' dBB' rho fits
        fwd = \ u ev -> convSound-Id-fwd A A' B B' rho u fwdA fwdB ev
        bwd = \ u ev -> convSound-Id-fwd A' A B' B rho u bwdA bwdB ev
        invId  = InvTyp-Id A  B  rho fits invA  invB
        invId' = InvTyp-Id A' B' rho fits invA' invB'
    in mkSigma invId (mkSigma invId' (mkSigma fwd bwd))

  -- conv-cast-refl: cast A B refl M ≡ M : B.  With A ≡ B : U (premise dAB),
  -- every member of ⟦M⟧ (M:A) is also a member of B, so the restriction that
  -- defines ⟦cast A B refl M⟧ keeps all of ⟦M⟧, i.e. the two values coincide.
  convSound' {G = G} (conv-cast-refl {A = A} {B = B} {M = M} dA dB dM dAB) rho fits =
    let crho = Fits-CoherentEnv rho fits
        -- InvTyp for M at B: retype M:A enlargements through A ≡ B.
        invMB : InvTyp G M B rho
        invMB = \ u ev ->
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) =
                theorem1 dM rho fits u ev
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM
               (mkSigma fm (convSound dAB rho fits a' evA)))))
        -- fwd: a cast value u sits below an M-value v; bring it down to u.
        fwd = \ u ev ->
          let mkSigma cu (mkSigma v (mkSigma le-uv (mkSigma evM-v _))) = ev
          in EvalRel-down M rho v u crho cu evM-v le-uv
        -- bwd: an M-value u, enlarged to u' and B-typed at a' via A≡B, is a
        -- B-typed M-value, hence a cast value.
        bwd = \ u ev ->
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM-u' (mkSigma fm evA)))) =
                theorem1 dM rho fits u ev
              cu = EvalRel-coh M rho u ev
          in mkSigma cu (mkSigma u' (mkSigma le (mkSigma evM-u'
               (mkSigma a' (mkSigma (convSound dAB rho fits a' evA) fm)))))
    in mkSigma (cast-InvTyp A B refl-tm M rho fits) (mkSigma invMB (mkSigma fwd bwd))

  -- conv-Id-irr: proof irrelevance.  Both p and q are proofs of Id A B, so
  -- (by theorem1) every value of either is forced to Bot, where every term's
  -- evaluation holds.  fwd/bwd transport tt across u = Bot.
  convSound' (conv-Id-irr {A = A} {B = B} {p = p} {q = q} dp dq) rho fits =
    let invP = theorem1 dp rho fits
        invQ = theorem1 dq rho fits
        fwd = \ u ev ->
          Eq-transport (\ w -> EvalRel q rho w) (Eq-sym (Id-val-Bot p invP u ev))
            (EvalRel-Bot q rho)
        bwd = \ u ev ->
          Eq-transport (\ w -> EvalRel p rho w) (Eq-sym (Id-val-Bot q invQ u ev))
            (EvalRel-Bot p rho)
    in mkSigma invP (mkSigma invQ (mkSigma fwd bwd))

  -- conv-cast-cong: cast A B p M ≡ cast A' B' p' M' : B.  Both InvTyp parts come
  -- from cast-InvTyp (guarded restriction); the RHS is at B', retyped to B via
  -- B ≡ B'.  fwd/bwd rebuild the B-typed M-value witness across M ≡ M' and B ≡ B'.
  convSound' (conv-cast-cong {A = A} {B = B} {A' = A'} {B' = B'}
    {p = p} {p' = p'} {M = M} {M' = M'}
    dA dB dp dM dA' dB' dp' dM' dAA' dBB' dMM') rho fits =
    let invL = cast-InvTyp A  B  p  M  rho fits
        invR-at-B' = cast-InvTyp A' B' p' M' rho fits
        invR = \ u ev ->
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evB')))) =
                invR-at-B' u ev
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM
               (mkSigma fm (convSound-inv dBB' rho fits a' evB')))))
        -- fwd: (B-typed M-value) ↦ (B'-typed M'-value), via M≡M' and B≡B'.
        fwd = \ u ev ->
          let mkSigma cu (mkSigma v (mkSigma le-uv (mkSigma evM-v (mkSigma b (mkSigma evB-b fm))))) = ev
          in mkSigma cu (mkSigma v (mkSigma le-uv
               (mkSigma (convSound dMM' rho fits v evM-v)
                 (mkSigma b (mkSigma (convSound dBB' rho fits b evB-b) fm)))))
        -- bwd: (B'-typed M'-value) ↦ (B-typed M-value), via M≡M' and B≡B'.
        bwd = \ u ev ->
          let mkSigma cu (mkSigma v (mkSigma le-uv (mkSigma evM'-v (mkSigma b (mkSigma evB'-b fm))))) = ev
          in mkSigma cu (mkSigma v (mkSigma le-uv
               (mkSigma (convSound-inv dMM' rho fits v evM'-v)
                 (mkSigma b (mkSigma (convSound-inv dBB' rho fits b evB'-b) fm)))))
    in mkSigma invL (mkSigma invR (mkSigma fwd bwd))

  -- conv-pi1: pi1 p ≡ pi1 p' : Id A C.  Both are proofs; value forced to Bot
  -- (directly, by the EvalRel definition of pi1).  Goal-driven so the two
  -- InvTyp / fwd / bwd components pin to their respective terms pi1 p / pi1 p'.
  convSound' (conv-pi1 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10) rho fits =
    mkSigma (\ { Bot ev -> mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))) ; UCode () ; (FunEl g) () ;
                 (PiCode a f) () ; (IdCode a b) () })
      (mkSigma (\ { Bot ev -> mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))) ; UCode () ; (FunEl g) () ;
                    (PiCode a f) () ; (IdCode a b) () })
        (mkSigma (\ { Bot ev -> tt ; UCode () ; (FunEl g) () ;
                      (PiCode a f) () ; (IdCode a b) () })
                 (\ { Bot ev -> tt ; UCode () ; (FunEl g) () ;
                      (PiCode a f) () ; (IdCode a b) () })))

  -- conv-pi2: pi2 p N ≡ pi2 p' N' : Id (..) (..).  Both are proofs; value
  -- forced to Bot (directly, by the EvalRel definition of pi2).
  convSound' (conv-pi2 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12) rho fits =
    mkSigma (\ { Bot ev -> mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))) ; UCode () ; (FunEl g) () ;
                 (PiCode a f) () ; (IdCode a b) () })
      (mkSigma (\ { Bot ev -> mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))) ; UCode () ; (FunEl g) () ;
                    (PiCode a f) () ; (IdCode a b) () })
        (mkSigma (\ { Bot ev -> tt ; UCode () ; (FunEl g) () ;
                      (PiCode a f) () ; (IdCode a b) () })
                 (\ { Bot ev -> tt ; UCode () ; (FunEl g) () ;
                      (PiCode a f) () ; (IdCode a b) () })))

  -- conv-cast-Pi : the coe-Pi reduction, via InvConv-cast-Pi (CastAgreement)
  convSound' (conv-cast-Pi {A = A} {C = C} {B = B} {D = D} {p = p} {M = M} {N = N}
                           dA dB dC dD dp dM dN) rho fits =
    InvConv-cast-Pi A C B D p M N rho fits (theorem1 dM rho fits) (theorem1 dN rho fits)

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

  -- ty-Id: Id A B : U  (mirror ty-Pi, via InvTyp-Id)
  theorem1 (ty-Id {A = A} {B = B} d1 d2) rho fits u ev =
    InvTyp-Id A B rho fits
      (theorem1 d1 rho fits)
      (theorem1 d2 rho fits)
      u ev

  -- ty-refl: refl : Id A A.  A proof; value forced to Bot.
  theorem1 (ty-refl d) rho fits Bot ev =
    mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
  theorem1 (ty-refl d) rho fits UCode ()
  theorem1 (ty-refl d) rho fits (FunEl g) ()
  theorem1 (ty-refl d) rho fits (PiCode a f) ()
  theorem1 (ty-refl d) rho fits (IdCode a b) ()

  -- ty-sym: sym p : Id B A.  A proof; value forced to Bot.
  theorem1 (ty-sym d1 d2 d3) rho fits Bot ev =
    mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
  theorem1 (ty-sym d1 d2 d3) rho fits UCode ()
  theorem1 (ty-sym d1 d2 d3) rho fits (FunEl g) ()
  theorem1 (ty-sym d1 d2 d3) rho fits (PiCode a f) ()
  theorem1 (ty-sym d1 d2 d3) rho fits (IdCode a b) ()

  -- ty-pi1: pi1 p : Id A C.  A proof; value forced to Bot.
  theorem1 (ty-pi1 d1 d2 d3 d4 d5) rho fits Bot ev =
    mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
  theorem1 (ty-pi1 d1 d2 d3 d4 d5) rho fits UCode ()
  theorem1 (ty-pi1 d1 d2 d3 d4 d5) rho fits (FunEl g) ()
  theorem1 (ty-pi1 d1 d2 d3 d4 d5) rho fits (PiCode a f) ()
  theorem1 (ty-pi1 d1 d2 d3 d4 d5) rho fits (IdCode a b) ()

  -- ty-pi2: pi2 p N : Id (B[N]) (D[..]).  A proof; value forced to Bot.
  theorem1 (ty-pi2 d1 d2 d3 d4 d5 d6) rho fits Bot ev =
    mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
  theorem1 (ty-pi2 d1 d2 d3 d4 d5 d6) rho fits UCode ()
  theorem1 (ty-pi2 d1 d2 d3 d4 d5 d6) rho fits (FunEl g) ()
  theorem1 (ty-pi2 d1 d2 d3 d4 d5 d6) rho fits (PiCode a f) ()
  theorem1 (ty-pi2 d1 d2 d3 d4 d5 d6) rho fits (IdCode a b) ()

  -- ty-cast: cast A B p M : B.  Guarded restriction ⇒ adequacy by construction.
  theorem1 (ty-cast {A = A} {B = B} {p = p} {M = M} d1 d2 d3 d4) rho fits u ev =
    cast-InvTyp A B p M rho fits u ev
