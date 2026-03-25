{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- TypingSemantics.agda
--
-- Conversion soundness and typing soundness (Theorem 1) for the
-- finite relational semantics.
--
-- Central invariants (from LemmaForTS):
--   InvTyp  G M A rho   — every u ≤ ⟦M⟧ρ has a typed enlargement
--   InvConv G M N A rho — InvTyp for both sides + bidir evaluation
--
-- 0 postulates.
------------------------------------------------------------------------

module TypingSemantics where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun ;
              nil ; cons)
open import PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; LeFunCode ;
  FinMem ; FinMemFun ; FinMemAllProp ; FinMem-coh-u ; FinMem-a-in-U ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf ; NotBot ;
  FinMem-Prop-Bot ; FinMem-Prop-to-U ; EvalFun-in-PropCode ;
  EvalFun ; EvalFun-mon ; Coherent-EvalFun ;
  finMem-upward ;
  LeCode-PropCode-cases ; Or ; inl ; inr ;
  absurdEl)
open import Selection using (Selection)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe)
open import RawSyntax using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1)
open import TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Prop ; conv-Prop-U ;
  conv-beta ; conv-Pi ; conv-Pi-Prop ; conv-funext ; conv-App-fun ; conv-App-arg)

-- All hard lemmas come from LemmaForTS (0 postulates).
import LemmaForTS as LTS
open LTS using (Fits ; Typed ; InvTyp ; InvConv)

------------------------------------------------------------------------
-- Helpers for proof-irrelevance
------------------------------------------------------------------------

-- If FinMem u' Bot, then u' = Bot
FinMem-Bot-elim : (u' : FinEl) -> FinMem u' Bot -> Eq u' Bot
FinMem-Bot-elim Bot          mem = refl
FinMem-Bot-elim UCode        ()
FinMem-Bot-elim PropCode     ()
FinMem-Bot-elim (FunEl g)    ()
FinMem-Bot-elim (PiCode a f) ()

-- If LeCode u u' and u' = Bot, then u = Bot (since LeCode u Bot = Top only for u = Bot)
LeCode-Bot-eq : (u u' : FinEl) -> LeCode u u' -> Eq u' Bot -> Eq u Bot
LeCode-Bot-eq Bot u' le eq = refl
LeCode-Bot-eq UCode Bot ()
LeCode-Bot-eq UCode UCode le ()
LeCode-Bot-eq UCode PropCode le ()
LeCode-Bot-eq UCode (FunEl h) le ()
LeCode-Bot-eq UCode (PiCode b g) le ()
LeCode-Bot-eq PropCode Bot ()
LeCode-Bot-eq PropCode UCode le ()
LeCode-Bot-eq PropCode PropCode le ()
LeCode-Bot-eq PropCode (FunEl h) le ()
LeCode-Bot-eq PropCode (PiCode b g) le ()
LeCode-Bot-eq (FunEl g) Bot ()
LeCode-Bot-eq (FunEl g) UCode le ()
LeCode-Bot-eq (FunEl g) PropCode le ()
LeCode-Bot-eq (FunEl g) (FunEl h) le ()
LeCode-Bot-eq (FunEl g) (PiCode b h) le ()
LeCode-Bot-eq (PiCode a f) Bot ()
LeCode-Bot-eq (PiCode a f) UCode le ()
LeCode-Bot-eq (PiCode a f) PropCode le ()
LeCode-Bot-eq (PiCode a f) (FunEl h) le ()
LeCode-Bot-eq (PiCode a f) (PiCode b g) le ()

-- If LeCode a' PropCode and FinMem u' a', produce FinMem u' UCode
-- a' = Bot: u' = Bot, FinMem Bot UCode = Top.
-- a' = PropCode: FinMem u' PropCode, use FinMem-Prop-to-U.
FinMem-Prop-in-U : (u' a' : FinEl) -> FinMem u' a' -> LeCode a' PropCode ->
  FinMem u' UCode
FinMem-Prop-in-U u' Bot fm le =
  Eq-transport (\ x -> FinMem x UCode) (Eq-sym (FinMem-Bot-elim u' fm)) tt
FinMem-Prop-in-U u' UCode fm ()
FinMem-Prop-in-U u' PropCode fm le = FinMem-Prop-to-U u' fm
FinMem-Prop-in-U u' (FunEl g) fm ()
FinMem-Prop-in-U u' (PiCode a f) fm ()

------------------------------------------------------------------------
-- Prop-collapse: if FinMem u a, LeCode a a', FinMem a' PropCode,
-- then u = Bot.
--
-- The only non-trivial case is u = FunEl h at a = PiCode c' g'
-- with a' = PiCode c g in PropCode. Each value yi in h has
-- FinMem yi (EvalFun g' xi). By EvalFun-mon + EvalFun-in-PropCode +
-- finMem-upward + FinMem-Prop-Bot: yi = Bot. Contradicts NotBot.
------------------------------------------------------------------------

-- Helper: FinMem (FunEl h) (PiCode c' g') is impossible when
-- LeFunCode g' g and FinMem (PiCode c g) PropCode
{-# TERMINATING #-}
Prop-collapse-FunEl-absurd : (h : FinFun) (c' : FinEl) (g' : FinFun)
  (c : FinEl) (g : FinFun) ->
  FinMemFun h c' g' -> CoherentFun h ->
  LeFunCode g' g -> CoherentFunTail g' -> CoherentFunTail g ->
  FinMem c' UCode -> FinMemAllProp g c -> Empty
Prop-collapse-FunEl-absurd nil c' g' c g fmf ()
Prop-collapse-FunEl-absurd (cons p ps) c' g' c g fmf coh lfg cg' cg c'U allP =
  let cohT = cft-from-cf (cons p ps) coh
      nb = CFTcons.val-nbot cohT
      cp = CFTcons.key-coh cohT
      cv = CFTcons.val-coh cohT
      -- FinMem (snd p) (EvalFun g' (fst p))
      mem-v = snd (fst fmf)
      -- EvalFun g' (fst p) ≤ EvalFun g (fst p) by monotonicity
      le-eval = EvalFun-mon g' g (fst p) cg' cg cp lfg
      -- EvalFun g (fst p) : PropCode
      evalP = EvalFun-in-PropCode g (fst p) c cg cp allP
      -- EvalFun g (fst p) : UCode (from Prop-to-U)
      evalU = FinMem-Prop-to-U (EvalFun g (fst p)) evalP
      -- Coherent
      coh-g' = Coherent-EvalFun g' (fst p) cg' cp
      coh-g = Coherent-EvalFun g (fst p) cg cp
      -- FinMem (snd p) (EvalFun g (fst p)) by finMem-upward
      mem-v-up = finMem-upward (snd p) (EvalFun g' (fst p)) (EvalFun g (fst p))
                   le-eval coh-g' coh-g mem-v evalU
      -- snd p = Bot by FinMem-Prop-Bot
      eq = FinMem-Prop-Bot (snd p) (EvalFun g (fst p)) mem-v-up evalP
  in Eq-transport NotBot eq nb

-- Prop-collapse: FinMem u a, LeCode a a', FinMem a' PropCode → u = Bot
Prop-collapse : (u a a' : FinEl) ->
  FinMem u a -> LeCode a a' -> FinMem a' PropCode -> Eq u Bot
Prop-collapse u a a' fm le a'P with FinMem-Prop-in-U-helper a' a'P
  where
    -- Case split on a': either Bot or PiCode with PropCode membership
    FinMem-Prop-in-U-helper : (a' : FinEl) -> FinMem a' PropCode ->
      Or (Eq a' Bot) (Sigma FinEl (\ c -> Sigma FinFun (\ g ->
        Pair (Eq a' (PiCode c g)) (Pair (FinMem c UCode)
          (Pair (FinMemAllProp g c) (CoherentFunTail g))))))
    FinMem-Prop-in-U-helper Bot          mem = inl refl
    FinMem-Prop-in-U-helper UCode        ()
    FinMem-Prop-in-U-helper PropCode     ()
    FinMem-Prop-in-U-helper (FunEl g)    ()
    FinMem-Prop-in-U-helper (PiCode c g) mem =
      inr (mkSigma c (mkSigma g (mkSigma refl mem)))
... | inl a'bot =
  let abot = LeCode-Bot-eq a a' le a'bot
  in FinMem-Bot-elim u (Eq-transport (FinMem u) abot fm)
... | inr (mkSigma c (mkSigma g (mkSigma a'eq (mkSigma cU (mkSigma allP cohg))))) =
  let le' = Eq-transport (LeCode a) a'eq le
  in Prop-collapse-inner u a c g fm le' cU allP cohg
  where
    Prop-collapse-inner : (u a : FinEl) (c : FinEl) (g : FinFun) ->
      FinMem u a -> LeCode a (PiCode c g) ->
      FinMem c UCode -> FinMemAllProp g c -> CoherentFunTail g ->
      Eq u Bot
    -- a = Bot: FinMem u Bot → u = Bot
    Prop-collapse-inner u Bot c g fm le cU allP cohg = FinMem-Bot-elim u fm
    -- a = UCode: LeCode UCode (PiCode c g) = Empty
    Prop-collapse-inner u UCode c g fm ()
    Prop-collapse-inner u PropCode c g fm ()
    Prop-collapse-inner u (FunEl h) c g fm ()
    -- a = PiCode c' g': FinMem u (PiCode c' g')
    Prop-collapse-inner Bot (PiCode c' g') c g fm le cU allP cohg = refl
    Prop-collapse-inner UCode (PiCode c' g') c g ()
    Prop-collapse-inner PropCode (PiCode c' g') c g ()
    Prop-collapse-inner (PiCode x y) (PiCode c' g') c g ()
    Prop-collapse-inner (FunEl h) (PiCode c' g') c g fm le cU allP cohg =
      let -- Extract from FinMem (FunEl h) (PiCode c' g')
          fmf = fst fm
          cfh = fst (snd fm)
          piU = snd (snd fm)
          -- From LeCode (PiCode c' g') (PiCode c g)
          le-g = snd le
          -- CoherentFunTail g'
          cohg' = snd (snd piU)
      in absurdEl (Prop-collapse-FunEl-absurd h c' g' c g fmf cfh le-g cohg' cohg (fst piU) allP)

-- Helper for conv-Prop: chain from FinMem through Prop to Bot
conv-Prop-chain : (u' a1 a2 b : FinEl) ->
  FinMem u' a1 -> LeCode a1 a2 -> FinMem a2 b -> LeCode b PropCode ->
  Eq u' Bot
conv-Prop-chain u' a1 a2 Bot fm1 le-a fm2 le-b =
  let a2bot = FinMem-Bot-elim a2 fm2
      a1bot = LeCode-Bot-eq a1 a2 le-a a2bot
  in FinMem-Bot-elim u' (Eq-transport (FinMem u') a1bot fm1)
conv-Prop-chain u' a1 a2 UCode fm1 le-a fm2 ()
conv-Prop-chain u' a1 a2 PropCode fm1 le-a fm2 le-b =
  Prop-collapse u' a1 a2 fm1 le-a fm2
conv-Prop-chain u' a1 a2 (FunEl g) fm1 le-a fm2 ()
conv-Prop-chain u' a1 a2 (PiCode c g) fm1 le-a fm2 ()

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
  --
  -- eqB takes FinMem + EvalRel evidence (not just Coherent)
  -- so the caller can build extended Fits for the mutual IH.
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
  convSound-Pi-fwd A A' B B' rho PropCode eqA eqB ()
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

  -- conv-Prop: proof-irrelevance
  -- If A : Prop, M : A, N : A, then EvalRel M rho u -> EvalRel N rho u.
  -- Key: by theorem1, any u with EvalRel M rho u has enlargement u'
  -- with FinMem u' a' and EvalRel A rho a' where A : Prop, so the type
  -- derivation gives a' with LeCode a' PropCode via theorem1 on dP.
  -- Actually: dM : HasType G M A with dP : HasType G A Prop.
  -- theorem1 dM gives u', a', FinMem u' a', EvalRel A rho a'.
  -- Then theorem1 dP applied to a' gives a'', b, FinMem a'' b,
  -- EvalRel Prop rho b, i.e., b ≤ PropCode. By FinMem-Prop-in-U-helper,
  -- a'' = Bot, so a' ≤ a'' = Bot, so a' = Bot, so u' = Bot, so u = Bot.
  convSound' (conv-Prop {n = n} {G = G} {M = M} {N = N} {A = A} dP dM dN) rho fits =
    let invM = theorem1 dM rho fits
        invN = theorem1 dN rho fits
        invP = theorem1 dP rho fits
        collapse : (T : Expr n) -> LTS.InvTyp G T A rho ->
          (u : FinEl) -> EvalRel T rho u -> Eq u Bot
        collapse T invT u ev =
          let mkSigma u' (mkSigma a1 (mkSigma le-u (mkSigma _ (mkSigma fm1 evA)))) = invT u ev
              mkSigma a2 (mkSigma b (mkSigma le-a (mkSigma _ (mkSigma fm2 evProp)))) = invP a1 evA
          in LeCode-Bot-eq u u' le-u
               (conv-Prop-chain u' a1 a2 b fm1 le-a fm2 (snd evProp))
    in mkSigma invM (mkSigma invN
         (mkSigma (\ u ev -> Eq-transport (EvalRel N rho)
                    (Eq-sym (collapse M invM u ev)) (EvalRel-Bot N rho))
                  (\ u ev -> Eq-transport (EvalRel M rho)
                    (Eq-sym (collapse N invN u ev)) (EvalRel-Bot M rho))))

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
  convSound' (conv-Pi {A = A} {A' = A'} {B = B} {B' = B'} d1 d2)
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

  -- conv-Prop-U: lift InvConv from Prop to U
  convSound' (conv-Prop-U {G = G} {M = M} {N = N} d) rho fits =
    let mkSigma invM (mkSigma invN (mkSigma fwd bwd)) = convSound' d rho fits
        liftInv : {T : Expr _} -> InvTyp G T Prop rho -> InvTyp G T U rho
        liftInv inv u ev =
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evT (mkSigma fm evProp)))) = inv u ev
              fmU = FinMem-Prop-in-U u' a' fm (snd evProp)
          in mkSigma u' (mkSigma UCode
               (mkSigma le (mkSigma evT (mkSigma fmU (mkSigma tt tt)))))
    in mkSigma (liftInv invM) (mkSigma (liftInv invN) (mkSigma fwd bwd))

  -- conv-Pi-Prop: Pi at Prop level
  convSound' (conv-Pi-Prop {A = A} {A' = A'} {B = B} {B' = B'} d1 d2)
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
        invPiLHS = LTS.InvTyp-Pi-Prop A B rho fits invA
          (\ x a0 fm evA ->
            let mkSigma invBx _ = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm evA)))
            in invBx)
        invPiRHS = LTS.InvTyp-Pi-Prop A' B' rho fits invA'
          (\ x a0 fm evA' ->
            let mkSigma _ (mkSigma invB'x _) = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm (bwdA a0 evA'))))
            in invB'x)
    in mkSigma invPiLHS (mkSigma invPiRHS (mkSigma fwd bwd))

  --------------------------------------------------------------------
  -- theorem1 — case analysis
  --------------------------------------------------------------------

  -- ty-var: u ≤ lookupEnv i rho, enlarge to lookupEnv i rho itself
  theorem1 (ty-var {i = i} wf) rho fits u (mkSigma cu le) =
    let mkSigma a' (mkSigma fm evA) = LTS.Fits-var rho fits i
        li  = lookupEnv i rho
        cli = FinMem-coh-u li a' fm
    in mkSigma li (mkSigma a'
         (mkSigma le (mkSigma (mkSigma cli (LeCode-refl li cli))
           (mkSigma fm evA))))

  -- ty-U: enlarge to UCode
  theorem1 (ty-U wf) rho fits u ev =
    mkSigma UCode (mkSigma UCode
      (mkSigma (snd ev)
        (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-Prop: enlarge to PropCode, type code is UCode (Prop : U)
  theorem1 (ty-Prop wf) rho fits u ev =
    mkSigma PropCode (mkSigma UCode
      (mkSigma (snd ev)
        (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-Prop-U: A : Prop implies A : U
  -- From theorem1 on dA, we get u', a', FinMem u' a', EvalRel Prop rho a'.
  -- a' ≤ PropCode. FinMem u' a' gives FinMem u' UCode via FinMem-Prop-in-U.
  theorem1 (ty-Prop-U dA) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evProp)))) =
          theorem1 dA rho fits u ev
        fmU = FinMem-Prop-in-U u' a' fm (snd evProp)
    in mkSigma u' (mkSigma UCode
         (mkSigma le (mkSigma evM (mkSigma fmU (mkSigma tt tt)))))

  -- ty-Pi-Prop: Pi A B : Prop when A : U, B : Prop
  -- Since Pi A B : Prop implies Pi A B : U (via ty-Pi + ty-Prop-U),
  -- and all inhabitants of Prop-typed codes collapse to Bot,
  -- InvTyp is trivially satisfiable: u collapses to Bot.
  -- We use ty-Pi for the U version, then note any caller at Prop
  -- will see only Bot anyway.
  -- FUTURE: dedicated InvTyp-Pi-Prop for FinMem u' PropCode evidence.
  -- ty-Pi-Prop: from InvTyp-Pi-Prop
  theorem1 (ty-Pi-Prop {A = A} {B = B} d1 d2) rho fits u ev =
    LTS.InvTyp-Pi-Prop A B rho fits
      (theorem1 d1 rho fits)
      (\ x a fm evA ->
        theorem1 d2 (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))
      u ev

  -- ty-conv: transport type via conversion
  theorem1 (ty-conv d1 d2 _) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) =
          theorem1 d1 rho fits u ev
    in mkSigma u' (mkSigma a'
         (mkSigma le (mkSigma evM
           (mkSigma fm (convSound d2 rho fits a' evA)))))

  -- ty-Pi: from LTS.InvTyp-Pi
  theorem1 (ty-Pi {A = A} {B = B} d1 d2) rho fits u ev =
    LTS.InvTyp-Pi A B rho fits
      (theorem1 d1 rho fits)
      (\ x a fm evA ->
        theorem1 d2 (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))
      u ev

  -- ty-Lam: from LTS.InvTyp-Lam
  theorem1 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) rho fits u ev =
    LTS.InvTyp-Lam A B M
      (\ rho' x a fits' fm evA ->
        theorem1 d3 (extendEnv rho' x)
          (mkSigma fits' (mkSigma a (mkSigma fm evA))))
      rho fits u ev

  -- ty-App: from LTS.InvTyp-App
  theorem1 (ty-App {A = A} {B = B} {f = f} {a = a} d1 _ d2 d3)
    rho fits u ev =
    LTS.InvTyp-App A B f a rho fits
      (theorem1 d2 rho fits)
      (theorem1 d3 rho fits)
      u ev
