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

module TypingSemanticsSigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ;
              nil ; cons)
open import PaperSemanticsSigma using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; LeFunCode ;
  FinMem ; FinMemFun ; FinMemAllProp ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf ; NotBot ;
  FinMem-Prop-Bot ; FinMem-Prop-to-U ; EvalFun-in-PropCode ;
  EvalFun ; EvalFun-mon ; Coherent-EvalFun ;
  finMem-upward ;
  LeCode-PropCode-cases ; Or ; inl ; inr ;
  absurdEl ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; comp-Bot-r ; comp-Bot-l ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  FinMemAllU)
open import SelectionSigma using (Selection)
open import RawSemanticsSigma using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ;
  EvalRel ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Bot ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl ;
  EvalRel-Comp ; EvalRel-Sup)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1)
  renaming (Sigma to SigmaE ; MkPair to MkPairE ; Fst to FstE ; Snd to SndE)
open import TypingRulesSigma using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-Prop ;
  conv-Prop-U ; conv-Pi-Prop ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Sigma ; conv-beta-fst ; conv-beta-snd ; conv-pair-eta ;
  conv-MkPair-fst ; conv-MkPair-snd ; conv-Fst ; conv-Snd)

-- All hard lemmas come from LemmaForTSSigma (0 postulates).
import LemmaForTSSigma as LTS
open LTS using (Fits ; Typed ; InvTyp ; InvConv ;
  Fits-CoherentEnv ; Fits-var ; InvTyp-MkPair)
open import EvalSubstitutionSigma using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-subst1-backward ; EvalRel-subst1-forward-bounded ;
  EvalRel-subst1-forward)

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
FinMem-Bot-elim (SigmaCode a f) ()
FinMem-Bot-elim (PairCode u v)  ()

-- If LeCode u u' and u' = Bot, then u = Bot
LeCode-Bot-eq : (u u' : FinEl) -> LeCode u u' -> Eq u' Bot -> Eq u Bot
LeCode-Bot-eq Bot u' le eq = refl
LeCode-Bot-eq UCode Bot ()
LeCode-Bot-eq UCode UCode le ()
LeCode-Bot-eq UCode PropCode le ()
LeCode-Bot-eq UCode (FunEl h) le ()
LeCode-Bot-eq UCode (PiCode b g) le ()
LeCode-Bot-eq UCode (SigmaCode b g) le ()
LeCode-Bot-eq UCode (PairCode u v) le ()
LeCode-Bot-eq PropCode Bot ()
LeCode-Bot-eq PropCode UCode le ()
LeCode-Bot-eq PropCode PropCode le ()
LeCode-Bot-eq PropCode (FunEl h) le ()
LeCode-Bot-eq PropCode (PiCode b g) le ()
LeCode-Bot-eq PropCode (SigmaCode b g) le ()
LeCode-Bot-eq PropCode (PairCode u v) le ()
LeCode-Bot-eq (FunEl g) Bot ()
LeCode-Bot-eq (FunEl g) UCode le ()
LeCode-Bot-eq (FunEl g) PropCode le ()
LeCode-Bot-eq (FunEl g) (FunEl h) le ()
LeCode-Bot-eq (FunEl g) (PiCode b h) le ()
LeCode-Bot-eq (FunEl g) (SigmaCode b h) le ()
LeCode-Bot-eq (FunEl g) (PairCode u v) le ()
LeCode-Bot-eq (PiCode a f) Bot ()
LeCode-Bot-eq (PiCode a f) UCode le ()
LeCode-Bot-eq (PiCode a f) PropCode le ()
LeCode-Bot-eq (PiCode a f) (FunEl h) le ()
LeCode-Bot-eq (PiCode a f) (PiCode b g) le ()
LeCode-Bot-eq (PiCode a f) (SigmaCode b g) le ()
LeCode-Bot-eq (PiCode a f) (PairCode u v) le ()
LeCode-Bot-eq (SigmaCode a f) Bot ()
LeCode-Bot-eq (SigmaCode a f) UCode le ()
LeCode-Bot-eq (SigmaCode a f) PropCode le ()
LeCode-Bot-eq (SigmaCode a f) (FunEl h) le ()
LeCode-Bot-eq (SigmaCode a f) (PiCode b g) le ()
LeCode-Bot-eq (SigmaCode a f) (SigmaCode b g) le ()
LeCode-Bot-eq (SigmaCode a f) (PairCode u v) le ()
LeCode-Bot-eq (PairCode u v) Bot ()
LeCode-Bot-eq (PairCode u v) UCode le ()
LeCode-Bot-eq (PairCode u v) PropCode le ()
LeCode-Bot-eq (PairCode u v) (FunEl h) le ()
LeCode-Bot-eq (PairCode u v) (PiCode b g) le ()
LeCode-Bot-eq (PairCode u v) (SigmaCode b g) le ()
LeCode-Bot-eq (PairCode u v) (PairCode u2 v2) le ()

-- If LeCode a' PropCode and FinMem u' a', produce FinMem u' UCode.
FinMem-Prop-in-U : (u' a' : FinEl) -> FinMem u' a' -> LeCode a' PropCode ->
  FinMem u' UCode
FinMem-Prop-in-U u' Bot fm le =
  Eq-transport (\ x -> FinMem x UCode) (Eq-sym (FinMem-Bot-elim u' fm)) tt
FinMem-Prop-in-U u' UCode fm ()
FinMem-Prop-in-U u' PropCode fm le = FinMem-Prop-to-U u' fm
FinMem-Prop-in-U u' (FunEl g) fm ()
FinMem-Prop-in-U u' (PiCode a f) fm ()
FinMem-Prop-in-U u' (SigmaCode a f) fm ()
FinMem-Prop-in-U u' (PairCode u v) fm ()

------------------------------------------------------------------------
-- Prop-collapse
------------------------------------------------------------------------

-- Helper: FinMem (FunEl h) (PiCode c' g') is impossible when
-- LeFunCode g' g and FinMem (PiCode c g) PropCode
{-# TERMINATING #-}
Prop-collapse-FunEl-absurd : (h : S.FinFun) (c' : FinEl) (g' : S.FinFun)
  (c : FinEl) (g : S.FinFun) ->
  FinMemFun h c' g' -> CoherentFun h ->
  LeFunCode g' g -> CoherentFunTail g' -> CoherentFunTail g ->
  FinMem c' UCode -> FinMemAllProp g c -> Empty
Prop-collapse-FunEl-absurd nil c' g' c g fmf ()
Prop-collapse-FunEl-absurd (cons p ps) c' g' c g fmf coh lfg cg' cg c'U allP =
  let cohT = cft-from-cf (cons p ps) coh
      nb = CFTcons.val-nbot cohT
      cp = CFTcons.key-coh cohT
      cv = CFTcons.val-coh cohT
      mem-v = snd (fst fmf)
      le-eval = EvalFun-mon g' g (fst p) cg' cg cp lfg
      evalP = EvalFun-in-PropCode g (fst p) c cg cp allP
      evalU = FinMem-Prop-to-U (EvalFun g (fst p)) evalP
      coh-g' = Coherent-EvalFun g' (fst p) cg' cp
      coh-g = Coherent-EvalFun g (fst p) cg cp
      mem-v-up = finMem-upward (snd p) (EvalFun g' (fst p)) (EvalFun g (fst p))
                   le-eval coh-g' coh-g mem-v evalU
      eq = FinMem-Prop-Bot (snd p) (EvalFun g (fst p)) mem-v-up evalP
  in Eq-transport NotBot eq nb

-- Helper for PairCode in PropCode (absurd because Coherent (PairCode u v)
-- requires Or (NotBot u) (NotBot v), but both collapse to Bot)
{-# TERMINATING #-}
Prop-collapse-PairCode-absurd : (u v : FinEl) (a : FinEl) (f : S.FinFun) ->
  FinMem (PairCode u v) (SigmaCode a f) ->
  FinMem (SigmaCode a f) PropCode -> Empty
Prop-collapse-PairCode-absurd u v a f mem ()

-- Prop-collapse: FinMem u a, LeCode a a', FinMem a' PropCode → u = Bot
Prop-collapse : (u a a' : FinEl) ->
  FinMem u a -> LeCode a a' -> FinMem a' PropCode -> Eq u Bot
Prop-collapse u a a' fm le a'P with FinMem-Prop-in-U-helper a' a'P
  where
    FinMem-Prop-in-U-helper : (a' : FinEl) -> FinMem a' PropCode ->
      Or (Eq a' Bot) (S.Sigma FinEl (\ c -> S.Sigma S.FinFun (\ g ->
        Pair (Eq a' (PiCode c g)) (Pair (FinMem c UCode)
          (Pair (FinMemAllProp g c) (CoherentFunTail g))))))
    FinMem-Prop-in-U-helper Bot          mem = inl refl
    FinMem-Prop-in-U-helper UCode        ()
    FinMem-Prop-in-U-helper PropCode     ()
    FinMem-Prop-in-U-helper (FunEl g)    ()
    FinMem-Prop-in-U-helper (PiCode c g) mem =
      inr (mkSigma c (mkSigma g (mkSigma refl mem)))
    FinMem-Prop-in-U-helper (SigmaCode c g) ()
    FinMem-Prop-in-U-helper (PairCode u v) ()
... | inl a'bot =
  let abot = LeCode-Bot-eq a a' le a'bot
  in FinMem-Bot-elim u (Eq-transport (FinMem u) abot fm)
... | inr (mkSigma c (mkSigma g (mkSigma a'eq (mkSigma cU (mkSigma allP cohg))))) =
  let le' = Eq-transport (LeCode a) a'eq le
  in Prop-collapse-inner u a c g fm le' cU allP cohg
  where
    Prop-collapse-inner : (u a : FinEl) (c : FinEl) (g : S.FinFun) ->
      FinMem u a -> LeCode a (PiCode c g) ->
      FinMem c UCode -> FinMemAllProp g c -> CoherentFunTail g ->
      Eq u Bot
    Prop-collapse-inner u Bot c g fm le cU allP cohg = FinMem-Bot-elim u fm
    Prop-collapse-inner u UCode c g fm ()
    Prop-collapse-inner u PropCode c g fm ()
    Prop-collapse-inner u (FunEl h) c g fm ()
    Prop-collapse-inner u (SigmaCode a0 f0) c g fm ()
    Prop-collapse-inner u (PairCode u0 v0) c g fm ()
    Prop-collapse-inner Bot (PiCode c' g') c g fm le cU allP cohg = refl
    Prop-collapse-inner UCode (PiCode c' g') c g ()
    Prop-collapse-inner PropCode (PiCode c' g') c g ()
    Prop-collapse-inner (PiCode x y) (PiCode c' g') c g ()
    Prop-collapse-inner (SigmaCode x y) (PiCode c' g') c g ()
    Prop-collapse-inner (PairCode x y) (PiCode c' g') c g ()
    Prop-collapse-inner (FunEl h) (PiCode c' g') c g fm le cU allP cohg =
      let fmf = fst fm
          cfh = fst (snd fm)
          piU = snd (snd fm)
          le-g = snd le
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
conv-Prop-chain u' a1 a2 (SigmaCode c g) fm1 le-a fm2 ()
conv-Prop-chain u' a1 a2 (PairCode u v) fm1 le-a fm2 ()

------------------------------------------------------------------------
-- Helper: make Fst/Snd evidence from PairCode evidence
------------------------------------------------------------------------

mkFstEv : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u' v' : FinEl) ->
  EvalRel M rho (PairCode u' v') -> EvalRel (FstE M) rho u'
mkFstEv M rho Bot v' evM = tt
mkFstEv M rho UCode v' evM = mkSigma v' evM
mkFstEv M rho PropCode v' evM = mkSigma v' evM
mkFstEv M rho (FunEl g) v' evM = mkSigma v' evM
mkFstEv M rho (PiCode a0 f0) v' evM = mkSigma v' evM
mkFstEv M rho (SigmaCode a0 f0) v' evM = mkSigma v' evM
mkFstEv M rho (PairCode u0 v0) v' evM = mkSigma v' evM

mkSndEv : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u' v' : FinEl) ->
  EvalRel M rho (PairCode u' v') -> EvalRel (SndE M) rho v'
mkSndEv M rho u' Bot evM = tt
mkSndEv M rho u' UCode evM = mkSigma u' evM
mkSndEv M rho u' PropCode evM = mkSigma u' evM
mkSndEv M rho u' (FunEl g) evM = mkSigma u' evM
mkSndEv M rho u' (PiCode a0 f0) evM = mkSigma u' evM
mkSndEv M rho u' (SigmaCode a0 f0) evM = mkSigma u' evM
mkSndEv M rho u' (PairCode u0 v0) evM = mkSigma u' evM

------------------------------------------------------------------------
-- Helper: extract PairCode evidence from Fst/Snd evidence
------------------------------------------------------------------------

-- From EvalRel (Fst M) rho u (non-Bot), get v and EvalRel M rho (PairCode u v)
fstEv-extract : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> NotBot u ->
  EvalRel (FstE M) rho u ->
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode u v))
fstEv-extract M rho Bot ()
fstEv-extract M rho UCode nbu ev = ev
fstEv-extract M rho PropCode nbu ev = ev
fstEv-extract M rho (FunEl g) nbu ev = ev
fstEv-extract M rho (PiCode a f) nbu ev = ev
fstEv-extract M rho (SigmaCode a f) nbu ev = ev
fstEv-extract M rho (PairCode u0 v0) nbu ev = ev

-- From EvalRel (Snd M) rho v (non-Bot), get u and EvalRel M rho (PairCode u v)
sndEv-extract : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (v : FinEl) -> NotBot v ->
  EvalRel (SndE M) rho v ->
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u v))
sndEv-extract M rho Bot ()
sndEv-extract M rho UCode nbv ev = ev
sndEv-extract M rho PropCode nbv ev = ev
sndEv-extract M rho (FunEl g) nbv ev = ev
sndEv-extract M rho (PiCode a f) nbv ev = ev
sndEv-extract M rho (SigmaCode a f) nbv ev = ev
sndEv-extract M rho (PairCode u0 v0) nbv ev = ev

-- Helper: lift NotBot through LeCode for Or cases
liftNotBot-Or : (u0 v0 u0' v0' : FinEl) ->
  Coherent u0 -> Coherent v0 -> Coherent u0' -> Coherent v0' ->
  LeCode u0 u0' -> LeCode v0 v0' ->
  Or (NotBot u0) (NotBot v0) -> Or (NotBot u0') (NotBot v0')
liftNotBot-Or u0 v0 u0' v0' cu0 cv0 cu0' cv0' leu lev (inl nbu0) =
  inl (LTS.NotBot-from-Le u0 u0' cu0 nbu0 leu)
liftNotBot-Or u0 v0 u0' v0' cu0 cv0 cu0' cv0' leu lev (inr nbv0) =
  inr (LTS.NotBot-from-Le v0 v0' cv0 nbv0 lev)

-- Convert InvTyp from subst1 B M to subst1 B M' using evaluation equivalence
convertInvTyp-subst1 : {n : Nat} {G : Ctx n}
  (B : Expr (suc n)) (M M' : Expr n) (N : Expr n)
  (rho : EnvApprox n) ->
  CoherentEnv rho ->
  ((u : FinEl) -> EvalRel M rho u -> EvalRel M' rho u) ->
  InvTyp G N (subst1 B M) rho ->
  InvTyp G N (subst1 B M') rho
convertInvTyp-subst1 B M M' N rho crho fwdM invN u ev =
  let r = invN u ev
      v0' = fst r
      b' = fst (snd r)
      le = fst (snd (snd r))
      evN-v0' = fst (snd (snd (snd r)))
      fm = fst (snd (snd (snd (snd r))))
      evBM-b' = snd (snd (snd (snd (snd r))))
      -- Convert EvalRel (subst1 B M) rho b' to EvalRel (subst1 B M') rho b'
      fwd-res = EvalRel-subst1-forward B M rho b' crho evBM-b'
      v-wit = fst fwd-res
      evM-vwit = fst (snd fwd-res)
      evB-vwit-b' = snd (snd fwd-res)
      evM'-vwit = fwdM v-wit evM-vwit
      evBM'-b' = EvalRel-subst1-backward B M' rho v-wit b' crho evM'-vwit evB-vwit-b'
  in mkSigma v0' (mkSigma b' (mkSigma le (mkSigma evN-v0' (mkSigma fm evBM'-b'))))

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
  convSound-Pi-fwd A A' B B' rho (SigmaCode a f) eqA eqB ()
  convSound-Pi-fwd A A' B B' rho (PairCode u v) eqA eqB ()

  --------------------------------------------------------------------
  -- Helper: Sigma congruence on evaluation
  --------------------------------------------------------------------

  convSound-Sigma-fwd : {n : Nat}
    (A A' : Expr n) (B B' : Expr (suc n))
    (rho : EnvApprox n) -> (u : FinEl) ->
    ((w : FinEl) -> EvalRel A rho w -> EvalRel A' rho w) ->
    ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
      (w : FinEl) -> EvalRel B (extendEnv rho x) w ->
                     EvalRel B' (extendEnv rho x) w) ->
    EvalRel (SigmaE A B) rho u -> EvalRel (SigmaE A' B') rho u
  convSound-Sigma-fwd A A' B B' rho Bot eqA eqB ev = tt
  convSound-Sigma-fwd A A' B B' rho (SigmaCode b f) eqA eqB
    (mkSigma coh (mkSigma evA-b (mkSigma a' (mkSigma evA' body)))) =
    mkSigma coh (mkSigma (eqA b evA-b)
      (mkSigma a' (mkSigma (eqA a' evA')
        (\ u v sel ->
          let mkSigma x (mkSigma le (mkSigma mem evB)) = body u v sel
          in mkSigma x (mkSigma le (mkSigma mem (eqB x a' mem evA' v evB)))))))
  convSound-Sigma-fwd A A' B B' rho UCode eqA eqB ()
  convSound-Sigma-fwd A A' B B' rho PropCode eqA eqB ()
  convSound-Sigma-fwd A A' B B' rho (FunEl g) eqA eqB ()
  convSound-Sigma-fwd A A' B B' rho (PiCode a f) eqA eqB ()
  convSound-Sigma-fwd A A' B B' rho (PairCode u v) eqA eqB ()

  --------------------------------------------------------------------
  -- Helper: MkPair congruence (first component)
  --
  -- EvalRel (MkPair M N) rho u -> EvalRel (MkPair M' N) rho u
  -- given fwd : forall w, EvalRel M rho w -> EvalRel M' rho w
  --------------------------------------------------------------------

  convSound-MkPair-fst-fwd : {n : Nat}
    (M M' N : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel M rho w -> EvalRel M' rho w) ->
    EvalRel (MkPairE M N) rho u -> EvalRel (MkPairE M' N) rho u
  convSound-MkPair-fst-fwd M M' N rho Bot fwd ev = tt
  convSound-MkPair-fst-fwd M M' N rho (PairCode u v) fwd
    (mkSigma coh (mkSigma evM evN)) =
    mkSigma coh (mkSigma (fwd u evM) evN)
  convSound-MkPair-fst-fwd M M' N rho UCode fwd ()
  convSound-MkPair-fst-fwd M M' N rho PropCode fwd ()
  convSound-MkPair-fst-fwd M M' N rho (FunEl g) fwd ()
  convSound-MkPair-fst-fwd M M' N rho (PiCode a f) fwd ()
  convSound-MkPair-fst-fwd M M' N rho (SigmaCode a f) fwd ()

  --------------------------------------------------------------------
  -- Helper: MkPair congruence (second component)
  --------------------------------------------------------------------

  convSound-MkPair-snd-fwd : {n : Nat}
    (M N N' : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel N rho w -> EvalRel N' rho w) ->
    EvalRel (MkPairE M N) rho u -> EvalRel (MkPairE M N') rho u
  convSound-MkPair-snd-fwd M N N' rho Bot fwd ev = tt
  convSound-MkPair-snd-fwd M N N' rho (PairCode u v) fwd
    (mkSigma coh (mkSigma evM evN)) =
    mkSigma coh (mkSigma evM (fwd v evN))
  convSound-MkPair-snd-fwd M N N' rho UCode fwd ()
  convSound-MkPair-snd-fwd M N N' rho PropCode fwd ()
  convSound-MkPair-snd-fwd M N N' rho (FunEl g) fwd ()
  convSound-MkPair-snd-fwd M N N' rho (PiCode a f) fwd ()
  convSound-MkPair-snd-fwd M N N' rho (SigmaCode a f) fwd ()

  --------------------------------------------------------------------
  -- Helper: Fst congruence
  --
  -- EvalRel (Fst M) rho u -> EvalRel (Fst M') rho u
  -- given fwd : forall w, EvalRel M rho w -> EvalRel M' rho w
  --------------------------------------------------------------------

  convSound-Fst-fwd : {n : Nat}
    (M M' : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel M rho w -> EvalRel M' rho w) ->
    EvalRel (FstE M) rho u -> EvalRel (FstE M') rho u
  convSound-Fst-fwd M M' rho Bot fwd ev = tt
  convSound-Fst-fwd M M' rho UCode fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode UCode v) evM)
  convSound-Fst-fwd M M' rho PropCode fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode PropCode v) evM)
  convSound-Fst-fwd M M' rho (FunEl g) fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode (FunEl g) v) evM)
  convSound-Fst-fwd M M' rho (PiCode a f) fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode (PiCode a f) v) evM)
  convSound-Fst-fwd M M' rho (SigmaCode a f) fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode (SigmaCode a f) v) evM)
  convSound-Fst-fwd M M' rho (PairCode u0 v0) fwd (mkSigma v evM) =
    mkSigma v (fwd (PairCode (PairCode u0 v0) v) evM)

  --------------------------------------------------------------------
  -- Helper: Snd congruence
  --------------------------------------------------------------------

  convSound-Snd-fwd : {n : Nat}
    (M M' : Expr n) (rho : EnvApprox n) (u : FinEl) ->
    ((w : FinEl) -> EvalRel M rho w -> EvalRel M' rho w) ->
    EvalRel (SndE M) rho u -> EvalRel (SndE M') rho u
  convSound-Snd-fwd M M' rho Bot fwd ev = tt
  convSound-Snd-fwd M M' rho UCode fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u UCode) evM)
  convSound-Snd-fwd M M' rho PropCode fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u PropCode) evM)
  convSound-Snd-fwd M M' rho (FunEl g) fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u (FunEl g)) evM)
  convSound-Snd-fwd M M' rho (PiCode a f) fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u (PiCode a f)) evM)
  convSound-Snd-fwd M M' rho (SigmaCode a f) fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u (SigmaCode a f)) evM)
  convSound-Snd-fwd M M' rho (PairCode u0 v0) fwd (mkSigma u evM) =
    mkSigma u (fwd (PairCode u (PairCode u0 v0)) evM)

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

  -- conv-Prop-U: Prop subtyping for conversions
  convSound' (conv-Prop-U {G = G} {M = M} {N = N} d) rho fits =
    let mkSigma invM (mkSigma invN (mkSigma fwd bwd)) = convSound' d rho fits
        liftInv : {T : Expr _} -> InvTyp G T Prop rho -> InvTyp G T U rho
        liftInv inv u ev =
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evT (mkSigma fm evProp)))) = inv u ev
              fmU = FinMem-Prop-in-U u' a' fm (snd evProp)
          in mkSigma u' (mkSigma UCode
               (mkSigma le (mkSigma evT (mkSigma fmU (mkSigma tt tt)))))
    in mkSigma (liftInv invM) (mkSigma (liftInv invN) (mkSigma fwd bwd))

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

  -- conv-Pi-Prop: Pi at Prop level
  -- Evaluation forward/backward is the same as conv-Pi.
  -- InvTyp at Prop: use LTS.InvTyp-Pi-Prop with body-ih from convSound' d2.
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

  -- conv-Sigma: congruence for Sigma types (mirrors conv-Pi)
  convSound' (conv-Sigma {A = A} {A' = A'} {B = B} {B' = B'} d1 d2)
    rho fits =
    let mkSigma invA (mkSigma invA' (mkSigma fwdA bwdA)) = convSound' d1 rho fits
        fwd = \ u ev -> convSound-Sigma-fwd A A' B B' rho u
                fwdA
                (\ x a0 fm evA w ->
                  convSound d2 (extendEnv rho x)
                    (mkSigma fits (mkSigma a0 (mkSigma fm evA))) w)
                ev
        bwd = \ u ev -> convSound-Sigma-fwd A' A B' B rho u
                bwdA
                (\ x a0 fm evA' w ->
                  convSound-inv d2 (extendEnv rho x)
                    (mkSigma fits (mkSigma a0 (mkSigma fm
                      (bwdA a0 evA')))) w)
                ev
        invSigLHS = LTS.InvTyp-Sigma A B rho fits invA
          (\ x a0 fm evA ->
            let mkSigma invB _ = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm evA)))
            in invB)
        invSigRHS = LTS.InvTyp-Sigma A' B' rho fits invA'
          (\ x a0 fm evA' ->
            let mkSigma _ (mkSigma invB' _) = convSound' d2 (extendEnv rho x)
                  (mkSigma fits (mkSigma a0 (mkSigma fm
                    (bwdA a0 evA'))))
            in invB')
    in mkSigma invSigLHS (mkSigma invSigRHS (mkSigma fwd bwd))

  -- conv-beta-fst: Fst (MkPair M N) = M : A
  convSound' (conv-beta-fst {G = G} {A = A} {B = B} {M = M} {N = N} dA dB dM dN) rho fits =
    let crho = Fits-CoherentEnv rho fits
        invM = theorem1 dM rho fits
        invFstMkPair : InvTyp G (FstE (MkPairE M N)) A rho
        invFstMkPair u ev =
          let evM' = conv-fst-fwd M N rho u ev
              mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM-u' (mkSigma fm evA)))) = invM u evM'
              evFst-u' = conv-fst-bwd M N rho crho u' evM-u'
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evFst-u' (mkSigma fm evA))))
    in mkSigma invFstMkPair (mkSigma invM
         (mkSigma (conv-fst-fwd M N rho) (conv-fst-bwd M N rho crho)))
    where
      conv-fst-fwd : {n : Nat} (M N : Expr n)
        (rho : EnvApprox n) ->
        (u : FinEl) -> EvalRel (FstE (MkPairE M N)) rho u -> EvalRel M rho u
      conv-fst-fwd M N rho Bot ev = EvalRel-Bot M rho
      conv-fst-fwd M N rho UCode (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
      conv-fst-fwd M N rho PropCode (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
      conv-fst-fwd M N rho (FunEl g) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
      conv-fst-fwd M N rho (PiCode a f) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
      conv-fst-fwd M N rho (SigmaCode a f) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
      conv-fst-fwd M N rho (PairCode u0 v0) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM

      conv-fst-bwd : {n : Nat} (M N : Expr n)
        (rho : EnvApprox n) -> CoherentEnv rho ->
        (u : FinEl) -> EvalRel M rho u -> EvalRel (FstE (MkPairE M N)) rho u
      conv-fst-bwd M N rho crho Bot ev = tt
      conv-fst-bwd M N rho crho UCode ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))
      conv-fst-bwd M N rho crho PropCode ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))
      conv-fst-bwd M N rho crho (FunEl g) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (FunEl g) ev) tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))
      conv-fst-bwd M N rho crho (PiCode a f) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (PiCode a f) ev) tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))
      conv-fst-bwd M N rho crho (SigmaCode a f) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (SigmaCode a f) ev) tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))
      conv-fst-bwd M N rho crho (PairCode u0 v0) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (PairCode u0 v0) ev) tt) (inl tt))
          (mkSigma ev (EvalRel-Bot N rho)))

  -- conv-beta-snd: Snd (MkPair M N) = N : subst1 B M
  convSound' (conv-beta-snd {G = G} {A = A} {B = B} {M = M} {N = N} dA dB dM dN) rho fits =
    let crho = Fits-CoherentEnv rho fits
        invN = theorem1 dN rho fits
        invSndMkPair : InvTyp G (SndE (MkPairE M N)) (subst1 B M) rho
        invSndMkPair u ev =
          let evN' = conv-snd-fwd M N rho u ev
              mkSigma u' (mkSigma a' (mkSigma le (mkSigma evN-u' (mkSigma fm evBM)))) = invN u evN'
              evSnd-u' = conv-snd-bwd M N rho crho u' evN-u'
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evSnd-u' (mkSigma fm evBM))))
    in mkSigma invSndMkPair (mkSigma invN
         (mkSigma (conv-snd-fwd M N rho) (conv-snd-bwd M N rho crho)))
    where
      conv-snd-fwd : {n : Nat} (M N : Expr n)
        (rho : EnvApprox n) ->
        (u : FinEl) -> EvalRel (SndE (MkPairE M N)) rho u -> EvalRel N rho u
      conv-snd-fwd M N rho Bot ev = EvalRel-Bot N rho
      conv-snd-fwd M N rho UCode (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN
      conv-snd-fwd M N rho PropCode (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN
      conv-snd-fwd M N rho (FunEl g) (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN
      conv-snd-fwd M N rho (PiCode a f) (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN
      conv-snd-fwd M N rho (SigmaCode a f) (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN
      conv-snd-fwd M N rho (PairCode u0 v0) (mkSigma u (mkSigma coh (mkSigma evM evN))) = evN

      conv-snd-bwd : {n : Nat} (M N : Expr n)
        (rho : EnvApprox n) -> CoherentEnv rho ->
        (u : FinEl) -> EvalRel N rho u -> EvalRel (SndE (MkPairE M N)) rho u
      conv-snd-bwd M N rho crho Bot ev = tt
      conv-snd-bwd M N rho crho UCode ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))
      conv-snd-bwd M N rho crho PropCode ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))
      conv-snd-bwd M N rho crho (FunEl g) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (FunEl g) ev)) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))
      conv-snd-bwd M N rho crho (PiCode a f) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (PiCode a f) ev)) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))
      conv-snd-bwd M N rho crho (SigmaCode a f) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (SigmaCode a f) ev)) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))
      conv-snd-bwd M N rho crho (PairCode u0 v0) ev =
        mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (PairCode u0 v0) ev)) (inr tt))
          (mkSigma (EvalRel-Bot M rho) ev))

  -- conv-pair-eta: MkPair (Fst M) (Snd M) = M : Sigma A B
  convSound' (conv-pair-eta {G = G} {A = A} {B = B} {M = M} dA dB dSigM) rho fits =
    mkSigma invLHS (mkSigma invM (mkSigma fwd bwd))
    where
      crho = Fits-CoherentEnv rho fits
      invM = theorem1 dSigM rho fits

      -- Helper: FinMem u' a' with a' from Sigma eval is absurd for non-PairCode u'
      le-absurd-same : (u' a' : FinEl) -> FinMem u' a' -> EvalRel (SigmaE A B) rho a' -> Empty
      le-absurd-same Bot Bot fm evSig = le-absurd-same Bot Bot fm evSig  -- unreachable
      le-absurd-same Bot (SigmaCode b g) fm evSig = le-absurd-same Bot (SigmaCode b g) fm evSig  -- unreachable
      le-absurd-same Bot UCode fm ()
      le-absurd-same Bot PropCode fm ()
      le-absurd-same Bot (FunEl g) fm ()
      le-absurd-same Bot (PiCode b g) fm ()
      le-absurd-same Bot (PairCode u1 v1) fm ()
      le-absurd-same UCode Bot ()
      le-absurd-same PropCode Bot ()
      le-absurd-same (FunEl g) Bot ()
      le-absurd-same (PiCode b g) Bot ()
      le-absurd-same (SigmaCode b g) Bot ()
      le-absurd-same (PairCode u v) Bot ()
      le-absurd-same u' UCode fm ()
      le-absurd-same u' PropCode fm ()
      le-absurd-same u' (FunEl g) fm ()
      le-absurd-same u' (PiCode b g) fm ()
      le-absurd-same UCode (SigmaCode b g) ()
      le-absurd-same PropCode (SigmaCode b g) ()
      le-absurd-same (FunEl h) (SigmaCode b g) ()
      le-absurd-same (PiCode c h) (SigmaCode b g) ()
      le-absurd-same (SigmaCode c h) (SigmaCode b g) ()
      le-absurd-same (PairCode u1 v1) (SigmaCode b g) fm evSig =
        le-absurd-same (PairCode u1 v1) (SigmaCode b g) fm evSig
      le-absurd-same u' (PairCode u1 v1) fm ()

      -- For non-Bot non-PairCode u, derive Empty from InvTyp evidence
      le-absurd : (u u' a' : FinEl) ->
        LeCode u u' -> FinMem u' a' -> EvalRel (SigmaE A B) rho a' ->
        NotBot u -> Empty
      -- u = Bot: NotBot Bot = Empty
      le-absurd Bot u' a' le fm evSig ()
      -- u = UCode: LeCode UCode u' is non-Empty only for u' = UCode
      le-absurd UCode Bot a' ()
      le-absurd UCode UCode a' le fm evSig nbu = le-absurd-same UCode a' fm evSig
      le-absurd UCode PropCode a' ()
      le-absurd UCode (FunEl g) a' ()
      le-absurd UCode (PiCode b g) a' ()
      le-absurd UCode (SigmaCode b g) a' ()
      le-absurd UCode (PairCode u1 v1) a' ()
      -- u = PropCode: LeCode PropCode u' non-Empty only for u' = PropCode
      le-absurd PropCode Bot a' ()
      le-absurd PropCode UCode a' ()
      le-absurd PropCode PropCode a' le fm evSig nbu = le-absurd-same PropCode a' fm evSig
      le-absurd PropCode (FunEl g) a' ()
      le-absurd PropCode (PiCode b g) a' ()
      le-absurd PropCode (SigmaCode b g) a' ()
      le-absurd PropCode (PairCode u1 v1) a' ()
      -- u = FunEl: LeCode (FunEl g) u' non-Empty only for u' = FunEl
      le-absurd (FunEl g) Bot a' ()
      le-absurd (FunEl g) UCode a' ()
      le-absurd (FunEl g) PropCode a' ()
      le-absurd (FunEl g) (FunEl h) a' le fm evSig nbu = le-absurd-same (FunEl h) a' fm evSig
      le-absurd (FunEl g) (PiCode b h) a' ()
      le-absurd (FunEl g) (SigmaCode b h) a' ()
      le-absurd (FunEl g) (PairCode u1 v1) a' ()
      -- u = PiCode: LeCode (PiCode b g) u' non-Empty only for u' = PiCode
      le-absurd (PiCode b g) Bot a' ()
      le-absurd (PiCode b g) UCode a' ()
      le-absurd (PiCode b g) PropCode a' ()
      le-absurd (PiCode b g) (FunEl h) a' ()
      le-absurd (PiCode b g) (PiCode c h) a' le fm evSig nbu = le-absurd-same (PiCode c h) a' fm evSig
      le-absurd (PiCode b g) (SigmaCode c h) a' ()
      le-absurd (PiCode b g) (PairCode u1 v1) a' ()
      -- u = SigmaCode: LeCode (SigmaCode b g) u' non-Empty only for u' = SigmaCode
      le-absurd (SigmaCode b g) Bot a' ()
      le-absurd (SigmaCode b g) UCode a' ()
      le-absurd (SigmaCode b g) PropCode a' ()
      le-absurd (SigmaCode b g) (FunEl h) a' ()
      le-absurd (SigmaCode b g) (PiCode c h) a' ()
      le-absurd (SigmaCode b g) (SigmaCode c h) a' le fm evSig nbu = le-absurd-same (SigmaCode c h) a' fm evSig
      le-absurd (SigmaCode b g) (PairCode u1 v1) a' ()
      -- u = PairCode: this case not actually reachable from bwd-nonPair
      -- but needed for completeness. LeCode (PairCode u v) u' non-Empty for u' = PairCode
      le-absurd (PairCode u v) Bot a' ()
      le-absurd (PairCode u v) UCode a' ()
      le-absurd (PairCode u v) PropCode a' ()
      le-absurd (PairCode u v) (FunEl h) a' ()
      le-absurd (PairCode u v) (PiCode c h) a' ()
      le-absurd (PairCode u v) (SigmaCode c h) a' ()
      le-absurd (PairCode u v) (PairCode u1 v1) a' le fm evSig nbu = le-absurd-same (PairCode u1 v1) a' fm evSig

      -- For non-Bot, non-PairCode u: derive absurdity
      bwd-nonPair : (u : FinEl) -> NotBot u ->
        EvalRel M rho u -> EvalRel (MkPairE (FstE M) (SndE M)) rho u
      bwd-nonPair u nbu ev =
        let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM-u' (mkSigma fm evSig)))) = invM u ev
        in absurdEl (le-absurd u u' a' le fm evSig nbu)

      -- Forward helper for PairCode case
      conv-eta-fwd-pair : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
        CoherentEnv rho ->
        (u0 v0 : FinEl) -> Or (NotBot u0) (NotBot v0) ->
        Coherent u0 -> Coherent v0 ->
        EvalRel (FstE M) rho u0 -> EvalRel (SndE M) rho v0 ->
        EvalRel M rho (PairCode u0 v0)
      conv-eta-fwd-pair M rho crho u0 Bot (inl nbu0) cu0 cv0 evFst evSnd =
        let mkSigma v1 evM-pv1 = fstEv-extract M rho u0 nbu0 evFst
        in EvalRel-down M rho (PairCode u0 v1) (PairCode u0 Bot) crho
             (mkSigma (mkSigma cu0 tt) (inl nbu0)) evM-pv1
             (mkSigma (LeCode-refl u0 cu0) tt)
      conv-eta-fwd-pair M rho crho u0 Bot (inr ()) cu0 cv0 evFst evSnd
      conv-eta-fwd-pair M rho crho Bot v0 (inl ()) cu0 cv0 evFst evSnd
      conv-eta-fwd-pair M rho crho Bot v0 (inr nbv0) cu0 cv0 evFst evSnd =
        let mkSigma u1 evM-pu1 = sndEv-extract M rho v0 nbv0 evSnd
        in EvalRel-down M rho (PairCode u1 v0) (PairCode Bot v0) crho
             (mkSigma (mkSigma tt cv0) (inr nbv0)) evM-pu1
             (mkSigma tt (LeCode-refl v0 cv0))
      conv-eta-fwd-pair M rho crho u0 v0 nb cu0 cv0 evFst evSnd =
        conv-eta-fwd-both M rho crho u0 v0 nb cu0 cv0 evFst evSnd
        where
          conv-eta-core : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
            CoherentEnv rho ->
            (u0 v0 : FinEl) -> NotBot u0 -> NotBot v0 ->
            Coherent u0 -> Coherent v0 ->
            EvalRel (FstE M) rho u0 -> EvalRel (SndE M) rho v0 ->
            Or (NotBot u0) (NotBot v0) ->
            EvalRel M rho (PairCode u0 v0)
          conv-eta-core M rho crho u0 v0 nbu0 nbv0 cu0 cv0 evFst evSnd nb =
            let mkSigma v1 evM-u0v1 = fstEv-extract M rho u0 nbu0 evFst
                mkSigma u1 evM-u1v0 = sndEv-extract M rho v0 nbv0 evSnd
                comp = EvalRel-Comp M rho crho (PairCode u0 v1) (PairCode u1 v0) evM-u0v1 evM-u1v0
                cu0v1 = EvalRel-coh M rho (PairCode u0 v1) evM-u0v1
                cu1v0 = EvalRel-coh M rho (PairCode u1 v0) evM-u1v0
                evM-sup = EvalRel-Sup M rho (PairCode u0 v1) (PairCode u1 v0) crho
                            cu0v1 cu1v0 comp evM-u0v1 evM-u1v0
                le-u0 = LeCode-Sup-left u0 u1 (fst comp) (fst (fst cu0v1)) (fst (fst cu1v0))
                le-v0 = LeCode-Sup-right v1 v0 (snd comp) (snd (fst cu0v1)) (snd (fst cu1v0))
            in EvalRel-down M rho (PairCode (Sup u0 u1) (Sup v1 v0)) (PairCode u0 v0) crho
                 (mkSigma (mkSigma cu0 cv0) nb) evM-sup (mkSigma le-u0 le-v0)
          conv-eta-fwd-both : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
            CoherentEnv rho ->
            (u0 v0 : FinEl) -> Or (NotBot u0) (NotBot v0) ->
            Coherent u0 -> Coherent v0 ->
            EvalRel (FstE M) rho u0 -> EvalRel (SndE M) rho v0 ->
            EvalRel M rho (PairCode u0 v0)
          conv-eta-fwd-both M rho crho Bot Bot (inl ()) cu0 cv0 evFst evSnd
          conv-eta-fwd-both M rho crho Bot Bot (inr ()) cu0 cv0 evFst evSnd
          conv-eta-fwd-both M rho crho Bot v0 nb cu0 cv0 evFst evSnd =
            let mkSigma u1 evM-pu1 = sndEv-extract M rho v0 (nb-right nb) evSnd
            in EvalRel-down M rho (PairCode u1 v0) (PairCode Bot v0) crho
                 (mkSigma (mkSigma tt cv0) (inr (nb-right nb))) evM-pu1
                 (mkSigma tt (LeCode-refl v0 cv0))
            where
              nb-right : Or (NotBot Bot) (NotBot v0) -> NotBot v0
              nb-right (inl ())
              nb-right (inr x) = x
          conv-eta-fwd-both M rho crho u0 Bot nb cu0 cv0 evFst evSnd =
            let mkSigma v1 evM-pv1 = fstEv-extract M rho u0 (nb-left nb) evFst
            in EvalRel-down M rho (PairCode u0 v1) (PairCode u0 Bot) crho
                 (mkSigma (mkSigma cu0 tt) (inl (nb-left nb))) evM-pv1
                 (mkSigma (LeCode-refl u0 cu0) tt)
            where
              nb-left : Or (NotBot u0) (NotBot Bot) -> NotBot u0
              nb-left (inl x) = x
              nb-left (inr ())
          conv-eta-fwd-both M rho crho u0 Bot (inl nbu0) cu0 cv0 evFst evSnd =
            let mkSigma v1 evM-pv1 = fstEv-extract M rho u0 nbu0 evFst
            in EvalRel-down M rho (PairCode u0 v1) (PairCode u0 Bot) crho
                 (mkSigma (mkSigma cu0 tt) (inl nbu0)) evM-pv1
                 (mkSigma (LeCode-refl u0 cu0) tt)
          conv-eta-fwd-both M rho crho u0 UCode (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 UCode nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho u0 PropCode (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 PropCode nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho u0 (FunEl g) (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 (FunEl g) nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho u0 (PiCode a f) (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 (PiCode a f) nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho u0 (SigmaCode a f) (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 (SigmaCode a f) nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho u0 (PairCode u' v') (inl nbu0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho u0 (PairCode u' v') nbu0 tt cu0 cv0 evFst evSnd (inl nbu0)
          conv-eta-fwd-both M rho crho Bot v0 (inr nbv0) cu0 cv0 evFst evSnd =
            let mkSigma u1 evM-pu1 = sndEv-extract M rho v0 nbv0 evSnd
            in EvalRel-down M rho (PairCode u1 v0) (PairCode Bot v0) crho
                 (mkSigma (mkSigma tt cv0) (inr nbv0)) evM-pu1
                 (mkSigma tt (LeCode-refl v0 cv0))
          conv-eta-fwd-both M rho crho UCode v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho UCode v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)
          conv-eta-fwd-both M rho crho PropCode v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho PropCode v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)
          conv-eta-fwd-both M rho crho (FunEl g) v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho (FunEl g) v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)
          conv-eta-fwd-both M rho crho (PiCode a f) v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho (PiCode a f) v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)
          conv-eta-fwd-both M rho crho (SigmaCode a f) v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho (SigmaCode a f) v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)
          conv-eta-fwd-both M rho crho (PairCode u' v') v0 (inr nbv0) cu0 cv0 evFst evSnd =
            conv-eta-core M rho crho (PairCode u' v') v0 tt nbv0 cu0 cv0 evFst evSnd (inr nbv0)

      -- Forward: MkPair(Fst M)(Snd M) -> M
      fwd : (u : FinEl) -> EvalRel (MkPairE (FstE M) (SndE M)) rho u -> EvalRel M rho u
      fwd Bot ev = EvalRel-Bot M rho
      fwd (PairCode u0 v0) (mkSigma coh (mkSigma evFst evSnd)) =
        conv-eta-fwd-pair M rho crho u0 v0 (snd coh) (fst (fst coh)) (snd (fst coh)) evFst evSnd
      fwd UCode ()
      fwd PropCode ()
      fwd (FunEl g) ()
      fwd (PiCode a f) ()
      fwd (SigmaCode a f) ()

      -- Backward: M -> MkPair(Fst M)(Snd M)
      bwd : (u : FinEl) -> EvalRel M rho u -> EvalRel (MkPairE (FstE M) (SndE M)) rho u
      bwd Bot ev = tt
      bwd (PairCode u0 v0) ev =
        mkSigma (EvalRel-coh M rho (PairCode u0 v0) ev)
          (mkSigma (mkFstEv M rho u0 v0 ev) (mkSndEv M rho u0 v0 ev))
      bwd UCode ev = bwd-nonPair UCode tt ev
      bwd PropCode ev = bwd-nonPair PropCode tt ev
      bwd (FunEl g) ev = bwd-nonPair (FunEl g) tt ev
      bwd (PiCode a f) ev = bwd-nonPair (PiCode a f) tt ev
      bwd (SigmaCode a f) ev = bwd-nonPair (SigmaCode a f) tt ev

      -- InvTyp for LHS
      invLHS : InvTyp G (MkPairE (FstE M) (SndE M)) (SigmaE A B) rho
      invLHS u ev =
        let evM' = fwd u ev
            mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM-u' (mkSigma fm evSig)))) = invM u evM'
        in mkSigma u' (mkSigma a' (mkSigma le (mkSigma (bwd u' evM-u') (mkSigma fm evSig))))

  -- conv-MkPair-fst: congruence for MkPair first component
  convSound' (conv-MkPair-fst {G = G} {A = A} {B = B} {M = M} {M' = M'} {N = N}
    dA dB dMM' dN) rho fits =
    let crho = Fits-CoherentEnv rho fits
        mkSigma invM (mkSigma invM' (mkSigma fwdM bwdM)) = convSound' dMM' rho fits
        fwd = \ u ev -> convSound-MkPair-fst-fwd M M' N rho u fwdM ev
        bwd = \ u ev -> convSound-MkPair-fst-fwd M' M N rho u bwdM ev
        invTypA = theorem1 dA rho fits
        body-ih = \ x a fm evA -> theorem1 dB (extendEnv rho x) (mkSigma fits (mkSigma a (mkSigma fm evA)))
        invN = theorem1 dN rho fits
        invN' = convertInvTyp-subst1 {G = G} B M M' N rho crho fwdM invN
        invMkP-lhs = InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN
        invMkP-rhs = InvTyp-MkPair A B M' N rho fits invTypA body-ih invM' invN'
    in mkSigma invMkP-lhs (mkSigma invMkP-rhs (mkSigma fwd bwd))

  -- conv-MkPair-snd: congruence for MkPair second component
  convSound' (conv-MkPair-snd {A = A} {B = B} {M = M} {N = N} {N' = N'}
    dA dB dM dNN') rho fits =
    let mkSigma invN (mkSigma invN' (mkSigma fwdN bwdN)) = convSound' dNN' rho fits
        fwd = \ u ev -> convSound-MkPair-snd-fwd M N N' rho u fwdN ev
        bwd = \ u ev -> convSound-MkPair-snd-fwd M N' N rho u bwdN ev
        invTypA = theorem1 dA rho fits
        body-ih = \ x a fm evA -> theorem1 dB (extendEnv rho x) (mkSigma fits (mkSigma a (mkSigma fm evA)))
        invM = theorem1 dM rho fits
        invMkP-lhs = InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN
        invMkP-rhs = InvTyp-MkPair A B M N' rho fits invTypA body-ih invM invN'
    in mkSigma invMkP-lhs (mkSigma invMkP-rhs (mkSigma fwd bwd))

  -- conv-Fst: congruence for Fst
  convSound' (conv-Fst {A = A} {B = B} {M = M} {M' = M'} dA dB dMM') rho fits =
    let mkSigma invM (mkSigma invM' (mkSigma fwdM bwdM)) = convSound' dMM' rho fits
        fwd = \ u ev -> convSound-Fst-fwd M M' rho u fwdM ev
        bwd = \ u ev -> convSound-Fst-fwd M' M rho u bwdM ev
        invFst-lhs = LTS.InvTyp-Fst A B M rho fits invM
        invFst-rhs = LTS.InvTyp-Fst A B M' rho fits invM'
    in mkSigma invFst-lhs (mkSigma invFst-rhs (mkSigma fwd bwd))

  -- conv-Snd: congruence for Snd
  convSound' (conv-Snd {G = G} {A = A} {B = B} {M = M} {M' = M'} dA dB dMM') rho fits =
    let crho = Fits-CoherentEnv rho fits
        mkSigma invM (mkSigma invM' (mkSigma fwdM bwdM)) = convSound' dMM' rho fits
        fwd = \ u ev -> convSound-Snd-fwd M M' rho u fwdM ev
        bwd = \ u ev -> convSound-Snd-fwd M' M rho u bwdM ev
        invSnd-lhs = LTS.InvTyp-Snd A B M rho fits invM
        -- InvTyp-Snd gives subst1 B (Fst M'), convert to subst1 B (Fst M)
        bwdFstM = \ u ev -> convSound-Fst-fwd M' M rho u bwdM ev
        invSnd-rhs = convertInvTyp-subst1 {G = G} B (FstE M') (FstE M) (SndE M') rho crho bwdFstM
          (LTS.InvTyp-Snd A B M' rho fits invM')
    in mkSigma invSnd-lhs (mkSigma invSnd-rhs (mkSigma fwd bwd))

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

  -- ty-Prop
  theorem1 (ty-Prop wf) rho fits u ev =
    mkSigma PropCode (mkSigma UCode
      (mkSigma (snd ev)
        (mkSigma (mkSigma tt tt) (mkSigma tt (mkSigma tt tt)))))

  -- ty-Prop-U
  theorem1 (ty-Prop-U dA) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evProp)))) =
          theorem1 dA rho fits u ev
        fmU = FinMem-Prop-in-U u' a' fm (snd evProp)
    in mkSigma u' (mkSigma UCode
         (mkSigma le (mkSigma evM (mkSigma fmU (mkSigma tt tt)))))

  -- ty-Pi-Prop: from LTS.InvTyp-Pi-Prop
  theorem1 (ty-Pi-Prop {A = A} {B = B} d1 d2) rho fits u ev =
    LTS.InvTyp-Pi-Prop A B rho fits
      (theorem1 d1 rho fits)
      (\ x a fm evA ->
        theorem1 d2 (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))
      u ev

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

  -- ty-Sigma
  theorem1 (ty-Sigma {A = A} {B = B} d1 d2) rho fits u ev =
    LTS.InvTyp-Sigma A B rho fits
      (theorem1 d1 rho fits)
      (\ x a fm evA ->
        theorem1 d2 (extendEnv rho x)
          (mkSigma fits (mkSigma a (mkSigma fm evA))))
      u ev

  -- ty-MkPair
  theorem1 (ty-MkPair {A = A} {B = B} {M = M} {N = N} dA dB dM dN)
    rho fits u ev =
    InvTyp-MkPair A B M N rho fits
      (theorem1 dA rho fits)
      (\ x a fm evA -> theorem1 dB (extendEnv rho x) (mkSigma fits (mkSigma a (mkSigma fm evA))))
      (theorem1 dM rho fits) (theorem1 dN rho fits)
      u ev

  -- ty-Fst
  theorem1 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) rho fits u ev =
    LTS.InvTyp-Fst A B M rho fits
      (theorem1 dM rho fits)
      u ev

  -- ty-Snd
  theorem1 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) rho fits u ev =
    LTS.InvTyp-Snd A B M rho fits
      (theorem1 dM rho fits)
      u ev
