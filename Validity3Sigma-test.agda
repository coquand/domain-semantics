{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3Sigma-test.agda
--
-- Prototype: test that EqVal2-sym at (PairCode, SigmaCode) works
-- with full bundling (Val2 = Pair HasType Val2c, edges take Val2).
--
-- Only definitions + sym. Not complete.
------------------------------------------------------------------------

module Validity3Sigma-test where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ;
              FinFun ; List ; nil ; cons)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  Fst ; Snd ; MkPair ; subst1)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-conv ; ty-Fst ; ty-Snd ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv)
import TypingRulesSigma
open import SubstitutionLemmaSigma using (typing-ConvTm)
import SubstitutionLemmaSigma
open import PaperSemanticsSigma using (Coherent ; EvalFun ;
  CoherentFun ; CoherentFunTail ; FinMem ; FinMemFun ; FinMemAllU ;
  Coherent-EvalFun ; coh-from-aU ; cft-from-cf)
open import ReductionSigma using (Red ; mkRed ; HeadRed ; headred-refl)
open import ValiditySigma using (
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Red-unique-Sigma)

------------------------------------------------------------------------
-- Minimal mutual block: test definitions + EqVal2-sym
------------------------------------------------------------------------

data Red3 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set where
  mkRed3 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    HeadRed M N -> ConvTm G M N A -> Red3 G M N A

Red3-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> HeadRed M N
Red3-hr (mkRed3 hr _) = hr

Red3-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> ConvTm G M N A
Red3-conv (mkRed3 _ ct) = ct

{-# TERMINATING #-}
mutual

  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
  Val2 G M A u a = Pair (HasType G M A) (Val2c G M A u a)

  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
  EqVal2 G M N A u a = Pair (ConvTm G M N A) (EqVal2c G M N A u a)

  -- Inner core (simplified: only show SigmaCode/PairCode cases + Top elsewhere)
  Val2c : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
  Val2c G M A (PairCode u' v') (SigmaCode b f) =
    Pair (ValTy2 G A (SigmaCode b f)) (ValPair2 G M A u' v' b f)
  Val2c G M A u a = Top  -- all other cases

  EqVal2c : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
  EqVal2c G M N A (PairCode u' v') (SigmaCode b f) =
    Pair (ValTy2 G A (SigmaCode b f))
         (Pair (ValPair2 G M A u' v' b f)
               (Pair (ValPair2 G N A u' v' b f)
                     (EqValPair2 G M N A u' v' b f)))
  EqVal2c G M N A u a = Top  -- all other cases

  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
  ValTy2 G M Bot = Top
  ValTy2 G M UCode = Top
  ValTy2 G M PropCode = Top
  ValTy2 G M (FunEl g) = Top
  ValTy2 G M (PiCode b f) = Top  -- simplified
  ValTy2 G M (SigmaCode b f) = ValTySigma2 G M b f
  ValTy2 G M (PairCode u v) = Top

  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
  EqValTy2 G M N u = Top  -- simplified for test

  -- Sigma structures
  ValTySigma2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set
  ValTySigma2 {n} G M b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red3 G M (SigmaE A B) U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (HasType G A U) \ _ ->
    Sigma (HasType (extend G A) B U) \ _ ->
    Pair (ValTy2 G A b)
         (Pair (SigmaEdgeVal2 G A B b f)
               (SigmaEdgeEq2 G A B b f))

  ValPair2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinEl -> FinEl -> FinFun -> Set
  ValPair2 {n} G M T u' v' b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red3 G T (SigmaE A B) U) \ _ ->
    Pair (Val2 G (Fst M) A u' b)
         (Val2 G (Snd M) (subst1 B (Fst M)) v' (EvalFun f u'))

  EqValPair2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> FinEl -> FinFun -> Set
  EqValPair2 {n} G M N T u' v' b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red3 G T (SigmaE A B) U) \ _ ->
    Sigma (EqVal2 G (Fst M) (Fst N) A u' b) \ _ ->
    Sigma (EqValTy2 G (subst1 B (Fst M)) (subst1 B (Fst N)) (EvalFun f u')) \ _ ->
    EqVal2 G (Snd M) (Snd N) (subst1 B (Fst M)) v' (EvalFun f u')

  -- Sigma edges: take Val2 (with HasType!)
  SigmaEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  SigmaEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
    ValTy2 G (subst1 B N) v

  SigmaEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  SigmaEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
    EqValTy2 G (subst1 B N1) (subst1 B N2) v

  -- Convert EqVal2c type parameter using EqValTy2
  EqVal2c-EqValTy2-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
    (u b : FinEl) -> EqValTy2 G C C' b ->
    EqVal2c G M N C u b -> EqVal2c G M N C' u b
  EqVal2c-EqValTy2-fwd (PairCode _ _) (SigmaCode _ _) eqv inner = inner  -- EqValTy2 is Top here
  EqVal2c-EqValTy2-fwd u a eqv tt = tt

  EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
    EqVal2 G M N A u a -> ConvTm G M N A
  EqVal2-ct = fst

  EqVal2-inner : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
    EqVal2 G M N A u a -> EqVal2c G M N A u a
  EqVal2-inner = snd

  ------------------------------------------------------------------
  -- THE KEY TEST: EqVal2-sym at (PairCode, SigmaCode)
  ------------------------------------------------------------------

  EqVal2c-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    ConvTm G M N A ->  -- from outer layer
    EqVal2c G M N A u a -> EqVal2c G N M A u a

  -- All non-Sigma cases: trivial (Top)
  EqVal2c-sym {A = A} (PairCode u' v') (SigmaCode b f) cu ca ctMN ev =
    let vty     = fst ev
        vpairM  = fst (snd ev)
        vpairN  = fst (snd (snd ev))
        eqpair  = snd (snd (snd ev))
        -- EqValPair2 fields
        A0      = fst eqpair
        B0      = fst (snd eqpair)
        red     = fst (snd (snd eqpair))
        eqFst   = fst (snd (snd (snd eqpair)))
        eqTySnd = fst (snd (snd (snd (snd eqpair))))
        eqSnd   = snd (snd (snd (snd (snd eqpair))))
        -- HasType for Fst M and Fst N from the outer ConvTm
        htM     = fst (typing-ConvTm ctMN)
        htN     = snd (typing-ConvTm ctMN)
        -- Extract A0, B0, Red3 from ValTySigma2
        A0sig  = fst vty
        B0sig  = fst (snd vty)
        redSig = fst (snd (snd vty))
        htA0   = fst (snd (snd (snd (snd (snd vty)))))
        htB0   = fst (snd (snd (snd (snd (snd (snd vty))))))
        -- Unify A0/B0 with A0sig/B0sig via Red uniqueness
        mkSigma eqA0 eqB0 = Red-unique-Sigma (mkRed (Red3-hr red)) (mkRed (Red3-hr redSig))
        -- ConvTm G A (SigmaE A0sig B0sig) U from Red3
        convASig = Red3-conv redSig
        -- HasType G M (SigmaE A0 B0) via ty-conv
        htMsig = ty-conv htM convASig (TypingRulesSigma.ty-Sigma htA0 htB0)
        htNsig = ty-conv htN convASig (TypingRulesSigma.ty-Sigma htA0 htB0)
        htFstM = ty-Fst htA0 htB0 htMsig
        htFstN = ty-Fst htA0 htB0 htNsig
        -- Symmetry for Fst EqVal2
        eqFstSym = EqVal2-sym u' b (fst (fst cu)) (fst ca) eqFst
        -- SigmaEdgeEq2 from ValTySigma2
        sigEdgeEq = snd (snd (snd (snd (snd (snd (snd (snd (snd vty))))))))
        -- ConvTm G M N (SigmaE A0sig B0sig) via conv-conv
        htSig   = TypingRulesSigma.ty-Sigma htA0 htB0
        ctMNsig = conv-conv ctMN convASig htSig
        -- ConvTm G (Fst M) (Fst N) A0sig via conv-Fst
        ctFst   = TypingRulesSigma.conv-Fst htA0 htB0 ctMNsig
        -- ConvTm G (subst1 B0sig (Fst M)) (subst1 B0sig (Fst N)) U
        convBFst0 = SubstitutionLemmaSigma.subst1-cong-ConvTm htA0 htB0 htFstM htFstN ctFst
        -- Transport to B0 (from EqValPair2) via eqB0
        convBFst = Eq-transport (\ X -> ConvTm _ (subst1 X (Fst _)) (subst1 X (Fst _)) U) (Eq-sym eqB0) convBFst0
        -- HasType G (subst1 B0 (Fst N)) U
        htBFstN0 = SubstitutionLemmaSigma.subst-HasType (SubstitutionLemmaSigma.subst1-WtSub htA0 htFstN) (SubstitutionLemmaSigma.typing-WfCtx htA0) htB0
        htBFstN = Eq-transport (\ X -> HasType _ (subst1 X (Fst _)) U) (Eq-sym eqB0) htBFstN0
        -- Sym the Snd EqVal2
        cv'     = snd (fst cu)
        cev     = Coherent-EvalFun f u' (snd ca) (fst (fst cu))
        eqSndSym = EqVal2-sym v' (EvalFun f u') cv' cev eqSnd
        -- Convert Snd from subst1 B0 (Fst M) to subst1 B0 (Fst N)
        -- outer ConvTm: conv-conv
        ctSndSym = EqVal2-ct eqSndSym  -- ConvTm G (Snd N) (Snd M) (subst1 B0 (Fst M))
        ctSndConverted = conv-conv ctSndSym convBFst htBFstN
        -- inner EqVal2c: EqValTy2 is Top in this test, so the inner is unchanged
        innerSndSym = EqVal2-inner eqSndSym
        -- Build converted EqVal2
        eqSndFinal = mkSigma ctSndConverted innerSndSym
        -- EqValTy2 sym (Top in this test)
        eqTySndSym = eqTySnd
    in mkSigma vty
         (mkSigma vpairN (mkSigma vpairM
           (mkSigma A0 (mkSigma B0 (mkSigma red
             (mkSigma eqFstSym (mkSigma eqTySndSym eqSndFinal)))))))

  -- Non-Sigma cases
  EqVal2c-sym u a cu ca ct tt = tt

  EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
    (u a : FinEl) -> Coherent u -> Coherent a ->
    EqVal2 G M N A u a -> EqVal2 G N M A u a
  EqVal2-sym u a cu ca (mkSigma ct inner) =
    mkSigma (conv-sym ct) (EqVal2c-sym u a cu ca ct inner)
