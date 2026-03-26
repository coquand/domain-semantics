{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Adequacy2Sigma.agda
--
-- Bundled adequacy layer extended with Sigma types.
-- Parallel version of Adequacy2.agda.
--
-- Produces Val2/EqVal2 (with HasType/ConvTm at leaves) from
-- Validity2Sigma, instead of Val/EqVal.
--
-- Uses the paper's two-substitution approach (Theorem 2, p.660):
--   1. adequacySub2 produces Val2 (bundled with HasType/ConvTm)
--   2. adequacyEqSub2 produces EqVal2
--   3. adequacyConvSub2 for cross-substitution equality
--
-- New cases relative to Adequacy2.agda:
--   HasType: ty-Sigma, ty-MkPair, ty-Fst, ty-Snd, ty-Prop, ty-Prop-U, ty-Pi-Prop
--   ConvTm:  conv-Sigma, conv-beta-fst, conv-beta-snd, conv-pair-eta,
--            conv-MkPair-fst, conv-MkPair-snd, conv-Fst, conv-Snd,
--            conv-Prop-U, conv-Pi-Prop
--
-- 0 postulates.
------------------------------------------------------------------------

module Adequacy2Sigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons)
open import PaperSemanticsSigma using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; Comp ; Comp-down ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; EvalFun ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  LeFunCode ; LeFunCode-refl ;
  FinMem ; FinMemFun ; FinMemAllU ; FinMemAllProp ;
  FinMem-a-in-U ; finMemUCode-Sup ;
  finMem-upward ; finMem-Sup-left ; finMem-Sup-right ; coh-from-aU ;
  FinMem-coh-u ; cft-from-cf ; CoherentFunTail ; CoherentFunTail-append ;
  mkCFT ; NotBot ; FinMem-Prop-Bot ; FinMem-Prop-Bot-FunEl ;
  FinMem-Prop-to-U ; FinMem-U-to-PropCode ; absurdEl)
open import ReductionSigma using (Red ; mkRed ; Red-refl ; Red-hr ; HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-strip-Sigma ;
  headred-step ; headred-beta ; headred-refl ; subst-subst1-comm ;
  headred-beta-fst ; headred-beta-snd ; headred-fst ; headred-snd ;
  idSub ; substExpr-id)
open import RawSemanticsSigma using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ; Pi-edgewise ; Sigma-edgewise ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr ; subst1Sub)
  renaming (Sigma to SigmaE)
open import TypingRulesSigma using (Ctx ; empty ; extend ; lookup ;
  HasType ; ConvTm ; WfCtx ; wf-empty ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ; ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Sigma ; conv-beta-fst ; conv-beta-snd ; conv-pair-eta ;
  conv-MkPair-fst ; conv-MkPair-snd ; conv-Fst ; conv-Snd ;
  conv-Prop ; conv-Prop-U ; conv-Pi-Prop)
open import Validity2Sigma using (
  Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  ValTyPi2 ; ValPi2 ; EqValTyPi2 ; EqValPi2 ;
  ValTySigma2 ; EqValTySigma2 ;
  PiEdgeVal2 ; PiEdgeEq2 ; PiEdgeEqTy2 ;
  PiAppVal2 ; PiAppEq2 ; PiAppEqVal2 ;
  SigmaEdgeVal2 ; SigmaEdgeEq2 ; SigmaEdgeEqTy2 ;
  Val2-Bot ; EqVal2-Bot ;
  Val2-transport-M ; Val2-transport-A ;
  EqVal2-transport-A ;
  ValTy2-transport ; EqValTy2-transport ;
  Val2-EqValTy2-fwd ; EqVal2-EqValTy2-fwd ;
  Val2-to-EqVal2 ; EqVal2-sym ; EqVal2-trans ;
  Val2-from-EqVal2-first ; Val2-from-EqVal2-second ;
  ValTy2-Sup ; EqValTy2-sym ;
  upVal2 ; downVal2 ; restrictVal2 ;
  upEqVal2 ; downEqVal2 ; restrictEqVal2 ;
  bU-from-cf-fmU)
open import ValiditySigma using (Edge ; EdgeIn ; here ; there ;
  Red-unique-Pi ; Red-unique-Sigma ;
  FinMem-Coherent ;
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val)
-- Re-import directly (Validity2Sigma re-exports don't always resolve)
open import ValiditySigma using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import SelectionSigma using (FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow)
open import TypingSemanticsSigma using (convSound ; convSound-inv ; convSound' ; theorem1 ;
  conv-Prop-chain ; LeCode-Bot-eq)
open import LemmaForTSSigma using (Fits ; Typed ; Fits-CoherentEnv)
open import EvalSubstitutionSigma using (EvalRel-subst1-backward ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-Pi-app-type ; EvalRel-Pi-body ; EvalRel-subst1-forward)
open import LemmaForA2Sigma using (tyU2-helper ;
  sup-transport-Val2 ; sup-transport-EqVal2 ;
  app-transport-Val2 ; app-transport-EqVal2)
  renaming (Val2-U-to-ValTy2 to Val2-U-to-ValTy2' ;
            EqVal2-U-to-ValTy2-fst to EqVal2-U-to-ValTy2-fst' ;
            EqVal2-U-to-ValTy2-snd to EqVal2-U-to-ValTy2-snd' ;
            EqVal2-U-to-EqValTy2 to EqVal2-U-to-EqValTy2')

open import RawSyntaxSigma using (Ren ; liftRen ; renExpr ; wkRen)
open import SubstitutionLemmaSigma using (typing-ConvTm ; WtSub ;
  subst-HasType ; subst-ConvTm ; liftSub-WtSub ; subst1-WtSub ;
  typing-WfCtx ; typing-type ; ctx-conv-HasType ; ctx-conv-ConvTm ;
  subst1-cong-ConvTm ; wk-HasType ; wk-ConvTm ;
  WtConvSub ; subst-ConvTm-cross ; liftSub-WtConvSub)

------------------------------------------------------------------------
-- Eq helpers
------------------------------------------------------------------------

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans S.refl q = q

Eq-cong2 : {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f S.refl S.refl = S.refl

------------------------------------------------------------------------
-- Part 1: Substitution helpers (extended with Sigma/MkPair/Fst/Snd/Prop)
------------------------------------------------------------------------

extSub : {h g : Nat} -> Sub h g -> Expr h -> Sub h (suc g)
extSub sigma t fzero    = t
extSub sigma t (fsuc i) = sigma i

substExpr-ext : {h g : Nat} (sigma sigma' : Sub h g) ->
  ((i : Fin g) -> Eq (sigma i) (sigma' i)) ->
  (M : Expr g) -> Eq (substExpr sigma M) (substExpr sigma' M)
substExpr-ext sigma sigma' hyp (Var i)   = hyp i
substExpr-ext sigma sigma' hyp U         = S.refl
substExpr-ext sigma sigma' hyp Prop      = S.refl
substExpr-ext sigma sigma' hyp (Pi A B)  =
  Eq-cong2 Pi (substExpr-ext sigma sigma' hyp A)
              (substExpr-ext (liftSub sigma) (liftSub sigma')
                (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong wkExpr (hyp j) }) B)
substExpr-ext sigma sigma' hyp (Lam A M) =
  Eq-cong2 Lam (substExpr-ext sigma sigma' hyp A)
               (substExpr-ext (liftSub sigma) (liftSub sigma')
                 (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong wkExpr (hyp j) }) M)
substExpr-ext sigma sigma' hyp (App f a) =
  Eq-cong2 App (substExpr-ext sigma sigma' hyp f)
               (substExpr-ext sigma sigma' hyp a)
substExpr-ext sigma sigma' hyp (SigmaE A B) =
  Eq-cong2 SigmaE (substExpr-ext sigma sigma' hyp A)
                   (substExpr-ext (liftSub sigma) (liftSub sigma')
                     (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong wkExpr (hyp j) }) B)
substExpr-ext sigma sigma' hyp (MkPair a b) =
  Eq-cong2 MkPair (substExpr-ext sigma sigma' hyp a)
                   (substExpr-ext sigma sigma' hyp b)
substExpr-ext sigma sigma' hyp (Fst M) =
  S.Eq-cong Fst (substExpr-ext sigma sigma' hyp M)
substExpr-ext sigma sigma' hyp (Snd M) =
  S.Eq-cong Snd (substExpr-ext sigma sigma' hyp M)

substExpr-ren : {k h g : Nat} (sigma : Sub h g) (rho : Ren k g) (M : Expr k) ->
  Eq (substExpr sigma (renExpr rho M)) (substExpr (\ i -> sigma (rho i)) M)
substExpr-ren sigma rho (Var i)   = S.refl
substExpr-ren sigma rho U         = S.refl
substExpr-ren sigma rho Prop      = S.refl
substExpr-ren sigma rho (Pi A B)  =
  Eq-cong2 Pi (substExpr-ren sigma rho A)
    (Eq-trans (substExpr-ren (liftSub sigma) (liftRen rho) B)
      (substExpr-ext (\ j -> liftSub sigma (liftRen rho j))
                     (liftSub (\ i -> sigma (rho i)))
                     (\ { fzero -> S.refl ; (fsuc j) -> S.refl })
                     B))
substExpr-ren sigma rho (Lam A M) =
  Eq-cong2 Lam (substExpr-ren sigma rho A)
    (Eq-trans (substExpr-ren (liftSub sigma) (liftRen rho) M)
      (substExpr-ext (\ j -> liftSub sigma (liftRen rho j))
                     (liftSub (\ i -> sigma (rho i)))
                     (\ { fzero -> S.refl ; (fsuc j) -> S.refl })
                     M))
substExpr-ren sigma rho (App f a) =
  Eq-cong2 App (substExpr-ren sigma rho f) (substExpr-ren sigma rho a)
substExpr-ren sigma rho (SigmaE A B) =
  Eq-cong2 SigmaE (substExpr-ren sigma rho A)
    (Eq-trans (substExpr-ren (liftSub sigma) (liftRen rho) B)
      (substExpr-ext (\ j -> liftSub sigma (liftRen rho j))
                     (liftSub (\ i -> sigma (rho i)))
                     (\ { fzero -> S.refl ; (fsuc j) -> S.refl })
                     B))
substExpr-ren sigma rho (MkPair a b) =
  Eq-cong2 MkPair (substExpr-ren sigma rho a) (substExpr-ren sigma rho b)
substExpr-ren sigma rho (Fst M) = S.Eq-cong Fst (substExpr-ren sigma rho M)
substExpr-ren sigma rho (Snd M) = S.Eq-cong Snd (substExpr-ren sigma rho M)

substExpr-wk : {h g : Nat} (sigma : Sub h g) (M : Expr g) (t : Expr h) ->
  Eq (substExpr (extSub sigma t) (wkExpr M)) (substExpr sigma M)
substExpr-wk sigma M t = substExpr-ren (extSub sigma t) wkRen M

renExpr-ext : {n m : Nat} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (M : Expr n) -> Eq (renExpr r1 M) (renExpr r2 M)
renExpr-ext r1 r2 hyp (Var i)   = S.Eq-cong Var (hyp i)
renExpr-ext r1 r2 hyp U         = S.refl
renExpr-ext r1 r2 hyp Prop      = S.refl
renExpr-ext r1 r2 hyp (Pi A B)  =
  Eq-cong2 Pi (renExpr-ext r1 r2 hyp A)
    (renExpr-ext (liftRen r1) (liftRen r2)
      (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong fsuc (hyp j) }) B)
renExpr-ext r1 r2 hyp (Lam A M) =
  Eq-cong2 Lam (renExpr-ext r1 r2 hyp A)
    (renExpr-ext (liftRen r1) (liftRen r2)
      (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong fsuc (hyp j) }) M)
renExpr-ext r1 r2 hyp (App f a) =
  Eq-cong2 App (renExpr-ext r1 r2 hyp f) (renExpr-ext r1 r2 hyp a)
renExpr-ext r1 r2 hyp (SigmaE A B) =
  Eq-cong2 SigmaE (renExpr-ext r1 r2 hyp A)
    (renExpr-ext (liftRen r1) (liftRen r2)
      (\ { fzero -> S.refl ; (fsuc j) -> S.Eq-cong fsuc (hyp j) }) B)
renExpr-ext r1 r2 hyp (MkPair a b) =
  Eq-cong2 MkPair (renExpr-ext r1 r2 hyp a) (renExpr-ext r1 r2 hyp b)
renExpr-ext r1 r2 hyp (Fst M) = S.Eq-cong Fst (renExpr-ext r1 r2 hyp M)
renExpr-ext r1 r2 hyp (Snd M) = S.Eq-cong Snd (renExpr-ext r1 r2 hyp M)

renExpr-comp : {a b c : Nat} (r2 : Ren b c) (r1 : Ren a b) (M : Expr a) ->
  Eq (renExpr r2 (renExpr r1 M)) (renExpr (\ i -> r2 (r1 i)) M)
renExpr-comp r2 r1 (Var i)   = S.refl
renExpr-comp r2 r1 U         = S.refl
renExpr-comp r2 r1 Prop      = S.refl
renExpr-comp r2 r1 (Pi A B)  =
  Eq-cong2 Pi (renExpr-comp r2 r1 A)
    (Eq-trans (renExpr-comp (liftRen r2) (liftRen r1) B)
      (renExpr-ext (\ i -> liftRen r2 (liftRen r1 i))
                   (liftRen (\ i -> r2 (r1 i)))
                   (\ { fzero -> S.refl ; (fsuc j) -> S.refl }) B))
renExpr-comp r2 r1 (Lam A M) =
  Eq-cong2 Lam (renExpr-comp r2 r1 A)
    (Eq-trans (renExpr-comp (liftRen r2) (liftRen r1) M)
      (renExpr-ext (\ i -> liftRen r2 (liftRen r1 i))
                   (liftRen (\ i -> r2 (r1 i)))
                   (\ { fzero -> S.refl ; (fsuc j) -> S.refl }) M))
renExpr-comp r2 r1 (App f a) =
  Eq-cong2 App (renExpr-comp r2 r1 f) (renExpr-comp r2 r1 a)
renExpr-comp r2 r1 (SigmaE A B) =
  Eq-cong2 SigmaE (renExpr-comp r2 r1 A)
    (Eq-trans (renExpr-comp (liftRen r2) (liftRen r1) B)
      (renExpr-ext (\ i -> liftRen r2 (liftRen r1 i))
                   (liftRen (\ i -> r2 (r1 i)))
                   (\ { fzero -> S.refl ; (fsuc j) -> S.refl }) B))
renExpr-comp r2 r1 (MkPair a b) =
  Eq-cong2 MkPair (renExpr-comp r2 r1 a) (renExpr-comp r2 r1 b)
renExpr-comp r2 r1 (Fst M) = S.Eq-cong Fst (renExpr-comp r2 r1 M)
renExpr-comp r2 r1 (Snd M) = S.Eq-cong Snd (renExpr-comp r2 r1 M)

wk-lift-comm : {h k : Nat} (rho : Ren h k) (M : Expr h) ->
  Eq (renExpr (liftRen rho) (wkExpr M)) (wkExpr (renExpr rho M))
wk-lift-comm rho M =
  Eq-trans (renExpr-comp (liftRen rho) wkRen M)
    (S.Eq-sym (renExpr-comp wkRen rho M))

renExpr-substExpr : {k h g : Nat} (rho : Ren h k) (sigma : Sub h g) (M : Expr g) ->
  Eq (renExpr rho (substExpr sigma M))
     (substExpr (\ i -> renExpr rho (sigma i)) M)
renExpr-substExpr rho sigma (Var i) = S.refl
renExpr-substExpr rho sigma U = S.refl
renExpr-substExpr rho sigma Prop = S.refl
renExpr-substExpr rho sigma (Pi A B) =
  Eq-cong2 Pi (renExpr-substExpr rho sigma A)
    (Eq-trans (renExpr-substExpr (liftRen rho) (liftSub sigma) B)
      (substExpr-ext (\ j -> renExpr (liftRen rho) (liftSub sigma j))
                     (liftSub (\ i -> renExpr rho (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> wk-lift-comm rho (sigma j) })
                     B))
renExpr-substExpr rho sigma (Lam A M) =
  Eq-cong2 Lam (renExpr-substExpr rho sigma A)
    (Eq-trans (renExpr-substExpr (liftRen rho) (liftSub sigma) M)
      (substExpr-ext (\ j -> renExpr (liftRen rho) (liftSub sigma j))
                     (liftSub (\ i -> renExpr rho (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> wk-lift-comm rho (sigma j) })
                     M))
renExpr-substExpr rho sigma (App f a) =
  Eq-cong2 App (renExpr-substExpr rho sigma f) (renExpr-substExpr rho sigma a)
renExpr-substExpr rho sigma (SigmaE A B) =
  Eq-cong2 SigmaE (renExpr-substExpr rho sigma A)
    (Eq-trans (renExpr-substExpr (liftRen rho) (liftSub sigma) B)
      (substExpr-ext (\ j -> renExpr (liftRen rho) (liftSub sigma j))
                     (liftSub (\ i -> renExpr rho (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> wk-lift-comm rho (sigma j) })
                     B))
renExpr-substExpr rho sigma (MkPair a b) =
  Eq-cong2 MkPair (renExpr-substExpr rho sigma a) (renExpr-substExpr rho sigma b)
renExpr-substExpr rho sigma (Fst M) = S.Eq-cong Fst (renExpr-substExpr rho sigma M)
renExpr-substExpr rho sigma (Snd M) = S.Eq-cong Snd (renExpr-substExpr rho sigma M)

substExpr-sub : {k h g : Nat} (tau : Sub k h) (sigma : Sub h g) (M : Expr g) ->
  Eq (substExpr tau (substExpr sigma M))
     (substExpr (\ i -> substExpr tau (sigma i)) M)
substExpr-sub tau sigma (Var i) = S.refl
substExpr-sub tau sigma U = S.refl
substExpr-sub tau sigma Prop = S.refl
substExpr-sub tau sigma (Pi A B) =
  Eq-cong2 Pi (substExpr-sub tau sigma A)
    (Eq-trans (substExpr-sub (liftSub tau) (liftSub sigma) B)
      (substExpr-ext (\ j -> substExpr (liftSub tau) (liftSub sigma j))
                     (liftSub (\ i -> substExpr tau (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> Eq-trans (substExpr-ren (liftSub tau) wkRen (sigma j))
                                               (S.Eq-sym (renExpr-substExpr wkRen tau (sigma j))) })
                     B))
substExpr-sub tau sigma (Lam A M) =
  Eq-cong2 Lam (substExpr-sub tau sigma A)
    (Eq-trans (substExpr-sub (liftSub tau) (liftSub sigma) M)
      (substExpr-ext (\ j -> substExpr (liftSub tau) (liftSub sigma j))
                     (liftSub (\ i -> substExpr tau (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> Eq-trans (substExpr-ren (liftSub tau) wkRen (sigma j))
                                               (S.Eq-sym (renExpr-substExpr wkRen tau (sigma j))) })
                     M))
substExpr-sub tau sigma (App f a) =
  Eq-cong2 App (substExpr-sub tau sigma f) (substExpr-sub tau sigma a)
substExpr-sub tau sigma (SigmaE A B) =
  Eq-cong2 SigmaE (substExpr-sub tau sigma A)
    (Eq-trans (substExpr-sub (liftSub tau) (liftSub sigma) B)
      (substExpr-ext (\ j -> substExpr (liftSub tau) (liftSub sigma j))
                     (liftSub (\ i -> substExpr tau (sigma i)))
                     (\ { fzero -> S.refl ;
                          (fsuc j) -> Eq-trans (substExpr-ren (liftSub tau) wkRen (sigma j))
                                               (S.Eq-sym (renExpr-substExpr wkRen tau (sigma j))) })
                     B))
substExpr-sub tau sigma (MkPair a b) =
  Eq-cong2 MkPair (substExpr-sub tau sigma a) (substExpr-sub tau sigma b)
substExpr-sub tau sigma (Fst M) = S.Eq-cong Fst (substExpr-sub tau sigma M)
substExpr-sub tau sigma (Snd M) = S.Eq-cong Snd (substExpr-sub tau sigma M)

substExpr-comp : {h g : Nat} (sigma : Sub h g)
  (M : Expr (suc g)) (t : Expr h) ->
  Eq (subst1 (substExpr (liftSub sigma) M) t)
     (substExpr (extSub sigma t) M)
substExpr-comp sigma M t =
  Eq-trans (substExpr-sub (subst1Sub t) (liftSub sigma) M)
    (substExpr-ext (\ i -> substExpr (subst1Sub t) (liftSub sigma i))
                   (extSub sigma t)
                   (\ { fzero -> S.refl ;
                        (fsuc j) -> Eq-trans (substExpr-ren (subst1Sub t) wkRen (sigma j))
                                             (substExpr-id (sigma j)) })
                   M)

------------------------------------------------------------------------
-- Part 2: EvalRel transport
------------------------------------------------------------------------

EvalRel-transport : {n : Nat} {M M' : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Eq M M' -> EvalRel M rho u -> EvalRel M' rho u
EvalRel-transport S.refl ev = ev

------------------------------------------------------------------------
-- Part 3: ValidSub2 / ValidConvSub2
------------------------------------------------------------------------

ValidSub2 : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> EnvApprox g -> Set
ValidSub2 {h} {g} H G sigma rho =
  (i : Fin g) -> (u : FinEl) -> (cu : Coherent u) ->
  LeCode u (lookupEnv i rho) ->
  (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem u a ->
  Val2 H (sigma i) (substExpr sigma (lookup G i)) u a

ValidSub2-empty : {h : Nat} {H : Ctx h} (sigma : Sub h zero)
  (rho : EnvApprox zero) -> ValidSub2 H empty sigma rho
ValidSub2-empty sigma rho ()

ValidSub2-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma : Sub h g) (t : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  ValidSub2 H G sigma rho ->
  ((u : FinEl) -> Coherent u -> LeCode u v ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H t (substExpr sigma A) u a) ->
  ValidSub2 H (extend G A) (extSub sigma t) (extendEnv rho v)
ValidSub2-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 fzero u cu le a evA fm =
  let evA' = EvalRel-unwk Asrc rho v a evA
      val  = hyp0 u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma Asrc t)
  in Val2-transport-A {u = u} {a = a} eq val
ValidSub2-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 (fsuc i) u cu le a evA fm =
  let evA' = EvalRel-unwk (lookup G i) rho v a evA
      val  = vs i u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma (lookup G i) t)
  in Val2-transport-A {u = u} {a = a} eq val

ValidConvSub2 : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> EnvApprox g -> Set
ValidConvSub2 {h} {g} H G sigma sigma' rho =
  (i : Fin g) -> (u : FinEl) -> (cu : Coherent u) ->
  LeCode u (lookupEnv i rho) ->
  (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem u a ->
  EqVal2 H (sigma i) (sigma' i) (substExpr sigma (lookup G i)) u a

ValidConvSub2-refl : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {sigma : Sub h g} {rho : EnvApprox g} ->
  ValidSub2 H G sigma rho -> ValidConvSub2 H G sigma sigma rho
ValidConvSub2-refl vs i u cu le a evA fm =
  Val2-to-EqVal2 u a (vs i u cu le a evA fm)

ValidConvSub2-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma sigma' : Sub h g) (t t' : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  ValidConvSub2 H G sigma sigma' rho ->
  ((u : FinEl) -> Coherent u -> LeCode u v ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H t t' (substExpr sigma A) u a) ->
  ValidConvSub2 H (extend G A) (extSub sigma t) (extSub sigma' t') (extendEnv rho v)
ValidConvSub2-extend {H = H} {G = G} {A = Asrc} sigma sigma' t t' rho v vcs hyp0 fzero u cu le a evA fm =
  let evA' = EvalRel-unwk Asrc rho v a evA
      val  = hyp0 u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma Asrc t)
  in EqVal2-transport-A {u = u} {a = a} eq val
ValidConvSub2-extend {H = H} {G = G} {A = Asrc} sigma sigma' t t' rho v vcs hyp0 (fsuc i) u cu le a evA fm =
  let evA' = EvalRel-unwk (lookup G i) rho v a evA
      val  = vcs i u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma (lookup G i) t)
  in EqVal2-transport-A {u = u} {a = a} eq val

WtConvSub-refl : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {sigma : Sub h g} ->
  WtSub H G sigma -> WtConvSub H G sigma sigma
WtConvSub-refl ws i = conv-refl (ws i)

extSub-WtConvSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  {sigma sigma' : Sub h g} {t t' : Expr h} ->
  WtSub H G sigma -> WtConvSub H G sigma sigma' -> WfCtx H ->
  HasType G A U -> ConvTm H t t' (substExpr sigma A) ->
  WtConvSub H (extend G A) (extSub sigma t) (extSub sigma' t')
extSub-WtConvSub {H = H} {A = A} {sigma = sigma} {sigma' = sigma'} {t = t} {t' = t'} ws wcs wfH dA cvtt' fzero =
  S.Eq-transport (\ X -> ConvTm H t t' X) (S.Eq-sym (substExpr-wk sigma A t)) cvtt'
extSub-WtConvSub {H = H} {G = G} {A = A} {sigma = sigma} {sigma' = sigma'} {t = t} ws wcs wfH dA cvtt' (fsuc i) =
  S.Eq-transport (\ X -> ConvTm H (sigma i) (sigma' i) X) (S.Eq-sym (substExpr-wk sigma (lookup G i) t)) (wcs i)

------------------------------------------------------------------------
-- Part 4: Helpers
------------------------------------------------------------------------

EvalRel-bot : {n : Nat} (M : Expr n) (rho : EnvApprox n) -> EvalRel M rho Bot
EvalRel-bot (Var i)     rho = mkSigma tt (PaperSemanticsSigma.LeCode-Bot (lookupEnv i rho))
EvalRel-bot U           rho = mkSigma tt (PaperSemanticsSigma.LeCode-Bot UCode)
EvalRel-bot Prop        rho = mkSigma tt (PaperSemanticsSigma.LeCode-Bot PropCode)
EvalRel-bot (Pi A B)    rho = tt
EvalRel-bot (Lam A M)   rho = tt
EvalRel-bot (App f a)   rho = tt
EvalRel-bot (SigmaE A B) rho = tt
EvalRel-bot (MkPair a b) rho = tt
EvalRel-bot (Fst M)     rho = tt
EvalRel-bot (Snd M)     rho = tt

Coherent-CoherentFun : (b : FinEl) (f : FinFun) ->
  Coherent (PiCode b f) -> CoherentFunTail f
Coherent-CoherentFun b f cpf = snd cpf

FinMem-bU-from-Pi : (b : FinEl) (f : FinFun) ->
  CoherentFun f -> FinMemAllU f b -> FinMem b UCode
FinMem-bU-from-Pi b f cf fmAllU = bU-from-cf-fmU f b cf fmAllU

FinMem-from-LeCode-UCode : (u : FinEl) -> LeCode u UCode -> FinMem u UCode
FinMem-from-LeCode-UCode Bot              le = tt
FinMem-from-LeCode-UCode UCode            le = tt
FinMem-from-LeCode-UCode PropCode         ()
FinMem-from-LeCode-UCode (FunEl g)        ()
FinMem-from-LeCode-UCode (PiCode a f)     ()
FinMem-from-LeCode-UCode (SigmaCode a f)  ()
FinMem-from-LeCode-UCode (PairCode u v)   ()

------------------------------------------------------------------------
-- Part 5b: WfCtx inversion and extSub-WtSub
------------------------------------------------------------------------

wfCtx-domain : {n : Nat} {G : Ctx n} {A : Expr n} ->
  WfCtx (extend G A) -> HasType G A U
wfCtx-domain (wf-extend htA) = htA

extSub-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  {sigma : Sub h g} {t : Expr h} ->
  WtSub H G sigma -> WfCtx H -> HasType G A U -> HasType H t (substExpr sigma A) ->
  WtSub H (extend G A) (extSub sigma t)
extSub-WtSub {H = H} {A = A} {sigma = sigma} {t = t} ws wfH dA dt fzero =
  S.Eq-transport (\ X -> HasType H t X) (S.Eq-sym (substExpr-wk sigma A t)) dt
extSub-WtSub {H = H} {G = G} {A = A} {sigma = sigma} {t = t} ws wfH dA dt (fsuc i) =
  S.Eq-transport (\ X -> HasType H (sigma i) X) (S.Eq-sym (substExpr-wk sigma (lookup G i) t)) (ws i)

idSub-WtSub : {n : Nat} {G : Ctx n} -> WfCtx G -> WtSub G G idSub
idSub-WtSub {G = G} wfG i =
  S.Eq-transport (\ X -> HasType G (Var i) X) (S.Eq-sym (substExpr-id (lookup G i)))
    (ty-var wfG)

ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB) = mkSigma dA dB
ty-Pi-invert (ty-Pi-Prop dA dB) = mkSigma dA (ty-Prop-U dB)
ty-Pi-invert (ty-Prop-U d) = ty-Pi-invert d
ty-Pi-invert (ty-conv d _ _) = ty-Pi-invert d

typing-Pi-codomain : {n : Nat} {G : Ctx n}
  {A : Expr n} {B : Expr (suc n)} {M : Expr n} ->
  HasType G A U -> HasType G M (Pi A B) ->
  HasType (extend G A) B U
typing-Pi-codomain dA dM = snd (ty-Pi-invert (typing-type dM))

------------------------------------------------------------------------
-- Part 5b: FinMem PropCode-to-UCode conversion
-- FinMem v PropCode is non-empty only for v = Bot or v = PiCode.
-- In both cases FinMem v UCode is also non-empty.
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  FinMem-PropCode-to-UCode : (v : FinEl) -> FinMem v PropCode -> FinMem v UCode
  FinMem-PropCode-to-UCode Bot mem = tt
  FinMem-PropCode-to-UCode (PiCode a f) mem =
    mkSigma (fst mem) (mkSigma (FinMemAllProp-to-FinMemAllU f a (fst (snd mem))) (snd (snd mem)))
  FinMem-PropCode-to-UCode UCode ()
  FinMem-PropCode-to-UCode PropCode ()
  FinMem-PropCode-to-UCode (FunEl _) ()
  FinMem-PropCode-to-UCode (SigmaCode _ _) ()
  FinMem-PropCode-to-UCode (PairCode _ _) ()

  FinMemAllProp-to-FinMemAllU : (f : FinFun) -> (b : FinEl) -> FinMemAllProp f b -> FinMemAllU f b
  FinMemAllProp-to-FinMemAllU nil b tt = tt
  FinMemAllProp-to-FinMemAllU (cons p ps) b mem =
    mkSigma (mkSigma (fst (fst mem)) (FinMem-PropCode-to-UCode (snd p) (snd (fst mem))))
            (FinMemAllProp-to-FinMemAllU ps b (snd mem))

FinMem-PropCode-to-UCode-full : (u : FinEl) -> FinMem u PropCode -> FinMem u UCode
FinMem-PropCode-to-UCode-full = FinMem-PropCode-to-UCode

-- Val2/EqVal2 at PropCode equals Val2/EqVal2 at UCode for all u with FinMem u PropCode.
-- (The only differing case would be SigmaCode, but FinMem (SigmaCode _ _) PropCode = Empty.)
Val2-UCode-to-PropCode : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u : FinEl) -> FinMem u PropCode ->
  Val2 G M A u UCode -> Val2 G M A u PropCode
Val2-UCode-to-PropCode Bot _ v = v
Val2-UCode-to-PropCode (PiCode a' f') _ v = v
Val2-UCode-to-PropCode UCode () _
Val2-UCode-to-PropCode PropCode () _
Val2-UCode-to-PropCode (FunEl _) () _
Val2-UCode-to-PropCode (SigmaCode _ _) () _
Val2-UCode-to-PropCode (PairCode _ _) () _

EqVal2-UCode-to-PropCode : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u : FinEl) -> FinMem u PropCode ->
  EqVal2 G M N A u UCode -> EqVal2 G M N A u PropCode
EqVal2-UCode-to-PropCode Bot _ v = v
EqVal2-UCode-to-PropCode (PiCode a' f') _ v = v
EqVal2-UCode-to-PropCode UCode () _
EqVal2-UCode-to-PropCode PropCode () _
EqVal2-UCode-to-PropCode (FunEl _) () _
EqVal2-UCode-to-PropCode (SigmaCode _ _) () _
EqVal2-UCode-to-PropCode (PairCode _ _) () _

------------------------------------------------------------------------
-- Part 5c: Headred transport (Val2-beta-expand etc.)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  ValTy2-headred-expand : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M' M ->
    ValTy2 G M u -> ValTy2 G M' u
  ValTy2-headred-expand Bot hr tt = tt
  ValTy2-headred-expand UCode hr tt = tt
  ValTy2-headred-expand PropCode hr tt = tt
  ValTy2-headred-expand (FunEl g) hr tt = tt
  ValTy2-headred-expand (PairCode _ _) hr tt = tt
  ValTy2-headred-expand (PiCode b f) hr vt =
    mkSigma (fst vt) (mkSigma (fst (snd vt))
      (mkSigma (mkRed (HeadRed-trans hr (Red-hr (fst (snd (snd vt)))))) (snd (snd (snd vt)))))
  ValTy2-headred-expand (SigmaCode b f) hr vt =
    mkSigma (fst vt) (mkSigma (fst (snd vt))
      (mkSigma (mkRed (HeadRed-trans hr (Red-hr (fst (snd (snd vt)))))) (snd (snd (snd vt)))))

  ValTy2-headred-contract : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M M' ->
    ValTy2 G M u -> ValTy2 G M' u
  ValTy2-headred-contract Bot hr tt = tt
  ValTy2-headred-contract UCode hr tt = tt
  ValTy2-headred-contract PropCode hr tt = tt
  ValTy2-headred-contract (FunEl g) hr tt = tt
  ValTy2-headred-contract (PairCode _ _) hr tt = tt
  ValTy2-headred-contract (PiCode b f) hr vt =
    mkSigma (fst vt) (mkSigma (fst (snd vt))
      (mkSigma (mkRed (HeadRed-strip-Pi hr (Red-hr (fst (snd (snd vt))))))
        (snd (snd (snd vt)))))
  ValTy2-headred-contract (SigmaCode b f) hr vt =
    mkSigma (fst vt) (mkSigma (fst (snd vt))
      (mkSigma (mkRed (HeadRed-strip-Sigma hr (Red-hr (fst (snd (snd vt))))))
        (snd (snd (snd vt)))))

  EqValTy2-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
    EqValTy2 G M1 M2 u -> EqValTy2 G M1' M2' u
  EqValTy2-headred-expand Bot hr1 hr2 tt = tt
  EqValTy2-headred-expand UCode hr1 hr2 tt = tt
  EqValTy2-headred-expand PropCode hr1 hr2 tt = tt
  EqValTy2-headred-expand (FunEl g) hr1 hr2 tt = tt
  EqValTy2-headred-expand (PairCode _ _) hr1 hr2 tt = tt
  EqValTy2-headred-expand (PiCode b f) hr1 hr2 eqvt =
    let vt1  = fst eqvt
        vt2  = fst (snd eqvt)
        core = snd (snd eqvt)
        redM = fst (snd (snd (snd (snd core))))
        redN = fst (snd (snd (snd (snd (snd core)))))
        tail = snd (snd (snd (snd (snd (snd core)))))
    in mkSigma (ValTy2-headred-expand (PiCode b f) hr1 vt1)
         (mkSigma (ValTy2-headred-expand (PiCode b f) hr2 vt2)
           (mkSigma (fst core) (mkSigma (fst (snd core)) (mkSigma (fst (snd (snd core))) (mkSigma (fst (snd (snd (snd core))))
             (mkSigma (mkRed (HeadRed-trans hr1 (Red-hr redM)))
               (mkSigma (mkRed (HeadRed-trans hr2 (Red-hr redN))) tail)))))))
  EqValTy2-headred-expand (SigmaCode b f) hr1 hr2 eqvt =
    let vt1  = fst eqvt
        vt2  = fst (snd eqvt)
        core = snd (snd eqvt)
        redM = fst (snd (snd (snd (snd core))))
        redN = fst (snd (snd (snd (snd (snd core)))))
        tail = snd (snd (snd (snd (snd (snd core)))))
    in mkSigma (ValTy2-headred-expand (SigmaCode b f) hr1 vt1)
         (mkSigma (ValTy2-headred-expand (SigmaCode b f) hr2 vt2)
           (mkSigma (fst core) (mkSigma (fst (snd core)) (mkSigma (fst (snd (snd core))) (mkSigma (fst (snd (snd (snd core))))
             (mkSigma (mkRed (HeadRed-trans hr1 (Red-hr redM)))
               (mkSigma (mkRed (HeadRed-trans hr2 (Red-hr redN))) tail)))))))

  ValPi2-headred-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M' M -> ValPi2 G M T g0 b f -> ValPi2 G M' T g0 b f
  ValPi2-headred-expand g0 b f hr vpiM =
    let A0  = fst vpiM
        B0  = fst (snd vpiM)
        red = fst (snd (snd vpiM))
        cg  = fst (snd (snd (snd vpiM)))
        fmg = fst (snd (snd (snd (snd vpiM))))
        pav = fst (snd (snd (snd (snd (snd vpiM)))))
        pae = snd (snd (snd (snd (snd (snd vpiM)))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
         (mkSigma
           (\ u v sel N htN valN -> Val2-beta-expand v (EvalFun f u) (HeadRed-App hr) (pav u v sel N htN valN))
           (\ u v sel N1 N2 htN1 htN2 cvN eqN -> EqVal2-headred-expand v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr) (pae u v sel N1 N2 htN1 htN2 cvN eqN)))))))

  EqValPi2-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1' M1 -> HeadRed M2' M2 ->
    EqValPi2 G M1 M2 T g0 b f -> EqValPi2 G M1' M2' T g0 b f
  EqValPi2-headred-expand g0 b f hr1 hr2 epi =
    let A0   = fst epi
        B0   = fst (snd epi)
        red  = fst (snd (snd epi))
        cg   = fst (snd (snd (snd epi)))
        fmg  = fst (snd (snd (snd (snd epi))))
        paev = snd (snd (snd (snd (snd epi))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
         (\ u v sel P htP valP ->
           EqVal2-headred-expand v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
             (paev u v sel P htP valP))))))

  ValPi2-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M M' -> ValPi2 G M T g0 b f -> ValPi2 G M' T g0 b f
  ValPi2-headred-contract g0 b f hr vpiM =
    let A0  = fst vpiM
        B0  = fst (snd vpiM)
        red = fst (snd (snd vpiM))
        cg  = fst (snd (snd (snd vpiM)))
        fmg = fst (snd (snd (snd (snd vpiM))))
        pav = fst (snd (snd (snd (snd (snd vpiM)))))
        pae = snd (snd (snd (snd (snd (snd vpiM)))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
         (mkSigma
           (\ u v sel N htN valN -> Val2-headred-contract v (EvalFun f u) (HeadRed-App hr) (pav u v sel N htN valN))
           (\ u v sel N1 N2 htN1 htN2 cvN eqN -> EqVal2-headred-contract v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr) (pae u v sel N1 N2 htN1 htN2 cvN eqN)))))))

  EqValPi2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqValPi2 G M1 M2 T g0 b f -> EqValPi2 G M1' M2' T g0 b f
  EqValPi2-headred-contract g0 b f hr1 hr2 epi =
    let A0   = fst epi
        B0   = fst (snd epi)
        red  = fst (snd (snd epi))
        cg   = fst (snd (snd (snd epi)))
        fmg  = fst (snd (snd (snd (snd epi))))
        paev = snd (snd (snd (snd (snd epi))))
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
         (\ u v sel P htP valP ->
           EqVal2-headred-contract v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
             (paev u v sel P htP valP))))))

  Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M' M ->
    Val2 G M T u a -> Val2 G M' T u a
  Val2-beta-expand u Bot hr tt = tt
  Val2-beta-expand Bot UCode hr tt = tt
  Val2-beta-expand UCode UCode hr tt = tt
  Val2-beta-expand PropCode UCode hr tt = tt
  Val2-beta-expand (FunEl g) UCode hr tt = tt
  Val2-beta-expand (PiCode a' f') UCode hr vt = ValTy2-headred-expand (PiCode a' f') hr vt
  Val2-beta-expand (SigmaCode a' f') UCode hr vt = ValTy2-headred-expand (SigmaCode a' f') hr vt
  Val2-beta-expand (PairCode _ _) UCode hr tt = tt
  Val2-beta-expand (PiCode a' f') PropCode hr vt = ValTy2-headred-expand (PiCode a' f') hr vt
  Val2-beta-expand Bot PropCode hr tt = tt
  Val2-beta-expand UCode PropCode hr tt = tt
  Val2-beta-expand PropCode PropCode hr tt = tt
  Val2-beta-expand (FunEl _) PropCode hr tt = tt
  Val2-beta-expand (SigmaCode _ _) PropCode hr tt = tt
  Val2-beta-expand (PairCode _ _) PropCode hr tt = tt
  Val2-beta-expand u (FunEl h) hr tt = tt
  Val2-beta-expand Bot (PiCode b f) hr tt = tt
  Val2-beta-expand UCode (PiCode b f) hr tt = tt
  Val2-beta-expand PropCode (PiCode b f) hr tt = tt
  Val2-beta-expand (FunEl g) (PiCode b f) hr val =
    mkSigma (fst val) (ValPi2-headred-expand g b f hr (snd val))
  Val2-beta-expand (PiCode a' f') (PiCode b f) hr tt = tt
  Val2-beta-expand (SigmaCode _ _) (PiCode b f) hr tt = tt
  Val2-beta-expand (PairCode _ _) (PiCode b f) hr tt = tt
  Val2-beta-expand Bot (SigmaCode _ _) hr tt = tt
  Val2-beta-expand UCode (SigmaCode _ _) hr tt = tt
  Val2-beta-expand PropCode (SigmaCode _ _) hr tt = tt
  Val2-beta-expand (FunEl _) (SigmaCode _ _) hr tt = tt
  Val2-beta-expand (PiCode _ _) (SigmaCode _ _) hr tt = tt
  Val2-beta-expand (SigmaCode _ _) (SigmaCode _ _) hr tt = tt
  Val2-beta-expand (PairCode u' v') (SigmaCode b0 f0) hr val =
    let A0  = fst val
        B0  = fst (snd val)
        red = fst (snd (snd val))
        v2F = snd (snd (snd val))
        -- Red G T (Sigma A0 B0) U and HeadRed M' M give Red G T (Sigma A0 B0) U unchanged
        -- (Red is on T, not on M, and HeadRed is M' → M, so Fst M' → Fst M)
        v2F' = Val2-beta-expand u' b0 (HeadRed-Fst hr) v2F
    in mkSigma A0 (mkSigma B0 (mkSigma red v2F'))
  Val2-beta-expand Bot (PairCode _ _) hr tt = tt
  Val2-beta-expand UCode (PairCode _ _) hr tt = tt
  Val2-beta-expand PropCode (PairCode _ _) hr tt = tt
  Val2-beta-expand (FunEl _) (PairCode _ _) hr tt = tt
  Val2-beta-expand (PiCode _ _) (PairCode _ _) hr tt = tt
  Val2-beta-expand (SigmaCode _ _) (PairCode _ _) hr tt = tt
  Val2-beta-expand (PairCode _ _) (PairCode _ _) hr tt = tt

  Val2-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M M' ->
    Val2 G M T u a -> Val2 G M' T u a
  Val2-headred-contract u Bot hr tt = tt
  Val2-headred-contract Bot UCode hr tt = tt
  Val2-headred-contract UCode UCode hr tt = tt
  Val2-headred-contract PropCode UCode hr tt = tt
  Val2-headred-contract (FunEl g) UCode hr tt = tt
  Val2-headred-contract (PiCode a' f') UCode hr vt = ValTy2-headred-contract (PiCode a' f') hr vt
  Val2-headred-contract (SigmaCode a' f') UCode hr vt = ValTy2-headred-contract (SigmaCode a' f') hr vt
  Val2-headred-contract (PairCode _ _) UCode hr tt = tt
  Val2-headred-contract (PiCode a' f') PropCode hr vt = ValTy2-headred-contract (PiCode a' f') hr vt
  Val2-headred-contract Bot PropCode hr tt = tt
  Val2-headred-contract UCode PropCode hr tt = tt
  Val2-headred-contract PropCode PropCode hr tt = tt
  Val2-headred-contract (FunEl _) PropCode hr tt = tt
  Val2-headred-contract (SigmaCode _ _) PropCode hr tt = tt
  Val2-headred-contract (PairCode _ _) PropCode hr tt = tt
  Val2-headred-contract u (FunEl h) hr tt = tt
  Val2-headred-contract Bot (PiCode b f) hr tt = tt
  Val2-headred-contract UCode (PiCode b f) hr tt = tt
  Val2-headred-contract PropCode (PiCode b f) hr tt = tt
  Val2-headred-contract (FunEl g) (PiCode b f) hr val =
    mkSigma (fst val) (ValPi2-headred-contract g b f hr (snd val))
  Val2-headred-contract (PiCode a' f') (PiCode b f) hr tt = tt
  Val2-headred-contract (SigmaCode _ _) (PiCode b f) hr tt = tt
  Val2-headred-contract (PairCode _ _) (PiCode b f) hr tt = tt
  Val2-headred-contract Bot (SigmaCode _ _) hr tt = tt
  Val2-headred-contract UCode (SigmaCode _ _) hr tt = tt
  Val2-headred-contract PropCode (SigmaCode _ _) hr tt = tt
  Val2-headred-contract (FunEl _) (SigmaCode _ _) hr tt = tt
  Val2-headred-contract (PiCode _ _) (SigmaCode _ _) hr tt = tt
  Val2-headred-contract (SigmaCode _ _) (SigmaCode _ _) hr tt = tt
  Val2-headred-contract (PairCode u' v') (SigmaCode b0 f0) hr val =
    let A0  = fst val
        B0  = fst (snd val)
        red = fst (snd (snd val))
        v2F = snd (snd (snd val))
        v2F' = Val2-headred-contract u' b0 (HeadRed-Fst hr) v2F
    in mkSigma A0 (mkSigma B0 (mkSigma red v2F'))
  Val2-headred-contract Bot (PairCode _ _) hr tt = tt
  Val2-headred-contract UCode (PairCode _ _) hr tt = tt
  Val2-headred-contract PropCode (PairCode _ _) hr tt = tt
  Val2-headred-contract (FunEl _) (PairCode _ _) hr tt = tt
  Val2-headred-contract (PiCode _ _) (PairCode _ _) hr tt = tt
  Val2-headred-contract (SigmaCode _ _) (PairCode _ _) hr tt = tt
  Val2-headred-contract (PairCode _ _) (PairCode _ _) hr tt = tt

  EqVal2-headred-expand : {n : Nat} {G : Ctx n} {M M' N N' T : Expr n}
    (u a : FinEl) -> HeadRed M' M -> HeadRed N' N ->
    EqVal2 G M N T u a -> EqVal2 G M' N' T u a
  EqVal2-headred-expand u Bot hr1 hr2 tt = tt
  EqVal2-headred-expand Bot UCode hr1 hr2 tt = tt
  EqVal2-headred-expand UCode UCode hr1 hr2 ev = mkSigma tt (mkSigma tt tt)
  EqVal2-headred-expand PropCode UCode hr1 hr2 tt = tt
  EqVal2-headred-expand (FunEl g) UCode hr1 hr2 ev = mkSigma tt (mkSigma tt tt)
  EqVal2-headred-expand (PiCode a' f') UCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-expand (PiCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-expand (PiCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-expand (PiCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-expand (SigmaCode a' f') UCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-expand (SigmaCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-expand (SigmaCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-expand (SigmaCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-expand (PairCode _ _) UCode hr1 hr2 tt = tt
  EqVal2-headred-expand (PiCode a' f') PropCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-expand (PiCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-expand (PiCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-expand (PiCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-expand Bot PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand UCode PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand PropCode PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand (FunEl _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand (PairCode _ _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-expand u (FunEl h) hr1 hr2 tt = tt
  EqVal2-headred-expand Bot (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand UCode (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand PropCode (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand (FunEl g) (PiCode b f) hr1 hr2 ev =
    mkSigma (fst ev)
      (mkSigma (ValPi2-headred-expand g b f hr1 (fst (snd ev)))
        (mkSigma (ValPi2-headred-expand g b f hr2 (fst (snd (snd ev))))
          (EqValPi2-headred-expand g b f hr1 hr2 (snd (snd (snd ev))))))
  EqVal2-headred-expand (PiCode a' f') (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand (PairCode _ _) (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-expand Bot (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand UCode (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand PropCode (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (FunEl _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (PiCode _ _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (PairCode u' v') (SigmaCode b0 f0) hr1 hr2 ev =
    let A0  = fst ev
        B0  = fst (snd ev)
        red = fst (snd (snd ev))
        v2M = fst (snd (snd (snd ev)))
        v2N = fst (snd (snd (snd (snd ev))))
        eq  = snd (snd (snd (snd (snd ev))))
        v2M' = Val2-beta-expand u' b0 (HeadRed-Fst hr1) v2M
        v2N' = Val2-beta-expand u' b0 (HeadRed-Fst hr2) v2N
        eq'  = EqVal2-headred-expand u' b0 (HeadRed-Fst hr1) (HeadRed-Fst hr2) eq
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma v2M' (mkSigma v2N' eq'))))
  EqVal2-headred-expand Bot (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand UCode (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand PropCode (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (FunEl _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (PiCode _ _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (SigmaCode _ _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-expand (PairCode _ _) (PairCode _ _) hr1 hr2 tt = tt

  EqVal2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqVal2 G M1 M2 T u a -> EqVal2 G M1' M2' T u a
  EqVal2-headred-contract u Bot hr1 hr2 tt = tt
  EqVal2-headred-contract Bot UCode hr1 hr2 tt = tt
  EqVal2-headred-contract UCode UCode hr1 hr2 ev = mkSigma tt (mkSigma tt tt)
  EqVal2-headred-contract PropCode UCode hr1 hr2 tt = tt
  EqVal2-headred-contract (FunEl g) UCode hr1 hr2 ev = mkSigma tt (mkSigma tt tt)
  EqVal2-headred-contract (PiCode a' f') UCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-contract (SigmaCode a' f') UCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-contract (SigmaCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-contract (SigmaCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-contract (SigmaCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-contract (PairCode _ _) UCode hr1 hr2 tt = tt
  EqVal2-headred-contract (PiCode a' f') PropCode hr1 hr2 ev =
    mkSigma (ValTy2-headred-contract (PiCode a' f') hr1 (fst ev))
         (mkSigma (ValTy2-headred-contract (PiCode a' f') hr2 (fst (snd ev)))
           (EqValTy2-headred-contract (PiCode a' f') hr1 hr2 (snd (snd ev))))
  EqVal2-headred-contract Bot PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract UCode PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract PropCode PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract (FunEl _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract (PairCode _ _) PropCode hr1 hr2 tt = tt
  EqVal2-headred-contract u (FunEl h) hr1 hr2 tt = tt
  EqVal2-headred-contract Bot (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract UCode (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract PropCode (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract (FunEl g) (PiCode b f) hr1 hr2 ev =
    mkSigma (fst ev)
      (mkSigma (ValPi2-headred-contract g b f hr1 (fst (snd ev)))
        (mkSigma (ValPi2-headred-contract g b f hr2 (fst (snd (snd ev))))
          (EqValPi2-headred-contract g b f hr1 hr2 (snd (snd (snd ev))))))
  EqVal2-headred-contract (PiCode a' f') (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract (PairCode _ _) (PiCode b f) hr1 hr2 tt = tt
  EqVal2-headred-contract Bot (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract UCode (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract PropCode (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (FunEl _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (PiCode _ _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (SigmaCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (PairCode u' v') (SigmaCode b0 f0) hr1 hr2 ev =
    let A0  = fst ev
        B0  = fst (snd ev)
        red = fst (snd (snd ev))
        v2M = fst (snd (snd (snd ev)))
        v2N = fst (snd (snd (snd (snd ev))))
        eq  = snd (snd (snd (snd (snd ev))))
        v2M' = Val2-headred-contract u' b0 (HeadRed-Fst hr1) v2M
        v2N' = Val2-headred-contract u' b0 (HeadRed-Fst hr2) v2N
        eq'  = EqVal2-headred-contract u' b0 (HeadRed-Fst hr1) (HeadRed-Fst hr2) eq
    in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma v2M' (mkSigma v2N' eq'))))
  EqVal2-headred-contract Bot (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract UCode (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract PropCode (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (FunEl _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (PiCode _ _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (SigmaCode _ _) (PairCode _ _) hr1 hr2 tt = tt
  EqVal2-headred-contract (PairCode _ _) (PairCode _ _) hr1 hr2 tt = tt

  EqValTy2-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqValTy2 G M1 M2 u -> EqValTy2 G M1' M2' u
  EqValTy2-headred-contract Bot hr1 hr2 tt = tt
  EqValTy2-headred-contract UCode hr1 hr2 tt = tt
  EqValTy2-headred-contract PropCode hr1 hr2 tt = tt
  EqValTy2-headred-contract (FunEl g) hr1 hr2 tt = tt
  EqValTy2-headred-contract (PairCode _ _) hr1 hr2 tt = tt
  EqValTy2-headred-contract (PiCode b f) hr1 hr2 eqvt =
    let vt1  = fst eqvt
        vt2  = fst (snd eqvt)
        core = snd (snd eqvt)
        redM = fst (snd (snd (snd (snd core))))
        redN = fst (snd (snd (snd (snd (snd core)))))
        tail = snd (snd (snd (snd (snd (snd core)))))
    in mkSigma (ValTy2-headred-contract (PiCode b f) hr1 vt1)
         (mkSigma (ValTy2-headred-contract (PiCode b f) hr2 vt2)
           (mkSigma (fst core) (mkSigma (fst (snd core)) (mkSigma (fst (snd (snd core))) (mkSigma (fst (snd (snd (snd core))))
             (mkSigma (mkRed (HeadRed-strip-Pi hr1 (Red-hr redM)))
               (mkSigma (mkRed (HeadRed-strip-Pi hr2 (Red-hr redN))) tail)))))))
  EqValTy2-headred-contract (SigmaCode b f) hr1 hr2 eqvt =
    let vt1  = fst eqvt
        vt2  = fst (snd eqvt)
        core = snd (snd eqvt)
        redM = fst (snd (snd (snd (snd core))))
        redN = fst (snd (snd (snd (snd (snd core)))))
        tail = snd (snd (snd (snd (snd (snd core)))))
    in mkSigma (ValTy2-headred-contract (SigmaCode b f) hr1 vt1)
         (mkSigma (ValTy2-headred-contract (SigmaCode b f) hr2 vt2)
           (mkSigma (fst core) (mkSigma (fst (snd core)) (mkSigma (fst (snd (snd core))) (mkSigma (fst (snd (snd (snd core))))
             (mkSigma (mkRed (HeadRed-strip-Sigma hr1 (Red-hr redM)))
               (mkSigma (mkRed (HeadRed-strip-Sigma hr2 (Red-hr redN))) tail)))))))

------------------------------------------------------------------------
-- Part 6: Main mutual block
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Main bundled adequacy theorem
  adequacySub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (substExpr sigma M) (substExpr sigma A) u a

  -- Bundled adequacy for conversion
  adequacyEqSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

  -- Two-substitution adequacy
  adequacyConvSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' ->
    WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a

  ----------------------------------------------------------------------
  -- adequacySub2-Prop-U-PiCode: stub for ty-Prop-U at PiCode
  -- TODO: needs full construction of ValTyPi2 from Prop typing
  adequacySub2-Prop-U-PiCode : {h g : Nat} {H : Ctx h} {G : Ctx g} {M : Expr g} ->
    HasType G M Prop ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (a' : FinEl) -> (f' : FinFun) ->
    EvalRel M rho (PiCode a' f') -> FinMem (PiCode a' f') UCode ->
    Val2 H (substExpr sigma M) (substExpr sigma U) (PiCode a' f') UCode
  adequacySub2-Prop-U-PiCode d sigma rho crho vs fits wtsub wfH a' f' hu fm =
    adequacySub2-Prop-U-PiCode-aux d S.refl sigma rho crho vs fits wtsub wfH a' f' hu fm

  -- Auxiliary: takes HasType G M A with proof A ≡ Prop, enabling case split
  adequacySub2-Prop-U-PiCode-aux : {h g : Nat} {H : Ctx h} {G : Ctx g} {M A : Expr g} ->
    HasType G M A -> S.Eq A Prop ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (a' : FinEl) -> (f' : FinFun) ->
    EvalRel M rho (PiCode a' f') -> FinMem (PiCode a' f') UCode ->
    Val2 H (substExpr sigma M) (substExpr sigma U) (PiCode a' f') UCode
  -- ty-Pi-Prop: M = Pi A B, direct via adequacySub2-Pi
  adequacySub2-Prop-U-PiCode-aux (ty-Pi-Prop d1 d2) S.refl sigma rho crho vs fits wtsub wfH a' f' hu fm =
    adequacySub2-Pi d1 (ty-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu (mkSigma tt (LeCode-refl UCode tt)) fm
  -- Remaining cases (ty-var, ty-conv, ty-App, ty-Fst, ty-Snd):
  -- These require ValTyPi2 H sM a' f' = Red H sM (Pi A B) U × HasType × semantic data.
  -- Val2 at (PiCode a' f', UCode) is ValTyPi2, independent of the type expression.
  -- But ValidSub2 only provides Val2 at PropCode, which is Top.
  -- Solution requires either strengthened ValidSub2 or canonical forms lemma.
  -- M : Prop and evaluates to PiCode a' f'. Typed data gives u' ≥ PiCode a' f'
  -- with FinMem u' a_t and a_t ≤ PropCode. For a_t = Bot: u' = Bot contradiction.
  -- For a_t = PropCode: FinMem (PiCode _) PropCode is non-empty → need proof irrelevance.
  adequacySub2-Prop-U-PiCode-aux d eq sigma rho crho vs fits wtsub wfH a' f' hu fm =
    let d' = S.Eq-transport (HasType _ _) eq d
    in adequacySub2-Prop-U-PiCode-aux2 d' sigma rho crho vs fits wtsub wfH a' f' fm
         (theorem1 d' rho fits (PiCode a' f') hu)
    where
      adequacySub2-Prop-U-PiCode-aux2 : {h' g' : Nat} {H' : Ctx h'} {G' : Ctx g'} {M' : Expr g'} ->
        HasType G' M' Prop ->
        (sigma' : Sub h' g') -> (rho' : EnvApprox g') ->
        CoherentEnv rho' -> ValidSub2 H' G' sigma' rho' -> Fits G' rho' ->
        WtSub H' G' sigma' -> WfCtx H' ->
        (a0 : FinEl) -> (f0 : FinFun) ->
        FinMem (PiCode a0 f0) UCode ->
        Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
          Pair (LeCode (PiCode a0 f0) u')
          (Pair (EvalRel M' rho' u')
          (Pair (FinMem u' a_t) (EvalRel Prop rho' a_t))))) ->
        Val2 H' (substExpr sigma' M') (substExpr sigma' U) (PiCode a0 f0) UCode
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma Bot (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma UCode (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      adequacySub2-Prop-U-PiCode-aux2 {H' = H'} {M' = M'} d' sigma' rho' crho' vs' fits' wtsub' wfH' a0 f0 fm0
        (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
          let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
              val_bg = adequacySub2 d' sigma' rho' crho' vs' fits' wtsub' wfH'
                         (PiCode b g) hu' PropCode (mkSigma tt tt) fmBG
          in restrictVal2 H' (substExpr sigma' M') U (PiCode b g) (PiCode a0 f0) UCode
               le fm0 fmBG_U val_bg

  ----------------------------------------------------------------------
  -- adequacySub2: ty-var
  ----------------------------------------------------------------------

  adequacySub2 (ty-var {G = G} {i = i} _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    vs i u (fst hu) (snd hu) a evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-U
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-U _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    tyU2-helper u a (snd hu) (snd evA) fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Prop
  -- EvalRel Prop rho u means u ≤ PropCode.
  -- EvalRel U rho a means a ≤ UCode.
  -- FinMem u a with u ≤ PropCode and a ≤ UCode.
  -- Val2 H Prop U u a: since substExpr sigma Prop = Prop,
  -- this is the same structure as ty-U but with PropCode.
  -- PropCode ≤ UCode is Empty, so u can only be Bot.
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Prop _) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacySub2-Prop u a (snd hu) (snd evA) fm
    where
      adequacySub2-Prop : (u a : FinEl) -> LeCode u PropCode -> LeCode a UCode ->
        FinMem u a -> Val2 H (substExpr sigma Prop) (substExpr sigma U) u a
      adequacySub2-Prop Bot a _ _ _ = Val2-Bot a
      adequacySub2-Prop UCode _ () _ _
      adequacySub2-Prop PropCode Bot _ _ ()
      adequacySub2-Prop PropCode UCode _ _ _ = tt
      adequacySub2-Prop PropCode PropCode _ () _
      adequacySub2-Prop PropCode (FunEl _) _ () _
      adequacySub2-Prop PropCode (PiCode _ _) _ () _
      adequacySub2-Prop PropCode (SigmaCode _ _) _ () _
      adequacySub2-Prop PropCode (PairCode _ _) _ () _
      adequacySub2-Prop (FunEl _) _ () _ _
      adequacySub2-Prop (PiCode _ _) _ () _ _
      adequacySub2-Prop (SigmaCode _ _) _ () _ _
      adequacySub2-Prop (PairCode _ _) _ () _ _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Prop-U
  -- If HasType G M Prop then HasType G M U.
  -- EvalRel M rho u, EvalRel U rho a (so a ≤ UCode).
  -- Need Val2 H sM U u a. Since M also has type Prop,
  -- EvalRel Prop rho a' gives a' ≤ PropCode. But we evaluate at U, not Prop.
  -- We just delegate to adequacySub2 on the underlying d.
  -- But d : HasType G M Prop, so type is Prop, not U.
  -- We need: Val2 H sM U u a from Val2 H sM Prop u a'.
  -- Actually: ty-Prop-U means M : Prop implies M : U.
  -- The type of M is U (the conclusion), so we evaluate at type U.
  -- But the premise is M : Prop.
  -- Since EvalRel Prop rho a' means a' ≤ PropCode,
  -- and Val2 at PropCode = Top, the IH gives tt.
  -- We need Val2 at (u, a) where a comes from U.
  -- This is the same as ty-U essentially - u ≤ UCode (from M : Prop, u ≤ PropCode ≤ ... no).
  -- Actually u comes from EvalRel M rho u, not from the type.
  -- For ty-Prop-U, the evaluation of M at rho gives u.
  -- The type is U, so a evaluates from U, meaning a ≤ UCode.
  -- We can use the IH at type Prop: adequacySub2 d sigma ... u hu PropCode evProp fm'
  -- where evProp : EvalRel Prop rho PropCode.
  -- But FinMem u PropCode may fail.
  -- Alternatively: ty-Prop-U behaves like ty-conv from Prop to U.
  -- Let's handle it as a conv case.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH Bot hu UCode evA fm =
    tt
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
    tt
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm =
    tt
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA ()
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu UCode evA fm =
    adequacySub2-Prop-U-PiCode d sigma rho crho vs fits wtsub wfH a' f' hu fm
  adequacySub2 {H = H} (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (SigmaCode a' f') hu UCode evA fm =
    let typed = theorem1 d rho fits (SigmaCode a' f') hu
        u'   = fst typed
        a''  = fst (snd typed)
        le   = fst (snd (snd typed))
        fm'  = fst (snd (snd (snd (snd typed))))
        evP  = snd (snd (snd (snd (snd typed))))
    in SigmaCode-Prop-absurd a'' u' le fm' (snd evP)
    where
      SigmaCode-Prop-absurd : (a'' u' : FinEl) -> LeCode (SigmaCode a' f') u' ->
        FinMem u' a'' -> LeCode a'' PropCode -> _
      SigmaCode-Prop-absurd Bot u' le fm' _ =
        let eq = FinMem-Prop-Bot u' Bot fm' tt
        in absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode a' f') x) eq le)
      SigmaCode-Prop-absurd PropCode (SigmaCode _ _) le () _
      SigmaCode-Prop-absurd UCode _ _ _ ()
      SigmaCode-Prop-absurd (FunEl _) _ _ _ ()
      SigmaCode-Prop-absurd (PiCode _ _) _ _ _ ()
      SigmaCode-Prop-absurd (SigmaCode _ _) _ _ _ ()
      SigmaCode-Prop-absurd (PairCode _ _) _ _ _ ()
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA ()
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (FunEl _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) (mkSigma _ ()) fm
  adequacySub2 (ty-Prop-U d) sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma _ ()) fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-conv (extended with SigmaCode/PairCode/PropCode)
  ----------------------------------------------------------------------

  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in Val2-EqValTy2-fwd u UCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
    in adequacySub2 d1 sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA' fm
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in Val2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl g) hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a'' f'') hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode a'' f'') hu (SigmaCode b' f') evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (SigmaCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b' f') evA' fm
        aU    = FinMem-a-in-U (PairCode u' v') (SigmaCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in Val2-EqValTy2-fwd (PairCode u' v') (SigmaCode b' f') (EvalRel-coh A rho (SigmaCode b' f') evA') eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH Bot hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH UCode hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH PropCode hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (FunEl g) hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PiCode a'' f'') hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (SigmaCode a'' f'') hu (PairCode _ _) evA fm = tt
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  -- adequacySub2: ty-Pi (same as original)
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu UCode evA fm =
    adequacySub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (FunEl _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PiCode _ _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu PropCode evA fm =
    adequacySub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu
      (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode b f) fm)
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (SigmaCode _ _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PairCode _ _) evA ()

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Pi-Prop
  -- Pi A B : Prop, so type is Prop. EvalRel Prop rho a means a ≤ PropCode.
  -- Val2 at PropCode = Top, so return tt.
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Pi-Prop d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    -- a ≤ PropCode. Val2 H (Pi sA sB) Prop u a.
    -- For a = Bot: tt. For a = PropCode: Val2 at PropCode = Top = tt.
    -- Other values of a are impossible (a ≤ PropCode).
    adequacySub2-at-Prop u a hu (snd evA) fm
    where
      adequacySub2-at-Prop : (u a : FinEl) -> EvalRel (Pi _ _) rho u -> LeCode a PropCode -> FinMem u a -> Val2 H (Pi (substExpr sigma _) (substExpr (liftSub sigma) _)) Prop u a
      adequacySub2-at-Prop u Bot _ _ fm = tt
      adequacySub2-at-Prop u UCode _ () _
      adequacySub2-at-Prop (PiCode a' f') PropCode hu' _ fm =
        adequacySub2-Pi d1 (ty-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu'
          (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode a' f') fm)
      adequacySub2-at-Prop Bot PropCode _ _ fm = tt
      adequacySub2-at-Prop UCode PropCode _ _ ()
      adequacySub2-at-Prop PropCode PropCode _ _ ()
      adequacySub2-at-Prop (FunEl _) PropCode _ _ ()
      adequacySub2-at-Prop (SigmaCode _ _) PropCode _ _ ()
      adequacySub2-at-Prop (PairCode _ _) PropCode _ _ ()
      adequacySub2-at-Prop u (FunEl _) _ () _
      adequacySub2-at-Prop u (PiCode _ _) _ () _
      adequacySub2-at-Prop u (SigmaCode _ _) _ () _
      adequacySub2-at-Prop u (PairCode _ _) _ () _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Sigma
  -- Mirrors ty-Pi: SigmaCode b f at UCode
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode _ _) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu UCode evA fm =
    adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (FunEl _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PiCode _ _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu PropCode evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (SigmaCode _ _) evA ()
  adequacySub2 {H = H} (ty-Sigma {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PairCode _ _) evA ()

  ----------------------------------------------------------------------
  -- adequacySub2: ty-MkPair
  -- MkPair M N : Sigma A B. MkPair evaluates to PairCode u v or Bot.
  -- Val2 at (PairCode, SigmaCode) = Top, and Val2 at (Bot, _) = Top.
  -- So this case is always tt.
  ----------------------------------------------------------------------

  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH PropCode () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (FunEl _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) () a evA fm
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu Bot evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu UCode evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu PropCode evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (FunEl _) evA fm = tt
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PiCode _ _) evA fm = tt
  adequacySub2 {H = H} (ty-MkPair {A = A} {B = B} {M = M0} {N = N0} d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b0 f0) evA fm =
    -- hu : EvalRel (MkPair M0 N0) rho (PairCode u' v') = Pair Coh (Pair (EvalRel M0 rho u') (EvalRel N0 rho v'))
    -- Need: ValPair2 H (MkPair sM sN) (Sigma sA sB) u' v' b0 f0
    --   = Σ A₀ B₀. Σ (Red H (Sigma sA sB) (Sigma A₀ B₀) U). Val2 H (Fst (MkPair sM sN)) A₀ u' b0
    -- Red is reflexive: A₀ = sA, B₀ = sB
    -- Val2 H (Fst (MkPair sM sN)) sA u' b0 comes from Val2 H sM sA u' b0 via beta-expand
    let sA  = substExpr sigma A
        sB  = substExpr (liftSub sigma) B
        sM  = substExpr sigma M0
        sN  = substExpr sigma N0
        evM = fst (snd hu)
        -- Get EvalRel A rho b0 from evA : EvalRel (SigmaE A B) rho (SigmaCode b0 f0)
        evA_b0 = fst (snd evA)
        -- FinMem u' b0 from FinMem (PairCode u' v') (SigmaCode b0 f0)
        fm_u'_b0 = fst (fst fm)
        -- Val2 for M at (u', b0)
        val_M = adequacySub2 d3 sigma rho crho vs fits wtsub wfH u' evM b0 evA_b0 fm_u'_b0
        -- Beta-expand: Fst (MkPair sM sN) →* sM, so expand Val2 from sM to Fst (MkPair sM sN)
        hr-beta : HeadRed (Fst (MkPair sM sN)) sM
        hr-beta = headred-step (headred-beta-fst {M = sM} {N = sN}) headred-refl
        val_fst = Val2-beta-expand u' b0 hr-beta val_M
    in mkSigma sA (mkSigma sB (mkSigma (mkRed headred-refl) val_fst))
  adequacySub2 (ty-MkPair d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Fst
  -- Fst M : A. Val2 H (Fst sM) sA u a.
  -- u comes from EvalRel (Fst M) rho u.
  -- a comes from EvalRel A rho a.
  -- Since A : U, a is a type code.
  -- The key insight: for most (u,a) pairs, Val2 is Top.
  -- The non-trivial cases are same as ty-App.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    {!!} -- TODO: ty-Fst at (PiCode, PropCode) — needs Val2 at (PiCode, PropCode) = ValTyPi2
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b0 f0) evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b0 f0) evA fm
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- ty-Fst at UCode: Val2 H (Fst sM) sA u UCode. Trivial for PropCode/PairCode.
  -- Hard cases (FunEl/PiCode/SigmaCode/UCode) need Red evidence for Fst M.
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm = tt
  adequacySub2 (ty-Fst dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm = tt
  adequacySub2 (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  adequacySub2 {H = H} (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (PiCode a' f') hu UCode evA fm
  adequacySub2 {H = H} (ty-Fst {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode a' f') hu UCode evA fm =
    adequacySub2-Fst-from-ValPair2 dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode a' f') hu UCode evA fm
  -- Actually this is getting too complex. Let me use a simpler approach.
  -- For ty-Fst at (u, PiCode b f): Val2 = Pair ValTyPi2 ValPi2 or Top depending on u.
  -- This requires the full App-like machinery. Since this is an IN PROGRESS file,
  -- let me use the fact that for the specific cases we can delegate.
  adequacySub2 (ty-Fst {A = A} dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PiCode b f) evA fm =
    let evA' = theorem1 (ty-Fst dA dB dM) rho fits u hu
    in adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH u hu b f evA fm evA'

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Snd (mirrors ty-Fst)
  -- Snd M : subst1 B (Fst M). Similar structure.
  -- For most (u,a) combinations, Val2 = Top.
  ----------------------------------------------------------------------

  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    {!!} -- TODO: ty-Snd at (PiCode, PropCode) — needs Val2 at (PiCode, PropCode) = ValTyPi2
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- ty-Snd at UCode: Val2 H (Snd sM) (subst1 sB (Fst sM)) u UCode. Trivial for PropCode/PairCode.
  -- Hard cases (FunEl/PiCode/SigmaCode/UCode) need Red evidence for Snd M.
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm = tt
  adequacySub2 (ty-Snd dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm = tt
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm = {!!}
  adequacySub2 (ty-Snd {A = A} {B = B} {M = M} dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm = {!!}
  adequacySub2 (ty-Snd {A = A} dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PiCode b f) evA fm =
    let evA' = theorem1 (ty-Snd dA dB dM) rho fits u hu
    in adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH u hu b f evA fm evA'

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Lam (same as original, extended absurd cases)
  ----------------------------------------------------------------------

  adequacySub2 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH UCode () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (PiCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH PropCode () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (PairCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu Bot evA fm = tt
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu UCode () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (FunEl h) () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu PropCode () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (SigmaCode _ _) () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits wtsub wfH (FunEl g) hu (PairCode _ _) () fm
  adequacySub2 {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3)
    sigma rho crho vs fits wtsub wfH (FunEl g) hu (PiCode b f0) evA fm =
    adequacySub2-Lam d1 d2 d3 sigma rho crho vs fits wtsub wfH g hu b f0 evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-App (same as original, extended absurd cases)
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH Bot hu ac evAc fm =
    Val2-Bot ac
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH UCode ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode tt ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl g') (EvalRel-coh (App f' a) rho (FunEl g') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b0' f0') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0' f0') (EvalRel-coh (App f' a) rho (PiCode b0' f0') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b0' f0') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode b0' f0') (EvalRel-coh (App f' a) rho (SigmaCode b0' f0') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH PropCode ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode (EvalRel-coh (App f' a) rho PropCode ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits wtsub wfH (PairCode u' v') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode u' v') (EvalRel-coh (App f' a) rho (PairCode u' v') ev) ev ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-refl
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-refl d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 d sigma rho crho vs fits wtsub wfH u hu a evA fm)

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-sym
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN  = convSound-inv d rho fits u hu
        cu'  = FinMem-Coherent u a fm
        ca   = EvalRel-coh Asrc rho a evA
        eq   = adequacyEqSub2 d sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-sym u a cu' ca eq

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-trans
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let huN  = convSound d1 rho fits u hu
        cu   = FinMem-Coherent u a fm
        ca   = EvalRel-coh A rho a evA
        eq1  = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu a evA fm
        eq2  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH u huN a evA fm
    in EqVal2-trans u a cu ca eq1 eq2

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-conv (extended with SigmaCode/PairCode/PropCode)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu UCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u UCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u UCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (FunEl g) evA fm = tt
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
    in adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA' fm
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH u hu (PiCode b' f') evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-beta {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4) sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
    adequacyEqSub2-beta d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u hu ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Prop
  -- Conv at type Prop. Val2 at PropCode = Top.
  -- a evaluates from Prop, so a ≤ PropCode.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Prop {M = M} {N = N} {A = A} dP dM dN) sigma rho crho vs fits wtsub wfH u0 hu a evA fm =
    adequacyEqSub2-at-Prop u0 a hu evA fm
    where
      -- A : Prop. If a = UCode, derive absurdity from theorem1 dP.
      ucode-absurd : (u0' : FinEl) -> EvalRel A rho UCode -> FinMem u0' UCode ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u0' UCode
      ucode-absurd u0' evA_U fm0 =
        let typed = theorem1 dP rho fits UCode evA_U
            u' = fst typed
            a_t = fst (snd typed)
            le_uc_u' = fst (snd (snd typed))
            fm_u'_at = fst (snd (snd (snd (snd typed))))
            evP = snd (snd (snd (snd (snd typed))))
        in ucode-split a_t u' le_uc_u' fm_u'_at (snd evP)
        where
          ucode-split : (a_t u' : FinEl) -> LeCode UCode u' ->
            FinMem u' a_t -> LeCode a_t PropCode -> _
          ucode-split Bot u' le fm_u' _ =
            let eq = FinMem-Prop-Bot u' Bot fm_u' tt
            in absurdEl (S.Eq-transport (\ x -> LeCode UCode x) eq le)
          ucode-split PropCode UCode le () _
          ucode-split UCode _ _ _ ()
          ucode-split (FunEl _) _ _ _ ()
          ucode-split (PiCode _ _) _ _ _ ()
          ucode-split (SigmaCode _ _) _ _ _ ()
          ucode-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-Prop : (u0' a' : FinEl) -> EvalRel M rho u0' -> EvalRel A rho a' -> FinMem u0' a' ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u0' a'
      adequacyEqSub2-at-Prop u0' Bot _ _ fm0 = tt
      adequacyEqSub2-at-Prop u0' UCode _ evA_U fm0 = ucode-absurd u0' evA_U fm0
      adequacyEqSub2-at-Prop (PiCode a0' f0') PropCode hu0 evA_P fm0 =
        let mkSigma u' (mkSigma a1 (mkSigma le_u (mkSigma hu' (mkSigma fm1 evA1)))) = theorem1 dM rho fits (PiCode a0' f0') hu0
            mkSigma a2 (mkSigma b (mkSigma le_a (mkSigma evA2 (mkSigma fm2 evProp)))) = theorem1 dP rho fits a1 evA1
            eq = LeCode-Bot-eq (PiCode a0' f0') u' le_u (conv-Prop-chain u' a1 a2 b fm1 le_a fm2 (snd evProp))
        in S.Eq-transport (\ x -> EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) x PropCode) (S.Eq-sym eq) (EqVal2-Bot PropCode)
      adequacyEqSub2-at-Prop Bot PropCode _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode PropCode _ _ ()
      adequacyEqSub2-at-Prop PropCode PropCode _ _ ()
      adequacyEqSub2-at-Prop (FunEl _) PropCode _ _ ()
      adequacyEqSub2-at-Prop (SigmaCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop (PairCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop u0' (FunEl _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop Bot (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop PropCode (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (FunEl g0) (PiCode b0 f0) _ evA_pi fm0 =
        -- FunEl at PiCode at Prop is absurd: FinMem-Prop-Bot-FunEl
        let typed = theorem1 dP rho fits (PiCode b0 f0) evA_pi
            u'    = fst typed
            a_t   = fst (snd typed)
            le'   = fst (snd (snd typed))
            fm'   = fst (snd (snd (snd (snd typed))))
            evP   = snd (snd (snd (snd (snd typed))))
            piU   = snd (snd fm0)  -- FinMem (PiCode b0 f0) UCode
        in funel-pi-split a_t u' le' fm' (snd evP) piU
        where
          funel-pi-split : (a_t u' : FinEl) -> LeCode (PiCode b0 f0) u' ->
            FinMem u' a_t -> LeCode a_t PropCode ->
            FinMem (PiCode b0 f0) UCode -> _
          funel-pi-split Bot u' le' fm' _ piU =
            let eq = FinMem-Prop-Bot u' Bot fm' tt
            in absurdEl (S.Eq-transport (\ x -> LeCode (PiCode b0 f0) x) eq le')
          funel-pi-split PropCode u' le' fm' _ piU =
            let piP = FinMem-U-to-PropCode (PiCode b0 f0) u' piU le' fm'
                eq  = FinMem-Prop-Bot-FunEl g0 b0 f0 fm0 piP
            in absurdEl (S.Eq-transport NotBot eq tt)
          funel-pi-split UCode _ _ _ ()
          funel-pi-split (FunEl _) _ _ _ ()
          funel-pi-split (PiCode _ _) _ _ _ ()
          funel-pi-split (SigmaCode _ _) _ _ _ ()
          funel-pi-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-Prop (PiCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (SigmaCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PairCode _ _) (PiCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop Bot (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop UCode (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop PropCode (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (FunEl _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PiCode _ _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (SigmaCode _ _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop (PairCode _ _) (SigmaCode _ _) _ _ fm0 = tt
      adequacyEqSub2-at-Prop u0' (PairCode _ _) _ _ fm0 = tt

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Prop-U
  -- ConvTm G M N Prop implies ConvTm G M N U.
  -- Type is U. Same structure as conv-conv from Prop to U.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-Prop-U d) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu a evA fm
    where
      adequacyEqSub2-at-U-from-Prop : {h g : Nat} {H : Ctx h} {G : Ctx g} {M N : Expr g} ->
        ConvTm G M N Prop ->
        (sigma : Sub h g) -> (rho : EnvApprox g) ->
        CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
        WtSub H G sigma -> WfCtx H ->
        (u : FinEl) -> EvalRel M rho u ->
        (a : FinEl) -> EvalRel U rho a -> FinMem u a ->
        EqVal2 H (substExpr sigma M) (substExpr sigma N) U u a
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH Bot hu UCode evA fm = tt
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm = tt
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
      -- M : Prop → non-Bot u leads to absurdity via theorem1.
      -- UCode: u' ≥ UCode, FinMem UCode PropCode = Empty → absurd.
      -- FunEl: u' ≥ FunEl, FinMem (FunEl _) PropCode = Empty → absurd.
      -- SigmaCode: u' ≥ SigmaCode, FinMem (SigmaCode _) PropCode = Empty → absurd.
      -- PiCode: u' ≥ PiCode, FinMem (PiCode _) PropCode non-empty → hard case.
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits UCode hu
        in ucode-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          ucode-split : (a_t u' : FinEl) -> LeCode UCode u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          ucode-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode UCode x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          ucode-split PropCode UCode le () _
          ucode-split UCode _ _ _ ()
          ucode-split (FunEl _) _ _ _ ()
          ucode-split (PiCode _ _) _ _ _ ()
          ucode-split (SigmaCode _ _) _ _ _ ()
          ucode-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (FunEl g0) hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits (FunEl g0) hu
        in funel-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          funel-split : (a_t u' : FinEl) -> LeCode (FunEl g0) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          funel-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode (FunEl g0) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          funel-split PropCode (FunEl _) le () _
          funel-split UCode _ _ _ ()
          funel-split (FunEl _) _ _ _ ()
          funel-split (PiCode _ _) _ _ _ ()
          funel-split (SigmaCode _ _) _ _ _ ()
          funel-split (PairCode _ _) _ _ _ ()
      -- PiCode: u' ≥ PiCode, a_t = PropCode → FinMem (PiCode _) PropCode non-empty → hard
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (PiCode a0 f0) hu UCode evA fm =
        adequacyEqSub2-Prop-U-PiCode-aux' d sigma rho crho vs fits wtsub wfH a0 f0 fm
          (theorem1 (fst (typing-ConvTm d)) rho fits (PiCode a0 f0) hu)
        where
          adequacyEqSub2-Prop-U-PiCode-aux' :
            {h' g' : Nat} {H' : Ctx h'} {G' : Ctx g'} {M' N' : Expr g'} ->
            ConvTm G' M' N' Prop ->
            (sigma' : Sub h' g') -> (rho' : EnvApprox g') ->
            CoherentEnv rho' -> ValidSub2 H' G' sigma' rho' -> Fits G' rho' ->
            WtSub H' G' sigma' -> WfCtx H' ->
            (a0' : FinEl) -> (f0' : FinFun) ->
            FinMem (PiCode a0' f0') UCode ->
            Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
              Pair (LeCode (PiCode a0' f0') u')
              (Pair (EvalRel M' rho' u')
              (Pair (FinMem u' a_t) (EvalRel Prop rho' a_t))))) ->
            EqVal2 H' (substExpr sigma' M') (substExpr sigma' N') U (PiCode a0' f0') UCode
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma Bot (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma UCode (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma PropCode (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
          adequacyEqSub2-Prop-U-PiCode-aux' {H' = H'} {M' = M'} {N' = N'} d' sigma' rho' crho' vs' fits' wtsub' wfH' a0' f0' fm0
            (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
              let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
                  eq_bg = adequacyEqSub2 d' sigma' rho' crho' vs' fits' wtsub' wfH'
                            (PiCode b g) hu' PropCode (mkSigma tt tt) fmBG
              in restrictEqVal2 H' (substExpr sigma' M') (substExpr sigma' N') U
                   (PiCode b g) (PiCode a0' f0') UCode le fm0 fmBG_U eq_bg
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH (SigmaCode a0 f0) hu UCode evA fm =
        let htM = fst (typing-ConvTm d)
            typed = theorem1 htM rho fits (SigmaCode a0 f0) hu
        in sigma-split (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
        where
          sigma-split : (a_t u' : FinEl) -> LeCode (SigmaCode a0 f0) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
          sigma-split Bot u' le fm_u' _ =
            absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode a0 f0) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
          sigma-split PropCode (SigmaCode _ _) le () _
          sigma-split UCode _ _ _ ()
          sigma-split (FunEl _) _ _ _ ()
          sigma-split (PiCode _ _) _ _ _ ()
          sigma-split (SigmaCode _ _) _ _ _ ()
          sigma-split (PairCode _ _) _ _ _ ()
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (FunEl _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu PropCode (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
      adequacyEqSub2-at-U-from-Prop d sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) (mkSigma _ ()) fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Pi-Prop
  -- ConvTm at Prop type. Val2 at PropCode = Top.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Pi-Prop d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-at-Prop-gen u a hu (snd evA) fm
    where
      adequacyEqSub2-at-Prop-gen : (u a : FinEl) -> EvalRel (Pi _ _) rho u -> LeCode a PropCode -> FinMem u a ->
        EqVal2 H (Pi (substExpr sigma _) (substExpr (liftSub sigma) _))
                 (Pi (substExpr sigma _) (substExpr (liftSub sigma) _)) Prop u a
      adequacyEqSub2-at-Prop-gen u Bot _ _ fm = tt
      adequacyEqSub2-at-Prop-gen u UCode _ () _
      adequacyEqSub2-at-Prop-gen (PiCode a' f') PropCode hu' _ fm =
        EqVal2-UCode-to-PropCode (PiCode a' f') fm
          (adequacyEqSub2-Pi d1 (conv-Prop-U d2) sigma rho crho vs fits wtsub wfH a' f' hu'
            (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode a' f') fm))
      adequacyEqSub2-at-Prop-gen Bot PropCode _ _ fm = tt
      adequacyEqSub2-at-Prop-gen UCode PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen PropCode PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (FunEl _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (SigmaCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen (PairCode _ _) PropCode _ _ ()
      adequacyEqSub2-at-Prop-gen u (FunEl _) _ () _
      adequacyEqSub2-at-Prop-gen u (PiCode _ _) _ () _
      adequacyEqSub2-at-Prop-gen u (SigmaCode _ _) _ () _
      adequacyEqSub2-at-Prop-gen u (PairCode _ _) _ () _

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Pi (same as original, extended absurd)
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu Bot evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (FunEl _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PiCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu PropCode evA fm =
    EqVal2-UCode-to-PropCode (PiCode b f) fm
      (adequacyEqSub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu
        (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode b f) fm))
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (SigmaCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu (PairCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (PiCode b f)
    hu UCode evA fm =
    adequacyEqSub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Sigma
  -- Mirrors conv-Pi. ConvTm G (Sigma A B) (Sigma A' B') U.
  -- Val2/EqVal2 at SigmaCode = Top for most u.
  -- At (SigmaCode b f, UCode): need ValTySigma2 etc.
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Sigma {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH UCode ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (FunEl g) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH PropCode ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (PiCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (PairCode _ _) ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu Bot evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (FunEl _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PiCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu PropCode evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (SigmaCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu (PairCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Sigma {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits wtsub wfH (SigmaCode b f)
    hu UCode evA fm =
    adequacyEqSub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta-fst
  -- Fst(MkPair M N) = M. Type A.
  -- Val2 approach: get Val2 for MkPair M N at Sigma type (= Top at PairCode,SigmaCode).
  -- Instead: adequacySub2 on M : A gives Val2, then headred-expand.
  ----------------------------------------------------------------------

  -- conv-beta-fst: Fst(MkPair M N) = M : A. Use convSound to get EvalRel M from EvalRel (Fst(MkPair M N)).
  adequacyEqSub2 (conv-beta-fst {M = M} {N = N} dA dB dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let evM = convSound (conv-beta-fst dA dB dM dN) rho fits u hu
        val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH u evM a evA fm
        eqval_diag = Val2-to-EqVal2 u a val_M
    in EqVal2-headred-expand u a (headred-step headred-beta-fst headred-refl) headred-refl eqval_diag

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta-snd
  -- Snd(MkPair M N) = N. Type subst1 B M.
  ----------------------------------------------------------------------

  -- conv-beta-snd: Snd(MkPair M N) = N : B[M]. Use convSound to get EvalRel N from EvalRel (Snd(MkPair M N)).
  adequacyEqSub2 (conv-beta-snd {M = M} {N = N} dA dB dM dN) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    let evN = convSound (conv-beta-snd dA dB dM dN) rho fits u hu
        val_N = adequacySub2 dN sigma rho crho vs fits wtsub wfH u evN a evA fm
        eqval_diag = Val2-to-EqVal2 u a val_N
    in EqVal2-headred-expand u a (headred-step headred-beta-snd headred-refl) headred-refl eqval_diag

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-pair-eta
  -- MkPair(Fst M)(Snd M) = M : Sigma A B.
  -- Type is Sigma A B, so a = SigmaCode or Bot.
  -- Val2/EqVal2 at SigmaCode = Top. So return tt.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-pair-eta dA dB dM) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm = {!!}

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-MkPair-fst, conv-MkPair-snd
  -- Congruence for MkPair. Type is Sigma A B.
  -- EqVal2 at SigmaCode = Top.
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-fst dA dB dMM' dN) sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm = {!!}

  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (PiCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode b f) evA fm = tt
  adequacyEqSub2 (conv-MkPair-snd dA dB dM dNN') sigma rho crho vs fits wtsub wfH (PairCode u' v') hu (SigmaCode b f) evA fm = {!!}

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Fst
  -- Fst M = Fst M' : A. Standard congruence.
  ----------------------------------------------------------------------

  -- conv-Fst: Fst M = Fst M' : A. Type is A : U. Most (u,a) trivial.
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    {!!} -- TODO: conv-Fst at (PiCode, PropCode) — same difficulty as ty-Fst
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- conv-Fst at UCode: requires ValTy2/EqValTy2 for Fst M, Fst M'
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  -- conv-Fst at (FunEl, UCode): ValTy2/EqValTy2 at FunEl = Top
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm =
    mkSigma tt (mkSigma tt tt)
  -- conv-Fst at (PiCode/SigmaCode, UCode): hard, need ValTyPi2/ValTySigma2 for Fst M
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm = {!!}
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm = {!!}
  -- conv-Fst at PiCode: only non-trivial when u = FunEl
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  -- conv-Fst at (FunEl, PiCode): hard, need full Pi semantics for Fst M
  adequacyEqSub2 (conv-Fst dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (PiCode _ _) evA fm = {!!}

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Snd
  -- Snd M = Snd M' : subst1 B (Fst M). Similar to conv-Fst.
  ----------------------------------------------------------------------

  -- conv-Snd: Snd M = Snd M' : subst1 B (Fst M). Type is subst1 B (Fst M) : U. Most (u,a) trivial.
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode a' f') hu PropCode evA fm =
    {!!} -- TODO: conv-Snd at (PiCode, PropCode) — same difficulty as ty-Snd
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu PropCode evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu PropCode evA ()
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (FunEl _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) evA fm = tt
  -- conv-Snd at UCode: requires ValTy2/EqValTy2 for Snd M, Snd M'
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu UCode evA fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu UCode evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu UCode evA fm = tt
  -- conv-Snd at (FunEl, UCode): ValTy2/EqValTy2 at FunEl = Top
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu UCode evA fm =
    mkSigma tt (mkSigma tt tt)
  -- conv-Snd at (PiCode/SigmaCode, UCode): hard, need ValTyPi2/ValTySigma2 for Snd M
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu UCode evA fm = {!!}
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu UCode evA fm = {!!}
  -- conv-Snd at PiCode: only non-trivial when u = FunEl
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH UCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  -- conv-Snd at (FunEl, PiCode): hard, need full Pi semantics for Snd M
  adequacyEqSub2 (conv-Snd dA dB dMM') sigma rho crho vs fits wtsub wfH (FunEl _) hu (PiCode _ _) evA fm = {!!}

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-funext (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-funext dA d1 d2 d3) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-funext dA d1 d2 d3 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-fun (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-fun _ dB d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-fun dB d1 d2 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-arg (same as original)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-arg _ dB d1 d2) sigma rho crho vs fits wtsub wfH u hu a evA fm =
    adequacyEqSub2-App-arg dB d1 d2 sigma rho crho vs fits wtsub wfH u hu a evA fm

  ----------------------------------------------------------------------
  -- Stub helpers (delegating to the full implementations)
  -- These are placeholders that use the structure from Adequacy2.agda
  -- adapted for the Sigma extension.
  ----------------------------------------------------------------------

  -- Val2 at U b UCode extractor
  Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
    (b : FinEl) -> FinMem b UCode ->
    Val2 G M U b UCode -> ValTy2 G M b
  Val2-U-to-ValTy2 = Val2-U-to-ValTy2'

  EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G M v0
  EqVal2-U-to-ValTy2-fst = EqVal2-U-to-ValTy2-fst'

  EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G N v0
  EqVal2-U-to-ValTy2-snd = EqVal2-U-to-ValTy2-snd'

  EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> EqValTy2 G M N v0
  EqVal2-U-to-EqValTy2 = EqVal2-U-to-EqValTy2'

  -- transportVal2: transport Val2 H N sA u0 b to Val2 H N sA u' a_arg
  transportVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> FinMem b UCode ->
    EvalRel A rho b ->
    (u0 : FinEl) -> FinMem u0 b ->
    (N : Expr h) -> Val2 H N (substExpr sigma A) u0 b ->
    (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
    (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
    Val2 H N (substExpr sigma A) u' a_arg
  transportVal2 {H = H} {A = A} d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
    let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
        a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtA_b    = Val2-U-to-ValTy2 b bU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
        vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
    in sup-transport-Val2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a valN

  -- transportEqVal2: transport EqVal2 H N1 N2 sA u0 b to EqVal2 H N1 N2 sA u' a_arg
  transportEqVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {N1 N2 : Expr h} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> FinMem b UCode ->
    EvalRel A rho b ->
    (u0 : FinEl) -> FinMem u0 b ->
    EqVal2 H N1 N2 (substExpr sigma A) u0 b ->
    (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
    (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
    EqVal2 H N1 N2 (substExpr sigma A) u' a_arg
  transportEqVal2 {H = H} {A = A} d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
    let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
        a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtA_b    = Val2-U-to-ValTy2 b bU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evU bU)
        vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (adequacySub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evU a_argU)
    in sup-transport-EqVal2 b a_arg comp_b_a bU a_argU u0 u' fm_u0_b cu' le_u'_u0 fm_u'_a vtA_b vtA_a eqN

  -- Sigma Pi helpers (stubs - to be filled with full proofs)
  adequacySub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    Val2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) U (PiCode b f) UCode
  adequacySub2-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm =
    let sA    = substExpr sigma A
        sB    = substExpr (liftSub sigma) B
        bU    = fst fm
        allU  = fst (snd fm)
        cf    = snd (snd fm)
        cb    = coh-from-aU b bU
        evAb  = fst (snd hu)
        valTyA = Val2-U-to-ValTy2 b bU
                   (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode
                     (mkSigma tt (LeCode-refl UCode tt)) bU)
        htA  = subst-HasType wtsub wfH d1
        htB  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend (subst-HasType wtsub wfH d1)) d2
    in mkSigma sA (mkSigma sB (mkSigma Red-refl
         (mkSigma cf (mkSigma allU
           (mkSigma htA (mkSigma htB
             (mkSigma valTyA (mkSigma (buildPiEdgeVal2 d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm)
                                      (buildPiEdgeEq2 d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm)))))))))

  -- buildPiEdgeVal2: PiEdgeVal2 for the Pi case
  buildPiEdgeVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeVal2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeVal2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm u0 v0 sel N htN valN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        bodyPi   = snd (snd (snd (snd hu)))
        fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
        fm_v0_U  = FinMem-Selection-UCode b sel allU cf
        cu0      = FinMem-coh-u u0 b fm_u0_b
        w        = bodyPi u0 v0 sel
        x        = fst w
        le_x_u0  = fst (snd w)
        fm_x_a'  = fst (snd (snd w))
        evB_x_v0 = snd (snd (snd w))
        cx       = FinMem-coh-u x a'pi fm_x_a'
        envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
        evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
        fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
        crho'    = mkSigma crho cu0
        htA      = subst-HasType wtsub wfH d1
        hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
        wtsub'   = extSub-WtSub wtsub wfH d1 htN
        evU      = mkSigma tt (LeCode-refl UCode tt)
        ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evU fm_v0_U)
    in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih

  -- buildPiEdgeEq2: PiEdgeEq2 for the Pi case
  buildPiEdgeEq2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeEq2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeEq2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu fm u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        bodyPi   = snd (snd (snd (snd hu)))
        fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
        fm_v0_U  = FinMem-Selection-UCode b sel allU cf
        cu0      = FinMem-coh-u u0 b fm_u0_b
        valN1    = Val2-from-EqVal2-first u0 b eqvalN
        valN2    = Val2-from-EqVal2-second u0 b eqvalN
        w        = bodyPi u0 v0 sel
        x        = fst w
        le_x_u0  = fst (snd w)
        fm_x_a'  = fst (snd (snd w))
        evB_x_v0 = snd (snd (snd w))
        cx       = FinMem-coh-u x a'pi fm_x_a'
        envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
        evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
        fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
        crho'    = mkSigma crho cu0
        htA      = subst-HasType wtsub wfH d1
        -- IH for N1
        hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
        evU      = mkSigma tt (LeCode-refl UCode tt)
        wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
        wfH'     = wfH
        vtN1     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N1) (extendEnv rho u0)
                       crho' vs'_N1 fits' wtsub'_N1 wfH' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN1'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N1)) vtN1
        -- IH for N2
        hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
        wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
        vtN2     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N2 fits' wtsub'_N2 wfH' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN2'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N2)) vtN2
        -- Use adequacyConvSub2 on d2
        vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                     (ValidConvSub2-refl {G = G} vs)
                     (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
        wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
        raw      = adequacyConvSub2 d2 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                     crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH'
                     v0 evB_u0_v0 UCode evU fm_v0_U
        raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                     (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
    in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

  adequacySub2-Sigma : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b f) ->
    EvalRel U rho UCode ->
    FinMem (SigmaCode b f) UCode ->
    Val2 H (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B)) U (SigmaCode b f) UCode
  adequacySub2-Sigma {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits wtsub wfH b f hu evA fm =
    let sA    = substExpr sigma A
        sB    = substExpr (liftSub sigma) B
        bU    = fst fm
        allU  = fst (snd fm)
        cf    = snd (snd fm)
        cb    = coh-from-aU b bU
        evAb  = fst (snd hu)
        valTyA = Val2-U-to-ValTy2 b bU
                   (adequacySub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode
                     (mkSigma tt (LeCode-refl UCode tt)) bU)
        htA  = subst-HasType wtsub wfH d1
        htB  = subst-HasType (liftSub-WtSub wtsub wfH d1) (wf-extend (subst-HasType wtsub wfH d1)) d2
        buildEdgeVal : SigmaEdgeVal2 H sA sB b f
        buildEdgeVal u0 v0 sel N htN valN =
          let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
              fm_v0_U  = FinMem-Selection-UCode b sel allU cf
              cu0      = FinMem-coh-u u0 b fm_u0_b
              w        = snd (snd (snd (snd hu))) u0 v0 sel
              x        = fst w
              le_x_u0  = fst (snd w)
              fm_x_a'  = fst (snd (snd w))
              evB_x_v0 = snd (snd (snd w))
              cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
              envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
              evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
              fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
              crho'    = mkSigma crho cu0
              hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
              wtsub'   = extSub-WtSub wtsub wfH d1 htN
              evU      = mkSigma tt (LeCode-refl UCode tt)
              ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                           (adequacySub2 d2 (extSub sigma N) (extendEnv rho u0)
                             crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evU fm_v0_U)
          in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih
        buildEdgeEq : SigmaEdgeEq2 H sA sB b f
        buildEdgeEq u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
          let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
              fm_v0_U  = FinMem-Selection-UCode b sel allU cf
              cu0      = FinMem-coh-u u0 b fm_u0_b
              valN1    = Val2-from-EqVal2-first u0 b eqvalN
              valN2    = Val2-from-EqVal2-second u0 b eqvalN
              w        = snd (snd (snd (snd hu))) u0 v0 sel
              x        = fst w
              le_x_u0  = fst (snd w)
              fm_x_a'  = fst (snd (snd w))
              evB_x_v0 = snd (snd (snd w))
              cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
              envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
              evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
              fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
              crho'    = mkSigma crho cu0
              evU      = mkSigma tt (LeCode-refl UCode tt)
              hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
              wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
              hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                           transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
              vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
              wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
              vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                           (ValidConvSub2-refl {G = G} vs)
                           (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
              wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
              raw      = adequacyConvSub2 d2 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                           crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                           v0 evB_u0_v0 UCode evU fm_v0_U
              raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                           (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
          in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'
    in mkSigma sA (mkSigma sB (mkSigma Red-refl
         (mkSigma cf (mkSigma allU
           (mkSigma htA (mkSigma htB
             (mkSigma valTyA (mkSigma buildEdgeVal buildEdgeEq))))))))

  adequacySub2-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
      {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} ->
      HasType G A U -> HasType (extend G A) B U ->
      HasType (extend G A) M B ->
      (sigma : Sub h g) -> (rho : EnvApprox g) ->
      CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
      WtSub H G sigma -> WfCtx H ->
      (g0 : FinFun) ->
      EvalRel (Lam A M) rho (FunEl g0) ->
      (b : FinEl) -> (f0 : FinFun) ->
      EvalRel (Pi A B) rho (PiCode b f0) ->
      FinMem (FunEl g0) (PiCode b f0) ->
      Val2 H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
             (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (FunEl g0) (PiCode b f0)
  adequacySub2-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3
      sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm =
    mkSigma valTyPi (mkSigma sA (mkSigma sB (mkSigma Red-refl
      (mkSigma cg (mkSigma fmg (mkSigma piAppVal piAppEq))))))
    where
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sM   = substExpr (liftSub sigma) M
      fmg  = fst fm
      cg   = fst (snd fm)
      pU   = snd (snd fm)
      bU   = fst pU
      allU = fst (snd pU)
      cf0  = snd (snd pU)
      cb   = coh-from-aU b bU
      evAb = fst (snd evA)
      a_lam = fst hu
      bodyLam = snd (snd (snd (snd hu)))
      evU  = mkSigma tt (LeCode-refl UCode tt)
      valTyPi = adequacySub2 (ty-Pi d1 d2) sigma rho crho vs fits wtsub wfH
                  (PiCode b f0) evA UCode evU pU
      piAppVal : PiAppVal2 H (Lam sA sM) sA sB b f0 g0
      piAppVal u' v' sel N htN valN =
        let cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u' v' sel
            x         = fst w
            le_x_u'   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v'  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
            evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
            evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
            crho'     = mkSigma crho cu'
            hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'       = ValidSub2-extend sigma N rho u' vs hyp0
            wtsub'    = extSub-WtSub wtsub wfH d1 htN
            ih        = adequacySub2 d3 (extSub sigma N) (extendEnv rho u')
                          crho' vs' fits' wtsub' wfH v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M      = S.Eq-sym (substExpr-comp sigma M N)
            eq_B      = S.Eq-sym (substExpr-comp sigma B N)
            ih'       = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u')) eq_B ih
            ih''      = S.Eq-transport (\ E -> Val2 H E (subst1 sB N) v' (EvalFun f0 u')) eq_M ih'
        in Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl) ih''
      piAppEq : PiAppEq2 H (Lam sA sM) sA sB b f0 g0
      piAppEq u' v' sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1     = Val2-from-EqVal2-first u' b eqvalN
            valN2     = Val2-from-EqVal2-second u' b eqvalN
            cu'       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u'_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v'_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u' v' sel
            x         = fst w
            le_x_u'   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v'  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
            evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
            evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
            crho'     = mkSigma crho cu'
            wtsub'_N1 = extSub-WtSub wtsub wfH d1 htN1
            wtsub'_N2 = extSub-WtSub wtsub wfH d1 htN2
            hyp0_N1   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            hyp0_N2   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'_N1    = ValidSub2-extend sigma N1 rho u' vs hyp0_N1
            vs'_N2    = ValidSub2-extend sigma N2 rho u' vs hyp0_N2
            vcs_ext   = ValidConvSub2-extend sigma sigma N1 N2 rho u'
                          (ValidConvSub2-refl {G = G} vs)
                          (transportEqVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u' fm_u'_b eqvalN)
            wcs_ext   = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH d1 cvN
            raw       = adequacyConvSub2 d3 (extSub sigma N1) (extSub sigma N2) (extendEnv rho u')
                          crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                          v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M1     = S.Eq-sym (substExpr-comp sigma M N1)
            eq_M2     = S.Eq-sym (substExpr-comp sigma M N2)
            eq_B1     = S.Eq-sym (substExpr-comp sigma B N1)
            raw'      = S.Eq-transport (\ T -> EqVal2 H (subst1 sM N1) T (subst1 sB N1) v' (EvalFun f0 u')) eq_M2
                          (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) M) (subst1 sB N1) v' (EvalFun f0 u')) eq_M1
                            (S.Eq-transport (\ T -> EqVal2 H _ _ T v' (EvalFun f0 u')) eq_B1 raw))
        in EqVal2-headred-expand v' (EvalFun f0 u')
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl) raw'

  adequacySub2-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
    WtSub H G0 sigma -> WfCtx H ->
    (u : FinEl) -> Coherent u ->
    EvalRel (App f' a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u ac
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev Bot evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev UCode evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev PropCode evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH UCode cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1 ev1 PropCode evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) PropCode evAc1 fm1
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev UCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev Bot evAc ()
  -- SigmaCode at UCode: delegate to App-core (handles all (u1, ac1) pairs)
  adequacySub2-App {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode a0s f0s) cu ev UCode evAc fm =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode a0s f0s) cu
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (SigmaCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev UCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (SigmaCode _ _) evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PairCode _ _) cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev UCode evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev PropCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (PiCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (SigmaCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH PropCode cu ev (PairCode _ _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits wtsub wfH Bot cu ev ac evAc fm = Val2-Bot ac
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1 ev1 UCode evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) UCode evAc1 fm1
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1 ev1 (PiCode bacfe facfe) evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits wtsub wfH (FunEl gfe) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (PiCode bacfe facfe) evAc1 fm1

  -- Extract Val2 for Fst sM from M's ValPair2 via theorem1 + adequacySub2 dM.
  -- Works for any (u, a) where u is non-Bot and the result is non-trivial.
  -- The approach: decompose hu to get EvalRel M rho (PairCode u v),
  -- enlarge via theorem1 dM, call adequacySub2 dM at (PairCode, SigmaCode),
  -- extract Val2 (Fst sM) from ValPair2, restrict from enlarged u₀ to u.
  adequacySub2-Fst-from-ValPair2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (Fst M) rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (Fst (substExpr sigma M)) (substExpr sigma A) u a
  adequacySub2-Fst-from-ValPair2 {H = H} {A = A} {B = B} {M = M}
    dA dB dM sigma rho crho vs fits wtsub wfH u hu a evA fm =
    -- hu : Sigma v. EvalRel M rho (PairCode u v)  (for u non-Bot)
    let v_snd   = fst hu
        evM_pair = snd hu
        -- Enlarge M via theorem1
        typed_M = theorem1 dM rho fits (PairCode u v_snd) evM_pair
        u_big   = fst typed_M
        a_sig   = fst (snd typed_M)
        le_pair = fst (snd (snd typed_M))
        evM_big = fst (snd (snd (snd typed_M)))
        fm_big  = fst (snd (snd (snd (snd typed_M))))
        evSig   = snd (snd (snd (snd (snd typed_M))))
    in fst-dispatch u_big a_sig le_pair evM_big fm_big evSig
    where
      sM = substExpr sigma M
      sA = substExpr sigma A
      -- Only (PairCode, SigmaCode) is productive; all others are absurd
      fst-dispatch : (u_big a_sig : FinEl) ->
        LeCode (PairCode u (fst hu)) u_big ->
        EvalRel M rho u_big -> FinMem u_big a_sig ->
        EvalRel (SigmaE A B) rho a_sig ->
        Val2 H (Fst sM) sA u a
      -- u_big = Bot/UCode/PropCode/FunEl/PiCode/SigmaCode: LeCode (PairCode _ _) u_big = Empty
      fst-dispatch Bot _ (mkSigma () _) _ _ _
      fst-dispatch UCode _ (mkSigma () _) _ _ _
      fst-dispatch PropCode _ (mkSigma () _) _ _ _
      fst-dispatch (FunEl _) _ (mkSigma () _) _ _ _
      fst-dispatch (PiCode _ _) _ (mkSigma () _) _ _ _
      fst-dispatch (SigmaCode _ _) _ (mkSigma () _) _ _ _
      -- PairCode: dispatch on a_sig
      fst-dispatch (PairCode u0 v0) Bot _ _ () _
      fst-dispatch (PairCode u0 v0) UCode _ _ () _
      fst-dispatch (PairCode u0 v0) PropCode _ _ () _
      fst-dispatch (PairCode u0 v0) (FunEl _) _ _ () _
      fst-dispatch (PairCode u0 v0) (PiCode _ _) _ _ () _
      fst-dispatch (PairCode u0 v0) (PairCode _ _) _ _ () _
      -- PairCode, SigmaCode: the productive case
      fst-dispatch (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig =
        let -- Get ValPair2 from adequacySub2 dM
            val_M = adequacySub2 dM sigma rho crho vs fits wtsub wfH
                      (PairCode u0 v0) evM_big (SigmaCode b0 f0) evSig fm_big
            -- Extract Val2 (Fst sM) A₀ u0 b0 from ValPair2
            val_fst = snd (snd (snd val_M))
            -- LeCode u u0 (first component of PairCode ordering)
            le_u = fst le_pair
            -- FinMem u0 b0 from FinMem (PairCode u0 v0) (SigmaCode b0 f0)
            fm_u0_b0 = fst (fst fm_big)
            -- EvalRel A rho b0 from evSig
            evA_b0 = fst (snd evSig)
            -- Get ValTy2 sA at b0 for transport
            evU = mkSigma tt (LeCode-refl UCode tt)
            fm_b0_U = fst (snd (snd (fst fm_big)))
            valTy_b0 = adequacySub2 dA sigma rho crho vs fits wtsub wfH b0 evA_b0 UCode evU fm_b0_U
            -- Get ValTy2 sA at a for transport
            fm_a_U = FinMem-a-in-U u a fm
            valTy_a = adequacySub2 dA sigma rho crho vs fits wtsub wfH a evA UCode evU fm_a_U
            -- Transport val_fst from (u0, b0) to (u, a) via sup-transport-Val2
            cb0 = coh-from-aU b0 fm_b0_U
            ca  = coh-from-aU a fm_a_U
            cu  = FinMem-Coherent u a fm
            comp_b0_a = EvalRel-Comp A rho crho b0 a evA_b0 evA
        in sup-transport-Val2 {H = H} {N = Fst sM} {A = sA}
             b0 a comp_b0_a fm_b0_U fm_a_U
             u0 u fm_u0_b0 cu le_u fm
             valTy_b0 valTy_a val_fst

  adequacySub2-Fst-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (Fst M) rho u ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel A rho (PiCode b f) -> FinMem u (PiCode b f) ->
    Typed (Fst M) A rho u ->
    Val2 H (Fst (substExpr sigma M)) (substExpr sigma A) u (PiCode b f)
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH Bot hu b f evA fm _ = tt
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH UCode hu b f evA fm _ = tt
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH PropCode hu b f evA fm _ = tt
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PiCode _ _) hu b f evA fm _ = tt
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu b f evA fm _ = tt
  adequacySub2-Fst-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PairCode _ _) hu b f evA fm _ = tt
  adequacySub2-Fst-Pi {H = H} {A = A} {B = B} {M = M} dA dB dM sigma rho crho vs fits wtsub wfH (FunEl gu) hu b f evA fm typed =
    -- Extract Val2 for Fst sM from M's ValPair2
    -- hu : EvalRel (Fst M) rho (FunEl gu) = Sigma v. EvalRel M rho (PairCode (FunEl gu) v)
    let v_snd  = fst hu
        evM_pair = snd hu
        -- Enlarge M's evaluation via theorem1
        typed_M = theorem1 dM rho fits (PairCode (FunEl gu) v_snd) evM_pair
        u_big   = fst typed_M
        a_sig   = fst (snd typed_M)
        le_pair = fst (snd (snd typed_M))
        evM_big = fst (snd (snd (snd typed_M)))
        fm_big  = fst (snd (snd (snd (snd typed_M))))
        evSig   = snd (snd (snd (snd (snd typed_M))))
    in adequacySub2-Fst-dispatch dA dB dM sigma rho crho vs fits wtsub wfH
         (FunEl gu) v_snd u_big a_sig le_pair evM_big fm_big evSig
         b f evA fm
    where
      sM = substExpr sigma M
      sA = substExpr sigma A
      -- Dispatch on (u_big, a_sig) from theorem1 output
      adequacySub2-Fst-dispatch : {h' g' : Nat} {H' : Ctx h'} {G' : Ctx g'}
        {A' : Expr g'} {B' : Expr (suc g')} {M' : Expr g'} ->
        HasType G' A' U -> HasType (extend G' A') B' U ->
        HasType G' M' (SigmaE A' B') ->
        (sigma' : Sub h' g') -> (rho' : EnvApprox g') ->
        CoherentEnv rho' -> ValidSub2 H' G' sigma' rho' -> Fits G' rho' ->
        WtSub H' G' sigma' -> WfCtx H' ->
        (u_fst v_snd' : FinEl) ->
        (u_big' a_sig' : FinEl) ->
        LeCode (PairCode u_fst v_snd') u_big' ->
        EvalRel M' rho' u_big' ->
        FinMem u_big' a_sig' ->
        EvalRel (SigmaE A' B') rho' a_sig' ->
        (b' : FinEl) -> (f' : FinFun) ->
        EvalRel A' rho' (PiCode b' f') -> FinMem u_fst (PiCode b' f') ->
        Val2 H' (Fst (substExpr sigma' M')) (substExpr sigma' A') u_fst (PiCode b' f')
      -- a_sig = Bot: EvalRel (Sigma A B) rho Bot = Top, FinMem u_big Bot forces u_big = Bot,
      -- but LeCode (PairCode ...) Bot = Empty
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' Bot a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' UCode a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' PropCode a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (FunEl _) a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PiCode _ _) a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (SigmaCode _ _) a_sig' (mkSigma () _) evM_big fm_big evSig b' f' evA' fm'
      -- PairCode case: dispatch on a_sig
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) Bot le_pair evM_big () evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) UCode le_pair evM_big () evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) PropCode le_pair evM_big () evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) (FunEl _) le_pair evM_big () evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) (PiCode _ _) le_pair evM_big () evSig b' f' evA' fm'
      adequacySub2-Fst-dispatch dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) (PairCode _ _) le_pair evM_big () evSig b' f' evA' fm'
      -- The productive case: (PairCode u0 v0, SigmaCode b0 f0)
      adequacySub2-Fst-dispatch {H' = H'} {A' = A'} {B' = B'} {M' = M'}
        dA' dB' dM' sigma' rho' crho' vs' fits' wtsub' wfH'
        u_fst v_snd' (PairCode u0 v0) (SigmaCode b0 f0) le_pair evM_big fm_big evSig b' f' evA' fm' =
        let -- Get ValPair2 from adequacySub2 dM
            val_M = adequacySub2 dM' sigma' rho' crho' vs' fits' wtsub' wfH'
                      (PairCode u0 v0) evM_big (SigmaCode b0 f0) evSig fm_big
            -- val_M : ValPair2 H' sM' sΣ u0 v0 b0 f0
            -- Extract: A₀, B₀, Red, HasType (Fst sM') A₀, Val2 (Fst sM') A₀ u0 b0
            val_fst = snd (snd (snd (snd val_M)))
            -- val_fst : Val2 H' (Fst sM') A₀ u0 b0
            -- le_pair gives LeCode u_fst u0 (first component)
            le_u = fst le_pair
            -- FinMem u0 b0 from FinMem (PairCode u0 v0) (SigmaCode b0 f0)
            fm_u0_b0 = fst (fst fm_big)
            -- Restrict from u0 to u_fst at b0
            fm_ufst_b0 = FinMem-U-to-PropCode u_fst u0 fm' le_u fm_u0_b0
            restricted = restrictVal2 H' (Fst (substExpr sigma' M')) (fst val_M) u0 u_fst b0
                           le_u fm_ufst_b0 fm_u0_b0 val_fst
        in restricted

  adequacySub2-Snd-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G M (SigmaE A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (Snd M) rho u ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (subst1 B (Fst M)) rho (PiCode b f) -> FinMem u (PiCode b f) ->
    Typed (Snd M) (subst1 B (Fst M)) rho u ->
    Val2 H (Snd (substExpr sigma M)) (substExpr sigma (subst1 B (Fst M))) u (PiCode b f)
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH Bot hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH UCode hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH PropCode hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PiCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi dA dB dM sigma rho crho vs fits wtsub wfH (PairCode _ _) hu b f evA fm _ = tt
  adequacySub2-Snd-Pi {H = H} {A = A} {B = B} {M = M} dA dB dM sigma rho crho vs fits wtsub wfH (FunEl gu) hu b f evA fm typed =
    let u'   = fst typed
        a'   = fst (snd typed)
        le'  = fst (snd (snd typed))
        evU' = fst (snd (snd (snd typed)))
        fm'  = fst (snd (snd (snd (snd typed))))
        evBFst = snd (snd (snd (snd (snd typed))))
        -- TODO: need EvalRel (subst1 B (Fst M)) rho (FunEl gu) from typed evidence
    in {!!}

  adequacyEqSub2-beta : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} {a : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType (extend G A) M B -> HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App (Lam A M) a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (substExpr sigma (App (Lam A M) a))
             (substExpr sigma (subst1 M a))
             (substExpr sigma (subst1 B a)) u ac
  adequacyEqSub2-beta {H = H} {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4 sigma rho crho vs fits wtsub wfH u hu ac evAc fm =
    let val_app = adequacySub2 (ty-App d1 d2 (ty-Lam d1 d2 d3) d4)
                    sigma rho crho vs fits wtsub wfH u hu ac evAc fm
        beta-hr : HeadRed (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
                                (substExpr sigma a0))
                          (substExpr sigma (subst1 M a0))
        beta-hr = S.Eq-transport
                    (\ X -> HeadRed (App (Lam (substExpr sigma A)
                      (substExpr (liftSub sigma) M)) (substExpr sigma a0)) X)
                    (subst-subst1-comm sigma M a0)
                    (headred-step headred-beta headred-refl)
        val_subst = Val2-headred-contract u ac beta-hr val_app
        eqval_diag = Val2-to-EqVal2 u ac val_subst
    in EqVal2-headred-expand u ac beta-hr headred-refl eqval_diag

  adequacyEqSub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G A A' U ->
    ConvTm (extend G A) B B' U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (Pi (substExpr sigma A') (substExpr (liftSub sigma) B'))
             U (PiCode b f) UCode
  adequacyEqSub2-Pi {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 sigma rho crho vs fits wtsub wfH b f hu evU fm =
    mkSigma valTyPiAB (mkSigma valTyPiA'B' eqValTyPi)
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma A'
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma) B'
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      a'pi = fst (snd (snd hu))
      bodyPi = snd (snd (snd (snd hu)))

      eqD1 = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evUU bU
      valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
      valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
      eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

      trVal : (u0 : FinEl) -> FinMem u0 b ->
        (N : Expr _) -> Val2 H N sA u0 b ->
        (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H N sA u' a_arg
      trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
        let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
            a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
            vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                         (adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evUU a_argU)
            vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
            ca_arg   = EvalRel-coh A rho a_arg evA_arg
            sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
            c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
            le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
            le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
            fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
            fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
            val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
            val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
            val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
        in val3

      -- Build codomain validity for B (first side)
      buildEdgeValB2 : PiEdgeVal2 H sA sB b f
      buildEdgeValB2 u0 v0 sel N htN valN =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
             (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

      buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
      buildEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1    = Val2-from-EqVal2-first u0 b eqvalN
            valN2    = Val2-from-EqVal2-second u0 b eqvalN
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB_conv  = fst (typing-ConvTm d2)
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
            raw      = adequacyConvSub2 dB_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      -- B' validity
      buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
      buildEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
        let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N
                           (Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A') u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
             (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

      -- B' edge equality (simplified)
      buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
      buildEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB'_conv = snd (typing-ConvTm d2)
            htA_loc  = subst-HasType wtsub wfH dA_conv
            convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
            htN1_A   = ty-conv htN1_A' convA'A htA_loc
            htN2_A   = ty-conv htN2_A' convA'A htA_loc
            cvN_A    = conv-conv cvN_A' convA'A htA_loc
            eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
            valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
            valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
            evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB'_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
            raw      = adequacyConvSub2 dB'_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB'_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
      buildEdgeEqTyBB'2 u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'pi fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
            ih       = adequacyEqSub2 d2 (extSub sigma P) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
            eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                         (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                           (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
        in eqvt

      htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
      htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

      valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
      valTyPiAB = mkSigma sA (mkSigma sB (mkSigma Red-refl
                    (mkSigma cf (mkSigma allU
                      (mkSigma htA_AB (mkSigma htB_AB
                        (mkSigma valTyA (mkSigma buildEdgeValB2 buildEdgeEqB2))))))))

      htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
      htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
      htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

      valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
      valTyPiA'B' = mkSigma sA' (mkSigma sB' (mkSigma Red-refl
                      (mkSigma cf (mkSigma allU
                        (mkSigma htA_A'B' (mkSigma htB_A'B'
                          (mkSigma valTyA' (mkSigma buildEdgeValB'2 buildEdgeEqB'2))))))))

      convA_sub  = subst-ConvTm wtsub wfH d1
      convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

      eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
      eqValTyPi = mkSigma valTyPiAB (mkSigma valTyPiA'B'
                    (mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                      (mkSigma Red-refl
                        (mkSigma Red-refl
                          (mkSigma cf (mkSigma allU
                            (mkSigma convA_sub (mkSigma convB_sub
                              (mkSigma eqValTyAA' buildEdgeEqTyBB'2))))))))))))


  adequacyEqSub2-Sigma : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G A A' U ->
    ConvTm (extend G A) B B' U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (SigmaE A B) rho (SigmaCode b f) ->
    EvalRel U rho UCode ->
    FinMem (SigmaCode b f) UCode ->
    EqVal2 H (SigmaE (substExpr sigma A) (substExpr (liftSub sigma) B))
             (SigmaE (substExpr sigma A') (substExpr (liftSub sigma) B'))
             U (SigmaCode b f) UCode
  -- Mirrors adequacyEqSub2-Pi with SigmaEdge functions.
  adequacyEqSub2-Sigma {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 sigma rho crho vs fits wtsub wfH b f hu evU fm =
    mkSigma valTySigmaAB (mkSigma valTySigmaA'B' eqValTySigma)
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma A'
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma) B'
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      a'sig = fst (snd (snd hu))
      bodySigma = snd (snd (snd (snd hu)))

      eqD1 = adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH b evAb UCode evUU bU
      valTyA  = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)
      valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1
      eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

      trVal : (u0 : FinEl) -> FinMem u0 b ->
        (N : Expr _) -> Val2 H N sA u0 b ->
        (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H N sA u' a_arg
      trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
        let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
            a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
            vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                         (adequacyEqSub2 d1 sigma rho crho vs fits wtsub wfH a_arg evA_arg UCode evUU a_argU)
            vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
            ca_arg   = EvalRel-coh A rho a_arg evA_arg
            sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
            c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
            le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
            le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
            fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
            fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
            val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup cb c_sup valN vtA_sup
            val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
            val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
        in val3

      -- Build codomain validity for B (first side)
      buildSigmaEdgeValB2 : SigmaEdgeVal2 H sA sB b f
      buildSigmaEdgeValB2 u0 v0 sel N htN valN =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
             (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

      buildSigmaEdgeEqB2 : SigmaEdgeEq2 H sA sB b f
      buildSigmaEdgeEqB2 u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
        let valN1    = Val2-from-EqVal2-first u0 b eqvalN
            valN2    = Val2-from-EqVal2-second u0 b eqvalN
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB_conv  = fst (typing-ConvTm d2)
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN
            raw      = adequacyConvSub2 dB_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B) U v0 UCode) (S.Eq-sym (substExpr-comp sigma B N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      -- B' validity (primed side)
      buildSigmaEdgeValB'2 : SigmaEdgeVal2 H sA' sB' b f
      buildSigmaEdgeValB'2 u0 v0 sel N htN_A' valN_A' =
        let valN_A   = Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A'
            fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N
                           (Val2-EqValTy2-fwd u0 b cb eqValTyA'A valN_A') u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
            htN_A    = ty-conv htN_A' (subst-ConvTm wtsub wfH (conv-sym d1)) (subst-HasType wtsub wfH (fst (typing-ConvTm d1)))
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htN_A
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
             (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

      -- B' edge equality (primed side)
      buildSigmaEdgeEqB'2 : SigmaEdgeEq2 H sA' sB' b f
      buildSigmaEdgeEqB'2 u0 v0 sel N1 N2 htN1_A' htN2_A' cvN_A' eqvalN_A' =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            dA_conv  = fst (typing-ConvTm d1)
            dB'_conv = snd (typing-ConvTm d2)
            htA_loc  = subst-HasType wtsub wfH dA_conv
            convA'A  = subst-ConvTm wtsub wfH (conv-sym d1)
            htN1_A   = ty-conv htN1_A' convA'A htA_loc
            htN2_A   = ty-conv htN2_A' convA'A htA_loc
            cvN_A    = conv-conv cvN_A' convA'A htA_loc
            eqvalN_A = EqVal2-EqValTy2-fwd u0 b cb eqValTyA'A eqvalN_A'
            valN1_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-first u0 b eqvalN_A')
            valN2_A  = Val2-EqValTy2-fwd u0 b cb eqValTyA'A (Val2-from-EqVal2-second u0 b eqvalN_A')
            evB'_u0_v0 = convSound d2 (extendEnv rho u0) fits' v0 evB_u0_v0
            hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N1 valN1_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
            wtsub'_N1 = extSub-WtSub wtsub wfH dA_conv htN1_A
            hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b N2 valN2_A u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
            wtsub'_N2 = extSub-WtSub wtsub wfH dA_conv htN2_A
            vcs_ext  = ValidConvSub2-extend sigma sigma N1 N2 rho u0
                         (ValidConvSub2-refl {G = G} vs)
                         (transportEqVal2 dA_conv dB'_conv sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b eqvalN_A)
            wcs_ext  = extSub-WtConvSub wtsub (WtConvSub-refl {G = G} wtsub) wfH dA_conv cvN_A
            raw      = adequacyConvSub2 dB'_conv (extSub sigma N1) (extSub sigma N2) (extendEnv rho u0)
                         crho' vs'_N1 vs'_N2 vcs_ext fits' wtsub'_N1 wtsub'_N2 wcs_ext wfH
                         v0 evB'_u0_v0 UCode evUU fm_v0_U
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB' N1) T U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N2))
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma N2) B') U v0 UCode) (S.Eq-sym (substExpr-comp sigma B' N1)) raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      buildSigmaEdgeEqTyBB'2 : SigmaEdgeEqTy2 H sA sB sB' b f
      buildSigmaEdgeEqTyBB'2 u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodySigma u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x a'sig fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         trVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs'      = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'   = extSub-WtSub wtsub wfH (fst (typing-ConvTm d1)) htP
            ih       = adequacyEqSub2 d2 (extSub sigma P) (extendEnv rho u0)
                         crho' vs' fits' wtsub' wfH v0 evB_u0_v0 UCode evUU fm_v0_U
            eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                         (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                           (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
        in eqvt

      htA_AB  = subst-HasType wtsub wfH (fst (typing-ConvTm d1))
      htB_AB  = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (fst (typing-ConvTm d2))

      valTySigmaAB : ValTy2 H (SigmaE sA sB) (SigmaCode b f)
      valTySigmaAB = mkSigma sA (mkSigma sB (mkSigma Red-refl
                       (mkSigma cf (mkSigma allU
                         (mkSigma htA_AB (mkSigma htB_AB
                           (mkSigma valTyA (mkSigma buildSigmaEdgeValB2 buildSigmaEdgeEqB2))))))))

      htA_A'B' = subst-HasType wtsub wfH (snd (typing-ConvTm d1))
      htBprime_sA = subst-HasType (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) (snd (typing-ConvTm d2))
      htB_A'B' = ctx-conv-HasType htA_AB htA_A'B' (subst-ConvTm wtsub wfH d1) htBprime_sA

      valTySigmaA'B' : ValTy2 H (SigmaE sA' sB') (SigmaCode b f)
      valTySigmaA'B' = mkSigma sA' (mkSigma sB' (mkSigma Red-refl
                         (mkSigma cf (mkSigma allU
                           (mkSigma htA_A'B' (mkSigma htB_A'B'
                             (mkSigma valTyA' (mkSigma buildSigmaEdgeValB'2 buildSigmaEdgeEqB'2))))))))

      convA_sub  = subst-ConvTm wtsub wfH d1
      convB_sub  = subst-ConvTm (liftSub-WtSub wtsub wfH (fst (typing-ConvTm d1))) (wf-extend htA_AB) d2

      eqValTySigma : EqValTy2 H (SigmaE sA sB) (SigmaE sA' sB') (SigmaCode b f)
      eqValTySigma = mkSigma valTySigmaAB (mkSigma valTySigmaA'B'
                       (mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                         (mkSigma Red-refl
                           (mkSigma Red-refl
                             (mkSigma cf (mkSigma allU
                               (mkSigma convA_sub (mkSigma convB_sub
                                 (mkSigma eqValTyAA' buildSigmaEdgeEqTyBB'2))))))))))))


  adequacyEqSub2-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
    HasType G A U ->
    ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                         (App (wkExpr g') (Var fzero)) B ->
    HasType G f (Pi A B) ->
    HasType G g' (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel f rho u ->
    (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma f) (substExpr sigma g')
            (substExpr sigma (Pi A B)) u a
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu Bot evA fm = tt
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu UCode () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (FunEl _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu PropCode () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (SigmaCode _ _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH u hu (PairCode _ _) () fm
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH Bot hu (PiCode b f0) evA fm = tt
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH UCode hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH PropCode hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (PiCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (SigmaCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits wtsub wfH (PairCode _ _) hu (PiCode b f0) evA ()
  adequacyEqSub2-funext {H = H} {G = G} {A = A} {B = B} {f = f} {g' = g'} dA d df dg sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm =
    let val_sf = adequacySub2 df sigma rho crho vs fits wtsub wfH (FunEl g0) hu (PiCode b f0) evA fm
        evG    = convSound (conv-funext dA d df dg) rho fits (FunEl g0) hu
        val_sg = adequacySub2 dg sigma rho crho vs fits wtsub wfH (FunEl g0) evG (PiCode b f0) evA fm
        valTyPi = fst val_sf
        valPi_sf = snd val_sf
        valPi_sg = snd val_sg
    in mkSigma valTyPi (mkSigma valPi_sf (mkSigma valPi_sg
         (mkSigma (substExpr sigma A) (mkSigma (substExpr (liftSub sigma) B) (mkSigma Red-refl
           (mkSigma (fst (snd (snd (snd valPi_sf)))) (mkSigma (fst (snd (snd (snd (snd valPi_sf)))))
             (buildEqBody valPi_sf))))))))
    where
      sA'   = substExpr sigma A
      sB'   = substExpr (liftSub sigma) B
      htBU' = typing-Pi-codomain dA df
      fmg'  = fst fm
      cg'   = fst (snd fm)
      pU'   = snd (snd fm)
      bU'   = fst pU'
      allU' = fst (snd pU')
      cf0'  = snd (snd pU')
      cb'   = coh-from-aU b bU'
      evAb' = fst (snd evA)
      ctg0' = cft-from-cf g0 cg'

      -- Core: build EqVal2 for non-Bot v0, taking ev_app as parameter
      buildEqBodyCore : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        Coherent u0 ->
        EvalRel (App (wkExpr f) (Var fzero)) (extendEnv rho u0) v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      buildEqBodyCore u0 v0 sel cu0 ev_app P htP valP =
        let fm_u0_b   = FinMem-Selection b f0 sel fmg' ctg0' cb' bU'
            fm_v0_ef  = FinMem-Selection-codomain b f0 sel fmg' ctg0' cf0' allU'
            evB_ef    = EvalRel-Pi-body A B rho b f0 u0 crho cu0 evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb'))
            crho'     = mkSigma crho cu0
            hyp0      = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 dA htBU' sigma rho crho vs fits wtsub wfH b bU' evAb' u0 fm_u0_b P valP u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'       = ValidSub2-extend sigma P rho u0 vs hyp0
            wtsub'    = extSub-WtSub wtsub wfH dA htP
            raw       = adequacyEqSub2 d (extSub sigma P) (extendEnv rho u0) crho' vs' fits' wtsub' wfH
                          v0 ev_app (EvalFun f0 u0) evB_ef fm_v0_ef
            eq_f_wk   = substExpr-wk sigma f P
            eq_g_wk   = substExpr-wk sigma g' P
            eq_B_comp = S.Eq-sym (substExpr-comp sigma B P)
            raw'      = S.Eq-transport (\ T -> EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) T v0 (EvalFun f0 u0)) eq_B_comp
                          (S.Eq-transport (\ X -> EqVal2 H (App (substExpr sigma f) P) (App X P) (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_g_wk
                            (S.Eq-transport (\ X -> EqVal2 H (App X P) _ (substExpr (extSub sigma P) B) v0 (EvalFun f0 u0)) eq_f_wk raw))
        in raw'

      -- Build singleton eval data and call core (for each concrete v0)
      mkEvAppAndCall : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        Coherent u0 -> Coherent v0 -> NotBot v0 ->
        EvalRel (App (wkExpr f) (Var fzero)) (extendEnv rho u0) v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      mkEvAppAndCall u0 v0 sel cu0 cv0 nbv0 ev_app P htP valP =
        buildEqBodyCore u0 v0 sel cu0 ev_app P htP valP

      mkSingEvApp : (u0 : FinEl) (v0 : FinEl) -> Coherent u0 -> Coherent v0 -> NotBot v0 ->
        LeCode v0 (EvalFun g0 u0) ->
        EvalRel f rho (FunEl (cons (mkSigma u0 v0) nil))
      mkSingEvApp u0 v0 cu0 cv0 nbv0 le_v0 =
        let c_sing    = mkCFT cu0 cv0 nbv0 tt tt
        in EvalRel-down f rho (FunEl g0) (FunEl (cons (mkSigma u0 v0) nil))
                          crho c_sing hu (mkSigma le_v0 tt)

      buildEqBody : _ -> (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        (P : Expr _) -> HasType H P sA' -> Val2 H P sA' u0 b ->
        EqVal2 H (App (substExpr sigma f) P) (App (substExpr sigma g') P) (subst1 sB' P) v0 (EvalFun f0 u0)
      buildEqBody _ u0 Bot sel P htP valP = EqVal2-Bot (EvalFun f0 u0)
      buildEqBody vps u0 UCode sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 UCode cu0 tt tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 UCode) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 UCode sel cu0 ev_app P htP valP
      buildEqBody vps u0 PropCode sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 PropCode cu0 tt tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 PropCode) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 PropCode sel cu0 ev_app P htP valP
      buildEqBody vps u0 (FunEl g1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (FunEl g1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (FunEl g1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (FunEl g1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (PiCode a1 f1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (PiCode a1 f1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (PiCode a1 f1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (PiCode a1 f1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (SigmaCode a1 f1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (SigmaCode a1 f1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (SigmaCode a1 f1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (SigmaCode a1 f1) sel cu0 ev_app P htP valP
      buildEqBody vps u0 (PairCode u1 v1) sel P htP valP =
        let cu0 = Coherent-Selection sel ctg0'
            cv0 = Coherent-Selection-val sel ctg0'
            le  = Selection-le-EvalFun g0 sel (LeFunCode-refl g0 ctg0') ctg0' ctg0' cu0
            ev_f_sing = mkSingEvApp u0 (PairCode u1 v1) cu0 cv0 tt le
            ev_wkf    = EvalRel-wk f rho u0 (FunEl (cons (mkSigma u0 (PairCode u1 v1)) nil)) ev_f_sing
            ev_var    = mkSigma cu0 (LeCode-refl u0 cu0)
            ev_app    = mkSigma u0 (mkSigma ev_var ev_wkf)
        in buildEqBodyCore u0 (PairCode u1 v1) sel cu0 ev_app P htP valP

  adequacyEqSub2-App-fun-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u1 : FinEl) ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-fun-core {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
    dB dff' da sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf' sa) T u1 ac1) (S.Eq-sym eq-sBA) transported
    where
      sf   = substExpr sigma f0
      sf'  = substExpr sigma f'
      sa   = substExpr sigma a
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sBA  = substExpr sigma (subst1 B a)
      eq-sBA : Eq sBA (subst1 sB sa)
      eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

      sing     = cons (mkSigma v0 u1) nil
      cv0      = EvalRel-coh a rho v0 evA_v0

      -- Enlarge function via convSound' (InvTyp for f)
      invTyp-f = fst (convSound' dff' rho fits)
      typed_f  = invTyp-f (FunEl sing) evF_sing
      u_big    = fst typed_f
      a_pi     = fst (snd typed_f)
      le_sing  = fst (snd (snd typed_f))
      evF_big  = fst (snd (snd (snd typed_f)))
      fm_big   = fst (snd (snd (snd (snd typed_f))))
      evPi     = snd (snd (snd (snd (snd typed_f))))

      -- Function's EqVal2 via adequacyEqSub2 on dff'
      eqval_fun = adequacyEqSub2 dff' sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

      -- Dispatch on (ub, ap) — only (FunEl, PiCode) is non-absurd
      appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        EqVal2 H sf sf' (Pi sA sB) ub ap ->
        EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
      appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
      appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
      appEqVal-dispatch PropCode     ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba eqvba
      appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba eqvba
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
        let le_u1_vsel = fst lf
            fmg_big  = fst fmba
            cg_big   = fst (snd fmba)
            piU      = snd (snd fmba)
            b_piU    = fst piU
            allU_fpi = fst (snd piU)
            cf_pi    = snd (snd piU)
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' : LeCode u1 v_sel
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

            -- Argument Val2
            evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
            val_arg  = adequacySub2 da sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract EqValPi2 from EqVal2 at (FunEl, PiCode)
            eqvpi_fun = snd (snd (snd eqvba))
            A0_eqfun  = fst eqvpi_fun
            B0_eqfun  = fst (snd eqvpi_fun)
            red_eqfun = fst (snd (snd eqvpi_fun))
            uniq_eqfun = Red-unique-Pi2 Red-refl red_eqfun
            eqA_eqfun = fst uniq_eqfun
            eqB_eqfun = snd uniq_eqfun
            paeqv_fun = snd (snd (snd (snd (snd eqvpi_fun))))

            -- Transport argument type
            val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_arg
            ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun (subst-HasType wtsub wfH da)

            -- Apply PiAppEqVal2
            eqval_app_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_arg'
            eqval_app : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            eqval_app = S.Eq-transport
              (\ X -> EqVal2 H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_eqfun) eqval_app_raw

            -- Transport chain
            ef_usel  = EvalFun f_pi u_sel
            cft_fpi  = cf_pi
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
            c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
            c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
            evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
            c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1
            sup_code = Sup ac1 ef_usel
            c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
            sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
            fm_u1_sup = finMem-upward u1 ac1 sup_code le_ac_sup c_ac c_sup fm1 sup_U
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
            fm_vsel_sup = finMem-upward v_sel ef_usel sup_code le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

            -- ValTy2 at Sup
            evU      = mkSigma tt (LeCode-refl UCode tt)
            fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
            v_fwd    = fst fwd_ac
            evA_vfwd = fst (snd fwd_ac)
            evB_vfwd = snd (snd fwd_ac)
            typed_a_fwd = theorem1 da rho fits v_fwd evA_vfwd
            v_fwd'   = fst typed_a_fwd
            a_fit    = fst (snd typed_a_fwd)
            le_vfwd  = fst (snd (snd typed_a_fwd))
            evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
            fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
            evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
            cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
            cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
            envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
            evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                          ac1 evB_vfwd envle_fwd
            fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
            crho_ext = mkSigma crho cv_fwd'
            dA_loc   = wfCtx-domain (typing-WfCtx dB)
            htA_loc  = subst-HasType wtsub wfH dA_loc
            wtsub_ext = extSub-WtSub wtsub wfH dA_loc (subst-HasType wtsub wfH da)
            wfH_ext  = wf-extend htA_loc
            hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
              in adequacySub2 da sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
            eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
            vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

            fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
            v_fwd_ef = fst fwd_ef
            evA_vfef = fst (snd fwd_ef)
            evB_vfef = snd (snd fwd_ef)
            typed_a_ef = theorem1 da rho fits v_fwd_ef evA_vfef
            v_fwd_ef' = fst typed_a_ef
            a_fit_ef  = fst (snd typed_a_ef)
            le_vfef   = fst (snd (snd typed_a_ef))
            evA_vfef' = fst (snd (snd (snd typed_a_ef)))
            fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
            evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
            cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
            cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
            envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
            evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                          ef_usel evB_vfef envle_ef
            fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
            crho_ef   = mkSigma crho cv_fef'
            hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
              in adequacySub2 da sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

            vt_sup   = ValTy2-Sup H (subst1 sB sa) ac1 ef_usel
                         comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
            eqval_up   = upEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel ef_usel sup_code
                           le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup eqval_app vt_sup
            eqval_res  = restrictEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel u1 sup_code
                           le_u1_vsel' fm_u1_sup fm_vsel_sup eqval_up
            eqval_down = downEqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1
                           ac1 sup_code le_ac_sup fm1 c_ac sup_U eqval_res
        in eqval_down

      transported : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
      transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_fun

  adequacyEqSub2-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev UCode evAc fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH UCode ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev PropCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) PropCode evAc fm
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev PropCode evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (FunEl _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev Bot evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev UCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH PropCode ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev UCode evAc fm = {!!} -- pre-existing: needs ValTySigma2
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev UCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits wtsub wfH (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  adequacyEqSub2-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev UCode evAc fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH UCode ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev PropCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) PropCode evAc fm
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PiCode _ _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev PropCode evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (SigmaCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (FunEl _) ev (PairCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev Bot evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev UCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH PropCode ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev UCode evAc fm = {!!} -- pre-existing: needs ValTySigma2
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (SigmaCode _ _) ev (PairCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev Bot evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev UCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev PropCode evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (FunEl _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PiCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (SigmaCode _ _) evAc fm = tt
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits wtsub wfH (PairCode _ _) ev (PairCode _ _) evAc fm = tt
  -- PiCode/UCode and FunEl/PiCode
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits wtsub wfH (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  -- Core App-arg helper
  adequacyEqSub2-App-arg-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u1 : FinEl) ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-arg-core {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits wtsub wfH u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf sa') T u1 ac1) (S.Eq-sym eq-sBA) transported
    where
      sf   = substExpr sigma f0
      sa   = substExpr sigma a
      sa'  = substExpr sigma a'
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sBA  = substExpr sigma (subst1 B a)
      eq-sBA : Eq sBA (subst1 sB sa)
      eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

      sing     = cons (mkSigma v0 u1) nil
      cv0      = EvalRel-coh a rho v0 evA_v0

      -- Enlarge function via theorem1 (df : HasType)
      typed_f  = theorem1 df rho fits (FunEl sing) evF_sing
      u_big    = fst typed_f
      a_pi     = fst (snd typed_f)
      le_sing  = fst (snd (snd typed_f))
      evF_big  = fst (snd (snd (snd typed_f)))
      fm_big   = fst (snd (snd (snd (snd typed_f))))
      evPi     = snd (snd (snd (snd (snd typed_f))))

      -- Function's Val2
      val_fun  = adequacySub2 df sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

      -- Helper: Val2 for sa via Val2-from-EqVal2-first
      val_sa : (u' : FinEl) -> EvalRel a rho u' ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H sa sA u' a_arg
      val_sa u' evA_u' a_arg evA_aarg fm_u'_a =
        Val2-from-EqVal2-first u' a_arg
          (adequacyEqSub2 daa' sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a)

      -- InvTyp for a from convSound' daa'
      invTyp_a = fst (convSound' daa' rho fits)

      -- Dispatch on (ub, ap)
      appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        Val2 H sf (Pi sA sB) ub ap ->
        EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
      appEqVal-dispatch Bot          ap    () evFb evPab fmba valba
      appEqVal-dispatch UCode        ap    () evFb evPab fmba valba
      appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
      appEqVal-dispatch PropCode     ap    () evFb evPab fmba valba
      appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba valba
      appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba valba
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
        let le_u1_vsel = fst lf
            fmg_big  = fst fmba
            cg_big   = fst (snd fmba)
            piU      = snd (snd fmba)
            b_piU    = fst piU
            allU_fpi = fst (snd piU)
            cf_pi    = snd (snd piU)
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' : LeCode u1 v_sel
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

            -- Argument EqVal2 via adequacyEqSub2 daa'
            evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
            eqval_arg = adequacyEqSub2 daa' sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract PiAppEq2 from function's Val2 at (FunEl, PiCode)
            -- Val2 = Pair ValTyPi2 ValPi2
            vpi_fun  = snd valba
            A0_fun   = fst vpi_fun
            B0_fun   = fst (snd vpi_fun)
            red_fun  = fst (snd (snd vpi_fun))
            uniq_fun = Red-unique-Pi2 Red-refl red_fun
            eqA_fun  = fst uniq_fun
            eqB_fun  = snd uniq_fun
            pae_fun  = snd (snd (snd (snd (snd (snd vpi_fun)))))

            -- Transport argument types
            eqval_arg' = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_fun eqval_arg
            ht_sa_A0   = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH (fst (typing-ConvTm daa')))
            ht_sa'_A0  = S.Eq-transport (\ X -> HasType H sa' X) eqA_fun (subst-HasType wtsub wfH (snd (typing-ConvTm daa')))
            cv_aa'_A0  = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_fun (subst-ConvTm wtsub wfH daa')

            -- Apply PiAppEq2
            eqval_app_raw : EqVal2 H (App sf sa) (App sf sa') (subst1 B0_fun sa) v_sel (EvalFun f_pi u_sel)
            eqval_app_raw = pae_fun u_sel v_sel sel_big sa sa' ht_sa_A0 ht_sa'_A0 cv_aa'_A0 eqval_arg'
            eqval_app : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            eqval_app = S.Eq-transport
              (\ X -> EqVal2 H (App sf sa) (App sf sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_fun) eqval_app_raw

            -- Transport chain
            ef_usel  = EvalFun f_pi u_sel
            cft_fpi  = cf_pi
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
            c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
            c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
            evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
            c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1
            sup_code = Sup ac1 ef_usel
            c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
            sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
            fm_u1_sup = finMem-upward u1 ac1 sup_code le_ac_sup c_ac c_sup fm1 sup_U
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
            fm_vsel_sup = finMem-upward v_sel ef_usel sup_code le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

            -- ValTy2 at Sup
            evU      = mkSigma tt (LeCode-refl UCode tt)
            fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
            v_fwd    = fst fwd_ac
            evA_vfwd = fst (snd fwd_ac)
            evB_vfwd = snd (snd fwd_ac)
            typed_a_fwd = invTyp_a v_fwd evA_vfwd
            v_fwd'   = fst typed_a_fwd
            a_fit    = fst (snd typed_a_fwd)
            le_vfwd  = fst (snd (snd typed_a_fwd))
            evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
            fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
            evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
            cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
            cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
            envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
            evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                          ac1 evB_vfwd envle_fwd
            fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
            crho_ext = mkSigma crho cv_fwd'
            hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
              in val_sa u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            dA_loc   = wfCtx-domain (typing-WfCtx dB)
            htA_loc  = subst-HasType wtsub wfH dA_loc
            htSa_loc = subst-HasType wtsub wfH (fst (typing-ConvTm daa'))
            wtsub_ext = extSub-WtSub wtsub wfH dA_loc htSa_loc
            wfH_ext  = wf-extend htA_loc
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
            eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
            vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

            fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
            v_fwd_ef = fst fwd_ef
            evA_vfef = fst (snd fwd_ef)
            evB_vfef = snd (snd fwd_ef)
            typed_a_ef = invTyp_a v_fwd_ef evA_vfef
            v_fwd_ef' = fst typed_a_ef
            a_fit_ef  = fst (snd typed_a_ef)
            le_vfef   = fst (snd (snd typed_a_ef))
            evA_vfef' = fst (snd (snd (snd typed_a_ef)))
            fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
            evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
            cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
            cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
            envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
            evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                          ef_usel evB_vfef envle_ef
            fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
            crho_ef   = mkSigma crho cv_fef'
            hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
              in val_sa u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

        in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_app

      transported : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
      transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

  -- Also define adequacySub2-App-core (needed by adequacySub2-App)
  adequacySub2-App-core : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
    WtSub H G0 sigma -> WfCtx H ->
    (u1 : FinEl) -> Coherent u1 ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f' rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u1 ac1
  adequacySub2-App-core {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits wtsub wfH u1 cu1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    S.Eq-transport (\ T -> Val2 H (App sf sa) T u1 ac1) (S.Eq-sym eq-sBA) transported
    where
      sf  = substExpr sigma f'
      sa  = substExpr sigma a
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sBA = substExpr sigma (subst1 B a)
      eq-sBA : Eq sBA (subst1 sB sa)
      eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

      sing     = cons (mkSigma v0 u1) nil
      cv0      = EvalRel-coh a rho v0 evA_v0

      -- Enlarge function via theorem1
      typed_f  = theorem1 d1 rho fits (FunEl sing) evF_sing
      u_big    = fst typed_f
      a_pi     = fst (snd typed_f)
      le_sing  = fst (snd (snd typed_f))
      evF_big  = fst (snd (snd (snd typed_f)))
      fm_big   = fst (snd (snd (snd (snd typed_f))))
      evPi     = snd (snd (snd (snd (snd typed_f))))

      -- Function's Val2
      val_fun  = adequacySub2 d1 sigma rho crho vs fits wtsub wfH u_big evF_big a_pi evPi fm_big

      -- Dispatch on (ub, ap)
      appVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f' rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        Val2 H sf (Pi sA sB) ub ap ->
        Val2 H (App sf sa) (subst1 sB sa) u1 ac1
      appVal-dispatch Bot          ap    () evFb evPab fmba valba
      appVal-dispatch UCode        ap    () evFb evPab fmba valba
      appVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
      appVal-dispatch PropCode     ap    () evFb evPab fmba valba
      appVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba valba
      appVal-dispatch (PairCode _ _) ap  () evFb evPab fmba valba
      appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
        let le_u1_vsel = fst lf
            fmg_big  = fst fmba
            cg_big   = fst (snd fmba)
            piU      = snd (snd fmba)
            b_piU    = fst piU
            allU_fpi = fst (snd piU)
            cf_pi    = snd (snd piU)
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' : LeCode u1 v_sel
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)

            -- Argument Val2
            evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU
            val_arg  = adequacySub2 d2 sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract PiAppVal2 from function's Val2
            vpi_fun  = snd valba
            A0_fun   = fst vpi_fun
            B0_fun   = fst (snd vpi_fun)
            red_fun  = fst (snd (snd vpi_fun))
            uniq_fun = Red-unique-Pi2 Red-refl red_fun
            eqA_fun  = fst uniq_fun
            eqB_fun  = snd uniq_fun
            pav_fun  = fst (snd (snd (snd (snd (snd vpi_fun)))))

            -- Transport argument type
            val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_fun val_arg
            ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_fun (subst-HasType wtsub wfH d2)

            -- Apply PiAppVal2
            val_app_raw = pav_fun u_sel v_sel sel_big sa ht_sa_A0 val_arg'
            val_app : Val2 H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            val_app = S.Eq-transport
              (\ X -> Val2 H (App sf sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_fun) val_app_raw

            -- Transport: (v_sel, EvalFun f_pi u_sel) -> (u1, ac1)
            ef_usel  = EvalFun f_pi u_sel
            cft_fpi  = cf_pi
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
            c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
            c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
            evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel

            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi

            -- ValTy2 at ac1
            evU      = mkSigma tt (LeCode-refl UCode tt)
            fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
            v_fwd    = fst fwd_ac
            evA_vfwd = fst (snd fwd_ac)
            evB_vfwd = snd (snd fwd_ac)
            typed_a_fwd = theorem1 d2 rho fits v_fwd evA_vfwd
            v_fwd'   = fst typed_a_fwd
            a_fit    = fst (snd typed_a_fwd)
            le_vfwd  = fst (snd (snd typed_a_fwd))
            evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
            fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
            evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
            cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
            cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
            envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
            evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                          ac1 evB_vfwd envle_fwd
            fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
            crho_ext = mkSigma crho cv_fwd'
            hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
              in adequacySub2 d2 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            wtsub_ext = extSub-WtSub wtsub wfH dA (subst-HasType wtsub wfH d2)
            wfH_ext  = wf-extend (subst-HasType wtsub wfH dA)
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
            eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
            vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

            -- ValTy2 at ef_usel
            fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
            v_fwd_ef = fst fwd_ef
            evA_vfef = fst (snd fwd_ef)
            evB_vfef = snd (snd fwd_ef)
            typed_a_ef = theorem1 d2 rho fits v_fwd_ef evA_vfef
            v_fwd_ef' = fst typed_a_ef
            a_fit_ef  = fst (snd typed_a_ef)
            le_vfef   = fst (snd (snd typed_a_ef))
            evA_vfef' = fst (snd (snd (snd typed_a_ef)))
            fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
            evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
            cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
            cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
            envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
            evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                          ef_usel evB_vfef envle_ef
            fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
            crho_ef   = mkSigma crho cv_fef'
            hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
              in adequacySub2 d2 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

        in app-transport-Val2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef val_app

      transported : Val2 H (App sf sa) (subst1 sB sa) u1 ac1
      transported = appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

  ----------------------------------------------------------------------
  -- adequacyConvSub2 cases (stubs)
  ----------------------------------------------------------------------

  -- Core helper for adequacyConvSub2 ty-App
  adequacyConvSub2-App-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType G f (Pi A B) -> HasType G a A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' -> WfCtx H ->
    (u1 : FinEl) ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma' f) (substExpr sigma' a))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
    d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
    u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    S.Eq-transport (\ T -> EqVal2 H (App sf sa) (App sf' sa') T u1 ac1) (S.Eq-sym eq-sBA) transported
    where
      sf   = substExpr sigma f0
      sf'  = substExpr sigma' f0
      sa   = substExpr sigma a
      sa'  = substExpr sigma' a
      sA   = substExpr sigma A
      sB   = substExpr (liftSub sigma) B
      sBA  = substExpr sigma (subst1 B a)
      eq-sBA : Eq sBA (subst1 sB sa)
      eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

      sing = cons (mkSigma v0 u1) nil
      cv0  = EvalRel-coh a rho v0 evA_v0

      -- Enlarge function via theorem1
      typed_f  = theorem1 d3 rho fits (FunEl sing) evF_sing
      u_big    = fst typed_f
      a_pi     = fst (snd typed_f)
      le_sing  = fst (snd (snd typed_f))
      evF_big  = fst (snd (snd (snd typed_f)))
      fm_big   = fst (snd (snd (snd (snd typed_f))))
      evPi     = snd (snd (snd (snd (snd typed_f))))

      -- EqVal2 for f at two subs
      eqval_f = adequacyConvSub2 d3 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                  u_big evF_big a_pi evPi fm_big

      -- Dispatch on (ub, ap)
      appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        EqVal2 H sf sf' (Pi sA sB) ub ap ->
        EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
      appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
      appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
      appEqVal-dispatch PropCode     ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (SigmaCode _ _) ap () evFb evPab fmba eqvba
      appEqVal-dispatch (PairCode _ _) ap  () evFb evPab fmba eqvba
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) PropCode     lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (SigmaCode _ _) lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PairCode _ _)  lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
        let le_u1_vsel = fst lf
            fmg_big  = fst fmba
            cg_big   = fst (snd fmba)
            piU      = snd (snd fmba)
            b_piU    = fst piU
            allU_fpi = fst (snd piU)
            cf_pi    = snd (snd piU)
            cb_pi    = coh-from-aU b_pi b_piU
            evA_bpi  = fst (snd evPab)
            sb       = selectionBelow g_big v0 (cft-from-cf g_big cg_big) cv0
            u_sel    = fst sb
            v_sel    = fst (snd sb)
            sel_big  = fst (snd (snd sb))
            le_usel  = fst (snd (snd (snd sb)))
            eq_vsel  = snd (snd (snd (snd sb)))
            le_u1_vsel' : LeCode u1 v_sel
            le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel
            cu_sel   = Coherent-Selection sel_big (cft-from-cf g_big cg_big)
            cv_sel   = Coherent-Selection-val sel_big (cft-from-cf g_big cg_big)

            -- Argument evaluation data
            evA_usel = EvalRel-down a rho v0 u_sel crho cu_sel evA_v0 le_usel
            fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cb_pi b_piU

            -- Common coherence
            c_efusel = Coherent-EvalFun f_pi u_sel cf_pi cu_sel

            -- ===== FUNCTION VARIATION: App sf sa vs App sf' sa =====
            eqvpi_fun = snd (snd (snd eqvba))
            A0_eqfun  = fst eqvpi_fun
            B0_eqfun  = fst (snd eqvpi_fun)
            red_eqfun = fst (snd (snd eqvpi_fun))
            uniq_eqfun = Red-unique-Pi2 Red-refl red_eqfun
            eqA_eqfun = fst uniq_eqfun
            eqB_eqfun = snd uniq_eqfun
            paeqv_fun = snd (snd (snd (snd (snd eqvpi_fun))))

            -- Val2 for sa at sA
            val_sa = adequacySub2 d4 sigma rho crho vs fits wtsub wfH u_sel evA_usel b_pi evA_bpi fm_usel_bpi
            val_sa_A0 = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_sa
            ht_sa_A0 = S.Eq-transport (\ X -> HasType H sa X) eqA_eqfun (subst-HasType wtsub wfH d4)

            -- Apply PiAppEqVal2
            eqval_fun_var_raw = paeqv_fun u_sel v_sel sel_big sa ht_sa_A0 val_sa_A0
            eqval_fun_var : EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            eqval_fun_var = S.Eq-transport
              (\ X -> EqVal2 H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_eqfun) eqval_fun_var_raw

            -- ===== ARGUMENT VARIATION: App sf' sa vs App sf' sa' =====
            vpi_sf'  = fst (snd (snd eqvba))
            A0_sf'   = fst vpi_sf'
            B0_sf'   = fst (snd vpi_sf')
            red_sf'  = fst (snd (snd vpi_sf'))
            uniq_sf' = Red-unique-Pi2 Red-refl red_sf'
            eqA_sf'  = fst uniq_sf'
            eqB_sf'  = snd uniq_sf'
            pae_sf'  = snd (snd (snd (snd (snd (snd vpi_sf')))))

            -- HasType and ConvTm for arguments
            htSa     = subst-HasType wtsub wfH d4
            htSa'raw = subst-HasType wtsub' wfH d4
            cvAA'    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
            htSA     = subst-HasType wtsub wfH d1
            htSa'sA  = ty-conv htSa'raw (conv-sym cvAA') htSA
            cvSaSa'  = subst-ConvTm-cross d4 wtsub wtsub' wcs wfH

            -- Transport to A0_sf'
            htSa_A0    = S.Eq-transport (\ X -> HasType H sa X) eqA_sf' htSa
            htSa'_A0   = S.Eq-transport (\ X -> HasType H sa' X) eqA_sf' htSa'sA
            cvSaSa'_A0 = S.Eq-transport (\ X -> ConvTm H sa sa' X) eqA_sf' cvSaSa'

            -- EqVal2 for sa vs sa' via adequacyConvSub2 d4
            eqval_arg = adequacyConvSub2 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                          u_sel evA_usel b_pi evA_bpi fm_usel_bpi
            eqval_arg_A0 = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_sf' eqval_arg

            -- Apply PiAppEq2
            eqval_arg_var_raw = pae_sf' u_sel v_sel sel_big sa sa' htSa_A0 htSa'_A0 cvSaSa'_A0 eqval_arg_A0
            eqval_arg_var : EqVal2 H (App sf' sa) (App sf' sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            eqval_arg_var = S.Eq-transport
              (\ X -> EqVal2 H (App sf' sa) (App sf' sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_sf') eqval_arg_var_raw

            -- ===== COMBINE via EqVal2-trans =====
            eqval_combined = EqVal2-trans v_sel (EvalFun f_pi u_sel) cv_sel c_efusel eqval_fun_var eqval_arg_var

            -- ===== TRANSPORT CHAIN =====
            ef_usel  = EvalFun f_pi u_sel
            cft_fpi  = cf_pi
            le_ef    = EvalFun-mon-arg f_pi u_sel v0 le_usel cft_fpi cu_sel cv0
            evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v0 crho evPab evA_v0
            c_efv    = Coherent-EvalFun f_pi v0 cft_fpi cv0
            evBa_efusel = EvalRel-down (subst1 B a) rho (EvalFun f_pi v0) ef_usel crho c_efusel evBa_efv le_ef
            comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
            c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1
            sup_code = Sup ac1 ef_usel
            c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
            le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel
            ac1_U    = FinMem-a-in-U u1 ac1 fm1
            ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
            sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
            fm_u1_sup = finMem-upward u1 ac1 sup_code le_ac_sup c_ac c_sup fm1 sup_U
            fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big (cft-from-cf g_big cg_big) cf_pi allU_fpi
            fm_vsel_sup = finMem-upward v_sel ef_usel sup_code le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

            -- ValTy2 at Sup
            evU      = mkSigma tt (LeCode-refl UCode tt)
            fwd_ac   = EvalRel-subst1-forward B a rho ac1 crho evAc1
            v_fwd    = fst fwd_ac
            evA_vfwd = fst (snd fwd_ac)
            evB_vfwd = snd (snd fwd_ac)
            typed_a_fwd = theorem1 d4 rho fits v_fwd evA_vfwd
            v_fwd'   = fst typed_a_fwd
            a_fit    = fst (snd typed_a_fwd)
            le_vfwd  = fst (snd (snd typed_a_fwd))
            evA_vfwd' = fst (snd (snd (snd typed_a_fwd)))
            fm_vfwd' = fst (snd (snd (snd (snd typed_a_fwd))))
            evA_afit = snd (snd (snd (snd (snd typed_a_fwd))))
            cv_fwd'  = FinMem-coh-u v_fwd' a_fit fm_vfwd'
            cv_fwd   = EvalRel-coh a rho v_fwd evA_vfwd
            envle_fwd = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fwd (mkSigma cv_fwd' le_vfwd))
            evB_vfwd' = EvalRel-mon-env B (extendEnv rho v_fwd) (extendEnv rho v_fwd')
                          ac1 evB_vfwd envle_fwd
            fits_ext = mkSigma fits (mkSigma a_fit (mkSigma fm_vfwd' evA_afit))
            crho_ext = mkSigma crho cv_fwd'
            htA_loc  = subst-HasType wtsub wfH d1
            wtsub_ext = extSub-WtSub wtsub wfH d1 htSa
            hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
              in adequacySub2 d4 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 d2 (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext wtsub_ext wfH ac1 evB_vfwd' UCode evU ac1_U)
            eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
            vt_ac    = S.Eq-transport (\ T -> ValTy2 H T ac1) eq_comp vt_ac_raw

            fwd_ef   = EvalRel-subst1-forward B a rho ef_usel crho evBa_efusel
            v_fwd_ef = fst fwd_ef
            evA_vfef = fst (snd fwd_ef)
            evB_vfef = snd (snd fwd_ef)
            typed_a_ef = theorem1 d4 rho fits v_fwd_ef evA_vfef
            v_fwd_ef' = fst typed_a_ef
            a_fit_ef  = fst (snd typed_a_ef)
            le_vfef   = fst (snd (snd typed_a_ef))
            evA_vfef' = fst (snd (snd (snd typed_a_ef)))
            fm_vfef'  = fst (snd (snd (snd (snd typed_a_ef))))
            evA_afef  = snd (snd (snd (snd (snd typed_a_ef))))
            cv_fef'   = FinMem-coh-u v_fwd_ef' a_fit_ef fm_vfef'
            cv_fef    = EvalRel-coh a rho v_fwd_ef evA_vfef
            envle_ef  = mkSigma (EnvLe-refl rho crho) (mkSigma cv_fef (mkSigma cv_fef' le_vfef))
            evB_vfef' = EvalRel-mon-env B (extendEnv rho v_fwd_ef) (extendEnv rho v_fwd_ef')
                          ef_usel evB_vfef envle_ef
            fits_ef   = mkSigma fits (mkSigma a_fit_ef (mkSigma fm_vfef' evA_afef))
            crho_ef   = mkSigma crho cv_fef'
            hyp_ef    = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd_ef' u' crho cu' evA_vfef' le_u'
              in adequacySub2 d4 sigma rho crho vs fits wtsub wfH u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 d2 (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef wtsub_ext wfH ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

        in app-transport-EqVal2 ac1 ef_usel comp_ac_ef ac1_U ef_uselU
             v_sel u1 fm_vsel_ef fm1 le_u1_vsel' vt_ac vt_ef eqval_combined

      transported : EqVal2 H (App sf sa) (App sf' sa') (subst1 sB sa) u1 ac1
      transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_f

  adequacyConvSub2 (ty-var {G = G} {i = i} _) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    vcs i u (fst hu) (snd hu) a evA fm

  adequacyConvSub2 (ty-U wfG) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 (ty-U wfG) sigma rho crho vs fits wtsub wfH u hu a evA fm)

  adequacyConvSub2 (ty-Prop wfG) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 (ty-Prop wfG) sigma rho crho vs fits wtsub wfH u hu a evA fm)

  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu UCode evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
    mkSigma tt (mkSigma tt tt)
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA ()
  adequacyConvSub2 {H = H} {M = M} (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu UCode evA fm =
    convSub2-Prop-U-PiCode-aux (theorem1 d rho fits (PiCode a' f') hu)
    where
      convSub2-Prop-U-PiCode-aux :
        Sigma FinEl (\ u' -> Sigma FinEl (\ a_t ->
          Pair (LeCode (PiCode a' f') u')
          (Pair (EvalRel M rho u')
          (Pair (FinMem u' a_t) (EvalRel Prop rho a_t))))) ->
        EqVal2 H (substExpr sigma M) (substExpr sigma' M) U (PiCode a' f') UCode
      convSub2-Prop-U-PiCode-aux (mkSigma Bot (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma UCode (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma PropCode (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (FunEl _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (SigmaCode _ _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (PairCode _ _) (mkSigma _ (mkSigma () _)))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma Bot (mkSigma le (mkSigma hu' (mkSigma () _)))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma UCode (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (FunEl _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (PiCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (SigmaCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma (PairCode _ _) (mkSigma le (mkSigma hu' (mkSigma fmBG (mkSigma _ ()))))))
      convSub2-Prop-U-PiCode-aux (mkSigma (PiCode b g) (mkSigma PropCode (mkSigma le (mkSigma hu' (mkSigma fmBG evProp))))) =
        let fmBG_U = FinMem-Prop-to-U (PiCode b g) fmBG
            eq_bg = adequacyConvSub2 d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
                      (PiCode b g) hu' PropCode (mkSigma tt tt) fmBG
        in restrictEqVal2 H (substExpr sigma M) (substExpr sigma' M) U
             (PiCode b g) (PiCode a' f') UCode le fm fmBG_U eq_bg
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu UCode evA fm =
    let typed = theorem1 d rho fits (SigmaCode _ _) hu
    in sigma-split-cs (fst (snd typed)) (fst typed) (fst (snd (snd typed))) (fst (snd (snd (snd (snd typed))))) (snd (snd (snd (snd (snd typed)))))
    where
      sigma-split-cs : (a_t u' : FinEl) -> LeCode (SigmaCode _ _) u' -> FinMem u' a_t -> EvalRel Prop rho a_t -> _
      sigma-split-cs Bot u' le fm_u' _ =
        absurdEl (S.Eq-transport (\ x -> LeCode (SigmaCode _ _) x) (FinMem-Prop-Bot u' Bot fm_u' tt) le)
      sigma-split-cs PropCode (SigmaCode _ _) le () _
      sigma-split-cs UCode _ _ _ ()
      sigma-split-cs (FunEl _) _ _ _ ()
      sigma-split-cs (PiCode _ _) _ _ _ ()
      sigma-split-cs (SigmaCode _ _) _ _ _ ()
      sigma-split-cs (PairCode _ _) _ _ _ ()
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode _ _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu PropCode (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (SigmaCode _ _) (mkSigma _ ()) fm
  adequacyConvSub2 (ty-Prop-U d) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) (mkSigma _ ()) fm

  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH UCode evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u UCode tt eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl g) evA fm = tt
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA fm =
    let evA'  = convSound-inv d2 rho fits PropCode evA
    in adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA' fm
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu PropCode evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA ()
  adequacyConvSub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        ih    = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits wtsub wfH (PiCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty ih
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-conv d1 d2 dB) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) evA fm = tt

  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu PropCode evA fm =
    EqVal2-UCode-to-PropCode (PiCode b f0) fm
      (adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode
        (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode b f0) fm))
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Pi d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Pi {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b f0) hu UCode evA fm =
    mkSigma valTyPi_s (mkSigma valTyPi_s' (mkSigma valTyPi_s (mkSigma valTyPi_s' eqValTyPi)))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      bodyPi = snd (snd (snd (snd hu)))

      valTyPi_s  = adequacySub2-Pi d1 d2 sigma rho crho vs fits wtsub wfH b f0 hu evA fm
      valTyPi_s' = adequacySub2-Pi d1 d2 sigma' rho crho vs' fits wtsub' wfH b f0 hu evA fm

      eqD1 = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evUU bU
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

      htA_loc  = subst-HasType wtsub wfH d1
      htA'_loc = subst-HasType wtsub' wfH d1
      convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      wtsub_lift  = liftSub-WtSub wtsub wfH d1
      wtsub'_lift_raw = liftSub-WtSub wtsub' wfH d1
      wtsub'_lift : WtSub (extend H sA) (extend G A) (liftSub sigma')
      wtsub'_lift = \ i -> ctx-conv-HasType htA'_loc htA_loc (conv-sym convA) (wtsub'_lift_raw i)
      wcs_lift    = liftSub-WtConvSub wtsub wcs wfH d1
      wfH_ext     = wf-extend htA_loc
      convB       = subst-ConvTm-cross d2 wtsub_lift wtsub'_lift wcs_lift wfH_ext

      buildEdgeCrossBB' : PiEdgeEqTy2 H sA sB sB' b f0
      buildEdgeCrossBB' u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            evU'     = mkSigma tt (LeCode-refl UCode tt)
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext   = ValidSub2-extend sigma P rho u0 vs hyp0
            valP'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valP
            hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext'  = ValidSub2-extend sigma' P rho u0 vs' hyp0'
            hyp0_eq  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         Val2-to-EqVal2 u' a_arg
                           (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a)
            vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs hyp0_eq
            wtsub_ext  = extSub-WtSub wtsub wfH d1 htP
            htP'       = ty-conv htP convA htA'_loc
            wtsub_ext' = extSub-WtSub wtsub' wfH d1 htP'
            wcs_ext  = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
            raw      = adequacyConvSub2 d2 (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                         crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                         v0 evB_u0_v0 UCode evU' fm_v0_U
            eq_B1    = S.Eq-sym (substExpr-comp sigma B P)
            eq_B2    = S.Eq-sym (substExpr-comp sigma' B P)
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB P) T U v0 UCode) eq_B2
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) B) U v0 UCode) eq_B1 raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      eqValTyPi : EqValTyPi2 H (Pi sA sB) (Pi sA' sB') b f0
      eqValTyPi = mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                    (mkSigma Red-refl
                      (mkSigma Red-refl
                        (mkSigma cf (mkSigma allU
                          (mkSigma convA (mkSigma convB
                            (mkSigma eqValTyAA' buildEdgeCrossBB'))))))))))


  adequacyConvSub2 {H = H} (ty-Pi-Prop {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-at-Prop-PP u a hu (snd evA) fm
    where
      adequacyConvSub2-at-Prop-PP : (u0 a0 : FinEl) -> EvalRel (Pi A B) rho u0 -> LeCode a0 PropCode -> FinMem u0 a0 ->
        EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) (Pi (substExpr sigma' A) (substExpr (liftSub sigma') B)) Prop u0 a0
      adequacyConvSub2-at-Prop-PP u0 Bot _ _ fm0 = tt
      adequacyConvSub2-at-Prop-PP u0 UCode _ () _
      adequacyConvSub2-at-Prop-PP Bot PropCode _ _ fm0 = tt
      adequacyConvSub2-at-Prop-PP UCode PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP PropCode PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (FunEl _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (SigmaCode _ _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (PairCode _ _) PropCode _ _ ()
      adequacyConvSub2-at-Prop-PP (PiCode a' f') PropCode hu' _ fm0 =
        adequacyConvSub2 (ty-Pi d1 (ty-Prop-U d2)) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu' UCode
          (mkSigma tt (LeCode-refl UCode tt)) (FinMem-PropCode-to-UCode-full (PiCode a' f') fm0)
      adequacyConvSub2-at-Prop-PP u0 (FunEl _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (PiCode _ _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (SigmaCode _ _) _ () _
      adequacyConvSub2-at-Prop-PP u0 (PairCode _ _) _ () _

  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu UCode evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu PropCode evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Lam d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl g0) hu (PiCode b f0) evA fm =
    mkSigma valTyPi (mkSigma valPi_s (mkSigma valPi_s' eqValPi))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      sM   = substExpr (liftSub sigma) M
      sM'  = substExpr (liftSub sigma') M
      evU  = mkSigma tt (LeCode-refl UCode tt)
      fmg  = fst fm
      cg   = fst (snd fm)
      pU   = snd (snd fm)
      bU   = fst pU
      allU = fst (snd pU)
      cf0  = snd (snd pU)
      cb   = coh-from-aU b bU
      evAb = fst (snd evA)
      a_lam = fst hu
      bodyLam = snd (snd (snd (snd hu)))
      htA_loc  = subst-HasType wtsub wfH d1
      htA'_loc = subst-HasType wtsub' wfH d1
      convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      wfH'     = wf-extend htA_loc

      -- Domain EqValTy2
      eqD = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evU bU
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD

      -- ValTyPi2 and ValPi2 from sigma side
      valTyPi = adequacySub2 (ty-Pi d1 d2) sigma rho crho vs fits wtsub wfH
                  (PiCode b f0) evA UCode evU pU
      val_s   = adequacySub2-Lam d1 d2 d3 sigma rho crho vs fits wtsub wfH g0 hu b f0 evA fm
      valPi_s = snd val_s

      -- Cross-body helper
      buildCrossBody : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        (N : Expr _) -> HasType H N sA -> Val2 H N sA u0 b ->
        EqVal2 H (App (Lam sA sM) N) (App (Lam sA' sM') N) (subst1 sB N) v0 (EvalFun f0 u0)
      buildCrossBody u0 v0 sel N htN valN =
        let cu0       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u0_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v0_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u0 v0 sel
            x         = fst w
            le_x_u0   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v0  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evM_u0_v0 = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u0) v0 evM_x_v0 envle_xu
            evB_u0_ef = EvalRel-Pi-body A B rho b f0 u0 crho cu0 evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'     = mkSigma crho cu0
            -- ValidSub2 for extSub sigma N
            hyp0_s    = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs_ext    = ValidSub2-extend sigma N rho u0 vs hyp0_s
            -- ValidSub2 for extSub sigma' N (need Val2 at sA')
            valN'     = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valN
            hyp0_s'   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b N valN' u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs_ext'   = ValidSub2-extend sigma' N rho u0 vs' hyp0_s'
            -- ValidConvSub2 for cross-subs with same N
            hyp0_eq   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          Val2-to-EqVal2 u'' a_arg
                            (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a)
            vcs_ext   = ValidConvSub2-extend sigma sigma' N N rho u0 vcs hyp0_eq
            -- WtSub/WtConvSub
            wtsub_ext  = extSub-WtSub wtsub wfH d1 htN
            htN'       = ty-conv htN convA htA'_loc
            wtsub_ext' = extSub-WtSub wtsub' wfH d1 htN'
            wcs_ext    = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htN)
            -- adequacyConvSub2 d3 with cross-subs
            raw        = adequacyConvSub2 d3 (extSub sigma N) (extSub sigma' N) (extendEnv rho u0)
                           crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                           v0 evM_u0_v0 (EvalFun f0 u0) evB_u0_ef fm_v0_ef
            -- Transport to subst1 forms
            eq_M1      = S.Eq-sym (substExpr-comp sigma M N)
            eq_M2      = S.Eq-sym (substExpr-comp sigma' M N)
            eq_B1      = S.Eq-sym (substExpr-comp sigma B N)
            raw'       = S.Eq-transport (\ T -> EqVal2 H (subst1 sM N) T (subst1 sB N) v0 (EvalFun f0 u0)) eq_M2
                           (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' N) M) (subst1 sB N) v0 (EvalFun f0 u0)) eq_M1
                             (S.Eq-transport (\ T -> EqVal2 H _ _ T v0 (EvalFun f0 u0)) eq_B1 raw))
        in EqVal2-headred-expand v0 (EvalFun f0 u0)
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl) raw'

      -- piAppVal2 for sigma' side
      piAppVal2_s' : PiAppVal2 H (Lam sA' sM') sA sB b f0 g0
      piAppVal2_s' u0 v0 sel N htN valN =
        Val2-from-EqVal2-second v0 (EvalFun f0 u0) (buildCrossBody u0 v0 sel N htN valN)

      -- piAppEq2 for sigma' side
      piAppEq2_s' : PiAppEq2 H (Lam sA' sM') sA sB b f0 g0
      piAppEq2_s' u0 v0 sel N1 N2 htN1 htN2 cvN eqvalN =
        let cu0       = Coherent-Selection sel (cft-from-cf g0 cg)
            fm_u0_b   = FinMem-Selection b f0 sel fmg (cft-from-cf g0 cg) cb bU
            fm_v0_ef  = FinMem-Selection-codomain b f0 sel fmg (cft-from-cf g0 cg) cf0 allU
            w         = bodyLam u0 v0 sel
            x         = fst w
            le_x_u0   = fst (snd w)
            fm_x_al   = fst (snd (snd w))
            evM_x_v0  = snd (snd (snd w))
            cx        = FinMem-coh-u x a_lam fm_x_al
            envle_xu  = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evM_u0_v0 = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u0) v0 evM_x_v0 envle_xu
            evB_u0_ef = EvalRel-Pi-body A B rho b f0 u0 crho cu0 evA
            fits'     = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'     = mkSigma crho cu0
            c_ef_u0   = Coherent-EvalFun f0 u0 cf0 cu0
            fm_ef_U   = EvalFun-in-UCode f0 u0 b cf0 cu0 allU
            -- Convert inputs to sA' for sigma' side
            htN1'     = ty-conv htN1 convA htA'_loc
            htN2'     = ty-conv htN2 convA htA'_loc
            cvN'      = conv-conv cvN convA htA'_loc
            valN1     = Val2-from-EqVal2-first u0 b eqvalN
            valN2     = Val2-from-EqVal2-second u0 b eqvalN
            valN1'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valN1
            valN2'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valN2
            eqvalN'   = EqVal2-EqValTy2-fwd u0 b cb eqValTyAA' eqvalN
            -- ValidSub2 for extSub sigma' N1 and N2
            hyp0_N1'  = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b N1 valN1' u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            hyp0_N2'  = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b N2 valN2' u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs_ext_N1' = ValidSub2-extend sigma' N1 rho u0 vs' hyp0_N1'
            vs_ext_N2' = ValidSub2-extend sigma' N2 rho u0 vs' hyp0_N2'
            vcs_ext'  = ValidConvSub2-extend sigma' sigma' N1 N2 rho u0
                          (ValidConvSub2-refl {G = G} vs')
                          (transportEqVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b eqvalN')
            wtsub_ext_N1' = extSub-WtSub wtsub' wfH d1 htN1'
            wtsub_ext_N2' = extSub-WtSub wtsub' wfH d1 htN2'
            wcs_ext'  = extSub-WtConvSub wtsub' (WtConvSub-refl {G = G} wtsub') wfH d1 cvN'
            -- adequacyConvSub2 d3 for sigma'/sigma' cross-terms
            raw_s'    = adequacyConvSub2 d3 (extSub sigma' N1) (extSub sigma' N2) (extendEnv rho u0)
                          crho' vs_ext_N1' vs_ext_N2' vcs_ext' fits' wtsub_ext_N1' wtsub_ext_N2' wcs_ext' wfH
                          v0 evM_u0_v0 (EvalFun f0 u0) evB_u0_ef fm_v0_ef
            -- Transport raw_s' to subst1 forms at type sB'
            eq_M'1    = S.Eq-sym (substExpr-comp sigma' M N1)
            eq_M'2    = S.Eq-sym (substExpr-comp sigma' M N2)
            eq_B'1    = S.Eq-sym (substExpr-comp sigma' B N1)
            raw_s'_tr = S.Eq-transport (\ T -> EqVal2 H (subst1 sM' N1) T (subst1 sB' N1) v0 (EvalFun f0 u0)) eq_M'2
                          (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' N2) M) (subst1 sB' N1) v0 (EvalFun f0 u0)) eq_M'1
                            (S.Eq-transport (\ T -> EqVal2 H _ _ T v0 (EvalFun f0 u0)) eq_B'1 raw_s'))
            -- Type conversion from sB' to sB via adequacyConvSub2 d2
            hyp0_N1_s = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs_ext_N1  = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1_s
            hyp0_eq_N1 = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          Val2-to-EqVal2 u'' a_arg
                            (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a)
            vcs_ext_N1 = ValidConvSub2-extend sigma sigma' N1 N1 rho u0 vcs hyp0_eq_N1
            wtsub_ext_N1 = extSub-WtSub wtsub wfH d1 htN1
            wcs_ext_N1 = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htN1)
            evU'       = mkSigma tt (LeCode-refl UCode tt)
            type_cv_raw = adequacyConvSub2 d2 (extSub sigma N1) (extSub sigma' N1) (extendEnv rho u0)
                            crho' vs_ext_N1 vs_ext_N1' vcs_ext_N1 fits' wtsub_ext_N1 wtsub_ext_N1' wcs_ext_N1 wfH
                            (EvalFun f0 u0) evB_u0_ef UCode evU' fm_ef_U
            eq_tB1     = S.Eq-sym (substExpr-comp sigma B N1)
            eq_tB2     = S.Eq-sym (substExpr-comp sigma' B N1)
            type_cv_tr = S.Eq-transport (\ T -> EqVal2 H (subst1 sB N1) T U (EvalFun f0 u0) UCode) eq_tB2
                           (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' N1) B) U (EvalFun f0 u0) UCode) eq_tB1 type_cv_raw)
            eqValTy_BB' = EqVal2-U-to-EqValTy2 (EvalFun f0 u0) fm_ef_U type_cv_tr
            eqValTy_B'B = EqValTy2-sym (EvalFun f0 u0) c_ef_u0 eqValTy_BB'
            -- Convert EqVal2 from type sB' to sB
            raw_conv  = EqVal2-EqValTy2-fwd v0 (EvalFun f0 u0) c_ef_u0 eqValTy_B'B raw_s'_tr
        in EqVal2-headred-expand v0 (EvalFun f0 u0)
             (headred-step headred-beta headred-refl) (headred-step headred-beta headred-refl) raw_conv

      -- ValPi2 for sigma' at type (Pi sA sB)
      valPi_s' : ValPi2 H (Lam sA' sM') (Pi sA sB) g0 b f0
      valPi_s' = mkSigma sA (mkSigma sB (mkSigma Red-refl
                   (mkSigma cg (mkSigma fmg (mkSigma piAppVal2_s' piAppEq2_s')))))

      -- EqValPi2: uses buildCrossBody directly
      eqValPi : EqValPi2 H (Lam sA sM) (Lam sA' sM') (Pi sA sB) g0 b f0
      eqValPi = mkSigma sA (mkSigma sB (mkSigma Red-refl
                  (mkSigma cg (mkSigma fmg
                    (\ u0 v0 sel P htP valP -> buildCrossBody u0 v0 sel P htP valP)))))

  -- ty-App: decompose into function variation + argument variation + EqVal2-trans
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu Bot evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm =
    mkSigma tt (mkSigma tt tt)
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu Bot evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (PiCode _ _) evA ()
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b0pc f0pc) hu PropCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) PropCode evA fm
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu Bot evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (PairCode _ _) evA ()
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu Bot evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu Bot evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu UCode evA fm = {!!} -- pre-existing: needs ValTySigma2
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu Bot evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-App d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (PairCode _ _) evA fm = tt
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode b0pc f0pc) hu UCode evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (PiCode b0pc f0pc) (fst hu) (fst (snd hu)) (snd (snd hu)) UCode evA fm
  adequacyConvSub2 {H = H} (ty-App {A = A} {B = B} {f = f0} {a = a} d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl gfe) hu (PiCode bacfe facfe) evA fm =
    adequacyConvSub2-App-core {H = H} {A = A} {B = B} {f = f0} {a = a}
      d1 d2 d3 d4 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH
      (FunEl gfe) (fst hu) (fst (snd hu)) (snd (snd hu)) (PiCode bacfe facfe) evA fm

  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) () a evA fm
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu Bot evA fm = tt
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (FunEl _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (PiCode _ _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu PropCode evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (SigmaCode _ _) evA ()
  adequacyConvSub2 (ty-Sigma d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu (PairCode _ _) evA ()
  adequacyConvSub2 {H = H} {G = G} (ty-Sigma {A = A} {B = B} d1 d2) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode b f0) hu UCode evA fm =
    mkSigma valTySig_s (mkSigma valTySig_s' (mkSigma valTySig_s (mkSigma valTySig_s' eqValTySig)))
    where
      sA   = substExpr sigma A
      sA'  = substExpr sigma' A
      sB   = substExpr (liftSub sigma) B
      sB'  = substExpr (liftSub sigma') B
      bU   = fst fm
      allU = fst (snd fm)
      cf   = snd (snd fm)
      cb   = coh-from-aU b bU
      evUU = mkSigma tt (LeCode-refl UCode tt)
      evAb = fst (snd hu)
      bodyPi = snd (snd (snd (snd hu)))

      valTySig_s  = adequacySub2-Sigma d1 d2 sigma rho crho vs fits wtsub wfH b f0 hu evA fm
      valTySig_s' = adequacySub2-Sigma d1 d2 sigma' rho crho vs' fits wtsub' wfH b f0 hu evA fm

      eqD1 = adequacyConvSub2 d1 sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH b evAb UCode evUU bU
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

      htA_loc  = subst-HasType wtsub wfH d1
      htA'_loc = subst-HasType wtsub' wfH d1
      convA    = subst-ConvTm-cross d1 wtsub wtsub' wcs wfH
      wtsub_lift  = liftSub-WtSub wtsub wfH d1
      wtsub'_lift_raw = liftSub-WtSub wtsub' wfH d1
      wtsub'_lift : WtSub (extend H sA) (extend G A) (liftSub sigma')
      wtsub'_lift = \ i -> ctx-conv-HasType htA'_loc htA_loc (conv-sym convA) (wtsub'_lift_raw i)
      wcs_lift    = liftSub-WtConvSub wtsub wcs wfH d1
      wfH_ext     = wf-extend htA_loc
      convB       = subst-ConvTm-cross d2 wtsub_lift wtsub'_lift wcs_lift wfH_ext

      buildEdgeCrossBB' : SigmaEdgeEqTy2 H sA sB sB' b f0
      buildEdgeCrossBB' u0 v0 sel P htP valP =
        let fm_u0_b  = FinMemAllU-Selection b sel allU cf cb bU
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            cu0      = FinMem-coh-u u0 b fm_u0_b
            w        = bodyPi u0 v0 sel
            x        = fst w
            le_x_u0  = fst (snd w)
            fm_x_a'  = fst (snd (snd w))
            evB_x_v0 = snd (snd (snd w))
            cx       = FinMem-coh-u x (fst (snd (snd hu))) fm_x_a'
            envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
            evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
            fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
            crho'    = mkSigma crho cu0
            evU'     = mkSigma tt (LeCode-refl UCode tt)
            hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext   = ValidSub2-extend sigma P rho u0 vs hyp0
            valP'    = Val2-EqValTy2-fwd u0 b cb eqValTyAA' valP
            hyp0'    = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         transportVal2 d1 d2 sigma' rho crho vs' fits wtsub' wfH b bU evAb u0 fm_u0_b P valP' u' cu' le_u' a_arg evA_arg fm_u'_a
            vs_ext'  = ValidSub2-extend sigma' P rho u0 vs' hyp0'
            hyp0_eq  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                         Val2-to-EqVal2 u' a_arg
                           (transportVal2 d1 d2 sigma rho crho vs fits wtsub wfH b bU evAb u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a)
            vcs_ext  = ValidConvSub2-extend sigma sigma' P P rho u0 vcs hyp0_eq
            wtsub_ext  = extSub-WtSub wtsub wfH d1 htP
            htP'       = ty-conv htP convA htA'_loc
            wtsub_ext' = extSub-WtSub wtsub' wfH d1 htP'
            wcs_ext  = extSub-WtConvSub wtsub wcs wfH d1 (conv-refl htP)
            raw      = adequacyConvSub2 d2 (extSub sigma P) (extSub sigma' P) (extendEnv rho u0)
                         crho' vs_ext vs_ext' vcs_ext fits' wtsub_ext wtsub_ext' wcs_ext wfH
                         v0 evB_u0_v0 UCode evU' fm_v0_U
            eq_B1    = S.Eq-sym (substExpr-comp sigma B P)
            eq_B2    = S.Eq-sym (substExpr-comp sigma' B P)
            raw'     = S.Eq-transport (\ T -> EqVal2 H (subst1 sB P) T U v0 UCode) eq_B2
                         (S.Eq-transport (\ T -> EqVal2 H T (substExpr (extSub sigma' P) B) U v0 UCode) eq_B1 raw)
        in EqVal2-U-to-EqValTy2 v0 fm_v0_U raw'

      eqValTySig : EqValTySigma2 H (SigmaE sA sB) (SigmaE sA' sB') b f0
      eqValTySig = mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                    (mkSigma Red-refl
                      (mkSigma Red-refl
                        (mkSigma cf (mkSigma allU
                          (mkSigma convA (mkSigma convB
                            (mkSigma eqValTyAA' buildEdgeCrossBB'))))))))))


  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm =
    EqVal2-Bot a
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) () a evA fm
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu Bot evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu UCode evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu PropCode evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (FunEl _) evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (PiCode _ _) evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2 (ty-MkPair d1 d2 d3 d4) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode u' v') hu (PairCode _ _) evA fm = tt

  adequacyConvSub2 (ty-Fst dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-Fst-Snd (ty-Fst dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

  adequacyConvSub2 (ty-Snd dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm =
    adequacyConvSub2-Fst-Snd (ty-Snd dA dB dM) sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu a evA fm

  -- adequacyConvSub2-Fst-Snd: cross-sub helper for Fst/Snd
  -- Uses adequacySub2 from both sigma sides and type equality from adequacyConvSub2 on the type
  adequacyConvSub2-Fst-Snd : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu Bot evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu a evA fm = EqVal2-Bot a
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode a' f') hu PropCode evA fm =
    {!!} -- TODO: Fst-Snd cross-sub at (PiCode, PropCode)
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu PropCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu PropCode evA ()
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (FunEl _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu (SigmaCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PairCode _ _) evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH Bot hu UCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH UCode hu UCode evA fm = mkSigma tt (mkSigma tt tt)
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH PropCode hu UCode evA fm =  tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (FunEl _) hu UCode evA fm = mkSigma tt (mkSigma tt tt)
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PairCode _ _) hu UCode evA fm = tt
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (PiCode _ _) hu UCode evA fm = {!!}
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH (SigmaCode _ _) hu UCode evA fm = {!!}
  adequacyConvSub2-Fst-Snd d sigma sigma' rho crho vs vs' vcs fits wtsub wtsub' wcs wfH u hu (PiCode b f) evA fm =
    {!!} -- TODO: Fst-Snd cross-sub at PiCode — needs correct eval witness for type

  -- Pipe operator for theorem1 result
  _|>_ : {A B : Set} -> A -> (A -> B) -> B
  x |> f = f x

------------------------------------------------------------------------
-- Part 8: Closed-term corollary
------------------------------------------------------------------------

adequacy2 : {M A : Expr zero} ->
  HasType empty M A ->
  (rho : EnvApprox zero) ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val2 empty M A u a
adequacy2 {M} {A} d emptyEnv u hu a evA fm =
  let wfEmpty = typing-WfCtx d
      wsId    = idSub-WtSub wfEmpty
  in Val2-transport-M {u = u} {a = a} (substExpr-id M)
       (Val2-transport-A {u = u} {a = a} (substExpr-id A)
         (adequacySub2 d idSub emptyEnv tt (ValidSub2-empty idSub emptyEnv) tt wsId wfEmpty u hu a evA fm))
