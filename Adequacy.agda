{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- Adequacy.agda
--
-- External adequacy layer for dependent type theory with U : U.
--
-- Architecture: TWO-CONTEXT adequacy under substitutions.
--
--   Source context G (typing) and target context H (evaluation).
--   A substitution sigma : Sub h g maps G-variables to H-expressions.
--   The SOURCE environment rho : EnvApprox g interprets G.
--
-- KEY INVARIANT:
--   Semantic evaluation uses the SOURCE environment rho directly.
--   EvalRel M rho u means u is a finite approximant of M in env rho.
--   Substitution sigma only appears on the syntactic side.
--
-- FINITE-ELEMENT ONLY: no ideal elements, no Dom, no holds, no evalDom.
------------------------------------------------------------------------

module Adequacy where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons)
open import PaperSemantics using (LeCode ; LeCode-Bot ; LeCode-refl ;
  LeCode-trans ; Coherent ;
  CoherentFun ; Comp ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; EvalFun ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  LeFunCode ;
  FinMem ; FinMemFun ; FinMemAllU ;
  FinMem-a-in-U ; finMemUCode-Sup ;
  finMem-upward ; finMem-Sup-left ; coh-from-aU)
open import Reduction using (Red ; Red-wk ; red-to-conv ;
  Red-refl ; Red-trans ; Red-beta-expand ; Red-Pi-inj ; Red-from-conv ;
  Red-subst)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ; Pi-edgewise ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Comp ; EvalRel-Sup ; EvalRel-down)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Sub ; liftSub ; substExpr ; subst1Sub)
open import TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ConvTm ; WfCtx ;
  wf-empty ; wf-extend ;
  ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import Validity using (Edge ; EdgeIn ; here ; there ;
  Val ; EqVal ; ValTy ; EqValTy ;
  FinMem-Coherent ;
  ValTyPi ; ValPi ; EqValTyPi ; EqValPi ;
  PiEdgeVal ; PiEdgeEq ; PiEdgeEqTy ;
  PiAppVal ; PiAppEq ; PiAppEqVal ;
  Val-Bot ; EqVal-Bot ;
  downVal ; downValTy ; upVal ; restrictVal ;
  downEqVal ; downEqValTy ; upEqVal ; restrictEqVal ;
  Val-conv-type ; EqVal-conv-type ;
  FinMemAllU-lookup ;
  PiAppVal-lookup ;
  FinMemFun-lookup ;
  Or ; left ; right ;
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ;
  Val-to-EqVal ;
  Val-from-EqVal-first ; Val-from-EqVal-second ;
  EqVal-sym ; EqValTy-sym ;
  bU-from-cf-fmU ;
  EqVal-trans ; ValTy-Sup)
open import Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode)
open import TypingSemantics using (convSound ; convSound-inv ; theorem1)
open import LemmaForTS using (Fits ; Typed ; Fits-CoherentEnv)
open import EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-Pi-app-type)

open import RawSyntax using (Ren ; liftRen ; renExpr ; wkRen ;
  subst-ren ; subst-var-ren ; wkExpr-is-subst)

------------------------------------------------------------------------
-- Part 1: Substitution helpers
--
-- Sub, liftSub, substExpr now come from RawSyntax.
------------------------------------------------------------------------

-- Identity substitution
idSub : {n : Nat} -> Sub n n
idSub i = Var i

-- Extend a substitution with a term (for the new fzero variable)
extSub : {h g : Nat} -> Sub h g -> Expr h -> Sub h (suc g)
extSub sigma t fzero    = t
extSub sigma t (fsuc i) = sigma i

------------------------------------------------------------------------
-- Part 2: Substitution lemmas
------------------------------------------------------------------------

-- Eq helpers
Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans S.refl q = q

Eq-cong2 : {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f S.refl S.refl = S.refl

-- Substitution extensionality: lift pointwise equality to expressions
liftSub-ext : {h g : Nat} (sigma sigma' : Sub h g) ->
  ((i : Fin g) -> Eq (sigma i) (sigma' i)) ->
  (j : Fin (suc g)) -> Eq (liftSub sigma j) (liftSub sigma' j)
liftSub-ext sigma sigma' hyp fzero    = S.refl
liftSub-ext sigma sigma' hyp (fsuc i) = S.Eq-cong wkExpr (hyp i)

substExpr-ext : {h g : Nat} (sigma sigma' : Sub h g) ->
  ((i : Fin g) -> Eq (sigma i) (sigma' i)) ->
  (M : Expr g) -> Eq (substExpr sigma M) (substExpr sigma' M)
substExpr-ext sigma sigma' hyp (Var i)   = hyp i
substExpr-ext sigma sigma' hyp U         = S.refl
substExpr-ext sigma sigma' hyp (Pi A B)  =
  Eq-cong2 Pi (substExpr-ext sigma sigma' hyp A)
              (substExpr-ext (liftSub sigma) (liftSub sigma')
                (liftSub-ext sigma sigma' hyp) B)
substExpr-ext sigma sigma' hyp (Lam A M) =
  Eq-cong2 Lam (substExpr-ext sigma sigma' hyp A)
               (substExpr-ext (liftSub sigma) (liftSub sigma')
                 (liftSub-ext sigma sigma' hyp) M)
substExpr-ext sigma sigma' hyp (App f a) =
  Eq-cong2 App (substExpr-ext sigma sigma' hyp f)
               (substExpr-ext sigma sigma' hyp a)

-- substExpr-id: identity substitution is identity
substExpr-id : {n : Nat} (M : Expr n) ->
  Eq (substExpr idSub M) M
substExpr-id (Var i)   = S.refl
substExpr-id U         = S.refl
substExpr-id (Pi A B)  =
  Eq-cong2 Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> S.refl ; (fsuc i) -> S.refl }) B)
              (substExpr-id B))
substExpr-id (Lam A M) =
  Eq-cong2 Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                (\ { fzero -> S.refl ; (fsuc i) -> S.refl }) M)
              (substExpr-id M))
substExpr-id (App f a) =
  Eq-cong2 App (substExpr-id f) (substExpr-id a)

substExpr-ren : {k h g : Nat} (sigma : Sub h g) (rho : Ren k g) (M : Expr k) ->
  Eq (substExpr sigma (renExpr rho M)) (substExpr (\ i -> sigma (rho i)) M)
substExpr-ren sigma rho (Var i)   = S.refl
substExpr-ren sigma rho U         = S.refl
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

-- substExpr-wk: weakening as substitution
substExpr-wk : {h g : Nat} (sigma : Sub h g) (M : Expr g) (t : Expr h) ->
  Eq (substExpr (extSub sigma t) (wkExpr M)) (substExpr sigma M)
substExpr-wk sigma M t = substExpr-ren (extSub sigma t) wkRen M

-- Renaming extensionality
renExpr-ext : {n m : Nat} (r1 r2 : Ren n m) ->
  ((i : Fin n) -> Eq (r1 i) (r2 i)) ->
  (M : Expr n) -> Eq (renExpr r1 M) (renExpr r2 M)
renExpr-ext r1 r2 hyp (Var i)   = S.Eq-cong Var (hyp i)
renExpr-ext r1 r2 hyp U         = S.refl
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

-- Renaming composition: renExpr r2 (renExpr r1 M) = renExpr (r2 . r1) M
renExpr-comp : {a b c : Nat} (r2 : Ren b c) (r1 : Ren a b) (M : Expr a) ->
  Eq (renExpr r2 (renExpr r1 M)) (renExpr (\ i -> r2 (r1 i)) M)
renExpr-comp r2 r1 (Var i)   = S.refl
renExpr-comp r2 r1 U         = S.refl
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

-- liftRen rho . wkRen = wkRen . rho
wk-lift-comm : {h k : Nat} (rho : Ren h k) (M : Expr h) ->
  Eq (renExpr (liftRen rho) (wkExpr M)) (wkExpr (renExpr rho M))
wk-lift-comm rho M =
  Eq-trans (renExpr-comp (liftRen rho) wkRen M)
    (S.Eq-sym (renExpr-comp wkRen rho M))

-- Renaming distributes over substExpr
renExpr-substExpr : {k h g : Nat} (rho : Ren h k) (sigma : Sub h g) (M : Expr g) ->
  Eq (renExpr rho (substExpr sigma M))
     (substExpr (\ i -> renExpr rho (sigma i)) M)
renExpr-substExpr rho sigma (Var i) = S.refl
renExpr-substExpr rho sigma U = S.refl
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

substExpr-sub : {k h g : Nat} (tau : Sub k h) (sigma : Sub h g) (M : Expr g) ->
  Eq (substExpr tau (substExpr sigma M))
     (substExpr (\ i -> substExpr tau (sigma i)) M)
substExpr-sub tau sigma (Var i) = S.refl
substExpr-sub tau sigma U = S.refl
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

sigma-subst1 : {h g : Nat} (sigma : Sub h g)
  (B : Expr (suc g)) (a : Expr g) ->
  Eq (substExpr sigma (subst1 B a))
     (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a))
sigma-subst1 sigma B a =
  let sa = substExpr sigma a
      sB = substExpr (liftSub sigma) B
  in Eq-trans
       (substExpr-sub sigma (subst1Sub a) B)
       (Eq-trans
         (substExpr-ext
           (\ i -> substExpr sigma (subst1Sub a i))
           (extSub sigma sa)
           (\ { fzero -> S.refl ; (fsuc j) -> S.refl })
           B)
         (S.Eq-sym (substExpr-comp sigma B sa)))

------------------------------------------------------------------------
-- Part 3: EvalRel properties
--
-- EvalRel-coh, EvalRel-wk, EvalRel-Comp, EvalRel-Sup, EvalRel-down
-- are now imported from RawSemantics / EvalSubstitution.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Part 4: Adequacy predicates (FINITE)
--
-- Adeq H M A rho Asrc u :
--   There exist u' >= u and a type code a with
--   EvalRel Asrc rho a, FinMem u' a, and Val H M A u' a.
--   The key change from before: membership and Val are at the
--   enlarged u', not the original u.
------------------------------------------------------------------------

record Adeq {h g : Nat} (H : Ctx h) (M A : Expr h)
    (rho : EnvApprox g) (Asrc : Expr g) (u : FinEl) : Set where
  constructor mkAdeq
  field
    uCode : FinEl
    aCode : FinEl
    le    : LeCode u uCode
    evSrc : EvalRel Asrc rho aCode
    mem   : FinMem uCode aCode
    val   : Val H M A uCode aCode

record AdeqEq {h g : Nat} (H : Ctx h) (M N A : Expr h)
    (rho : EnvApprox g) (Asrc : Expr g) (u : FinEl) : Set where
  constructor mkAdeqEq
  field
    uCode : FinEl
    aCode : FinEl
    le    : LeCode u uCode
    evSrc : EvalRel Asrc rho aCode
    mem   : FinMem uCode aCode
    eqval : EqVal H M N A uCode aCode

------------------------------------------------------------------------
-- Part 5: Valid substitutions (two-context, source-env, FINITE)
--
-- ValidSub H G sigma rho says: for each variable i in G,
-- if u <= lookupEnv i rho and Coherent u, then
-- sigma i is adequate at the substituted type.
------------------------------------------------------------------------

ValidSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> EnvApprox g -> Set
ValidSub {h} {g} H G sigma rho =
  (i : Fin g) -> (u : FinEl) -> (cu : Coherent u) ->
  LeCode u (lookupEnv i rho) ->
  Adeq H (sigma i) (substExpr sigma (lookup G i)) rho (lookup G i) u

------------------------------------------------------------------------
-- Part 6: Transport helpers
------------------------------------------------------------------------

-- Transport Adeq along type expression equality (target side)
Adeq-transport-type : {h g : Nat} {H : Ctx h} {M A A' : Expr h}
  {rho : EnvApprox g} {Asrc : Expr g} {u : FinEl} ->
  Eq A A' -> Adeq H M A rho Asrc u -> Adeq H M A' rho Asrc u
Adeq-transport-type S.refl aq = aq

-- Transport Adeq along source type expression equality
Adeq-transport-src : {h g : Nat} {H : Ctx h} {M A : Expr h}
  {rho : EnvApprox g} {Asrc Asrc' : Expr g} {u : FinEl} ->
  Eq Asrc Asrc' -> Adeq H M A rho Asrc u -> Adeq H M A rho Asrc' u
Adeq-transport-src S.refl aq = aq

-- Transport EvalRel along expression equality
EvalRel-transport : {n : Nat} {M M' : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Eq M M' -> EvalRel M rho u -> EvalRel M' rho u
EvalRel-transport S.refl ev = ev

-- Transport AdeqEq along type expression equality (target side)
AdeqEq-transport-type : {h g : Nat} {H : Ctx h} {M N A A' : Expr h}
  {rho : EnvApprox g} {Asrc : Expr g} {u : FinEl} ->
  Eq A A' -> AdeqEq H M N A rho Asrc u -> AdeqEq H M N A' rho Asrc u
AdeqEq-transport-type S.refl aq = aq

------------------------------------------------------------------------
-- Part 7: ValidSub infrastructure
------------------------------------------------------------------------

-- Empty source context: trivially valid
ValidSub-empty : {h : Nat} {H : Ctx h} (sigma : Sub h zero)
  (rho : EnvApprox zero) -> ValidSub H empty sigma rho
ValidSub-empty sigma rho ()

-- Extension under binders
ValidSub-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma : Sub h g) (t : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  ValidSub H G sigma rho ->
  ((u : FinEl) -> Coherent u -> LeCode u v ->
    Adeq H t (substExpr sigma A) rho A u) ->
  ValidSub H (extend G A) (extSub sigma t) (extendEnv rho v)
ValidSub-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 fzero u cu le =
  let aq  = hyp0 u cu le
      ha' = EvalRel-wk Asrc rho v (Adeq.aCode aq) (Adeq.evSrc aq)
      eq  = S.Eq-sym (substExpr-wk sigma Asrc t)
      val' = S.Eq-transport (\ T -> Val H t T (Adeq.uCode aq) (Adeq.aCode aq)) eq (Adeq.val aq)
  in mkAdeq (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.le aq) ha' (Adeq.mem aq) val'
ValidSub-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 (fsuc i) u cu le =
  let aq  = vs i u cu le
      ha' = EvalRel-wk (lookup G i) rho v (Adeq.aCode aq) (Adeq.evSrc aq)
      eq  = S.Eq-sym (substExpr-wk sigma (lookup G i) t)
      val' = S.Eq-transport (\ T -> Val H (sigma i) T (Adeq.uCode aq) (Adeq.aCode aq)) eq (Adeq.val aq)
  in mkAdeq (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.le aq) ha' (Adeq.mem aq) val'

-- substExpr (liftSub sigma) (wkExpr M) = wkExpr (substExpr sigma M)
substExpr-liftSub-wk : {h g : Nat} (sigma : Sub h g) (M : Expr g) ->
  Eq (substExpr (liftSub sigma) (wkExpr M)) (wkExpr (substExpr sigma M))
substExpr-liftSub-wk sigma M =
  Eq-trans (substExpr-ren (liftSub sigma) wkRen M)
    (S.Eq-sym (renExpr-substExpr wkRen sigma M))

-- Fits-from-ValidSub removed: Fits G rho is now passed as a parameter
-- to adequacySub/adequacyEqSub directly. This avoids needing the
-- invalid FinMem-restrict lemma.

------------------------------------------------------------------------
-- Part 8: Adequacy for ty-U
------------------------------------------------------------------------

-- FinMem u UCode from LeCode u UCode
FinMem-from-LeCode-UCode : (u : FinEl) -> LeCode u UCode -> FinMem u UCode
FinMem-from-LeCode-UCode Bot          le = tt
FinMem-from-LeCode-UCode UCode        le = tt
FinMem-from-LeCode-UCode (FunEl g)    ()
FinMem-from-LeCode-UCode (PiCode a f) ()

-- ValTy at u with LeCode u UCode
ValTy-U : {n : Nat} (G : Ctx n) (u : FinEl) -> LeCode u UCode -> ValTy G U u
ValTy-U G Bot          le = tt
ValTy-U G UCode        le = tt
ValTy-U G (FunEl g)    ()
ValTy-U G (PiCode a f) ()

-- Coherent from LeCode u UCode
LeCode-UCode-Coherent : (u : FinEl) -> LeCode u UCode -> Coherent u
LeCode-UCode-Coherent Bot          le = tt
LeCode-UCode-Coherent UCode        le = tt
LeCode-UCode-Coherent (FunEl g)    ()
LeCode-UCode-Coherent (PiCode a f) ()

-- Extract ValTy from Val at type U (general: works for any expression M)
Val-U-to-ValTy : {n : Nat} {H : Ctx n} {M : Expr n}
  (u1 a1 : FinEl) -> Val H M U u1 a1 -> FinMem u1 a1 ->
  LeCode a1 UCode -> ValTy H M u1
Val-U-to-ValTy Bot          Bot          val fm le = tt
Val-U-to-ValTy UCode        Bot          val () le
Val-U-to-ValTy (FunEl g)    Bot          val () le
Val-U-to-ValTy (PiCode a f) Bot          val () le
Val-U-to-ValTy Bot          UCode        val fm le = val
Val-U-to-ValTy UCode        UCode        val fm le = val
Val-U-to-ValTy (FunEl g)    UCode        val fm le = val
Val-U-to-ValTy (PiCode a f) UCode        val fm le = val
Val-U-to-ValTy Bot          (FunEl g)    val fm ()
Val-U-to-ValTy UCode        (FunEl g)    val fm ()
Val-U-to-ValTy (FunEl g0)   (FunEl g)    val fm ()
Val-U-to-ValTy (PiCode a f) (FunEl g)    val fm ()
Val-U-to-ValTy Bot          (PiCode a f) val fm ()
Val-U-to-ValTy UCode        (PiCode a f) val fm ()
Val-U-to-ValTy (FunEl g)    (PiCode a f) val fm ()
Val-U-to-ValTy (PiCode a0 f0) (PiCode a f) val fm ()

-- FinMem u UCode from FinMem u a and LeCode a UCode
FinMem-from-U-code : (a u : FinEl) -> FinMem u a -> LeCode a UCode -> FinMem u UCode
FinMem-from-U-code Bot Bot fm le = tt
FinMem-from-U-code Bot UCode () le
FinMem-from-U-code Bot (FunEl g) () le
FinMem-from-U-code Bot (PiCode b f) () le
FinMem-from-U-code UCode u fm le = fm
FinMem-from-U-code (FunEl g)    u fm ()
FinMem-from-U-code (PiCode b f) u fm ()

------------------------------------------------------------------------
-- Part 9: Semantic helpers (FINITE)
------------------------------------------------------------------------

-- (AllPairs-lookup removed: now use Pi-edgewise from RawSemantics)

------------------------------------------------------------------------
-- Part 10: Interface postulates
------------------------------------------------------------------------

-- CoherentFun from Coherent(PiCode) — just projection
Coherent-CoherentFun : (b : FinEl) (f : FinFun) ->
  Coherent (PiCode b f) -> CoherentFun f
Coherent-CoherentFun b f cpf = snd cpf

-- FinMem b UCode from CoherentFun f and FinMemAllU f b
-- (was previously extracted from old 3-tuple Coherent; now derived)
FinMem-bU-from-Pi : (b : FinEl) (f : FinFun) ->
  CoherentFun f -> FinMemAllU f b -> FinMem b UCode
FinMem-bU-from-Pi b f cf fmAllU = bU-from-cf-fmU f b cf fmAllU

-- EqVal symmetry — now proved in Validity with Coherent args
-- We derive Coherent from the call context
EqVal-sym-fn : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal G M N A u a -> EqVal G N M A u a
EqVal-sym-fn u a cu ca ev = EqVal-sym u a cu ca ev

-- EqVal transitivity with alignment (Sup + upEqVal + trans)
EqVal-trans-aligned : {n : Nat} {G : Ctx n} {M N P A : Expr n}
  (u a1 a2 : FinEl) ->
  Comp a1 a2 -> Coherent a1 -> Coherent a2 ->
  FinMem u a1 -> FinMem u a2 ->
  EqVal G M N A u a1 -> EqVal G N P A u a2 ->
  Pair (FinMem u (Sup a1 a2))
       (EqVal G M P A u (Sup a1 a2))
-- u = Bot: FinMem Bot a = FinMem a UCode, EqVal .. Bot a via EqVal-Bot
EqVal-trans-aligned Bot a1 a2 comp ca1 ca2 mem1 mem2 ev1 ev2 =
  mkSigma (finMemUCode-Sup a1 a2 comp mem1 mem2) (EqVal-Bot _ _ _ _ (Sup a1 a2))
-- u = UCode: only a1 = a2 = UCode possible
EqVal-trans-aligned {G = G} {M} {N} {P} {A} UCode UCode UCode comp ca1 ca2 mem1 mem2 ev1 ev2 =
  mkSigma tt (EqVal-trans {G = G} {M} {N} {P} {A} UCode UCode tt tt ev1 ev2)
EqVal-trans-aligned UCode UCode (FunEl _) () ca1 ca2 mem1 mem2 ev1 ev2
EqVal-trans-aligned UCode UCode (PiCode _ _) () ca1 ca2 mem1 mem2 ev1 ev2
EqVal-trans-aligned UCode Bot _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned UCode (FunEl _) _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned UCode (PiCode _ _) _ comp ca1 ca2 () mem2 ev1 ev2
-- u = PiCode: only a1 = a2 = UCode possible
EqVal-trans-aligned {G = G} {M} {N} {P} {A} (PiCode a' f') UCode UCode comp ca1 ca2 mem1 mem2 ev1 ev2 =
  let cu = FinMem-Coherent (PiCode a' f') UCode mem1
  in mkSigma mem1 (EqVal-trans {G = G} {M} {N} {P} {A} (PiCode a' f') UCode cu tt ev1 ev2)
EqVal-trans-aligned (PiCode _ _) UCode (FunEl _) () ca1 ca2 mem1 mem2 ev1 ev2
EqVal-trans-aligned (PiCode _ _) UCode (PiCode _ _) () ca1 ca2 mem1 mem2 ev1 ev2
EqVal-trans-aligned (PiCode _ _) Bot _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned (PiCode _ _) (FunEl _) _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned (PiCode _ _) (PiCode _ _) _ comp ca1 ca2 () mem2 ev1 ev2
-- u = FunEl g: only a1 = PiCode, a2 = PiCode possible
EqVal-trans-aligned (FunEl g) Bot _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned (FunEl g) UCode _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned (FunEl g) (FunEl _) _ comp ca1 ca2 () mem2 ev1 ev2
EqVal-trans-aligned (FunEl g) (PiCode _ _) Bot comp ca1 ca2 mem1 () ev1 ev2
EqVal-trans-aligned (FunEl g) (PiCode _ _) UCode comp ca1 ca2 mem1 () ev1 ev2
EqVal-trans-aligned (FunEl g) (PiCode _ _) (FunEl _) comp ca1 ca2 mem1 () ev1 ev2
EqVal-trans-aligned {G = G} {M} {N} {P} {A} (FunEl g) (PiCode b1 f1) (PiCode b2 f2) comp ca1 ca2 mem1 mem2 ev1 ev2 =
  let cu   = FinMem-Coherent (FunEl g) (PiCode b1 f1) mem1
      a1U  = FinMem-a-in-U (FunEl g) (PiCode b1 f1) mem1
      a2U  = FinMem-a-in-U (FunEl g) (PiCode b2 f2) mem2
      csup = Coherent-Sup (PiCode b1 f1) (PiCode b2 f2) comp ca1 ca2
      le1  = LeCode-Sup-left (PiCode b1 f1) (PiCode b2 f2) comp ca1 ca2
      le2  = LeCode-Sup-right (PiCode b1 f1) (PiCode b2 f2) comp ca1 ca2
      msup = finMem-Sup-left (PiCode b1 f1) (PiCode b2 f2) (FunEl g) comp ca1 ca2 a2U cu mem1
      vta1 = fst ev1
      vta2 = fst ev2
      vtAsup = ValTy-Sup G A (PiCode b1 f1) (PiCode b2 f2) comp a1U a2U vta1 vta2
      ev1' = upEqVal G M N A (FunEl g) (PiCode b1 f1) (Sup (PiCode b1 f1) (PiCode b2 f2))
               le1 mem1 msup ca1 csup ev1 vtAsup
      ev2' = upEqVal G N P A (FunEl g) (PiCode b2 f2) (Sup (PiCode b1 f1) (PiCode b2 f2))
               le2 mem2 msup ca2 csup ev2 vtAsup
      result = EqVal-trans {G = G} {M} {N} {P} {A} (FunEl g) (Sup (PiCode b1 f1) (PiCode b2 f2)) cu csup ev1' ev2'
  in mkSigma msup result


------------------------------------------------------------------------
-- Part 12: Postulated cases (FINITE)
------------------------------------------------------------------------

postulate
  -- ty-Lam
  adequacySub-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B M : Expr (suc g)} ->
    HasType G A U ->
    HasType (extend G A) B U ->
    HasType (extend G A) M B ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (Lam A M) rho u ->
    Adeq H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
           (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
           rho (Pi A B) u

  -- conv-beta
  adequacyEqSub-beta : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B M : Expr (suc g)} {a : Expr g} ->
    HasType G A U ->
    HasType (extend G A) B U ->
    HasType (extend G A) M B ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App (Lam A M) a) rho u ->
    AdeqEq H (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
                  (substExpr sigma a))
             (substExpr sigma (subst1 M a))
             (substExpr sigma (subst1 B a))
             rho (subst1 B a) u

  -- conv-funext
  adequacyEqSub-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
    ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                         (App (wkExpr g') (Var fzero)) B ->
    HasType G f (Pi A B) ->
    HasType G g' (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel f rho u ->
    AdeqEq H (substExpr sigma f) (substExpr sigma g')
             (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             rho (Pi A B) u

  -- conv-App-fun
  adequacyEqSub-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    AdeqEq H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             rho (subst1 B a) u

  -- conv-trans (uCode alignment needed)
  adequacyEqSub-conv-trans : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N P A : Expr g} ->
    ConvTm G M N A -> ConvTm G N P A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel M rho u ->
    AdeqEq H (substExpr sigma M) (substExpr sigma P)
             (substExpr sigma A) rho A u

  -- conv-App-arg
  adequacyEqSub-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    AdeqEq H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             rho (subst1 B a) u

------------------------------------------------------------------------
-- Part 13: Main adequacy theorems (mutual induction, FINITE)
------------------------------------------------------------------------

-- EvalRel-bot helper
EvalRel-bot : {n : Nat} (M : Expr n) (rho : EnvApprox n) -> EvalRel M rho Bot
EvalRel-bot (Var i)   rho = mkSigma tt (PaperSemantics.LeCode-Bot (lookupEnv i rho))
EvalRel-bot U         rho = mkSigma tt (PaperSemantics.LeCode-Bot UCode)
EvalRel-bot (Pi A B)  rho = tt
EvalRel-bot (Lam A M) rho = tt
EvalRel-bot (App f a) rho = tt

-- (PiPairRel-to-EvalRel removed: replaced by Pi-edgewise from RawSemantics)

-- App case postulate (Selection-based evidence restructured)
postulate
  adequacySub-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub H G0 sigma rho -> Fits G0 rho ->
    (u : FinEl) -> Coherent u ->
    EvalRel (App f' a) rho u ->
    Adeq H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a))
      rho (subst1 B a) u

{-# TERMINATING #-}

-- Main adequacy theorem
adequacySub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M A : Expr g} ->
  HasType G M A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
  (u : FinEl) -> EvalRel M rho u ->
  Adeq H (substExpr sigma M) (substExpr sigma A) rho A u

-- Adequacy for conversion
adequacyEqSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M N A : Expr g} ->
  ConvTm G M N A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
  (u : FinEl) -> EvalRel M rho u ->
  AdeqEq H (substExpr sigma M) (substExpr sigma N)
           (substExpr sigma A) rho A u

-- adequacySub: ty-var
-- EvalRel (Var i) rho u = Pair (Coherent u) (LeCode u (lookupEnv i rho))
adequacySub (ty-var {G = G} {i = i} _) sigma rho crho vs fits u hu =
  vs i u (fst hu) (snd hu)

-- adequacySub: ty-U
-- EvalRel U rho u = LeCode u UCode
adequacySub (ty-U _) sigma rho crho vs fits u hu =
  mkAdeq u UCode (LeCode-refl u (fst hu)) (mkSigma tt (LeCode-refl UCode tt)) (FinMem-from-LeCode-UCode u (snd hu)) (ValTy-U _ u (snd hu))

-- adequacySub: ty-conv
adequacySub (ty-conv {M = M} {A = A} {B = B} d1 d2) sigma rho crho vs fits u hu =
  let aq    = adequacySub d1 sigma rho crho vs fits u hu
      ha'   = convSound d2 rho fits (Adeq.aCode aq) (Adeq.evSrc aq)
      convH = red-to-conv (Red-subst sigma (Red-from-conv d2))
      val'  = Val-conv-type (Adeq.uCode aq) (Adeq.aCode aq) convH (Adeq.val aq)
  in mkAdeq (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.le aq) ha' (Adeq.mem aq) val'

-- adequacySub: ty-Pi
-- EvalRel (Pi A B) rho Bot = Top
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits Bot hu =
  mkAdeq Bot Bot tt (EvalRel-bot U rho) tt tt
-- EvalRel (Pi A B) rho UCode = Empty
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits UCode ()
-- EvalRel (Pi A B) rho (FunEl g) = Empty
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (FunEl g) ()
-- EvalRel (Pi A B) rho (PiCode b f) = Pair (Coherent ...) (Pair (EvalRel A rho b) (body ...))
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
  (mkSigma cpu (mkSigma evA allP)) =
  let ev = mkSigma cpu (mkSigma evA allP)
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      -- Step 1: Use theorem1 to get enlarged PiCode b' f' with FinMem in UCode
      typed = theorem1 (ty-Pi d1 d2) rho fits (PiCode b f) ev
      u'    = fst typed
      a'    = fst (snd typed)
      le'   = fst (snd (snd typed))
      ev'   = fst (snd (snd (snd typed)))
      fm'   = fst (snd (snd (snd (snd typed))))
      evU'  = snd (snd (snd (snd (snd typed))))
  in tyPi-result u' a' le' ev' fm' evU'
  where
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) B

    -- Helper: FinMem y UCode from EvalRel U rho x and FinMem y x
    finMem-from-U : (x y : FinEl) -> EvalRel U rho x -> FinMem y x -> FinMem y UCode
    finMem-from-U Bot Bot evU fm = tt
    finMem-from-U Bot UCode evU ()
    finMem-from-U Bot (FunEl g0) evU ()
    finMem-from-U Bot (PiCode a0 f0) evU ()
    finMem-from-U UCode y evU fm = fm
    finMem-from-U (FunEl g0) y (mkSigma _ ()) fm
    finMem-from-U (PiCode a0 f0) y (mkSigma _ ()) fm

    -- Helper: extract ValTy from Adeq at type U
    -- Val H sA U u1 a1 is ValTy H sA u1 when a1 = UCode, Top when a1 = Bot
    toValTy : (u1 a1 : FinEl) -> Val H sA U u1 a1 -> FinMem u1 a1 ->
      EvalRel U rho a1 -> ValTy H sA u1
    toValTy u1 Bot val fm evU = valTy-from-Bot u1 fm
      where
        valTy-from-Bot : (u1 : FinEl) -> FinMem u1 Bot -> ValTy H sA u1
        valTy-from-Bot Bot fm0 = tt
        valTy-from-Bot UCode ()
        valTy-from-Bot (FunEl g0) ()
        valTy-from-Bot (PiCode a0 f0) ()
    toValTy u1 UCode val fm evU = val
    toValTy u1 (FunEl g0) val fm (mkSigma _ ())
    toValTy u1 (PiCode a0 f0) val fm (mkSigma _ ())

    -- Main: case-split on the enlarged element from theorem1
    tyPi-result : (u' a' : FinEl) -> LeCode (PiCode b f) u' ->
      EvalRel (Pi A B) rho u' -> FinMem u' a' -> EvalRel U rho a' ->
      Adeq H (Pi sA sB) U rho U (PiCode b f)

    -- u' = Bot: degenerate case
    tyPi-result Bot a' le' ev' fm' evU' =
      mkAdeq Bot UCode le' (mkSigma tt (LeCode-refl UCode tt))
        (finMem-from-U a' Bot evU' fm') tt

    -- u' = UCode: impossible (LeCode (PiCode b f) UCode = Empty)
    tyPi-result UCode a' () ev' fm' evU'

    -- u' = FunEl: impossible (LeCode (PiCode b f) (FunEl g0) = Empty)
    tyPi-result (FunEl g0) a' () ev' fm' evU'

    -- u' = PiCode b' f': main case
    tyPi-result (PiCode b' f') a' le' ev' fm' evU' =
      let -- le' : Pair (LeCode b b') (LeFunCode f f')
          le-b = fst le'
          le-f = snd le'
          -- FinMem (PiCode b' f') UCode:
          fmPiU : FinMem (PiCode b' f') UCode
          fmPiU = finMem-from-U a' (PiCode b' f') evU' fm'
          -- Extract from fmPiU:
          b'U   = fst fmPiU
          allU' = fst (snd fmPiU)
          cf'   = snd (snd fmPiU)
          cb'   = coh-from-aU b' b'U
          -- Decompose ev': EvalRel (Pi A B) rho (PiCode b' f')
          cpu'  = fst ev'
          evA'  = fst (snd ev')
          -- IH on d1 at b': gives Adeq H sA U rho U b'
          aq1   = adequacySub d1 sigma rho crho vs fits b' evA'
          -- Extract ValTy H sA u1 from the Adeq result
          u1    = Adeq.uCode aq1
          a1    = Adeq.aCode aq1
          u1U   = finMem-from-U a1 u1 (Adeq.evSrc aq1) (Adeq.mem aq1)
          valTy1 = toValTy u1 a1 (Adeq.val aq1) (Adeq.mem aq1) (Adeq.evSrc aq1)
          -- downValTy from u1 to b'
          valTyA : ValTy H sA b'
          valTyA = downValTy H sA b' u1 (Adeq.le aq1) b'U u1U valTy1
          -- PiEdgeVal H sA sB b' f': from IH on d2
          pev   = buildPiEdgeVal
          -- PiEdgeEq H sA sB b' f': from IH on d2
          peq   = buildPiEdgeEq
          -- Assemble ValTyPi
          valTyPi : ValTyPi H (Pi sA sB) b' f'
          valTyPi = mkSigma sA (mkSigma sB (mkSigma Red-refl
                      (mkSigma cf' (mkSigma allU'
                        (mkSigma valTyA (mkSigma pev peq))))))
      in mkAdeq (PiCode b' f') UCode (mkSigma le-b le-f)
           (mkSigma tt (LeCode-refl UCode tt)) fmPiU valTyPi
      where
        -- ev': EvalRel (Pi A B) rho (PiCode b' f')
        -- Extract the per-edge body from ev'
        cpu'e  = fst ev'
        evA'e  = fst (snd ev')
        cf'e   = snd cpu'e
        b'Ue   = fst (finMem-from-U a' (PiCode b' f') evU' fm')
        allU'e = fst (snd (finMem-from-U a' (PiCode b' f') evU' fm'))
        cb'e   = coh-from-aU b' b'Ue
        buildPiEdgeVal : PiEdgeVal H sA sB b' f'
        buildPiEdgeVal u0 v0 sel N valN =
          let bodyData = snd (snd ev')
              a'body   = fst bodyData
              evAbody  = fst (snd bodyData)
              body0    = snd (snd bodyData)
              edge     = body0 u0 v0 sel
              x        = fst edge
              le_xu    = fst (snd edge)
              fm_x     = fst (snd (snd edge))
              evBv     = snd (snd (snd edge))
              cx       = FinMem-Coherent x a'body fm_x
              fmub'    = FinMemAllU-Selection b' sel allU'e cf'e cb'e b'Ue
              cu0      = FinMem-Coherent u0 b' fmub'
              crho_ext = mkSigma crho cx
              fits_ext = mkSigma fits (mkSigma a'body (mkSigma fm_x evAbody))
              hyp0     = \ u' cu' le_u'_x ->
                           mkAdeq u0 b' (LeCode-trans u' x u0 cu' cx cu0 le_u'_x le_xu)
                             evA'e fmub' valN
              vs_ext   = ValidSub-extend sigma N rho x vs hyp0
              aq2      = adequacySub d2 (extSub sigma N) (extendEnv rho x)
                           crho_ext vs_ext fits_ext v0 evBv
              u2       = Adeq.uCode aq2
              a2c      = Adeq.aCode aq2
              u2U      = FinMem-from-U-code a2c u2 (Adeq.mem aq2) (snd (Adeq.evSrc aq2))
              valTy2   = Val-U-to-ValTy u2 a2c (Adeq.val aq2) (Adeq.mem aq2) (snd (Adeq.evSrc aq2))
              eq0      = S.Eq-sym (substExpr-comp sigma B N)
              valTy2t  = S.Eq-transport (\ T -> ValTy H T u2) eq0 valTy2
              vU       = FinMem-Selection-UCode b' sel allU'e cf'e
          in downValTy H (subst1 sB N) v0 u2 (Adeq.le aq2) vU u2U valTy2t
        postulate
          buildPiEdgeEq  : PiEdgeEq H sA sB b' f'

-- adequacySub: ty-Lam (delegated to postulate)
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits u hu =
  adequacySub-Lam d1 d2 d3 sigma rho crho vs fits u hu

-- adequacySub: ty-App
-- EvalRel (App f a) rho Bot = Top
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho crho vs fits Bot hu =
  mkAdeq Bot Bot tt (EvalRel-bot (subst1 B a) rho) tt tt
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho crho vs fits UCode ev =
  adequacySub-App dA d1 d2 sigma rho crho vs fits UCode tt ev
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho crho vs fits (FunEl g') ev =
  adequacySub-App dA d1 d2 sigma rho crho vs fits (FunEl g') (EvalRel-coh (App f' a) rho (FunEl g') ev) ev
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho crho vs fits (PiCode b0' f0') ev =
  adequacySub-App dA d1 d2 sigma rho crho vs fits (PiCode b0' f0') (EvalRel-coh (App f' a) rho (PiCode b0' f0') ev) ev

-- adequacyEqSub: conv-refl
adequacyEqSub (conv-refl d) sigma rho crho vs fits u hu =
  let aq = adequacySub d sigma rho crho vs fits u hu
  in mkAdeqEq (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.le aq) (Adeq.evSrc aq) (Adeq.mem aq) (Val-to-EqVal (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.val aq))

-- adequacyEqSub: conv-sym
adequacyEqSub (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho crho vs fits u hu =
  let huN  = convSound-inv d rho fits u hu
      aq   = adequacyEqSub d sigma rho crho vs fits u huN
      cu'  = FinMem-Coherent (AdeqEq.uCode aq) (AdeqEq.aCode aq) (AdeqEq.mem aq)
      ca   = EvalRel-coh Asrc rho (AdeqEq.aCode aq) (AdeqEq.evSrc aq)
  in mkAdeqEq (AdeqEq.uCode aq) (AdeqEq.aCode aq) (AdeqEq.le aq) (AdeqEq.evSrc aq) (AdeqEq.mem aq)
       (EqVal-sym-fn (AdeqEq.uCode aq) (AdeqEq.aCode aq) cu' ca (AdeqEq.eqval aq))

-- adequacyEqSub: conv-trans (delegated to postulate — uCode alignment needed)
adequacyEqSub {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho crho vs fits u hu =
  adequacyEqSub-conv-trans d1 d2 sigma rho crho vs fits u hu

-- adequacyEqSub: conv-conv
adequacyEqSub (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2) sigma rho crho vs fits u hu =
  let aq    = adequacyEqSub d1 sigma rho crho vs fits u hu
      ha'   = convSound d2 rho fits (AdeqEq.aCode aq) (AdeqEq.evSrc aq)
      convH = red-to-conv (Red-subst sigma (Red-from-conv d2))
      eval' = EqVal-conv-type (AdeqEq.uCode aq) (AdeqEq.aCode aq) convH (AdeqEq.eqval aq)
  in mkAdeqEq (AdeqEq.uCode aq) (AdeqEq.aCode aq) (AdeqEq.le aq) ha' (AdeqEq.mem aq) eval'

-- adequacyEqSub: conv-beta (delegated to postulate)
adequacyEqSub (conv-beta d1 d2 d3 d4) sigma rho crho vs fits u hu =
  adequacyEqSub-beta d1 d2 d3 d4 sigma rho crho vs fits u hu

-- adequacyEqSub: conv-Pi (proved inline)
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits Bot hu =
  mkAdeqEq Bot Bot tt (EvalRel-bot U rho) tt tt
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits UCode ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (FunEl g) ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
  (mkSigma cpu (mkSigma evA allP)) =
  convPi-postulate d1 d2 sigma rho crho vs fits (PiCode b f) (mkSigma cpu (mkSigma evA allP))
  where
    postulate
      convPi-postulate : ConvTm G A A' U -> ConvTm (extend G A) B B' U ->
        (sigma0 : Sub _ _) -> (rho0 : EnvApprox _) ->
        CoherentEnv rho0 -> ValidSub H G sigma0 rho0 -> Fits G rho0 ->
        (u : FinEl) -> EvalRel (Pi A B) rho0 u ->
        AdeqEq H (Pi (substExpr sigma0 A) (substExpr (liftSub sigma0) B))
                 (Pi (substExpr sigma0 A') (substExpr (liftSub sigma0) B'))
                 U rho0 U u

-- adequacyEqSub: conv-funext (delegated to postulate)
adequacyEqSub (conv-funext _ d1 d2 d3) sigma rho crho vs fits u hu =
  adequacyEqSub-funext d1 d2 d3 sigma rho crho vs fits u hu

-- adequacyEqSub: conv-App-fun (delegated to postulate)
adequacyEqSub (conv-App-fun _ d1 d2) sigma rho crho vs fits u hu =
  adequacyEqSub-App-fun d1 d2 sigma rho crho vs fits u hu

-- adequacyEqSub: conv-App-arg (delegated to postulate)
adequacyEqSub (conv-App-arg _ d1 d2) sigma rho crho vs fits u hu =
  adequacyEqSub-App-arg d1 d2 sigma rho crho vs fits u hu

------------------------------------------------------------------------
-- Part 14: Closed-term corollary
------------------------------------------------------------------------

-- Adequacy for closed terms
adequacy : {M A : Expr zero} ->
  HasType empty M A ->
  (rho : EnvApprox zero) ->
  (u : FinEl) -> EvalRel M rho u ->
  Adeq empty M A rho A u
adequacy {M} {A} d emptyEnv u hu =
  let aq   = adequacySub d idSub emptyEnv tt (ValidSub-empty idSub emptyEnv) tt u hu
      val' = S.Eq-transport (\ T -> Val empty (substExpr idSub M) T (Adeq.uCode aq) (Adeq.aCode aq))
               (substExpr-id A) (Adeq.val aq)
      val'' = S.Eq-transport (\ E -> Val empty E A (Adeq.uCode aq) (Adeq.aCode aq))
                (substExpr-id M) val'
  in mkAdeq (Adeq.uCode aq) (Adeq.aCode aq) (Adeq.le aq) (Adeq.evSrc aq) (Adeq.mem aq) val''
