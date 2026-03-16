{-# OPTIONS --without-K --exact-split #-}

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
  CoherentFun ; Comp ; Comp-down ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; EvalFun ; EvalFun-in-UCode ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  LeFunCode ;
  FinMem ; FinMemFun ; FinMemAllU ;
  FinMem-a-in-U ; finMemUCode-Sup ;
  finMem-upward ; finMem-Sup-left ; finMem-Sup-right ; coh-from-aU ;
  FinMem-coh-u ; cft-from-cf)
open import Reduction using (Red ; Red-refl ; HeadRed ;
  headred-step ; headred-beta ; headred-refl ; subst-subst1-comm)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ; Pi-edgewise ;
  EvalRel-coh ; CoherentEnv ; lookupEnv-coh ;
  EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ;
  EvalRel-mon-env ; EnvLe ; EnvLe-refl)
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
  Val-EqValTy-fwd ; EqVal-EqValTy-fwd ;
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
  EqVal-trans ; ValTy-Sup ;
  Val-beta-expand ; EqVal-beta-expand ;
  Val-headred-contract ; EqVal-headred-expand ;
  Red-unique-Pi)
open import Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode ;
  FinMem-Selection ; FinMem-Selection-codomain ;
  selectionBelow)
open import TypingSemantics using (convSound ; convSound-inv ; convSound' ; theorem1)
open import LemmaForTS using (Fits ; Typed ; Fits-CoherentEnv)
open import EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-Pi-app-type ; EvalRel-Pi-body ; EvalRel-subst1-forward)

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
-- Part 4: (Adeq/AdeqEq records removed)
--
-- The adequacy theorems now take u and a as inputs (with FinMem u a
-- as hypothesis) and return Val/EqVal directly, without existential
-- quantification over uCode/aCode.
------------------------------------------------------------------------

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
  (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem u a ->
  Val H (sigma i) (substExpr sigma (lookup G i)) u a

------------------------------------------------------------------------
-- Part 6: Transport helpers
------------------------------------------------------------------------

-- Transport EvalRel along expression equality
EvalRel-transport : {n : Nat} {M M' : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Eq M M' -> EvalRel M rho u -> EvalRel M' rho u
EvalRel-transport S.refl ev = ev

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
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val H t (substExpr sigma A) u a) ->
  ValidSub H (extend G A) (extSub sigma t) (extendEnv rho v)
ValidSub-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 fzero u cu le a evA fm =
  let evA' = EvalRel-unwk Asrc rho v a evA
      val  = hyp0 u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma Asrc t)
  in S.Eq-transport (\ T -> Val H t T u a) eq val
ValidSub-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 (fsuc i) u cu le a evA fm =
  let evA' = EvalRel-unwk (lookup G i) rho v a evA
      val  = vs i u cu le a evA' fm
      eq   = S.Eq-sym (substExpr-wk sigma (lookup G i) t)
  in S.Eq-transport (\ T -> Val H (sigma i) T u a) eq val

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


-- adequacyEqSub-funext: proved below (after twoVal-to-EqVal)

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

-- Forward declarations for mutual recursion
{-# TERMINATING #-}

-- Main adequacy theorem
adequacySub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M A : Expr g} ->
  HasType G M A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val H (substExpr sigma M) (substExpr sigma A) u a

-- Adequacy for conversion
adequacyEqSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M N A : Expr g} ->
  ConvTm G M N A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  EqVal H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

-- App case helper (was postulate, now proved)
--
-- PROOF PLAN for adequacySub-App  (REVISED: target-edge-driven)
-- ==============================================================
-- Called with u ∈ {UCode, FunEl g, PiCode a' f'} (Bot handled before call).
-- Let sf = substExpr sigma f', sa = substExpr sigma a,
--     sA = substExpr sigma A, sB = substExpr (liftSub sigma) B,
--     sBA = substExpr sigma (subst1 B a).
-- Note: sBA = subst1 sB sa  (by sigma-subst1).
--
-- TRIVIAL CASES (u, ac):
--  (u, Bot)                 → Val = Top → tt
--  (u, FunEl h)             → Val = Top → tt
--  (UCode, UCode)           → Val = ValTy UCode = Top → tt
--  (UCode, PiCode b f)      → FinMem UCode (PiCode ..) = Empty → absurd
--  (FunEl g, UCode)         → Val = ValTy (FunEl g) = Top → tt
--  (PiCode _ _, PiCode _ _) → FinMem (PiCode ..) (PiCode ..) = Empty → absurd
--  (PiCode a' f', UCode)    → HARD CASE A
--  (FunEl g, PiCode b_ac f_ac) → HARD CASE B
--
-- COMMON SETUP (for both hard cases, when ev is non-Bot):
-- --------------------------------------------------------
-- Step 1: Decompose ev : EvalRel (App f' a) rho u.
--   For non-Bot u: ev = mkSigma v (mkSigma evA_v evF_sing)
--   where sing = [(v, u)], evA_v : EvalRel a rho v,
--   evF_sing : EvalRel f' rho (FunEl sing).
--
-- Step 2: Enlarge the function via theorem1.
--   theorem1 d1 rho fits (FunEl sing) evF_sing
--   Case-split u_big: must be FunEl g_big (since FunEl ≤ only FunEl).
--   Case-split a_pi:  must be PiCode b_pi f_pi (since FinMem (FunEl _) only PiCode).
--   Yields: evF_big, fm_big, evPi : EvalRel (Pi A B) rho (PiCode b_pi f_pi),
--   LeFunCode sing g_big.
--
-- Step 3: Get Val for the enlarged function.
--   adequacySub d1 at (FunEl g_big, PiCode b_pi f_pi)
--   → Pair (ValTyPi H (Pi sA sB) b_pi f_pi)
--          (ValPi  H sf (Pi sA sB) g_big b_pi f_pi)
--   HeadRed1-not-Pi forces Red to be Red-refl, so A0 = sA, B0 = sB.
--   Extract: PiAppVal from the ValPi.
--   Since Red H (Pi sA sB) (Pi A0 B0) U must be Red-refl (Pi can't
--   head-reduce), A0 = sA, B0 = sB.
--
-- Step 4: Apply function's PiAppVal at argument v (via selectionBelow).
--   selectionBelow g_big v cg_big cv → (u_sel, v_sel, sel_big)
--   with LeCode u_sel v and EvalFun g_big v = v_sel.
--   Build Val H sa sA u_sel b_pi from adequacySub d2 (using EvalRel-down).
--   Apply PiAppVal at (u_sel, v_sel, sel_big, sa) →
--     Val H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
--
-- Step 5: Transport to target (u, ac).
--   Bridge: LeCode u v_sel (from LeFunCode sing g_big).
--   Sup(ac, EvalFun f_pi u_sel) as intermediate type code.
--   upVal → restrictVal → downVal.
--
adequacySub-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub H G0 sigma rho -> Fits G0 rho ->
    (u : FinEl) -> Coherent u ->
    EvalRel (App f' a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    Val H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u ac

-- u = Bot: trivial
adequacySub-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
  dA dB d1 d2 sigma rho crho vs fits Bot cu ev ac evAc fm =
  Val-Bot H (App (substExpr sigma f') (substExpr sigma a))
            (substExpr sigma (subst1 B a)) ac

-- u = UCode: FinMem UCode ac forces ac = UCode, Val = Top
adequacySub-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev Bot evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev UCode evAc fm = tt
adequacySub-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev (FunEl _) evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev (PiCode _ _) evAc ()

-- u = PiCode: FinMem (PiCode ..) ac forces ac = UCode
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (PiCode b0 f0) cu ev Bot evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (PiCode b0 f0) cu ev (FunEl _) evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (PiCode b0 f0) cu ev (PiCode _ _) evAc ()
-- u = FunEl g: FinMem (FunEl g) ac forces ac = PiCode
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (FunEl g) cu ev Bot evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (FunEl g) cu ev UCode evAc ()
adequacySub-App dA dB d1 d2 sigma rho crho vs fits (FunEl g) cu ev (FunEl _) evAc ()
-- PiCode/UCode and FunEl/PiCode: use full approach
adequacySub-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
  dA dB d1 d2 sigma rho crho vs fits u0 cu ev ac0 evAc fm =
  appVal-core u0 ac0 cu ev evAc fm
  where
    sf  = substExpr sigma f'
    sa  = substExpr sigma a
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) B
    sBA = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    appVal-inner : (u1 : FinEl) -> (ac1 : FinEl) ->
      Coherent u1 ->
      (v0 : FinEl) -> EvalRel a rho v0 ->
      EvalRel f' rho (FunEl (cons (mkSigma v0 u1) nil)) ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      Val H (App sf sa) sBA u1 ac1
    appVal-inner u1 ac1 cu1 v0 evA_v0 evF_sing0 evAc1 fm1 =
      S.Eq-transport (\ T -> Val H (App sf sa) T u1 ac1)
        (S.Eq-sym eq-sBA) transported
      where
        -- Decomposed App evaluation
        v        = v0
        evA_v    = evA_v0
        sing     = cons (mkSigma v u1) nil
        evF_sing = evF_sing0
        cv       = EvalRel-coh a rho v evA_v

        -- Step 2: Enlarge function via theorem1
        typed_f  = theorem1 d1 rho fits (FunEl sing) evF_sing
        u_big    = fst typed_f
        a_pi     = fst (snd typed_f)
        le_sing  = fst (snd (snd typed_f))
        evF_big  = fst (snd (snd (snd typed_f)))
        fm_big   = fst (snd (snd (snd (snd typed_f))))
        evPi     = snd (snd (snd (snd (snd typed_f))))

        -- Step 3: Get function's Val
        val_fun  = adequacySub d1 sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

        appVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
          LeCode (FunEl sing) ub ->
          EvalRel f' rho ub -> EvalRel (Pi A B) rho ap ->
          FinMem ub ap ->
          Val H sf (Pi sA sB) ub ap ->
          Val H (App sf sa) (subst1 sB sa) u1 ac1
        appVal-dispatch Bot          ap    () evFb evPab fmba valba
        appVal-dispatch UCode        ap    () evFb evPab fmba valba
        appVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
        appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
        appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
        appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
        appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
          let -- Bridge: LeCode u1 (EvalFun g_big v)
              le_u1_vsel : LeCode u1 (EvalFun g_big v)
              le_u1_vsel = fst lf

              -- Extract from fmba
              fmg_big  = fst fmba
              cg_big   = fst (snd fmba)
              piU      = snd (snd fmba)
              b_piU    = fst piU
              allU_fpi = fst (snd piU)
              cf_pi    = snd (snd piU)
              cb_pi    = coh-from-aU b_pi b_piU

              -- Extract EvalRel A rho b_pi from Pi evaluation
              evA_bpi  = fst (snd evPab)

              -- selectionBelow g_big v
              sb       = selectionBelow g_big v cg_big cv
              u_sel    = fst sb
              v_sel    = fst (snd sb)
              sel_big  = fst (snd (snd sb))
              le_usel  = fst (snd (snd (snd sb)))
              eq_vsel  = snd (snd (snd (snd sb)))
              le_u1_vsel' : LeCode u1 v_sel
              le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel

              cu_sel   = Coherent-Selection sel_big cg_big

              -- Argument Val: Val H sa sA u_sel b_pi
              evA_usel = EvalRel-down a rho v u_sel crho cu_sel evA_v le_usel
              fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big cg_big cb_pi b_piU
              val_arg  = adequacySub d2 sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

              -- Extract PiAppVal from function's Val
              vpi_fun  = snd valba
              A0_fun   = fst vpi_fun
              B0_fun   = fst (snd vpi_fun)
              red_fun  = fst (snd (snd vpi_fun))
              uniq_fun = Red-unique-Pi Red-refl red_fun
              eqA_fun  = fst uniq_fun
              eqB_fun  = snd uniq_fun
              pav_fun  = fst (snd (snd (snd (snd (snd vpi_fun)))))

              -- Transport argument type
              val_arg' = S.Eq-transport (\ X -> Val H sa X u_sel b_pi) eqA_fun val_arg

              -- Apply PiAppVal
              val_app_raw = pav_fun u_sel v_sel sel_big sa val_arg'
              val_app : Val H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
              val_app = S.Eq-transport
                (\ X -> Val H (App sf sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
                (S.Eq-sym eqB_fun) val_app_raw

              -- Transport: (v_sel, EvalFun f_pi u_sel) → (u1, ac1)
              ef_usel  = EvalFun f_pi u_sel
              ef_v     = EvalFun f_pi v
              cft_fpi  = cft-from-cf f_pi cf_pi
              le_ef    = EvalFun-mon-arg f_pi u_sel v le_usel cft_fpi cu_sel cv
              evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v crho evPab evA_v
              c_efv    = Coherent-EvalFun f_pi v cft_fpi cv
              c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
              evBa_efusel = EvalRel-down (subst1 B a) rho ef_v ef_usel crho c_efusel evBa_efv le_ef
              comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
              c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1

              sup_code = Sup ac1 ef_usel
              c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel

              ac1_U    = FinMem-a-in-U u1 ac1 fm1
              ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
              sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
              fm_u1_sup = finMem-upward u1 ac1 sup_code
                           le_ac_sup c_ac c_sup fm1 sup_U
              fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big cg_big cf_pi allU_fpi
              fm_vsel_sup = finMem-upward v_sel ef_usel sup_code
                              le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

              -- ValTy at Sup (need ValTy at ac1 and at ef_usel)
              evU      = mkSigma tt (LeCode-refl UCode tt)

              -- ValTy at ac1
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
                in adequacySub d2 sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
              vs_ext   = ValidSub-extend sigma sa rho v_fwd' vs hyp_ext
              vt_ac_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U
              eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
              vt_ac    = S.Eq-transport (\ T -> ValTy H T ac1) eq_comp vt_ac_raw

              -- ValTy at ef_usel
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
                in adequacySub d2 sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
              vs_ef     = ValidSub-extend sigma sa rho v_fwd_ef' vs hyp_ef
              vt_ef_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU
              vt_ef     = S.Eq-transport (\ T -> ValTy H T ef_usel) eq_comp vt_ef_raw

              -- ValTy-Sup
              vt_sup   = ValTy-Sup H (subst1 sB sa) ac1 ef_usel
                           comp_ac_ef ac1_U ef_uselU vt_ac vt_ef

              -- Transport chain
              val_up   = upVal H (App sf sa) (subst1 sB sa) v_sel ef_usel sup_code
                           le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup val_app vt_sup
              val_res  = restrictVal H (App sf sa) (subst1 sB sa) v_sel u1 sup_code
                           le_u1_vsel' fm_u1_sup fm_vsel_sup val_up
              val_down = downVal H (App sf sa) (subst1 sB sa) u1
                           ac1 sup_code le_ac_sup fm1 c_ac sup_U val_res
          in val_down

        -- Dispatch on u_big (FunEl) and a_pi (PiCode)
        transported : Val H (App sf sa) (subst1 sB sa) u1 ac1
        transported = appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

    appVal-core : (u1 : FinEl) -> (ac1 : FinEl) ->
      Coherent u1 ->
      EvalRel (App f' a) rho u1 ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      Val H (App sf sa) sBA u1 ac1
    -- Bot: trivial
    appVal-core Bot ac1 _ _ _ _ = Val-Bot H (App sf sa) sBA ac1
    -- UCode: Val at UCode is Top for any ac (FinMem UCode ac forces ac = UCode or Bot)
    appVal-core UCode Bot _ _ _ _ = tt
    appVal-core UCode UCode _ _ _ _ = tt
    appVal-core UCode (FunEl _) _ _ _ ()
    appVal-core UCode (PiCode _ _) _ _ _ ()
    -- PiCode: only ac = UCode is possible
    appVal-core (PiCode _ _) Bot _ _ _ ()
    appVal-core (PiCode _ _) (FunEl _) _ _ _ ()
    appVal-core (PiCode _ _) (PiCode _ _) _ _ _ ()
    appVal-core (PiCode b0pc f0pc) UCode cu1 ev1 evAc1 fm1 =
      appVal-inner (PiCode b0pc f0pc) UCode cu1 (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1
    -- FunEl: only ac = PiCode is possible
    appVal-core (FunEl _) Bot _ _ _ ()
    appVal-core (FunEl _) UCode _ _ _ ()
    appVal-core (FunEl _) (FunEl _) _ _ _ ()
    appVal-core (FunEl gfe) (PiCode bacfe facfe) cu1 ev1 evAc1 fm1 =
      appVal-inner (FunEl gfe) (PiCode bacfe facfe) cu1 (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1
------------------------------------------------------------------------
-- adequacyEqSub-App-arg (conv-App-arg case, proved)
--
-- Same structure as adequacyEqSub-App-fun but uses PiAppEq (from ValPi of f)
-- to get argument congruence: EqVal sa sa' sA → EqVal (App sf sa) (App sf sa').
------------------------------------------------------------------------

adequacyEqSub-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal H (App (substExpr sigma f) (substExpr sigma a))
            (App (substExpr sigma f) (substExpr sigma a'))
            (substExpr sigma (subst1 B a))
            u ac

-- u = Bot: trivial
adequacyEqSub-App-arg {H = H} {A = A} {B = B} {f = f} {a = a} {a' = a'}
  dB df daa' sigma rho crho vs fits Bot ev ac evAc fm =
  EqVal-Bot H (App (substExpr sigma f) (substExpr sigma a))
              (App (substExpr sigma f) (substExpr sigma a'))
              (substExpr sigma (subst1 B a)) ac

-- u = UCode: FinMem UCode ac forces ac = UCode or Bot
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits UCode ev Bot evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits UCode ev UCode evAc fm =
  mkSigma tt (mkSigma tt tt)
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits UCode ev (FunEl _) evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits UCode ev (PiCode _ _) evAc ()

-- u = PiCode: only ac = UCode is possible
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (PiCode b0 f0) ev Bot evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (PiCode b0 f0) ev (FunEl _) evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (PiCode b0 f0) ev (PiCode _ _) evAc ()
-- u = FunEl g: FinMem (FunEl g) ac forces ac = PiCode
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (FunEl g) ev Bot evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (FunEl g) ev UCode evAc ()
adequacyEqSub-App-arg dB df daa' sigma rho crho vs fits (FunEl g) ev (FunEl _) evAc ()
-- PiCode/UCode and FunEl/PiCode: use full approach
adequacyEqSub-App-arg {H = H} {A = A} {B = B} {f = f} {a = a} {a' = a'}
  dB df daa' sigma rho crho vs fits u0 ev ac0 evAc fm =
  appEqVal-core u0 ac0 ev evAc fm
  where
    sf   = substExpr sigma f
    sa   = substExpr sigma a
    sa'  = substExpr sigma a'
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sBA  = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    appEqVal-inner : (u1 : FinEl) -> (ac1 : FinEl) ->
      (v0 : FinEl) -> EvalRel a rho v0 ->
      EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      EqVal H (App sf sa) (App sf sa') sBA u1 ac1
    appEqVal-inner u1 ac1 v0 evA_v0 evF_sing0 evAc1 fm1 =
      S.Eq-transport (\ T -> EqVal H (App sf sa) (App sf sa') T u1 ac1)
        (S.Eq-sym eq-sBA) transported
      where
        -- Decomposed App evaluation
        v        = v0
        evA_v    = evA_v0
        sing     = cons (mkSigma v u1) nil
        evF_sing = evF_sing0
        cv       = EvalRel-coh a rho v evA_v

        -- Step 2: Enlarge function via theorem1
        typed_f  = theorem1 df rho fits (FunEl sing) evF_sing
        u_big    = fst typed_f
        a_pi     = fst (snd typed_f)
        le_sing  = fst (snd (snd typed_f))
        evF_big  = fst (snd (snd (snd typed_f)))
        fm_big   = fst (snd (snd (snd (snd typed_f))))
        evPi     = snd (snd (snd (snd (snd typed_f))))

        -- Step 3: Get function's Val via adequacySub on df
        val_fun = adequacySub df sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

        appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
          LeCode (FunEl sing) ub ->
          EvalRel f rho ub -> EvalRel (Pi A B) rho ap ->
          FinMem ub ap ->
          Val H sf (Pi sA sB) ub ap ->
          EqVal H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
        appEqVal-dispatch Bot          ap    () evFb evPab fmba valba
        appEqVal-dispatch UCode        ap    () evFb evPab fmba valba
        appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
        appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
          let -- Bridge: LeCode u1 (EvalFun g_big v)
              le_u1_vsel : LeCode u1 (EvalFun g_big v)
              le_u1_vsel = fst lf

              -- Extract from fmba
              fmg_big  = fst fmba
              cg_big   = fst (snd fmba)
              piU      = snd (snd fmba)
              b_piU    = fst piU
              allU_fpi = fst (snd piU)
              cf_pi    = snd (snd piU)
              cb_pi    = coh-from-aU b_pi b_piU

              -- Extract EvalRel A rho b_pi from Pi evaluation
              evA_bpi  = fst (snd evPab)

              -- selectionBelow g_big v
              sb       = selectionBelow g_big v cg_big cv
              u_sel    = fst sb
              v_sel    = fst (snd sb)
              sel_big  = fst (snd (snd sb))
              le_usel  = fst (snd (snd (snd sb)))
              eq_vsel  = snd (snd (snd (snd sb)))
              le_u1_vsel' : LeCode u1 v_sel
              le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel

              cu_sel   = Coherent-Selection sel_big cg_big

              -- Argument EqVal: EqVal H sa sa' sA u_sel b_pi
              evA_usel = EvalRel-down a rho v u_sel crho cu_sel evA_v le_usel
              fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big cg_big cb_pi b_piU
              eqval_arg = adequacyEqSub daa' sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

              -- Extract PiAppEq from function's Val at (FunEl g_big, PiCode b_pi f_pi)
              -- Val = Pair (ValTyPi) (ValPi)
              -- ValPi = (A0, B0, Red, CoherentFun, FinMemFun, Pair (PiAppVal, PiAppEq))
              vpi_fun  = snd valba
              A0_fun   = fst vpi_fun
              B0_fun   = fst (snd vpi_fun)
              red_fun  = fst (snd (snd vpi_fun))
              uniq_fun = Red-unique-Pi Red-refl red_fun
              eqA_fun  = fst uniq_fun
              eqB_fun  = snd uniq_fun
              pae_fun  = snd (snd (snd (snd (snd (snd vpi_fun)))))

              -- Transport argument types: EqVal sa sa' sA → EqVal sa sa' A0
              eqval_arg' = S.Eq-transport (\ X -> EqVal H sa sa' X u_sel b_pi) eqA_fun eqval_arg

              -- Apply PiAppEq: N1 = sa, N2 = sa'
              eqval_app_raw = pae_fun u_sel v_sel sel_big sa sa' eqval_arg'
              eqval_app : EqVal H (App sf sa) (App sf sa') (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
              eqval_app = S.Eq-transport
                (\ X -> EqVal H (App sf sa) (App sf sa') (subst1 X sa) v_sel (EvalFun f_pi u_sel))
                (S.Eq-sym eqB_fun) eqval_app_raw

              -- Transport: (v_sel, EvalFun f_pi u_sel) → (u1, ac1)
              ef_usel  = EvalFun f_pi u_sel
              ef_v     = EvalFun f_pi v
              cft_fpi  = cft-from-cf f_pi cf_pi
              le_ef    = EvalFun-mon-arg f_pi u_sel v le_usel cft_fpi cu_sel cv
              evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v crho evPab evA_v
              c_efv    = Coherent-EvalFun f_pi v cft_fpi cv
              c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
              evBa_efusel = EvalRel-down (subst1 B a) rho ef_v ef_usel crho c_efusel evBa_efv le_ef
              comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
              c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1

              sup_code = Sup ac1 ef_usel
              c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel

              ac1_U    = FinMem-a-in-U u1 ac1 fm1
              ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
              sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
              fm_u1_sup = finMem-upward u1 ac1 sup_code
                           le_ac_sup c_ac c_sup fm1 sup_U
              fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big cg_big cf_pi allU_fpi
              fm_vsel_sup = finMem-upward v_sel ef_usel sup_code
                              le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

              -- ValTy at Sup (need ValTy at ac1 and at ef_usel)
              evU      = mkSigma tt (LeCode-refl UCode tt)

              -- InvTyp for a from convSound' daa'
              invTyp_a = fst (convSound' daa' rho fits)

              -- Helper: produce Val H sa sA for ValidSub-extend
              -- Uses adequacyEqSub daa' + Val-from-EqVal-first
              val_sa : (u' : FinEl) -> EvalRel a rho u' ->
                (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
                Val H sa sA u' a_arg
              val_sa u' evA_u' a_arg evA_aarg fm_u'_a =
                Val-from-EqVal-first u' a_arg
                  (adequacyEqSub daa' sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a)

              -- ValTy at ac1
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
              vs_ext   = ValidSub-extend sigma sa rho v_fwd' vs hyp_ext
              vt_ac_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U
              eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
              vt_ac    = S.Eq-transport (\ T -> ValTy H T ac1) eq_comp vt_ac_raw

              -- ValTy at ef_usel
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
              vs_ef     = ValidSub-extend sigma sa rho v_fwd_ef' vs hyp_ef
              vt_ef_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU
              vt_ef     = S.Eq-transport (\ T -> ValTy H T ef_usel) eq_comp vt_ef_raw

              -- ValTy-Sup
              vt_sup   = ValTy-Sup H (subst1 sB sa) ac1 ef_usel
                           comp_ac_ef ac1_U ef_uselU vt_ac vt_ef

              -- Transport chain (EqVal version)
              eqval_up   = upEqVal H (App sf sa) (App sf sa') (subst1 sB sa) v_sel ef_usel sup_code
                             le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup eqval_app vt_sup
              eqval_res  = restrictEqVal H (App sf sa) (App sf sa') (subst1 sB sa) v_sel u1 sup_code
                             le_u1_vsel' fm_u1_sup fm_vsel_sup eqval_up
              eqval_down = downEqVal H (App sf sa) (App sf sa') (subst1 sB sa) u1
                             ac1 sup_code le_ac_sup fm1 c_ac sup_U eqval_res
          in eqval_down

        transported : EqVal H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
        transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

    appEqVal-core : (u1 : FinEl) -> (ac1 : FinEl) ->
      EvalRel (App f a) rho u1 ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      EqVal H (App sf sa) (App sf sa') sBA u1 ac1
    -- Bot: trivial
    appEqVal-core Bot ac1 _ _ _ = EqVal-Bot H (App sf sa) (App sf sa') sBA ac1
    -- UCode
    appEqVal-core UCode Bot _ _ _ = tt
    appEqVal-core UCode UCode _ _ _ = mkSigma tt (mkSigma tt tt)
    appEqVal-core UCode (FunEl _) _ _ ()
    appEqVal-core UCode (PiCode _ _) _ _ ()
    -- PiCode
    appEqVal-core (PiCode _ _) Bot _ _ ()
    appEqVal-core (PiCode _ _) (FunEl _) _ _ ()
    appEqVal-core (PiCode _ _) (PiCode _ _) _ _ ()
    appEqVal-core (PiCode b0pc f0pc) UCode ev1 evAc1 fm1 =
      appEqVal-inner (PiCode b0pc f0pc) UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1
    -- FunEl
    appEqVal-core (FunEl _) Bot _ _ ()
    appEqVal-core (FunEl _) UCode _ _ ()
    appEqVal-core (FunEl _) (FunEl _) _ _ ()
    appEqVal-core (FunEl gfe) (PiCode bacfe facfe) ev1 evAc1 fm1 =
      appEqVal-inner (FunEl gfe) (PiCode bacfe facfe) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1

------------------------------------------------------------------------
-- adequacyEqSub-App-fun (conv-App-fun case, proved)
--
-- Same structure as adequacySub-App but for equality:
-- uses convSound' for enlargement, adequacyEqSub for EqVal,
-- and EqVal transport chain (upEqVal, restrictEqVal, downEqVal).
------------------------------------------------------------------------

adequacyEqSub-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal H (App (substExpr sigma f) (substExpr sigma a))
            (App (substExpr sigma f') (substExpr sigma a))
            (substExpr sigma (subst1 B a))
            u ac

-- u = Bot: trivial
adequacyEqSub-App-fun {H = H} {A = A} {B = B} {f = f} {f' = f'} {a = a}
  dB dff' da sigma rho crho vs fits Bot ev ac evAc fm =
  EqVal-Bot H (App (substExpr sigma f) (substExpr sigma a))
              (App (substExpr sigma f') (substExpr sigma a))
              (substExpr sigma (subst1 B a)) ac

-- u = UCode: FinMem UCode ac forces ac = UCode or Bot
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits UCode ev Bot evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits UCode ev UCode evAc fm =
  mkSigma tt (mkSigma tt tt)
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits UCode ev (FunEl _) evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits UCode ev (PiCode _ _) evAc ()

-- u = PiCode: only ac = UCode is possible
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (PiCode b0 f0) ev Bot evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (PiCode b0 f0) ev (FunEl _) evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (PiCode b0 f0) ev (PiCode _ _) evAc ()
-- u = FunEl g: FinMem (FunEl g) ac forces ac = PiCode
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (FunEl g) ev Bot evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (FunEl g) ev UCode evAc ()
adequacyEqSub-App-fun dB dff' da sigma rho crho vs fits (FunEl g) ev (FunEl _) evAc ()
-- PiCode/UCode and FunEl/PiCode: use full approach
adequacyEqSub-App-fun {H = H} {A = A} {B = B} {f = f} {f' = f'} {a = a}
  dB dff' da sigma rho crho vs fits u0 ev ac0 evAc fm =
  appEqVal-core u0 ac0 ev evAc fm
  where
    sf   = substExpr sigma f
    sf'  = substExpr sigma f'
    sa   = substExpr sigma a
    sA   = substExpr sigma A
    sB   = substExpr (liftSub sigma) B
    sBA  = substExpr sigma (subst1 B a)
    eq-sBA : Eq sBA (subst1 sB sa)
    eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

    -- InvTyp for f from convSound': first projection gives enlargement for f
    invTyp-f = fst (convSound' dff' rho fits)

    appEqVal-inner : (u1 : FinEl) -> (ac1 : FinEl) ->
      (v0 : FinEl) -> EvalRel a rho v0 ->
      EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      EqVal H (App sf sa) (App sf' sa) sBA u1 ac1
    appEqVal-inner u1 ac1 v0 evA_v0 evF_sing0 evAc1 fm1 =
      S.Eq-transport (\ T -> EqVal H (App sf sa) (App sf' sa) T u1 ac1)
        (S.Eq-sym eq-sBA) transported
      where
        -- Decomposed App evaluation
        v        = v0
        evA_v    = evA_v0
        sing     = cons (mkSigma v u1) nil
        evF_sing = evF_sing0
        cv       = EvalRel-coh a rho v evA_v

        -- Step 2: Enlarge function via InvTyp from convSound'
        typed_f  = invTyp-f (FunEl sing) evF_sing
        u_big    = fst typed_f
        a_pi     = fst (snd typed_f)
        le_sing  = fst (snd (snd typed_f))
        evF_big  = fst (snd (snd (snd typed_f)))
        fm_big   = fst (snd (snd (snd (snd typed_f))))
        evPi     = snd (snd (snd (snd (snd typed_f))))

        -- Step 3: Get function's EqVal via adequacyEqSub on dff'
        eqval_fun = adequacyEqSub dff' sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

        appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
          LeCode (FunEl sing) ub ->
          EvalRel f rho ub -> EvalRel (Pi A B) rho ap ->
          FinMem ub ap ->
          EqVal H sf sf' (Pi sA sB) ub ap ->
          EqVal H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
        appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
        appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
        appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
        appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
        appEqVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba eqvba =
          let -- Bridge: LeCode u1 (EvalFun g_big v)
              le_u1_vsel : LeCode u1 (EvalFun g_big v)
              le_u1_vsel = fst lf

              -- Extract from fmba
              fmg_big  = fst fmba
              cg_big   = fst (snd fmba)
              piU      = snd (snd fmba)
              b_piU    = fst piU
              allU_fpi = fst (snd piU)
              cf_pi    = snd (snd piU)
              cb_pi    = coh-from-aU b_pi b_piU

              -- Extract EvalRel A rho b_pi from Pi evaluation
              evA_bpi  = fst (snd evPab)

              -- selectionBelow g_big v
              sb       = selectionBelow g_big v cg_big cv
              u_sel    = fst sb
              v_sel    = fst (snd sb)
              sel_big  = fst (snd (snd sb))
              le_usel  = fst (snd (snd (snd sb)))
              eq_vsel  = snd (snd (snd (snd sb)))
              le_u1_vsel' : LeCode u1 v_sel
              le_u1_vsel' = S.Eq-transport (LeCode u1) eq_vsel le_u1_vsel

              cu_sel   = Coherent-Selection sel_big cg_big

              -- Argument Val: Val H sa sA u_sel b_pi
              evA_usel = EvalRel-down a rho v u_sel crho cu_sel evA_v le_usel
              fm_usel_bpi = FinMem-Selection b_pi f_pi sel_big fmg_big cg_big cb_pi b_piU
              val_arg  = adequacySub da sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

              -- Extract from EqVal at (FunEl g_big, PiCode b_pi f_pi):
              -- Pair (ValTy) (Pair (ValPi sf) (Pair (ValPi sf') (EqValPi sf sf')))
              vty_fun   = fst eqvba
              vpi_sf    = fst (snd eqvba)
              vpi_sf'   = fst (snd (snd eqvba))
              eqvpi_fun = snd (snd (snd eqvba))

              -- Extract PiAppEqVal from EqValPi
              A0_eqfun   = fst eqvpi_fun
              B0_eqfun   = fst (snd eqvpi_fun)
              red_eqfun  = fst (snd (snd eqvpi_fun))
              uniq_eqfun = Red-unique-Pi Red-refl red_eqfun
              eqA_eqfun  = fst uniq_eqfun
              eqB_eqfun  = snd uniq_eqfun
              paeqv_fun  = snd (snd (snd (snd (snd eqvpi_fun))))

              -- Transport argument type
              val_arg' = S.Eq-transport (\ X -> Val H sa X u_sel b_pi) eqA_eqfun val_arg

              -- Apply PiAppEqVal
              eqval_app_raw = paeqv_fun u_sel v_sel sel_big sa val_arg'
              eqval_app : EqVal H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
              eqval_app = S.Eq-transport
                (\ X -> EqVal H (App sf sa) (App sf' sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
                (S.Eq-sym eqB_eqfun) eqval_app_raw

              -- Transport: (v_sel, EvalFun f_pi u_sel) → (u1, ac1)
              ef_usel  = EvalFun f_pi u_sel
              ef_v     = EvalFun f_pi v
              cft_fpi  = cft-from-cf f_pi cf_pi
              le_ef    = EvalFun-mon-arg f_pi u_sel v le_usel cft_fpi cu_sel cv
              evBa_efv = EvalRel-Pi-app-type A B a rho b_pi f_pi v crho evPab evA_v
              c_efv    = Coherent-EvalFun f_pi v cft_fpi cv
              c_efusel = Coherent-EvalFun f_pi u_sel cft_fpi cu_sel
              evBa_efusel = EvalRel-down (subst1 B a) rho ef_v ef_usel crho c_efusel evBa_efv le_ef
              comp_ac_ef = EvalRel-Comp (subst1 B a) rho crho ac1 ef_usel evAc1 evBa_efusel
              c_ac     = EvalRel-coh (subst1 B a) rho ac1 evAc1

              sup_code = Sup ac1 ef_usel
              c_sup    = Coherent-Sup ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ac_sup = LeCode-Sup-left ac1 ef_usel comp_ac_ef c_ac c_efusel
              le_ef_sup = LeCode-Sup-right ac1 ef_usel comp_ac_ef c_ac c_efusel

              ac1_U    = FinMem-a-in-U u1 ac1 fm1
              ef_uselU = EvalFun-in-UCode f_pi u_sel b_pi cft_fpi cu_sel allU_fpi
              sup_U    = finMemUCode-Sup ac1 ef_usel comp_ac_ef ac1_U ef_uselU
              fm_u1_sup = finMem-upward u1 ac1 sup_code
                           le_ac_sup c_ac c_sup fm1 sup_U
              fm_vsel_ef = FinMem-Selection-codomain b_pi f_pi sel_big fmg_big cg_big cf_pi allU_fpi
              fm_vsel_sup = finMem-upward v_sel ef_usel sup_code
                              le_ef_sup c_efusel c_sup fm_vsel_ef sup_U

              -- ValTy at Sup (need ValTy at ac1 and at ef_usel)
              evU      = mkSigma tt (LeCode-refl UCode tt)

              -- ValTy at ac1
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
              hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
                let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
                in adequacySub da sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
              vs_ext   = ValidSub-extend sigma sa rho v_fwd' vs hyp_ext
              vt_ac_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U
              eq_comp  = S.Eq-sym (substExpr-comp sigma B sa)
              vt_ac    = S.Eq-transport (\ T -> ValTy H T ac1) eq_comp vt_ac_raw

              -- ValTy at ef_usel
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
                in adequacySub da sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
              vs_ef     = ValidSub-extend sigma sa rho v_fwd_ef' vs hyp_ef
              vt_ef_raw = adequacySub dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU
              vt_ef     = S.Eq-transport (\ T -> ValTy H T ef_usel) eq_comp vt_ef_raw

              -- ValTy-Sup
              vt_sup   = ValTy-Sup H (subst1 sB sa) ac1 ef_usel
                           comp_ac_ef ac1_U ef_uselU vt_ac vt_ef

              -- Transport chain (EqVal version)
              eqval_up   = upEqVal H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel ef_usel sup_code
                             le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup eqval_app vt_sup
              eqval_res  = restrictEqVal H (App sf sa) (App sf' sa) (subst1 sB sa) v_sel u1 sup_code
                             le_u1_vsel' fm_u1_sup fm_vsel_sup eqval_up
              eqval_down = downEqVal H (App sf sa) (App sf' sa) (subst1 sB sa) u1
                             ac1 sup_code le_ac_sup fm1 c_ac sup_U eqval_res
          in eqval_down

        -- Dispatch on u_big (FunEl) and a_pi (PiCode)
        transported : EqVal H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
        transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big eqval_fun

    appEqVal-core : (u1 : FinEl) -> (ac1 : FinEl) ->
      EvalRel (App f a) rho u1 ->
      EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
      EqVal H (App sf sa) (App sf' sa) sBA u1 ac1
    -- Bot: trivial
    appEqVal-core Bot ac1 _ _ _ = EqVal-Bot H (App sf sa) (App sf' sa) sBA ac1
    -- UCode: EqVal at UCode
    appEqVal-core UCode Bot _ _ _ = tt
    appEqVal-core UCode UCode _ _ _ = mkSigma tt (mkSigma tt tt)
    appEqVal-core UCode (FunEl _) _ _ ()
    appEqVal-core UCode (PiCode _ _) _ _ ()
    -- PiCode: only ac = UCode is possible
    appEqVal-core (PiCode _ _) Bot _ _ ()
    appEqVal-core (PiCode _ _) (FunEl _) _ _ ()
    appEqVal-core (PiCode _ _) (PiCode _ _) _ _ ()
    appEqVal-core (PiCode b0pc f0pc) UCode ev1 evAc1 fm1 =
      appEqVal-inner (PiCode b0pc f0pc) UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1
    -- FunEl: only ac = PiCode is possible
    appEqVal-core (FunEl _) Bot _ _ ()
    appEqVal-core (FunEl _) UCode _ _ ()
    appEqVal-core (FunEl _) (FunEl _) _ _ ()
    appEqVal-core (FunEl gfe) (PiCode bacfe facfe) ev1 evAc1 fm1 =
      appEqVal-inner (FunEl gfe) (PiCode bacfe facfe) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) evAc1 fm1


------------------------------------------------------------------------
-- twoValTy-to-EqValTy: two ValTy at the same code → EqValTy
--
-- By recursion on the type code v. At PiCode b' f':
--   - domains: recurse at b'
--   - codomains: use Val-EqValTy-fwd to bridge, recurse at v (selection value)
------------------------------------------------------------------------

{-# TERMINATING #-}
twoValTy-to-EqValTy : {n : Nat} {G : Ctx n} {T1 T2 : Expr n}
  (v : FinEl) -> FinMem v UCode ->
  ValTy G T1 v -> ValTy G T2 v ->
  EqValTy G T1 T2 v
-- v = Bot: EqValTy = Top
twoValTy-to-EqValTy Bot fm vt1 vt2 = tt
-- v = UCode: EqValTy = Top
twoValTy-to-EqValTy UCode fm vt1 vt2 = tt
-- v = FunEl: FinMem (FunEl g) UCode = Empty
twoValTy-to-EqValTy (FunEl g) () vt1 vt2
-- v = PiCode b' f': main case
twoValTy-to-EqValTy {G = G} {T1 = T1} {T2 = T2} (PiCode b' f') fm vt1 vt2 =
  mkSigma vt1 (mkSigma vt2 eqCore)
  where
    bU'  = fst fm
    allU' = fst (snd fm)
    cf'  = snd (snd fm)
    cb'  = coh-from-aU b' bU'

    -- Extract from vt1 : ValTyPi G T1 b' f'
    A1     = fst vt1
    B1     = fst (snd vt1)
    red1   = fst (snd (snd vt1))
    cf1    = fst (snd (snd (snd vt1)))
    allU1  = fst (snd (snd (snd (snd vt1))))
    vtA1   = fst (snd (snd (snd (snd (snd vt1)))))
    pevB1  = fst (snd (snd (snd (snd (snd (snd vt1))))))
    peeB1  = snd (snd (snd (snd (snd (snd (snd vt1))))))

    -- Extract from vt2 : ValTyPi G T2 b' f'
    A2     = fst vt2
    B2     = fst (snd vt2)
    red2   = fst (snd (snd vt2))

    vtA2   = fst (snd (snd (snd (snd (snd vt2)))))
    pevB2  = fst (snd (snd (snd (snd (snd (snd vt2))))))

    -- Recursive: EqValTy G A1 A2 b'
    eqDom : EqValTy G A1 A2 b'
    eqDom = twoValTy-to-EqValTy b' bU' vtA1 vtA2

    -- PiEdgeEqTy G A1 B1 B2 b' f'
    eqCod : PiEdgeEqTy G A1 B1 B2 b' f'
    eqCod u v sel P valP =
      let valP' = Val-EqValTy-fwd u b' cb' eqDom valP
          vtBP1 = pevB1 u v sel P valP
          vtBP2 = pevB2 u v sel P valP'
          fmvU  = FinMem-Selection-UCode b' sel allU1 cf1
      in twoValTy-to-EqValTy v fmvU vtBP1 vtBP2

    -- Full EqValTyPi G T1 T2 b' f'
    eqCore : EqValTyPi G T1 T2 b' f'
    eqCore = mkSigma A1 (mkSigma B1 (mkSigma A2 (mkSigma B2
               (mkSigma red1 (mkSigma red2
                 (mkSigma cf1 (mkSigma allU1
                   (mkSigma eqDom eqCod))))))))

------------------------------------------------------------------------
-- twoVal-to-EqVal: two Val at the same type code → EqVal
--
-- Given Val G M1 T u a and Val G M2 T u a (same syntactic type T,
-- same semantic indices u, a), produce EqVal G M1 M2 T u a.
-- At (FunEl g, PiCode b f): uses Red-unique-Pi (HeadRed determinism)
-- to align domain/codomain, then recurses via PiAppVal from each Val.
------------------------------------------------------------------------

{-# TERMINATING #-}
twoVal-to-EqVal : {n : Nat} {G : Ctx n} {M1 M2 T : Expr n}
  (u a : FinEl) -> FinMem u a ->
  Val G M1 T u a -> Val G M2 T u a -> EqVal G M1 M2 T u a
-- u = Bot: EqVal .. Bot a = Top for all a
twoVal-to-EqVal Bot Bot fm v1 v2 = tt
twoVal-to-EqVal Bot UCode fm v1 v2 = mkSigma tt (mkSigma tt tt)
twoVal-to-EqVal Bot (FunEl h) fm v1 v2 = tt
twoVal-to-EqVal Bot (PiCode b f) fm v1 v2 = tt
-- u = UCode: a must be Bot or UCode (FinMem constraint)
twoVal-to-EqVal UCode Bot fm v1 v2 = tt
twoVal-to-EqVal {G = G} {M1 = M1} {M2 = M2} UCode UCode fm v1 v2 =
  mkSigma v1 (mkSigma v2 (twoValTy-to-EqValTy {G = G} {T1 = M1} {T2 = M2} UCode fm v1 v2))
twoVal-to-EqVal UCode (FunEl h) fm v1 v2 = tt
twoVal-to-EqVal UCode (PiCode b f) fm v1 v2 = tt
-- u = FunEl g
twoVal-to-EqVal (FunEl g) Bot fm v1 v2 = tt
twoVal-to-EqVal {G = G} {M1 = M1} {M2 = M2} (FunEl g) UCode fm v1 v2 =
  mkSigma v1 (mkSigma v2 (twoValTy-to-EqValTy {G = G} {T1 = M1} {T2 = M2} (FunEl g) fm v1 v2))
twoVal-to-EqVal (FunEl g) (FunEl h) fm v1 v2 = tt
-- u = PiCode
twoVal-to-EqVal (PiCode _ _) Bot fm v1 v2 = tt
twoVal-to-EqVal {G = G} {M1 = M1} {M2 = M2} (PiCode a' ff) UCode fm v1 v2 =
  mkSigma v1 (mkSigma v2 (twoValTy-to-EqValTy {G = G} {T1 = M1} {T2 = M2} (PiCode a' ff) fm v1 v2))
twoVal-to-EqVal (PiCode _ _) (FunEl h) fm v1 v2 = tt
twoVal-to-EqVal (PiCode _ _) (PiCode b f) fm v1 v2 = tt
-- a = PiCode b f, u = FunEl g: main case
twoVal-to-EqVal {G = G} {M1 = M1} {M2 = M2} {T = T}
  (FunEl g) (PiCode b f) fm v1 v2 =
  mkSigma vty1 (mkSigma vpi1 (mkSigma vpi2T eqvpi))
  where
    -- Extract from v1
    vty1  = fst v1
    vpi1  = snd v1
    A0    = fst vpi1
    B0    = fst (snd vpi1)
    red   = fst (snd (snd vpi1))
    cg1   = fst (snd (snd (snd vpi1)))
    fmg1  = fst (snd (snd (snd (snd vpi1))))
    pav1  = fst (snd (snd (snd (snd (snd vpi1)))))

    -- Extract from v2
    vpi2  = snd v2
    A0'   = fst vpi2
    B0'   = fst (snd vpi2)
    red'  = fst (snd (snd vpi2))
    pav2  = fst (snd (snd (snd (snd (snd vpi2)))))
    pae2  = snd (snd (snd (snd (snd (snd vpi2)))))

    -- Red-unique-Pi: A0 = A0', B0 = B0'
    uniq  = Red-unique-Pi red red'
    eqA   = fst uniq
    eqB   = snd uniq

    -- Transport pav2 and pae2 from (A0', B0') to (A0, B0)
    pav2t : PiAppVal G M2 A0 B0 b f g
    pav2t = S.Eq-transport (\ X -> PiAppVal G M2 X B0 b f g) (S.Eq-sym eqA)
              (S.Eq-transport (\ Y -> PiAppVal G M2 A0' Y b f g) (S.Eq-sym eqB) pav2)
    pae2t : PiAppEq G M2 A0 B0 b f g
    pae2t = S.Eq-transport (\ X -> PiAppEq G M2 X B0 b f g) (S.Eq-sym eqA)
              (S.Eq-transport (\ Y -> PiAppEq G M2 A0' Y b f g) (S.Eq-sym eqB) pae2)

    -- FinMem subcomponents
    fmFun = fst fm
    cgFun = fst (snd fm)
    pfU   = snd (snd fm)
    allU0 = fst (snd pfU)
    cf0   = snd (snd pfU)

    -- Build ValPi for M2 at T with A0, B0, red from v1
    vpi2T = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg1
              (mkSigma fmg1 (mkSigma pav2t pae2t)))))

    -- Build EqValPi: PiAppEqVal by recursion
    paev : PiAppEqVal G M1 M2 A0 B0 b f g
    paev u' v' sel P valP =
      let body1    = pav1 u' v' sel P valP
          body2    = pav2t u' v' sel P valP
          fm_v'_ef = FinMem-Selection-codomain b f sel fmFun cgFun cf0 allU0
      in twoVal-to-EqVal v' (EvalFun f u') fm_v'_ef body1 body2

    eqvpi = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg1
              (mkSigma fmg1 paev))))

------------------------------------------------------------------------
-- adequacyEqSub-funext (conv-funext case, proved)
--
-- Given f = g : Pi A B by function extensionality,
-- produce EqVal H sf sg (Pi sA sB) u a.
-- Strategy: use convSound to get EvalRel g rho u from EvalRel f rho u,
-- then adequacySub on both f and g to get two Vals, and combine
-- with twoVal-to-EqVal.
------------------------------------------------------------------------

adequacyEqSub-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
    HasType G A U ->
    ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                         (App (wkExpr g') (Var fzero)) B ->
    HasType G f (Pi A B) ->
    HasType G g' (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel f rho u ->
    (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem u a ->
    EqVal H (substExpr sigma f) (substExpr sigma g')
            (substExpr sigma (Pi A B))
            u a
adequacyEqSub-funext dA d df dg sigma rho crho vs fits u hu a evA fm =
  let evG    = convSound (conv-funext dA d df dg) rho fits u hu
      val_sf = adequacySub df sigma rho crho vs fits u hu a evA fm
      val_sg = adequacySub dg sigma rho crho vs fits u evG a evA fm
  in twoVal-to-EqVal u a fm val_sf val_sg

-- adequacySub: ty-var
-- EvalRel (Var i) rho u = Pair (Coherent u) (LeCode u (lookupEnv i rho))
adequacySub (ty-var {G = G} {i = i} _) sigma rho crho vs fits u hu a evA fm =
  vs i u (fst hu) (snd hu) a evA fm

-- adequacySub: ty-U
-- EvalRel U rho u = Pair (Coherent u) (LeCode u UCode)
-- Val H U U u a: case-split on a (≤ UCode) and u (≤ UCode)
adequacySub (ty-U _) sigma rho crho vs fits u hu a evA fm =
  tyU-helper u a (snd hu) (snd evA) fm
  where
    tyU-helper : (u0 a0 : FinEl) -> LeCode u0 UCode -> LeCode a0 UCode -> FinMem u0 a0 -> Val _ U U u0 a0
    tyU-helper u0 Bot          _  _  _   = tt
    tyU-helper Bot UCode        _  _  _   = tt
    tyU-helper UCode UCode       _  _  _   = tt
    tyU-helper (FunEl _)    UCode () _  _
    tyU-helper (PiCode _ _) UCode () _  _
    tyU-helper u0 (FunEl _)    _  () _
    tyU-helper u0 (PiCode _ _) _  () _

-- adequacySub: ty-conv
-- Uses Lemma 8: Val-EqValTy-fwd with EqValTy from adequacyEqSub on d2
adequacySub (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits u hu a evA fm =
  let evA'  = convSound-inv d2 rho fits a evA
      val   = adequacySub d1 sigma rho crho vs fits u hu a evA' fm
      aU    = FinMem-a-in-U u a fm
      ca    = coh-from-aU a aU
      evU   = mkSigma tt (LeCode-refl UCode tt)
      eqAB  = adequacyEqSub d2 sigma rho crho vs fits a evA' UCode evU aU
      eqvty = snd (snd eqAB)
  in Val-EqValTy-fwd u a ca eqvty val

-- adequacySub: ty-Pi
-- The term (Pi A B) has type U.
-- u : EvalRel (Pi A B) rho u
-- a : EvalRel U rho a, fm : FinMem u a
-- Result: Val H (Pi sA sB) U u a
-- Val H (Pi sA sB) U u a:
--   a = Bot: Top
--   a = UCode: ValTy H (Pi sA sB) u
--   a = FunEl/PiCode: need FinMem u a => but a ≤ UCode so impossible
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits Bot hu a evA fm =
  Val-Bot H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) U a
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits UCode ()
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (FunEl g) ()
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu Bot evA fm = tt
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu UCode evA fm =
  -- fm : FinMem (PiCode b f) UCode = Pair (FinMem b UCode) (Pair (FinMemAllU f b) (CoherentFun f))
  -- We build ValTyPi H (Pi sA sB) b f directly
  let sA    = substExpr sigma A
      sB    = substExpr (liftSub sigma) B
      bU    = fst fm
      allU  = fst (snd fm)
      cf    = snd (snd fm)
      cb    = coh-from-aU b bU
      ev    = hu
      cpu   = fst ev
      evA'  = fst (snd ev)
      -- IH on d1 at b: ValTy H sA b
      valTyA = adequacySub d1 sigma rho crho vs fits b evA' UCode
                 (mkSigma tt (LeCode-refl UCode tt)) bU
      pev   = buildPiEdgeVal bU allU cf cb
      peq   = buildPiEdgeEq bU allU cf cb
      valTyPi : ValTyPi H (Pi sA sB) b f
      valTyPi = mkSigma sA (mkSigma sB (mkSigma (Red-refl)
                  (mkSigma cf (mkSigma allU
                    (mkSigma valTyA (mkSigma pev peq))))))
  in valTyPi
  where
    sA = substExpr sigma A
    sB = substExpr (liftSub sigma) B

    -- Extract from hu
    evAb : EvalRel A rho b
    evAb = fst (snd hu)
    a'pi : FinEl
    a'pi = fst (snd (snd hu))
    evA'pi : EvalRel A rho a'pi
    evA'pi = fst (snd (snd (snd hu)))
    bodyPi : (u0 v0 : FinEl) -> Selection f u0 v0 ->
      Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a'pi) (EvalRel B (extendEnv rho x) v0)))
    bodyPi = snd (snd (snd (snd hu)))

    -- Transport Val H N sA u0 b to Val H N sA u' a_arg
    -- via upVal to Sup(b, a_arg), restrictVal, downVal
    transportVal : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr _) -> Val H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val H N sA u' a_arg
    transportVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          vtA_b    = adequacySub d1 sigma rho crho vs fits b evAb UCode
                       (mkSigma tt (LeCode-refl UCode tt)) bU
          vtA_a    = adequacySub d1 sigma rho crho vs fits a_arg evA_arg UCode
                       (mkSigma tt (LeCode-refl UCode tt)) a_argU
          vtA_sup  = ValTy-Sup H sA b a_arg comp_b_a bU a_argU vtA_b vtA_a
          val1     = upVal H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup
                       cb c_sup valN vtA_sup
          cu0      = FinMem-coh-u u0 b fm_u0_b
          fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          val2     = restrictVal H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u_sup val1
          val3     = downVal H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3
      where
        bU = fst fm
        cb = coh-from-aU b (fst fm)

    buildPiEdgeVal : FinMem b UCode -> FinMemAllU f b -> CoherentFun f -> Coherent b ->
      PiEdgeVal H sA sB b f
    buildPiEdgeVal bU0 allU0 cf0 cb0 u0 v0 sel N valN =
      let -- Selection gives us membership evidence
          fm_u0_b  = FinMemAllU-Selection b sel allU0 cf0 cb0 bU0
          fm_v0_U  = FinMem-Selection-UCode b sel allU0 cf0
          cu0      = FinMem-coh-u u0 b fm_u0_b
          -- Get EvalRel B (extendEnv rho x) v0 from body, then lift to u0
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          -- Build Fits and CoherentEnv for extended context
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          -- Build ValidSub for (extend G A) via ValidSub-extend
          hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub-extend sigma N rho u0 vs hyp0
          -- IH on d2: Val H (substExpr (extSub sigma N) B) U v0 UCode
          evU      = mkSigma tt (LeCode-refl UCode tt)
          ih       = adequacySub d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' v0 evB_u0_v0 UCode evU fm_v0_U
          -- Transport from substExpr (extSub sigma N) B to subst1 sB N
      in S.Eq-transport (\ T -> ValTy H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih

    buildPiEdgeEq : FinMem b UCode -> FinMemAllU f b -> CoherentFun f -> Coherent b ->
      PiEdgeEq H sA sB b f
    buildPiEdgeEq bU0 allU0 cf0 cb0 u0 v0 sel N1 N2 eqvalN =
      let -- Selection gives us membership evidence
          fm_u0_b  = FinMemAllU-Selection b sel allU0 cf0 cb0 bU0
          fm_v0_U  = FinMem-Selection-UCode b sel allU0 cf0
          cu0      = FinMem-coh-u u0 b fm_u0_b
          -- Extract Val for N1 and N2 from EqVal
          valN1    = Val-from-EqVal-first u0 b eqvalN
          valN2    = Val-from-EqVal-second u0 b eqvalN
          -- Get EvalRel B (extendEnv rho u0) v0
          w        = bodyPi u0 v0 sel
          x        = fst w
          le_x_u0  = fst (snd w)
          fm_x_a'  = fst (snd (snd w))
          evB_x_v0 = snd (snd (snd w))
          cx       = FinMem-coh-u x a'pi fm_x_a'
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu0 le_x_u0))
          evB_u0_v0 = EvalRel-mon-env B (extendEnv rho x) (extendEnv rho u0) v0 evB_x_v0 envle_xu
          -- Fits and CoherentEnv for extended context
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u0_b evAb))
          crho'    = mkSigma crho cu0
          -- IH for N1
          hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N1   = ValidSub-extend sigma N1 rho u0 vs hyp0_N1
          evU      = mkSigma tt (LeCode-refl UCode tt)
          vtN1     = adequacySub d2 (extSub sigma N1) (extendEnv rho u0)
                       crho' vs'_N1 fits' v0 evB_u0_v0 UCode evU fm_v0_U
          vtN1'    = S.Eq-transport (\ T -> ValTy H T v0) (S.Eq-sym (substExpr-comp sigma B N1)) vtN1
          -- IH for N2
          hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                       transportVal u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'_N2   = ValidSub-extend sigma N2 rho u0 vs hyp0_N2
          vtN2     = adequacySub d2 (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N2 fits' v0 evB_u0_v0 UCode evU fm_v0_U
          vtN2'    = S.Eq-transport (\ T -> ValTy H T v0) (S.Eq-sym (substExpr-comp sigma B N2)) vtN2
          -- For EqValTy, we also need adequacyEqSub on conv-refl d2
          -- with a ValidSub that captures the equality between N1 and N2
          -- For now: construct EqValTy from the two ValTy's
      in twoValTy-to-EqValTy v0 fm_v0_U vtN1' vtN2'

adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu (FunEl _) evA ()
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu (PiCode _ _) evA ()

-- adequacySub: ty-Lam
-- u = Bot: trivial
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits Bot hu a evA fm =
  Val-Bot _ _ _ a
-- u = UCode/PiCode: absurd (EvalRel (Lam ..) rho UCode = Empty, etc.)
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits UCode () a evA fm
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits (PiCode _ _) () a evA fm
-- u = FunEl g, a = Bot/UCode/FunEl: Val is Top
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits (FunEl g) hu Bot evA fm = tt
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits (FunEl g) hu UCode evA fm = tt
adequacySub (ty-Lam d1 d2 d3) sigma rho crho vs fits (FunEl g) hu (FunEl h) evA fm = tt
-- u = FunEl g, a = PiCode b f0: main case
adequacySub {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3)
  sigma rho crho vs fits (FunEl g) hu (PiCode b f0) evA fm =
  mkSigma valTyPi (mkSigma sA (mkSigma sB (mkSigma (Red-refl)
    (mkSigma cg (mkSigma fmg (mkSigma piAppVal piAppEq))))))
  where
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) B
    sM  = substExpr (liftSub sigma) M
    fmg  = fst fm
    cg   = fst (snd fm)
    pU   = snd (snd fm)
    bU   = fst pU
    allU = fst (snd pU)
    cf0  = snd (snd pU)
    cb   = coh-from-aU b bU
    evAb : EvalRel A rho b
    evAb = fst (snd evA)
    a_lam = fst hu
    bodyLam : (u0 v0 : FinEl) -> Selection g u0 v0 ->
      Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a_lam) (EvalRel M (extendEnv rho x) v0)))
    bodyLam = snd (snd (snd (snd hu)))
    evU : EvalRel U rho UCode
    evU = mkSigma tt (LeCode-refl UCode tt)
    valTyPi : ValTyPi H (Pi sA sB) b f0
    valTyPi = adequacySub (ty-Pi d1 d2) sigma rho crho vs fits
                (PiCode b f0) evA UCode evU pU
    transportVal-Lam : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr _) -> Val H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val H N sA u' a_arg
    transportVal-Lam u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          vtA_b    = adequacySub d1 sigma rho crho vs fits b evAb UCode evU bU
          vtA_a    = adequacySub d1 sigma rho crho vs fits a_arg evA_arg UCode evU a_argU
          vtA_sup  = ValTy-Sup H sA b a_arg comp_b_a bU a_argU vtA_b vtA_a
          val1     = upVal H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup
                       cb c_sup valN vtA_sup
          val2     = restrictVal H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3
    piAppVal : PiAppVal H (Lam sA sM) sA sB b f0 g
    piAppVal u' v' sel N valN =
      let cu'      = Coherent-Selection sel cg
          fm_u'_b  = FinMem-Selection b f0 sel fmg cg cb bU
          fm_v'_ef = FinMem-Selection-codomain b f0 sel fmg cg cf0 allU
          w        = bodyLam u' v' sel
          x        = fst w
          le_x_u'  = fst (snd w)
          fm_x_al  = fst (snd (snd w))
          evM_x_v' = snd (snd (snd w))
          cx       = FinMem-coh-u x a_lam fm_x_al
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho'    = mkSigma crho cu'
          hyp0     = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                       transportVal-Lam u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'      = ValidSub-extend sigma N rho u' vs hyp0
          ih       = adequacySub d3 (extSub sigma N) (extendEnv rho u')
                       crho' vs' fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M     = S.Eq-sym (substExpr-comp sigma M N)
          eq_B     = S.Eq-sym (substExpr-comp sigma B N)
          ih'      = S.Eq-transport (\ T -> Val H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u')) eq_B ih
          ih''     = S.Eq-transport (\ E -> Val H E (subst1 sB N) v' (EvalFun f0 u')) eq_M ih'
      in Val-beta-expand v' (EvalFun f0 u') ih''
    piAppEq : PiAppEq H (Lam sA sM) sA sB b f0 g
    piAppEq u' v' sel N1 N2 eqvalN =
      let valN1    = Val-from-EqVal-first u' b eqvalN
          valN2    = Val-from-EqVal-second u' b eqvalN
          -- Common setup (same as piAppVal)
          cu'      = Coherent-Selection sel cg
          fm_u'_b  = FinMem-Selection b f0 sel fmg cg cb bU
          fm_v'_ef = FinMem-Selection-codomain b f0 sel fmg cg cf0 allU
          w        = bodyLam u' v' sel
          x        = fst w
          le_x_u'  = fst (snd w)
          fm_x_al  = fst (snd (snd w))
          evM_x_v' = snd (snd (snd w))
          cx       = FinMem-coh-u x a_lam fm_x_al
          envle_xu = mkSigma (EnvLe-refl rho crho) (mkSigma cx (mkSigma cu' le_x_u'))
          evM_u'_v' = EvalRel-mon-env M (extendEnv rho x) (extendEnv rho u') v' evM_x_v' envle_xu
          evB_u'_ef = EvalRel-Pi-body A B rho b f0 u' crho cu' evA
          fits'    = mkSigma fits (mkSigma b (mkSigma fm_u'_b evAb))
          crho'    = mkSigma crho cu'
          -- IH for N1: adequacySub d3 with (extSub sigma N1)
          hyp0_N1  = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                       transportVal-Lam u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'_N1   = ValidSub-extend sigma N1 rho u' vs hyp0_N1
          ih1      = adequacySub d3 (extSub sigma N1) (extendEnv rho u')
                       crho' vs'_N1 fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M1    = S.Eq-sym (substExpr-comp sigma M N1)
          eq_B1    = S.Eq-sym (substExpr-comp sigma B N1)
          ih1'     = S.Eq-transport (\ T -> Val H (substExpr (extSub sigma N1) M) T v' (EvalFun f0 u')) eq_B1 ih1
          ih1''    = S.Eq-transport (\ E -> Val H E (subst1 sB N1) v' (EvalFun f0 u')) eq_M1 ih1'
          val1     = Val-beta-expand v' (EvalFun f0 u') ih1''
          -- IH for N2: adequacySub d3 with (extSub sigma N2)
          hyp0_N2  = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                       transportVal-Lam u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
          vs'_N2   = ValidSub-extend sigma N2 rho u' vs hyp0_N2
          ih2      = adequacySub d3 (extSub sigma N2) (extendEnv rho u')
                       crho' vs'_N2 fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
          eq_M2    = S.Eq-sym (substExpr-comp sigma M N2)
          eq_B2    = S.Eq-sym (substExpr-comp sigma B N2)
          ih2'     = S.Eq-transport (\ T -> Val H (substExpr (extSub sigma N2) M) T v' (EvalFun f0 u')) eq_B2 ih2
          ih2''    = S.Eq-transport (\ E -> Val H E (subst1 sB N2) v' (EvalFun f0 u')) eq_M2 ih2'
          val2_raw = Val-beta-expand v' (EvalFun f0 u') ih2''
          -- val2_raw : Val H (App (Lam sA sM) N2) (subst1 sB N2) v' (EvalFun f0 u')
          -- Transport to type (subst1 sB N1) via EqValTy
          fm_ef_U  = FinMem-a-in-U v' (EvalFun f0 u') fm_v'_ef
          c_ef     = coh-from-aU (EvalFun f0 u') fm_ef_U
          -- Get two ValTys at (EvalFun f0 u') for B[N1] and B[N2]
          vtBN1    = adequacySub d2 (extSub sigma N1) (extendEnv rho u')
                       crho' vs'_N1 fits' (EvalFun f0 u') evB_u'_ef UCode evU fm_ef_U
          vtBN1'   = S.Eq-transport (\ T -> ValTy H T (EvalFun f0 u'))
                       (S.Eq-sym (substExpr-comp sigma B N1)) vtBN1
          vtBN2    = adequacySub d2 (extSub sigma N2) (extendEnv rho u')
                       crho' vs'_N2 fits' (EvalFun f0 u') evB_u'_ef UCode evU fm_ef_U
          vtBN2'   = S.Eq-transport (\ T -> ValTy H T (EvalFun f0 u'))
                       (S.Eq-sym (substExpr-comp sigma B N2)) vtBN2
          eqBN1N2  = twoValTy-to-EqValTy (EvalFun f0 u') fm_ef_U vtBN1' vtBN2'
          eqBN2N1  = EqValTy-sym (EvalFun f0 u') c_ef eqBN1N2
          -- Transport val2_raw from type (subst1 sB N2) to type (subst1 sB N1)
          val2     = Val-EqValTy-fwd v' (EvalFun f0 u') c_ef eqBN2N1 val2_raw
          -- Combine two Vals at the same type into EqVal
      in twoVal-to-EqVal v' (EvalFun f0 u') fm_v'_ef val1 val2

-- adequacySub: ty-App
-- EvalRel (App f a) rho Bot = Top; Val at (Bot, _) = Top
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits Bot hu ac evAc fm =
  Val-Bot H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) ac
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits UCode ev ac evAc fm =
  adequacySub-App dA dB d1 d2 sigma rho crho vs fits UCode tt ev ac evAc fm
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits (FunEl g') ev ac evAc fm =
  adequacySub-App dA dB d1 d2 sigma rho crho vs fits (FunEl g') (EvalRel-coh (App f' a) rho (FunEl g') ev) ev ac evAc fm
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits (PiCode b0' f0') ev ac evAc fm =
  adequacySub-App dA dB d1 d2 sigma rho crho vs fits (PiCode b0' f0') (EvalRel-coh (App f' a) rho (PiCode b0' f0') ev) ev ac evAc fm

-- adequacyEqSub: conv-refl
adequacyEqSub (conv-refl d) sigma rho crho vs fits u hu a evA fm =
  Val-to-EqVal u a (adequacySub d sigma rho crho vs fits u hu a evA fm)

-- adequacyEqSub: conv-sym
adequacyEqSub (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho crho vs fits u hu a evA fm =
  let huN  = convSound-inv d rho fits u hu
      cu'  = FinMem-Coherent u a fm
      ca   = EvalRel-coh Asrc rho a evA
      eq   = adequacyEqSub d sigma rho crho vs fits u huN a evA fm
  in EqVal-sym-fn u a cu' ca eq

-- adequacyEqSub: conv-trans (now direct: both IH calls use the same (u, a))
adequacyEqSub {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho crho vs fits u hu a evA fm =
  let huN  = convSound d1 rho fits u hu
      cu   = FinMem-Coherent u a fm
      ca   = EvalRel-coh A rho a evA
      eq1  = adequacyEqSub d1 sigma rho crho vs fits u hu a evA fm
      eq2  = adequacyEqSub d2 sigma rho crho vs fits u huN a evA fm
  in EqVal-trans u a cu ca eq1 eq2

-- adequacyEqSub: conv-conv
-- Uses Lemma 8: EqVal-EqValTy-fwd with EqValTy from adequacyEqSub on d2
adequacyEqSub (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits u hu a evA fm =
  let evA'  = convSound-inv d2 rho fits a evA
      eq    = adequacyEqSub d1 sigma rho crho vs fits u hu a evA' fm
      aU    = FinMem-a-in-U u a fm
      ca    = coh-from-aU a aU
      evU   = mkSigma tt (LeCode-refl UCode tt)
      eqAB  = adequacyEqSub d2 sigma rho crho vs fits a evA' UCode evU aU
      eqvty = snd (snd eqAB)
  in EqVal-EqValTy-fwd u a ca eqvty eq

-- adequacyEqSub: conv-beta (proved via headred-contract + headred-expand)
adequacyEqSub {H = H} (conv-beta {A = A} {B = B} {M = M} {a = a0}
  d1 d2 d3 d4) sigma rho crho vs fits u hu ac evAc fm =
  let val_app = adequacySub (ty-App d1 d2 (ty-Lam d1 d2 d3) d4)
                  sigma rho crho vs fits u hu ac evAc fm
      beta-hr : HeadRed (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
                              (substExpr sigma a0))
                        (substExpr sigma (subst1 M a0))
      beta-hr = S.Eq-transport
                  (\ X -> HeadRed (App (Lam (substExpr sigma A)
                    (substExpr (liftSub sigma) M)) (substExpr sigma a0)) X)
                  (subst-subst1-comm sigma M a0)
                  (headred-step headred-beta headred-refl)
      val_subst = Val-headred-contract u ac beta-hr val_app
      eqval_diag = Val-to-EqVal u ac val_subst
  in EqVal-headred-expand u ac beta-hr headred-refl eqval_diag

-- adequacyEqSub: conv-Pi (proved inline)
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits Bot hu a evA fm =
  EqVal-Bot H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
              (Pi (substExpr sigma A') (substExpr (liftSub sigma) B')) U a
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits UCode ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (FunEl g) ()
-- a = Bot: FinMem (PiCode b f) Bot = Empty
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu Bot evA ()
-- a = FunEl/PiCode: FinMem (PiCode ..) (FunEl/PiCode) = Empty
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu (FunEl _) evA ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu (PiCode _ _) evA ()
-- a = UCode: main case
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
  hu UCode evA fm =
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
    evU  = mkSigma tt (LeCode-refl UCode tt)

    -- hu : EvalRel (Pi A B) rho (PiCode b f)
    cpu   = fst hu
    evAb : EvalRel A rho b
    evAb  = fst (snd hu)
    a'pi  = fst (snd (snd hu))
    evA'pi = fst (snd (snd (snd hu)))
    bodyPi : (u0 v0 : FinEl) -> Selection f u0 v0 ->
      Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a'pi) (EvalRel B (extendEnv rho x) v0)))
    bodyPi = snd (snd (snd (snd hu)))

    -- EqVal from d1: gives ValTy H sA b, ValTy H sA' b, EqValTy H sA sA' b
    -- Need EvalRel (Pi A' B') rho (PiCode b f) for the d1 IH at b
    -- We get EvalRel A rho b from hu; we need convSound-inv d1 to get EvalRel A' rho b from A
    -- Actually d1 is at type U, and we evaluate A at rho.
    -- adequacyEqSub d1 needs EvalRel A rho b and FinMem b UCode
    eqD1 : EqVal H sA sA' U b UCode
    eqD1 = adequacyEqSub d1 sigma rho crho vs fits b evAb UCode evU bU

    valTyA  : ValTy H sA b
    valTyA  = fst eqD1
    valTyA' : ValTy H sA' b
    valTyA' = fst (snd eqD1)
    eqValTyAA' : EqValTy H sA sA' b
    eqValTyAA' = snd (snd eqD1)

    -- Semantic type equality EqValTy H sA' sA b for Val-EqValTy-fwd (Lemma 8)
    eqValTyA'A : EqValTy H sA' sA b
    eqValTyA'A = EqValTy-sym b cb eqValTyAA'

    -- Transport Val H N sA u0 b to Val H N sA u' a_arg
    -- (same as in ty-Pi case)
    transportVal : (u0 : FinEl) -> FinMem u0 b ->
      (N : Expr _) -> Val H N sA u0 b ->
      (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
      (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
      Val H N sA u' a_arg
    transportVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
      let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
          ca_arg   = EvalRel-coh A rho a_arg evA_arg
          a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
          sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
          c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
          le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
          le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
          fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
          fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
          vtA_b    = valTyA
          vtA_a    = adequacyEqSub d1 sigma rho crho vs fits a_arg evA_arg UCode evU a_argU
          vtA_a_fst = fst vtA_a
          vtA_sup  = ValTy-Sup H sA b a_arg comp_b_a bU a_argU vtA_b vtA_a_fst
          val1     = upVal H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup
                       cb c_sup valN vtA_sup
          val2     = restrictVal H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
          val3     = downVal H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
      in val3

    -- Build PiEdgeVal H sA sB b f (codomain validity for B)
    buildEdgeValB : PiEdgeVal H sA sB b f
    buildEdgeValB u0 v0 sel N valN =
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
                       transportVal u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub-extend sigma N rho u0 vs hyp0
          ih       = adequacyEqSub d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' v0 evB_u0_v0 UCode evU fm_v0_U
      in S.Eq-transport (\ T -> ValTy H T v0) (S.Eq-sym (substExpr-comp sigma B N)) (fst ih)

    -- Build PiEdgeEq H sA sB b f (codomain argument congruence for B)
    -- Same pattern as buildPiEdgeEq in ty-Pi case: two ValTy + buildEqValTy_B
    buildEdgeEqB : PiEdgeEq H sA sB b f
    buildEdgeEqB u0 v0 sel N1 N2 eqvalN =
      let valN1    = Val-from-EqVal-first u0 b eqvalN
          valN2    = Val-from-EqVal-second u0 b eqvalN
          vtN1     = buildEdgeValB u0 v0 sel N1 valN1
          vtN2     = buildEdgeValB u0 v0 sel N2 valN2
          fm_v0_U  = FinMem-Selection-UCode b sel allU cf
      in twoValTy-to-EqValTy v0 fm_v0_U vtN1 vtN2

    -- Build PiEdgeVal H sA' sB' b f (codomain validity for B')
    -- Uses Val-EqValTy-fwd (Lemma 8) to convert Val H N sA' u b -> Val H N sA u b
    buildEdgeValB' : PiEdgeVal H sA' sB' b f
    buildEdgeValB' u0 v0 sel N valN_A' =
      let valN_A = Val-EqValTy-fwd u0 b cb eqValTyA'A valN_A'
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
                       transportVal u0 fm_u0_b N (Val-EqValTy-fwd u0 b cb eqValTyA'A valN_A') u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub-extend sigma N rho u0 vs hyp0
          ih       = adequacyEqSub d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' v0 evB_u0_v0 UCode evU fm_v0_U
      in S.Eq-transport (\ T -> ValTy H T v0) (S.Eq-sym (substExpr-comp sigma B' N)) (fst (snd ih))

    -- Build PiEdgeEq H sA' sB' b f (codomain argument congruence for B')
    buildEdgeEqB' : PiEdgeEq H sA' sB' b f
    buildEdgeEqB' u0 v0 sel N1 N2 eqvalN_A' =
      let vtN1 = buildEdgeValB' u0 v0 sel N1 (Val-from-EqVal-first u0 b eqvalN_A')
          vtN2 = buildEdgeValB' u0 v0 sel N2 (Val-from-EqVal-second u0 b eqvalN_A')
          fm_v0_U = FinMem-Selection-UCode b sel allU cf
      in twoValTy-to-EqValTy v0 fm_v0_U vtN1 vtN2

    -- Build PiEdgeEqTy H sA sB sB' b f (heterogeneous codomain type equality)
    buildEdgeEqTyBB' : PiEdgeEqTy H sA sB sB' b f
    buildEdgeEqTyBB' u0 v0 sel P valP =
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
                       transportVal u0 fm_u0_b P valP u' cu' le_u' a_arg evA_arg fm_u'_a
          vs'      = ValidSub-extend sigma P rho u0 vs hyp0
          ih       = adequacyEqSub d2 (extSub sigma P) (extendEnv rho u0)
                       crho' vs' fits' v0 evB_u0_v0 UCode evU fm_v0_U
          eqvt     = S.Eq-transport (\ T -> EqValTy H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                       (S.Eq-transport (\ T -> EqValTy H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                         (snd (snd ih)))
      in eqvt

    -- Assemble ValTyPi H (Pi sA sB) b f
    valTyPiAB : ValTy H (Pi sA sB) (PiCode b f)
    valTyPiAB = mkSigma sA (mkSigma sB (mkSigma (Red-refl)
                  (mkSigma cf (mkSigma allU
                    (mkSigma valTyA (mkSigma buildEdgeValB buildEdgeEqB))))))

    -- Assemble ValTyPi H (Pi sA' sB') b f
    valTyPiA'B' : ValTy H (Pi sA' sB') (PiCode b f)
    valTyPiA'B' = mkSigma sA' (mkSigma sB' (mkSigma (Red-refl)
                    (mkSigma cf (mkSigma allU
                      (mkSigma valTyA' (mkSigma buildEdgeValB' buildEdgeEqB'))))))

    -- Assemble EqValTyPi H (Pi sA sB) (Pi sA' sB') b f
    eqValTyPi : EqValTy H (Pi sA sB) (Pi sA' sB') (PiCode b f)
    eqValTyPi = mkSigma valTyPiAB (mkSigma valTyPiA'B'
                  (mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                    (mkSigma (Red-refl)
                      (mkSigma (Red-refl)
                        (mkSigma cf (mkSigma allU
                          (mkSigma eqValTyAA' buildEdgeEqTyBB'))))))))))

-- adequacyEqSub: conv-funext (proved)
adequacyEqSub (conv-funext dA d1 d2 d3) sigma rho crho vs fits u hu a evA fm =
  adequacyEqSub-funext dA d1 d2 d3 sigma rho crho vs fits u hu a evA fm

-- adequacyEqSub: conv-App-fun (proved)
adequacyEqSub (conv-App-fun _ dB d1 d2) sigma rho crho vs fits u hu a evA fm =
  adequacyEqSub-App-fun dB d1 d2 sigma rho crho vs fits u hu a evA fm

-- adequacyEqSub: conv-App-arg (delegated to postulate)
adequacyEqSub (conv-App-arg _ dB d1 d2) sigma rho crho vs fits u hu a evA fm =
  adequacyEqSub-App-arg dB d1 d2 sigma rho crho vs fits u hu a evA fm

------------------------------------------------------------------------
-- Part 14: Closed-term corollary
------------------------------------------------------------------------

-- Adequacy for closed terms
adequacy : {M A : Expr zero} ->
  HasType empty M A ->
  (rho : EnvApprox zero) ->
  (u : FinEl) -> EvalRel M rho u ->
  (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
  Val empty M A u a
adequacy {M} {A} d emptyEnv u hu a evA fm =
  let val  = adequacySub d idSub emptyEnv tt (ValidSub-empty idSub emptyEnv) tt u hu a evA fm
      val' = S.Eq-transport (\ T -> Val empty (substExpr idSub M) T u a) (substExpr-id A) val
  in S.Eq-transport (\ E -> Val empty E A u a) (substExpr-id M) val'
