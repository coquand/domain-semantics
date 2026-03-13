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
  finMem-upward)
open import Reduction using (Red ; Red-wk ; red-to-conv ;
  Red-refl ; Red-trans ; Red-beta-expand ; Red-Pi-inj ; Red-from-conv)
open import RawSemantics using (EnvApprox ; emptyEnv ; extendEnv ;
  lookupEnv ; EvalRel ; Pi-edgewise)
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
  downVal ; upVal ; restrictVal ;
  downEqVal ; upEqVal ; restrictEqVal ;
  Val-conv-type ; EqVal-conv-type ;
  FinMemAllU-lookup ;
  PiAppVal-lookup ;
  FinMemFun-lookup ;
  Or ; left ; right ;
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ;
  Val-to-EqVal ;
  Val-from-EqVal-first ; Val-from-EqVal-second ;
  EqVal-sym ; EqValTy-sym)
open import TypingSemantics using (convSound ; convSound-inv)
open import EvalSubstitution using (EvalRel-subst1-backward)

open import RawSyntax using (Ren ; liftRen ; renExpr ; wkRen)

postulate
  evalFun-sat-witness :
    (full : FinFun) -> CoherentFun full ->
    (rest : FinFun) -> CoherentFun rest ->
    ((e : Edge) -> EdgeIn e rest -> EdgeIn e full) ->
    (v : FinEl) -> Coherent v ->
    Or (Eq (EvalFun rest v) Bot)
       (Sigma FinEl \ v* -> Sigma FinEl \ w* ->
         Pair (EdgeIn (mkSigma v* w*) full)
              (Pair (LeCode v* v) (LeCode (EvalFun rest v) w*)))

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

-- Substitution preserves conversion (postulated — standard metatheorem)
postulate
  ConvTm-subst : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) ->
    ConvTm H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A)

------------------------------------------------------------------------
-- Part 3: EvalRel properties
--
-- Properties of the finite evaluation relation needed for adequacy.
-- Proved in GeneralSemantics via the Dom construction; restated here
-- in purely finite terms.
------------------------------------------------------------------------

-- Coherence from EvalRel: every evaluation witness is coherent
EvalRel-coh : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> EvalRel M rho u -> Coherent u
EvalRel-coh (Var i) rho u ev = fst ev
EvalRel-coh U rho Bot ev = tt
EvalRel-coh U rho UCode ev = tt
EvalRel-coh U rho (FunEl g) ()
EvalRel-coh U rho (PiCode b f) ()
EvalRel-coh (App f a) rho Bot ev = tt
EvalRel-coh (App f a) rho UCode ev = fst ev
EvalRel-coh (App f a) rho (FunEl g) ev = fst ev
EvalRel-coh (App f a) rho (PiCode b0 f0) ev = fst ev
EvalRel-coh (Lam A M) rho Bot ev = tt
EvalRel-coh (Lam A M) rho (FunEl g) ev = fst (snd ev)
EvalRel-coh (Lam A M) rho UCode ()
EvalRel-coh (Lam A M) rho (PiCode b f) ()
EvalRel-coh (Pi A B) rho Bot ev = tt
EvalRel-coh (Pi A B) rho (PiCode b f) ev = fst ev
EvalRel-coh (Pi A B) rho UCode ()
EvalRel-coh (Pi A B) rho (FunEl g) ()

-- Remaining EvalRel properties (proved in GeneralSemantics, restated)
postulate
  -- Weakening: EvalRel M rho u -> EvalRel (wkExpr M) (extendEnv rho v) u
  EvalRel-wk : {n : Nat} (M : Expr n) (rho : EnvApprox n)
    (v u : FinEl) -> EvalRel M rho u -> EvalRel (wkExpr M) (extendEnv rho v) u

  -- Compatibility: two witnesses from the same expression are compatible
  EvalRel-comp : {n : Nat} (M : Expr n) (rho : EnvApprox n)
    (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> Comp u v

  -- Sup closure: compatible witnesses have a Sup witness
  EvalRel-sup : {n : Nat} (M : Expr n) (rho : EnvApprox n)
    (u v : FinEl) -> Comp u v ->
    EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)

  -- Downward closure: smaller coherent elements also evaluate
  EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox n)
    (u v : FinEl) -> Coherent u -> LeCode u v ->
    EvalRel M rho v -> EvalRel M rho u

------------------------------------------------------------------------
-- Part 4: Adequacy predicates (FINITE)
--
-- Adeq H M A rho Asrc u :
--   There exists a type code a with EvalRel Asrc rho a, FinMem u a,
--   and Val H M A u a.  rho : EnvApprox g is the source environment,
--   Asrc : Expr g is the source type expression.
------------------------------------------------------------------------

Adeq : {h g : Nat} -> Ctx h -> Expr h -> Expr h ->
  EnvApprox g -> Expr g -> FinEl -> Set
Adeq H M A rho Asrc u =
  Sigma FinEl \ a ->
    Pair (EvalRel Asrc rho a)
         (Pair (FinMem u a) (Val H M A u a))

AdeqEq : {h g : Nat} -> Ctx h -> Expr h -> Expr h -> Expr h ->
  EnvApprox g -> Expr g -> FinEl -> Set
AdeqEq H M N A rho Asrc u =
  Sigma FinEl \ a ->
    Pair (EvalRel Asrc rho a)
         (Pair (FinMem u a) (EqVal H M N A u a))

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
EvalRel-transport S.refl h = h

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
      a   = fst aq
      ha  = fst (snd aq)
      fm  = fst (snd (snd aq))
      val = snd (snd (snd aq))
      ha' = EvalRel-wk Asrc rho v a ha
      eq  = S.Eq-sym (substExpr-wk sigma Asrc t)
      val' = S.Eq-transport (\ T -> Val H t T u a) eq val
  in mkSigma a (mkSigma ha' (mkSigma fm val'))
ValidSub-extend {h} {g} {H} {G} {Asrc} sigma t rho v vs hyp0 (fsuc i) u cu le =
  let aq  = vs i u cu le
      a   = fst aq
      ha  = fst (snd aq)
      fm  = fst (snd (snd aq))
      val = snd (snd (snd aq))
      ha' = EvalRel-wk (lookup G i) rho v a ha
      eq  = S.Eq-sym (substExpr-wk sigma (lookup G i) t)
      val' = S.Eq-transport (\ T -> Val H (sigma i) T u a) eq val
  in mkSigma a (mkSigma ha' (mkSigma fm val'))

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
Coherent-CoherentFun b f cpf = snd (snd cpf)

-- FinMemAllU from Coherent(PiCode) — just projection
FinMemAllU-from-Coherent : (f : FinFun) (b : FinEl) ->
  Coherent (PiCode b f) -> FinMemAllU f b
FinMemAllU-from-Coherent f b cpf = fst (snd cpf)

-- FinMem b UCode from Coherent(PiCode) — identity
FinMem-UCode-from-Coherent : (b : FinEl) ->
  PaperSemantics.FinMem b UCode -> FinMem b UCode
FinMem-UCode-from-Coherent b fm = fm

-- EqVal symmetry — now proved in Validity with Coherent args
-- We derive Coherent from the call context
EqVal-sym-fn : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal G M N A u a -> EqVal G N M A u a
EqVal-sym-fn u a cu ca ev = EqVal-sym u a cu ca ev

postulate
  -- EqVal transitivity with alignment (Sup + upEqVal + trans)
  EqVal-trans-aligned : {n : Nat} {G : Ctx n} {M N P A : Expr n}
    (u a1 a2 : FinEl) ->
    Comp a1 a2 -> Coherent a1 -> Coherent a2 ->
    FinMem u a1 -> FinMem u a2 ->
    EqVal G M N A u a1 -> EqVal G N P A u a2 ->
    Pair (FinMem u (Sup a1 a2))
         (EqVal G M P A u (Sup a1 a2))

  -- Restrict Adeq from value v to smaller value u <= v (FINITE)
  Adeq-from-Val-restrict : {h g : Nat} {H : Ctx h} {M A : Expr h}
    {rho : EnvApprox g} {Asrc : Expr g}
    (u v b : FinEl) ->
    EvalRel Asrc rho b -> Coherent u -> Coherent v -> Coherent b ->
    LeCode u v -> FinMem v b ->
    Val H M A v b ->
    Adeq H M A rho Asrc u

  -- Pi codomain evaluation at EvalFun result (FINITE)
  -- Combines Pi codomain extraction with substitution backward.
  EvalRel-Pi-app-type :
    {n : Nat} (A : Expr n) (B : Expr (suc n)) (a : Expr n)
    (rho : EnvApprox n) (b : FinEl) (f : FinFun) (v : FinEl) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel a rho v ->
    EvalRel (subst1 B a) rho (EvalFun f v)

------------------------------------------------------------------------
-- Part 11: PiEdgeEq (postulated)
------------------------------------------------------------------------

postulate
  PiEdgeEq-from-IH : {n : Nat} (G : Ctx n) (A : Expr n)
    (B : Expr (suc n)) (b : FinEl) (f : FinFun) ->
    FinMemAllU f b -> PiEdgeEq G A B b f

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
    ValidSub H G sigma rho ->
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
    ValidSub H G sigma rho ->
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
    ValidSub H G sigma rho ->
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
    ValidSub H G sigma rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    AdeqEq H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             rho (subst1 B a) u

  -- conv-App-arg
  adequacyEqSub-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    ValidSub H G sigma rho ->
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
EvalRel-bot U         rho = PaperSemantics.LeCode-Bot UCode
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
    ValidSub H G0 sigma rho ->
    (u : FinEl) -> Coherent u ->
    (g : FinFun) -> (x v_sel : FinEl) ->
    EvalRel f' rho (FunEl g) -> EvalRel a rho x ->
    Selection g x v_sel -> LeCode u v_sel ->
    Adeq H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a))
      rho (subst1 B a) u

{-# TERMINATING #-}

-- Main adequacy theorem
adequacySub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M A : Expr g} ->
  HasType G M A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  ValidSub H G sigma rho ->
  (u : FinEl) -> EvalRel M rho u ->
  Adeq H (substExpr sigma M) (substExpr sigma A) rho A u

-- Adequacy for conversion
adequacyEqSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {M N A : Expr g} ->
  ConvTm G M N A ->
  (sigma : Sub h g) -> (rho : EnvApprox g) ->
  ValidSub H G sigma rho ->
  (u : FinEl) -> EvalRel M rho u ->
  AdeqEq H (substExpr sigma M) (substExpr sigma N)
           (substExpr sigma A) rho A u

-- adequacySub: ty-var
-- EvalRel (Var i) rho u = Pair (Coherent u) (LeCode u (lookupEnv i rho))
adequacySub (ty-var {G = G} {i = i} _) sigma rho vs u hu =
  vs i u (fst hu) (snd hu)

-- adequacySub: ty-U
-- EvalRel U rho u = LeCode u UCode
adequacySub (ty-U _) sigma rho vs u hu =
  mkSigma UCode
    (mkSigma (LeCode-refl UCode tt)
      (mkSigma (FinMem-from-LeCode-UCode u hu)
               (ValTy-U _ u hu)))

-- adequacySub: ty-conv
adequacySub (ty-conv {M = M} {A = A} {B = B} d1 d2) sigma rho vs u hu =
  let aq   = adequacySub d1 sigma rho vs u hu
      a    = fst aq
      ha   = fst (snd aq)
      fm   = fst (snd (snd aq))
      val  = snd (snd (snd aq))
      ha'  = convSound d2 rho a ha
      convH = ConvTm-subst d2 sigma
      val' = Val-conv-type u a convH val
  in mkSigma a (mkSigma ha' (mkSigma fm val'))

-- adequacySub: ty-Pi
-- EvalRel (Pi A B) rho Bot = Top
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho vs Bot hu =
  mkSigma Bot (mkSigma (EvalRel-bot U rho) (mkSigma tt tt))
-- EvalRel (Pi A B) rho UCode = Empty
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho vs UCode ()
-- EvalRel (Pi A B) rho (FunEl g) = Empty
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho vs (FunEl g) ()
-- EvalRel (Pi A B) rho (PiCode b f) = Pair (Coherent ...) (Pair (EvalRel A rho b) (body ...))
adequacySub {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho vs (PiCode b f)
  (mkSigma cpu (mkSigma evA allP)) =
  let sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      -- From Coherent (PiCode b f):
      fmBU    = FinMem-UCode-from-Coherent b (fst cpu)
      fmAllU  = FinMemAllU-from-Coherent f b cpu
      cg      = Coherent-CoherentFun b f cpu
      cb      = FinMem-Coherent b UCode fmBU
      -- ValTy H sA b from IH on d1
      aq1     = adequacySub d1 sigma rho vs b evA
      a1      = fst aq1
      ha1     = fst (snd aq1)
      fm1     = fst (snd (snd aq1))
      val1    = snd (snd (snd aq1))
      le1     = ha1
      ca1     = LeCode-UCode-Coherent a1 ha1
      valTyA  = upVal H sA U b a1 UCode le1 fm1 fmBU ca1 tt val1 tt
      -- PiEdgeVal from IH on d2
      pev     = buildPiEdgeVal
      -- PiEdgeEq from postulate
      peq     = PiEdgeEq-from-IH H sA sB b f fmAllU
      -- Assemble ValTyPi
      valTyPi : ValTyPi H (Pi sA sB) b f
      valTyPi = mkSigma sA (mkSigma sB (mkSigma Red-refl
                  (mkSigma cg (mkSigma fmAllU
                    (mkSigma valTyA (mkSigma pev peq))))))
      -- FinMem (PiCode b f) UCode
      fmPiU : FinMem (PiCode b f) UCode
      fmPiU = mkSigma fmBU (mkSigma fmAllU cg)
  in mkSigma UCode (mkSigma (LeCode-refl UCode tt) (mkSigma fmPiU valTyPi))
  where
    sA  = substExpr sigma A
    sB  = substExpr (liftSub sigma) B
    fmBU' = FinMem-UCode-from-Coherent b
              (fst (fst (mkSigma cpu (mkSigma evA allP))))
    cb'   = FinMem-Coherent b UCode fmBU'
    -- Build a single edge function (Selection-based)
    -- Pi-edgewise gives (x, LeCode x v, FinMem x b, EvalRel B (rho,x) w)
    -- for each edge (v,w) in f.
    piEdge : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ x ->
        Pair (LeCode x (fst p))
             (Pair (FinMem x b)
                   (EvalRel B (extendEnv rho x) (snd p))))
    piEdge = snd (snd (Pi-edgewise A B rho b f (mkSigma cpu (mkSigma evA allP))))
    buildEdgeFn : (v w : FinEl) -> FinMem v b -> FinMem w UCode ->
      EdgeIn (mkSigma v w) f ->
      (N : Expr _) -> Val H N sA v b -> ValTy H (subst1 sB N) w
    buildEdgeFn v w fmvb fmwU ein N valN =
      let pew  = piEdge (mkSigma v w) ein
          x    = fst pew
          lxv  = fst (snd pew)
          fmxb = fst (snd (snd pew))
          evBxw = snd (snd (snd pew))
          cx   = FinMem-Coherent x b fmxb
          cv   = FinMem-Coherent v b fmvb
          -- Restrict Val from v to x (x <= v)
          fm-x-b = fmxb
          valN-x = restrictVal H N sA v x b lxv fm-x-b cv cb' valN
          -- Build extended ValidSub at x
          newVar : (u' : FinEl) -> Coherent u' -> LeCode u' x ->
                   Adeq H N (substExpr sigma A) rho A u'
          newVar u' cu' le' = Adeq-from-Val-restrict {M = N}
                            {A = substExpr sigma A} {rho = rho} {Asrc = A}
                            u' x b evA cu' cx cb' le' fmxb valN-x
          vs_ext = ValidSub-extend sigma N rho x vs newVar
          aq2   = adequacySub d2 (extSub sigma N) (extendEnv rho x) vs_ext w evBxw
          a2    = fst aq2
          ha2   = fst (snd aq2)
          fm2   = fst (snd (snd aq2))
          val2  = snd (snd (snd aq2))
          -- upVal to UCode
          le2   = ha2
          ca2   = LeCode-UCode-Coherent a2 ha2
          vt2   = upVal H (substExpr (extSub sigma N) B) U w a2 UCode
                    le2 fm2 fmwU ca2 tt val2 tt
          -- Transport: substExpr (extSub sigma N) B = subst1 sB N
          eq : Eq (substExpr (extSub sigma N) B) (subst1 sB N)
          eq = S.Eq-sym (substExpr-comp sigma B N)
      in S.Eq-transport (\ T -> ValTy H T w) eq vt2
    -- Build PiEdgeVal (Selection-based; postulated)
    postulate
      buildPiEdgeVal : PiEdgeVal H sA sB b f

-- adequacySub: ty-Lam (delegated to postulate)
adequacySub (ty-Lam d1 d2 d3) sigma rho vs u hu =
  adequacySub-Lam d1 d2 d3 sigma rho vs u hu

-- adequacySub: ty-App
-- EvalRel (App f a) rho Bot = Top
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho vs Bot hu =
  mkSigma Bot (mkSigma (EvalRel-bot (subst1 B a) rho) (mkSigma tt tt))
-- Non-Bot cases: dispatch to adequacySub-App postulate
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho vs UCode (mkSigma cu evidence) =
  adequacySub-App dA d1 d2 sigma rho vs UCode cu
    (fst evidence) (fst (snd evidence)) (fst (snd (snd evidence)))
    (fst (snd (snd (snd evidence)))) (fst (snd (snd (snd (snd evidence)))))
    (fst (snd (snd (snd (snd (snd evidence)))))) (snd (snd (snd (snd (snd (snd evidence))))))
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho vs (FunEl g') (mkSigma cu evidence) =
  adequacySub-App dA d1 d2 sigma rho vs (FunEl g') cu
    (fst evidence) (fst (snd evidence)) (fst (snd (snd evidence)))
    (fst (snd (snd (snd evidence)))) (fst (snd (snd (snd (snd evidence)))))
    (fst (snd (snd (snd (snd (snd evidence)))))) (snd (snd (snd (snd (snd (snd evidence))))))
adequacySub {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA d1 d2) sigma rho vs (PiCode b0' f0') (mkSigma cu evidence) =
  adequacySub-App dA d1 d2 sigma rho vs (PiCode b0' f0') cu
    (fst evidence) (fst (snd evidence)) (fst (snd (snd evidence)))
    (fst (snd (snd (snd evidence)))) (fst (snd (snd (snd (snd evidence)))))
    (fst (snd (snd (snd (snd (snd evidence)))))) (snd (snd (snd (snd (snd (snd evidence))))))

-- adequacyEqSub: conv-refl
adequacyEqSub (conv-refl d) sigma rho vs u hu =
  let aq  = adequacySub d sigma rho vs u hu
      a   = fst aq
      ha  = fst (snd aq)
      fm  = fst (snd (snd aq))
      val = snd (snd (snd aq))
  in mkSigma a (mkSigma ha (mkSigma fm (Val-to-EqVal u a val)))

-- adequacyEqSub: conv-sym
adequacyEqSub (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho vs u hu =
  let huN  = convSound-inv d rho u hu
      aq   = adequacyEqSub d sigma rho vs u huN
      a    = fst aq
      ha   = fst (snd aq)
      fm   = fst (snd (snd aq))
      eval = snd (snd (snd aq))
      cu   = EvalRel-coh N rho u hu
      ca   = EvalRel-coh Asrc rho a ha
  in mkSigma a (mkSigma ha (mkSigma fm (EqVal-sym-fn u a cu ca eval)))

-- adequacyEqSub: conv-trans
adequacyEqSub {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho vs u hu =
  let huN  = convSound d1 rho u hu
      -- IH on d1: EqVal M N at u
      aq1  = adequacyEqSub d1 sigma rho vs u hu
      a1   = fst aq1
      ha1  = fst (snd aq1)
      fm1  = fst (snd (snd aq1))
      eq1  = snd (snd (snd aq1))
      -- IH on d2: EqVal N P at u
      aq2  = adequacyEqSub d2 sigma rho vs u huN
      a2   = fst aq2
      ha2  = fst (snd aq2)
      fm2  = fst (snd (snd aq2))
      eq2  = snd (snd (snd aq2))
      -- Align via EqVal-trans-aligned (handles Sup + upEqVal + trans internally)
      ca1  = EvalRel-coh A rho a1 ha1
      ca2  = EvalRel-coh A rho a2 ha2
      comp = EvalRel-comp A rho a1 a2 ha1 ha2
      ha12 = EvalRel-sup A rho a1 a2 comp ha1 ha2
      res  = EqVal-trans-aligned u a1 a2 comp ca1 ca2 fm1 fm2 eq1 eq2
      fm12 = fst res
      eq12 = snd res
  in mkSigma (Sup a1 a2) (mkSigma ha12 (mkSigma fm12 eq12))

-- adequacyEqSub: conv-conv
adequacyEqSub (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2) sigma rho vs u hu =
  let aq   = adequacyEqSub d1 sigma rho vs u hu
      a    = fst aq
      ha   = fst (snd aq)
      fm   = fst (snd (snd aq))
      eval = snd (snd (snd aq))
      ha'  = convSound d2 rho a ha
      convH = ConvTm-subst d2 sigma
      eval' = EqVal-conv-type u a convH eval
  in mkSigma a (mkSigma ha' (mkSigma fm eval'))

-- adequacyEqSub: conv-beta (delegated to postulate)
adequacyEqSub (conv-beta d1 d2 d3 d4) sigma rho vs u hu =
  adequacyEqSub-beta d1 d2 d3 d4 sigma rho vs u hu

-- adequacyEqSub: conv-Pi (proved inline)
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho vs Bot hu =
  mkSigma Bot (mkSigma (EvalRel-bot U rho) (mkSigma tt tt))
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho vs UCode ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho vs (FunEl g) ()
adequacyEqSub {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho vs (PiCode b f)
  (mkSigma cpu (mkSigma evA allP)) =
  let sA  = substExpr sigma A
      sA' = substExpr sigma A'
      sB  = substExpr (liftSub sigma) B
      sB' = substExpr (liftSub sigma) B'
      -- From Coherent (PiCode b f):
      fmBU    = FinMem-UCode-from-Coherent b (fst cpu)
      fmAllU  = FinMemAllU-from-Coherent f b cpu
      cg      = Coherent-CoherentFun b f cpu
      cb      = FinMem-Coherent b UCode fmBU
      -- EqValTy H sA sA' b from IH on d1 via upEqVal
      aq1     = adequacyEqSub d1 sigma rho vs b evA
      a1      = fst aq1
      ha1     = fst (snd aq1)
      fm1     = fst (snd (snd aq1))
      eval1   = snd (snd (snd aq1))
      le1     = ha1
      ca1     = LeCode-UCode-Coherent a1 ha1
      eqValTyA-full = upEqVal H sA sA' U b a1 UCode le1 fm1 fmBU ca1 tt eval1 tt
      eqValTyA = snd (snd eqValTyA-full)
      -- PiEdgeEqTy from IH on d2 (postulated)
      peqt    = buildPiEdgeEqTy
      -- Assemble EqValTyPi
      eqValTyPi : EqValTyPi H (Pi sA sB) (Pi sA' sB') b f
      eqValTyPi = mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                    (mkSigma Red-refl (mkSigma Red-refl
                      (mkSigma cg (mkSigma fmAllU
                        (mkSigma eqValTyA peqt))))))))
      -- FinMem (PiCode b f) UCode
      fmPiU : FinMem (PiCode b f) UCode
      fmPiU = mkSigma fmBU (mkSigma fmAllU cg)
      -- ValTyPi wrappers for EqVal bundling at UCode
      vtyM : ValTyPi H (Pi sA sB) b f
      vtyM = mkSigma sA (mkSigma sB (mkSigma Red-refl
               (mkSigma cg (mkSigma fmAllU
                 (mkSigma (fst eqValTyA-full)
                 (mkSigma buildPiEdgeVal-M buildPiEdgeEq-M))))))
      vtyN : ValTyPi H (Pi sA' sB') b f
      vtyN = mkSigma sA' (mkSigma sB' (mkSigma Red-refl
               (mkSigma cg (mkSigma fmAllU
                 (mkSigma (fst (snd eqValTyA-full))
                 (mkSigma buildPiEdgeVal-N buildPiEdgeEq-N))))))
      -- Assemble: EqVal at (PiCode b f, UCode) =
      --   Pair (ValTy M) (Pair (ValTy N) (Pair (ValTy M) (Pair (ValTy N) EqValTyPi)))
      eqval : EqVal H (Pi sA sB) (Pi sA' sB') U (PiCode b f) UCode
      eqval = mkSigma vtyM (mkSigma vtyN (mkSigma vtyM (mkSigma vtyN eqValTyPi)))
  in mkSigma UCode (mkSigma (LeCode-refl UCode tt) (mkSigma fmPiU eqval))
  where
    sA  = substExpr sigma A
    sA' = substExpr sigma A'
    sB  = substExpr (liftSub sigma) B
    sB' = substExpr (liftSub sigma) B'
    fmBU' = FinMem-UCode-from-Coherent b (fst cpu)
    cb'   = FinMem-Coherent b UCode fmBU'
    -- Pi-edgewise for edge extraction
    piEdge : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ x0 ->
        Pair (LeCode x0 (fst p))
             (Pair (FinMem x0 b)
                   (EvalRel B (extendEnv rho x0) (snd p))))
    piEdge = snd (snd (Pi-edgewise A B rho b f (mkSigma cpu (mkSigma evA allP))))
    -- Build a single edge function for EqTy (Selection-based)
    buildEdgeEqTyFn : (v w : FinEl) -> FinMem v b -> FinMem w UCode ->
      EdgeIn (mkSigma v w) f ->
      (P : Expr _) -> Val H P sA v b -> EqValTy H (subst1 sB P) (subst1 sB' P) w
    buildEdgeEqTyFn v w fmvb fmwU ein P valP =
      let pew   = piEdge (mkSigma v w) ein
          x0    = fst pew
          lx0v  = fst (snd pew)
          fmx0b = fst (snd (snd pew))
          evBx0w = snd (snd (snd pew))
          cx0   = FinMem-Coherent x0 b fmx0b
          cv    = FinMem-Coherent v b fmvb
          -- Restrict Val from v to x0 (x0 <= v)
          valP-x0 = restrictVal H P sA v x0 b lx0v fmx0b cv cb' valP
          -- Build extended ValidSub at x0
          newVar : (u' : FinEl) -> Coherent u' -> LeCode u' x0 ->
                   Adeq H P (substExpr sigma A) rho A u'
          newVar u' cu' le' = Adeq-from-Val-restrict {M = P}
                            {A = substExpr sigma A} {rho = rho} {Asrc = A}
                            u' x0 b evA cu' cx0 cb' le' fmx0b valP-x0
          vs_ext = ValidSub-extend sigma P rho x0 vs newVar
          aq2   = adequacyEqSub d2 (extSub sigma P) (extendEnv rho x0) vs_ext w evBx0w
          a2    = fst aq2
          ha2   = fst (snd aq2)
          fm2   = fst (snd (snd aq2))
          eval2 = snd (snd (snd aq2))
          -- upEqVal to UCode
          le2   = ha2
          ca2   = LeCode-UCode-Coherent a2 ha2
          evt2-full = upEqVal H (substExpr (extSub sigma P) B) (substExpr (extSub sigma P) B') U w a2 UCode
                        le2 fm2 fmwU ca2 tt eval2 tt
          evt2  = snd (snd evt2-full)
          -- Transport
          eqB : Eq (substExpr (extSub sigma P) B) (subst1 sB P)
          eqB = S.Eq-sym (substExpr-comp sigma B P)
          eqB' : Eq (substExpr (extSub sigma P) B') (subst1 sB' P)
          eqB' = S.Eq-sym (substExpr-comp sigma B' P)
      in S.Eq-transport (\ T -> EqValTy H (subst1 sB P) T w) eqB'
           (S.Eq-transport (\ T -> EqValTy H T (substExpr (extSub sigma P) B') w) eqB evt2)
    -- Build PiEdgeVal/Eq and PiEdgeEqTy (Selection-based; postulated)
    postulate
      buildPiEdgeVal-M : PiEdgeVal H sA sB b f
      buildPiEdgeEq-M  : PiEdgeEq H sA sB b f
      buildPiEdgeVal-N : PiEdgeVal H sA' sB' b f
      buildPiEdgeEq-N  : PiEdgeEq H sA' sB' b f
      buildPiEdgeEqTy : PiEdgeEqTy H sA sB sB' b f

-- adequacyEqSub: conv-funext (delegated to postulate)
adequacyEqSub (conv-funext _ d1 d2 d3) sigma rho vs u hu =
  adequacyEqSub-funext d1 d2 d3 sigma rho vs u hu

-- adequacyEqSub: conv-App-fun (delegated to postulate)
adequacyEqSub (conv-App-fun _ d1 d2) sigma rho vs u hu =
  adequacyEqSub-App-fun d1 d2 sigma rho vs u hu

-- adequacyEqSub: conv-App-arg (delegated to postulate)
adequacyEqSub (conv-App-arg _ d1 d2) sigma rho vs u hu =
  adequacyEqSub-App-arg d1 d2 sigma rho vs u hu

------------------------------------------------------------------------
-- Part 14: Closed-term corollary
------------------------------------------------------------------------

-- Adequacy for closed terms
adequacy : {M A : Expr zero} ->
  HasType empty M A ->
  (rho : EnvApprox zero) ->
  (u : FinEl) -> EvalRel M rho u ->
  Adeq empty M A rho A u
adequacy {M} {A} d rho u hu =
  let aq   = adequacySub d idSub rho (ValidSub-empty idSub rho) u hu
      a    = fst aq
      ha   = fst (snd aq)
      fm   = fst (snd (snd aq))
      val  = snd (snd (snd aq))
      val' = S.Eq-transport (\ T -> Val empty (substExpr idSub M) T u a)
               (substExpr-id A) val
      val'' = S.Eq-transport (\ E -> Val empty E A u a)
                (substExpr-id M) val'
  in mkSigma a (mkSigma ha (mkSigma fm val''))
