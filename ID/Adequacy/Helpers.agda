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

module ID.Adequacy.Helpers where

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ; Pair ; Eq ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons)
open import ID.Domain.Kernel using (LeCode ; LeCode-Bot ; LeCode-refl ; LeCode-trans ; Coherent ; CoherentFun ; Comp ; Comp-down ; Sup ; LeCode-Sup-left ; LeCode-Sup-right ; Coherent-Sup ; EvalFun ; EvalFun-in-UCode ; Coherent-EvalFun ; EvalFun-mon-arg ; LeFunCode ; LeFunCode-refl ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-a-in-U ; finMemUCode-Sup ; finMem-upward ; finMem-Sup-left ; finMem-Sup-right ; coh-from-aU ; FinMem-coh-u ; cft-from-cf ; CoherentFunTail ; CoherentFunTail-append ; mkCFT ; NotBot ; absurdEl)
open import ID.Syntax.Reduction using (Red ; mkRed ; Red-refl ; Red-hr ; HeadRed ; HeadRed-trans ; HeadRed-App ; HeadRed-strip-Pi ; headred-step ; headred-beta ; headred-refl ; subst-subst1-comm ; idSub ; substExpr-id)
open import ID.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ; EvalRel ; Pi-edgewise ; EvalRel-coh ; CoherentEnv ; lookupEnv-coh ; EvalRel-Comp ; EvalRel-Sup ; EvalRel-down ; EvalRel-mon-env ; EnvLe ; EnvLe-refl)
open import ID.Syntax.Raw using (Expr ; Var ; U ; Pi ; Lam ; App ; Id ; Ref ; J ; Fin ; fzero ; fsuc ; wkExpr ; subst1 ; Sub ; liftSub ; substExpr ; subst1Sub)
  renaming ()
open import ID.Syntax.Typing using (Ctx ; empty ; extend ; lookup ; HasType ; ConvTm ; WfCtx ; wf-empty ; wf-extend ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ; conv-refl ; conv-sym ; conv-trans ; conv-conv ; conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import ID.Validity.Public public
open import ID.Validity.Core using (Edge ; EdgeIn ; here ; there ; Red-unique-Pi ; FinMem-Coherent ; Selection ; sel-nil ; sel-skip ; sel-take ; Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ; bU-from-cf-fmU)
-- Re-import directly (Validity2Sigma re-exports don't always resolve)
open import ID.Validity.Core using () renaming (Red-unique-Pi to Red-unique-Pi2)
open import ID.Model.Selection using (FinMemAllU-Selection ; FinMem-Selection-UCode ; FinMem-Selection ; FinMem-Selection-codomain ; selectionBelow)
open import ID.Model.Soundness using (convSound ; convSound-inv ; convSound' ; theorem1 ; LeCode-Bot-eq)
open import ID.Model.SoundnessLemmas using (Fits ; Typed ; Fits-CoherentEnv)
open import ID.Model.EvalSubstitution using (EvalRel-subst1-backward ; EvalRel-wk ; EvalRel-unwk ; EvalRel-Pi-app-type ; EvalRel-Pi-body ; EvalRel-subst1-forward)

open import ID.Syntax.Raw using (Ren ; liftRen ; renExpr ; wkRen)
open import ID.Syntax.Substitution using (typing-ConvTm ; WtSub ; subst-HasType ; subst-ConvTm ; liftSub-WtSub ; subst1-WtSub ; typing-WfCtx ; typing-type ; ctx-conv-HasType ; ctx-conv-ConvTm ; subst1-cong-ConvTm ; wk-HasType ; wk-ConvTm ; WtConvSub ; subst-ConvTm-cross ; liftSub-WtConvSub)

------------------------------------------------------------------------
-- Eq helpers
------------------------------------------------------------------------

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans S.refl q = q

Eq-cong2 : {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f S.refl S.refl = S.refl

Eq-cong3 : {A B C D : Set} (f : A -> B -> C -> D) {a a' : A} {b b' : B} {c c' : C} ->
  Eq a a' -> Eq b b' -> Eq c c' -> Eq (f a b c) (f a' b' c')
Eq-cong3 f S.refl S.refl S.refl = S.refl

------------------------------------------------------------------------
-- Eq-transport helpers for Val2/EqVal2/ValTy2/EqValTy2
------------------------------------------------------------------------

Val2-transport-M : {n : Nat} {G : Ctx n} {M M' A : Expr n}
  {u a : FinEl} -> Eq M M' -> Val2 G M A u a -> Val2 G M' A u a
Val2-transport-M S.refl v = v

Val2-transport-A : {n : Nat} {G : Ctx n} {M A A' : Expr n}
  {u a : FinEl} -> Eq A A' -> Val2 G M A u a -> Val2 G M A' u a
Val2-transport-A S.refl v = v

EqVal2-transport-A : {n : Nat} {G : Ctx n} {M N A A' : Expr n}
  {u a : FinEl} -> Eq A A' -> EqVal2 G M N A u a -> EqVal2 G M N A' u a
EqVal2-transport-A S.refl v = v

ValTy2-transport : {n : Nat} {G : Ctx n} {M M' : Expr n}
  {u : FinEl} -> Eq M M' -> ValTy2 G M u -> ValTy2 G M' u
ValTy2-transport S.refl v = v

EqValTy2-transport : {n : Nat} {G : Ctx n} {M M' N N' : Expr n}
  {u : FinEl} -> Eq M M' -> Eq N N' -> EqValTy2 G M N u -> EqValTy2 G M' N' u
EqValTy2-transport S.refl S.refl v = v

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
substExpr-ext sigma sigma' hyp (Id A a b) =
  Eq-cong3 Id (substExpr-ext sigma sigma' hyp A) (substExpr-ext sigma sigma' hyp a) (substExpr-ext sigma sigma' hyp b)
substExpr-ext sigma sigma' hyp (Ref a) = S.Eq-cong Ref (substExpr-ext sigma sigma' hyp a)
substExpr-ext sigma sigma' hyp (J C d p) =
  Eq-cong3 J (substExpr-ext sigma sigma' hyp C) (substExpr-ext sigma sigma' hyp d) (substExpr-ext sigma sigma' hyp p)
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
substExpr-ren sigma rho (Id A a b) =
  Eq-cong3 Id (substExpr-ren sigma rho A) (substExpr-ren sigma rho a) (substExpr-ren sigma rho b)
substExpr-ren sigma rho (Ref a) = S.Eq-cong Ref (substExpr-ren sigma rho a)
substExpr-ren sigma rho (J C d p) =
  Eq-cong3 J (substExpr-ren sigma rho C) (substExpr-ren sigma rho d) (substExpr-ren sigma rho p)
substExpr-wk : {h g : Nat} (sigma : Sub h g) (M : Expr g) (t : Expr h) ->
  Eq (substExpr (extSub sigma t) (wkExpr M)) (substExpr sigma M)
substExpr-wk sigma M t = substExpr-ren (extSub sigma t) wkRen M

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
renExpr-ext r1 r2 hyp (Id A a b) =
  Eq-cong3 Id (renExpr-ext r1 r2 hyp A) (renExpr-ext r1 r2 hyp a) (renExpr-ext r1 r2 hyp b)
renExpr-ext r1 r2 hyp (Ref a) = S.Eq-cong Ref (renExpr-ext r1 r2 hyp a)
renExpr-ext r1 r2 hyp (J C d p) =
  Eq-cong3 J (renExpr-ext r1 r2 hyp C) (renExpr-ext r1 r2 hyp d) (renExpr-ext r1 r2 hyp p)
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
renExpr-comp r2 r1 (Id A a b) =
  Eq-cong3 Id (renExpr-comp r2 r1 A) (renExpr-comp r2 r1 a) (renExpr-comp r2 r1 b)
renExpr-comp r2 r1 (Ref a) = S.Eq-cong Ref (renExpr-comp r2 r1 a)
renExpr-comp r2 r1 (J C d p) =
  Eq-cong3 J (renExpr-comp r2 r1 C) (renExpr-comp r2 r1 d) (renExpr-comp r2 r1 p)
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
renExpr-substExpr rho sigma (Id A a b) =
  Eq-cong3 Id (renExpr-substExpr rho sigma A) (renExpr-substExpr rho sigma a) (renExpr-substExpr rho sigma b)
renExpr-substExpr rho sigma (Ref a) = S.Eq-cong Ref (renExpr-substExpr rho sigma a)
renExpr-substExpr rho sigma (J C d p) =
  Eq-cong3 J (renExpr-substExpr rho sigma C) (renExpr-substExpr rho sigma d) (renExpr-substExpr rho sigma p)
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
substExpr-sub tau sigma (Id A a b) =
  Eq-cong3 Id (substExpr-sub tau sigma A) (substExpr-sub tau sigma a) (substExpr-sub tau sigma b)
substExpr-sub tau sigma (Ref a) = S.Eq-cong Ref (substExpr-sub tau sigma a)
substExpr-sub tau sigma (J C d p) =
  Eq-cong3 J (substExpr-sub tau sigma C) (substExpr-sub tau sigma d) (substExpr-sub tau sigma p)
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
EvalRel-bot (Var i)     rho = mkSigma tt (ID.Domain.Kernel.LeCode-Bot (lookupEnv i rho))
EvalRel-bot U           rho = mkSigma tt (ID.Domain.Kernel.LeCode-Bot UCode)
EvalRel-bot (Pi A B)    rho = tt
EvalRel-bot (Lam A M)   rho = tt
EvalRel-bot (App f a)   rho = tt
EvalRel-bot (Id A a b)  rho = tt
EvalRel-bot (Ref a)     rho = tt
EvalRel-bot (J C d p)   rho =
  mkSigma Bot (mkSigma (EvalRel-bot p rho) (mkSigma tt (LeCode-Bot Bot)))
Coherent-CoherentFun : (b : FinEl) (f : FinFun) ->
  Coherent (PiCode b f) -> CoherentFunTail f
Coherent-CoherentFun b f cpf = snd cpf

FinMem-bU-from-Pi : (b : FinEl) (f : FinFun) ->
  CoherentFun f -> FinMemAllU f b -> FinMem b UCode
FinMem-bU-from-Pi b f cf fmAllU = bU-from-cf-fmU f b cf fmAllU

FinMem-from-LeCode-UCode : (u : FinEl) -> LeCode u UCode -> FinMem u UCode
FinMem-from-LeCode-UCode Bot              le = tt
FinMem-from-LeCode-UCode UCode            le = tt
FinMem-from-LeCode-UCode (FunEl g)        ()
FinMem-from-LeCode-UCode (PiCode a f)     ()
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
ty-Pi-invert (ty-conv d _ _) = ty-Pi-invert d

typing-Pi-codomain : {n : Nat} {G : Ctx n}
  {A : Expr n} {B : Expr (suc n)} {M : Expr n} ->
  HasType G A U -> HasType G M (Pi A B) ->
  HasType (extend G A) B U
typing-Pi-codomain dA dM = snd (ty-Pi-invert (typing-type dM))

-- Val2-U-to-ValTy2, sup-transport-*, app-transport-* live in ID.Adequacy.agda
-- (before the mutual block). They are NOT duplicated here to avoid clashes.
