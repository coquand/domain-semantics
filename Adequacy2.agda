{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- Adequacy2.agda
--
-- Bundled adequacy layer: produces Val2/EqVal2 (with HasType/ConvTm
-- at leaves) instead of Val/EqVal.
--
-- Architecture mirrors Adequacy.agda exactly, but:
--   1. ValidSub2 produces Val2 (not Val)
--   2. adequacySub2 / adequacyEqSub2 mirror Adequacy.agda
--   3. Pi record constructions include HasType/ConvTm as first fields
--
-- PHASE 1: Simple cases fully proved.
-- PHASE 2: Hard cases (ty-Pi, ty-Lam, ty-App, conv-Pi, conv-beta,
--           conv-funext, conv-App-fun, conv-App-arg) left as postulates.
------------------------------------------------------------------------

module Adequacy2 where

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
  FinMem-coh-u ; cft-from-cf ; CoherentFunTail ; CoherentFunTail-append)
open import Reduction using (Red ; Red-refl ; HeadRed ;
  headred-step ; headred-beta ; headred-refl ; subst-subst1-comm ;
  idSub ; substExpr-id)
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
  ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import Validity2 using (
  Val2 ; EqVal2 ; ValTy2 ; EqValTy2 ;
  ValTyPi2 ; ValPi2 ; EqValTyPi2 ; EqValPi2 ;
  PiEdgeVal2 ; PiEdgeEq2 ; PiEdgeEqTy2 ;
  PiAppVal2 ; PiAppEq2 ; PiAppEqVal2 ;
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
  Val2-beta-expand ; Val2-headred-contract ; EqVal2-headred-expand ;
  twoVal2-to-EqVal2 ; twoValTy2-to-EqValTy2)
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

open import RawSyntax using (Ren ; liftRen ; renExpr ; wkRen)

------------------------------------------------------------------------
-- Eq helpers (same as Adequacy.agda)
------------------------------------------------------------------------

Eq-trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq-trans S.refl q = q

Eq-cong2 : {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f S.refl S.refl = S.refl

------------------------------------------------------------------------
-- Part 1: Substitution helpers (reused from Adequacy)
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

------------------------------------------------------------------------
-- Part 2: EvalRel transport
------------------------------------------------------------------------

EvalRel-transport : {n : Nat} {M M' : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Eq M M' -> EvalRel M rho u -> EvalRel M' rho u
EvalRel-transport S.refl ev = ev

------------------------------------------------------------------------
-- Part 3: ValidSub2 — bundled valid substitutions
--
-- Like ValidSub but produces Val2 instead of Val.
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

------------------------------------------------------------------------
-- Part 4: Helpers from Adequacy.agda (reused)
------------------------------------------------------------------------

EvalRel-bot : {n : Nat} (M : Expr n) (rho : EnvApprox n) -> EvalRel M rho Bot
EvalRel-bot (Var i)   rho = mkSigma tt (PaperSemantics.LeCode-Bot (lookupEnv i rho))
EvalRel-bot U         rho = mkSigma tt (PaperSemantics.LeCode-Bot UCode)
EvalRel-bot (Pi A B)  rho = tt
EvalRel-bot (Lam A M) rho = tt
EvalRel-bot (App f a) rho = tt

Coherent-CoherentFun : (b : FinEl) (f : FinFun) ->
  Coherent (PiCode b f) -> CoherentFunTail f
Coherent-CoherentFun b f cpf = snd cpf

FinMem-bU-from-Pi : (b : FinEl) (f : FinFun) ->
  CoherentFun f -> FinMemAllU f b -> FinMem b UCode
FinMem-bU-from-Pi b f cf fmAllU = bU-from-cf-fmU f b cf fmAllU

EqVal-sym-fn : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal G M N A u a -> EqVal G N M A u a
EqVal-sym-fn u a cu ca ev = EqVal-sym u a cu ca ev

FinMem-from-LeCode-UCode : (u : FinEl) -> LeCode u UCode -> FinMem u UCode
FinMem-from-LeCode-UCode Bot          le = tt
FinMem-from-LeCode-UCode UCode        le = tt
FinMem-from-LeCode-UCode (FunEl g)    ()
FinMem-from-LeCode-UCode (PiCode a f) ()

ValTy-U : {n : Nat} (G : Ctx n) (u : FinEl) -> LeCode u UCode -> ValTy G U u
ValTy-U G Bot          le = tt
ValTy-U G UCode        le = tt
ValTy-U G (FunEl g)    ()
ValTy-U G (PiCode a f) ()

LeCode-UCode-Coherent : (u : FinEl) -> LeCode u UCode -> Coherent u
LeCode-UCode-Coherent Bot          le = tt
LeCode-UCode-Coherent UCode        le = tt
LeCode-UCode-Coherent (FunEl g)    ()
LeCode-UCode-Coherent (PiCode a f) ()

FinMem-from-U-code : (a u : FinEl) -> FinMem u a -> LeCode a UCode -> FinMem u UCode
FinMem-from-U-code Bot Bot fm le = tt
FinMem-from-U-code Bot UCode () le
FinMem-from-U-code Bot (FunEl g) () le
FinMem-from-U-code Bot (PiCode b f) () le
FinMem-from-U-code UCode u fm le = fm
FinMem-from-U-code (FunEl g)    u fm ()
FinMem-from-U-code (PiCode b f) u fm ()

------------------------------------------------------------------------
-- Part 6: Main mutual block — adequacySub2 / adequacyEqSub2
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Main bundled adequacy theorem
  adequacySub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (substExpr sigma M) (substExpr sigma A) u a

  -- Bundled adequacy for conversion
  adequacyEqSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

  ----------------------------------------------------------------------
  -- adequacySub2: ty-var
  ----------------------------------------------------------------------

  adequacySub2 (ty-var {G = G} {i = i} _) sigma rho crho vs fits u hu a evA fm =
    vs i u (fst hu) (snd hu) a evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-U
  --
  -- Val2 H U U u a:
  --   a = Bot:   HasType H U U (always)
  --   u = Bot:   HasType H U U (always)
  --   UCode UCode: Pair (HasType H U U) (ValTy2 H U UCode)
  --   Others: absurd (u ≤ UCode, a ≤ UCode)
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-U _) sigma rho crho vs fits u hu a evA fm =
    tyU2-helper u a (snd hu) (snd evA) fm
    where
      tyU2-helper : (u0 a0 : FinEl) -> LeCode u0 UCode -> LeCode a0 UCode ->
        FinMem u0 a0 -> Val2 _ U U u0 a0
      tyU2-helper u0 Bot          _  _  _   = tt
      tyU2-helper Bot UCode        _  _  _   = tt
      tyU2-helper UCode UCode       _  _  _   = tt
      tyU2-helper (FunEl _)    UCode () _  _
      tyU2-helper (PiCode _ _) UCode () _  _
      tyU2-helper u0 (FunEl _)    _  () _
      tyU2-helper u0 (PiCode _ _) _  () _

  ----------------------------------------------------------------------
  -- adequacySub2: ty-conv
  --
  -- Uses adequacySub2 on d1 with converted type, then
  -- adequacyEqSub2 on d2 for the type equality.
  -- For Val2, we need Val2-EqValTy2-fwd (postulated below).
  ----------------------------------------------------------------------

  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits u hu Bot evA fm = tt
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        val   = adequacySub2 d1 sigma rho crho vs fits u hu UCode evA' fm
        aU    = FinMem-a-in-U u UCode fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits UCode evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in Val2-EqValTy2-fwd u UCode tt eqvty val
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits Bot hu (FunEl g) evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits UCode hu (FunEl g) evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits (FunEl _) hu (FunEl g) evA ()
  adequacySub2 (ty-conv d1 d2 dB) sigma rho crho vs fits (PiCode _ _) hu (FunEl g) evA ()
  adequacySub2 (ty-conv {M = M} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        val   = adequacySub2 d1 sigma rho crho vs fits u hu (PiCode b' f') evA' fm
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits (PiCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in Val2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty val

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Pi (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 1690-1842
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits UCode ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (FunEl g) ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu Bot evA fm = tt
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu UCode evA fm =
    adequacySub2-Pi d1 d2 sigma rho crho vs fits b f hu evA fm
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu (FunEl _) evA ()
  adequacySub2 {H = H} (ty-Pi {G = G} {A = A} {B = B} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu (PiCode _ _) evA ()

  ----------------------------------------------------------------------
  -- adequacySub2: ty-Lam (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 1846-1991
  ----------------------------------------------------------------------

  adequacySub2 (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3) sigma rho crho vs fits Bot hu a evA fm =
    Val2-Bot a
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits UCode () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits (PiCode _ _) () a evA fm
  adequacySub2 (ty-Lam d1 d2 d3) sigma rho crho vs fits (FunEl g) hu Bot evA fm = tt
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits (FunEl g) hu UCode () fm
  adequacySub2 (ty-Lam {A = A} d1 d2 d3) sigma rho crho vs fits (FunEl g) hu (FunEl h) () fm
  adequacySub2 {H = H} {G = G} (ty-Lam {A = A} {B = B} {M = M} d1 d2 d3)
    sigma rho crho vs fits (FunEl g) hu (PiCode b f0) evA fm =
    adequacySub2-Lam d1 d2 d3 sigma rho crho vs fits g hu b f0 evA fm

  ----------------------------------------------------------------------
  -- adequacySub2: ty-App (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 1994-2001 + 620-883
  ----------------------------------------------------------------------

  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits Bot hu ac evAc fm =
    Val2-Bot ac
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits UCode ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits UCode tt ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits (FunEl g') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (FunEl g') (EvalRel-coh (App f' a) rho (FunEl g') ev) ev ac evAc fm
  adequacySub2 {H = H} (ty-App {G = G} {A = A} {B = B} {f = f'} {a = a} dA dB d1 d2) sigma rho crho vs fits (PiCode b0' f0') ev ac evAc fm =
    adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (PiCode b0' f0') (EvalRel-coh (App f' a) rho (PiCode b0' f0') ev) ev ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-refl
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-refl d) sigma rho crho vs fits u hu a evA fm =
    Val2-to-EqVal2 u a (adequacySub2 d sigma rho crho vs fits u hu a evA fm)

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-sym
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-sym {M = M} {N = N} {A = Asrc} d) sigma rho crho vs fits u hu a evA fm =
    let huN  = convSound-inv d rho fits u hu
        cu'  = FinMem-Coherent u a fm
        ca   = EvalRel-coh Asrc rho a evA
        eq   = adequacyEqSub2 d sigma rho crho vs fits u huN a evA fm
    in EqVal2-sym u a cu' ca eq

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-trans
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-trans {M = M} {N = N} {P = P} {A = A} d1 d2) sigma rho crho vs fits u hu a evA fm =
    let huN  = convSound d1 rho fits u hu
        cu   = FinMem-Coherent u a fm
        ca   = EvalRel-coh A rho a evA
        eq1  = adequacyEqSub2 d1 sigma rho crho vs fits u hu a evA fm
        eq2  = adequacyEqSub2 d2 sigma rho crho vs fits u huN a evA fm
    in EqVal2-trans u a cu ca eq1 eq2

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-conv
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 dB) sigma rho crho vs fits u hu Bot evA fm = tt
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits u hu UCode evA fm =
    let evA'  = convSound-inv d2 rho fits UCode evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits u hu UCode evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u UCode fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits UCode evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u UCode tt eqvty eq
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits Bot hu (FunEl g) evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits UCode hu (FunEl g) evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits (FunEl _) hu (FunEl g) evA ()
  adequacyEqSub2 (conv-conv d1 d2 _) sigma rho crho vs fits (PiCode _ _) hu (FunEl g) evA ()
  adequacyEqSub2 (conv-conv {M = M} {N = N} {A = A} {B = B} d1 d2 _) sigma rho crho vs fits u hu (PiCode b' f') evA fm =
    let evA'  = convSound-inv d2 rho fits (PiCode b' f') evA
        eq    = adequacyEqSub2 d1 sigma rho crho vs fits u hu (PiCode b' f') evA' fm
        evU   = mkSigma tt (LeCode-refl UCode tt)
        aU    = FinMem-a-in-U u (PiCode b' f') fm
        eqAB  = adequacyEqSub2 d2 sigma rho crho vs fits (PiCode b' f') evA' UCode evU aU
        eqvty = snd (snd eqAB)
    in EqVal2-EqValTy2-fwd u (PiCode b' f') (EvalRel-coh A rho (PiCode b' f') evA') eqvty eq

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-beta (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 2037-2051
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-beta {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4) sigma rho crho vs fits u hu ac evAc fm =
    adequacyEqSub2-beta d1 d2 d3 d4 sigma rho crho vs fits u hu ac evAc fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-Pi (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 2054-2250
  ----------------------------------------------------------------------

  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits Bot hu a evA fm =
    EqVal2-Bot a
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits UCode ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (FunEl g) ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu Bot evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu (FunEl _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu (PiCode _ _) evA ()
  adequacyEqSub2 {H = H} (conv-Pi {G = G} {A = A} {A' = A'} {B = B} {B' = B'} d1 d2) sigma rho crho vs fits (PiCode b f)
    hu UCode evA fm =
    adequacyEqSub2-Pi d1 d2 sigma rho crho vs fits b f hu evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-funext (postulated — hard case)
  -- TODO: Full implementation mirroring Adequacy.agda lines 2252-2254
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-funext dA d1 d2 d3) sigma rho crho vs fits u hu a evA fm =
    adequacyEqSub2-funext dA d1 d2 d3 sigma rho crho vs fits u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-fun (postulated — hard case)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-fun _ dB d1 d2) sigma rho crho vs fits u hu a evA fm =
    adequacyEqSub2-App-fun dB d1 d2 sigma rho crho vs fits u hu a evA fm

  ----------------------------------------------------------------------
  -- adequacyEqSub2: conv-App-arg (postulated — hard case)
  ----------------------------------------------------------------------

  adequacyEqSub2 (conv-App-arg _ dB d1 d2) sigma rho crho vs fits u hu a evA fm =
    adequacyEqSub2-App-arg dB d1 d2 sigma rho crho vs fits u hu a evA fm

  ----------------------------------------------------------------------
  -- Hard case helpers (postulated)
  -- TODO: Each mirrors the corresponding helper in Adequacy.agda
  ----------------------------------------------------------------------

  -- Helper: Val2 at U b UCode is the same as ValTy2 b
  -- (substExpr sigma U = U definitionally, but Agda doesn't see through it)
  Val2-U-to-ValTy2 : {n : Nat} {G : Ctx n} {M : Expr n}
    (b : FinEl) -> FinMem b UCode ->
    Val2 G M U b UCode -> ValTy2 G M b
  Val2-U-to-ValTy2 Bot            fm v = v
  Val2-U-to-ValTy2 UCode          fm v = v
  Val2-U-to-ValTy2 (FunEl g)      fm v = v
  Val2-U-to-ValTy2 (PiCode a f)   fm v = v

  -- ty-Pi at (PiCode b f, UCode): build ValTyPi2
  adequacySub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    Val2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)) U (PiCode b f) UCode
  adequacySub2-Pi {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits b f hu evA fm =
    let sA    = substExpr sigma A
        sB    = substExpr (liftSub sigma) B
        bU    = fst fm
        allU  = fst (snd fm)
        cf    = snd (snd fm)
        cb    = coh-from-aU b bU
        -- IH on d1 at b: Val2 H sA (substExpr sigma U) b UCode
        -- Since substExpr sigma U = U, this is ValTy2 H sA b
        evAb  = fst (snd hu)
        valTyA = Val2-U-to-ValTy2 b bU
                   (adequacySub2 d1 sigma rho crho vs fits b evAb UCode
                     (mkSigma tt (LeCode-refl UCode tt)) bU)
    in mkSigma sA (mkSigma sB (mkSigma Red-refl
         (mkSigma cf (mkSigma allU
           (mkSigma valTyA (mkSigma (buildPiEdgeVal2 d1 d2 sigma rho crho vs fits b f hu fm)
                                    (buildPiEdgeEq2 d1 d2 sigma rho crho vs fits b f hu fm)))))))

  -- transportVal2: transport Val2 H N sA u0 b to Val2 H N sA u' a_arg
  transportVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (b : FinEl) -> FinMem b UCode ->
    EvalRel A rho b ->
    (u0 : FinEl) -> FinMem u0 b ->
    (N : Expr h) -> Val2 H N (substExpr sigma A) u0 b ->
    (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
    (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
    Val2 H N (substExpr sigma A) u' a_arg
  transportVal2 {H = H} {A = A} d1 d2 sigma rho crho vs fits b bU evAb u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
    let sA       = substExpr sigma A
        comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
        ca_arg   = EvalRel-coh A rho a_arg evA_arg
        cb       = coh-from-aU b bU
        a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
        sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
        c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
        le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
        le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
        fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
        fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtA_b    = Val2-U-to-ValTy2 b bU (adequacySub2 d1 sigma rho crho vs fits b evAb UCode evU bU)
        vtA_a    = Val2-U-to-ValTy2 a_arg a_argU (adequacySub2 d1 sigma rho crho vs fits a_arg evA_arg UCode evU a_argU)
        vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU vtA_b vtA_a
        val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup
                     cb c_sup valN vtA_sup
        fm_u_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
        val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u_sup val1
        val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
    in val3

  -- buildPiEdgeVal2: PiEdgeVal2 for the Pi case
  buildPiEdgeVal2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeVal2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeVal2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits b f hu fm u0 v0 sel N valN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        evA'pi   = fst (snd (snd (snd hu)))
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
        hyp0     = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u0 fm_u0_b N valN u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'      = ValidSub2-extend sigma N rho u0 vs hyp0
        evU      = mkSigma tt (LeCode-refl UCode tt)
        ih       = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N) (extendEnv rho u0)
                       crho' vs' fits' v0 evB_u0_v0 UCode evU fm_v0_U)
    in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N)) ih

  -- buildPiEdgeEq2: PiEdgeEq2 for the Pi case
  buildPiEdgeEq2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} ->
    HasType G A U -> HasType (extend G A) B U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    FinMem (PiCode b f) UCode ->
    PiEdgeEq2 H (substExpr sigma A) (substExpr (liftSub sigma) B) b f
  buildPiEdgeEq2 {H = H} {G = G} {A = A} {B = B} d1 d2 sigma rho crho vs fits b f hu fm u0 v0 sel N1 N2 eqvalN =
    let sA       = substExpr sigma A
        sB       = substExpr (liftSub sigma) B
        bU       = fst fm
        allU     = fst (snd fm)
        cf       = snd (snd fm)
        cb       = coh-from-aU b bU
        evAb     = fst (snd hu)
        a'pi     = fst (snd (snd hu))
        evA'pi   = fst (snd (snd (snd hu)))
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
        -- IH for N1
        hyp0_N1  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u0 fm_u0_b N1 valN1 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N1   = ValidSub2-extend sigma N1 rho u0 vs hyp0_N1
        evU      = mkSigma tt (LeCode-refl UCode tt)
        vtN1     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N1) (extendEnv rho u0)
                       crho' vs'_N1 fits' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN1'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N1)) vtN1
        -- IH for N2
        hyp0_N2  = \ u' cu' le_u' a_arg evA_arg fm_u'_a ->
                     transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u0 fm_u0_b N2 valN2 u' cu' le_u' a_arg evA_arg fm_u'_a
        vs'_N2   = ValidSub2-extend sigma N2 rho u0 vs hyp0_N2
        vtN2     = Val2-U-to-ValTy2 v0 fm_v0_U
                     (adequacySub2 d2 (extSub sigma N2) (extendEnv rho u0)
                       crho' vs'_N2 fits' v0 evB_u0_v0 UCode evU fm_v0_U)
        vtN2'    = S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N2)) vtN2
    in twoValTy2-to-EqValTy2 v0 fm_v0_U vtN1' vtN2'

  -- ty-Lam at (FunEl g, PiCode b f0): build ValPi2
  adequacySub2-Lam : {h g : Nat} {H : Ctx h} {G : Ctx g}
      {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} ->
      HasType G A U -> HasType (extend G A) B U ->
      HasType (extend G A) M B ->
      (sigma : Sub h g) -> (rho : EnvApprox g) ->
      CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
      (g0 : FinFun) ->
      EvalRel (Lam A M) rho (FunEl g0) ->
      (b : FinEl) -> (f0 : FinFun) ->
      EvalRel (Pi A B) rho (PiCode b f0) ->
      FinMem (FunEl g0) (PiCode b f0) ->
      Val2 H (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
             (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (FunEl g0) (PiCode b f0)
  adequacySub2-Lam {H = H} {G = G} {A = A} {B = B} {M = M} d1 d2 d3
      sigma rho crho vs fits g0 hu b f0 evA fm =
    mkSigma valTyPi (mkSigma sA (mkSigma sB (mkSigma Red-refl
      (mkSigma cg (mkSigma fmg (mkSigma piAppVal2 piAppEq2))))))
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
      evAb : EvalRel A rho b
      evAb = fst (snd evA)
      a_lam = fst hu
      bodyLam : (u0 v0 : FinEl) -> Selection g0 u0 v0 ->
        Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a_lam) (EvalRel M (extendEnv rho x) v0)))
      bodyLam = snd (snd (snd (snd hu)))
      evU : EvalRel U rho UCode
      evU = mkSigma tt (LeCode-refl UCode tt)
      valTyPi : ValTyPi2 H (Pi sA sB) b f0
      valTyPi = adequacySub2 (ty-Pi d1 d2) sigma rho crho vs fits
                  (PiCode b f0) evA UCode evU pU
      piAppVal2 : PiAppVal2 H (Lam sA sM) sA sB b f0 g0
      piAppVal2 u' v' sel N valN =
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
                          transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u' fm_u'_b N valN u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'       = ValidSub2-extend sigma N rho u' vs hyp0
            ih        = adequacySub2 d3 (extSub sigma N) (extendEnv rho u')
                          crho' vs' fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M      = S.Eq-sym (substExpr-comp sigma M N)
            eq_B      = S.Eq-sym (substExpr-comp sigma B N)
            ih'       = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N) M) T v' (EvalFun f0 u')) eq_B ih
            ih''      = S.Eq-transport (\ E -> Val2 H E (subst1 sB N) v' (EvalFun f0 u')) eq_M ih'
        in Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl) ih''
      piAppEq2 : PiAppEq2 H (Lam sA sM) sA sB b f0 g0
      piAppEq2 u' v' sel N1 N2 eqvalN =
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
            -- IH for N1
            hyp0_N1   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u' fm_u'_b N1 valN1 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'_N1    = ValidSub2-extend sigma N1 rho u' vs hyp0_N1
            ih1       = adequacySub2 d3 (extSub sigma N1) (extendEnv rho u')
                          crho' vs'_N1 fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M1     = S.Eq-sym (substExpr-comp sigma M N1)
            eq_B1     = S.Eq-sym (substExpr-comp sigma B N1)
            ih1'      = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N1) M) T v' (EvalFun f0 u')) eq_B1 ih1
            ih1''     = S.Eq-transport (\ E -> Val2 H E (subst1 sB N1) v' (EvalFun f0 u')) eq_M1 ih1'
            val1      = Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl) ih1''
            -- IH for N2
            hyp0_N2   = \ u'' cu'' le_u'' a_arg evA_arg fm_u''_a ->
                          transportVal2 d1 d2 sigma rho crho vs fits b bU evAb u' fm_u'_b N2 valN2 u'' cu'' le_u'' a_arg evA_arg fm_u''_a
            vs'_N2    = ValidSub2-extend sigma N2 rho u' vs hyp0_N2
            ih2       = adequacySub2 d3 (extSub sigma N2) (extendEnv rho u')
                          crho' vs'_N2 fits' v' evM_u'_v' (EvalFun f0 u') evB_u'_ef fm_v'_ef
            eq_M2     = S.Eq-sym (substExpr-comp sigma M N2)
            eq_B2     = S.Eq-sym (substExpr-comp sigma B N2)
            ih2'      = S.Eq-transport (\ T -> Val2 H (substExpr (extSub sigma N2) M) T v' (EvalFun f0 u')) eq_B2 ih2
            ih2''     = S.Eq-transport (\ E -> Val2 H E (subst1 sB N2) v' (EvalFun f0 u')) eq_M2 ih2'
            val2_raw  = Val2-beta-expand v' (EvalFun f0 u') (headred-step headred-beta headred-refl) ih2''
            -- Transport val2_raw from type (subst1 sB N2) to (subst1 sB N1)
            fm_ef_U   = FinMem-a-in-U v' (EvalFun f0 u') fm_v'_ef
            vtBN1     = Val2-U-to-ValTy2 (EvalFun f0 u') fm_ef_U
                          (adequacySub2 d2 (extSub sigma N1) (extendEnv rho u')
                            crho' vs'_N1 fits' (EvalFun f0 u') evB_u'_ef UCode evU fm_ef_U)
            vtBN1'    = S.Eq-transport (\ T -> ValTy2 H T (EvalFun f0 u'))
                          (S.Eq-sym (substExpr-comp sigma B N1)) vtBN1
            vtBN2     = Val2-U-to-ValTy2 (EvalFun f0 u') fm_ef_U
                          (adequacySub2 d2 (extSub sigma N2) (extendEnv rho u')
                            crho' vs'_N2 fits' (EvalFun f0 u') evB_u'_ef UCode evU fm_ef_U)
            vtBN2'    = S.Eq-transport (\ T -> ValTy2 H T (EvalFun f0 u'))
                          (S.Eq-sym (substExpr-comp sigma B N2)) vtBN2
            eqBN1N2   = twoValTy2-to-EqValTy2 (EvalFun f0 u') fm_ef_U vtBN1' vtBN2'
            eqBN2N1   = EqValTy2-sym (EvalFun f0 u') (coh-from-aU (EvalFun f0 u') fm_ef_U) eqBN1N2
            val2      = Val2-EqValTy2-fwd v' (EvalFun f0 u') (coh-from-aU (EvalFun f0 u') fm_ef_U) eqBN2N1 val2_raw
        in twoVal2-to-EqVal2 v' (EvalFun f0 u') fm_v'_ef val1 val2

  -- ty-App helper (proved)
  adequacySub2-App : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
    (u : FinEl) -> Coherent u ->
    EvalRel (App f' a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u ac
  -- u = UCode: Val2 at UCode ac is Top for ac = Bot/UCode, absurd otherwise
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev Bot evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev UCode evAc fm = tt
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits UCode cu ev (PiCode _ _) evAc ()
  -- u = PiCode: FinMem forces ac = UCode (or Bot, absurd)
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (PiCode _ _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (PiCode _ _) cu ev (FunEl _) evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (PiCode _ _) cu ev (PiCode _ _) evAc ()
  -- u = FunEl: FinMem forces ac = PiCode (or Bot, absurd)
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (FunEl _) cu ev Bot evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (FunEl _) cu ev UCode evAc ()
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits (FunEl _) cu ev (FunEl _) evAc ()
  -- Bot case (shouldn't be called but needed for coverage)
  adequacySub2-App dA dB d1 d2 sigma rho crho vs fits Bot cu ev ac evAc fm = Val2-Bot ac
  -- PiCode/UCode case
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits (PiCode b0pc f0pc) cu1 ev1 UCode evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits (PiCode b0pc f0pc) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) UCode evAc1 fm1
  -- FunEl/PiCode case
  adequacySub2-App {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits (FunEl gfe) cu1 ev1 (PiCode bacfe facfe) evAc1 fm1 =
    adequacySub2-App-core {H = H} dA dB d1 d2 sigma rho crho vs fits (FunEl gfe) cu1
      (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (PiCode bacfe facfe) evAc1 fm1

  -- Core App helper — shared by both real cases
  adequacySub2-App-core : {h g0 : Nat} {H : Ctx h} {G0 : Ctx g0}
    {A : Expr g0} {B : Expr (suc g0)} {f' a : Expr g0} ->
    HasType G0 A U -> HasType (extend G0 A) B U ->
    HasType G0 f' (Pi A B) -> HasType G0 a A ->
    (sigma : Sub h g0) -> (rho : EnvApprox g0) ->
    CoherentEnv rho -> ValidSub2 H G0 sigma rho -> Fits G0 rho ->
    (u1 : FinEl) -> Coherent u1 ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f' rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    Val2 H (substExpr sigma (App f' a)) (substExpr sigma (subst1 B a)) u1 ac1
  adequacySub2-App-core {H = H} {A = A} {B = B} {f' = f'} {a = a}
    dA dB d1 d2 sigma rho crho vs fits u1 cu1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
    S.Eq-transport (\ T -> Val2 H (App sf sa) T u1 ac1) (S.Eq-sym eq-sBA) transported
    where
      sf  = substExpr sigma f'
      sa  = substExpr sigma a
      sA  = substExpr sigma A
      sB  = substExpr (liftSub sigma) B
      sBA = substExpr sigma (subst1 B a)
      eq-sBA : Eq sBA (subst1 sB sa)
      eq-sBA = S.Eq-sym (subst-subst1-comm sigma B a)

      -- Decompose App evaluation (already decomposed by caller)
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
      val_fun  = adequacySub2 d1 sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

      -- Dispatch on (ub, ap) — only (FunEl, PiCode) is non-absurd
      appVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f' rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        Val2 H sf (Pi sA sB) ub ap ->
        Val2 H (App sf sa) (subst1 sB sa) u1 ac1
      appVal-dispatch Bot          ap    () evFb evPab fmba valba
      appVal-dispatch UCode        ap    () evFb evPab fmba valba
      appVal-dispatch (PiCode _ _) ap    () evFb evPab fmba valba
      appVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
      appVal-dispatch (FunEl g_big) (PiCode b_pi f_pi) lf evFb evPab fmba valba =
        let -- LeCode u1 (EvalFun g_big v0)
            le_u1_vsel = fst lf

            -- Extract from fmba (FinMem (FunEl g_big) (PiCode b_pi f_pi))
            fmg_big  = fst fmba
            cg_big   = fst (snd fmba)
            piU      = snd (snd fmba)
            b_piU    = fst piU
            allU_fpi = fst (snd piU)
            cf_pi    = snd (snd piU)
            cb_pi    = coh-from-aU b_pi b_piU

            -- Extract EvalRel A rho b_pi from Pi evaluation
            evA_bpi  = fst (snd evPab)

            -- selectionBelow g_big v0
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
            val_arg  = adequacySub2 d2 sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract PiAppVal2 from function's Val2
            -- Val2 at (FunEl, PiCode) = Pair ValTyPi2 ValPi2
            vpi_fun  = snd valba
            A0_fun   = fst vpi_fun
            B0_fun   = fst (snd vpi_fun)
            red_fun  = fst (snd (snd vpi_fun))
            uniq_fun = Red-unique-Pi Red-refl red_fun
            eqA_fun  = fst uniq_fun
            eqB_fun  = snd uniq_fun
            pav_fun  = fst (snd (snd (snd (snd (snd vpi_fun)))))

            -- Transport argument type
            val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_fun val_arg

            -- Apply PiAppVal2
            val_app_raw = pav_fun u_sel v_sel sel_big sa val_arg'
            val_app : Val2 H (App sf sa) (subst1 sB sa) v_sel (EvalFun f_pi u_sel)
            val_app = S.Eq-transport
              (\ X -> Val2 H (App sf sa) (subst1 X sa) v_sel (EvalFun f_pi u_sel))
              (S.Eq-sym eqB_fun) val_app_raw

            -- Transport: (v_sel, EvalFun f_pi u_sel) → (u1, ac1)
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

            -- ValTy2 at Sup: need ValTy2 at ac1 and at ef_usel
            evU      = mkSigma tt (LeCode-refl UCode tt)

            -- ValTy2 at ac1
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
              in adequacySub2 d2 sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U)
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
              in adequacySub2 d2 sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

            -- ValTy2-Sup
            vt_sup   = ValTy2-Sup H (subst1 sB sa) ac1 ef_usel
                         comp_ac_ef ac1_U ef_uselU vt_ac vt_ef

            -- Transport chain
            val_up   = upVal2 H (App sf sa) (subst1 sB sa) v_sel ef_usel sup_code
                         le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup val_app vt_sup
            val_res  = restrictVal2 H (App sf sa) (subst1 sB sa) v_sel u1 sup_code
                         le_u1_vsel' fm_u1_sup fm_vsel_sup val_up
            val_down = downVal2 H (App sf sa) (subst1 sB sa) u1
                         ac1 sup_code le_ac_sup fm1 c_ac sup_U val_res
        in val_down

      -- Dispatch on u_big (FunEl) and a_pi (PiCode)
      transported : Val2 H (App sf sa) (subst1 sB sa) u1 ac1
      transported = appVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

  -- conv-beta helper (proved via headred-contract + headred-expand)
  adequacyEqSub2-beta : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {M : Expr (suc g)} {a : Expr g} ->
    HasType G A U -> HasType (extend G A) B U ->
    HasType (extend G A) M B -> HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App (Lam A M) a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (substExpr sigma (App (Lam A M) a))
             (substExpr sigma (subst1 M a))
             (substExpr sigma (subst1 B a)) u ac
  adequacyEqSub2-beta {H = H} {A = A} {B = B} {M = M} {a = a0}
    d1 d2 d3 d4 sigma rho crho vs fits u hu ac evAc fm =
    let val_app = adequacySub2 (ty-App d1 d2 (ty-Lam d1 d2 d3) d4)
                    sigma rho crho vs fits u hu ac evAc fm
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

  -- EqVal2-U extraction helpers: EqVal2 at UCode case-splits on u
  -- (unbundled EqVal at UCode is uniform Pair for all u; bundled has Top at Bot)
  EqVal2-U-to-ValTy2-fst : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G M v0
  EqVal2-U-to-ValTy2-fst Bot            fm ev = tt
  EqVal2-U-to-ValTy2-fst UCode          fm ev = fst ev
  EqVal2-U-to-ValTy2-fst (FunEl g)      fm ev = fst ev
  EqVal2-U-to-ValTy2-fst (PiCode a' f') fm ev = fst ev

  EqVal2-U-to-ValTy2-snd : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> ValTy2 G N v0
  EqVal2-U-to-ValTy2-snd Bot            fm ev = tt
  EqVal2-U-to-ValTy2-snd UCode          fm ev = fst (snd ev)
  EqVal2-U-to-ValTy2-snd (FunEl g)      fm ev = fst (snd ev)
  EqVal2-U-to-ValTy2-snd (PiCode a' f') fm ev = fst (snd ev)

  EqVal2-U-to-EqValTy2 : {n : Nat} {G : Ctx n} {M N : Expr n}
    (v0 : FinEl) -> FinMem v0 UCode ->
    EqVal2 G M N U v0 UCode -> EqValTy2 G M N v0
  EqVal2-U-to-EqValTy2 Bot            fm ev = tt
  EqVal2-U-to-EqValTy2 UCode          fm ev = snd (snd ev)
  EqVal2-U-to-EqValTy2 (FunEl g)      fm ev = snd (snd ev)
  EqVal2-U-to-EqValTy2 (PiCode a' f') fm ev = snd (snd ev)

  -- conv-Pi helper (proved)
  adequacyEqSub2-Pi : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A A' : Expr g} {B B' : Expr (suc g)} ->
    ConvTm G A A' U ->
    ConvTm (extend G A) B B' U ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (b : FinEl) -> (f : FinFun) ->
    EvalRel (Pi A B) rho (PiCode b f) ->
    EvalRel U rho UCode ->
    FinMem (PiCode b f) UCode ->
    EqVal2 H (Pi (substExpr sigma A) (substExpr (liftSub sigma) B))
             (Pi (substExpr sigma A') (substExpr (liftSub sigma) B'))
             U (PiCode b f) UCode
  adequacyEqSub2-Pi {H = H} {G = G} {A = A} {A' = A'} {B = B} {B' = B'}
    d1 d2 sigma rho crho vs fits b f hu evU fm =
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

      -- hu : EvalRel (Pi A B) rho (PiCode b f)
      cpu   = fst hu
      evAb : EvalRel A rho b
      evAb  = fst (snd hu)
      a'pi  = fst (snd (snd hu))
      evA'pi = fst (snd (snd (snd hu)))
      bodyPi : (u0 v0 : FinEl) -> Selection f u0 v0 ->
        Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a'pi) (EvalRel B (extendEnv rho x) v0)))
      bodyPi = snd (snd (snd (snd hu)))

      -- IH on d1: EqVal2 H sA sA' U b UCode
      eqD1 : EqVal2 H sA sA' U b UCode
      eqD1 = adequacyEqSub2 d1 sigma rho crho vs fits b evAb UCode evUU bU

      valTyA : ValTy2 H sA b
      valTyA = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-first b UCode eqD1)

      valTyA' : ValTy2 H sA' b
      valTyA' = Val2-U-to-ValTy2 b bU (Val2-from-EqVal2-second b UCode eqD1)

      eqValTyAA' : EqValTy2 H sA sA' b
      eqValTyAA' = EqVal2-U-to-EqValTy2 b bU eqD1

      eqValTyA'A : EqValTy2 H sA' sA b
      eqValTyA'A = EqValTy2-sym b cb eqValTyAA'

      -- Local transport: Val2 H N sA u0 b -> Val2 H N sA u' a_arg
      -- Like transportVal2 but uses adequacyEqSub2 d1 (ConvTm) instead of adequacySub2 (HasType)
      trVal : (u0 : FinEl) -> FinMem u0 b ->
        (N : Expr _) -> Val2 H N sA u0 b ->
        (u' : FinEl) -> Coherent u' -> LeCode u' u0 ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H N sA u' a_arg
      trVal u0 fm_u0_b N valN u' cu' le_u'_u0 a_arg evA_arg fm_u'_a =
        let comp_b_a = EvalRel-Comp A rho crho b a_arg evAb evA_arg
            ca_arg   = EvalRel-coh A rho a_arg evA_arg
            a_argU   = FinMem-a-in-U u' a_arg fm_u'_a
            sup_bU   = finMemUCode-Sup b a_arg comp_b_a bU a_argU
            c_sup    = Coherent-Sup b a_arg comp_b_a cb ca_arg
            le_b_sup = LeCode-Sup-left b a_arg comp_b_a cb ca_arg
            le_a_sup = LeCode-Sup-right b a_arg comp_b_a cb ca_arg
            fm_u0_sup = finMem-upward u0 b (Sup b a_arg) le_b_sup cb c_sup fm_u0_b sup_bU
            fm_u'_sup = finMem-upward u' a_arg (Sup b a_arg) le_a_sup ca_arg c_sup fm_u'_a sup_bU
            vtA_a    = EqVal2-U-to-ValTy2-fst a_arg a_argU
                         (adequacyEqSub2 d1 sigma rho crho vs fits a_arg evA_arg UCode evUU a_argU)
            vtA_sup  = ValTy2-Sup H sA b a_arg comp_b_a bU a_argU valTyA vtA_a
            val1     = upVal2 H N sA u0 b (Sup b a_arg) le_b_sup fm_u0_b fm_u0_sup
                         cb c_sup valN vtA_sup
            val2     = restrictVal2 H N sA u0 u' (Sup b a_arg) le_u'_u0 fm_u'_sup fm_u0_sup val1
            val3     = downVal2 H N sA u' a_arg (Sup b a_arg) le_a_sup fm_u'_a ca_arg sup_bU val2
        in val3

      -- buildEdgeValB2: PiEdgeVal2 H sA sB b f (codomain validity for B)
      buildEdgeValB2 : PiEdgeVal2 H sA sB b f
      buildEdgeValB2 u0 v0 sel N valN =
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
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B N))
             (EqVal2-U-to-ValTy2-fst v0 fm_v0_U ih)

      -- buildEdgeEqB2: PiEdgeEq2 H sA sB b f (codomain argument congruence for B)
      buildEdgeEqB2 : PiEdgeEq2 H sA sB b f
      buildEdgeEqB2 u0 v0 sel N1 N2 eqvalN =
        let valN1    = Val2-from-EqVal2-first u0 b eqvalN
            valN2    = Val2-from-EqVal2-second u0 b eqvalN
            fm_v0_U  = FinMem-Selection-UCode b sel allU cf
            vtN1     = buildEdgeValB2 u0 v0 sel N1 valN1
            vtN2     = buildEdgeValB2 u0 v0 sel N2 valN2
        in twoValTy2-to-EqValTy2 v0 fm_v0_U vtN1 vtN2

      -- buildEdgeValB'2: PiEdgeVal2 H sA' sB' b f (codomain validity for B')
      -- Uses Val2-EqValTy2-fwd to convert Val2 H N sA' u b -> Val2 H N sA u b
      buildEdgeValB'2 : PiEdgeVal2 H sA' sB' b f
      buildEdgeValB'2 u0 v0 sel N valN_A' =
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
            ih       = adequacyEqSub2 d2 (extSub sigma N) (extendEnv rho u0)
                         crho' vs' fits' v0 evB_u0_v0 UCode evUU fm_v0_U
        in S.Eq-transport (\ T -> ValTy2 H T v0) (S.Eq-sym (substExpr-comp sigma B' N))
             (EqVal2-U-to-ValTy2-snd v0 fm_v0_U ih)

      -- buildEdgeEqB'2: PiEdgeEq2 H sA' sB' b f (codomain argument congruence for B')
      buildEdgeEqB'2 : PiEdgeEq2 H sA' sB' b f
      buildEdgeEqB'2 u0 v0 sel N1 N2 eqvalN_A' =
        let vtN1 = buildEdgeValB'2 u0 v0 sel N1 (Val2-from-EqVal2-first u0 b eqvalN_A')
            vtN2 = buildEdgeValB'2 u0 v0 sel N2 (Val2-from-EqVal2-second u0 b eqvalN_A')
            fm_v0_U = FinMem-Selection-UCode b sel allU cf
        in twoValTy2-to-EqValTy2 v0 fm_v0_U vtN1 vtN2

      -- buildEdgeEqTyBB'2: PiEdgeEqTy2 H sA sB sB' b f (heterogeneous codomain equality)
      buildEdgeEqTyBB'2 : PiEdgeEqTy2 H sA sB sB' b f
      buildEdgeEqTyBB'2 u0 v0 sel P valP =
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
            ih       = adequacyEqSub2 d2 (extSub sigma P) (extendEnv rho u0)
                         crho' vs' fits' v0 evB_u0_v0 UCode evUU fm_v0_U
            eqvt     = S.Eq-transport (\ T -> EqValTy2 H (subst1 sB P) T v0) (S.Eq-sym (substExpr-comp sigma B' P))
                         (S.Eq-transport (\ T -> EqValTy2 H T (substExpr (extSub sigma P) B') v0) (S.Eq-sym (substExpr-comp sigma B P))
                           (EqVal2-U-to-EqValTy2 v0 fm_v0_U ih))
        in eqvt

      -- Assemble ValTyPi2 H (Pi sA sB) b f
      valTyPiAB : ValTy2 H (Pi sA sB) (PiCode b f)
      valTyPiAB = mkSigma sA (mkSigma sB (mkSigma Red-refl
                    (mkSigma cf (mkSigma allU
                      (mkSigma valTyA (mkSigma buildEdgeValB2 buildEdgeEqB2))))))

      -- Assemble ValTyPi2 H (Pi sA' sB') b f
      valTyPiA'B' : ValTy2 H (Pi sA' sB') (PiCode b f)
      valTyPiA'B' = mkSigma sA' (mkSigma sB' (mkSigma Red-refl
                      (mkSigma cf (mkSigma allU
                        (mkSigma valTyA' (mkSigma buildEdgeValB'2 buildEdgeEqB'2))))))

      -- Assemble EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
      -- = Pair (ValTyPi2 M) (Pair (ValTyPi2 N) (EqValTyPi2 M N))
      eqValTyPi : EqValTy2 H (Pi sA sB) (Pi sA' sB') (PiCode b f)
      eqValTyPi = mkSigma valTyPiAB (mkSigma valTyPiA'B'
                    (mkSigma sA (mkSigma sB (mkSigma sA' (mkSigma sB'
                      (mkSigma Red-refl
                        (mkSigma Red-refl
                          (mkSigma cf (mkSigma allU
                            (mkSigma eqValTyAA' buildEdgeEqTyBB'2))))))))))

  -- conv-funext helper (proved)
  adequacyEqSub2-funext : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f g' : Expr g} ->
    HasType G A U ->
    ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                         (App (wkExpr g') (Var fzero)) B ->
    HasType G f (Pi A B) ->
    HasType G g' (Pi A B) ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel f rho u ->
    (a : FinEl) -> EvalRel (Pi A B) rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma f) (substExpr sigma g')
            (substExpr sigma (Pi A B)) u a
  adequacyEqSub2-funext dA d df dg sigma rho crho vs fits u hu a evA fm =
    let evG    = convSound (conv-funext dA d df dg) rho fits u hu
        val_sf = adequacySub2 df sigma rho crho vs fits u hu a evA fm
        val_sg = adequacySub2 dg sigma rho crho vs fits u evG a evA fm
    in twoVal2-to-EqVal2 u a fm val_sf val_sg

  -- conv-App-fun helper (proved)
  adequacyEqSub2-App-fun : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits UCode ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits UCode ev UCode evAc fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-fun dB dff' da sigma rho crho vs fits (FunEl _) ev (FunEl _) evAc ()
  -- PiCode/UCode and FunEl/PiCode: decompose ev and delegate
  adequacyEqSub2-App-fun {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
    dB dff' da sigma rho crho vs fits (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-fun {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
    dB dff' da sigma rho crho vs fits (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-fun-core {H = H} dB dff' da sigma rho crho vs fits (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  -- Core App-fun helper
  adequacyEqSub2-App-fun-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f f' a : Expr g} ->
    HasType (extend G A) B U ->
    ConvTm G f f' (Pi A B) ->
    HasType G a A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u1 : FinEl) ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f') (substExpr sigma a))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-fun-core {H = H} {A = A} {B = B} {f = f0} {f' = f'} {a = a}
    dB dff' da sigma rho crho vs fits u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
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
      eqval_fun = adequacyEqSub2 dff' sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

      -- Dispatch on (ub, ap) — only (FunEl, PiCode) is non-absurd
      appEqVal-dispatch : (ub : FinEl) -> (ap : FinEl) ->
        LeCode (FunEl sing) ub ->
        EvalRel f0 rho ub -> EvalRel (Pi A B) rho ap ->
        FinMem ub ap ->
        EqVal2 H sf sf' (Pi sA sB) ub ap ->
        EqVal2 H (App sf sa) (App sf' sa) (subst1 sB sa) u1 ac1
      appEqVal-dispatch Bot          ap    () evFb evPab fmba eqvba
      appEqVal-dispatch UCode        ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (PiCode _ _) ap    () evFb evPab fmba eqvba
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
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
            val_arg  = adequacySub2 da sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract EqValPi2 from EqVal2 at (FunEl, PiCode)
            -- EqVal2 = Pair ValTy2 (Pair ValPi2_M (Pair ValPi2_N EqValPi2))
            eqvpi_fun = snd (snd (snd eqvba))
            A0_eqfun  = fst eqvpi_fun
            B0_eqfun  = fst (snd eqvpi_fun)
            red_eqfun = fst (snd (snd eqvpi_fun))
            uniq_eqfun = Red-unique-Pi Red-refl red_eqfun
            eqA_eqfun = fst uniq_eqfun
            eqB_eqfun = snd uniq_eqfun
            paeqv_fun = snd (snd (snd (snd (snd eqvpi_fun))))

            -- Transport argument type
            val_arg' = S.Eq-transport (\ X -> Val2 H sa X u_sel b_pi) eqA_eqfun val_arg

            -- Apply PiAppEqVal2
            eqval_app_raw = paeqv_fun u_sel v_sel sel_big sa val_arg'
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
            hyp_ext  = \ u' cu' le_u' a_arg evA_aarg fm_u'_a ->
              let evA_u' = EvalRel-down a rho v_fwd' u' crho cu' evA_vfwd' le_u'
              in adequacySub2 da sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ext   = ValidSub2-extend sigma sa rho v_fwd' vs hyp_ext
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U)
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
              in adequacySub2 da sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a
            vs_ef     = ValidSub2-extend sigma sa rho v_fwd_ef' vs hyp_ef
            vt_ef_raw = Val2-U-to-ValTy2 ef_usel ef_uselU
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd_ef')
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU)
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

  -- conv-App-arg helper (proved)
  adequacyEqSub2-App-arg : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u : FinEl) -> EvalRel (App f a) rho u ->
    (ac : FinEl) -> EvalRel (subst1 B a) rho ac -> FinMem u ac ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits Bot ev ac evAc fm = EqVal2-Bot ac
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits UCode ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits UCode ev UCode evAc fm = mkSigma tt (mkSigma tt tt)
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits UCode ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits UCode ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (PiCode _ _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (PiCode _ _) ev (FunEl _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (PiCode _ _) ev (PiCode _ _) evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (FunEl _) ev Bot evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (FunEl _) ev UCode evAc ()
  adequacyEqSub2-App-arg dB df daa' sigma rho crho vs fits (FunEl _) ev (FunEl _) evAc ()
  -- PiCode/UCode and FunEl/PiCode
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits (PiCode b0pc f0pc) ev UCode evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits (PiCode b0pc f0pc)
      (fst ev) (fst (snd ev)) (snd (snd ev)) UCode evAc fm
  adequacyEqSub2-App-arg {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits (FunEl gfe) ev (PiCode bacfe facfe) evAc fm =
    adequacyEqSub2-App-arg-core {H = H} dB df daa' sigma rho crho vs fits (FunEl gfe)
      (fst ev) (fst (snd ev)) (snd (snd ev)) (PiCode bacfe facfe) evAc fm

  -- Core App-arg helper
  adequacyEqSub2-App-arg-core : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {A : Expr g} {B : Expr (suc g)} {f a a' : Expr g} ->
    HasType (extend G A) B U ->
    HasType G f (Pi A B) ->
    ConvTm G a a' A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    (u1 : FinEl) ->
    (v0 : FinEl) -> EvalRel a rho v0 ->
    EvalRel f rho (FunEl (cons (mkSigma v0 u1) nil)) ->
    (ac1 : FinEl) -> EvalRel (subst1 B a) rho ac1 -> FinMem u1 ac1 ->
    EqVal2 H (App (substExpr sigma f) (substExpr sigma a))
             (App (substExpr sigma f) (substExpr sigma a'))
             (substExpr sigma (subst1 B a))
             u1 ac1
  adequacyEqSub2-App-arg-core {H = H} {A = A} {B = B} {f = f0} {a = a} {a' = a'}
    dB df daa' sigma rho crho vs fits u1 v0 evA_v0 evF_sing ac1 evAc1 fm1 =
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
      val_fun  = adequacySub2 df sigma rho crho vs fits u_big evF_big a_pi evPi fm_big

      -- Helper: Val2 for sa via Val2-from-EqVal2-first
      val_sa : (u' : FinEl) -> EvalRel a rho u' ->
        (a_arg : FinEl) -> EvalRel A rho a_arg -> FinMem u' a_arg ->
        Val2 H sa sA u' a_arg
      val_sa u' evA_u' a_arg evA_aarg fm_u'_a =
        Val2-from-EqVal2-first u' a_arg
          (adequacyEqSub2 daa' sigma rho crho vs fits u' evA_u' a_arg evA_aarg fm_u'_a)

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
      appEqVal-dispatch (FunEl g_big) Bot          lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) UCode        lf evFb evPab ()
      appEqVal-dispatch (FunEl g_big) (FunEl _)    lf evFb evPab ()
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
            eqval_arg = adequacyEqSub2 daa' sigma rho crho vs fits u_sel evA_usel b_pi evA_bpi fm_usel_bpi

            -- Extract PiAppEq2 from function's Val2 at (FunEl, PiCode)
            -- Val2 = Pair ValTyPi2 ValPi2
            vpi_fun  = snd valba
            A0_fun   = fst vpi_fun
            B0_fun   = fst (snd vpi_fun)
            red_fun  = fst (snd (snd vpi_fun))
            uniq_fun = Red-unique-Pi Red-refl red_fun
            eqA_fun  = fst uniq_fun
            eqB_fun  = snd uniq_fun
            pae_fun  = snd (snd (snd (snd (snd (snd vpi_fun)))))

            -- Transport argument types
            eqval_arg' = S.Eq-transport (\ X -> EqVal2 H sa sa' X u_sel b_pi) eqA_fun eqval_arg

            -- Apply PiAppEq2
            eqval_app_raw = pae_fun u_sel v_sel sel_big sa sa' eqval_arg'
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
            vt_ac_raw = Val2-U-to-ValTy2 ac1 ac1_U
                          (adequacySub2 dB (extSub sigma sa) (extendEnv rho v_fwd')
                            crho_ext vs_ext fits_ext ac1 evB_vfwd' UCode evU ac1_U)
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
                            crho_ef vs_ef fits_ef ef_usel evB_vfef' UCode evU ef_uselU)
            vt_ef     = S.Eq-transport (\ T -> ValTy2 H T ef_usel) eq_comp vt_ef_raw

            vt_sup   = ValTy2-Sup H (subst1 sB sa) ac1 ef_usel
                         comp_ac_ef ac1_U ef_uselU vt_ac vt_ef
            eqval_up   = upEqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) v_sel ef_usel sup_code
                           le_ef_sup fm_vsel_ef fm_vsel_sup c_efusel c_sup eqval_app vt_sup
            eqval_res  = restrictEqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) v_sel u1 sup_code
                           le_u1_vsel' fm_u1_sup fm_vsel_sup eqval_up
            eqval_down = downEqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1
                           ac1 sup_code le_ac_sup fm1 c_ac sup_U eqval_res
        in eqval_down

      transported : EqVal2 H (App sf sa) (App sf sa') (subst1 sB sa) u1 ac1
      transported = appEqVal-dispatch u_big a_pi le_sing evF_big evPi fm_big val_fun

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
  Val2-transport-M {u = u} {a = a} (substExpr-id M)
    (Val2-transport-A {u = u} {a = a} (substExpr-id A)
      (adequacySub2 d idSub emptyEnv tt (ValidSub2-empty idSub emptyEnv) tt u hu a evA fm))
