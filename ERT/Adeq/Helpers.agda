{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Adeq.Helpers
--
-- T_R version of MIN/Adequacy/Helpers.agda: transports of the validity
-- relations, substitution extension, valid substitutions (single and
-- two-sided), and small typing inversions.  Environments evaluate the
-- stripped terms (ERT.Model.Strip).
------------------------------------------------------------------------

module ERT.Adeq.Helpers where

import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
              Sigma ; Eq ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; U0)
open import ERT.Basic using (Fin ; fzero ; fsuc ; wkRen ; absurd)
open import ERT.RussellSyntax
open import ERT.RussellTyping
open import ERT.RussellMeta
open import ERT.RussellMetaCong using (ConvTmSub ; consSub ; consSub-subst1)
open import ERT.Dom.Kernel using (LeCode ; Coherent ; CoherentFun ; CoherentFunTail ;
  FinMem ; FinMemAllU ; LeCode-Bot)
open import ERT.Model.Eval using (EnvApprox ; emptyEnv ; extendEnv ; lookupEnv ; EvalRel)
open import ERT.Model.EvalSubstitution using (EvalRel-unwk)
import ERT.Model.Core as C
open import ERT.Model.Strip using (strip ; strip-wk)
open import ERT.Valid.Public
open import ERT.Valid.Core using (bU-from-cf-fmU)

------------------------------------------------------------------------
-- Transports
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

EvalRel-transport : {n : Nat} {M M' : C.Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Eq M M' -> EvalRel M rho u -> EvalRel M' rho u
EvalRel-transport S.refl ev = ev

------------------------------------------------------------------------
-- Extending a substitution
------------------------------------------------------------------------

extSub : {h g : Nat} -> Sub h g -> Expr h -> Sub h (suc g)
extSub sigma t fzero    = t
extSub sigma t (fsuc i) = sigma i

substExpr-wk : {h g : Nat} (sigma : Sub h g) (M : Expr g) (t : Expr h) ->
  Eq (substExpr (extSub sigma t) (wkExpr M)) (substExpr sigma M)
substExpr-wk sigma M t =
  Eq-trans (subst-ren (extSub sigma t) wkRen M)
           (substExpr-ext _ sigma (\ i -> S.refl) M)

-- The extended substitution is the single substitution after lifting.
substExpr-comp : {h g : Nat} (sigma : Sub h g) (B : Expr (suc g)) (N : Expr h) ->
  Eq (subst1 (substExpr (liftSub sigma) B) N) (substExpr (extSub sigma N) B)
substExpr-comp sigma B N =
  S.Eq-sym (Eq-trans (substExpr-ext (extSub sigma N) (consSub sigma N) pt B)
                     (consSub-subst1 sigma N B))
  where
    pt : (i : Fin _) -> Eq (extSub sigma N i) (consSub sigma N i)
    pt fzero    = S.refl
    pt (fsuc i) = S.refl

------------------------------------------------------------------------
-- Valid substitutions
------------------------------------------------------------------------

ValidSub2 : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> EnvApprox g -> Set
ValidSub2 {h} {g} H G sigma rho =
  (i : Fin g) -> (u : FinEl) -> (cu : Coherent u) ->
  LeCode u (lookupEnv i rho) ->
  (a : FinEl) -> EvalRel (strip (lookup G i)) rho a -> FinMem u a ->
  Val2 H (sigma i) (substExpr sigma (lookup G i)) u a

ValidSub2-empty : {h : Nat} {H : Ctx h} (sigma : Sub h zero)
  (rho : EnvApprox zero) -> ValidSub2 H empty sigma rho
ValidSub2-empty sigma rho ()

private
  evalRel-unwk-strip : {n : Nat} (A : Expr n) (rho : EnvApprox n) (v a : FinEl)
    -> EvalRel (strip (wkExpr A)) (extendEnv rho v) a -> EvalRel (strip A) rho a
  evalRel-unwk-strip A rho v a ev =
    EvalRel-unwk (strip A) rho v a (EvalRel-transport (strip-wk A) ev)

ValidSub2-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma : Sub h g) (t : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  ValidSub2 H G sigma rho ->
  ((u : FinEl) -> Coherent u -> LeCode u v ->
    (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
    Val2 H t (substExpr sigma A) u a) ->
  ValidSub2 H (extend G A) (extSub sigma t) (extendEnv rho v)
ValidSub2-extend {A = Asrc} sigma t rho v vs hyp0 fzero u cu le a evA fm =
  Val2-transport-A {u = u} {a = a} (S.Eq-sym (substExpr-wk sigma Asrc t))
    (hyp0 u cu le a (evalRel-unwk-strip Asrc rho v a evA) fm)
ValidSub2-extend {G = G} sigma t rho v vs hyp0 (fsuc i) u cu le a evA fm =
  Val2-transport-A {u = u} {a = a} (S.Eq-sym (substExpr-wk sigma (lookup G i) t))
    (vs i u cu le a (evalRel-unwk-strip (lookup G i) rho v a evA) fm)

ValidConvSub2 : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> EnvApprox g -> Set
ValidConvSub2 {h} {g} H G sigma sigma' rho =
  (i : Fin g) -> (u : FinEl) -> (cu : Coherent u) ->
  LeCode u (lookupEnv i rho) ->
  (a : FinEl) -> EvalRel (strip (lookup G i)) rho a -> FinMem u a ->
  EqVal2 H (sigma i) (sigma' i) (substExpr sigma (lookup G i)) u a

ValidConvSub2-refl : {h g : Nat} {H : Ctx h} {G : Ctx g}
  {sigma : Sub h g} {rho : EnvApprox g} ->
  ValidSub2 H G sigma rho -> ValidConvSub2 H G sigma sigma rho
ValidConvSub2-refl vs i u cu le a evA fm = Val2-to-EqVal2 u a (vs i u cu le a evA fm)

ValidConvSub2-extend : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  (sigma sigma' : Sub h g) (t t' : Expr h) (rho : EnvApprox g) (v : FinEl) ->
  ValidConvSub2 H G sigma sigma' rho ->
  ((u : FinEl) -> Coherent u -> LeCode u v ->
    (a : FinEl) -> EvalRel (strip A) rho a -> FinMem u a ->
    EqVal2 H t t' (substExpr sigma A) u a) ->
  ValidConvSub2 H (extend G A) (extSub sigma t) (extSub sigma' t') (extendEnv rho v)
ValidConvSub2-extend {A = Asrc} sigma sigma' t t' rho v vcs hyp0 fzero u cu le a evA fm =
  EqVal2-transport-A {u = u} {a = a} (S.Eq-sym (substExpr-wk sigma Asrc t))
    (hyp0 u cu le a (evalRel-unwk-strip Asrc rho v a evA) fm)
ValidConvSub2-extend {G = G} sigma sigma' t t' rho v vcs hyp0 (fsuc i) u cu le a evA fm =
  EqVal2-transport-A {u = u} {a = a} (S.Eq-sym (substExpr-wk sigma (lookup G i) t))
    (vcs i u cu le a (evalRel-unwk-strip (lookup G i) rho v a evA) fm)

------------------------------------------------------------------------
-- Well-typed (pairs of) substitutions
------------------------------------------------------------------------

WtConvSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> Set
WtConvSub = ConvTmSub

WtConvSub-refl : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g} ->
  WtSub H G sigma -> WtConvSub H G sigma sigma
WtConvSub-refl ws i = conv-refl (ws i)

extSub-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  {sigma : Sub h g} {t : Expr h} ->
  WtSub H G sigma -> HasType H t (substExpr sigma A) ->
  WtSub H (extend G A) (extSub sigma t)
extSub-WtSub {H = H} {A = A} {sigma = sigma} {t = t} ws dt fzero =
  S.Eq-transport (\ X -> HasType H t X) (S.Eq-sym (substExpr-wk sigma A t)) dt
extSub-WtSub {H = H} {G = G} {sigma = sigma} {t = t} ws dt (fsuc i) =
  S.Eq-transport (\ X -> HasType H (sigma i) X) (S.Eq-sym (substExpr-wk sigma (lookup G i) t)) (ws i)

extSub-WtConvSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {A : Expr g}
  {sigma sigma' : Sub h g} {t t' : Expr h} ->
  WtConvSub H G sigma sigma' -> ConvTm H t t' (substExpr sigma A) ->
  WtConvSub H (extend G A) (extSub sigma t) (extSub sigma' t')
extSub-WtConvSub {H = H} {A = A} {sigma = sigma} {t = t} {t' = t'} wcs cvtt' fzero =
  S.Eq-transport (\ X -> ConvTm H t t' X) (S.Eq-sym (substExpr-wk sigma A t)) cvtt'
extSub-WtConvSub {H = H} {G = G} {sigma = sigma} {sigma' = sigma'} {t = t} wcs cvtt' (fsuc i) =
  S.Eq-transport (\ X -> ConvTm H (sigma i) (sigma' i) X)
    (S.Eq-sym (substExpr-wk sigma (lookup G i) t)) (wcs i)

idSub-WtSub : {n : Nat} {G : Ctx n} -> WfCtx G -> WtSub G G idSub
idSub-WtSub {G = G} wfG i =
  S.Eq-transport (\ X -> HasType G (Var i) X) (S.Eq-sym (substExpr-id (lookup G i)))
    (ty-var wfG)

------------------------------------------------------------------------
-- Small domain facts
------------------------------------------------------------------------

FinMem-bU-from-Pi : (b : FinEl) (f : FinFun) ->
  CoherentFun f -> FinMemAllU f b -> FinMem b U0
FinMem-bU-from-Pi b f cf fmAllU = bU-from-cf-fmU f b cf fmAllU

FinMem-from-LeCode-UCode : (u : FinEl) (k : Nat) -> LeCode u (UCode k) -> FinMem u U0
FinMem-from-LeCode-UCode Bot          k le = tt
FinMem-from-LeCode-UCode (UCode _)    k le = tt
FinMem-from-LeCode-UCode (FunEl g)    k ()
FinMem-from-LeCode-UCode (PiCode a f) k ()

------------------------------------------------------------------------
-- Typing inversions
------------------------------------------------------------------------

wfCtx-domain : {n : Nat} {G : Ctx n} {A : Expr n} -> WfCtx (extend G A) -> IsType G A
wfCtx-domain (wf-extend dA) = dA

-- The components of a product type are types.
ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (IsType G A) (IsType (extend G A) B)
ty-Pi-invert (ty-Pi dA dB)   = mkSigma (is-Ty-from-U dA) (is-Ty-from-U dB)
ty-Pi-invert (ty-conv d _)   = ty-Pi-invert d
ty-Pi-invert (ty-cum d)      = ty-Pi-invert d

isType-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
  IsType G (Pi A B) -> Pair (IsType G A) (IsType (extend G A) B)
isType-Pi-invert (is-Ty-from-U d) = ty-Pi-invert d
