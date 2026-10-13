{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Soundness.agda
--
-- Theorem 16 of mahlo-plan.tex (soundness of the PER model): every
-- rule of MAHLO/Typing.agda preserves validity, by induction on
-- derivations.  Consequently, if  G |- t = t' : C,  then  t = t'  in
-- [C] in every pair of related environments, hence  t ~ t'  in the
-- safe relation S; in particular in any environment of neutrals.  In
-- the concrete term model this is (T2a).
--
-- Relative to: the abstract term model (MAHLO.Model.Model, i.e. P1's
-- TermModel plus the denotation) and the fixed point of Gamma
-- (MAHLO.Fixpoint.Fixpoint, Lemma 14).  No other hypothesis.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
import MAHLO.Model
import MAHLO.Fixpoint

module MAHLO.Soundness (TM : TermModel) (M : MAHLO.Model.Model TM)
                       (Fx : MAHLO.Fixpoint.Fixpoint TM) where

open TermModel TM
open MAHLO.Model TM using (Env ; cons)
open MAHLO.Model.Model M
open import MAHLO.Candidate TM
open import MAHLO.Validity TM M Fx
open import MAHLO.ValPi TM M Fx
open import MAHLO.ValNat TM M Fx
open import MAHLO.ValU TM M Fx
open import MAHLO.Syntax
  renaming (Pi to tPi ; Sigma to tSigma ; Nat to tNat ; V to tV)
open import MAHLO.Typing

------------------------------------------------------------------------
-- Elements of V are types; equal elements of V are equal types
------------------------------------------------------------------------

private
  v-isty-el : {n : Num} {G : Ctx n} {A : Expr n} -> ValTm G A tV -> ValTy G A
  v-isty-el h e = tyv _ (tySm (Rof (h e)) ~-refl)

  v-tyeq-el : {n : Num} {G : Ctx n} {A B : Expr n} -> ValConv G A B tV -> ValTyEq G A B
  v-tyeq-el h e = tyv _ (tySm (Rof (h e)) ~-refl)

------------------------------------------------------------------------
-- The soundness theorem
------------------------------------------------------------------------

mutual
  sTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> ValTy G A
  sTy (isty-V w) = v-isty-V
  sTy (isty-el h) = v-isty-el (sTm h)
  sTy (isty-Pi hA hB) = v-isty-Pi (sTy hA) (sTy hB)
  sTy (isty-Sigma hA hB) = v-isty-Sigma (sTy hA) (sTy hB)

  sTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> ValTm G t A
  sTm (ty-var {G = G} {i} w) = v-var G i
  sTm (ty-conv h q) = v-ty-conv (sTm h) (sTyEq q)
  sTm (ty-sub h) = v-conv-sub (sTm h)
  sTm (ty-Pi (univ-V refl) hA hB) = v-conv-Pi-V (sTm hA) (sTm hB)
  sTm (ty-Pi (univ-U f g refl) hA hB) = v-conv-Pi-U (sTm hA) (sTm hB)
  sTm (ty-Sigma (univ-V refl) hA hB) = v-conv-Sigma-V (sTm hA) (sTm hB)
  sTm (ty-Sigma (univ-U f g refl) hA hB) = v-conv-Sigma-U (sTm hA) (sTm hB)
  sTm (ty-Nat-V w) = v-ty-Nat-V
  sTm (ty-Nat-U h) = v-ty-Nat-U (sTm h)
  sTm (ty-Ucode hf hg) = v-ty-Ucode (sTm hf) (sTm hg)
  sTm (ty-Fhat hf hg hA hB) = v-conv-Fhat (sTm hf) (sTm hA) (sTm hB)
  sTm (ty-Ghat hf hg hA hB hc) =
    v-conv-Ghat (sTm hf) (sTm hg) (sTm hA) (sTm hB) (sTm hc)
  sTm (ty-Lam hA hB ht) = v-ty-Lam (sTy hA) (sTy hB) (sTm ht)
  sTm (ty-App hA hB ht ha) = v-ty-App (sTm ht) (sTm ha)
  sTm (ty-Pair hA hB ht hu) = v-ty-Pair (sTy hA) (sTy hB) (sTm ht) (sTm hu)
  sTm (ty-Fst hA hB ht) = v-ty-Fst (sTm ht)
  sTm (ty-Snd hA hB ht) = v-ty-Snd (sTm ht)
  sTm (ty-Zero w) = v-ty-Zero
  sTm (ty-Suc h) = v-conv-Suc (sTm h)
  sTm (ty-Rec hC hz hs hk) = v-ty-Rec (sTy hC) (sTm hz) (sTm hs) (sTm hk)

  sTyEq : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> ValTyEq G A B
  sTyEq (tyeq-refl h) = v-tyeq-refl (sTy h)
  sTyEq (tyeq-sym q) = v-tyeq-sym (sTyEq q)
  sTyEq (tyeq-trans q q') = v-tyeq-trans (sTyEq q) (sTyEq q')
  sTyEq (tyeq-el c) = v-tyeq-el (sConv c)
  sTyEq (tyeq-Pi hA hB hB' qA qB) = v-tyeq-Pi (sTy hA) (sTyEq qA) (sTyEq qB)
  sTyEq (tyeq-Sigma hA hB hB' qA qB) = v-tyeq-Sigma (sTy hA) (sTyEq qA) (sTyEq qB)

  sConv : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A -> ValConv G t u A
  sConv (conv-refl h) = v-conv-refl (sTm h)
  sConv (conv-sym c) = v-conv-sym (sConv c)
  sConv (conv-trans c c') = v-conv-trans (sConv c) (sConv c')
  sConv (conv-conv c q) = v-conv-conv (sConv c) (sTyEq q)
  sConv (conv-sub c) = v-conv-sub (sConv c)
  sConv (conv-R' hA hB c) = v-conv-R' (sTm hA) (sTm hB) (sConv c)
  sConv (conv-delta-f hf hg hA hB) = v-conv-delta-f (sTm hf) (sTm hA) (sTm hB)
  sConv (conv-delta-g hf hg hA hB hc) =
    v-conv-delta-g (sTm hf) (sTm hg) (sTm hA) (sTm hB) (sTm hc)
  sConv (conv-beta hA hB ht ha) = v-conv-beta (sTm ht) (sTm ha)
  sConv (conv-funext hA hB ht ht' c) = v-conv-funext (sTm ht) (sConv c)
  sConv (conv-fst-beta hA hB ht hu) = v-conv-fst-beta (sTm ht)
  sConv (conv-snd-beta hA hB ht hu) = v-conv-snd-beta (sTm hu)
  sConv (conv-pairext hA hB ht ht' cf cs) = v-conv-pairext (sTm ht) (sConv cf) (sConv cs)
  sConv (conv-rec-zero hC hz hs) = v-conv-rec-zero (sTm hz)
  sConv (conv-rec-suc hC hz hs hk) = v-conv-rec-suc (sTy hC) (sTm hz) (sTm hs) (sTm hk)
  sConv (conv-App hA hB c ca) = v-conv-App (sTy hA) (sTy hB) (sConv c) (sConv ca)
  sConv (conv-Fst hA hB c) = v-conv-Fst (sConv c)
  sConv (conv-Snd hA hB c) = v-conv-Snd (sTy hB) (sConv c)
  sConv (conv-Pi (univ-V refl) hA hB hB' cA cB) = v-conv-Pi-V (sConv cA) (sConv cB)
  sConv (conv-Pi (univ-U f g refl) hA hB hB' cA cB) = v-conv-Pi-U (sConv cA) (sConv cB)
  sConv (conv-Sigma (univ-V refl) hA hB hB' cA cB) = v-conv-Sigma-V (sConv cA) (sConv cB)
  sConv (conv-Sigma (univ-U f g refl) hA hB hB' cA cB) =
    v-conv-Sigma-U (sConv cA) (sConv cB)
  sConv (conv-Suc c) = v-conv-Suc (sConv c)
  sConv (conv-Rec hC hC' q cz cs ck) =
    v-conv-Rec (sTy hC) (sTyEq q) (sConv cz) (sConv cs) (sConv ck)
  sConv (conv-Ucode hf hg cf cg) = v-conv-Ucode (sTm hf) (sConv cf) (sConv cg)
  sConv (conv-Fhat cf cg hA hB hB' cA cB) = v-conv-Fhat (sConv cf) (sConv cA) (sConv cB)
  sConv (conv-Ghat cf cg hA hB hB' cA cB cc) =
    v-conv-Ghat (sConv cf) (sConv cg) (sConv cA) (sConv cB) (sConv cc)

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

-- presupposition: a type or a term lives in a well-formed context
mutual
  wfTy : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx G
  wfTy (isty-V w) = w
  wfTy (isty-el h) = wfTm h
  wfTy (isty-Pi hA hB) = wfTy hA
  wfTy (isty-Sigma hA hB) = wfTy hA

  wfTm : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> WfCtx G
  wfTm (ty-var w) = w
  wfTm (ty-conv h q) = wfTm h
  wfTm (ty-sub h) = wfTm h
  wfTm (ty-Pi u hA hB) = wfTm hA
  wfTm (ty-Sigma u hA hB) = wfTm hA
  wfTm (ty-Nat-V w) = w
  wfTm (ty-Nat-U h) = wfTm h
  wfTm (ty-Ucode hf hg) = wfTm hf
  wfTm (ty-Fhat hf hg hA hB) = wfTm hf
  wfTm (ty-Ghat hf hg hA hB hc) = wfTm hf
  wfTm (ty-Lam hA hB ht) = wfTy hA
  wfTm (ty-App hA hB ht ha) = wfTy hA
  wfTm (ty-Pair hA hB ht hu) = wfTy hA
  wfTm (ty-Fst hA hB ht) = wfTy hA
  wfTm (ty-Snd hA hB ht) = wfTy hA
  wfTm (ty-Zero w) = w
  wfTm (ty-Suc h) = wfTm h
  wfTm (ty-Rec hC hz hs hk) = wfTm hz

sCtx : {n : Num} (G : Ctx n) -> WfCtx G -> ValCtx G
sCtx empty w = tt1
sCtx (extend G A) (wf-extend hA) = sCtx G (wfTy hA) ,, sTy hA

-- an environment of neutrals is valid  (the "identity environment")
neutralEnv : {n : Num} (G : Ctx n) -> ValCtx G -> (rho : Env n) ->
             ((i : Fin n) -> N (rho i) (rho i)) -> EnvR G rho rho
neutralEnv empty vc rho nr = tt1
neutralEnv (extend G A) (vc ,, vA) rho nr =
  e ,, tmv _ (TyV.ty (vA e)) (lo (TyV.ty (vA e)) (nr fzero))
  where e = neutralEnv G vc (tl rho) (\ i -> nr (fsuc i))

------------------------------------------------------------------------
-- Consequences
------------------------------------------------------------------------

-- Theorem 16: judgemental equality is sound for the safe relation
soundness : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
            {rho rho' : Env n} -> EnvR G rho rho' -> S (den t rho) (den u rho')
soundness c e = hi (TmV.ty (sConv c e)) (TmV.el (sConv c e))

-- in an environment of neutrals (the identity environment)
soundness-ne : {n : Num} {G : Ctx n} {t u A : Expr n} -> WfCtx G -> ConvTm G t u A ->
               (rho : Env n) -> ((i : Fin n) -> N (rho i) (rho i)) ->
               S (den t rho) (den u rho)
soundness-ne {G = G} w c rho nr = soundness c (neutralEnv G (sCtx G w) rho nr)

-- every well-typed term is safe, i.e. (T2a) in the concrete model
wt-safe : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A ->
          (rho : Env n) -> ((i : Fin n) -> N (rho i) (rho i)) -> S (den t rho) (den t rho)
wt-safe h rho nr = soundness-ne (wfTm h) (conv-refl h) rho nr

-- closed terms
emptyEnv : Env zero
emptyEnv ()

soundness-closed : {t u A : Expr zero} -> ConvTm empty t u A ->
                   S (den t emptyEnv) (den u emptyEnv)
soundness-closed c = soundness c tt1
